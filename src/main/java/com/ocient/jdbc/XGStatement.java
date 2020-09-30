package com.ocient.jdbc;

import java.io.IOException;
import java.lang.reflect.Method;
import java.math.BigDecimal;
import java.sql.Array;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.Date;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.SQLFeatureNotSupportedException;
import java.sql.SQLTimeoutException;
import java.sql.SQLWarning;
import java.sql.Statement;
import java.sql.Timestamp;
import java.sql.Time;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.GregorianCalendar;
import java.util.Optional;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;
import java.util.OptionalLong;
import java.util.logging.Logger;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import com.ocient.jdbc.proto.ClientWireProtocol;
import com.ocient.jdbc.proto.ClientWireProtocol.CancelQuery;
import com.ocient.jdbc.proto.ClientWireProtocol.ConfirmationResponse;
import com.ocient.jdbc.proto.ClientWireProtocol.ConfirmationResponse.ResponseType;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteExplain;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteExport;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteExportResponse;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecutePlan;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteInlinePlan;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteQuery;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteUpdate;
import com.ocient.jdbc.proto.ClientWireProtocol.ExplainPlan;
import com.ocient.jdbc.proto.ClientWireProtocol.ListPlan;
import com.ocient.jdbc.proto.ClientWireProtocol.FetchSystemMetadata;
import com.ocient.jdbc.proto.ClientWireProtocol.Request;
import com.ocient.jdbc.proto.ClientWireProtocol.SysQueriesRow;
import com.ocient.jdbc.proto.ClientWireProtocol.SystemWideQueries;
import com.ocient.jdbc.proto.ClientWireProtocol.KillQuery;
import com.ocient.jdbc.proto.PlanProtocol.PlanMessage;
import com.google.protobuf.util.JsonFormat;
import java.util.TimeZone;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Function;

import com.google.common.base.Preconditions;
import com.google.protobuf.util.JsonFormat;

public class XGStatement implements Statement {
	public static final Logger LOGGER = Logger.getLogger("com.ocient.jdbc");

	private static final int defaultFetchSize = 30000;

	private static String bytesToHex(final byte[] in) {
		final StringBuilder builder = new StringBuilder();
		for (final byte b : in) {
			builder.append(String.format("%02x", b));
		}
		return builder.toString();
	}

	private static int bytesToInt(final byte[] val) {
		final int ret = java.nio.ByteBuffer.wrap(val).getInt();
		return ret;
	}

	private static byte[] intToBytes(final int val) {
		final byte[] buff = new byte[4];
		buff[0] = (byte) (val >> 24);
		buff[1] = (byte) ((val & 0x00FF0000) >> 16);
		buff[2] = (byte) ((val & 0x0000FF00) >> 8);
		buff[3] = (byte) ((val & 0x000000FF));
		return buff;
	}

	protected boolean closed = false;
	private final XGConnection conn;
	private XGResultSet result;
	private int updateCount = -1;
	private int fetchSize = defaultFetchSize;
	protected ArrayList<Object> parms = new ArrayList<>();
	private int maxRows = 0;

	// not thread safe because individual queries are single threaded
	// The queryId is set on the initial call to executeQuery()
	// TODO enable timeouts on initial call to executeQuery()
	private volatile String queryId = null;

	private volatile AtomicReference<Thread> runningQueryThread = new AtomicReference<Thread>(null);
	private volatile AtomicBoolean queryCancelled = new AtomicBoolean(false);

	public void setQueryCancelled(boolean b) {
		queryCancelled.set(b);
	}

	public void setRunningQueryThread(Thread t) {
		runningQueryThread.set(t);
	}

	public void passUpCancel(boolean clearCancelFlag) throws SQLException {
		synchronized (this) {
			boolean cancelled = queryCancelled.get();
			if (clearCancelFlag) {
				queryCancelled.set(false);
			}
			if (cancelled || conn.isClosed()) {
				LOGGER.log(Level.INFO, "Throwing OK - query cancelled");
				throw SQLStates.OK.cloneAndSpecify("Query cancelled");
			}
		}
	}

	private final ArrayList<SQLWarning> warnings = new ArrayList<>();

	private final boolean force;

	// the tmeout is inherited from the connection but can be updated
	// via setQueryTimeout()
	private volatile long timeoutMillis;

	private boolean oneShotForce;

	//TODO make a builder class for xgstatement to avoid so many constructors
	public XGStatement(final XGConnection conn, final boolean shouldRequestVersion) throws SQLException {
		this.conn = conn.copy(shouldRequestVersion);
		this.force = false;
		this.oneShotForce = false;
		this.timeoutMillis = conn.getTimeoutMillis(); // inherit the connections timeout
	}

	public XGStatement(final XGConnection conn, final boolean force, final boolean oneShotForce) throws SQLException {
		this.conn = conn.copy();
		this.force = force;
		this.oneShotForce = oneShotForce;
		this.timeoutMillis = conn.getTimeoutMillis(); // inherit the connections timeout
	}

	public XGStatement(final XGConnection conn, final int type, final int concur, final boolean force,
			final boolean oneShotForce) throws SQLException {
		this.conn = conn.copy();
		this.force = force;
		this.oneShotForce = oneShotForce;
		this.timeoutMillis = conn.getTimeoutMillis(); // inherit the connections timeout
		if (concur != ResultSet.CONCUR_READ_ONLY) {
			LOGGER.log(Level.SEVERE, "Unsupported concurrency in Statement constructor");
			throw new SQLFeatureNotSupportedException();
		}

		if (type != ResultSet.TYPE_FORWARD_ONLY) {
			LOGGER.log(Level.SEVERE, "Unsupported type in Statement constructor");
			throw new SQLFeatureNotSupportedException();
		}
	}

	public XGStatement(final XGConnection conn, final int type, final int concur, final int hold, final boolean force,
			final boolean oneShotForce) throws SQLException {
		this.conn = conn.copy();
		this.force = force;
		this.oneShotForce = oneShotForce;
		this.timeoutMillis = conn.getTimeoutMillis(); // inherit the connections timeout

		if (concur != ResultSet.CONCUR_READ_ONLY) {
			LOGGER.log(Level.SEVERE, "Unsupported concurrency in Statement constructor");
			throw new SQLFeatureNotSupportedException();
		}

		if (type != ResultSet.TYPE_FORWARD_ONLY) {
			LOGGER.log(Level.SEVERE, "Unsupported type in Statement constructor");
			throw new SQLFeatureNotSupportedException();
		}

		if (hold != ResultSet.CLOSE_CURSORS_AT_COMMIT) {
			LOGGER.log(Level.SEVERE, "Unsupported holdability in Statement constructor");
			throw new SQLFeatureNotSupportedException();
		}
	}

	/**
	 * Associates the query with this statement
	 */
	private void associateQuery(final String queryId) {
		assert this.queryId == null : "Statement was not cleaned up before next query was dispatched";
		this.queryId = queryId;
	}

	/**
	 * Dissociate the current query with this statement
	 */
	private void dissociateQuery() {
		this.queryId = null;
	}

	protected Optional<String> getQueryId() {
		return Optional.ofNullable(queryId).filter(s -> !s.isEmpty());
	}

	/**
	 * Same as {@link Runnable} but can throw an exception
	 */
	protected interface ExceptionalRunnable {
		void run() throws Exception;
	}

	/**
	 * Executes a potentially exceptional task, canceling the backing query its it
	 * takes longer than the timeout specified by {@link #getQueryTimeout()}.
	 *
	 * @param task          the task to execute
	 * @param optQueryId    the query associated with this task. Empty of none
	 *                      exists
	 * @param timeoutMillis the number of milliseconds to wait before firing off a
	 *                      kill query command to the sql node
	 *
	 * @throws SQLTimeoutException if the timeout is reached before the call
	 *                             completes
	 */
	protected void startTask(ExceptionalRunnable task, final Optional<String> optQueryId, final long timeoutMillis)
			throws Exception {
		Preconditions.checkArgument(timeoutMillis >= 0L);

		// Check if we even have a cancelable query at this point
		if (!optQueryId.isPresent()) {
			task.run();
			return;
		}

		// Check if a timeout value has been set
		if (timeoutMillis == 0L) {
			task.run();
			return;
		}

		// Create a future that we'll use the propagate timeouts to the caller
		final CompletableFuture<SQLTimeoutException> killFuture = new CompletableFuture<>();

		// Capture the current thread that will block waiting for a response from the
		// server
		final Thread submittingThread = Thread.currentThread();

		// Create a task that will cancel this query if the timeout has been exceeded
		final TimerTask killQueryTask = new TimerTask() {

			@Override
			public void run() {

				// execute the cancel routine iff it's still active
				final long timeoutSec = timeoutMillis / 1000;

				LOGGER.log(Level.INFO, String.format("Timeout invoked after %s seconds. Canceling query %s", timeoutSec,
						optQueryId.get()));

				// send the kill query message on the timeout thread. This is okay because we
				// don't
				// share Timers across connection threads.
				Exception suppressed = null;
				try {

					// interrupt the thread waiting for the server response
					submittingThread.interrupt();

					// we can't reuse the existing socket because it can now have garbage sitting
					// on it (from the timed out request). We could add sequence numbers to our
					// protocol but that's a heavy handed solution. The easist thing to do here
					// is to tear down our current connection.
					conn.reconnect();

					// set the result set to null. We forego closing it because the server sql node
					// should clean up all resources related to this query.
					conn.rs = null;

					// send the kill query message to the server
					XGStatement.this.killQuery(optQueryId.get());
				} catch (Exception e) {
					LOGGER.log(Level.WARNING, String
							.format("Sending kill query failed with exception %s with message %s", e.toString(), e.getMessage()));
					suppressed = e;
				} finally {
					final SQLTimeoutException e = new SQLTimeoutException(
							String.format("Timeout of %s seconds exceeded", timeoutSec));
					if (suppressed != null) {
						e.addSuppressed(suppressed);
					}

					// return the timeout exception to the blocking caller
					killFuture.complete(e);
				}
			}
		};

		conn.addTimeout(killQueryTask, timeoutMillis);

		try {
			// run the task
			task.run();
		} finally {
			// Our task completed or we were interrupted
			if (!killQueryTask.cancel()) {
				// this is ugly, but we're within the context of a synchronous framework so
				// whatever
				SQLException e = killFuture.join(); // wait for the kill query response (don't interrupt)
				Thread.interrupted(); // clear interrupted condition
				throw e;
			} else {
				// Removes our canceled task (any those from any other connection) from the
				// timer task queue
				conn.purgeTimeoutTasks();
			}
		}
	}

	@Override
	public void addBatch(final String sql) throws SQLException {
		LOGGER.log(Level.WARNING, "addBatch() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	/**
	 * Kill the currently running query
	 *
	 * @throws SQLException
	 */
	@Override
	public void cancel() throws SQLException {
		LOGGER.log(Level.INFO, "Called cancel()");
		boolean needsReconnect = false;
		// TODO: Fail gracefully upon cancel
		// See startTask
		synchronized (this) {
			// Only statements associated to a query may be cancelled
			// No need to cancel queries twice
			if (queryId == null || queryCancelled.get()) {
				LOGGER.log(Level.INFO, "Cancel complete");
				return;
			}
			setQueryCancelled(true);
			if (runningQueryThread.get() != null && runningQueryThread.get() != Thread.currentThread()) {
				LOGGER.log(Level.WARNING, "Calling interrupt() on the running thread due to cancel()");
				runningQueryThread.get().interrupt();
				needsReconnect = true;
			}
		}

		LOGGER.log(Level.INFO, "Cancel complete");

		if (needsReconnect) {
			LOGGER.log(Level.INFO, "Cancel is initiating reconnect");
			try {
				conn.reconnect();
				conn.rs = null;

				killQuery(queryId);
			} catch (IOException | SQLException e) {
				LOGGER.log(Level.SEVERE,
						String.format("Error cancelling query with exception %s with message %s", e.toString(), e.getMessage()));
			}
		}
	}

	@Override
	public void clearBatch() throws SQLException {
		LOGGER.log(Level.WARNING, "clearBatch() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void clearWarnings() throws SQLException {
		LOGGER.log(Level.INFO, "Called clearWarnings()");
		if (closed) {
			LOGGER.log(Level.WARNING, "clearWarnings() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		warnings.clear();
	}

	@Override
	public void close() throws SQLException {
		LOGGER.log(Level.INFO, "Called close()");
		if (this.result != null) {
			result.close();
		}

		dissociateQuery();
		result = null;
		closed = true;
		conn.close(); // Since it's a clone, close this too.
	}

	@Override
	public void closeOnCompletion() throws SQLException {
		LOGGER.log(Level.WARNING, "closeOnCompletion() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public boolean execute(String sql) throws SQLException {
		LOGGER.log(Level.INFO, "Called execute()");
		clearWarnings();
		setRunningQueryThread(Thread.currentThread());
		sql = sql.trim();

		while (sql.startsWith("--") || sql.startsWith("/*")) {
			if (sql.startsWith("--")) {
				// Single line comment
				int index = sql.indexOf('\n');

				if (index == -1) {
					sql = "";
				} else {
					sql = sql.substring(index + 1).trim();
				}
			}

			if (sql.startsWith("/*")) {
				// Multi-line comment
				int index = sql.indexOf("*/");
				if (index == -1) {
					sql = "";
				} else {
					sql = sql.substring(index + 2).trim();
				}
			}
		}

		try {
			passUpCancel(false);
			if (sql.toUpperCase().startsWith("SELECT") || sql.toUpperCase().startsWith("WITH") || sql.toUpperCase().startsWith("EXPLAIN") ||
			sql.toUpperCase().startsWith("LIST TABLES") || sql.toUpperCase().startsWith("LIST SYSTEM TABLES") || sql.toUpperCase().startsWith("LIST VIEWS") || 
			sql.toUpperCase().startsWith("LIST INDICES") || sql.toUpperCase().startsWith("LIST INDEXES") || sql.toUpperCase().startsWith("GET SCHEMA") || 
			sql.toUpperCase().startsWith("DESCRIBE VIEW") || sql.toUpperCase().startsWith("DESCRIBE TABLE") || sql.toUpperCase().startsWith("PLAN EXECUTE") || 
			sql.toUpperCase().startsWith("PLAN EXPLAIN") || sql.toUpperCase().startsWith("LIST ALL QUERIES") || sql.toUpperCase().startsWith("EXPORT TABLE") || 
			sql.toUpperCase().startsWith("EXPORT TRANSLATION")) {
				this.result = (XGResultSet) executeQuery(sql);
				return true;
			} else {
				this.executeUpdate(sql);
				return false;
			}
		} catch (SQLException sqle) {
			throw sqle;
		} finally {
			setRunningQueryThread(null);
			passUpCancel(true);
		}
	}

	@Override
	public boolean execute(final String sql, final int autoGeneratedKeys) throws SQLException {
		LOGGER.log(Level.WARNING, "execute() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public boolean execute(final String sql, final int[] columnIndexes) throws SQLException {
		LOGGER.log(Level.WARNING, "execute() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public boolean execute(final String sql, final String[] columnNames) throws SQLException {
		LOGGER.log(Level.WARNING, "execute() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public int[] executeBatch() throws SQLException {
		LOGGER.log(Level.WARNING, "executeBatch() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	private static boolean startsWithIgnoreCase(final String in, final String cmp) {
		int firstNonParentheses = 0;
		int len = in.length();
		while (firstNonParentheses < len && in.charAt(firstNonParentheses) == '(') {
			firstNonParentheses++;
		}
		
		if (firstNonParentheses + cmp.length() > in.length())
		{
			return false;
		}
		
		if (in.substring(firstNonParentheses, firstNonParentheses + cmp.length()).toUpperCase().startsWith(cmp.toUpperCase())) {
			return true;
		}

		return false;
	}

	@Override
	public ResultSet executeQuery(String sql) throws SQLException {
		LOGGER.log(Level.INFO, String.format("Called executeQuery() with sql : %s", sql));
		if (sql.charAt(0) == ' ' || sql.charAt(sql.length() - 1) == ' ')
		{
			sql = sql.trim();
		}
		
		try{
			if (startsWithIgnoreCase(sql, "EXPLAIN")) {
				return explainSQL(sql);
			} else if (startsWithIgnoreCase(sql, "LIST TABLES") || startsWithIgnoreCase(sql, "LIST SYSTEM TABLES")){
				return listTables(sql, startsWithIgnoreCase(sql, "LIST SYSTEM TABLES"));
			} else if (startsWithIgnoreCase(sql, "LIST VIEWS")){
				return listViews(sql);
			} else if (startsWithIgnoreCase(sql, "LIST INDICES") || startsWithIgnoreCase(sql, "LIST INDEXES")){
				return listIndexes(sql);
			} else if (startsWithIgnoreCase(sql, "GET SCHEMA")){
				return getSchema();
			} else if(startsWithIgnoreCase(sql, "DESCRIBE TABLE")){
				return describeTable(sql);
			} else if(startsWithIgnoreCase(sql, "DESCRIBE VIEW")){
				return describeView(sql);
			} else if(startsWithIgnoreCase(sql, "PLAN EXECUTE")){
				return executePlanSQL(sql);
			} else if(startsWithIgnoreCase(sql, "PLAN EXPLAIN")){
				return explainPlanSQL(sql);
			} else if(startsWithIgnoreCase(sql, "LIST ALL QUERIES")){
				return listAllQueries();
			} else if(startsWithIgnoreCase(sql, "EXPORT TABLE")){
				return exportTableSQL(sql);
			} else if(startsWithIgnoreCase(sql, "EXPORT TRANSLATION")){
				return exportTranslationSQL(sql);
			}
		} catch (Exception e) {
			throw SQLStates.newGenericException(e);
		}

		// Handle maxRows
		if (maxRows != 0) {
			sql = "WITH THE_USER_QUERY_TO_ADD_A_LIMIT_TO as (" + sql
					+ ") SELECT * FROM THE_USER_QUERY_TO_ADD_A_LIMIT_TO LIMIT " + maxRows;
		}

		LOGGER.log(Level.INFO, String.format("Executing query: %s", sql));
		sendAndReceive(sql, Request.RequestType.EXECUTE_QUERY, 0, false, Optional.empty());
		try {
			result = conn.rs = new XGResultSet(conn, fetchSize, this);
		} catch (final Exception e) {
			LOGGER.log(Level.WARNING,
					String.format("Exception %s occurred during executeQuery() with message %s", e.toString(), e.getMessage()));
			passUpCancel(false);
			try {
				reconnect();
			} catch (final Exception reconnectException) {
				LOGGER.log(Level.WARNING, "executeQuery: reconnect", reconnectException);
				if (reconnectException instanceof SQLException) {
					throw (SQLException) reconnectException;
				}
				throw SQLStates.newGenericException(reconnectException);
			}

			return executeQuery(sql);
		}
		this.updateCount = -1;
		return result;
	}

	@Override
	public int executeUpdate(String sql) throws SQLException {
		LOGGER.log(Level.INFO, String.format("Called executeUpdate() with sql: %s", sql));
		// if this is a set command we just use a separately crafted proto message to
		// make things simpler
		sql = sql.trim();
		if (sql.toUpperCase().startsWith("SET PSO")) {
			String ending = sql.toUpperCase().substring("SET PSO".length());
			ending = ending.trim();
			if (ending.equals("ON") || ending.equals("OFF")) {
				try {
					conn.setPSO(ending.equals("ON"));
				} catch (final Exception e) {
					if (e instanceof SQLException) {
						throw (SQLException) e;
					}

					throw SQLStates.newGenericException(e);
				}
			} else {
				try {
					long threshold = Long.parseLong(ending);
					try {
						conn.setPSO(threshold);
					} catch (final Exception e) {
						if (e instanceof SQLException) {
							throw (SQLException) e;
						}

						throw SQLStates.newGenericException(e);
					}
				} catch (final NumberFormatException e) {
					throw SQLStates.SYNTAX_ERROR.cloneAndSpecify(
							"SET PSO command requires argument \"ON\" or \"OFF\" or an integer, got: " + ending);
				}
			}

			return 0;
		} else if(sql.toUpperCase().startsWith("KILL") || sql.toUpperCase().startsWith("CANCEL")){
			return killCancelQuery(sql);
		} else if (sql.toUpperCase().startsWith("SET MAXROWS")){
			return setMaxRowsSQL(sql);
		} else if(sql.toUpperCase().startsWith("SET SCHEMA")){
			return setSchema(sql);
		}

		// otherwise we are handling a normal update command
		LOGGER.log(Level.INFO, String.format("Executing update: %s", sql));
		final ClientWireProtocol.ExecuteUpdateResponse.Builder eur = (ClientWireProtocol.ExecuteUpdateResponse.Builder) sendAndReceive(
				sql, Request.RequestType.EXECUTE_UPDATE, 0, false, Optional.empty());
		return eur.getUpdateRowCount();
	}

	@Override
	public int executeUpdate(final String sql, final int autoGeneratedKeys) throws SQLException {
		LOGGER.log(Level.WARNING, "executeUpdate() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public int executeUpdate(final String sql, final int[] columnIndexes) throws SQLException {
		LOGGER.log(Level.WARNING, "executeUpdate() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public int executeUpdate(final String sql, final String[] columnNames) throws SQLException {
		LOGGER.log(Level.WARNING, "executeUpdate() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}


	private boolean shouldDeprecatedExplain()
	{
		return conn.getServerVersion().compareTo("7.0.1") == -1;
	}
	
	private String planProtoToString(final PlanMessage plan, final ClientWireProtocol.ExplainFormat format) throws SQLException
	{
		if(format == ClientWireProtocol.ExplainFormat.PROTO)
		{
			return plan.toString();
		}
		else // JSON
		{
			try{
				return JsonFormat.printer().print(plan);
			}
			catch(Exception e)
			{
				throw SQLStates.newGenericException(e);
			}
		}
	}

	//Used before version 7.0.1
	//The explain responses are proto instead of strings
	private String explainDeprecated(final String sql, final ClientWireProtocol.ExplainFormat format) throws SQLException
	{
		final ClientWireProtocol.ExplainResponse.Builder er = (ClientWireProtocol.ExplainResponse.Builder) sendAndReceive(
				sql, Request.RequestType.EXECUTE_EXPLAIN, 0, false, Optional.empty());
		return planProtoToString(er.getPlan(), format);
	}

	// used by CLI
	public String explain(final String sql, final ClientWireProtocol.ExplainFormat format) throws SQLException {

		if(shouldDeprecatedExplain())
		{
			return explainDeprecated(sql, format);
		}

		Function<Object, Void> typeSetter = (Object builder) -> {
			ClientWireProtocol.ExecuteExplain.Builder typedBuilder = (ClientWireProtocol.ExecuteExplain.Builder) builder;
			typedBuilder.setFormat(format);
			return null;
		};

		final ClientWireProtocol.ExplainResponseStringPlan.Builder er = (ClientWireProtocol.ExplainResponseStringPlan.Builder) sendAndReceive(
				sql, Request.RequestType.EXECUTE_EXPLAIN, 0, false, Optional.of(typeSetter));
		return er.getPlan();
	}

	//Used before version 7.0.1
	//The explain responses are proto instead of strings
	private String explainPlanDeprecated(final String plan, final ClientWireProtocol.ExplainFormat format) throws SQLException
	{
		final ClientWireProtocol.ExplainResponse.Builder er = (ClientWireProtocol.ExplainResponse.Builder) sendAndReceive(
				plan, Request.RequestType.EXPLAIN_PLAN, 0, false, Optional.empty());
		return planProtoToString(er.getPlan(), format);
	}

	// used by CLI
	public String explainPlan(final String plan, final ClientWireProtocol.ExplainFormat format) throws SQLException {

		if(shouldDeprecatedExplain())
		{
			return explainPlanDeprecated(plan, format);
		}

		Function<Object, Void> typeSetter = (Object builder) -> {
			ClientWireProtocol.ExplainPlan.Builder typedBuilder = (ClientWireProtocol.ExplainPlan.Builder) builder;
			typedBuilder.setFormat(format);
			return null;
		};

		final ClientWireProtocol.ExplainResponseStringPlan.Builder er = (ClientWireProtocol.ExplainResponseStringPlan.Builder) sendAndReceive(
				plan, Request.RequestType.EXPLAIN_PLAN, 0, false, Optional.of(typeSetter));
		return er.getPlan();
	}

	public ResultSet executePlan(final String plan) throws SQLException {
		LOGGER.log(Level.INFO, "executePlan()");
		sendAndReceive(plan, Request.RequestType.EXECUTE_PLAN, 0, false, Optional.empty());
		try {
			result = conn.rs = new XGResultSet(conn, fetchSize, this);
		} catch (final Exception e) {
			passUpCancel(false);
			try {
				reconnect();
			} catch (final Exception reconnectException) {
				if (reconnectException instanceof SQLException) {
					throw (SQLException) reconnectException;
				}
				throw SQLStates.newGenericException(reconnectException);
			}
			return executePlan(plan);
		}
		this.updateCount = -1;
		return result;
	}

	public ResultSet executeInlinePlan(final String plan) throws SQLException {
		LOGGER.log(Level.INFO, "executeInlinePlan()");
		sendAndReceive(plan, Request.RequestType.EXECUTE_INLINE_PLAN, 0, false, Optional.empty());
		try {
			result = conn.rs = new XGResultSet(conn, fetchSize, this);
		} catch (final Exception e) {
			passUpCancel(false);
			try {
				reconnect();
			} catch (final Exception reconnectException) {
				if (reconnectException instanceof SQLException) {
					throw (SQLException) reconnectException;
				}
				throw SQLStates.newGenericException(reconnectException);
			}
			return executePlan(plan);
		}
		this.updateCount = -1;
		return result;
	}

	// used by CLI
	public ArrayList<String> listPlan() throws SQLException {
		final ClientWireProtocol.ListPlanResponse.Builder er = (ClientWireProtocol.ListPlanResponse.Builder) sendAndReceive(
				"", Request.RequestType.LIST_PLAN, 0, false, Optional.empty());
		ArrayList<String> planNames = new ArrayList<String>(er.getPlanNameCount());
		for (int i = 0; i < er.getPlanNameCount(); ++i)
			planNames.add(er.getPlanName(i));

		return planNames;
	}

	// used by CLI
	public void cancelQuery(String uuid) throws SQLException {
		final ClientWireProtocol.CancelQueryResponse.Builder er = (ClientWireProtocol.CancelQueryResponse.Builder) sendAndReceive(
				uuid, Request.RequestType.CANCEL_QUERY, 0, false, Optional.empty());
		return;
	}

	public void killQuery(String uuid) throws SQLException {
		final ClientWireProtocol.KillQueryResponse.Builder er = (ClientWireProtocol.KillQueryResponse.Builder) sendAndReceive(
				uuid, Request.RequestType.KILL_QUERY, 0, false, Optional.empty());
		return;
	}

	public ResultSet listAllQueries() throws SQLException {
		final ClientWireProtocol.SystemWideQueriesResponse.Builder er = (ClientWireProtocol.SystemWideQueriesResponse.Builder) sendAndReceive(
				"", Request.RequestType.SYSTEM_WIDE_QUERIES, 0, false, Optional.empty());

		// Manufacture the result set.
		ArrayList<Object> rs = new ArrayList<>(er.getRowsCount());
		for(int i = 0; i < er.getRowsCount(); i++){
			SysQueriesRow row = er.getRows(i);
			ArrayList<Object> newRow = new ArrayList<>();
			newRow.add(row.getQueryId());
			newRow.add(row.getUserid());
			newRow.add(row.getImportance());
			newRow.add(row.getEstimatedTimeSec());
			newRow.add(row.getElapsedTimeSec());
			newRow.add(row.getStatus());
			newRow.add(row.getQueryServer());
			newRow.add(row.getDatabase());
			newRow.add(row.getSqlText());
			rs.add(newRow);
		}
		result = conn.rs = new XGResultSet(conn, rs, this);
		// Map the table metadata
		Map<String, Integer> cols2Pos = new HashMap<String, Integer>();
		TreeMap<Integer, String> pos2Cols = new TreeMap<Integer, String>();
		Map<String, String> cols2Types = new HashMap<String, String>();
		cols2Pos.put("query_id", 0);
		cols2Pos.put("user", 1);
		cols2Pos.put("importance", 2);
		cols2Pos.put("estimated_time", 3);
		cols2Pos.put("elapsed_time", 4);
		cols2Pos.put("status", 5);
		cols2Pos.put("server", 6);
		cols2Pos.put("database", 7);
		cols2Pos.put("sql", 8);

		pos2Cols.put(0, "query_id");
		pos2Cols.put(1, "user");
		pos2Cols.put(2, "importance");
		pos2Cols.put(3, "estimated_time");
		pos2Cols.put(4, "elapsed_time");
		pos2Cols.put(5, "status");
		pos2Cols.put(6, "server");
		pos2Cols.put(7, "database");
		pos2Cols.put(8, "sql");

		cols2Types.put("query_id", "CHAR");
		cols2Types.put("user", "CHAR");
		cols2Types.put("importance", "FLOAT");
		cols2Types.put("estimated_time", "INT");
		cols2Types.put("elapsed_time", "INT");
		cols2Types.put("status", "CHAR");
		cols2Types.put("server", "CHAR");
		cols2Types.put("database", "CHAR");
		cols2Types.put("sql", "CHAR");

		result.setCols2Pos(cols2Pos);
		result.setPos2Cols(pos2Cols);
		result.setCols2Types(cols2Types);

		this.updateCount = -1;
		return result;
	}

	// used by CLI
	public String exportTable(final String table) throws SQLException {
		final ClientWireProtocol.ExecuteExportResponse.Builder er = (ClientWireProtocol.ExecuteExportResponse.Builder) sendAndReceive(
				table, Request.RequestType.EXECUTE_EXPORT, 0, false, Optional.empty());
		return er.getExportStatement();
	}

        // used by CLI
        public String exportTranslation(final String table) throws SQLException {
                final ClientWireProtocol.ExecuteExportResponse.Builder er = (ClientWireProtocol.ExecuteExportResponse.Builder) sendAndReceive(
                                table, Request.RequestType.EXECUTE_EXPORT, 0, false, Optional.empty());
                return er.getExportStatement();
        }

	private ClientWireProtocol.FetchSystemMetadataResponse.Builder fetchSystemMetadata(
			final FetchSystemMetadata.SystemMetadataCall call, final String schema, final String table,
			final String col, final boolean test) throws SQLException {
		LOGGER.log(Level.INFO, "Entered fetchSystemMetadata()");
		clearWarnings();
		if (conn.rs != null && !conn.rs.isClosed()) {
			throw SQLStates.PREVIOUS_RESULT_SET_STILL_OPEN.clone();
		}

		try {
			final FetchSystemMetadata.Builder b1 = FetchSystemMetadata.newBuilder();
			b1.setCall(call);
			// these checks aren't necessary (we know what parameters will be used from the
			// call)
			// but they mean that the has_* methods will be accurate, if we ever care to use
			// them
			if ((schema != null) && (!schema.equals(""))) {
				b1.setSchema(schema);
			} else {
				b1.setSchema("%");
			}
			if ((call == FetchSystemMetadata.SystemMetadataCall.GET_VIEWS) && (table != null) && (!table.equals(""))) {
				b1.setView(table);
			} else if ((table != null) && (!table.equals(""))) {
				b1.setTable(table);
			} else {
				b1.setTable("%");
			}
			if ((col != null) && (!col.equals(""))) {
				b1.setColumn(col);
			}
			b1.setTest(test);
			final Request.Builder b2 = Request.newBuilder();
			b2.setType(Request.RequestType.FETCH_SYSTEM_METADATA);
			b2.setFetchSystemMetadata(b1.build());
			final Request wrapper = b2.build();
			final ClientWireProtocol.FetchSystemMetadataResponse.Builder br = ClientWireProtocol.FetchSystemMetadataResponse
					.newBuilder();
			try {
				conn.out.write(intToBytes(wrapper.getSerializedSize()));
				wrapper.writeTo(conn.out);
				conn.out.flush();

				// get confirmation
				final int length = getLength();
				final byte[] data = new byte[length];
				readBytes(data);
				br.mergeFrom(data);

				final ConfirmationResponse response = br.getResponse();
				final ResponseType rType = response.getType();
				processResponseType(rType, response);

				return br;
			} catch (SQLException | NullPointerException | IOException e) {
				LOGGER.log(Level.WARNING, "fetchSystemMetadataResponse: ", e);
				if (e instanceof SQLException && !SQLStates.UNEXPECTED_EOF.equals((SQLException) e)) {
					throw e;
				}
				if (e instanceof IOException){
					// When its a socket exception like this, the query is not cancelled.
					setQueryCancelled(false);
				}
				passUpCancel(false);
				reconnect(); // try this at most once--if every node is down, report failure
				return fetchSystemMetadata(call, schema, table, col, test);
			}
		} catch (final Exception e) {
			LOGGER.log(Level.WARNING, "fetchSystemMetadataResponse: final ", e);
			if (e instanceof SQLException) {
				throw (SQLException) e;
			}
			throw SQLStates.newGenericException(e);
		}
	}

	public int fetchSystemMetadataInt(final FetchSystemMetadata.SystemMetadataCall call) throws SQLException {
		return fetchSystemMetadata(call, "", "", "", false).getIntVal();
	}

	public ResultSet fetchSystemMetadataResultSet(final FetchSystemMetadata.SystemMetadataCall call,
			final String schema, final String table, final String col, final boolean test) throws SQLException {
		try {
			conn.rs = new XGResultSet(conn, fetchSize, this,
					fetchSystemMetadata(call, schema, table, col, test).getResultSetVal());
			// DatabaseMetaData won't pass on the statement, only the result set,
			// so save any warnings there
			conn.rs.addWarnings(warnings);
			result = conn.rs;
		} catch (final Exception e) {
			LOGGER.log(Level.WARNING, "fetchSystemMetadataResultSet: ", e);
			passUpCancel(false);
			try {
				reconnect();
			} catch (final Exception reconnectException) {
				LOGGER.log(Level.WARNING, "fetchSystemMetadataResultSet: reconnect", reconnectException);
				if (reconnectException instanceof SQLException) {
					throw (SQLException) reconnectException;
				}
				throw SQLStates.newGenericException(reconnectException);
			}
			return fetchSystemMetadataResultSet(call, schema, table, col, test);
		}
		this.updateCount = -1;
		return result;
	}

	public String fetchSystemMetadataString(final FetchSystemMetadata.SystemMetadataCall call) throws SQLException {
		return fetchSystemMetadata(call, "", "", "", false).getStringVal();
	}

	@Override
	public Connection getConnection() throws SQLException {
		LOGGER.log(Level.INFO, "Called getConnection()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getConnection() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return conn;
	}

	@Override
	public int getFetchDirection() throws SQLException {
		LOGGER.log(Level.INFO, "Called getFetchDirection()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getFetchDirection() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return ResultSet.FETCH_FORWARD;
	}

	@Override
	public int getFetchSize() throws SQLException {
		LOGGER.log(Level.INFO, "Called getFetchSize()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getFetchSize() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return fetchSize;
	}

	@Override
	public ResultSet getGeneratedKeys() throws SQLException {
		LOGGER.log(Level.WARNING, "getGeneratedKeys() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	private int getLength() throws Exception {
		int count = 4;
		final byte[] data = new byte[4];
		while (count > 0) {
			final int temp = conn.in.read(data, 4 - count, count);
			if (temp == -1) {
				throw SQLStates.UNEXPECTED_EOF.clone();
			}

			count -= temp;
		}

		return bytesToInt(data);
	}

	@Override
	public int getMaxFieldSize() throws SQLException {
		LOGGER.log(Level.INFO, "Called getMaxFieldSize()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getMaxFieldSize() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		return 0;
	}

	@Override
	public int getMaxRows() throws SQLException {
		LOGGER.log(Level.INFO, "Called getMaxRows()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getMaxRows() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return maxRows;
	}

	@Override
	public boolean getMoreResults() throws SQLException {
		if (closed) {
			LOGGER.log(Level.WARNING, "getMoreResults() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (result != null) {
			result.close();
			result = null;
			dissociateQuery();
		}

		return false;
	}

	@Override
	public boolean getMoreResults(final int current) throws SQLException {
		LOGGER.log(Level.WARNING, "getMoreResults() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public int getQueryTimeout() throws SQLException {
		LOGGER.log(Level.INFO, "Called getQueryTimeout()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getQueryTimeout() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return Math.toIntExact((int) (timeoutMillis / 1000));
	}

	protected long getQueryTimeoutMillis() {
		return timeoutMillis;
	}

	@Override
	public ResultSet getResultSet() throws SQLException {
		LOGGER.log(Level.INFO, "Called getResultSet()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getResultSet() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return result;
	}

	@Override
	public int getResultSetConcurrency() throws SQLException {
		LOGGER.log(Level.INFO, "Called getResultSetConcurrency()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getResultSetConcurrency() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return ResultSet.CONCUR_READ_ONLY;
	}

	@Override
	public int getResultSetHoldability() throws SQLException {
		LOGGER.log(Level.INFO, "Called getResultSetHoldability()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getResultSetHoldability() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return ResultSet.CLOSE_CURSORS_AT_COMMIT;
	}

	@Override
	public int getResultSetType() throws SQLException {
		LOGGER.log(Level.INFO, "Called getResultSetType()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getResultSetType() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return ResultSet.TYPE_FORWARD_ONLY;
	}

	@Override
	public int getUpdateCount() throws SQLException {
		LOGGER.log(Level.INFO, "Called getUpdateCount()");
		if (closed) {
			LOGGER.log(Level.WARNING, "getUpdateCount() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return updateCount;
	}

	@Override
	public SQLWarning getWarnings() throws SQLException {
		LOGGER.log(Level.INFO, "Called getWarnings()");
		if (closed) {

			LOGGER.log(Level.WARNING, "getWarnings() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (warnings.size() == 0) {
			return null;
		}

		final SQLWarning retval = warnings.get(0);
		SQLWarning current = retval;
		int i = 1;
		while (i < warnings.size()) {
			current.setNextWarning(warnings.get(i));
			current = warnings.get(i);
			i++;
		}

		return retval;
	}

	@Override
	public boolean isClosed() throws SQLException {
		LOGGER.log(Level.INFO, "Called isClosed()");
		if (closed) {
			LOGGER.log(Level.INFO, "Returning true from isClosed()");
		} else {
			LOGGER.log(Level.INFO, "Returning false from isClosed()");
		}

		return closed;
	}

	@Override
	public boolean isCloseOnCompletion() throws SQLException {
		LOGGER.log(Level.INFO, "Called isCloseOnCompletion()");
		if (closed) {
			LOGGER.log(Level.WARNING, "isCloseOnCompletion() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return false;
	}

	@Override
	public boolean isPoolable() throws SQLException {
		LOGGER.log(Level.INFO, "Called isPoolable()");
		if (closed) {
			LOGGER.log(Level.WARNING, "isPoolable() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return false;
	}

	@Override
	public boolean isWrapperFor(final Class<?> iface) throws SQLException {
		LOGGER.log(Level.INFO, "Called isWrapperFor()");
		return false;
	}

	private void processResponseType(final ResponseType rType, final ConfirmationResponse response)
			throws SQLException {
		if (rType.equals(ResponseType.INVALID)) {
			LOGGER.log(Level.WARNING, "Server returned an invalid response");
			throw SQLStates.INVALID_RESPONSE_TYPE.clone();
		} else if (rType.equals(ResponseType.RESPONSE_ERROR)) {
			final String reason = response.getReason();
			final String sqlState = response.getSqlState();
			final int code = response.getVendorCode();
			LOGGER.log(Level.WARNING, String.format("Server returned an error response [%s] %s", sqlState, reason));
			throw new SQLException(reason, sqlState, code);
		} else if (rType.equals(ResponseType.RESPONSE_WARN)) {
			LOGGER.log(Level.WARNING, "Server returned a warning response");
			final String reason = response.getReason();
			final String sqlState = response.getSqlState();
			final int code = response.getVendorCode();
			warnings.add(new SQLWarning(reason, sqlState, code));
		}
	}

	private void readBytes(final byte[] bytes) throws Exception {
		int count = 0;
		final int size = bytes.length;
		while (count < size) {
			final int temp = conn.in.read(bytes, count, bytes.length - count);
			if (temp == -1) {
				throw SQLStates.UNEXPECTED_EOF.clone();
			} else {
				count += temp;
			}
		}

		return;
	}

	private void reconnect() throws IOException, SQLException {
		conn.reconnect();
		return;
	}

	private void redirect(final String host, final int port) throws IOException, SQLException {
		conn.redirect(host, port);
		oneShotForce = true;
		conn.clearOneShotForce();
		return;
	}

	private Object sendAndReceive(String sql, final Request.RequestType requestType, final int val,
			final boolean isInMb, final Optional<Function<Object, Void>> additionalPropertySetter) throws SQLException {
		LOGGER.log(Level.INFO, "Entered sendAndReceive()");
		clearWarnings();
		if (conn.rs != null && !conn.rs.isClosed()) {
			throw SQLStates.PREVIOUS_RESULT_SET_STILL_OPEN.clone();
		}
		// Lord forgive us for our reflective ways, an abject abuse of power.
		try {
			Object b1, br;
			Class<?> c;
			Method setWrapped;
			final Request.Builder b2 = Request.newBuilder();
			boolean forceFlag = true;
			boolean redirectFlag = true;
			boolean hasQueryId = false; // set to true if the query ID is encoded in the response message
			switch (requestType) {
			case EXECUTE_QUERY:
				c = ExecuteQuery.class;
				b1 = ExecuteQuery.newBuilder();
				br = ClientWireProtocol.ExecuteQueryResponse.newBuilder();
				setWrapped = b2.getClass().getMethod("setExecuteQuery", c);
				hasQueryId = true;
				break;
			case EXECUTE_EXPLAIN:
				c = ExecuteExplain.class;
				b1 = ExecuteExplain.newBuilder();
				br = shouldDeprecatedExplain() ? ClientWireProtocol.ExplainResponse.newBuilder() : ClientWireProtocol.ExplainResponseStringPlan.newBuilder();
				setWrapped = b2.getClass().getMethod("setExecuteExplain", c);
				break;
			case EXECUTE_UPDATE:
				c = ExecuteUpdate.class;
				b1 = ExecuteUpdate.newBuilder();
				br = ClientWireProtocol.ExecuteUpdateResponse.newBuilder();
				setWrapped = b2.getClass().getMethod("setExecuteUpdate", c);
				break;
			case EXECUTE_PLAN:
				c = ExecutePlan.class;
				b1 = ExecutePlan.newBuilder();
				br = ClientWireProtocol.ExecuteQueryResponse.newBuilder();
				setWrapped = b2.getClass().getMethod("setExecutePlan", c);
				break;
			case EXECUTE_INLINE_PLAN:
				c = ExecuteInlinePlan.class;
				b1 = ExecuteInlinePlan.newBuilder();
				br = ClientWireProtocol.ExecuteQueryResponse.newBuilder();
				setWrapped = b2.getClass().getMethod("setExecuteInlinePlan", c);
				break;
			case EXPLAIN_PLAN:
				c = ExplainPlan.class;
				b1 = ExplainPlan.newBuilder();
				br = shouldDeprecatedExplain() ? ClientWireProtocol.ExplainResponse.newBuilder() : ClientWireProtocol.ExplainResponseStringPlan.newBuilder();
				setWrapped = b2.getClass().getMethod("setExplainPlan", c);
				break;
			case LIST_PLAN:
				c = ListPlan.class;
				b1 = ListPlan.newBuilder();
				br = ClientWireProtocol.ListPlanResponse.newBuilder();
				setWrapped = b2.getClass().getMethod("setListPlan", c);
				forceFlag = false;
				redirectFlag = false;
				break;
			case CANCEL_QUERY:
				c = CancelQuery.class;
				b1 = CancelQuery.newBuilder();
				br = ClientWireProtocol.CancelQueryResponse.newBuilder();
				setWrapped = b2.getClass().getMethod("setCancelQuery", c);
				forceFlag = false;
				redirectFlag = false;
				break;
			case SYSTEM_WIDE_QUERIES:
				c = SystemWideQueries.class;
				b1 = SystemWideQueries.newBuilder();
				br = ClientWireProtocol.SystemWideQueriesResponse.newBuilder();
				setWrapped = b2.getClass().getMethod("setSystemWideQueries", c);
				forceFlag = false;
				redirectFlag = false;
				break;
			case KILL_QUERY:
				c = KillQuery.class;
				b1 = KillQuery.newBuilder();
				br = ClientWireProtocol.KillQueryResponse.newBuilder();
				setWrapped = b2.getClass().getMethod("setKillQuery", c);
				forceFlag = false;
				redirectFlag = false;
				break;
			case EXECUTE_EXPORT:
				c = ExecuteExport.class;
				b1 = ExecuteExport.newBuilder();
				br = ClientWireProtocol.ExecuteExportResponse.newBuilder();
				setWrapped = b2.getClass().getMethod("setExecuteExport", c);
				forceFlag = false;
				redirectFlag = false;
				break;
			default:
				LOGGER.log(Level.WARNING, "sendAndReceive() Internal Error");
				throw SQLStates.INTERNAL_ERROR.clone();
			}
			if (requestType != Request.RequestType.EXECUTE_INLINE_PLAN) {
				//don't touch the statment if this is a plan (proto buffer string plan)
				sql = setParms(sql);
			}

			if (sql.length() > 0) {
				b1.getClass().getMethod("setSql", String.class).invoke(b1, sql);
				if (forceFlag) {
					final Method setForce = b1.getClass().getMethod("setForce", boolean.class);
					setForce.invoke(b1, force);
					if (oneShotForce) {
						setForce.invoke(b1, true);
						oneShotForce = false;
					}
				}
			}

			//Lambda to set properties specific to a message type
			//Not all that nice but better than more reflection
			if(additionalPropertySetter.isPresent())
			{
				additionalPropertySetter.get().apply(b1);
			}

			b2.getClass().getMethod("setType", requestType.getClass()).invoke(b2, requestType);
			setWrapped.invoke(b2, c.cast(b1.getClass().getMethod("build").invoke(b1)));
			final Request wrapper = (Request) b2.getClass().getMethod("build").invoke(b2);
			try {
				conn.out.write(intToBytes(wrapper.getSerializedSize()));
				wrapper.writeTo(conn.out);
				conn.out.flush();
				// get confirmation
				final int length = getLength();
				final byte[] data = new byte[length];
				readBytes(data);
				br.getClass().getMethod("mergeFrom", byte[].class).invoke(br, data);

				final Method getResponse = br.getClass().getMethod("getResponse");
				final ConfirmationResponse response = (ConfirmationResponse) getResponse.invoke(br);
				final ResponseType rType = response.getType();
				processResponseType(rType, response);

				if (redirectFlag) {
					final Method getRedirect = br.getClass().getMethod("getRedirect");
					if ((boolean) getRedirect.invoke(br)) {
						final Method getRedirectHost = br.getClass().getMethod("getRedirectHost");
						final Method getRedirectPort = br.getClass().getMethod("getRedirectPort");
						redirect((String) getRedirectHost.invoke(br), (int) getRedirectPort.invoke(br));
						return sendAndReceive(sql, requestType, val, isInMb, additionalPropertySetter);
					}
				}

				if (hasQueryId) {
					final Method getQueryId = br.getClass().getMethod("getQueryId");
					final String recvQueryId = ((String) getQueryId.invoke(br));
					if (!recvQueryId.isEmpty()) {
						associateQuery(recvQueryId);
					}
				}

				return br;
			} catch (SQLException | NullPointerException |IOException e ) {
				if (e instanceof SQLException && !SQLStates.UNEXPECTED_EOF.equals((SQLException) e)) {
					LOGGER.log(Level.WARNING, "sendAndReceive() SQL or IO Exception.");
					throw e;
				}
				if (e instanceof IOException){
					// When its a socket exception like this, the query is not cancelled.
					setQueryCancelled(false);
				}
				passUpCancel(false);
				reconnect(); // try this at most once--if every node is down, report failure
				return sendAndReceive(sql, requestType, val, isInMb, additionalPropertySetter);
			}
		} catch (final Exception e) {
			if (e instanceof SQLException) {
				LOGGER.log(Level.WARNING, "sendAndReceive() throw SQLException e.");
				throw (SQLException) e;
			}
			LOGGER.log(Level.WARNING, "sendAndReceive() throw new generic exception e");
			throw SQLStates.newGenericException(e);
		}
	}

	@Override
	public void setCursorName(final String name) throws SQLException {
		LOGGER.log(Level.WARNING, "setCursorName() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setEscapeProcessing(final boolean enable) throws SQLException {
		LOGGER.log(Level.WARNING, "setEscapeProcessing() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setFetchDirection(final int direction) throws SQLException {
		LOGGER.log(Level.INFO, "Called setFetchDirection()");
		if (closed) {
			LOGGER.log(Level.WARNING, "setFetchDirection() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (direction != ResultSet.FETCH_FORWARD) {
			LOGGER.log(Level.WARNING, "setFetchDirection() is throwing SQLFeatureNotSupportedException");
			throw new SQLFeatureNotSupportedException();
		}
	}

	@Override
	public void setFetchSize(final int rows) throws SQLException {
		LOGGER.log(Level.INFO, "Called setFetchSize()");
		if (closed) {
			LOGGER.log(Level.WARNING, "setFetchSize() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (rows < 0) {
			LOGGER.log(Level.WARNING, "setFetchSize() is throwing INVALID_ARGUMENT");
			throw SQLStates.INVALID_ARGUMENT.clone();
		}

		if (rows == 0) {
			// switch back to the default settings
			fetchSize = defaultFetchSize;
		} else {
			fetchSize = rows;
		}
	}

	@Override
	public void setMaxFieldSize(final int max) throws SQLException {
		LOGGER.log(Level.WARNING, "setMaxFieldSize() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setMaxRows(final int max) throws SQLException {
		LOGGER.log(Level.INFO, "Called setMaxRows()");
		if (closed) {
			LOGGER.log(Level.WARNING, "setMaxRows() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		maxRows = max;
	}

	private String setParms(final String in) throws SQLException {
		if (parms.size() == 0)
		{
			return in;
		}
		
		String out = "";
		int x = 0;
		int i = 0;
		boolean quoted = false;
		int quoteType = 0;
		final int size = in.length();
		while (i < size) {
			if ((in.charAt(i) != '\'' && in.charAt(i) != '"') || (in.charAt(i) == '\'' && quoteType == 2)
					|| (in.charAt(i) == '"' && quoteType == 1)) {
				if (!quoted) {
					if (in.charAt(i) == '?') {
						try {
							final Object parm = parms.get(x);

							// System.out.println("parm type: " + parm.getClass());

							if (parm == null) {
								out += "NULL";
							} else if (parm instanceof String) {
								out += ("'" + ((String) parm).replace("'", "''") + "'");
							} else if (parm instanceof Timestamp) {
								final SimpleDateFormat format = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss.SSS");
								final TimeZone utc = TimeZone.getTimeZone("UTC");
								format.setTimeZone(utc);
								GregorianCalendar cal = new GregorianCalendar();
								cal.setGregorianChange(new java.util.Date(Long.MIN_VALUE));
								format.setCalendar(cal);
								out += ("TIMESTAMP('" + format.format((Timestamp) parm) + "')");
							} else if (parm instanceof Boolean) {
								// System.out.println("inside BOOLEAN set param");
								out += ("BOOLEAN('" + parm + "')");
							} else if (parm instanceof byte[]) {
								out += ("BINARY('0x" + bytesToHex((byte[]) parm) + "')");
							} else if (parm instanceof Date) {
								final SimpleDateFormat format = new SimpleDateFormat("yyyy-MM-dd");
								final TimeZone utc = TimeZone.getTimeZone("UTC");
								format.setTimeZone(utc);
								GregorianCalendar cal = new GregorianCalendar();
								cal.setGregorianChange(new java.util.Date(Long.MIN_VALUE));
								format.setCalendar(cal);
								out += ("DATE('" + format.format((Date) parm) + "')");
							} else if (parm instanceof Time) {
								final SimpleDateFormat format = new SimpleDateFormat("HH:mm:ss.SSS");
								final TimeZone utc = TimeZone.getTimeZone("UTC");
								format.setTimeZone(utc);
								GregorianCalendar cal = new GregorianCalendar();
								cal.setGregorianChange(new java.util.Date(Long.MIN_VALUE));
								format.setCalendar(cal);
								out += ("TIME('" + format.format((Time) parm) + "')");
							} else if (parm instanceof Byte) {
								out += ("BYTE(" + parm + ")");
							} else if (parm instanceof Short) {
								out += ("SMALLINT(" + parm + ")");
							} else if (parm instanceof Integer) {
								out += ("INT(" + parm + ")");
							} else if (parm instanceof Float) {
								out += ("FLOAT(" + parm + ")");
							} else if (parm instanceof Long || parm instanceof Double) {
								out += parm;
							} else if (parm instanceof BigDecimal) {
								out += ("DECIMAL(" + parm + ", " + ((BigDecimal) parm).precision() + ", "
										+ ((BigDecimal) parm).scale() + ")");
							} else {
								throw new SQLFeatureNotSupportedException();
							}
						} catch (final IndexOutOfBoundsException e) {
							throw SQLStates.INVALID_PARAMETER_MARKER.clone();
						}

						x++;
					} else {
						out += in.charAt(i);
					}
				} else {
					out += in.charAt(i);
				}
			} else {
				if (quoteType == 0) {
					if (in.charAt(i) == '\'' && ((i + 1) == in.length() || in.charAt(i + 1) != '\'')) {
						quoteType = 1;
						quoted = true;
						out += '\'';
					} else if (in.charAt(i) == '"' && ((i + 1) == in.length() || in.charAt(i + 1) != '"')) {
						quoteType = 2;
						quoted = true;
						out += '"';
					} else {
						out += in.charAt(i);
						out += in.charAt(i + 1);
						i++;
					}
				} else if (quoteType == 1) {
					if (in.charAt(i) == '\'' && ((i + 1) == in.length() || in.charAt(i + 1) != '\'')) {
						quoteType = 0;
						quoted = false;
						out += '\'';
					} else if (in.charAt(i) == '"') {
						out += '"';
					} else {
						out += "''";
						i++;
					}
				} else {
					if (in.charAt(i) == '"' && ((i + 1) == in.length() || in.charAt(i + 1) != '"')) {
						quoteType = 0;
						quoted = false;
						out += '"';
					} else if (in.charAt(i) == '\'') {
						out += '\'';
					} else {
						out += "\"\"";
						i++;
					}
				}
			}

			i++;
		}

		return out;
	}

	@Override
	public void setPoolable(final boolean poolable) throws SQLException {
		LOGGER.log(Level.WARNING, "setPoolable() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setQueryTimeout(final int seconds) throws SQLException {
		LOGGER.log(Level.INFO, "Called setQueryTimeout()");
		if (closed) {
			LOGGER.log(Level.WARNING, "setQueryTimeout() is throwing CALL_ON_CLOSED_OBJECT");
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		if (seconds < 0) {
			LOGGER.log(Level.WARNING, "setQueryTimeout() is throwing SQLWarning");
			throw new SQLWarning(String.format("timeout value must be non-negative, was: %s", seconds));
		}
		timeoutMillis = seconds * 1000;
		LOGGER.log(Level.FINE, "Query timeout set to {} seconds", seconds);
	}

	@Override
	public <T> T unwrap(final Class<T> iface) throws SQLException {
		LOGGER.log(Level.WARNING, "unwrap() was called, which is not supported");
		throw new SQLFeatureNotSupportedException();
	}
	/*!
	 * New functions which have been moved from the CLI into the driver.
	 * TODO: move some of these utility functions into another file to clean this up a bit.
	 */

	// Generate a regex for an unquoted alphanumeric ([a-zA-Z0-9_]) or quoted free
	// (.) token. Reluctant.
	// Do not insert multiple regexes for tokens of the same name (or "q0" + another
	// name) into a single pattern.
	private static String tk(String name) {
		return "(?<q0" + name + ">\"?)(?<" + name + ">(\\w+?|(?<=\").+?(?=\")))\\k<q0" + name + ">";
	}

	// Get a token from its generated regex according to SQL case-sensitivity rules
	// (sensitive iff quoted).
	// Do not call on a matcher that has not yet called matches().
	private static String getTk(Matcher m, String name, String def) {
		if (m.group(name) == null) {
			return def;
		}
		if (m.group("q0" + name).length() == 0) {
			return m.group(name).toLowerCase();
		}
		return m.group(name);
	}

	private static Pattern listTablesSyntax = Pattern.compile("list\\s+tables(?<verbose>\\s+verbose)?",
			Pattern.CASE_INSENSITIVE);

	private static Pattern listSystemTablesSyntax = Pattern.compile("list\\s+system\\s+tables(?<verbose>\\s+verbose)?",
			Pattern.CASE_INSENSITIVE);

	private ResultSet listTables(final String cmd, boolean isSystemTables) throws SQLException{
		LOGGER.log(Level.INFO, "Entered driver's listTables()");
		ResultSet rs = null;

		final Matcher m = isSystemTables ? listSystemTablesSyntax.matcher(cmd) : listTablesSyntax.matcher(cmd);
		if (!m.matches()) {
			// this line will never be reached,
			// but we have to call matches() anyway
			LOGGER.log(Level.WARNING, "Driver's listTables() reached a line it shouldn't have.");
			return rs;
		}
		final DatabaseMetaData dbmd = conn.getMetaData();
		if (isSystemTables) {
			final XGDatabaseMetaData xgdbmd = (XGDatabaseMetaData) dbmd;
			rs = xgdbmd.getSystemTables("", "%", "%", new String[0]);
		} else {
			rs = dbmd.getTables("", "%", "%", new String[0]);
		}
		return rs;
	}

	private static Pattern listViewsSyntax = Pattern.compile("list\\s+views(?<verbose>\\s+verbose)?",
			Pattern.CASE_INSENSITIVE);

	private ResultSet listViews(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO, "Entered driver's listViews()");
		ResultSet rs = null;

		final Matcher m = listViewsSyntax.matcher(cmd);
		if (!m.matches()) {
			// this line will never be reached,
			// but we have to call matches() anyway
			LOGGER.log(Level.WARNING, "Driver's listViews() reached a line it shouldn't have.");
			return rs;
		}
		final DatabaseMetaData md = conn.getMetaData();
		final XGDatabaseMetaData dbmd = (XGDatabaseMetaData) md;

		return dbmd.getViews("", "%", "%", new String[0]);
	}

	private static Pattern listIndexesSyntax = Pattern.compile(
			"list\\s+ind(ic|ex)es\\s+((" + tk("schema") + ")\\.)?(" + tk("table") + ")(?<verbose>\\s+verbose)?",
			Pattern.CASE_INSENSITIVE);

	private ResultSet listIndexes(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO, "Entered driver's listIndexes()");
		ResultSet rs = null;
		final Matcher m = listIndexesSyntax.matcher(cmd);
	
		if (!m.matches()) {
			throw SQLStates.SYNTAX_ERROR.cloneAndSpecify(
					"Syntax: list indexes (<schema>.)?<table>");
		}
		final DatabaseMetaData dbmd = conn.getMetaData();
		return dbmd.getIndexInfo("", getTk(m, "schema", conn.getSchema()), getTk(m, "table", null), false, false);
	}

	private ResultSet getSchema() throws SQLException{
		LOGGER.log(Level.INFO, "Entered driver's getSchema()");
		String schema = conn.getSchema();
		// Construct the result set.
		// split the proto string using the line break delimiter and build a one string
		// column resultset.
		ArrayList<Object> rs = new ArrayList<>();
		String lines[] = schema.split("\\r?\\n");
		for (int i = 0; i < lines.length; i++) {
			String str = lines[i];
			ArrayList<Object> row = new ArrayList<>();
			row.add(str);
			rs.add(row);
		}
		result = conn.rs = new XGResultSet(conn, rs, this);

		Map<String, Integer> cols2Pos = new HashMap<String, Integer>();
		TreeMap<Integer, String> pos2Cols = new TreeMap<Integer, String>();
		Map<String, String> cols2Types = new HashMap<String, String>();
		cols2Pos.put("schema", 0);
		pos2Cols.put(0, "schema");
		cols2Types.put("schema", "CHAR");
		result.setCols2Pos(cols2Pos);
		result.setPos2Cols(pos2Cols);
		result.setCols2Types(cols2Types);

		return result;
	}

	private static Pattern describeTableSyntax = Pattern.compile(
			"describe(\\s+table\\s+)?((" + tk("schema") + ")\\.)?(" + tk("table") + ")(?<verbose>\\s+verbose)?",
			Pattern.CASE_INSENSITIVE);

	private ResultSet describeTable(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO, "Entered driver's describeTable()");
		ResultSet rs = null;
		final Matcher m = describeTableSyntax.matcher(cmd);
		if (!m.matches()) {
			throw SQLStates.SYNTAX_ERROR.cloneAndSpecify(
					"Syntax: describe (<schema>.)?<table>");
		}
		final DatabaseMetaData dbmd = conn.getMetaData();
		return dbmd.getColumns("", getTk(m, "schema", conn.getSchema()), getTk(m, "table", null), "%");
	}

	private static Pattern describeViewSyntax = Pattern.compile(
		"describe(\\s+view\\s+)?((" + tk("schema") + ")\\.)?(" + tk("view") + ")(?<verbose>\\s+verbose)?",
		Pattern.CASE_INSENSITIVE);

	private ResultSet describeView(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO, "Entered driver's describeView()");
		ResultSet rs = null;
		final Matcher m = describeViewSyntax.matcher(cmd);
		if (!m.matches()) {
			throw SQLStates.SYNTAX_ERROR.cloneAndSpecify(
					"Syntax: describe view (<schema>.)?<view>");
		}
		final DatabaseMetaData md = conn.getMetaData();
		final XGDatabaseMetaData dbmd = (XGDatabaseMetaData) md;
		return dbmd.getViews("", getTk(m, "schema", conn.getSchema()), getTk(m, "view", null), null);
	}

	private ResultSet executePlanSQL(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO, "Entered driver's executePlan()");
		ResultSet rs = null;
		String plan = cmd.substring("PLAN EXECUTE ".length()).trim();

		if(startsWithIgnoreCase(plan, "INLINE ")){
			plan = plan.substring("INLINE ".length()).trim();
			rs = executeInlinePlan(plan);
		} else {
			rs = executePlan(plan);
		}
		return rs;
	}

	private ResultSet explainPlanSQL(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO, "Entered driver's explainPlan()");
		String plan = cmd.substring("PLAN EXPLAIN ".length()).trim();
		ClientWireProtocol.ExplainFormat format = ClientWireProtocol.ExplainFormat.PROTO;
		if (startsWithIgnoreCase(plan, "JSON ")) {
			plan = plan.substring("JSON ".length()).trim();
			format = ClientWireProtocol.ExplainFormat.JSON;
		}
		String pm = explainPlan(plan, format);
		ArrayList<Object> rs = new ArrayList<>();
		ArrayList<Object> row = new ArrayList<>();
		row.add(pm);
		rs.add(row);

		result = conn.rs = new XGResultSet(conn, rs, this);
		Map<String, Integer> cols2Pos = new HashMap<String, Integer>();
		TreeMap<Integer, String> pos2Cols = new TreeMap<Integer, String>();
		Map<String, String> cols2Types = new HashMap<String, String>();
		cols2Pos.put("explain", 0);
		pos2Cols.put(0, "explain");
		cols2Types.put("explain", "CHAR");
		result.setCols2Pos(cols2Pos);
		result.setPos2Cols(pos2Cols);
		result.setCols2Types(cols2Types);

		return result;
	}

	private ResultSet exportTableSQL(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO, "Enetered driver's exportTable");
		String exportStr = exportTable(cmd);
		ArrayList<Object> rs = new ArrayList<>();
		ArrayList<Object> row = new ArrayList<>();
		row.add(exportStr);
		rs.add(row);
	
		result = conn.rs = new XGResultSet(conn, rs, this);
		Map<String, Integer> cols2Pos = new HashMap<String, Integer>();
		TreeMap<Integer, String> pos2Cols = new TreeMap<Integer, String>();
		Map<String, String> cols2Types = new HashMap<String, String>();
		cols2Pos.put("export", 0);
		pos2Cols.put(0, "export");
		cols2Types.put("export", "CHAR");
		result.setCols2Pos(cols2Pos);
		result.setPos2Cols(pos2Cols);
		result.setCols2Types(cols2Types);

		return result;
	}

	private ResultSet exportTranslationSQL(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO, "Enetered driver's exportTranslation");
		String exportTranslationStr = exportTranslation(cmd);
		ArrayList<Object> rs = new ArrayList<>();
		ArrayList<Object> row = new ArrayList<>();
		row.add(exportTranslationStr);
		rs.add(row);
	
		result = conn.rs = new XGResultSet(conn, rs, this);
		Map<String, Integer> cols2Pos = new HashMap<String, Integer>();
		TreeMap<Integer, String> pos2Cols = new TreeMap<Integer, String>();
		Map<String, String> cols2Types = new HashMap<String, String>();
		cols2Pos.put("translation", 0);
		pos2Cols.put(0, "translation");
		cols2Types.put("translation", "CHAR");
		result.setCols2Pos(cols2Pos);
		result.setPos2Cols(pos2Cols);
		result.setCols2Types(cols2Types);

		return result;
	}

	private ResultSet explainSQL(final String cmd) throws SQLException {
		LOGGER.log(Level.INFO, "Entered Driver's explainSQL()");

		ClientWireProtocol.ExplainFormat format;
		String sql = "";

		if(startsWithIgnoreCase(cmd, "EXPLAIN JSON")){
			format = ClientWireProtocol.ExplainFormat.JSON;
			sql = cmd.substring("EXPLAIN JSON".length()).trim();
		} else {
			format = ClientWireProtocol.ExplainFormat.PROTO;
			sql = cmd.substring("EXPLAIN".length()).trim();
		}
		String explainString = explain(sql, format);

		ArrayList<Object> rs = new ArrayList<>();
		ArrayList<Object> row = new ArrayList<>();
		row.add(explainString);
		rs.add(row);

		result = conn.rs = new XGResultSet(conn, rs, this);
		Map<String, Integer> cols2Pos = new HashMap<String, Integer>();
		TreeMap<Integer, String> pos2Cols = new TreeMap<Integer, String>();
		Map<String, String> cols2Types = new HashMap<String, String>();
		cols2Pos.put("explain", 0);
		pos2Cols.put(0, "explain");
		cols2Types.put("explain", "CHAR");
		result.setCols2Pos(cols2Pos);
		result.setPos2Cols(pos2Cols);
		result.setCols2Types(cols2Types);

		return result;
	}

	/*!
	 * Non result set custom functions.
	 * The int values returned by these functions will indicate the number of modifed rows.
	 */

	private int killCancelQuery(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO,"Entered driver's killCancelQuery()");
		String uuid;
		if (startsWithIgnoreCase(cmd, "KILL ")) {
			uuid = cmd.substring("KILL ".length()).trim();
			killQuery(uuid);
		} else {
			// Cancel
			uuid = cmd.substring("CANCEL ".length()).trim();
			cancelQuery(uuid);
		}
		return 0;

	}

	private int setMaxRowsSQL(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO,"Entered driver's setMaxRows()");
		final int maxRow = Integer.parseInt(cmd.substring("SET MAXROWS ".length()).trim());
		setMaxRows(maxRow);
		return 0;
	}

	private int setSchema(final String cmd) throws SQLException{
		LOGGER.log(Level.INFO,"Entered driver's setSchema()");
		String schema = cmd.substring(11).trim();
		if (schema.startsWith("\"")) {
			if (!schema.endsWith("\"")) {
			throw SQLStates.SYNTAX_ERROR.cloneAndSpecify(
					"Uncloseed Quotes!");
			}

			schema = schema.substring(1, schema.length() - 1);
		}
		conn.setSchema(schema);
		return 0;
	}

}
