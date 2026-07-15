/*
 * Licensed to Julian Hyde under one or more contributor license
 * agreements.  See the NOTICE file distributed with this work
 * for additional information regarding copyright ownership.
 * Julian Hyde licenses this file to you under the Apache
 * License, Version 2.0 (the "License"); you may not use this
 * file except in compliance with the License.  You may obtain a
 * copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.  See the License for the specific
 * language governing permissions and limitations under the
 * License.
 */
package net.hydromatic.morel;

import static java.util.Objects.requireNonNull;
import static net.hydromatic.morel.util.Characters.isHexDigit;
import static net.hydromatic.morel.util.Static.last;
import static net.hydromatic.morel.util.Static.skipLast;
import static net.hydromatic.morel.util.Static.str;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.util.concurrent.Runnables;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.StringReader;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Consumer;
import javax.sql.DataSource;
import net.hydromatic.morel.ast.AstNode;
import net.hydromatic.morel.ast.Pos;
import net.hydromatic.morel.compile.CompileException;
import net.hydromatic.morel.compile.CompiledStatement;
import net.hydromatic.morel.compile.Compiles;
import net.hydromatic.morel.compile.Environment;
import net.hydromatic.morel.compile.Environments;
import net.hydromatic.morel.compile.Tracer;
import net.hydromatic.morel.compile.Tracers;
import net.hydromatic.morel.eval.Code;
import net.hydromatic.morel.eval.Codes;
import net.hydromatic.morel.eval.Prop;
import net.hydromatic.morel.eval.Session;
import net.hydromatic.morel.foreign.Calcite;
import net.hydromatic.morel.foreign.DataSet;
import net.hydromatic.morel.foreign.ForeignValue;
import net.hydromatic.morel.parse.MorelParseException;
import net.hydromatic.morel.parse.MorelParserImpl;
import net.hydromatic.morel.type.Binding;
import net.hydromatic.morel.type.TypeSystem;
import net.hydromatic.morel.util.JavaVersion;
import net.hydromatic.morel.util.MorelException;
import net.hydromatic.morel.util.Pair;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.sql.SqlDialect;
import org.apache.calcite.sql.dialect.ClickHouseSqlDialect;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.jline.reader.EndOfFileException;
import org.jline.reader.LineReader;
import org.jline.reader.LineReaderBuilder;
import org.jline.reader.MaskingCallback;
import org.jline.reader.ParsedLine;
import org.jline.reader.Parser;
import org.jline.reader.UserInterruptException;
import org.jline.reader.impl.DefaultParser;
import org.jline.terminal.Attributes;
import org.jline.terminal.Terminal;
import org.jline.terminal.TerminalBuilder;
import org.jline.utils.AttributedStringBuilder;
import org.jline.utils.AttributedStyle;
import org.jline.utils.NonBlockingReader;

/** Command shell for ML, powered by JLine3. */
public class Shell {
  private final ConfigImpl config;
  private final Terminal terminal;

  /**
   * Command-line entry point.
   *
   * @param args Command-line arguments
   */
  public static void main(String[] args) {
    try {
      final Config config =
          parse(
              ConfigImpl.DEFAULT.withDirectory(
                  new File(System.getProperty("user.dir"))),
              ImmutableList.copyOf(args));
      final Shell main = create(config, System.in, System.out);
      main.run();
    } catch (Throwable e) {
      e.printStackTrace();
      System.exit(1);
    }
  }

  /** Creates a Shell. */
  public static Shell create(
      List<String> args, InputStream in, OutputStream out) throws IOException {
    final Config config = parse(ConfigImpl.DEFAULT, args);
    return create(config, in, out);
  }

  /** Creates a Shell. */
  public static Shell create(Config config, InputStream in, OutputStream out)
      throws IOException {
    final TerminalBuilder builder = TerminalBuilder.builder();
    builder.streams(in, out);
    final ConfigImpl configImpl = (ConfigImpl) config;
    builder.system(configImpl.system);
    builder.dumb(configImpl.dumb);
    if (configImpl.dumb) {
      builder.type("dumb");
    }
    final Terminal terminal = builder.build();
    return new Shell(config, terminal);
  }

  /** Creates a Shell. */
  public Shell(Config config, Terminal terminal) {
    this.config = (ConfigImpl) config;
    this.terminal = terminal;
  }

  /** Parses an argument list to an equivalent Config. */
  public static Config parse(Config config, List<String> argList) {
    ConfigImpl c = (ConfigImpl) config;
    // Use LinkedHashMap so that later --foreign= entries overwrite earlier
    // ones; duplicate keys are allowed (last-wins).
    final Map<String, ForeignValue> valueMapBuilder = new LinkedHashMap<>();
    for (int i = 0; i < argList.size(); i++) {
      String arg = argList.get(i);
      if (arg.equals("--banner=false")) {
        c = c.withBanner(false);
      }
      if (arg.equals("--terminal=dumb")) {
        c = c.withDumb(true);
      }
      if (arg.equals("--echo")) {
        c = c.withEcho(true);
      }
      if (arg.equals("--help")) {
        c = c.withHelp(true);
      }
      if (arg.equals("--system=false")) {
        c = c.withSystem(false);
      }
      if (arg.startsWith("--foreign=")) {
        final String className = arg.substring("--foreign=".length());
        @SuppressWarnings("unchecked")
        final Map<String, DataSet> map = instantiate(className, Map.class);
        valueMapBuilder.putAll(Calcite.withDataSets(map).foreignValues());
      }
      if (arg.startsWith("--directory=")) {
        final String directoryPath = arg.substring("--directory=".length());
        c = c.withDirectory(new File(directoryPath));
      }
      if (arg.startsWith("--maxUseDepth=")) {
        int maxUseDepth =
            Integer.parseInt(arg.substring("--maxUseDepth=".length()));
        c = c.withMaxUseDepth(maxUseDepth);
      }
      if (arg.equals("-e") || arg.equals("--eval")) {
        if (i + 1 < argList.size()) {
          c = c.withEval(argList.get(++i));
        }
      }
      if (arg.startsWith("--eval=")) {
        c = c.withEval(arg.substring("--eval=".length()));
      }
      if (arg.startsWith("--color-scheme=")) {
        c = c.withColorScheme(arg.substring("--color-scheme=".length()));
      }
      if (arg.startsWith("--dialect=")) {
        c = c.withDialect(arg.substring("--dialect=".length()));
      }
      if (arg.startsWith("--jdbc=")) {
        c = c.withJdbc(arg.substring("--jdbc=".length()));
      }
      if (arg.startsWith("--materialize=")) {
        c = c.withMaterialize(arg.substring("--materialize=".length()));
      }
      if (arg.startsWith("--output=")) {
        c = c.withOutput(arg.substring("--output=".length()));
      }
      if (arg.startsWith("--file=")) {
        c = c.withFile(arg.substring("--file=".length()));
      }
      if (arg.endsWith(".sml") && !arg.startsWith("--")) {
        c = c.withFile(arg);
      }
    }

    return c.withValueMap(ImmutableMap.copyOf(valueMapBuilder));
  }

  static void usage(Consumer<String> outLines) {
    String[] usageLines = {
      "Usage: java " + Shell.class.getName() + " [options]",
      "",
      "Options:",
      "  -e, --eval <expr>   Evaluate expression and exit",
      "  --dialect=<name>    Print the expression as SQL (only 'clickhouse')",
      "  --file=<f.sml>      Read the expression from a file",
      "  --jdbc=<url|schema> Connect to a JDBC source (or CLICKHOUSE_* env)",
      "  --materialize=<t>   CREATE TABLE <t> AS the generated SQL",
      "  --output=<name>     Create an incremental pipeline targeting <name>",
      "  --help              Print this help",
    };
    Arrays.asList(usageLines).forEach(outLines);
  }

  static void help(Consumer<String> outLines) {
    String[] helpLines = {
      "List of available commands:",
      "    help   Print this help",
      "    quit   Quit shell",
    };
    Arrays.asList(helpLines).forEach(outLines);
  }

  /** Evaluates a single expression and prints the result. */
  private void runEval() {
    if (config.sql.dialect != null) {
      runToSql();
      return;
    }
    final TypeSystem typeSystem = new TypeSystem();
    final Map<Prop, Object> map = new LinkedHashMap<>();
    Prop.DIRECTORY.set(map, config.directory);
    Prop.SCRIPT_DIRECTORY.set(map, config.directory);
    final Session session = new Session(map, typeSystem);
    Environment env = Environments.env(typeSystem, session, config.valueMap);

    String code = config.eval;
    // Ensure the code ends with a semicolon
    if (!code.trim().endsWith(";")) {
      code = code + ";";
    }

    try {
      final MorelParserImpl smlParser =
          new MorelParserImpl(new StringReader(code));
      smlParser.zero("eval");
      final AstNode statement = smlParser.statementSemicolonSafe();
      final List<CompileException> warningList = new ArrayList<>();
      final Tracer tracer = Tracers.empty();
      final CompiledStatement compiled =
          Compiles.prepareStatement(
              typeSystem,
              session,
              env,
              statement,
              null,
              warningList::add,
              tracer);
      final List<Binding> bindings = new ArrayList<>();
      compiled.eval(session, env, terminal.writer()::println, bindings::add);
      warningList.forEach(w -> terminal.writer().println(w.description()));
    } catch (MorelParseException | CompileException e) {
      terminal.writer().println(e.description());
    }
    terminal.writer().flush();
  }

  /**
   * Compiles an expression to SQL in the configured dialect and prints the
   * result.
   *
   * <p>Uses the HYBRID compilation path so that overloaded operators are fully
   * resolved before generating the Calcite relational plan.
   */
  private void runToSql() {
    final SqlDialect dialect = resolveDialect(config.sql.dialect);
    final TypeSystem typeSystem = new TypeSystem();
    final Session session = newHybridSession(typeSystem);
    final Calcite calcite = newCalcite();
    final String code = readSource();
    if (code == null) {
      return;
    }
    try {
      final List<CompileException> warningList = new ArrayList<>();
      final CompiledStatement compiled =
          compileLast(code, typeSystem, session, calcite, warningList);
      warningList.forEach(w -> terminal.writer().println(w.description()));
      if (compiled != null) {
        final Code plan = compiled.getCode();
        final RelNode rel = plan == null ? null : Calcite.extractRelNode(plan);
        if (rel != null) {
          final String sql = calcite.toSql(rel, dialect);
          if (config.sql.materialize != null) {
            materialize(calcite, config.sql.materialize, sql);
          } else {
            terminal.writer().println(sql);
          }
        } else {
          terminal
              .writer()
              .println(
                  "Expression cannot be converted to SQL"
                      + (plan == null ? " (no code)" : ""));
        }
      }
    } catch (MorelParseException | CompileException e) {
      terminal.writer().println(e.description());
    } catch (RuntimeException e) {
      terminal.writer().println("Error: " + e);
    }
    terminal.writer().flush();
  }

  /**
   * Compiles an expression and creates an incremental DBSP pipeline in
   * ClickHouse via JDBC; without a JDBC connection, prints the DDL.
   */
  private void runIncrementalPipeline() {
    // Incremental pipelines are only generated for ClickHouse.
    final SqlDialect dialect = ClickHouseSqlDialect.DEFAULT;
    final String targetName = requireNonNull(config.sql.output);
    final TypeSystem typeSystem = new TypeSystem();
    final Session session = newHybridSession(typeSystem);
    final Calcite calcite = newCalcite();
    final String code = readSource();
    if (code == null) {
      return;
    }
    try {
      final List<CompileException> warningList = new ArrayList<>();
      final CompiledStatement compiled =
          compileLast(code, typeSystem, session, calcite, warningList);
      warningList.forEach(w -> terminal.writer().println(w.description()));
      if (compiled != null) {
        final Code plan = compiled.getCode();
        final RelNode rel = plan == null ? null : Calcite.extractRelNode(plan);
        if (rel == null) {
          terminal
              .writer()
              .println(
                  "Expression cannot be converted to SQL"
                      + (plan == null ? " (no code)" : ""));
        } else {
          final List<String> ddls =
              calcite.toIncrementalDdl(rel, dialect, targetName);
          final DataSource ds = calcite.getDataSource();
          if (ds == null) {
            // No JDBC connection; print the DDL instead of executing it.
            ddls.forEach(ddl -> terminal.writer().println(ddl + ";\n"));
          } else {
            try (Connection conn = ds.getConnection();
                Statement stmt = conn.createStatement()) {
              for (String ddl : ddls) {
                stmt.execute(ddl);
              }
            }
            terminal.writer().println("Pipeline: " + targetName);
          }
        }
      }
    } catch (MorelParseException | CompileException e) {
      terminal.writer().println(e.description());
    } catch (SQLException e) {
      terminal.writer().println("JDBC error: " + e.getMessage());
    } catch (RuntimeException e) {
      terminal.writer().println("Error: " + e);
    }
    terminal.writer().flush();
  }

  /**
   * Creates the Calcite instance for the configured JDBC source, or an empty
   * one when {@code --jdbc} is absent.
   */
  private Calcite newCalcite() {
    if (config.sql.jdbc == null) {
      return Calcite.withDataSets(ImmutableMap.of());
    }
    if (config.sql.jdbc.startsWith("jdbc:")) {
      return Calcite.withJdbc(config.sql.jdbc, extractSchema(config.sql.jdbc));
    }
    // --jdbc=<schema> reads the connection from CLICKHOUSE_* environment
    // variables
    return Calcite.withJdbcFromEnv(config.sql.jdbc);
  }

  /**
   * Creates a session on the HYBRID compilation path, so that relational
   * expressions become Calcite plans.
   */
  private Session newHybridSession(TypeSystem typeSystem) {
    final Map<Prop, Object> propMap = new LinkedHashMap<>();
    Prop.DIRECTORY.set(propMap, config.directory);
    Prop.SCRIPT_DIRECTORY.set(propMap, config.directory);
    Prop.HYBRID.set(propMap, true);
    return new Session(propMap, typeSystem);
  }

  /**
   * Reads the source program from {@code --file} or {@code -e} (ensuring the
   * latter ends with a semicolon); null, with a message printed, if neither is
   * available or the file cannot be read.
   */
  private @Nullable String readSource() {
    if (config.sql.file != null) {
      try {
        return Files.readString(Paths.get(config.sql.file));
      } catch (IOException e) {
        terminal.writer().println("Cannot read file: " + e.getMessage());
        terminal.writer().flush();
        return null;
      }
    }
    if (config.eval != null) {
      final String eval = config.eval;
      return eval.trim().endsWith(";") ? eval : eval + ";";
    }
    terminal.writer().println("--dialect requires -e or a .sml file");
    terminal.writer().flush();
    return null;
  }

  /**
   * Parses the source, evaluates all statements but the last to build up the
   * environment, and returns the last statement compiled in that environment;
   * null, with a message printed, if the source contains no statements.
   */
  private @Nullable CompiledStatement compileLast(
      String code,
      TypeSystem typeSystem,
      Session session,
      Calcite calcite,
      List<CompileException> warningList) {
    final MorelParserImpl parser = new MorelParserImpl(new StringReader(code));
    parser.zero("eval");
    final List<AstNode> statements = new ArrayList<>();
    for (; ; ) {
      final AstNode statement = parser.statementSemicolonOrEofSafe();
      if (statement == null) {
        break;
      }
      statements.add(statement);
    }
    if (statements.isEmpty()) {
      terminal.writer().println("No statements found");
      return null;
    }
    final Map<String, ForeignValue> allForeign =
        new LinkedHashMap<>(config.valueMap);
    allForeign.putAll(calcite.foreignValues());
    Environment env = Environments.env(typeSystem, session, allForeign);
    final Tracer tracer = Tracers.empty();
    for (AstNode statement : skipLast(statements)) {
      final CompiledStatement compiled =
          Compiles.prepareStatement(
              typeSystem,
              session,
              env,
              statement,
              calcite,
              warningList::add,
              tracer);
      final List<Binding> bindings = new ArrayList<>();
      compiled.eval(session, env, line -> {}, bindings::add);
      env = env.bindAll(bindings);
    }
    return Compiles.prepareStatement(
        typeSystem,
        session,
        env,
        last(statements),
        calcite,
        warningList::add,
        tracer);
  }

  /** Resolves a dialect name to a {@link SqlDialect}. */
  private static SqlDialect resolveDialect(@Nullable String name) {
    if (name == null) {
      return ClickHouseSqlDialect.DEFAULT;
    }
    switch (name.toLowerCase()) {
      case "clickhouse":
        return ClickHouseSqlDialect.DEFAULT;
      default:
        throw new IllegalArgumentException(
            "Unknown dialect: " + name + "; supported: clickhouse");
    }
  }

  /**
   * Materializes a query result as a new table by executing {@code CREATE TABLE
   * ... AS SELECT} via JDBC.
   */
  private void materialize(
      Calcite calcite, String tableSpec, String selectSql) {
    final DataSource ds = calcite.getDataSource();
    if (ds == null) {
      terminal.writer().println("--materialize requires --jdbc");
      return;
    }
    final String ddl =
        "CREATE TABLE IF NOT EXISTS " + tableSpec + " AS\n" + selectSql;
    try (Connection conn = ds.getConnection();
        Statement stmt = conn.createStatement()) {
      stmt.execute(ddl);
      // Extract table name (first word of tableSpec)
      final String tableName = tableSpec.split("\\s+")[0];
      terminal.writer().println("Created " + tableName);
    } catch (SQLException e) {
      terminal.writer().println("Materialization failed: " + e.getMessage());
    }
  }

  /**
   * Extracts the schema/database name from a JDBC URL.
   *
   * <p>For example, from {@code jdbc:clickhouse://host:8123/mydb} extracts
   * {@code "mydb"}.
   */
  private static String extractSchema(String url) {
    // Find the first '/' after the authority ("jdbc:x://host:port/db");
    // without this, "jdbc:x://host:port" would yield "host:port".
    final int authority = url.indexOf("://");
    final int lastSlash =
        url.lastIndexOf('/') > (authority < 0 ? -1 : authority + 2)
            ? url.lastIndexOf('/')
            : -1;
    if (lastSlash >= 0 && lastSlash < url.length() - 1) {
      String tail = url.substring(lastSlash + 1);
      // Remove query parameters if any
      int q = tail.indexOf('?');
      if (q >= 0) {
        tail = tail.substring(0, q);
      }
      if (!tail.isEmpty()) {
        return tail;
      }
    }
    return "default";
  }

  /**
   * Pauses after creating the terminal.
   *
   * <p>Calls the value set by {@link Config#withPauseFn(Runnable)} which, for
   * the default config, does nothing; the instance used in testing pauses for a
   * few milliseconds, which gives classes time to load and makes test
   * deterministic.
   */
  protected final void pause() {
    config.pauseFn.run();
  }

  /**
   * Returns whether we can ignore a line. We can ignore a line if it consists
   * only of comments, spaces, and optionally semicolon, and if we are not on a
   * continuation line.
   */
  private static boolean canIgnoreLine(StringBuilder buf, String line) {
    final String trimmedLine =
        line.replaceAll("\\(\\*.*\\*\\)", "")
            .replaceAll("\\(\\*\\) .*$", "")
            .trim();
    return buf.length() == 0
        && (trimmedLine.isEmpty() || trimmedLine.equals(";"));
  }

  /**
   * Returns the file where command history is stored, {@code ~/.morel/history},
   * creating the {@code ~/.morel} directory if necessary. Returns null (and
   * prints a warning) if the directory cannot be created, in which case history
   * is not persisted between sessions.
   */
  private @Nullable Path historyFile() {
    final Path morelHome = Paths.get(System.getProperty("user.home"), ".morel");
    try {
      Files.createDirectories(morelHome);
    } catch (IOException e) {
      terminal
          .writer()
          .println("Warning: cannot create " + morelHome + ": " + e);
      return null;
    }
    return morelHome.resolve("history");
  }

  public void run() {
    if (config.help) {
      usage(terminal.writer()::println);
      return;
    }

    if (config.sql.output != null) {
      if (config.sql.jdbc == null) {
        terminal.writer().println("--output requires --jdbc");
      } else if (config.eval == null && config.sql.file == null) {
        terminal.writer().println("--output requires -e or --file");
      } else {
        runIncrementalPipeline();
      }
      terminal.writer().flush();
      return;
    }

    if (config.eval != null) {
      runEval();
      return;
    }

    if (config.sql.file != null && config.sql.dialect != null) {
      runToSql();
      return;
    }

    final Parser parser =
        new DefaultParser() {
          {
            // Only double quotes delimit a literal; a single quote is part of
            // an identifier or type variable (e.g. 'a), not a quote.
            setQuoteChars(new char[] {'"'});
            setEofOnUnclosedQuote(true);
            setEofOnUnclosedBracket(
                DefaultParser.Bracket.CURLY,
                DefaultParser.Bracket.ROUND,
                DefaultParser.Bracket.SQUARE);
          }

          @Override
          public ParsedLine parse(
              String line, int cursor, ParseContext context) {
            // Remove from "(*)" to end of line, if present
            if (line.matches(".*\\(\\*\\).*")) {
              line = line.replaceAll("\\(\\*\\).*$", "");
            }
            return super.parse(line, cursor, context);
          }
        };

    final String equalsPrompt =
        new AttributedStringBuilder()
            .style(AttributedStyle.DEFAULT.bold())
            .append("=")
            .style(AttributedStyle.DEFAULT)
            .append(" ")
            .toAnsi(terminal);
    final String minusPrompt =
        new AttributedStringBuilder()
            .style(AttributedStyle.DEFAULT.bold())
            .append("-")
            .style(AttributedStyle.DEFAULT)
            .append(" ")
            .toAnsi(terminal);

    if (config.banner) {
      terminal.writer().println(JavaVersion.banner(this.terminal));
    }
    final TypeSystem typeSystem = new TypeSystem();
    final Map<Prop, Object> map = new LinkedHashMap<>();
    Prop.DIRECTORY.set(map, config.directory);
    Prop.SCRIPT_DIRECTORY.set(map, config.directory);
    if (config.colorScheme != null) {
      Prop.COLOR_SCHEME.set(map, config.colorScheme);
    }
    // Query the terminal's background now, while it is idle, and record it.
    final String background = queryTerminalBackground(terminal);
    if (background != null) {
      Prop.TERMINAL_BACKGROUND.set(map, background);
    }
    final Session session = new Session(map, typeSystem);

    final LineReaderBuilder lineReaderBuilder =
        LineReaderBuilder.builder()
            .appName("morel")
            .terminal(terminal)
            .parser(parser)
            .highlighter(new ShellHighlighter(session))
            .variable(LineReader.SECONDARY_PROMPT_PATTERN, equalsPrompt);
    final Path historyFile = historyFile();
    if (historyFile != null) {
      // Persist command history across sessions in ~/.morel/history.
      lineReaderBuilder.variable(LineReader.HISTORY_FILE, historyFile);
    }
    LineReader lineReader = lineReaderBuilder.build();

    pause();
    Environment env = Environments.env(typeSystem, session, config.valueMap);
    final LineFn lineFn =
        new TerminalLineFn(minusPrompt, equalsPrompt, lineReader);
    final SubShell subShell =
        new SubShell(
            1,
            config.maxUseDepth,
            lineFn,
            config.echo,
            typeSystem,
            env,
            terminal.writer()::println,
            session,
            config.directory);
    final Map<String, Binding> bindings = new LinkedHashMap<>();
    subShell.extracted(bindings);
  }

  /**
   * Determines the terminal's background color, reading the {@code NO_COLOR},
   * {@code TERM} and {@code COLORFGBG} environment variables, and delegates to
   * {@link #queryTerminalBackground(Terminal, String, String, String)}.
   *
   * <p>This method is <b>the only one in the shell that reads the
   * environment.</b> Because {@link System#getenv} returns process-wide mutable
   * state, this method is not deterministic and is awkward to unit-test in
   * isolation; the real logic lives in the sibling method, which takes the
   * three environment values as parameters and never calls {@code getenv}. Keep
   * new environment reads out of the rest of the shell and funnel them through
   * here.
   *
   * @see #queryTerminalBackground(Terminal, String, String, String)
   */
  private static @Nullable String queryTerminalBackground(Terminal terminal) {
    final @Nullable String noColor = System.getenv("NO_COLOR");
    final @Nullable String term = System.getenv("TERM");
    final @Nullable String colorFgBg = System.getenv("COLORFGBG");
    return queryTerminalBackground(terminal, noColor, term, colorFgBg);
  }

  /**
   * Determines the terminal's background color and returns it as an {@code
   * "rgb:RRRR/GGGG/BBBB"} string (each channel 1 to 4 hexadecimal digits), or
   * null if color is disabled or the background cannot be determined.
   *
   * <p>The environment is passed in as {@code noColor}, {@code term} and {@code
   * colorFgBg} (the values of {@code NO_COLOR}, {@code TERM} and {@code
   * COLORFGBG}); this method never calls {@link System#getenv}, so it is
   * deterministic and testable. Its environment-reading sibling {@link
   * #queryTerminalBackground(Terminal)} supplies the values in production.
   *
   * <p>Returns null if {@code noColor} is set, or the terminal is dumb ({@code
   * term} is {@code "dumb"} or the terminal's type is dumb). Otherwise, it
   * queries the terminal (OSC 11, see {@link #queryOsc11Background}); if the
   * terminal does not answer, it falls back to the background implied by {@code
   * colorFgBg}, defaulting to a dark background.
   *
   * <p>The result is stored in the {@link Prop#TERMINAL_BACKGROUND} property.
   * When the {@code colorScheme} property is unset it is used to deduce the
   * color scheme (see {@link
   * net.hydromatic.morel.util.ColorScheme#deduce(String)}).
   *
   * <p>Must be called while the terminal is idle, before the line reader runs:
   * the query does raw-mode terminal I/O, so it cannot run later, from the
   * highlighter, while JLine owns the terminal.
   */
  static @Nullable String queryTerminalBackground(
      Terminal terminal,
      @Nullable String noColor,
      @Nullable String term,
      @Nullable String colorFgBg) {
    if (noColor != null) {
      return null;
    }
    final String type = terminal.getType();
    if (type == null
        || type.startsWith(Terminal.TYPE_DUMB)
        || "dumb".equals(term)) {
      return null;
    }
    final String rgb = queryOsc11Background(terminal);
    if (rgb != null) {
      return rgb;
    }
    // The terminal did not answer; fall back to the background implied by
    // COLORFGBG (form "fg;bg", e.g. "0;15"), treating a background of 7 or 15
    // (white or bright white) as light and everything else — including an
    // absent or unparsable value — as dark.
    if (colorFgBg != null) {
      final String[] parts = colorFgBg.split(";");
      try {
        final int bg = Integer.parseInt(parts[parts.length - 1].trim());
        if (bg == 7 || bg == 15) {
          return "rgb:ffff/ffff/ffff";
        }
      } catch (NumberFormatException e) {
        // fall through to the dark default
      }
    }
    return "rgb:0000/0000/0000";
  }

  /**
   * Queries the terminal for its background color using the OSC 11 escape
   * sequence and returns the reply as an {@code "rgb:RRRR/GGGG/BBBB"} string,
   * or null if the terminal does not support the query or does not respond
   * promptly. Does raw-mode terminal I/O but does not read the environment.
   */
  private static @Nullable String queryOsc11Background(Terminal terminal) {
    Attributes savedAttributes = null;
    try {
      savedAttributes = terminal.enterRawMode();
      // Ask the terminal for its background color. The reply is
      // "ESC ] 11 ; rgb:RRRR/GGGG/BBBB" terminated by BEL or ST (ESC \).
      terminal.writer().write("\033]11;?\033\\");
      terminal.writer().flush();
      final NonBlockingReader reader = terminal.reader();
      final StringBuilder buf = new StringBuilder();
      while (buf.length() < 64) {
        final int c = reader.read(200L);
        if (c < 0 || c == 0x07) {
          break; // timeout, end of stream, or BEL terminator
        }
        if (c == '\\'
            && buf.length() > 0
            && buf.charAt(buf.length() - 1) == '\033') {
          break; // ST terminator (ESC \)
        }
        buf.append((char) c);
      }
      // Extract "rgb:RRRR/GGGG/BBBB", dropping the OSC prefix and terminator.
      final String response = buf.toString();
      final int i = response.indexOf("rgb:");
      if (i < 0) {
        return null;
      }
      int end = i + 4;
      while (end < response.length()
          && (response.charAt(end) == '/'
              || isHexDigit(response.charAt(end)))) {
        end++;
      }
      return response.substring(i, end);
    } catch (IOException e) {
      return null;
    } finally {
      if (savedAttributes != null) {
        terminal.setAttributes(savedAttributes);
      }
    }
  }

  /**
   * Instantiates a class.
   *
   * <p>Assumes that the class has a public no-arguments constructor.
   */
  private static <T> T instantiate(
      String className,
      @SuppressWarnings("SameParameterValue") Class<T> clazz) {
    try {
      final Class<?> aClass = Class.forName(className);
      return clazz.cast(aClass.getConstructor().newInstance());
    } catch (ClassNotFoundException
        | NoSuchMethodException
        | InstantiationException
        | InvocationTargetException
        | IllegalAccessException e) {
      throw new RuntimeException("Cannot load class: " + className, e);
    }
  }

  /** Shell configuration. */
  @SuppressWarnings("unused")
  public interface Config {
    Config DEFAULT = ConfigImpl.DEFAULT;

    Config withBanner(boolean banner);

    Config withDumb(boolean dumb);

    Config withSystem(boolean system);

    Config withEcho(boolean echo);

    Config withHelp(boolean help);

    Config withValueMap(Map<String, ForeignValue> valueMap);

    Config withDirectory(File directory);

    Config withPauseFn(Runnable runnable);

    Config withMaxUseDepth(int maxUseDepth);

    Config withEval(@Nullable String eval);

    Config withColorScheme(@Nullable String colorScheme);

    Config withDialect(@Nullable String dialect);

    Config withJdbc(@Nullable String jdbc);

    Config withMaterialize(@Nullable String materialize);

    Config withOutput(@Nullable String output);

    Config withFile(@Nullable String file);
  }

  /** Implementation of {@link Config}. */
  private static class ConfigImpl implements Config {
    private final boolean banner;
    private final boolean dumb;
    private final boolean echo;
    private final boolean help;
    private final boolean system;
    private final ImmutableMap<String, ForeignValue> valueMap;
    private final File directory;
    private final Runnable pauseFn;
    private final int maxUseDepth;
    private final @Nullable String eval;
    private final @Nullable String colorScheme;
    private final SqlConfig sql;

    static final ConfigImpl DEFAULT =
        new ConfigImpl(
            true,
            false,
            true,
            false,
            false,
            ImmutableMap.of(),
            new File(""),
            Runnables.doNothing(),
            -1,
            null,
            null,
            SqlConfig.DEFAULT);

    private ConfigImpl(
        boolean banner,
        boolean dumb,
        boolean system,
        boolean echo,
        boolean help,
        ImmutableMap<String, ForeignValue> valueMap,
        File directory,
        Runnable pauseFn,
        int maxUseDepth,
        @Nullable String eval,
        @Nullable String colorScheme,
        SqlConfig sql) {
      this.banner = banner;
      this.dumb = dumb;
      this.system = system;
      this.echo = echo;
      this.help = help;
      this.valueMap = requireNonNull(valueMap, "valueMap");
      this.directory = requireNonNull(directory, "directory");
      this.pauseFn = requireNonNull(pauseFn, "pauseFn");
      this.maxUseDepth = maxUseDepth;
      this.eval = eval;
      this.colorScheme = colorScheme;
      this.sql = requireNonNull(sql, "sql");
    }

    @Override
    public ConfigImpl withBanner(boolean banner) {
      if (this.banner == banner) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withDumb(boolean dumb) {
      if (this.dumb == dumb) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withSystem(boolean system) {
      if (this.system == system) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withEcho(boolean echo) {
      if (this.echo == echo) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withHelp(boolean help) {
      if (this.help == help) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withValueMap(Map<String, ForeignValue> valueMap) {
      if (this.valueMap.equals(valueMap)) {
        return this;
      }
      final ImmutableMap<String, ForeignValue> immutableValueMap =
          ImmutableMap.copyOf(valueMap);
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          immutableValueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withDirectory(File directory) {
      if (this.directory.equals(directory)) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public Config withPauseFn(Runnable pauseFn) {
      if (this.pauseFn.equals(pauseFn)) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withMaxUseDepth(int maxUseDepth) {
      if (this.maxUseDepth == maxUseDepth) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withEval(@Nullable String eval) {
      if (Objects.equals(this.eval, eval)) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withColorScheme(@Nullable String colorScheme) {
      if (Objects.equals(this.colorScheme, colorScheme)) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    /** Creates a copy of this config with a new SQL-mode configuration. */
    private ConfigImpl withSql(SqlConfig sql) {
      if (this.sql == sql) {
        return this;
      }
      return new ConfigImpl(
          banner,
          dumb,
          system,
          echo,
          help,
          valueMap,
          directory,
          pauseFn,
          maxUseDepth,
          eval,
          colorScheme,
          sql);
    }

    @Override
    public ConfigImpl withDialect(@Nullable String dialect) {
      return withSql(sql.withDialect(dialect));
    }

    @Override
    public ConfigImpl withJdbc(@Nullable String jdbc) {
      return withSql(sql.withJdbc(jdbc));
    }

    @Override
    public ConfigImpl withMaterialize(@Nullable String materialize) {
      return withSql(sql.withMaterialize(materialize));
    }

    @Override
    public ConfigImpl withOutput(@Nullable String output) {
      return withSql(sql.withOutput(output));
    }

    @Override
    public ConfigImpl withFile(@Nullable String file) {
      return withSql(sql.withFile(file));
    }
  }

  /**
   * Configuration of the SQL-generation modes: {@code --dialect}, {@code
   * --jdbc}, {@code --materialize} (CREATE TABLE AS over the JDBC source),
   * {@code --output} (incremental pipeline target), and {@code --file}.
   */
  private static class SqlConfig {
    static final SqlConfig DEFAULT =
        new SqlConfig(null, null, null, null, null);

    final @Nullable String dialect;
    final @Nullable String jdbc;
    final @Nullable String materialize;
    final @Nullable String output;
    final @Nullable String file;

    private SqlConfig(
        @Nullable String dialect,
        @Nullable String jdbc,
        @Nullable String materialize,
        @Nullable String output,
        @Nullable String file) {
      this.dialect = dialect;
      this.jdbc = jdbc;
      this.materialize = materialize;
      this.output = output;
      this.file = file;
    }

    SqlConfig withDialect(@Nullable String dialect) {
      return Objects.equals(this.dialect, dialect)
          ? this
          : new SqlConfig(dialect, jdbc, materialize, output, file);
    }

    SqlConfig withJdbc(@Nullable String jdbc) {
      return Objects.equals(this.jdbc, jdbc)
          ? this
          : new SqlConfig(dialect, jdbc, materialize, output, file);
    }

    SqlConfig withMaterialize(@Nullable String materialize) {
      return Objects.equals(this.materialize, materialize)
          ? this
          : new SqlConfig(dialect, jdbc, materialize, output, file);
    }

    SqlConfig withOutput(@Nullable String output) {
      return Objects.equals(this.output, output)
          ? this
          : new SqlConfig(dialect, jdbc, materialize, output, file);
    }

    SqlConfig withFile(@Nullable String file) {
      return Objects.equals(this.file, file)
          ? this
          : new SqlConfig(dialect, jdbc, materialize, output, file);
    }
  }

  /**
   * Abstraction of a terminal's line reader. Can read lines from an input
   * (terminal or file) and categorize the lines.
   */
  interface LineFn {
    Pair<LineType, String> read(StringBuilder buf);
  }

  /** Type of line from {@link LineFn}. */
  enum LineType {
    QUIT,
    EOF,
    INTERRUPT,
    IGNORE,
    HELP,
    REGULAR
  }

  /**
   * Simplified shell that works in both interactive mode (where input and
   * output is a terminal) and batch mode (where input is a file, and output is
   * to an array of lines).
   */
  static class SubShell {
    private final int depth;
    private final int maxDepth;
    private final LineFn lineFn;
    private final boolean echo;
    private final TypeSystem typeSystem;
    private final Environment env;
    private final Consumer<String> outLines;
    private final Session session;
    private final File directory;

    SubShell(
        int depth,
        int maxDepth,
        LineFn lineFn,
        boolean echo,
        TypeSystem typeSystem,
        Environment env,
        Consumer<String> outLines,
        Session session,
        File directory) {
      this.depth = depth;
      this.maxDepth = maxDepth;
      this.lineFn = lineFn;
      this.echo = echo;
      this.typeSystem = typeSystem;
      this.env = env;
      this.outLines = outLines;
      this.session = session;
      this.directory = directory;
    }

    void extracted(@Nullable Map<String, Binding> outBindings) {
      final StringBuilder buf = new StringBuilder();
      final Map<String, Binding> bindingMap = new LinkedHashMap<>();
      final List<Binding> bindings = new ArrayList<>();
      Environment env1 = env;
      for (; ; ) {
        final Pair<LineType, String> line = lineFn.read(buf);
        switch (line.left) {
          case EOF:
          case QUIT:
            return;

          case IGNORE:
            continue;

          case HELP:
            help(outLines);
            buf.append(line.right).append("\n");
            break;

          case REGULAR:
            try {
              buf.append(line.right);
              if (line.right.endsWith(";")) {
                final String code = str(buf);
                final MorelParserImpl smlParser =
                    new MorelParserImpl(new StringReader(code));
                final AstNode statement;
                try {
                  smlParser.zero("stdIn");
                  statement = smlParser.statementSemicolonSafe();
                  final Environment env0 = env1;
                  final List<CompileException> warningList = new ArrayList<>();
                  final Tracer tracer = Tracers.empty();
                  final CompiledStatement compiled =
                      Compiles.prepareStatement(
                          typeSystem,
                          session,
                          env0,
                          statement,
                          null,
                          warningList::add,
                          tracer);
                  final Use shell = new Use(env0, bindingMap);
                  session.withShell(
                      shell,
                      outLines,
                      session1 ->
                          compiled.eval(
                              session1, env0, outLines, bindings::add));
                  warningList.forEach(
                      w -> {
                        final StringBuilder buf2 = new StringBuilder();
                        shell.handle(w, buf2);
                        outLines.accept(buf2.toString());
                      });
                  bindings.forEach(b -> bindingMap.put(b.id.name, b));
                  env1 = env0.bindAll(bindingMap.values());
                  if (outBindings != null) {
                    outBindings.putAll(bindingMap);
                  }
                  bindingMap.clear();
                  bindings.clear();
                } catch (MorelParseException | CompileException e) {
                  outLines.accept(e.description());
                }
                if (echo) {
                  outLines.accept(code);
                }
              } else {
                buf.append("\n");
              }
            } catch (IllegalArgumentException e) {
              outLines.accept(e.getMessage());
            }
        }
      }
    }

    /** Implementation of the "use" function. */
    private class Use implements Session.Shell {
      private final Environment env;
      private final Map<String, Binding> bindings;

      Use(Environment env, Map<String, Binding> bindings) {
        this.env = env;
        this.bindings = bindings;
      }

      @Override
      public void use(String fileName, boolean silent, Pos pos) {
        outLines.accept("[opening " + fileName + "]");
        File file = new File(fileName);
        if (!file.isAbsolute()) {
          file = new File(directory, fileName);
        }
        if (!file.exists()) {
          outLines.accept(
              "[use failed: Io: openIn failed on "
                  + fileName
                  + ", No such file or directory]");
          throw new Codes.MorelRuntimeException(Codes.BuiltInExn.ERROR, pos);
        }
        if (depth > maxDepth && maxDepth >= 0) {
          outLines.accept(
              "[use failed: Io: openIn failed on "
                  + fileName
                  + ", Too many open files]");
          throw new Codes.MorelRuntimeException(Codes.BuiltInExn.ERROR, pos);
        }
        try (FileReader fileReader = new FileReader(file);
            BufferedReader bufferedReader = new BufferedReader(fileReader)) {
          final SubShell subShell =
              new SubShell(
                  depth + 1,
                  maxDepth,
                  new ReaderLineFn(bufferedReader),
                  false,
                  typeSystem,
                  env,
                  outLines,
                  session,
                  directory);
          subShell.extracted(bindings);
        } catch (IOException e) {
          e.printStackTrace();
        }
      }

      @Override
      public void handle(RuntimeException e, StringBuilder buf) {
        if (depth != 1) {
          throw e;
        }
        if (e instanceof MorelException) {
          ((MorelException) e).describe(buf);
        } else {
          buf.append(e);
        }
      }
    }
  }

  /** Implementation of {@link LineFn} that reads from a reader. */
  static class ReaderLineFn implements LineFn {
    private final BufferedReader reader;

    ReaderLineFn(BufferedReader reader) {
      this.reader = reader;
    }

    @Override
    public Pair<LineType, String> read(StringBuilder buf) {
      try {
        final String line = reader.readLine();
        if (line == null) {
          return Pair.of(LineType.EOF, "");
        }
        if (canIgnoreLine(buf, line)) {
          return Pair.of(LineType.IGNORE, "");
        }
        return Pair.of(LineType.REGULAR, line);
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }
  }

  /**
   * Implementation of {@link LineFn} that reads from JLine's terminal. It is
   * used for interactive sessions.
   */
  private static class TerminalLineFn implements LineFn {
    private final String minusPrompt;
    private final String equalsPrompt;
    private final LineReader lineReader;

    TerminalLineFn(
        String minusPrompt, String equalsPrompt, LineReader lineReader) {
      this.minusPrompt = minusPrompt;
      this.equalsPrompt = equalsPrompt;
      this.lineReader = lineReader;
    }

    @Override
    public Pair<LineType, String> read(StringBuilder buf) {
      final String line;
      try {
        final String prompt = buf.length() == 0 ? minusPrompt : equalsPrompt;
        final String rightPrompt = null;
        line =
            lineReader.readLine(
                prompt, rightPrompt, (MaskingCallback) null, null);
      } catch (UserInterruptException e) {
        return Pair.of(LineType.INTERRUPT, "");
      } catch (EndOfFileException e) {
        return Pair.of(LineType.EOF, "");
      }

      if (canIgnoreLine(buf, line)) {
        return Pair.of(LineType.IGNORE, "");
      }

      if (line.equalsIgnoreCase("quit") || line.equalsIgnoreCase("exit")) {
        return Pair.of(LineType.QUIT, "");
      }

      final ParsedLine pl = lineReader.getParser().parse(line, 0);
      if ("help".equals(pl.word()) || "?".equals(pl.word())) {
        return Pair.of(LineType.HELP, "");
      }
      return Pair.of(LineType.REGULAR, pl.line());
    }
  }
}

// End Shell.java
