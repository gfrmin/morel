<!--
{% comment %}
Licensed to Julian Hyde under one or more contributor license
agreements.  See the NOTICE file distributed with this work
for additional information regarding copyright ownership.
Julian Hyde licenses this file to you under the Apache
License, Version 2.0 (the "License"); you may not use this
file except in compliance with the License.  You may obtain a
copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing,
software distributed under the License is distributed on an
"AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied.  See the License for the specific
language governing permissions and limitations under the
License.
{% endcomment %}
-->

# Claude Code Notes

This file provides guidance to Claude Code (claude.ai/code) when working
with code in this repository.

## Overview

Morel is a Standard ML interpreter with relational extensions,
implemented in Java. It allows users to write Standard ML code with
SQL-like query expressions to operate on in-memory data structures.
The project uses Apache Calcite for query optimization and planning.

## Fork context (read first)

This repository is a fork of `hydromatic/morel`. `origin` is
`github.com/gfrmin/morel`; `upstream` is `github.com/hydromatic/morel`.

- **Branches:** `main` mirrors `upstream/main`. The long-lived `clickhouse`
  branch is the daily-driver dev branch and the default branch to work on.
- **Purpose:** use Morel as a rigorous, typed, relational-algebra front end to
  replace dbt/SQL for transformation over ClickHouse. North star: the *compiler*
  chooses materialization (no `materialized=` hints), with DBSP-style incremental
  view maintenance compiled to ClickHouse-native objects.

**STANDING DIRECTIVE (do not violate without explicit instruction):** only keep
`clickhouse` aligned with upstream. Anything *new* (the fork features below, or
further ideas) is discussed with the maintainer (Julian Hyde) **before**
upstreaming — do **not** open upstream PRs unilaterally. When realigning, prefer
merge (preserve the daily-driver history); `./mvnw install` must be green before
any push; get explicit confirmation before pushing.

### Fork-only features (not in upstream), with entry points

- **SQL generation:** `Calcite.toSql(RelNode, SqlDialect)`, `--dialect=clickhouse`,
  routed through the HYBRID compile path (`Shell.runToSql`, `Ml.assertSql`,
  `Calcite.extractRelNode`). Commits `5a25f91`, `2d38f05`.
- **Nested-record field-name fix** in `CalciteCompiler.translate` for TUPLE
  (use `tuple.type().argNames()`, not ordinal "0"/"1"). Manifests **only** in
  generated SQL text — plain Calcite execution resolves fields by ordinal.
  Commits `c93e132`, `fd0fa33`.
- **`--jdbc`** + JDBC schema discovery + `CLICKHOUSE_*` env credentials
  (`Calcite.withJdbc`, `JdbcCalcite`). Commits `f15b6d0`, `c65442a`, `dc4a3e8`.
- **`--materialize`** (`CREATE TABLE AS` over the JDBC source). Commit `dc4a3e8`.
- **File input** (`--file` / `.sml` in dialect mode). Commit `4c024f7`.
  Known limit: intermediate `val` bindings over JDBC tables can't be referenced
  by the final SQL-generating expression (RelList binding field-name resolution).
- **DBSP → ClickHouse native objects** (`--jdbc … --output …`): incremental MVs +
  `AggregatingMergeTree`/`MergeTree` targets. Commit `b2fd2df`. Early prototype.
- **Relational aggregates** `argMax`/`argMin` (`96c41fb`, fork-only, **abandoned** —
  per-column reduction yields chimera rows), `maxBy`/`minBy` (`8714418`, whole-row
  dedup). Hyde **upstreamed `maxBy`/`minBy` in #390** (2026-06-07), citing `8714418`
  by hash. The principled design is post-`group` `order`+`take` ⇒ `ROW_NUMBER() OVER
  (…)` (the n=1 case = `maxBy`/`minBy`), aligned with #280/#290; whether ROW_NUMBER is
  even the right model vs. Measures (Discussion **#344**) is the open question — settle
  with Hyde on #390 / #344 before extending.

### Known Morel limitations / upstream issues to raise (verified 2026-06-03)

- **#139** (open, *Type deduction for records*) — function-parameter flex-record
  inference: `fun singleUnitItems items = from i in items where i.units = 1` fails
  with `unresolved flex record (can't tell what fields there are besides #units)`
  (`TypeResolver.java:290–296` applied-selector path; `:783–788` bare-selector).
  Hyde's own canonical repro is `fun hasJob e job = e.job = job` (ClassCastException).
  Blocks reusable typed transformations over records; engage *on #139*. Kin to
  **#375**. (Was tracked here as #175, which closed 2026-06-06 — that issue was only
  the misleading *message* for a typo'd field name, not parameter inference.)
- **Calcite interpreter wrong answers** on set-ops — correctness bug. NEW / unfiled.
  Disabled tests at `AlgebraTest.java:252–259`. Narrower than "all multi-operand":
  multi-operand `union` (line 248) and *literal* multi-operand `intersect` (line 250)
  are enabled and correct; only **chained `except`** and **any set-op whose operand
  is a subquery** diverge. Native (HYBRID=false) is correct; Calcite (HYBRID=true)
  is wrong. E.g. `from i in [1,2,3] except [2,5,4], [2,1,6]` ⇒ native `[3]`, Calcite ≠.
- **#299** (open) — declaring a function whose arg could be `list` or `bag`
  throws `UnsupportedOperationException`. Relevant to `elem`/`notelem` overloads.
- **#357** (open) — position-less type errors (`Cannot deduce type: no valid
  overloads` at `0.0-0.0`).
- **`morel` launcher bug** — `FILES="$FILES $1"` (lines 133/137) accrues a leading
  space, then expands inconsistently: quoted `"$FILES"` at 203/230, unquoted `$FILES`
  at 210. Two `.smli` args collapse because a `*.smli` arg flips `SUBCMD` execute→smli
  (130–132), routing them to the **quoted `"$FILES"` at line 203** (one token, leading
  space) — *not* the unquoted line 210, which actually word-splits correctly (it only
  breaks on names with spaces/globs). NEW / unfiled. Fix with a bash array
  (`FILES=()` / `FILES+=("$1")` / `"${FILES[@]}"`) at all three sites.
- **`.smli` ScriptTest** — the old `from`→`rom` first-character claim is **STALE**:
  not reproducible on `clickhouse` after the harness rewrite in `9430af3` (#334);
  verified across 7 scenarios, first char preserved (`Main.java:533–535` strips only a
  leading `\n`, never a letter). Keep one blank line between top-level statements as
  defensive style, but do **not** file a character-eating bug. Real residual artifacts
  (minor): regenerated `.out` gains a spurious trailing blank line, and a statement
  with no pre-existing `>` output line regenerates no output (`command()` emits only
  when `expectedOutput != null`, `Main.java:720–766`).

### Fork conventions

- **Build gate:** `./mvnw install` is the real pre-commit gate — the `fullMake`
  command referenced later in this file does **not** exist on this machine. Read
  pass/fail from a log file, not inline stdout.
- **Never** verify with `./morel <path>` (the wrapper mangles a path argument);
  use the ScriptTest harness — it is the only ground truth.
- `.smli` editing: one blank line between every top-level statement; never
  hand-write golden output (copy from
  `target/test-classes/script/surefire/script/<f>.smli` after a failing run).
- Morel commits on this fork omit the `Co-Authored-By` trailer.

## Build and Test Commands

### Building
```bash
./mvnw install              # Full build with all checks
./mvnw verify               # Compile and run tests
./mvnw compile              # Compile only
```

### Running Tests
```bash
./mvnw test                 # Run all tests
./mvnw test -Dtest=MainTest # Run specific test class
./mvnw test -Dtest=MainTest#testRepl # Run specific test method

# Run individual .smli script test files
./morel src/test/resources/script/wordle.smli

# Run individual script with visible output (for debugging)
# The --echo flag shows test output to stdout in real-time
./morel --echo src/test/resources/script/wordle.smli
```

### Running the Shell
```bash
./morel                     # Start interactive REPL
./morel -e '1 + 2'          # Evaluate expression and exit
```

### Code Quality
```bash
./mvnw checkstyle:check     # Run checkstyle
./mvnw javadoc:javadoc      # Generate javadoc
```

Note: The build uses Google Java Format automatically during the
`process-sources` phase. Checkstyle runs in the same phase.

## Architecture

Morel follows a traditional interpreter pipeline:
Parse → Type Check → Compile → Evaluate.

### Core Components

**Parser (`net.hydromatic.morel.parse`)**
- `MorelParser.jj`: JavaCC grammar for Standard ML plus extensions
- `MorelParserImpl`: Generated parser implementation
- Produces AST (`Ast` nodes)

**AST Layer (`net.hydromatic.morel.ast`)**
- `Ast`: User-facing abstract syntax tree from parser
- `Core`: Internal representation after type resolution
- `AstBuilder`, `CoreBuilder`: Fluent builders for constructing nodes
- `Visitor`, `Shuttle`: Tree traversal patterns

**Type System (`net.hydromatic.morel.type`)**
- `TypeSystem`: Central registry for types
- `Type` hierarchy: `PrimitiveType`, `RecordType`, `TupleType`,
  `ListType`, `FnType`, `DataType`, `TypeVar`, etc.
- `TypeVar`: Polymorphic type variables (parametric polymorphism)
- `TypeUnifier`: Hindley-Milner type inference using unification
- `Binding`: Associates names with types and values

**Compilation (`net.hydromatic.morel.compile`)**
- `TypeResolver`: Type inference and checking; converts `Ast` to `Core`
- `Compiler`: Compiles typed `Core` expressions into executable `Code`
- `Environment`: Symbol table holding bindings
- `BuiltIn`: Defines all built-in functions, operators, and types
- `CalciteCompiler`: Translates relational expressions to Calcite plans
- `Resolver`: Resolves names and converts patterns to code

**Evaluation (`net.hydromatic.morel.eval`)**
- `Code`: Interface for executable code nodes
- `Codes`: Implementations of all code types
- `EvalEnv`: Runtime environment mapping variables to values
- `Closure`: Function values that capture their environment
- `Applicable`: Function objects with apply methods
- `Session`: Maintains REPL state and configuration

**Datalog (`net.hydromatic.morel.datalog`)**
- `DatalogParserImpl`: JavaCC parser for Datalog syntax
- `DatalogAst`: Datalog abstract syntax tree nodes
- `DatalogAnalyzer`: Safety and stratification checking
- `DatalogTranslator`: Translates Datalog to Morel source
- `DatalogEvaluator`: Orchestrates parse → analyze → translate → execute

**Foreign Interface (`net.hydromatic.morel.foreign`)**
- `ForeignValue`: Interface for exposing Java values/functions to Morel
- `Calcite`: Integration with Apache Calcite for relational queries
- `DataSet`: Abstraction for queryable datasets (backed by Calcite)

**Main Entry Points**
- `Main`: REPL implementation with shell and sub-shell support
- `Shell`: Handles command execution and error reporting

### Key Execution Flow

1. **Parsing**: User input → `MorelParser` → `Ast` nodes
2. **Type Resolution**: `Ast` + `Environment` → `TypeResolver` →
   typed `Core` nodes
3. **Compilation**: `Core` → `Compiler` → `Code` nodes
4. **Evaluation**: `Code` + `EvalEnv` → execution → result value

### Important Implementation Details

**Type Inference**
- Uses Hindley-Milner algorithm (Algorithm W) via `TypeResolver`
- Type variables represent unknown types during inference
- Unification (`TypeUnifier`) propagates type constraints
- Generalization introduces polymorphism at `let` bindings

**Relational Extensions**
- `from` expressions are first-class and composable
- TypeResolver converts `from` to `Core.From` nodes
- Compiler can either:
  - Inline as nested loops (simple cases)
  - Send to `CalciteCompiler` for optimization (complex queries)
- Integration with Calcite allows joining external data sources

**Overloading**
- Functions like `+`, `max`, `empty` support multiple type signatures
- Declared using `over` (declares overloaded name) and `inst` (adds
  instance)
- Bindings track `overloadId` to distinguish overload instances
- Type resolution selects appropriate instance based on argument types

**Pattern Matching**
- Patterns appear in `val`, `fun`, `case`, `fn`, and `from`
- `PatternCoverageChecker` ensures exhaustiveness and redundancy
- Compiled to decision trees with guards

## Test Organization

Tests are in `src/test/java` and use JUnit 5. The main test
infrastructure:

- `MainTest`: Primary tests using the `Ml` helper class
- `Ml.ml()`: Helper to run Morel code and check results
- `src/test/resources/script/`: Reference test files (`.smli` suffix)
  - These are Morel source files with expected output
  - Run via `MainTest` methods that check actual vs. expected output

Key test files in `src/test/resources/script/`:
- `built-in.smli`: Tests for built-in functions and operators
- `relational.smli`: Tests for relational/query features
- `simple.smli`: Basic language features
- `datatype.smli`: Algebraic data types
- `type.smli`: Type system tests
- `foreign.smli`: Foreign value integration
- `datalog.smli`: Datalog interface tests

## Common Development Patterns

### Adding a Built-in Function

1. Add the function definition in `BuiltIn.java`
2. Register it in the appropriate structure (LIST, STRING, etc.)
3. Add tests in the corresponding `src/test/resources/script/` file
4. Update type signatures if polymorphic

### Adding a Standard Basis Library Structure

When implementing a structure from the
[SML Standard Basis Library](https://smlfamily.github.io/Basis/):

1. **`BuiltIn.java`** — If the structure introduces a new abstract type
   (e.g., `eqtype time`), add it to the `Eqtype` enum (zero type parameters)
   or `Datatype` enum (with type parameters). Then add one enum constant per
   function/value in the structure, named `STRUCTNAME_FUNCTIONNAME` (e.g.,
   `TIME_FROM_REAL`). Mark a constant as a method (`true` flag) if its first
   argument — or the first element of its tuple argument — is the structure's
   own type, following the same pattern as `REAL_COMPARE`.

2. **`Codes.java`** — Add an `Applicable` implementation for each function
   and register it in the `CODES` static map. If the structure has an
   exception (e.g., `exception Time`), add it to `BuiltInExn`.

3. **`lib/{name}.sig`** — Add a signature file declaring each `val`,
   `eqtype`/`type`, `datatype`, and `exception` in the structure. Types
   must agree with `BuiltIn.java` — `LintTest#testSignatures` cross-checks
   the two. Wrap reserved-word names (e.g., `take`, `order`, `exists`) and
   operator symbols (e.g., `^`, `<`, `@`) in backticks. Comment out
   unimplemented entries with a block comment so they remain visible.

   **Spec-attribute convention.** Use attributes in `.sig` files to carry
   metadata for generated docs and lint checks.

   On a `val` spec:

   * `(** description text *)` — prose description, immediately above
     the spec. Desugars to `[@@doc "..."]`.
   * `[@@prototype "drop (b, i)"]` — call form with named parameters,
     for use in generated docs.
   * `[@@method]` — function is postfix-callable (its first argument,
     or the first element of its tuple argument, is the structure's
     own type).
   * `[@@specified "morel"]` — distinguishes Morel extensions from
     SML Basis members; defaults to `"basis"` if absent.
   * `[@@syntax "infix"]` — declares operator syntax (`"infix"`,
     `"prefix"`); omit for ordinary functions.
   * `[@@extra "..."]` — supplemental sentence appended after the
     description in generated docs.

   On a `type`, `datatype`, or `exception` spec: the same `(** ... *)`
   doc-comment convention applies; `[@@specified "morel"]` may appear
   where relevant.

   Structure-level metadata follows the `end` of the signature declaration:

   * `[@@description "one-line summary."]` — short description for
     the structure-index table.
   * `(** Longer paragraph(s)... *)` — multi-paragraph
     overview shown at the top of the structure's doc page.
   * `[@@specified "morel"]` — defaults `specified` for every spec
     in the structure to this value.

4. **`src/test/resources/script/built-in.smli`** — Add tests for all
   functions, inserted alphabetically by structure name. Include a test that
   prints the whole structure (e.g., `Time;`) and postfix syntax tests for
   method functions (e.g., `t.toReal ()`). Update any environment count tests
   in `misc.smli` if they exist.

5. **`docs/lib/{name}.md`** (new file) — Create a doc page using the license
   header from an existing page, with `[//]: # (start:lib/{name})` and
   `[//]: # (end:lib/{name})` markers. The content between the markers is
   auto-generated from `lib/{name}.sig`.

6. **Regenerate docs** — Run `./mvnw test -Dtest=LintTest` to validate. The
   test fails with diffs showing what content to insert between the markers in
   the `.md` files. Copy the generated content into `docs/lib/{name}.md`,
   `docs/lib/index.md`, and `docs/reference.md`.

Notes:
- `scan` functions (those taking a `StringCvt.reader`) are omitted since
  Morel does not implement `StringCvt`.
- In Morel, `LargeReal.real` = `real` and `LargeInt.int` = `int`.
- Enum constants in `BuiltIn.java` and `Codes.java` must be in alphabetical
  order within their sort region (checked by `LintTest.testLint`).
- For opaque eqtypes (like `time`) backed by non-List Java objects,
  `Pretty.java` handles printing via `!(value instanceof List)` in
  `prettyDataType`.

### Adding a Language Feature

1. Update `MorelParser.jj` grammar
2. Add AST node types to `Ast.java` if needed
3. Update `TypeResolver.java` for type checking
4. Add compilation logic in `Compiler.java`
5. Add evaluation logic in `Codes.java`
6. Add tests

### Debugging Type Errors

- The `TypeResolver` tracks type constraints during inference
- Look for `unify()` calls to see where types are constrained
- Type variables have unique IDs; follow them through unification
- The `Tracer` interface can log type resolution steps

### Multi-line string formatting

Morel's linter (`LintTest`) requires that string literals that contain
line endings are split across lines, but if the total string can fit
on one line Google Java Format will join the lines. Add `//` after the
first `\n"` to prevent this. For example:

```java
String s = "first line\n" //
    + "second line";
```

### English

We use American English. Use "optimize" instead of "optimise",
"behavior" instead of "behaviour", etc.

### Verification

Before a commit, run the `fullMake` command (in `/usr/local/bin` and on path).
