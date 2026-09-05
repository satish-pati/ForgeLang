---

title: Custom Language Compiler — Group 3

---

# Custom Language Compiler — Group 3

A full compiler pipeline for a custom programming language. Takes source code through lexing → parsing → semantic analysis → TAC generation → optimization → RISC-V assembly generation → native binary execution, and also transpiles to Python for immediate execution. Serves an interactive HTML visualization dashboard.

---

## Folder Structure

```
3/
├── Makefile                # Builds parser binaries from lexer + parser source
├── compiler                # Shell script — runs the full pipeline end to end
├── lexer.l                 # Flex lexer — tokenizes source files
├── parser_unoptimized.y    # Yacc parser — token trace + unoptimized TAC
├── parser_optimized.y      # Yacc parser — optimized TAC, CFG, call graph, symbol table, HTML
├── tac_to_risc.py          # TAC → RISC-V assembly generator (output.s) → compiles & runs via QEMU
├── transpiler.py           # TAC → Python transpiler (executes via generated.py)
├── script.js               # Frontend JS for the visualization dashboard
├── styles.css              # Frontend CSS for the visualization dashboard
├── README.md               # This file
└── tests/                  # Test programs covering all language features
    ├── 01_primitive_dtypes
    ├── 02_literals
    ├── 03_arithmetic
    ├── 04_conditions
    ├── 05_bitwise
    ├── 06_ternary
    ├── 07_assign_arthiops
    ├── 07_assign_bitwise
    ├── 08_inc_dec
    ├── 09_loop_while
    ├── 10_loop_dowhile
    ├── 11_loop_for
    ├── 12_nested_loops
    ├── 13_exit
    ├── 14_skip
    ├── 15_switch
    ├── 16_scopes
    ├── 17_scopes2
    ├── 18_explicit_cast
    ├── 19_type_widen
    ├── 20_typenarrow
    ├── 21_typepromotion
    ├── 22_builtins_abs
    ├── 23_builtins_getsize
    ├── 24_function
    ├── 25_arrays
    ├── 27_enums
    ├── 27_strings
    ├── 28_pass_by_value_vs_ptr
    ├── 29_pointers
    ├── 30_ptr_alias
    ├── 31_alloc
    ├── 32_calloc
    ├── 33_realloc
    ├── 34_ptr_func
    ├── 35_free
    ├── 36_overflow_range
    ├── 37_warn_typenarow
    ├── 38_type_fun
    ├── 39_func_arg_type
    ├── test_bubble_sort
    ├── test_binary_search
    ├── test_factorial
    ├── test_fibonacci
    ├── test_insertion_sort
    ├── test_palindrome
    ├── test_reverse_array
    ├── test_selection_sort
    ├── test_swap_by_val_ref
    ├── err01_redecl
    ├── err02_undeclared
    │   ... (error/warning tests through err33_void_print)
    └── warn01_unusedvars
```

---



> ## Language Syntax Overview
>
> This compiler accepts a **custom language** — not standard C. Key syntax:
>
>
> | Concept          | Keyword / Syntax                                                         |
> | ---------------- | ------------------------------------------------------------------------ |
> | Types            | `@int`, `@float`, `@char`, `@double`, `@short`, `@long`, `@void`, `@ptr` |
> | Function def     | `func`                                                                   |
> | Return           | `ret`                                                                    |
> | Function call    | `call`                                                                   |
> | Print            | `show`                                                                   |
> | Input            | `input`                                                                  |
> | If / Else        | `if / else` or `when / otherwise`                                        |
> | While loop       | `loop`                                                                   |
> | For loop         | `iterate`                                                                |
> | Do-While         | `repeat`                                                                 |
> | Switch / Case    | `choose / option / def`                                                  |
> | Break / Continue | `exit` / `skip`                                                          |
> | Assignment       | `is` (e.g. `x is 5`)                                                     |
> | Block delimiters | `begin` / `end` (instead of `{ }`)                                       |
> | Boolean          | `true`, `false`                                                          |
> | Logical ops      | `and`, `or`, `not`                                                       |
> | Bitwise ops      | `bitand`, `bitor`, `bitxor`, `bitnot`, `lshift`, `rshift`                |
> | Const            | `fixed`                                                                  |
> | Pointers         | `ref` (address-of), `deref` (dereference)                                |
> | Heap memory      | `alloc`, `calloc`, `realloc`, `free` / `release`                         |
> | Null pointer     | `null`                                                                   |
> | Sizeof           | `getsizeof`                                                              |
> | Comments         | `# single line`, `''' multi-line '''`, `""" multi-line """`              |
> | Number literals  | decimal, `hex1F` (hex), `oct17` (octal), `bin1010` (binary)              |
>

---



## System Requirements

- **OS:** Linux (Ubuntu 20.04+) or WSL2 on Windows
- **GCC** — compiles C code generated by flex/yacc
- **flex** — lexer generator
- **bison / yacc** — parser generator
- **libfl-dev** — flex runtime library (needed for linking)
- **Python 3.8+** — runs transpiler and TAC-to-RISC converter (standard library only, no pip packages)
- **Graphviz** — renders CFG and call graph `.dot` files to PNG images
- **RISC-V cross-compiler + QEMU** — to compile `output.s` to a binary and execute it

---



## Setup



### Step 1 — Extract the archive

```bash
tar -xzvf 3.tar.gz
cd ForgeLang
```



### Step 2 — Install all dependencies

Run the following on Ubuntu/Debian (or WSL2):

```bash
sudo apt update

# Core build tools
sudo apt install -y gcc flex bison

# Flex runtime library (required for linking)
sudo apt install -y libfl-dev

# Graphviz — for CFG and call graph rendering
sudo apt install -y graphviz

# Python 3
sudo apt install -y python3

# RISC-V cross-compiler + QEMU — to compile and run output.s
sudo apt install -y gcc-riscv64-linux-gnu qemu-user
```

---



### Step 3 — Build

Compile both parsers from source:

```bash
make
```

This runs `flex` on `lexer.l` and `yacc` on each `.y` file, then compiles the C output into two binaries:

- `parser_unoptimized` — produces token trace and unoptimized TAC
- `parser_optimized`   — produces optimized TAC, CFG, call graph, symbol table, and HTML dashboard

To remove all build artifacts and generated files:

```bash
make clean
```

---



## Running



### Option 1 — Automated (recommended)

```bash
chmod +x compiler        # only needed once
./compiler <source_file>
```



### Option 2 — Manual step by step

```bash
make
LEXER_TOKEN_TRACE=1 ./parser_unoptimized <source_file> 2>tokens.txt
./parser_optimized <source_file>
python3 tac_to_risc.py --run
python3 transpiler.py && python3 generated.py
python3 -m http.server 8080
```

To manually compile and run the generated RISC-V assembly:

```bash
riscv64-linux-gnu-gcc -static -o a.out output.s
qemu-riscv64 a.out
```



### Pipeline — what happens step by step:

1. `make` — builds both parsers (skipped if already up to date)
2. `parser_unoptimized` — tokenizes and parses the input; writes `tokens.txt` (token trace) and `unopt.tac`
3. `parser_optimized` — full semantic analysis; writes `optimized.tac`, `symtab.json`, `.dot` graph files, and the HTML visualization dashboard
4. `tac_to_risc.py` — converts `optimized.tac` → `output.s` (RISC-V assembly); then compiles with `riscv64-linux-gnu-gcc -static -o a.out output.s` and executes via `qemu-riscv64 a.out`
5. `transpiler.py` — converts `unopt.tac` → `generated.py` and executes it (program output appears here)
6. **HTTP server** — starts `python3 -m http.server 8080` in the background

Open your browser at: **[http://localhost:8080](http://localhost:8080)**

---



## Running Tests

Each entry inside `tests/` is a source file (no extension). Pass it directly to the `compiler` script.

### Run an algorithm test

```bash
./compiler tests/test_bubble_sort
./compiler tests/test_factorial
./compiler tests/test_fibonacci
./compiler tests/test_binary_search
./compiler tests/test_insertion_sort
./compiler tests/test_selection_sort
./compiler tests/test_palindrome
./compiler tests/test_reverse_array
./compiler tests/test_swap_by_val_ref
```



### Run a feature test

```bash
./compiler tests/01_primitive_dtypes
./compiler tests/03_arithmetic
./compiler tests/25_arrays
./compiler tests/29_pointers
./compiler tests/31_alloc
```



### Run an error test (should report a compile error)

```bash
./compiler tests/err01_redecl
./compiler tests/err02_undeclared
./compiler tests/err05_div_zero
./compiler tests/err12_undef_func
```



### Run all tests in a loop

```bash
for f in tests/*; do
    echo "=== $f ==="
    ./compiler "$f"
done
```

---



## Output Files (generated per run)


| File                      | Description                                                    |
| ------------------------- | -------------------------------------------------------------- |
| `tokens.txt`              | Token trace — line, column, token type, lexeme                 |
| `unopt.tac`               | Three-address code before optimization                         |
| `optimized.tac`           | Three-address code after optimization                          |
| `quadruples.txt`          | Quadruple representation of TAC instructions                   |
| `symboltable.txt`         | Symbol table in plain-text format                              |
| `symtab.json`             | Symbol table in JSON format — scopes, variables, types, arrays |
| `optimization_report.txt` | Summary of optimizations applied                               |
| `output.s`                | Generated RISC-V assembly                                      |
| `a.out`                   | Compiled RISC-V binary (produced from `output.s`)              |
| `generated.py`            | Python equivalent of the input program (used for execution)    |
| `tac_flow.dot`            | Graphviz source for the TAC-level CFG                          |
| `tac_flow_blocks.dot`     | Graphviz source for the basic-blocks CFG                       |
| `call_graph.dot`          | Graphviz source for the call graph                             |
| `symbol_table.dot`        | Graphviz source for the symbol table visualization             |
| `*.png`                   | Rendered CFG and call graph images (from `.dot` files)         |
| `index.html`              | Main visualization dashboard                                   |
| `source.html`             | Source code viewer page                                        |
| `tokens.html`             | Token trace viewer page                                        |
| `tac.html`                | TAC viewer page                                                |
| `cfg.html`                | Control flow graph page                                        |
| `bsb.html`                | Basic blocks viewer page                                       |
| `callgraph.html`          | Call graph page                                                |
| `symbols.html`            | Symbol table page                                              |
| `quadruples.html`         | Quadruples viewer page                                         |
| `optreport.html`          | Optimization report page                                       |
| `asm.html`                | RISC-V assembly viewer page                                    |


---



## Troubleshooting

`flex: command not found` **/** `yacc: command not found`

```bash
sudo apt install flex bison
```

`-lfl: not found` **linker error**

```bash
sudo apt install libfl-dev
```

`dot: command not found` — CFG/call graph PNGs won't be generated

```bash
sudo apt install graphviz
```

`riscv64-linux-gnu-gcc: command not found` — `output.s` is generated but can't be compiled to `a.out`

```bash
sudo apt install gcc-riscv64-linux-gnu qemu-user
```

**Port 8080 already in use**

```bash
pkill -f "http.server"
./compiler <source_file>
```

`Permission denied: ./compiler`

```bash
chmod +x compiler
```

