# aplusb

A simple WebAssembly function that adds two numbers.

## Files

- `add.wat` — WebAssembly Text source defining the `add(a, b)` function
- `add.wasm` — compiled WebAssembly binary
- `test.js` — Node.js test harness

## Build

Requires [wabt](https://github.com/WebAssembly/wabt) (`brew install wabt`):

```sh
wat2wasm add.wat -o add.wasm
```

## Test

```sh
node test.js
```

## Formal proof of correctness

`coq/` contains a machine-checked proof, against
[WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq) (a real formal
semantics of WebAssembly, not an approximation of it), that invoking `add`
through the actual small-step operational semantics returns exactly
`Wasm_int.Int32.iadd a b` — 32-bit wrapping addition, for any two i32
arguments.

### Trust chain

Everything lives in the single file `coq/Add.v`, organized into sections
(marked by comments) that mirror the stages of the trust chain below. The
proof is about a hand-encoded Coq AST term, not directly about the `.wat`
file — WasmCert-Coq's text-format parser only handles value literals, not
whole modules. The correspondence between them is machine-checked, not
eyeballed:

```
add.wat --(wat2wasm, trusted, external)--> add.wasm
   |
   | tools/wasm_bytes_to_coq.py copies the exact bytes (make bytes)
   v
add_wasm_bytes : list byte                (coq/Add.v, "bytes" section)
   |
   | WasmCert-Coq's binary parser (run_parse_module, trusted, external)
   v
parsed : module                                    (a Coq term)
   |
   | vm_compute / reflexivity  <-- kernel-checked, NOT trusted-by-assertion
   v
coq/Add.v's "correspondence" section proves:
  parsed.mod_funcs[0] = add_module_func    (the "AST" section's term)
  parsed.mod_types[0] = add_function_type
```

So `wat2wasm` and WasmCert-Coq's binary parser are trusted, external to the
proof — but the *equality* between what they produce and the term the rest
of the proof is about is checked by Coq's kernel. Everything downstream is a
genuine proof against WebAssembly's real small-step semantics
(`reduce`/`reduce_trans`), invoking the function directly (a hand-built
store/frame/closure, skipping WasmCert-Coq's generic module-instantiation
machinery, which is orthogonal boilerplate already proven sound upstream).

| Section (in `coq/Add.v`) | What it proves |
|---|---|
| bytes | `add_wasm_bytes`, generated verbatim from `add.wasm` |
| AST | The function hand-encoded as a WasmCert-Coq AST term (`add_module_func`) |
| correspondence | That term is byte-identical (via the compiled binary) to what `wat2wasm` actually produced from `add.wat` |
| invocation setup | The store/frame/function-closure setup for invoking the function directly through the real semantics (no memory needed — `add.wat` declares none) |
| small-step infrastructure | Reusable lemmas (`reduce_trans_label`/`reduce_trans_frame`, lifting a whole multi-step execution through a label/frame context) plus atomic-instruction steps for `local.get` and i32 binops |
| top-level correctness | The theorem `add_correct`: invoking the function on any two i32 arguments reduces, through the real semantics, to the single value `Wasm_int.Int32.iadd a b`. `add_correct_unsigned` restates this as ordinary unsigned-integer addition mod 2^32 |

The whole file compiles with `Qed`; zero `Admitted`/`Axiom` introduced by
this project.

### Building the proof

Requires `coqc` 8.20.x and the `coq-wasm` (WasmCert-Coq) library on the Coq
load path — see `coq/_CoqProject`.

```sh
make bytes   # regenerate the bytes definition inside coq/Add.v from add.wasm
make coq     # build the Coq development
```
