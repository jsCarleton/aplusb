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
