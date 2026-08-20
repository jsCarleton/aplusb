.PHONY: all wasm validate smoke bytes coq clean

all: wasm smoke bytes coq

wasm: add.wasm

add.wasm: add.wat
	wat2wasm add.wat -o add.wasm

validate: wasm
	wasm-validate add.wasm

smoke: wasm
	node test.js

bytes: wasm
	python3 tools/wasm_bytes_to_coq.py add.wasm coq/AddBytes.v add_wasm_bytes

coq: bytes
	$(MAKE) -C coq

clean:
	rm -f add.wasm
	$(MAKE) -C coq clean
