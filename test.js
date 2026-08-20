const fs = require("fs");

async function main() {
  const bytes = fs.readFileSync(__dirname + "/add.wasm");
  const { instance } = await WebAssembly.instantiate(bytes);
  const { add } = instance.exports;

  const cases = [
    [1, 2, 3],
    [0, 0, 0],
    [-5, 5, 0],
    [100, 250, 350],
  ];

  for (const [a, b, expected] of cases) {
    const result = add(a, b);
    const status = result === expected ? "ok" : "FAIL";
    console.log(`add(${a}, ${b}) = ${result} (expected ${expected}) [${status}]`);
  }
}

main();
