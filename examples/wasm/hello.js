function instantiate(bytes, imports) {
  return WebAssembly.compile(bytes).then(m => new WebAssembly.Instance(m, imports));
}

let mem;

const env = {
  env: {
    trace: (ptr, len) => {
      const str = (new TextDecoder()).decode(new Uint8Array(mem.buffer, ptr, len));
      console.log(str);
    }
  }
}

const fs = require('node:fs/promises');

fs.readFile(process.argv[2])
  .then(bytes => instantiate(bytes, env))
  .then(instance => {
    mem = instance.exports.memory;
    instance.exports._start();
  });
