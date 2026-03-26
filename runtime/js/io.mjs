// Krypton JS runtime — I/O

export function raw_println(x) {
  console.log(x);
}

export function raw_print(x) {
  if (typeof process !== 'undefined' && process.stdout && typeof process.stdout.write === 'function') {
    process.stdout.write(String(x));
  } else {
    console.log(x);
  }
}

export function readLine() {
  throw new Error('readLine is not supported on the JS target');
}

export function read_file(_path) {
  throw new Error('read_file is not supported on the JS target');
}

export function write_file(_path, _content) {
  throw new Error('write_file is not supported on the JS target');
}
