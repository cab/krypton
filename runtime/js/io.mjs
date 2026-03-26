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
