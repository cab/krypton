export function raw_println(x: unknown) {
  console.log(x);
}

export function raw_print(x: unknown) {
  const maybeProcess = globalThis as {
    process?: {
      stdout?: {
        write?: (text: string) => unknown;
      };
    };
  };
  if (
    maybeProcess.process?.stdout &&
    typeof maybeProcess.process.stdout.write === 'function'
  ) {
    maybeProcess.process.stdout.write(String(x));
  } else {
    console.log(x);
  }
}

export function readLine() {
  throw new Error('readLine is not supported on the JS target');
}

export function read_file(_path: string) {
  throw new Error('read_file is not supported on the JS target');
}

export function write_file(_path: string, _content: string) {
  throw new Error('write_file is not supported on the JS target');
}
