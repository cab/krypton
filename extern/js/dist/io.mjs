// src/io.mts
function raw_println(x) {
  console.log(x);
}
function raw_print(x) {
  const maybeProcess = globalThis;
  if (maybeProcess.process?.stdout && typeof maybeProcess.process.stdout.write === "function") {
    maybeProcess.process.stdout.write(String(x));
  } else {
    console.log(x);
  }
}
function readLine() {
  throw new Error("readLine is not supported on the JS target");
}
function read_file(_path) {
  throw new Error("read_file is not supported on the JS target");
}
function write_file(_path, _content) {
  throw new Error("write_file is not supported on the JS target");
}
export {
  raw_print,
  raw_println,
  readLine,
  read_file,
  write_file
};
