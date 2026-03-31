// src/panic.mts
var KryptonPanic = class extends Error {
  constructor(message) {
    super(message);
    this.name = "KryptonPanic";
  }
};
export {
  KryptonPanic
};
