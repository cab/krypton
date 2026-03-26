// Krypton JS runtime — panic

export class KryptonPanic extends Error {
  constructor(message) {
    super(message);
    this.name = 'KryptonPanic';
  }
}
