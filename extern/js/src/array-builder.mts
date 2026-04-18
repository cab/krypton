import { List } from 'immutable';

/**
 * Transient-mode List from Immutable.js. Single-ownership is enforced by the
 * Krypton `~VecBuilder[a]` linear type; that authorizes the in-place mutation.
 * `builderFreeze` returns the builder to immutable mode in O(1).
 *
 * Exports use the `builder*` prefix (rather than the usual `static*`
 * convention) because Krypton has no function overloading — sharing the
 * `push` name with the Vec extern would collide in imported scope.
 */

export function builderNew<T>(): List<T> {
  return List<T>().asMutable();
}

export function builderPush<T>(builder: List<T>, item: T): List<T> {
  return builder.push(item);
}

export function builderFreeze<T>(builder: List<T>): List<T> {
  return builder.asImmutable();
}
