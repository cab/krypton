package krypton.runtime;

import org.organicdesign.fp.collections.MutMap;
import org.organicdesign.fp.collections.PersistentHashMap;

/**
 * Transient (mutable) builder over Paguro's {@link MutMap}. Transitions back
 * to an immutable {@link KryptonMap} in O(1) via {@link #builderFreeze}.
 *
 * <h3>Thread-safety invariant</h3>
 *
 * <p>This class is <b>not</b> thread-safe, and it is not meant to be. Two
 * load-bearing facts keep it safe in practice:
 *
 * <ol>
 *   <li><b>Single-owner at the Krypton level.</b> A Krypton {@code
 *       ~MapBuilder[k, v]} is a linear type — the Krypton typechecker
 *       statically enforces that exactly one scope owns it at any time. No
 *       two threads can hold references to the same builder concurrently
 *       because the type system rules out aliasing before codegen ever runs.
 *   <li><b>No JMM crutch would help.</b> Declaring {@code data} {@code
 *       volatile} would publish the <i>reference</i> to {@code MutMap}
 *       across threads but would not make {@code MutMap}'s internal trie
 *       thread-safe — Paguro's mutable map has non-volatile internal state
 *       and concurrent {@code .assoc()} from two threads races regardless
 *       of how we declare the wrapper field. The correct fix is preventing
 *       aliasing at the Krypton level, not layering JMM primitives on top.
 * </ol>
 *
 * <p>The Krypton-level invariant is codified by the typechecker fixture
 * {@code tests/fixtures/actors/actor_map_builder_cannot_send.kr}, which
 * verifies that {@code ~MapBuilder} cannot escape across an actor boundary.
 * Any relaxation of that linearity guarantee would break the assumption this
 * class relies on.
 *
 * <h3>Naming</h3>
 *
 * <p>Method names use the {@code builder*} prefix for historical reasons —
 * Krypton now supports function overloading, so the Krypton-level stdlib
 * re-exposes these as overloaded {@code put} / {@code freeze} on Map via
 * {@code stdlib/core/map.kr}.
 */
public final class KryptonMapBuilder {
    private MutMap<KryptonMap.HashedKey, Object> data;
    private Fun1 hashFn;
    private Fun2 eqFn;

    KryptonMapBuilder(MutMap<KryptonMap.HashedKey, Object> data, Fun1 hashFn, Fun2 eqFn) {
        this.data = data;
        this.hashFn = hashFn;
        this.eqFn = eqFn;
    }

    public static KryptonMapBuilder builderNew() {
        return new KryptonMapBuilder(PersistentHashMap.emptyMutable(), null, null);
    }

    public static KryptonMapBuilder builderPut(KryptonMapBuilder b, Object key, Object value, Object eqDict, Object hashDict) {
        Fun2 eq = (Fun2) eqDict;
        Fun1 hash = (Fun1) hashDict;
        if (b.hashFn == null) {
            b.hashFn = hash;
            b.eqFn = eq;
        }
        KryptonMap.HashedKey wrapped = new KryptonMap.HashedKey(key, hash, eq);
        b.data = b.data.assoc(wrapped, value);
        return b;
    }

    public static KryptonMap builderFreeze(KryptonMapBuilder b) {
        return new KryptonMap(b.data.immutable(), b.hashFn, b.eqFn);
    }
}
