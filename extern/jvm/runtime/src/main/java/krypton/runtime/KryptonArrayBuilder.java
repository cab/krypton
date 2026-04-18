package krypton.runtime;

import org.organicdesign.fp.collections.MutList;
import org.organicdesign.fp.collections.PersistentVector;

/**
 * Transient (mutable) builder over Paguro's {@link MutList}. Transitions back
 * to an immutable {@link KryptonArray} in O(1) via {@link #builderFreeze}.
 *
 * <h3>Thread-safety invariant</h3>
 *
 * <p>This class is <b>not</b> thread-safe, and it is not meant to be. Two
 * load-bearing facts keep it safe in practice:
 *
 * <ol>
 *   <li><b>Single-owner at the Krypton level.</b> A Krypton {@code
 *       ~VecBuilder[a]} is a linear type — the Krypton typechecker statically
 *       enforces that exactly one scope owns it at any time. No two threads
 *       can hold references to the same builder concurrently because the type
 *       system rules out aliasing before codegen ever runs.
 *   <li><b>No JMM crutch would help.</b> Declaring {@code data} {@code
 *       volatile} would publish the <i>reference</i> to {@code MutList}
 *       across threads but would not make {@code MutList}'s internal arrays
 *       thread-safe — Paguro's mutable list has non-volatile internal state
 *       and concurrent {@code .append()} from two threads races regardless
 *       of how we declare the wrapper field. The correct fix is preventing
 *       aliasing at the Krypton level, not layering JMM primitives on top.
 * </ol>
 *
 * <p>The Krypton-level invariant is codified by the typechecker fixture
 * {@code tests/fixtures/actors/actor_vec_builder_cannot_send.kr}, which
 * verifies that {@code ~VecBuilder} cannot escape across an actor boundary.
 * Any relaxation of that linearity guarantee would break the assumption this
 * class relies on.
 *
 * <h3>Naming</h3>
 *
 * <p>Method names use the {@code builder*} prefix for historical reasons —
 * Krypton now supports function overloading, so the Krypton-level stdlib
 * re-exposes these as overloaded {@code push} / {@code freeze} on Vec via
 * {@code stdlib/core/vec.kr}.
 */
public final class KryptonArrayBuilder {
    private MutList<Object> data;

    KryptonArrayBuilder(MutList<Object> data) {
        this.data = data;
    }

    public static KryptonArrayBuilder builderNew() {
        return new KryptonArrayBuilder(PersistentVector.emptyMutable());
    }

    public static KryptonArrayBuilder builderPush(KryptonArrayBuilder b, Object value) {
        b.data = b.data.append(value);
        return b;
    }

    public static KryptonArray builderFreeze(KryptonArrayBuilder b) {
        return KryptonArray.of(b.data.immutable());
    }
}
