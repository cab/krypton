package krypton.runtime;

import org.organicdesign.fp.collections.MutList;
import org.organicdesign.fp.collections.PersistentVector;

/**
 * Transient (mutable) builder over Paguro's MutList. Single-ownership is
 * enforced at the Krypton type level via linear (~) parameters; that authorizes
 * the in-place mutation. {@code builderFreeze} transitions back to an immutable
 * persistent vector in O(1).
 *
 * <p>Method names use the {@code builder*} prefix (rather than the usual
 * {@code static*} convention) because Krypton has no function overloading —
 * sharing the {@code push} name with {@link KryptonArray} would collide in
 * imported scope.
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
