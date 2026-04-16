package krypton.runtime;

import java.util.concurrent.atomic.AtomicBoolean;

@SuppressWarnings({"rawtypes", "unchecked"})
final class ExitHandler {
    final Mailbox<?> targetMailbox;
    final Fun1 normalFactory;
    final Fun2 crashFactory;
    private final AtomicBoolean fired = new AtomicBoolean(false);

    ExitHandler(Mailbox<?> mb, Fun1 n, Fun2 c) {
        this.targetMailbox = mb;
        this.normalFactory = n;
        this.crashFactory = c;
    }

    void fire(long actorId, Throwable crashReason) {
        if (!fired.compareAndSet(false, true)) return;
        try {
            Object msg;
            if (crashReason == null) {
                msg = normalFactory.apply(actorId);
            } else {
                String m = crashReason.getMessage();
                msg = crashFactory.apply(actorId, m != null ? m : "unknown error");
            }
            ((Mailbox<Object>) targetMailbox).enqueue(msg);
        } catch (Exception ignored) {
        }
    }
}
