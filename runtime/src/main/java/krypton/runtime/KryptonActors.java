package krypton.runtime;

@SuppressWarnings("unchecked")
public final class KryptonActors {

    public static Object raw_spawn(Object actorFn) {
        Mailbox<Object> mailbox = new Mailbox<>();
        Fun1 fn = (Fun1) actorFn;
        return KryptonRuntime.spawn(mailbox, () -> fn.apply(mailbox));
    }

    public static void raw_send(Object ref, Object msg) {
        ((Ref<Object>) ref).send(msg);
    }

    public static Object raw_receive(Object mailbox) {
        return ((Mailbox<Object>) mailbox).receive();
    }

    public static Object raw_receive_timeout(Object mailbox, long millis) {
        Object msg = ((Mailbox<Object>) mailbox).receiveTimeout(millis);
        return (msg != null) ? wrapSome(msg) : wrapNone();
    }

    public static Object raw_actor_ref(Object mailbox) {
        return ((Mailbox<Object>) mailbox).ref();
    }

    public static long raw_mailbox_size(Object mailbox) {
        return ((Mailbox<Object>) mailbox).size();
    }

    public static Object raw_create_mailbox() {
        return new Mailbox<>();
    }

    public static Object raw_adapter(Object ref, Object wrapperFn) {
        Fun1 wrapper = (Fun1) wrapperFn;
        return new Ref<>(msg -> { raw_send(ref, wrapper.apply(msg)); return null; });
    }

    public static Object raw_ask(Object target, Object wrapperFn, long timeout) {
        Mailbox<Object> replyMb = new Mailbox<>();
        Object replyRef = replyMb.ref();
        Fun1 fn = (Fun1) wrapperFn;
        Object msg = fn.apply(replyRef);
        raw_send(target, msg);
        Object reply = replyMb.receiveTimeout(timeout);
        return (reply != null) ? wrapOk(reply) : wrapErr(wrapTimeout());
    }

    // --- Helpers ---

    private static Object wrapSome(Object value) {
        try {
            Class<?> cls = Class.forName("core.option.Option$Some");
            return cls.getDeclaredConstructor(Object.class).newInstance(value);
        } catch (Exception e) {
            throw new RuntimeException("Failed to construct Some: " + e.getMessage(), e);
        }
    }

    private static Object wrapNone() {
        try {
            Class<?> cls = Class.forName("core.option.Option$None");
            return cls.getDeclaredConstructor().newInstance();
        } catch (Exception e) {
            throw new RuntimeException("Failed to construct None: " + e.getMessage(), e);
        }
    }

    private static Object wrapOk(Object value) {
        try {
            Class<?> cls = Class.forName("core.result.Result$Ok");
            return cls.getDeclaredConstructor(Object.class).newInstance(value);
        } catch (Exception e) {
            throw new RuntimeException("Failed to construct Ok: " + e.getMessage(), e);
        }
    }

    private static Object wrapErr(Object value) {
        try {
            Class<?> cls = Class.forName("core.result.Result$Err");
            return cls.getDeclaredConstructor(Object.class).newInstance(value);
        } catch (Exception e) {
            throw new RuntimeException("Failed to construct Err: " + e.getMessage(), e);
        }
    }

    private static Object wrapTimeout() {
        try {
            Class<?> cls = Class.forName("core.actor.Timeout$Timeout");
            return cls.getDeclaredConstructor().newInstance();
        } catch (Exception e) {
            throw new RuntimeException("Failed to construct Timeout: " + e.getMessage(), e);
        }
    }

    private KryptonActors() {}
}
