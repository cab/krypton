package krypton.runtime;

@SuppressWarnings("unchecked")
public final class KryptonActors {

    public static Object raw_spawn(Object actorFn) {
        Mailbox<Object> mailbox = new Mailbox<>();
        Fun1 fn = (Fun1) actorFn;
        return KryptonRuntime.instance().spawn(mailbox, () -> fn.apply(mailbox));
    }

    public static void raw_send(Object ref, Object msg) {
        ((Ref<Object>) ref).send(msg);
    }

    public static Object raw_receive(Object mailbox) {
        return ((Mailbox<Object>) mailbox).receive();
    }

    public static Object raw_receive_timeout(Object mailbox, long millis) {
        return ((Mailbox<Object>) mailbox).receiveTimeout(millis);
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
        replyMb.close();
        return reply;  // null on timeout, value on success
    }

    private KryptonActors() {}
}
