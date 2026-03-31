package krypton.runtime;

@SuppressWarnings("unchecked")
public final class KryptonActors {

    public static Ref<?> raw_spawn(Fun1 actorFn) {
        Mailbox<Object> mailbox = new Mailbox<>();
        return KryptonRuntime.instance().spawn(mailbox, () -> actorFn.apply(mailbox));
    }

    public static void raw_send(Ref<?> ref, Object msg) {
        ((Ref<Object>) ref).send(msg);
    }

    public static Object raw_receive(Mailbox<?> mailbox) {
        return ((Mailbox<Object>) mailbox).receive();
    }

    public static Object raw_receive_timeout(Mailbox<?> mailbox, long millis) {
        return ((Mailbox<Object>) mailbox).receiveTimeout(millis);
    }

    public static Ref<?> raw_actor_ref(Mailbox<?> mailbox) {
        return ((Mailbox<Object>) mailbox).ref();
    }

    public static long raw_mailbox_size(Mailbox<?> mailbox) {
        return ((Mailbox<Object>) mailbox).size();
    }

    public static Mailbox<?> raw_create_mailbox() {
        return new Mailbox<>();
    }

    public static Ref<?> raw_adapter(Ref<?> ref, Fun1 wrapperFn) {
        return new Ref<>(msg -> { raw_send(ref, wrapperFn.apply(msg)); return null; });
    }

    public static Object raw_ask(Ref<?> target, Fun1 wrapperFn, long timeout) {
        Mailbox<Object> replyMb = new Mailbox<>();
        Ref<?> replyRef = replyMb.ref();
        Object msg = wrapperFn.apply(replyRef);
        raw_send(target, msg);
        Object reply = replyMb.receiveTimeout(timeout);
        replyMb.close();
        return reply;  // null on timeout, value on success
    }

    private KryptonActors() {}
}
