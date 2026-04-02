package krypton.runtime;

public final class Ref<M> {
    private final Fun1 sendFn;

    @SuppressWarnings("unchecked")
    Ref(Mailbox<M> mailbox) {
        this.sendFn = msg -> { mailbox.enqueue((M) msg); return null; };
    }

    Ref(Fun1 sendFn) {
        this.sendFn = sendFn;
    }

    public void send(M msg) {
        sendFn.apply(msg);
    }
}
