package krypton.runtime;

public final class Ref<M> {
    private final Fun1 sendFn;
    final ActorThread actor;

    @SuppressWarnings("unchecked")
    Ref(Mailbox<M> mailbox, ActorThread actor) {
        this.sendFn = msg -> { mailbox.enqueue((M) msg); return null; };
        this.actor = actor;
    }

    Ref(Fun1 sendFn) {
        this.sendFn = sendFn;
        this.actor = null;
    }

    public void send(M msg) {
        sendFn.apply(msg);
    }
}
