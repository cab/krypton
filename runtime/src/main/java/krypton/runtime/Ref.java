package krypton.runtime;

public final class Ref<M> {
    private final Mailbox<M> mailbox;

    Ref(Mailbox<M> mailbox) {
        this.mailbox = mailbox;
    }

    public void send(M msg) {
        mailbox.enqueue(msg);
    }
}
