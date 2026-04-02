package krypton.runtime;

import java.util.concurrent.atomic.AtomicLong;

public final class ActorThread {
    private static final AtomicLong ID_COUNTER = new AtomicLong(0);

    private final long actorId;
    private final Thread virtualThread;
    private final Mailbox<?> mailbox;
    private volatile boolean alive = true;
    private volatile Throwable crashReason;

    ActorThread(Runnable body, Mailbox<?> mailbox, KryptonRuntime runtime) {
        this.actorId = ID_COUNTER.getAndIncrement();
        this.mailbox = mailbox;
        runtime.trackActor(this);
        this.virtualThread = Thread.ofVirtual()
                .name("krypton-actor-" + actorId)
                .start(() -> {
                    try {
                        body.run();
                    } catch (Throwable t) {
                        crashReason = t;
                        System.err.println("[krypton] actor-" + actorId + " crashed: " + t.getMessage());
                    } finally {
                        mailbox.close();
                        alive = false;
                        runtime.notifyActorDone(this);
                    }
                });
    }

    public boolean isAlive() {
        return alive;
    }

    public long actorId() {
        return actorId;
    }

    public Throwable crashReason() {
        return crashReason;
    }

    Thread thread() {
        return virtualThread;
    }
}
