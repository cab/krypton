package krypton.runtime;

import java.util.concurrent.atomic.AtomicLong;

public final class ActorThread {
    private static final AtomicLong ID_COUNTER = new AtomicLong(0);

    private final long actorId;
    private final Thread virtualThread;
    private final Mailbox<?> mailbox;
    private volatile boolean alive = true;

    ActorThread(Runnable body, Mailbox<?> mailbox, KryptonRuntime runtime) {
        this.actorId = ID_COUNTER.getAndIncrement();
        this.mailbox = mailbox;
        runtime.incrementActorCount();
        runtime.trackActor(this);
        this.virtualThread = Thread.ofVirtual()
                .name("krypton-actor-" + actorId)
                .start(() -> {
                    try {
                        body.run();
                    } finally {
                        alive = false;
                        mailbox.close();
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

    Thread thread() {
        return virtualThread;
    }
}
