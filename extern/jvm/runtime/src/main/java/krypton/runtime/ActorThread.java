package krypton.runtime;

import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicLong;

public final class ActorThread {
    private static final AtomicLong ID_COUNTER = new AtomicLong(0);

    private final long actorId;
    private final Thread virtualThread;
    private final Mailbox<?> mailbox;
    private final CopyOnWriteArrayList<ExitHandler> exitHandlers = new CopyOnWriteArrayList<>();
    private final Set<ActorThread> linkedActors = ConcurrentHashMap.newKeySet();
    private volatile boolean alive = true;
    private volatile boolean exiting = false;
    private volatile Throwable crashReason;

    ActorThread(Runnable body, Mailbox<?> mailbox, KryptonRuntime runtime) {
        this.actorId = ID_COUNTER.getAndIncrement();
        this.mailbox = mailbox;
        mailbox.ownerActor = this;
        runtime.trackActor(this);
        this.virtualThread = Thread.ofVirtual()
                .name("krypton-actor-" + actorId)
                .unstarted(() -> {
                    try {
                        body.run();
                    } catch (Throwable t) {
                        crashReason = t;
                        if (!(t instanceof InterruptedException)) {
                            System.err.println("[krypton] actor-" + actorId + " crashed: " + t.getMessage());
                        }
                    } finally {
                        exiting = true;
                        for (ExitHandler h : exitHandlers) h.fire(actorId, crashReason);
                        for (ActorThread a : linkedActors) {
                            if (a.isAlive()) a.thread().interrupt();
                        }
                        mailbox.close();
                        alive = false;
                        runtime.notifyActorDone(this);
                    }
                });
    }

    void start() {
        virtualThread.start();
    }

    void addExitHandler(ExitHandler h) {
        exitHandlers.add(h);
        if (exiting) h.fire(actorId, crashReason);
    }

    void addLinkedActor(ActorThread other) {
        linkedActors.add(other);
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
