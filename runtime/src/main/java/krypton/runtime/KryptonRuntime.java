package krypton.runtime;

import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;
import java.util.function.Consumer;

public final class KryptonRuntime {
    public static final String VERSION = "0.1.0";

    private static final AtomicInteger actorCount = new AtomicInteger(0);
    private static final ReentrantLock awaitLock = new ReentrantLock();
    private static final Condition allDone = awaitLock.newCondition();
    private static final Set<ActorThread> actors = ConcurrentHashMap.newKeySet();
    private static volatile boolean shutdownRequested = false;

    public static void init() {
        // Runtime initialization hook — currently a no-op.
    }

    public static <M> Ref<M> spawn(Consumer<Mailbox<M>> actorFn) {
        Mailbox<M> mailbox = new Mailbox<>();
        KryptonRuntime runtime = new KryptonRuntime();
        new ActorThread(() -> actorFn.accept(mailbox), mailbox, runtime);
        return mailbox.ref();
    }

    public static <M> Ref<M> spawn(Mailbox<M> mailbox, Runnable body) {
        KryptonRuntime runtime = new KryptonRuntime();
        new ActorThread(body, mailbox, runtime);
        return mailbox.ref();
    }

    public static void awaitAll() {
        awaitLock.lock();
        try {
            while (actorCount.get() > 0) {
                allDone.await();
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        } finally {
            awaitLock.unlock();
        }
    }

    public static void shutdown() {
        shutdownRequested = true;
        for (ActorThread actor : actors) {
            actor.thread().interrupt();
        }
    }

    public static int actorCount() {
        return actorCount.get();
    }

    static void reset() {
        shutdownRequested = false;
        actors.clear();
        actorCount.set(0);
    }

    void incrementActorCount() {
        actorCount.incrementAndGet();
    }

    void trackActor(ActorThread actor) {
        actors.add(actor);
    }

    void notifyActorDone(ActorThread actor) {
        actors.remove(actor);
        int remaining = actorCount.decrementAndGet();
        if (remaining == 0) {
            awaitLock.lock();
            try {
                allDone.signalAll();
            } finally {
                awaitLock.unlock();
            }
        }
    }

    private KryptonRuntime() {}
}
