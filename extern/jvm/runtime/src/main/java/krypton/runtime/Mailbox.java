package krypton.runtime;

import java.util.concurrent.LinkedTransferQueue;
import java.util.concurrent.TimeUnit;

public final class Mailbox<M> {
    private final LinkedTransferQueue<M> queue = new LinkedTransferQueue<>();
    private volatile boolean closed = false;
    volatile ActorThread ownerActor;

    void enqueue(M msg) {
        if (closed) return;
        queue.put(msg);
    }

    public M receive() {
        try {
            while (!closed) {
                M msg = queue.poll(100, TimeUnit.MILLISECONDS);
                if (msg != null) return msg;
            }
            return queue.poll(); // drain any remaining
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return null;
        }
    }

    public M receiveTimeout(long millis) {
        try {
            M msg = queue.poll(millis, TimeUnit.MILLISECONDS);
            if (msg != null) return msg;
            if (closed) return null;
            return null;
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return null;
        }
    }

    public Ref<M> ref() {
        return new Ref<>(this, ownerActor);
    }

    public int size() {
        return queue.size();
    }

    void close() {
        closed = true;
    }
}
