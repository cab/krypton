package krypton.runtime;

import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

public final class Mailbox<M> {
    private final ConcurrentLinkedQueue<M> queue = new ConcurrentLinkedQueue<>();
    private final ReentrantLock lock = new ReentrantLock();
    private final Condition notEmpty = lock.newCondition();
    private volatile boolean closed = false;

    void enqueue(M msg) {
        if (closed) return;
        queue.add(msg);
        lock.lock();
        try {
            notEmpty.signal();
        } finally {
            lock.unlock();
        }
    }

    public M receive() {
        lock.lock();
        try {
            M msg;
            while ((msg = queue.poll()) == null) {
                if (closed) return null;
                notEmpty.await();
            }
            return msg;
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return null;
        } finally {
            lock.unlock();
        }
    }

    public M receiveTimeout(long millis) {
        long deadline = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(millis);
        lock.lock();
        try {
            M msg;
            while ((msg = queue.poll()) == null) {
                if (closed) return null;
                long remaining = deadline - System.nanoTime();
                if (remaining <= 0) return null;
                notEmpty.await(remaining, TimeUnit.NANOSECONDS);
            }
            return msg;
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return null;
        } finally {
            lock.unlock();
        }
    }

    public Ref<M> ref() {
        return new Ref<>(this);
    }

    public int size() {
        return queue.size();
    }

    void close() {
        closed = true;
        lock.lock();
        try {
            notEmpty.signalAll();
        } finally {
            lock.unlock();
        }
    }
}
