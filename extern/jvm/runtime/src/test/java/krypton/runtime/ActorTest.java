package krypton.runtime;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

class ActorTest {

    private KryptonRuntime runtime;

    @BeforeEach
    void setUp() {
        runtime = new KryptonRuntime();
    }

    @Test
    void spawnAndReceiveReply() {
        Mailbox<String> replyBox = new Mailbox<>();
        Ref<String> actor = runtime.spawn((Mailbox<String> mb) -> {
            String msg = mb.receive();
            if (msg != null) {
                replyBox.enqueue(msg.toUpperCase());
            }
        });
        actor.send("hello");
        runtime.awaitAll();
        assertEquals("HELLO", replyBox.receive());
    }

    @Test
    void mainWaitsForAllActors() {
        AtomicReference<String> result = new AtomicReference<>();
        runtime.spawn((Mailbox<Object> mb) -> {
            try { Thread.sleep(100); } catch (InterruptedException e) { return; }
            result.set("done");
        });
        runtime.awaitAll();
        assertEquals("done", result.get());
    }

    @Test
    void sendToDeadActorIsNoOp() {
        Ref<String> ref = runtime.spawn((Mailbox<String> mb) -> {
            // return immediately
        });
        runtime.awaitAll();
        // Should not throw
        ref.send("ignored");
    }

    @Test
    void actorCountTracking() throws Exception {
        Mailbox<String> gate1 = new Mailbox<>();
        Mailbox<String> gate2 = new Mailbox<>();
        runtime.spawn((Mailbox<Object> mb) -> gate1.receive());
        runtime.spawn((Mailbox<Object> mb) -> gate2.receive());
        // Brief pause to let virtual threads start
        Thread.sleep(50);
        assertEquals(2, runtime.actorCount());
        gate1.enqueue("go");
        gate2.enqueue("go");
        runtime.awaitAll();
        assertEquals(0, runtime.actorCount());
    }

    @Test
    void shutdownTerminatesRuntime() {
        assertDoesNotThrow(runtime::shutdown);
    }
}
