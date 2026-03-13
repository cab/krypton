package krypton.runtime;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

class ActorTest {

    @BeforeEach
    void setUp() {
        KryptonRuntime.reset();
    }

    @Test
    void spawnAndReceiveReply() {
        Mailbox<String> replyBox = new Mailbox<>();
        Ref<String> actor = KryptonRuntime.spawn((Mailbox<String> mb) -> {
            String msg = mb.receive();
            if (msg != null) {
                replyBox.enqueue(msg.toUpperCase());
            }
        });
        actor.send("hello");
        KryptonRuntime.awaitAll();
        assertEquals("HELLO", replyBox.receive());
    }

    @Test
    void mainWaitsForAllActors() {
        AtomicReference<String> result = new AtomicReference<>();
        KryptonRuntime.spawn((Mailbox<Object> mb) -> {
            try { Thread.sleep(100); } catch (InterruptedException e) { return; }
            result.set("done");
        });
        KryptonRuntime.awaitAll();
        assertEquals("done", result.get());
    }

    @Test
    void sendToDeadActorIsNoOp() {
        Ref<String> ref = KryptonRuntime.spawn((Mailbox<String> mb) -> {
            // return immediately
        });
        KryptonRuntime.awaitAll();
        // Should not throw
        ref.send("ignored");
    }

    @Test
    void actorCountTracking() throws Exception {
        Mailbox<String> gate1 = new Mailbox<>();
        Mailbox<String> gate2 = new Mailbox<>();
        KryptonRuntime.spawn((Mailbox<Object> mb) -> gate1.receive());
        KryptonRuntime.spawn((Mailbox<Object> mb) -> gate2.receive());
        // Brief pause to let virtual threads start
        Thread.sleep(50);
        assertEquals(2, KryptonRuntime.actorCount());
        gate1.enqueue("go");
        gate2.enqueue("go");
        KryptonRuntime.awaitAll();
        assertEquals(0, KryptonRuntime.actorCount());
    }

    @Test
    void shutdownTerminatesRuntime() {
        assertDoesNotThrow(KryptonRuntime::shutdown);
    }
}
