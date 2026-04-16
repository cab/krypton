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

    @Test
    void linkCrashNotifiesCaller() throws Exception {
        Mailbox<Object> callerMb = new Mailbox<>();
        Mailbox<Object> startGate = new Mailbox<>();
        Ref<Object> target = runtime.spawn((Mailbox<Object> mb) -> {
            startGate.enqueue("started");
            mb.receive();
            throw new RuntimeException("boom");
        });
        startGate.receive();
        KryptonActors.raw_link(
                callerMb, target,
                (Fun1<Long, Object>) id -> "normal-" + id,
                (Fun2<Long, String, Object>) (id, msg) -> "crashed-" + id + "-" + msg);
        KryptonActors.raw_send(target, "go");
        Object received = callerMb.receiveTimeout(2000);
        assertNotNull(received);
        assertTrue(((String) received).startsWith("crashed-"));
        assertTrue(((String) received).endsWith("-boom"));
    }

    @Test
    void monitorNormalExitDelivers() throws Exception {
        Mailbox<Object> callerMb = new Mailbox<>();
        Ref<String> target = runtime.spawn((Mailbox<String> mb) -> {
            mb.receive();
        });
        KryptonActors.raw_monitor(
                callerMb, target,
                (Fun1<Long, Object>) id -> "normal-" + id,
                (Fun2<Long, String, Object>) (id, msg) -> "crashed-" + id + "-" + msg);
        target.send("stop");
        Object received = callerMb.receiveTimeout(2000);
        assertNotNull(received);
        assertTrue(((String) received).startsWith("normal-"));
    }

    @Test
    void linkToAlreadyDeadActor() throws Exception {
        Mailbox<Object> callerMb = new Mailbox<>();
        Ref<String> target = runtime.spawn((Mailbox<String> mb) -> {
            // returns immediately
        });
        runtime.awaitAll();
        KryptonActors.raw_link(
                callerMb, target,
                (Fun1<Long, Object>) id -> "normal-" + id,
                (Fun2<Long, String, Object>) (id, msg) -> "crashed-" + id + "-" + msg);
        Object received = callerMb.receiveTimeout(2000);
        assertNotNull(received);
        assertTrue(((String) received).startsWith("normal-"));
    }
}
