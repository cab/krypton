package krypton.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class MailboxTest {

    @Test
    void receiveBlocksUntilSend() throws Exception {
        Mailbox<String> mb = new Mailbox<>();
        Thread.startVirtualThread(() -> {
            try { Thread.sleep(50); } catch (InterruptedException e) { return; }
            mb.enqueue("hello");
        });
        assertEquals("hello", mb.receive());
    }

    @Test
    void receiveTimeoutReturnsNull() {
        Mailbox<String> mb = new Mailbox<>();
        assertNull(mb.receiveTimeout(50));
    }

    @Test
    void receiveTimeoutReturnsValue() {
        Mailbox<String> mb = new Mailbox<>();
        mb.enqueue("present");
        assertEquals("present", mb.receiveTimeout(100));
    }

    @Test
    void fifoOrdering() {
        Mailbox<String> mb = new Mailbox<>();
        mb.enqueue("a");
        mb.enqueue("b");
        mb.enqueue("c");
        assertEquals("a", mb.receive());
        assertEquals("b", mb.receive());
        assertEquals("c", mb.receive());
    }

    @Test
    void sizeReflectsQueueDepth() {
        Mailbox<String> mb = new Mailbox<>();
        mb.enqueue("x");
        mb.enqueue("y");
        mb.enqueue("z");
        assertEquals(3, mb.size());
        mb.receive();
        assertEquals(2, mb.size());
    }

    @Test
    void refSendAndReceive() {
        Mailbox<String> mb = new Mailbox<>();
        Ref<String> ref = mb.ref();
        ref.send("via-ref");
        assertEquals("via-ref", mb.receive());
    }
}
