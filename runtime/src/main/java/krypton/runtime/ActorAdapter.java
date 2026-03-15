package krypton.runtime;

public final class ActorAdapter {
    private final Object target;
    private final Fun1 wrapperFn;

    public ActorAdapter(Object target, Fun1 wrapperFn) {
        this.target = target;
        this.wrapperFn = wrapperFn;
    }

    public void send(Object msg) {
        Object wrapped = wrapperFn.apply(msg);
        KryptonActors.raw_send(target, wrapped);
    }
}
