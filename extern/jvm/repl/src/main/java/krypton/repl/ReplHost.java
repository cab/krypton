package krypton.repl;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;

public final class ReplHost {
    private static final byte CMD_LOAD = 1;
    private static final byte CMD_RESET = 2;
    private static final byte CMD_QUIT = 3;

    private static final byte RESP_OK = 0;
    private static final byte RESP_ERROR = 1;

    private final DataInputStream in;
    private final DataOutputStream out;
    private final ReplClassLoader loader;

    public ReplHost(DataInputStream in, DataOutputStream out) {
        this.in = in;
        this.out = out;
        this.loader = new ReplClassLoader(getClass().getClassLoader());
    }

    public void run() throws IOException {
        while (true) {
            int cmd = in.readByte();
            switch (cmd) {
                case CMD_LOAD -> handleLoad();
                case CMD_RESET -> handleReset();
                case CMD_QUIT -> { return; }
                default -> throw new IOException("Unknown command: " + cmd);
            }
        }
    }

    private void handleLoad() throws IOException {
        int classCount = in.readInt();
        String evalClassName = null;
        for (int i = 0; i < classCount; i++) {
            String name = in.readUTF();
            int len = in.readInt();
            byte[] bytes = in.readNBytes(len);
            // Register bytes for lazy loading — don't defineClass yet,
            // because verification may require classes not yet registered.
            loader.register(name.replace('/', '.'), bytes);
            if (i == 0) {
                evalClassName = name.replace('/', '.');
            }
        }

        boolean hasVarName = in.readBoolean();
        String varName = hasVarName ? in.readUTF() : null;

        try {
            Class<?> cls = loader.loadClass(Objects.requireNonNull(evalClassName));
            Method eval = cls.getMethod("eval");
            Object[] resultArr = (Object[]) eval.invoke(null);
            Object value = resultArr[0];
            String display = (String) resultArr[1];

            if (varName != null && value != null) {
                Registry.intern(varName).set(value);
            }

            String resultStr;
            if (display != null) {
                resultStr = display;
            } else if (value == null) {
                resultStr = "()";
            } else if (value.getClass().getName().startsWith("krypton.runtime.Fun")) {
                resultStr = "<function>";
            } else {
                resultStr = value.toString();
            }
            out.writeByte(RESP_OK);
            out.writeUTF(resultStr);
            out.flush();
        } catch (Exception e) {
            Throwable cause = e.getCause() != null ? e.getCause() : e;
            out.writeByte(RESP_ERROR);
            out.writeUTF(cause.getClass().getSimpleName() + ": " + cause.getMessage());
            out.flush();
        }
    }

    private void handleReset() throws IOException {
        Registry.clear();
        out.writeByte(RESP_OK);
        out.writeUTF("reset");
        out.flush();
    }

    public static void main(String[] args) throws IOException {
        var host = new ReplHost(
            new DataInputStream(System.in),
            new DataOutputStream(System.out)
        );
        host.run();
    }

    /**
     * ClassLoader that supports lazy definition from pre-registered byte arrays.
     * Classes are registered first, then defined on demand when loadClass is called.
     * This ensures that class verification can resolve dependencies in any order.
     */
    static final class ReplClassLoader extends ClassLoader {
        private final ConcurrentHashMap<String, byte[]> pending = new ConcurrentHashMap<>();

        ReplClassLoader(ClassLoader parent) {
            super(parent);
        }

        void register(String dotName, byte[] bytes) {
            pending.put(dotName, bytes);
        }

        @Override
        protected Class<?> findClass(String name) throws ClassNotFoundException {
            byte[] bytes = pending.remove(name);
            if (bytes != null) {
                return defineClass(name, bytes, 0, bytes.length);
            }
            throw new ClassNotFoundException(name);
        }
    }
}
