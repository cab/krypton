package krypton.runtime;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpServer;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetSocketAddress;
import java.net.URI;
import java.net.URLDecoder;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.Executors;

@SuppressWarnings("unchecked")
public final class KryptonHttp {

    /**
     * Start an HTTP server that forwards every request to the given router actor ref.
     *
     * Protocol: sends Tuple2(httpExchange, replyRef) to the router.
     * Expects Tuple2(statusCode: Long, body: String) back.
     *
     * @param routerRef  actor Ref to forward requests to
     * @param port       port to bind (0 for random free port)
     * @param timeoutMs  timeout in ms waiting for router reply; 500 on timeout
     * @return the HttpServer object
     */
    public static Object startServer(Object routerRef, long port, long timeoutMs) {
        try {
            HttpServer server = HttpServer.create(new InetSocketAddress((int) port), 0);
            server.setExecutor(Executors.newVirtualThreadPerTaskExecutor());
            server.createContext("/", exchange -> handleRequest(exchange, (Ref<Object>) routerRef, timeoutMs));
            server.start();
            return server;
        } catch (IOException e) {
            throw new RuntimeException("Failed to start HTTP server: " + e.getMessage(), e);
        }
    }

    private static void handleRequest(HttpExchange exchange, Ref<Object> routerRef, long timeoutMs) {
        try {
            Mailbox<Object> replyMb = new Mailbox<>();
            Ref<Object> replyRef = replyMb.ref();
            routerRef.send(new Tuple2(exchange, replyRef));

            Object reply = replyMb.receiveTimeout(timeoutMs);
            replyMb.close();

            if (reply != null) {
                Tuple2 response = (Tuple2) reply;
                long status = (Long) response._0();
                String body = (String) response._1();
                sendResponse(exchange, (int) status, body);
            } else {
                sendResponse(exchange, 500, "Internal Server Error");
            }
        } catch (Exception e) {
            try {
                sendResponse(exchange, 500, "Internal Server Error");
            } catch (Exception ignored) {
            }
        }
    }

    private static void sendResponse(HttpExchange exchange, int status, String body) throws IOException {
        byte[] bytes = body.getBytes(StandardCharsets.UTF_8);
        exchange.getResponseHeaders().set("Content-Type", "text/plain; charset=utf-8");
        exchange.sendResponseHeaders(status, bytes.length);
        try (OutputStream os = exchange.getResponseBody()) {
            os.write(bytes);
        }
    }

    // --- Request accessors ---

    public static Object reqMethod(Object request) {
        return ((HttpExchange) request).getRequestMethod();
    }

    public static Object reqPath(Object request) {
        return ((HttpExchange) request).getRequestURI().getPath();
    }

    public static Object reqBody(Object request) {
        try {
            try (InputStream is = ((HttpExchange) request).getRequestBody()) {
                return new String(is.readAllBytes(), StandardCharsets.UTF_8);
            }
        } catch (IOException e) {
            throw new KryptonPanic("Failed to read request body: " + e.getMessage());
        }
    }

    public static Object reqHeader(Object request, Object name) {
        String value = ((HttpExchange) request).getRequestHeaders().getFirst((String) name);
        return value; // null if not present
    }

    public static Object reqQuery(Object request, Object name) {
        String query = ((HttpExchange) request).getRequestURI().getQuery();
        if (query == null) return null;
        String key = (String) name;
        for (String param : query.split("&")) {
            int eq = param.indexOf('=');
            if (eq >= 0) {
                String paramName = param.substring(0, eq);
                if (paramName.equals(key)) {
                    return URLDecoder.decode(param.substring(eq + 1), StandardCharsets.UTF_8);
                }
            } else if (param.equals(key)) {
                return "";
            }
        }
        return null;
    }

    private KryptonHttp() {}
}
