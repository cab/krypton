package krypton.runtime;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

public final class JsonRuntime {

    private static final ObjectMapper MAPPER = new ObjectMapper();

    // ── Internal JSON representation ──────────────────────────────────

    public sealed interface JavaJson {
        record JNull() implements JavaJson {}
        record JBool(boolean value) implements JavaJson {}
        record JNum(double value) implements JavaJson {}
        record JStr(String value) implements JavaJson {}
        record JArr(ArrayList<JavaJson> elements) implements JavaJson {}
        record JObj(LinkedHashMap<String, JavaJson> entries) implements JavaJson {}
        JNull NULL_INSTANCE = new JNull();
    }

    // ── Int tags for staticRawType ────────────────────────────────────

    private static final long TAG_NULL = 0, TAG_BOOL = 1, TAG_NUM = 2,
                               TAG_STR = 3, TAG_ARR = 4, TAG_OBJ = 5;

    // ── Jackson → JavaJson ────────────────────────────────────────────

    private static JavaJson fromNode(JsonNode node) {
        if (node == null || node.isNull()) return JavaJson.NULL_INSTANCE;
        if (node.isBoolean()) return new JavaJson.JBool(node.booleanValue());
        if (node.isNumber()) return new JavaJson.JNum(node.doubleValue());
        if (node.isTextual()) return new JavaJson.JStr(node.textValue());
        if (node.isArray()) {
            var elements = new ArrayList<JavaJson>();
            for (JsonNode child : node) elements.add(fromNode(child));
            return new JavaJson.JArr(elements);
        }
        // object
        var entries = new LinkedHashMap<String, JavaJson>();
        Iterator<Map.Entry<String, JsonNode>> it = node.fields();
        while (it.hasNext()) {
            var entry = it.next();
            entries.put(entry.getKey(), fromNode(entry.getValue()));
        }
        return new JavaJson.JObj(entries);
    }

    // ── JavaJson → JSON string ────────────────────────────────────────

    private static void writeJson(JavaJson j, StringBuilder sb) {
        switch (j) {
            case JavaJson.JNull n -> sb.append("null");
            case JavaJson.JBool b -> sb.append(b.value());
            case JavaJson.JNum n -> {
                if (n.value() == Math.floor(n.value()) && !Double.isInfinite(n.value())) {
                    sb.append((long) n.value());
                } else {
                    sb.append(n.value());
                }
            }
            case JavaJson.JStr s -> {
                sb.append('"');
                sb.append(escapeString(s.value()));
                sb.append('"');
            }
            case JavaJson.JArr a -> {
                sb.append('[');
                for (int i = 0; i < a.elements().size(); i++) {
                    if (i > 0) sb.append(',');
                    writeJson(a.elements().get(i), sb);
                }
                sb.append(']');
            }
            case JavaJson.JObj o -> {
                sb.append('{');
                boolean first = true;
                for (var entry : o.entries().entrySet()) {
                    if (!first) sb.append(',');
                    sb.append('"');
                    sb.append(escapeString(entry.getKey()));
                    sb.append('"');
                    sb.append(':');
                    writeJson(entry.getValue(), sb);
                    first = false;
                }
                sb.append('}');
            }
        }
    }

    private static String escapeString(String s) {
        var sb = new StringBuilder(s.length());
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\b' -> sb.append("\\b");
                case '\f' -> sb.append("\\f");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                default -> {
                    if (c < 0x20) {
                        sb.append(String.format("\\u%04x", (int) c));
                    } else {
                        sb.append(c);
                    }
                }
            }
        }
        return sb.toString();
    }

    // ── Static methods exposed to Krypton ─────────────────────────────

    // Parse: returns 2-element KryptonArray [ok, value_or_error]
    public static Object staticParse(String s) {
        try {
            JsonNode node = MAPPER.readTree(s);
            KryptonArray result = new KryptonArray(2);
            result.set(0, true);
            result.set(1, fromNode(node));
            result.freeze();
            return result;
        } catch (Exception e) {
            KryptonArray result = new KryptonArray(2);
            result.set(0, false);
            result.set(1, e.getMessage());
            result.freeze();
            return result;
        }
    }

    // Serialize: JavaJson → JSON string
    public static String staticSerialize(JavaJson j) {
        StringBuilder sb = new StringBuilder();
        writeJson(j, sb);
        return sb.toString();
    }

    // ── Inspect methods (for from_java conversion) ────────────────────

    public static long staticRawType(JavaJson j) {
        return switch (j) {
            case JavaJson.JNull n -> TAG_NULL;
            case JavaJson.JBool b -> TAG_BOOL;
            case JavaJson.JNum n -> TAG_NUM;
            case JavaJson.JStr s -> TAG_STR;
            case JavaJson.JArr a -> TAG_ARR;
            case JavaJson.JObj o -> TAG_OBJ;
        };
    }

    public static boolean staticRawBool(JavaJson j) {
        return ((JavaJson.JBool) j).value();
    }

    public static double staticRawNum(JavaJson j) {
        return ((JavaJson.JNum) j).value();
    }

    public static String staticRawStr(JavaJson j) {
        return ((JavaJson.JStr) j).value();
    }

    public static KryptonArray staticRawArr(JavaJson j) {
        ArrayList<JavaJson> elements = ((JavaJson.JArr) j).elements();
        KryptonArray arr = new KryptonArray(elements.size());
        for (int i = 0; i < elements.size(); i++) {
            arr.set(i, elements.get(i));
        }
        arr.freeze();
        return arr;
    }

    public static KryptonArray staticRawEntryKeys(JavaJson j) {
        LinkedHashMap<String, JavaJson> map = ((JavaJson.JObj) j).entries();
        KryptonArray arr = new KryptonArray(map.size());
        int i = 0;
        for (String key : map.keySet()) {
            arr.set(i++, key);
        }
        arr.freeze();
        return arr;
    }

    public static KryptonArray staticRawEntryValues(JavaJson j) {
        LinkedHashMap<String, JavaJson> map = ((JavaJson.JObj) j).entries();
        KryptonArray arr = new KryptonArray(map.size());
        int i = 0;
        for (JavaJson value : map.values()) {
            arr.set(i++, value);
        }
        arr.freeze();
        return arr;
    }

    // ── Build methods (for to_java conversion) ────────────────────────

    public static JavaJson staticMkNull() {
        return JavaJson.NULL_INSTANCE;
    }

    public static JavaJson staticMkBool(boolean b) {
        return new JavaJson.JBool(b);
    }

    public static JavaJson staticMkNum(double n) {
        return new JavaJson.JNum(n);
    }

    public static JavaJson staticMkStr(String s) {
        return new JavaJson.JStr(s);
    }

    public static JavaJson staticNewArr() {
        return new JavaJson.JArr(new ArrayList<>());
    }

    public static void staticArrPush(JavaJson arr, JavaJson elem) {
        ((JavaJson.JArr) arr).elements().add(elem);
    }

    public static JavaJson staticNewObj() {
        return new JavaJson.JObj(new LinkedHashMap<>());
    }

    public static void staticObjPut(JavaJson obj, String key, JavaJson value) {
        ((JavaJson.JObj) obj).entries().put(key, value);
    }

    private JsonRuntime() {}
}
