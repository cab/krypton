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

    private static final class JavaJson {
        final String type; // "null", "bool", "num", "str", "arr", "obj"
        boolean boolVal;
        double numVal;
        String strVal;
        ArrayList<JavaJson> arrVal;
        LinkedHashMap<String, JavaJson> objVal;

        private JavaJson(String type) { this.type = type; }

        static JavaJson ofNull() { return new JavaJson("null"); }
        static JavaJson ofBool(boolean v) { var j = new JavaJson("bool"); j.boolVal = v; return j; }
        static JavaJson ofNum(double v) { var j = new JavaJson("num"); j.numVal = v; return j; }
        static JavaJson ofStr(String v) { var j = new JavaJson("str"); j.strVal = v; return j; }
        static JavaJson ofArr() { var j = new JavaJson("arr"); j.arrVal = new ArrayList<>(); return j; }
        static JavaJson ofObj() { var j = new JavaJson("obj"); j.objVal = new LinkedHashMap<>(); return j; }
    }

    // ── Jackson → JavaJson ────────────────────────────────────────────

    private static JavaJson fromNode(JsonNode node) {
        if (node == null || node.isNull()) return JavaJson.ofNull();
        if (node.isBoolean()) return JavaJson.ofBool(node.booleanValue());
        if (node.isNumber()) return JavaJson.ofNum(node.doubleValue());
        if (node.isTextual()) return JavaJson.ofStr(node.textValue());
        if (node.isArray()) {
            var arr = JavaJson.ofArr();
            for (JsonNode child : node) arr.arrVal.add(fromNode(child));
            return arr;
        }
        // object
        var obj = JavaJson.ofObj();
        Iterator<Map.Entry<String, JsonNode>> it = node.fields();
        while (it.hasNext()) {
            var entry = it.next();
            obj.objVal.put(entry.getKey(), fromNode(entry.getValue()));
        }
        return obj;
    }

    // ── JavaJson → JSON string ────────────────────────────────────────

    private static void writeJson(JavaJson j, StringBuilder sb) {
        switch (j.type) {
            case "null" -> sb.append("null");
            case "bool" -> sb.append(j.boolVal);
            case "num" -> {
                if (j.numVal == Math.floor(j.numVal) && !Double.isInfinite(j.numVal)) {
                    sb.append((long) j.numVal);
                } else {
                    sb.append(j.numVal);
                }
            }
            case "str" -> {
                sb.append('"');
                sb.append(escapeString(j.strVal));
                sb.append('"');
            }
            case "arr" -> {
                sb.append('[');
                for (int i = 0; i < j.arrVal.size(); i++) {
                    if (i > 0) sb.append(',');
                    writeJson(j.arrVal.get(i), sb);
                }
                sb.append(']');
            }
            case "obj" -> {
                sb.append('{');
                boolean first = true;
                for (var entry : j.objVal.entrySet()) {
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
            default -> throw new KryptonPanic("unknown json type: " + j.type);
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

    // Parse: returns 2-element KryptonArray [result_or_null, error_or_null]
    public static Object staticParse(String s) {
        try {
            JsonNode node = MAPPER.readTree(s);
            KryptonArray result = new KryptonArray(2);
            result.set(0, fromNode(node));
            result.set(1, null);
            result.freeze();
            return result;
        } catch (Exception e) {
            KryptonArray result = new KryptonArray(2);
            result.set(0, null);
            result.set(1, e.getMessage());
            result.freeze();
            return result;
        }
    }

    // Serialize: JavaJson → JSON string
    public static String staticSerialize(Object j) {
        StringBuilder sb = new StringBuilder();
        writeJson((JavaJson) j, sb);
        return sb.toString();
    }

    // ── Inspect methods (for from_java conversion) ────────────────────

    public static String staticRawType(Object j) {
        return ((JavaJson) j).type;
    }

    public static boolean staticRawBool(Object j) {
        return ((JavaJson) j).boolVal;
    }

    public static double staticRawNum(Object j) {
        return ((JavaJson) j).numVal;
    }

    public static String staticRawStr(Object j) {
        return ((JavaJson) j).strVal;
    }

    // Returns KryptonArray of JavaJson elements
    public static Object staticRawArr(Object j) {
        ArrayList<JavaJson> elements = ((JavaJson) j).arrVal;
        KryptonArray arr = new KryptonArray(elements.size());
        for (int i = 0; i < elements.size(); i++) {
            arr.set(i, elements.get(i));
        }
        arr.freeze();
        return arr;
    }

    // Returns KryptonArray of [key0, val0, key1, val1, ...]
    public static Object staticRawEntries(Object j) {
        LinkedHashMap<String, JavaJson> map = ((JavaJson) j).objVal;
        KryptonArray arr = new KryptonArray(map.size() * 2);
        int i = 0;
        for (var entry : map.entrySet()) {
            arr.set(i, entry.getKey());
            arr.set(i + 1, entry.getValue());
            i += 2;
        }
        arr.freeze();
        return arr;
    }

    // ── Build methods (for to_java conversion) ────────────────────────

    public static Object staticMkNull() {
        return JavaJson.ofNull();
    }

    public static Object staticMkBool(boolean b) {
        return JavaJson.ofBool(b);
    }

    public static Object staticMkNum(double n) {
        return JavaJson.ofNum(n);
    }

    public static Object staticMkStr(String s) {
        return JavaJson.ofStr(s);
    }

    public static Object staticNewArr() {
        return JavaJson.ofArr();
    }

    public static void staticArrPush(Object arr, Object elem) {
        ((JavaJson) arr).arrVal.add((JavaJson) elem);
    }

    public static Object staticNewObj() {
        return JavaJson.ofObj();
    }

    public static void staticObjPut(Object obj, Object key, Object value) {
        ((JavaJson) obj).objVal.put((String) key, (JavaJson) value);
    }

    private JsonRuntime() {}
}
