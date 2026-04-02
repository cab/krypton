package krypton.runtime;

public final class KryptonConvert {
    public static double toFloat(long v) { return (double) v; }
    public static long toInt(double v) { return (long) v; }
    public static String intToString(long v) { return String.valueOf(v); }
    public static String floatToString(double v) { return String.valueOf(v); }
    private KryptonConvert() {}
}
