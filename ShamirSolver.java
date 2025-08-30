import java.io.*;
import java.math.*;
import java.util.*;
import java.util.regex.*;

public class ShamirSolver {
    static class BigRational {
        final BigInteger num;
        final BigInteger den;
        BigRational(BigInteger n, BigInteger d) {
            if (d.signum() == 0) throw new ArithmeticException("zero denominator");
            if (d.signum() < 0) {
                n = n.negate();
                d = d.negate();
            }
            BigInteger g = n.gcd(d);
            if (!g.equals(BigInteger.ONE)) {
                n = n.divide(g);
                d = d.divide(g);
            }
            this.num = n;
            this.den = d;
        }
        static BigRational valueOf(BigInteger v) {
            return new BigRational(v, BigInteger.ONE);
        }
        static BigRational zero() { return new BigRational(BigInteger.ZERO, BigInteger.ONE); }
        static BigRational one() { return new BigRational(BigInteger.ONE, BigInteger.ONE); }
        BigRational add(BigRational o) {
            BigInteger n = this.num.multiply(o.den).add(o.num.multiply(this.den));
            BigInteger d = this.den.multiply(o.den);
            return new BigRational(n, d);
        }
        BigRational subtract(BigRational o) {
            BigInteger n = this.num.multiply(o.den).subtract(o.num.multiply(this.den));
            BigInteger d = this.den.multiply(o.den);
            return new BigRational(n, d);
        }

        BigRational multiply(BigRational o) {
            BigInteger n = this.num.multiply(o.num);
            BigInteger d = this.den.multiply(o.den);
            return new BigRational(n, d);
        }

        BigRational divide(BigRational o) {
            if (o.num.equals(BigInteger.ZERO)) throw new ArithmeticException("divide by zero");
            BigInteger n = this.num.multiply(o.den);
            BigInteger d = this.den.multiply(o.num);
            return new BigRational(n, d);
        }

        BigRational negate() {
            return new BigRational(this.num.negate(), this.den);
        }

        boolean equalsTo(BigRational o) {
            return this.num.equals(o.num) && this.den.equals(o.den);
        }

        @Override
        public String toString() {
            if (den.equals(BigInteger.ONE)) return num.toString();
            return num.toString() + "/" + den.toString();
        }
    }

    static BigRational[] solveForCoefficients(List<BigInteger> xs, List<BigInteger> ys) {
        int k = xs.size();
        BigRational[][] A = new BigRational[k][k + 1];

        for (int i = 0; i < k; ++i) {
            BigInteger xi = xs.get(i);
            BigInteger pow = BigInteger.ONE;
            for (int j = 0; j < k; ++j) {
                A[i][j] = BigRational.valueOf(pow);
                pow = pow.multiply(xi);
            }
            A[i][k] = BigRational.valueOf(ys.get(i));
        }
        int row = 0;
        for (int col = 0; col < k && row < k; ++col) {
            int sel = -1;
            for (int i = row; i < k; ++i) {
                if (!A[i][col].num.equals(BigInteger.ZERO)) { sel = i; break; }
            }
            if (sel == -1) continue;
            if (sel != row) {
                BigRational[] tmp = A[sel]; A[sel] = A[row]; A[row] = tmp;
            }
            BigRational pivot = A[row][col];
            for (int j = col; j <= k; ++j) {
                A[row][j] = A[row][j].divide(pivot);
            }
            for (int i = 0; i < k; ++i) {
                if (i == row) continue;
                BigRational factor = A[i][col];
                if (factor.num.equals(BigInteger.ZERO)) continue;
                for (int j = col; j <= k; ++j) {
                    A[i][j] = A[i][j].subtract(A[row][j].multiply(factor));
                }
            }
            row++;
        }
        BigRational[] coef = new BigRational[k];
        for (int i = 0; i < k; ++i) coef[i] = BigRational.zero();

        for (int i = 0; i < k; ++i) {
            int pivotCol = -1;
            for (int j = 0; j < k; ++j) {
                if (!A[i][j].num.equals(BigInteger.ZERO)) { pivotCol = j; break; }
            }
            if (pivotCol == -1) {
                if (!A[i][k].num.equals(BigInteger.ZERO)) return null; 
                continue;
            }
            coef[pivotCol] = A[i][k];
        }
        return coef;
    }
    static BigRational evaluatePolynomial(BigRational[] coef, BigInteger x) {
        BigRational res = BigRational.zero();
        BigInteger pow = BigInteger.ONE;
        for (int i = 0; i < coef.length; ++i) {
            res = res.add(coef[i].multiply(BigRational.valueOf(pow)));
            pow = pow.multiply(x);
        }
        return res;
    }
    static void combine(int n, int k, int start, int idx, int[] cur, List<int[]> out) {
        if (idx == k) {
            out.add(cur.clone());
            return;
        }
        for (int i = start; i <= n - (k - idx); ++i) {
            cur[idx] = i;
            combine(n, k, i + 1, idx + 1, cur, out);
        }
    }
    static Map<String, Map<String,String>> parseShares(String json) {
        Map<String, Map<String,String>> shares = new LinkedHashMap<>();
        Pattern p = Pattern.compile("\"(\\d+)\"\\s*:\\s*\\{\\s*\"base\"\\s*:\\s*\"(\\d+)\"\\s*,\\s*\"value\"\\s*:\\s*\"([^\"]+)\"\\s*\\}", Pattern.DOTALL);
        Matcher m = p.matcher(json);
        while (m.find()) {
            String key = m.group(1); 
            String base = m.group(2);
            String value = m.group(3);
            Map<String,String> obj = new HashMap<>();
            obj.put("base", base);
            obj.put("value", value);
            shares.put(key, obj);
        }
        return shares;
    }

    static int[] parseKeysNK(String json) {
        int n = -1, k = -1;
        Pattern p = Pattern.compile("\"keys\"\\s*:\\s*\\{(.+?)\\}", Pattern.DOTALL);
        Matcher m = p.matcher(json);
        if (m.find()) {
            String inside = m.group(1);
            Pattern p2 = Pattern.compile("\"n\"\\s*:\\s*(\\d+)");
            Matcher m2 = p2.matcher(inside);
            if (m2.find()) n = Integer.parseInt(m2.group(1));
            Pattern p3 = Pattern.compile("\"k\"\\s*:\\s*(\\d+)");
            Matcher m3 = p3.matcher(inside);
            if (m3.find()) k = Integer.parseInt(m3.group(1));
        }
        return new int[]{n, k};
    }

    static BigInteger parseValueInBase(String value, int base) {
        return new BigInteger(value, base);
    }

    public static void main(String[] args) throws Exception {
        StringBuilder sb = new StringBuilder();
        try (BufferedReader br = new BufferedReader(new InputStreamReader(System.in))) {
            String line;
            while ((line = br.readLine()) != null) {
                sb.append(line).append("\n");
            }
        }
        String json = sb.toString();
        if (json.trim().isEmpty()) {
            System.err.println("No input.");
            return;
        }
        int[] nk = parseKeysNK(json);
        int n = nk[0], k = nk[1];
        if (n == -1 || k == -1) {
            System.err.println("Could not parse n and k from JSON.");
            return;
        }
        Map<String, Map<String,String>> rawShares = parseShares(json);
        List<String> labels = new ArrayList<>();
        List<BigInteger> xs = new ArrayList<>();
        List<BigInteger> ys = new ArrayList<>();

        for (Map.Entry<String, Map<String,String>> e : rawShares.entrySet()) {
            String label = e.getKey(); 
            Map<String,String> obj = e.getValue();
            String baseStr = obj.get("base");
            String valStr = obj.get("value");
            if (baseStr == null || valStr == null) continue;
            int base = Integer.parseInt(baseStr);
            BigInteger y = parseValueInBase(valStr, base);
            BigInteger x = new BigInteger(label); 
            labels.add(label);
            xs.add(x);
            ys.add(y);
        }

        if (xs.size() < n) {
        }

        int total = xs.size();
        if (total < k) {
            System.err.println("Not enough shares provided: total=" + total + " but k=" + k);
            return;
        }

        List<int[]> combos = new ArrayList<>();
        combine(total, k, 0, 0, new int[k], combos);
        boolean found = false;
        BigRational[] bestCoeffs = null;
        String badLabel = "NONE";

        for (int[] comb : combos) {
            List<BigInteger> sx = new ArrayList<>();
            List<BigInteger> sy = new ArrayList<>();
            for (int idx : comb) {
                sx.add(xs.get(idx));
                sy.add(ys.get(idx));
            }
            BigRational[] coeffs;
            try {
                coeffs = solveForCoefficients(sx, sy);
            } catch (Exception ex) {
                continue;
            }
            if (coeffs == null) continue;

            int mismatches = 0;
            int mismatchIndex = -1;
            for (int i = 0; i < total; ++i) {
                BigRational val = evaluatePolynomial(coeffs, xs.get(i));
                BigRational expected = BigRational.valueOf(ys.get(i));
                if (!val.equalsTo(expected)) {
                    mismatches++;
                    mismatchIndex = i;
                    if (mismatches > 1) break;
                }
            }
            if (mismatches <= 1) {
                found = true;
                bestCoeffs = coeffs;
                if (mismatches == 1) badLabel = labels.get(mismatchIndex);
                else badLabel = "NONE";
                break;
            }
        }

        if (!found) {
            System.err.println("No valid polynomial found that matches all but at most one share.");
            return;
        }

        BigRational secretRat = bestCoeffs[0];
        if (!secretRat.den.equals(BigInteger.ONE)) {
            if (secretRat.num.mod(secretRat.den).equals(BigInteger.ZERO)) {
                BigInteger secretInt = secretRat.num.divide(secretRat.den);
                System.out.println(secretInt.toString());
            } else {
                System.out.println(secretRat.toString());
            }
        } else {
            System.out.println(secretRat.num.toString());
        }
        System.out.println(badLabel);
    }
}