//! Math expression evaluator for the finder.
//!
//! This is a port of dwm's finder calculator (`finder_math_*` in `dwm.c`).
//! Expressions are parsed with a small recursive-descent parser over `f64`
//! values; a query is only turned into a result when dwm would have activated
//! math mode (an operator is present, or the whole query is a known constant).

const MAX_IDENT_LEN: usize = 32;
/// 2^53, the largest integer every f64 can represent exactly. dwm's bit helpers
/// refuse values outside this range.
const MAX_EXACT_INT: f64 = 9_007_199_254_740_992.0;
const PI: f64 = std::f64::consts::PI;

/// Mirrors dwm's `finder_query_is_numeric_expression()`.
///
/// This is a *guard* for partially typed calculator input: it is true when the
/// query contains a digit and an operator and nothing else but digits,
/// operators, `.` and whitespace. It intentionally does not recognize named
/// constants (e.g. `pi`), because it is used to keep such input out of
/// translation/app search while the user is still typing.
pub fn is_math_expression(s: &str) -> bool {
    let mut has_digit = false;
    let mut has_operator = false;

    for b in s.bytes() {
        if b.is_ascii_digit() {
            has_digit = true;
        } else if matches!(
            b,
            b'+' | b'-' | b'*' | b'/' | b'%' | b'^' | b'!' | b'(' | b')' | b'='
        ) {
            has_operator = true;
        } else if b != b'.' && !b.is_ascii_whitespace() {
            return false;
        }
    }
    has_digit && has_operator
}

/// Evaluates `expression` and returns the `%.15g`-formatted result, or `None`
/// when the query should not be shown as math (invalid syntax, non-finite
/// intermediate result, or an ordinary search string such as `"firefox"`).
pub fn evaluate(expression: &str) -> Option<String> {
    // dwm trims trailing whitespace and then one conventional '=' marker.
    let mut text = expression.trim_end_matches(|c: char| c.is_ascii_whitespace());
    if let Some(rest) = text.strip_suffix('=') {
        text = rest;
    }
    if text.is_empty() {
        return None;
    }
    // The C version switches to the math help screen here; there is no result
    // string to return, so report "no math result".
    if text.eq_ignore_ascii_case("math") {
        return None;
    }

    let has_operator = text.bytes().any(|b| {
        matches!(
            b,
            b'+' | b'-' | b'*' | b'/' | b'%' | b'^' | b'!' | b'(' | b')'
        )
    });

    if !has_operator {
        // Without an operator dwm only accepts a bare constant name.
        let mut parser = Parser::new(text);
        parser.skip_ws();
        let name = parser.identifier()?;
        parser.skip_ws();
        if !parser.at_end() {
            return None;
        }
        return constant(&name).map(format_g15);
    }

    let mut parser = Parser::new(text);
    let value = parser.expression()?;
    parser.skip_ws();
    if !parser.at_end() {
        return None;
    }
    Some(format_g15(value))
}

struct Parser<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        // C strings end at NUL; mirror that truncation.
        let bytes = input.as_bytes();
        let len = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
        Self {
            input: &bytes[..len],
            pos: 0,
        }
    }

    fn peek(&self) -> u8 {
        self.input.get(self.pos).copied().unwrap_or(0)
    }

    fn at_end(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn bump(&mut self) {
        if self.pos < self.input.len() {
            self.pos += 1;
        }
    }

    fn skip_ws(&mut self) {
        while self.peek().is_ascii_whitespace() {
            self.bump();
        }
    }

    fn identifier(&mut self) -> Option<String> {
        let start = self.pos;
        if !(self.peek().is_ascii_alphabetic() || self.peek() == b'_') {
            return None;
        }
        self.bump();
        while self.peek().is_ascii_alphanumeric() || self.peek() == b'_' {
            self.bump();
        }
        let len = self.pos - start;
        if len >= MAX_IDENT_LEN {
            return None;
        }
        std::str::from_utf8(&self.input[start..self.pos])
            .ok()
            .map(str::to_owned)
    }

    /// A `strtod`-style number token: decimal (with optional exponent) or
    /// hexadecimal float. Non-finite and ERANGE-style underflow results fail.
    fn number(&mut self) -> Option<f64> {
        let start = self.pos;
        let bytes = self.input;
        let mut p = start;
        let value;

        let is_hex = bytes.get(p) == Some(&b'0') && matches!(bytes.get(p + 1), Some(b'x' | b'X'));

        if is_hex {
            p += 2;
            let mut digits = 0usize;
            while bytes.get(p).is_some_and(|b| b.is_ascii_hexdigit()) {
                p += 1;
                digits += 1;
            }
            if bytes.get(p) == Some(&b'.') {
                p += 1;
                while bytes.get(p).is_some_and(|b| b.is_ascii_hexdigit()) {
                    p += 1;
                    digits += 1;
                }
            }
            if digits == 0 {
                return None;
            }
            if matches!(bytes.get(p), Some(b'p' | b'P')) {
                let mut q = p + 1;
                if matches!(bytes.get(q), Some(b'+' | b'-')) {
                    q += 1;
                }
                let exp_start = q;
                while bytes.get(q).is_some_and(|b| b.is_ascii_digit()) {
                    q += 1;
                }
                if q > exp_start {
                    p = q;
                }
            }
            let token = std::str::from_utf8(&bytes[start..p]).ok()?;
            value = parse_hex_float(token)?;
        } else {
            let mut digits = 0usize;
            while bytes.get(p).is_some_and(|b| b.is_ascii_digit()) {
                p += 1;
                digits += 1;
            }
            if bytes.get(p) == Some(&b'.') {
                p += 1;
                while bytes.get(p).is_some_and(|b| b.is_ascii_digit()) {
                    p += 1;
                    digits += 1;
                }
            }
            if digits == 0 {
                return None;
            }
            if matches!(bytes.get(p), Some(b'e' | b'E')) {
                let mut q = p + 1;
                if matches!(bytes.get(q), Some(b'+' | b'-')) {
                    q += 1;
                }
                let exp_start = q;
                while bytes.get(q).is_some_and(|b| b.is_ascii_digit()) {
                    q += 1;
                }
                if q > exp_start {
                    p = q;
                }
            }
            let token = std::str::from_utf8(&bytes[start..p]).ok()?;
            value = token.parse::<f64>().ok()?;
            // strtod sets ERANGE for overflow, underflow to zero and subnormal
            // results; dwm rejects all three in finder_math_primary().
            if !value.is_finite() || (value != 0.0 && value.abs() < f64::MIN_POSITIVE) {
                return None;
            }
            let mantissa = token
                .split(|c| c == 'e' || c == 'E')
                .next()
                .unwrap_or(token);
            if value == 0.0 && mantissa.bytes().any(|b| matches!(b, b'1'..=b'9')) {
                return None;
            }
        }

        self.pos = p;
        Some(value)
    }

    fn primary(&mut self) -> Option<f64> {
        self.skip_ws();
        if self.peek() == b'(' {
            self.bump();
            let value = self.expression()?;
            self.skip_ws();
            if self.peek() != b')' {
                return None;
            }
            self.bump();
            return Some(value);
        }
        if self.peek().is_ascii_alphabetic() || self.peek() == b'_' {
            let name = self.identifier()?;
            self.skip_ws();
            if self.peek() == b'(' {
                let args = self.args()?;
                return apply(&name, &args);
            }
            return constant(&name);
        }
        self.number()
    }

    /// Parses up to two comma-separated arguments. Commas are not expression
    /// operators, so `expression()` naturally stops at the next comma or ')'.
    fn args(&mut self) -> Option<Vec<f64>> {
        self.skip_ws();
        if self.peek() != b'(' {
            return None;
        }
        self.bump();
        let mut args = Vec::with_capacity(2);
        self.skip_ws();
        if self.peek() == b')' {
            self.bump();
            return Some(args);
        }
        while args.len() < 2 {
            args.push(self.expression()?);
            self.skip_ws();
            if self.peek() == b',' {
                self.bump();
                continue;
            }
            if self.peek() == b')' {
                self.bump();
                return Some(args);
            }
            return None;
        }
        None
    }

    fn postfix(&mut self) -> Option<f64> {
        let mut value = self.primary()?;
        loop {
            self.skip_ws();
            if self.peek() != b'!' {
                return Some(value);
            }
            self.bump();
            value = factorial(value)?;
        }
    }

    fn power(&mut self) -> Option<f64> {
        let mut value = self.postfix()?;
        self.skip_ws();
        if self.peek() == b'^' {
            self.bump();
            let rhs = self.unary()?;
            value = value.powf(rhs);
            if !value.is_finite() {
                return None;
            }
        }
        Some(value)
    }

    fn unary(&mut self) -> Option<f64> {
        self.skip_ws();
        match self.peek() {
            b'+' => {
                self.bump();
                self.unary()
            }
            b'-' => {
                self.bump();
                Some(-self.unary()?)
            }
            _ => self.power(),
        }
    }

    fn term(&mut self) -> Option<f64> {
        let mut value = self.unary()?;
        loop {
            self.skip_ws();
            let op = self.peek();
            if !matches!(op, b'*' | b'/' | b'%') {
                return Some(value);
            }
            self.bump();
            let rhs = self.unary()?;
            match op {
                b'*' => value *= rhs,
                b'/' | b'%' => {
                    if rhs == 0.0 {
                        return None;
                    }
                    if op == b'/' {
                        value /= rhs;
                    } else {
                        value %= rhs;
                    }
                }
                _ => return None,
            }
            if !value.is_finite() {
                return None;
            }
        }
    }

    fn expression(&mut self) -> Option<f64> {
        let mut value = self.term()?;
        loop {
            self.skip_ws();
            let op = self.peek();
            if !matches!(op, b'+' | b'-') {
                return Some(value);
            }
            self.bump();
            let rhs = self.term()?;
            value = if op == b'+' { value + rhs } else { value - rhs };
            if !value.is_finite() {
                return None;
            }
        }
    }
}

// `f64::cbrt` uses Rust's own math library, which differs from glibc's cbrt
// by one ulp for some inputs. Call the C library function to keep results
// bit-identical to dwm's calculator.
#[cfg(unix)]
#[link(name = "m")]
unsafe extern "C" {
    #[link_name = "cbrt"]
    fn libc_cbrt(value: f64) -> f64;
}

fn cbrt(value: f64) -> f64 {
    #[cfg(unix)]
    unsafe {
        libc_cbrt(value)
    }
    #[cfg(not(unix))]
    {
        value.cbrt()
    }
}

fn constant(name: &str) -> Option<f64> {
    let lower = name.to_ascii_lowercase();
    let value = match lower.as_str() {
        "pi" => PI,
        "e" => std::f64::consts::E,
        "tau" => std::f64::consts::TAU,
        "phi" => std::f64::consts::GOLDEN_RATIO,
        "epsilon" => f64::EPSILON,
        "byte_max" => 255.0,
        "word_max" => 65535.0,
        "dword_max" | "uint_max" => 4294967295.0,
        "int_max" => 2147483647.0,
        "int_min" => -2147483648.0,
        "kb" => 1024.0,
        "mb" => 1048576.0,
        "gb" => 1073741824.0,
        "tb" => 1099511627776.0,
        "true" => 1.0,
        "false" => 0.0,
        _ => return None,
    };
    Some(value)
}

fn apply(name: &str, args: &[f64]) -> Option<f64> {
    let lower = name.to_ascii_lowercase();
    let value = match (lower.as_str(), args) {
        ("sqrt", [v]) => {
            if *v < 0.0 {
                return None;
            }
            v.sqrt()
        }
        ("cbrt", [v]) => cbrt(*v),
        ("abs", [v]) => v.abs(),
        ("exp", [v]) => v.exp(),
        ("ln" | "log", [v]) => {
            if *v <= 0.0 {
                return None;
            }
            v.ln()
        }
        ("log2", [v]) => {
            if *v <= 0.0 {
                return None;
            }
            v.log2()
        }
        ("log10", [v]) => {
            if *v <= 0.0 {
                return None;
            }
            v.log10()
        }
        ("sin", [v]) => v.sin(),
        ("cos", [v]) => v.cos(),
        ("tan", [v]) => v.tan(),
        ("asin", [v]) => {
            if !(-1.0..=1.0).contains(v) {
                return None;
            }
            v.asin()
        }
        ("acos", [v]) => {
            if !(-1.0..=1.0).contains(v) {
                return None;
            }
            v.acos()
        }
        ("atan", [v]) => v.atan(),
        ("floor", [v]) => v.floor(),
        ("ceil", [v]) => v.ceil(),
        ("round", [v]) => v.round(),
        ("trunc", [v]) => v.trunc(),
        ("deg", [v]) => v * 180.0 / PI,
        ("rad", [v]) => v * PI / 180.0,
        ("fact", [v]) => factorial(*v)?,
        ("bitnot", [v]) => (!to_i64(*v)?) as f64,
        ("pow", [a, b]) => a.powf(*b),
        ("hypot", [a, b]) => a.hypot(*b),
        ("mod", [a, b]) => {
            if *b == 0.0 {
                return None;
            }
            *a % *b
        }
        ("atan2", [a, b]) => a.atan2(*b),
        // C's MIN/MAX macros return the second operand on ties; do the same
        // (f64::min/max differ in their treatment of -0.0).
        ("min", [a, b]) => {
            if a < b {
                *a
            } else {
                *b
            }
        }
        ("max", [a, b]) => {
            if a > b {
                *a
            } else {
                *b
            }
        }
        ("gcd", [a, b]) => gcd_u64(to_u64(*a)?, to_u64(*b)?) as f64,
        ("lcm", [a, b]) => {
            let x = to_u64(*a)?;
            let y = to_u64(*b)?;
            if x == 0 || y == 0 {
                0.0
            } else {
                let g = gcd_u64(x, y);
                if (x / g) as f64 * y as f64 > MAX_EXACT_INT {
                    return None;
                }
                ((x / g) * y) as f64
            }
        }
        ("bitor", [a, b]) => (to_i64(*a)? | to_i64(*b)?) as f64,
        ("bitand", [a, b]) => (to_i64(*a)? & to_i64(*b)?) as f64,
        ("bitxor", [a, b]) => (to_i64(*a)? ^ to_i64(*b)?) as f64,
        ("shl", [a, b]) => {
            let x = to_i64(*a)?;
            let n = to_i64(*b)?;
            if !(0..=62).contains(&n) {
                return None;
            }
            ((x as u64) << (n as u32)) as f64
        }
        ("shr", [a, b]) => {
            let x = to_i64(*a)?;
            let n = to_i64(*b)?;
            if !(0..=62).contains(&n) {
                return None;
            }
            ((x as u64) >> (n as u32)) as f64
        }
        _ => return None,
    };
    value.is_finite().then_some(value)
}

fn factorial(value: f64) -> Option<f64> {
    if !value.is_finite() || !(0.0..=170.0).contains(&value) || value.fract() != 0.0 {
        return None;
    }
    let n = value as u32;
    let mut result = 1.0f64;
    for i in 2..=n {
        result *= i as f64;
    }
    result.is_finite().then_some(result)
}

fn to_u64(value: f64) -> Option<u64> {
    if !value.is_finite() || value < 0.0 || value > MAX_EXACT_INT || value.fract() != 0.0 {
        return None;
    }
    Some(value as u64)
}

fn to_i64(value: f64) -> Option<i64> {
    if !value.is_finite() || value < -MAX_EXACT_INT || value > MAX_EXACT_INT || value.fract() != 0.0
    {
        return None;
    }
    Some(value as i64)
}

fn gcd_u64(mut x: u64, mut y: u64) -> u64 {
    while y != 0 {
        let t = x % y;
        x = y;
        y = t;
    }
    x
}

fn hex_digit(b: u8) -> Option<u32> {
    match b {
        b'0'..=b'9' => Some((b - b'0') as u32),
        b'a'..=b'f' => Some((b - b'a' + 10) as u32),
        b'A'..=b'F' => Some((b - b'A' + 10) as u32),
        _ => None,
    }
}

fn parse_hex_float(token: &str) -> Option<f64> {
    let body = token
        .strip_prefix("0x")
        .or_else(|| token.strip_prefix("0X"))?;
    let (mantissa, exponent) = match body.find(['p', 'P']) {
        Some(i) => (&body[..i], body[i + 1..].parse::<i32>().ok()?),
        None => (body, 0),
    };
    let (int_part, frac_part) = match mantissa.split_once('.') {
        Some((i, f)) => (i, f),
        None => (mantissa, ""),
    };
    if int_part.is_empty() && frac_part.is_empty() {
        return None;
    }
    let mut m = 0.0f64;
    for b in int_part.bytes() {
        m = m * 16.0 + hex_digit(b)? as f64;
    }
    let mut scale = 1.0 / 16.0;
    for b in frac_part.bytes() {
        m += hex_digit(b)? as f64 * scale;
        scale /= 16.0;
    }
    // Clamping is harmless: beyond this range f64 goes to inf/zero anyway.
    let factor = 2.0f64.powi(exponent.clamp(-2000, 2000));
    let value = m * factor;
    if !value.is_finite()
        || (value == 0.0 && m != 0.0)
        || (value != 0.0 && value.abs() < f64::MIN_POSITIVE)
    {
        return None;
    }
    Some(value)
}

/// Formats like C's `%.15g`: 15 significant digits, exponential notation when
/// the decimal exponent is < -4 or >= 15, trailing zeros removed.
fn format_g15(value: f64) -> String {
    if value.is_nan() {
        return "nan".to_owned();
    }
    if value.is_infinite() {
        return if value.is_sign_negative() {
            "-inf".to_owned()
        } else {
            "inf".to_owned()
        };
    }
    if value == 0.0 {
        return if value.is_sign_negative() {
            "-0".to_owned()
        } else {
            "0".to_owned()
        };
    }

    let negative = value.is_sign_negative();
    let scientific = format!("{:.14e}", value.abs());
    let (mantissa, exponent_text) = scientific.split_once('e').unwrap_or((&scientific, "0"));
    let exponent: i32 = exponent_text.parse().unwrap_or(0);
    let digits: String = mantissa.chars().filter(char::is_ascii_digit).collect();
    if digits.is_empty() {
        return if negative {
            "-0".to_owned()
        } else {
            "0".to_owned()
        };
    }

    let mut out = if exponent < -4 || exponent >= 15 {
        let first = &digits[..1];
        let rest = digits[1..].trim_end_matches('0');
        let mut s = String::from(first);
        if !rest.is_empty() {
            s.push('.');
            s.push_str(rest);
        }
        s.push('e');
        s.push(if exponent >= 0 { '+' } else { '-' });
        let magnitude = exponent.unsigned_abs();
        if magnitude < 10 {
            s.push('0');
        }
        s.push_str(&magnitude.to_string());
        s
    } else {
        let point = exponent + 1;
        let mut s = String::new();
        if point <= 0 {
            s.push_str("0.");
            for _ in 0..-point {
                s.push('0');
            }
            s.push_str(&digits);
        } else if point as usize >= digits.len() {
            s.push_str(&digits);
            for _ in digits.len()..point as usize {
                s.push('0');
            }
        } else {
            let p = point as usize;
            s.push_str(&digits[..p]);
            s.push('.');
            s.push_str(&digits[p..]);
        }
        if s.contains('.') {
            while s.ends_with('0') {
                s.pop();
            }
            if s.ends_with('.') {
                s.pop();
            }
        }
        s
    };

    if negative {
        out.insert(0, '-');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ev(expression: &str) -> Option<String> {
        evaluate(expression)
    }

    fn is(expression: &str, expected: &str) {
        assert_eq!(
            ev(expression).as_deref(),
            Some(expected),
            "expression: {expression}"
        );
    }

    fn none(expression: &str) {
        assert_eq!(ev(expression), None, "expression: {expression}");
    }

    fn close(expression: &str, expected: f64) {
        let text = ev(expression).unwrap_or_else(|| panic!("no result for {expression}"));
        let got: f64 = text
            .parse()
            .unwrap_or_else(|_| panic!("bad number: {text}"));
        let tolerance = 1e-12 * expected.abs().max(1.0);
        assert!(
            (got - expected).abs() <= tolerance,
            "{expression}: {got} != {expected}"
        );
    }

    #[test]
    fn basic_arithmetic() {
        is("2+3*4", "14");
        is("10/4", "2.5");
        is("7%3", "1");
        is("8-3-2", "3");
    }

    #[test]
    fn precedence_and_associativity() {
        is("2+3*4^2", "50");
        is("2^3^2", "512");
        is("(2+3)*4", "20");
        is("16/4/2", "2");
    }

    #[test]
    fn unary_operators() {
        is("-2^2", "-4");
        is("2^-3", "0.125");
        is("--3", "3");
        is("-(-3)", "3");
        is("+4", "4");
    }

    #[test]
    fn factorial() {
        is("5!", "120");
        is("0!", "1");
        is("3!+1", "7");
        is("2!!", "2");
        none("171!");
        none("3.5!");
        none("(-1)!");
    }

    #[test]
    fn functions() {
        is("sqrt(16)", "4");
        is("pow(2,10)", "1024");
        is("sqrt(16)+1", "5");
        is("abs(-5)", "5");
        is("hypot(3,4)", "5");
        is("mod(7,3)", "1");
        is("max(3,7)", "7");
        is("min(-0,0)", "0");
        close("cbrt(27)", 3.0);
        close("ln(e)", 1.0);
        close("sin(pi/2)", 1.0);
    }

    #[test]
    fn constants() {
        is("pi", "3.14159265358979");
        is("e", "2.71828182845905");
        is("tau", "6.28318530717959");
        is("epsilon", "2.22044604925031e-16");
        is("int_max+1", "2147483648");
        is("kb*2", "2048");
        is("true+false", "1");
        is("PI", "3.14159265358979");
    }

    #[test]
    fn bitwise_functions() {
        is("bitor(5,3)", "7");
        is("bitand(5,3)", "1");
        is("bitxor(5,3)", "6");
        is("bitnot(0)", "-1");
        is("shl(1,10)", "1024");
        is("shr(8,2)", "2");
        is("gcd(12,18)", "6");
        is("lcm(4,6)", "12");
        is("gcd(0,0)", "0");
        is("lcm(0,5)", "0");
    }

    #[test]
    fn integer_limits_and_bit_safety() {
        assert!(ev("bitnot(9007199254740992)").is_some());
        none("gcd(9007199254740992+2,6)");
        none("shl(1,63)");
        none("shl(1,-1)");
        none("lcm(9007199254740992,3)");
    }

    #[test]
    fn domain_errors_and_non_finite_results() {
        none("1/0");
        none("1%0");
        none("mod(1,0)");
        none("sqrt(-1)");
        none("ln(0)");
        none("1e400");
        none("1e-400+1");
        none("5e-324+0"); // ERANGE: subnormal literal
        none("1e-320+0"); // ERANGE: subnormal literal
        none("1/0+1");
    }

    #[test]
    fn invalid_expressions() {
        none("firefox");
        none("");
        none("2+");
        none("(1+2");
        none("1+2)");
        none("sqrt");
        none("pow(1,2,3)");
        none("foo(1)");
        none("1 2");
        none("1=2");
        none("1..2");
    }

    #[test]
    fn formatting() {
        is("1/3", "0.333333333333333");
        is("100000/3", "33333.3333333333");
        is("2+2", "4");
        is("1.5*2", "3");
        is("1e20+0", "1e+20");
        is("1e-5+0", "1e-05");
        is("1e15+0", "1e+15");
        is("0.0001+0", "0.0001");
        is("-0", "-0");
        is("0-0", "0");
    }

    #[test]
    fn trailing_marker_and_help() {
        is("1+2=", "3");
        is(" 1 + 2 = ", "3");
        is("pi=", "3.14159265358979");
        none("math");
        none("MATH");
    }

    #[test]
    fn numeric_expression_guard() {
        assert!(is_math_expression("2+2"));
        assert!(is_math_expression("2+2="));
        assert!(is_math_expression(" ( 1 + 2 ) "));
        assert!(is_math_expression(".5*2"));
        assert!(!is_math_expression("firefox"));
        assert!(!is_math_expression("pi"));
        assert!(!is_math_expression("1e3+2"));
    }

    #[test]
    fn numeric_tokenization() {
        is("1e3+1", "1001");
        is(".5*4", "2");
        is("0x10+1", "17");
        is("0x1.8p3+1", "13");
    }
}
