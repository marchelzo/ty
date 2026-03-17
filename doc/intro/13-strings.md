# Strings and Regular Expressions

## String literals

### Single-quoted strings

Single-quoted strings are for plain literals without any interpolation. They support the following limited set of escape sequences:

 - `\\` for a literal backslash
 - `\'` for a literal single quote
 - `\n` for newline
 - `\t` for tab
 - `\r` for carriage return

```ty
pp('hello, {world}\n')
pp('it\'s a backslash: \\')
```

### Triple-quoted strings

Triple single quotes (`'''`) create multi-line strings. The content is automatically dedented based on the indentation of the closing `'''`:

```ty
let html =
    '''
    <html>
      <body>
        <p>Hello</p>
      </body>
    </html>
    '''
print(html)
```

The leading whitespace common to all lines (matching the closing `'''`'s indent) is stripped. This lets you indent multi-line strings naturally without affecting their content.

### Double-quoted strings (interpolated)

Double-quoted strings support `{expr}` interpolation and some extra escape sequences (`\x1b`, `\u{1F600}`, etc.):

```ty
let name = 'Ty'
let version = 1
print("Hello from {name} v{version}!")
print("{2 + 2} is {true ? 'four' : 'not four'}")
```

### Format specifiers

Interpolated expressions can include format specifiers after a colon:

```ty
import time (..)

let pi = 3.14159
print("{pi:.2}")

let n = 42
dbg("{n:08b}")
dbg("{n:#04x}")
dbg("{'hello':>20}")
dbg("{255:02x}{128:02x}{0:02x}")
dbg("{rand():.2q}")
dbg("{time():,}")
```

Interpolated expressions can include arbitrarily nested `"` strings, and interpolation
works inside the format specifier as well. All of the padding and alignment options are
SGR-aware and Unicode-aware, so they work (mostly :^)) correctly with styled text and wide characters.
They also work with custom fill characters, which can be styled themselves.

```ty
let pad = "\x1b[94m-\x1b[0m"
let msg = "\x1b[92;1m Howdy! 🤠 \x1b[0m"
print("{msg:{pad}^24}")
```

You can use `*` as a width specifier to have the width determined by the width of the literal interpolation
region in the source code. This is useful for aligning multiple interpolated strings to the same width:

```ty
let name = 'Alice'
let occupation = 'Engineer'
print("|{name:                  *}|")
print("|{occupation.upper():    *}|")
```

### Adjacent string concatenation

String literals placed next to each other are concatenated at parse time. This is useful for breaking long strings across lines:

```ty
let msg = 'hello, '
          'world'
print(msg)
```

This works with any combination of string literal types — single, double, or triple-quoted.

## Tagged string literals

Any callable value can be used as a string tag. When you write `tag"text {expr} more"`, the compiler generates the function call `tag(parts)` where `parts` is an array of plain strings and `(value, format_spec, width)` tuples for interpolated expressions.

The `chalk` module uses this to create styled terminal output:

```ty
import chalk (chalk)

let name = 'World'
let n = 42

// Chalk markup: [style]...[/] for styled regions
let greeting = chalk"[green bold]Hello[/], [#c585f5]{name}[/]! ({n:03})"
print(greeting)
```

You can define your own tagged string literals. Here's a simple HTML-escaping tag:

```ty
fn html(parts) {
    let buf = Blob()
    for match parts {
        s: String   => buf.push(s),
        (val, _, _) => {
            let s = "{val}"
            buf.push(
                s.sub('&', '&amp;')
                 .sub('<', '&lt;')
                 .sub('>', '&gt;')
            )
        }
    }
    buf.str!()
}

let user = '<script>alert("xss")</script>'
print(html"<p>Hello, {user}!</p>")
```

## Regular expressions

Regex literals use `/pattern/flags` syntax. Available flags include `i` (case-insensitive), `u` (Unicode-aware `\w`, `\d`, etc.), and `v` (return `RegexMatch` objects with positional info).

### Matching

```ty
let s = 'Order #1234 placed on 2024-03-14'

// match() returns nil on failure
if let [_, id, date] = s.match(/Order #(\d+) .* (\d{4}-\d{2}-\d{2})/) {
    print("order {id}, date {date}")
}

// match?() returns Bool
print('hello'.match?(/^[a-z]+$/))
```

### Scanning

`scan` / `matches` returns all non-overlapping matches:

```ty
let text = 'rgb(100, 200, 50)'
let nums = text.scan(/\d+/)
print(nums)
```

With capture groups, each match is an array:

```ty
let pairs = 'name=Alice age=30 city=NYC'
for [_, k, v] in pairs.scan(/(\w+)=(\w+)/) {
    print("{k} -> {v}")
}
```

### Substitution

`sub` replaces matches. The replacement can be a string or a function:

```ty
print('hello world'.sub(/\w+/, &upper))
```

```ty
let date = '2024-03-14'
print(date.sub(/(\d{4})-(\d{2})-(\d{2})/, [_, y, m, d] -> "{d}/{m}/{y}"))
```

```ty
// Using postfix `[]` to treat a `Dict` as a mapping function
print('abc'.sub(/./, %{'a': 'x', 'b': 'y', 'c': 'z'}[]))
```

### Comb

`comb` removes all matches of a pattern.

```ty
let noisy = 'h.e" l*l!o'
print(noisy.comb(/[^a-z]/))
```

### Split

`split` divides a string by a delimiter. With a regex, capture groups are included in the result:

```ty
print('a::b::c'.split('::'))
print('one1two2three'.split(/(\d)/))
```

### Regex in `match` expressions

Regex literals work as patterns in `match`. Capture groups bind to `$0`, `$1`, etc. within the arm:

```ty
fn parse-value(s: String) {
    match s {
        /^(\d+)\.(\d+)$/  => print("float: {$1}.{$2}"),
        /^\d+$/           => print("int: {$0}"),
        /^"(.*)"$/        => print("string: {$1}"),
        _                 => print("unknown: {s}")
    }
}

parse-value('42')
parse-value('3.14')
parse-value('"hello"')
parse-value('???')
```

### The `/v` flag

Patterns which were specified with the `/v` flag cause regex-matching methods to produce `RegexMatch` objects instead of plain strings / arrays, giving access to match positions:

```ty
let m = '..hello world..'.match(/(\w+)\s+(\w+)/v)
pp({
    m,
    start: m.start,
    end: m.end,
    pre: m.pre,
    post: m.post,
    captures: m.captures
})
```

## Other string methods

```ty
let s = '  Hello, World!  '

print(s.trim())
print(s.words())
print(s.lines())
print(s.upper())
print(s.lower())
print(s.reverse())
print('hello'.starts?('he'))
print('hello'.ends?('lo'))
print('hello'.chars())
print('hello'.repeat(3))
print('café'.len())
print('café'.size())
```
