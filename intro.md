## Types

- `Int`
- `Float`
- `Bool`
- `Blob`
- `String`
- `Regex`
- `Array`
- `Dict`
- `Object`
- `Ptr`
- `nil`

## Operators

#### Infix

- `=`
- `==`
- `?=`
- `!=`
- `%`
- `+`
- `-`
- `*`
- `/`
- `??`
- `&&`
- `||`
- `+=`
- `-=`
- `/=`
- `*=`
- `>`
- `<`
- `<=`
- `>=`
- `<=>`
- (and any user-defined operators (the prelude defines some common ones))

#### Prefix
- `++`
- `--`
- `!`
- `?`

#### Postfix
- `++`
- `--`
- `[]`
- `.`

## Declarations (runtime exception if we fail to match)

```js
let x = 10;

/* s becomes "x = 10" */
let s = "x = {x}";

/* Always succeeds, but if f() returns only a single value, b will be nil */
let a, b = f();

let c, d = 4, 5;

/* Fails if RHS is not an array, or if RHS has 0 elements */
let [x, *xs] = [1, 2, 3]

/* Fails if None (or anything else that isn't Some(something)) */
let Some(x) = safeSqrt(-4) 

/* Fails if RHS yields nil */
let $x = xs.search(k);

/*
 * First apply int() to the RHS, and then match against $n (non-nil pattern).
 * This succeeds only if readLine() yields a string that can be parsed as an int.
 */
let (int ~> $n) = readLine();
```

## Pattern Matching

In addition to simple assignment which results in a runtime exception
upon failure to match, we can use several other constructs to pattern
match.

```js
let s = match (k % 3, k % 5) {
    (0, 0) => "FizzBuzz",
    (0, _) => "Fizz",
    (_, 0) => "Buzz",
    _      => str(k)
};



match xs.map(safeSqrt) {
    [Some(a), _, Some(b), *_] => {
        return a * b;
    },
    _ => {
        print("Oh no!");
        exit(1);
    }
}



if let Ok(f) = io::Stream.open("/dev/urandom") {
    doSomething(f);
} else {
    die("Couldn't read /dev/urandom");
}



if !let $d = os::opendir(".") {
    return nil;
}

/* use d here */



while let $line = io::stdin.nextLine() {
    print(f(line));
}



/*
 * Iterate over tokenized lines in stdin, skipping any which do not
 * have 3 fields or whose 3rd field, when converted to int, is not
 * greater than 3.
 */
for [a, b, int ~> $c] in io::stdin.map(line -> line.words()) | c > 3 {
    g(a, b  c);
}



/* Dictionary comprehension (similar to python) */
let d = { line: line.len() for line in io::stdin.take(5) };

/*
 * List comprehension
 *
 * yields [1, 2, 3, 1, 2, 3, 1, 2, 3]
 */
let numbers = [1, 2, 3 for _ in ..3];
```


## Functions

```js
/* Define a named function */

function factorial(k) {
    return match k {
        0 => 1,
        _ => k * factorial(k - 1)
    };
}



/* Function as an expression */
let usage = function () {
    print("usage: foo BAR BAZ");
    exit(1);
};


/* Anonymous arrow function */
[1, 2, 3].map(x -> x + 1)
io::stdin.map(line -> line.reverse())
let unwrap = Some(x) -> x;
let first = [x, *_] -> x;
let returnFive = () -> 5;

/* Or with implicit parameters */
[1, 2, 3].map(-> $ + 1)
io::stdin.map(-> $.reverse())
let returnFive = -> 5;
[4, 5, 6].fold(-> $1 * $2)

/* Or between | | with # as the implicit parameter */
[1, 2, 3].map(|# + 1|).filter(|# > 2|)

/* Sugar for using binary infix operators as functions */
let product = numbers.fold([*]);
let intersection = sets.fold([&]);
```


## Classes

Classes are templates for values of type Object. To construct an Object
of class A, we use the same syntax as a function call, i.e., A(a, b, c).
A new Object is created, and then the 'init' method of A is called, and
is passed the Object as well as any arguments supplied in the construction
expression. The Object is associated with the class A, and whenever a method
is called on it, we look for the method in A, and then its parent class, its
parent's parent, etc. All classes are subclasses of Object, and Object has no
parent.

```js
class A {
    init(self, a, b, c) {
        self.a, self.b, self.c = a, b, c;
    }

    f(self) {
        return self.a, self.b + self.c;
    }

    g(self) {
        let x, y = self.f();
        print(x * y);
    }
}

/* This will print 27 */
let a = A(3, 4, 5);
a.g();


```

Parent class is optinally specified by writing a colon followed by
the parent's name:

```

class B : A {
    f(self) {
        return 2, 10;
    }
}

/* This prints 20 */
let b = B(5, 6);
b.g();
```
