# Classes

Classes are defined with the `class` keyword. They support fields, methods, operator overloading, inheritance, traits, generics, and multiple dispatch on methods.

## Basics

Fields are declared with a name and optional type annotation. Methods are just functions defined inside the class body. `self` refers to the instance.

```ty
class Point {
    x: Float
    y: Float

    distance(other: Point) -> Float {
        ((x - other.x) ** 2.0 + (y - other.y) ** 2.0).sqrt
    }
}

let a = Point(1.0, 2.0)
let b = Point(4.0, 6.0)
print(a.distance(b))
```

Constructors are implicit from the declared public fields. You can also define an explicit `init` method:

```ty
class Counter {
    __n: Int

    init(start: Int = 0) {
        __n = start
    }

    tick() { __n += 1 }
    value -> Int { __n }
}

let c = Counter(10)
c.tick()
c.tick()
print(c.value)
```

## Computed properties

A method with no parameter list is a computed property, accessed without parentheses. The return type annotation follows `->`:

```ty
class Rect {
    w: Float
    h: Float

    area -> Float { w * h }
    perimeter -> Float { 2.0 * (w + h) }
}

let r = Rect(3.0, 4.0)
print(r.area)
print(r.perimeter)
```

## Operator overloading

Classes can define operators as methods. Binary operators dispatch on the types of both operands.

```ty
class Vec2 {
    x: Float
    y: Float

    __str__() -> String { "({x}, {y})" }

    +(other: Vec2) -> Vec2 { Vec2(x + other.x, y + other.y) }
    *(k: Float) -> Vec2    { Vec2(x * k, y * k) }
    #() -> Float           { (x * x + y * y).sqrt }
}

let v = Vec2(3.0, 4.0) + Vec2(1.0, 1.0)
print(v)
print(#v)
print(v * 2.0)
```

The `#` operator is overloaded by defining `#()` and is used for length/magnitude. Index operators `[]` and `[]=` are also overloadable:

```ty
class Grid {
    __data: Array[Int]
    __w: Int

    init(w: Int, h: Int) {
        __w = w
        __data = [0 for _ in ..(w * h)]
    }

    [](x: Int, y: Int) -> Int {
        __data[y * __w + x]
    }

    []=(x: Int, y: Int, v: Int) -> Int {
        __data[y * __w + x] = v
    }
}

let g = Grid(3, 3)
g[1, 2] = 42
print(g[1, 2])
```

## Inheritance

Classes inherit from other classes with `<`. Methods can call `super`.

```ty
class Animal {
    name: String
    speak() -> String { "{name} says ..." }
}

class Dog < Animal {
    speak() -> String { "{name} says woof!" }
}

class Cat < Animal {
    speak() -> String { "{name} says meow!" }
}

for a in [Dog('Rex'), Cat('Whiskers')] {
    print(a.speak())
}
```

## Traits

Traits define shared interfaces. Classes implement them by providing the required methods. Traits can carry default implementations.

```ty
trait Greetable {
    greeting -> String;
    greet() -> String { "Hi, I'm {greeting}" }
}

class Person : Greetable {
    name: String
    greeting -> String { name }
}

class Bot : Greetable {
    id: Int
    greeting -> String { "Bot #{id}" }
}

print(Person('Alice').greet())
print(Bot(7).greet())
```

## Generics

Classes and traits accept type parameters in brackets:

```ty
class Pair[A, B] {
    first: A
    second: B

    map-first[C](f: A -> C) -> Pair[C, B] {
        Pair(f(first), second)
    }

    __str__() -> String { "({first}, {second})" }
}

let p = Pair(1, 'hello')
print(p)
print(p.map-first(x -> x * 10))
```

## Multiple dispatch on methods

Like top-level functions, methods support overloading with multiple definitions. The first matching signature wins:

```ty
class Formatter {
    format(x: Int) -> String    { "int({x})" }
    format(x: Float) -> String  { "float({x})" }
    format(x: String) -> String { "str({x})" }
}

let f = Formatter()
print(f.format(42))
print(f.format(3.14))
print(f.format('hello'))
```

## Static methods

Methods and fields prefixed with `static` belong to the class itself rather than instances:

```ty
class Temperature {
    value: Float
    unit: String

    static from-celsius(c: Float) -> Temperature {
        Temperature(c, 'C')
    }

    static from-fahrenheit(f: Float) -> Temperature {
        Temperature((f - 32.0) / 1.8, 'C')
    }

    __str__() -> String { "{value:.1}°{unit}" }
}

print(Temperature.from-celsius(100.0))
print(Temperature.from-fahrenheit(212.0))
```
