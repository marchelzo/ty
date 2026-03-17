# Tags and Algebraic Types

`tag` declares lightweight `newtype`-like constructors — Ty's version of sum types / variants.

```ty
tag Circle, Rect;

fn area(shape) {
    match shape {
        Circle(r)  => 3.14159 * r * r,
        Rect(w, h) => w * h
    }
}

print(area(Circle(5.0)))
print(area(Rect(3.0, 4.0)))
```

Tags can be used without payloads:

```ty
tag Red, Green, Blue;

fn hex(c) {
    match c {
        Red   => '#ff0000',
        Green => '#00ff00',
        Blue  => '#0000ff'
    }
}

print(hex(Red))
```

## Type aliases

`use` creates type aliases. Combined with tags, this gives you typed sum types:

```ty
tag Leaf, Node;
use Tree = Leaf[Int] | Node[(Tree, Tree)]

fn sum(t: Tree) -> Int {
    match t {
        Leaf(n)    => n,
        Node(l, r) => sum(l) + sum(r)
    }
}

let tree = Node(Node(Leaf(1), Leaf(2)), Leaf(3))
print(sum(tree))
```

There are some built-in tags for common use cases. `Some` and `None` are used for optional values. `Ok` and `Err` are used for results of computations that may fail.

The alias `Maybe[T] = Some[T] | None` is provided for convenience, but you can use `Some` and `None` directly if you prefer.

```ty
fn safe-div(a: Float, b: Float) -> Maybe[Float] {
    (b == 0.0) ? None : Some(a / b)
}

print(safe-div(10.0, 2.0))
print(safe-div(10.0, 0.0))
```
