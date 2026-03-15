N = 50000

def build_tree(lo, hi):
    if lo >= hi:
        return None
    mid = (lo + hi) // 2
    return (build_tree(lo, mid), mid, build_tree(mid + 1, hi))

def walk(node):
    if node is None:
        return
    left, val, right = node
    yield from walk(left)
    yield val
    yield from walk(right)

def gen_tree(n):
    tree = build_tree(0, N)
    for _ in range(n):
        count = 0
        for _ in walk(tree):
            count += 1
        assert count == N
