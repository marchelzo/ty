def ack(m, n):
    if m == 0:
        return n + 1
    if n == 0:
        return ack(m - 1, 1)
    return ack(m - 1, ack(m, n - 1))

def fib_rec(n):
    if n < 2:
        return n
    return fib_rec(n - 1) + fib_rec(n - 2)

def fib_iter(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return b

def hanoi(n, src, dst, aux, moves):
    if n == 0:
        return
    hanoi(n - 1, src, aux, dst, moves)
    moves[0] += 1
    hanoi(n - 1, aux, dst, src, moves)

def sieve(limit):
    is_prime = [True] * limit
    is_prime[0] = False
    is_prime[1] = False
    i = 2
    while i * i < limit:
        if is_prime[i]:
            j = i * i
            while j < limit:
                is_prime[j] = False
                j += i
        i += 1
    return sum(is_prime)

def recursion(n):
    for _ in range(n):
        assert ack(3, 4) == 125
        assert fib_rec(25) == 75025
        fib_iter(70)
        moves = [0]
        hanoi(18, 0, 2, 1, moves)
        assert moves[0] == 262143
        assert sieve(50000) == 5133
