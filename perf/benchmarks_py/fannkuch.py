def fannkuch(n):
    count = list(range(1, n + 1))
    perm1 = list(range(n))
    perm = [0] * n
    max_flips = 0
    m = n - 1
    r = n

    while True:
        while r != 1:
            count[r - 1] = r
            r -= 1

        if perm1[0] != 0 and perm1[m] != m:
            perm[:] = perm1[:]

            flips = 0
            while perm[0] != 0:
                k = perm[0]
                i = 0
                j = k
                while i < j:
                    perm[i], perm[j] = perm[j], perm[i]
                    i += 1
                    j -= 1
                flips += 1

            if flips > max_flips:
                max_flips = flips

        while True:
            if r == n:
                return max_flips

            p0 = perm1[0]
            for i in range(r):
                perm1[i] = perm1[i + 1]
            perm1[r] = p0

            count[r] -= 1
            if count[r] > 0:
                break
            r += 1

    return max_flips

def fannkuch_bench(n):
    for _ in range(n):
        result = fannkuch(9)
        assert result == 30
