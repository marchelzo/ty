def solve(n):
    count = 0
    cols = [0] * n

    def place(row):
        nonlocal count
        if row == n:
            count += 1
            return
        for col in range(n):
            ok = True
            for r in range(row):
                if (cols[r] == col
                    or cols[r] - r == col - row
                    or cols[r] + r == col + row):
                    ok = False
                    break
            if ok:
                cols[row] = col
                place(row + 1)

    place(0)
    return count

def nqueens(n):
    for _ in range(n):
        result = solve(10)
        assert result == 724
