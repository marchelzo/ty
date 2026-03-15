import math

def eval_A(i, j):
    return 1.0 / ((i + j) * (i + j + 1) // 2 + i + 1)

def eval_A_times_u(n, u, au):
    for i in range(n):
        au[i] = 0.0
        for j in range(n):
            au[i] += eval_A(i, j) * u[j]

def eval_At_times_u(n, u, au):
    for i in range(n):
        au[i] = 0.0
        for j in range(n):
            au[i] += eval_A(j, i) * u[j]

def eval_AtA_times_u(n, u, atau):
    v = [0.0] * n
    eval_A_times_u(n, u, v)
    eval_At_times_u(n, v, atau)

def spectral(n):
    u = [1.0] * n
    v = [0.0] * n
    for _ in range(10):
        eval_AtA_times_u(n, u, v)
        eval_AtA_times_u(n, v, u)
    vBv = 0.0
    vv = 0.0
    for i in range(n):
        vBv += u[i] * v[i]
        vv += v[i] * v[i]
    return math.sqrt(vBv / vv)

def spectral_norm(n):
    for _ in range(n):
        result = spectral(100)
        assert abs(result - 1.274219991) < 0.0001
