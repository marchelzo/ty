import math
import random

class GVec:
    __slots__ = ('x', 'y', 'z')
    def __init__(self, x=0.0, y=0.0, z=0.0):
        self.x = x; self.y = y; self.z = z

    @property
    def mag(self):
        return math.sqrt(self.x*self.x + self.y*self.y + self.z*self.z)

    def dist(self, o):
        dx = self.x - o.x; dy = self.y - o.y; dz = self.z - o.z
        return math.sqrt(dx*dx + dy*dy + dz*dz)

def vec_add(a, b):
    return GVec(a.x + b.x, a.y + b.y, a.z + b.z)

def vec_sub(a, b):
    return GVec(a.x - b.x, a.y - b.y, a.z - b.z)

def vec_scale(a, s):
    return GVec(a.x * s, a.y * s, a.z * s)

def linear_combination(a, b, la, lb):
    return GVec(a.x*la + b.x*lb, a.y*la + b.y*lb, a.z*la + b.z*lb)

class Spline:
    def __init__(self, pts, degree=3):
        self.pts = pts
        self.degree = degree
        n = len(pts) + degree + 1
        self.knots = [0.0] * n
        for i in range(n):
            if i <= degree:
                self.knots[i] = 0.0
            elif i >= n - degree - 1:
                self.knots[i] = 1.0
            else:
                self.knots[i] = float(i - degree) / float(n - 2 * degree - 1)

    def at(self, u):
        pts = self.pts
        n = len(pts)
        k = self.degree
        knots = self.knots

        seg = k
        while seg < n - 1 and knots[seg + 1] <= u:
            seg += 1

        d = [GVec() for _ in range(k + 1)]
        for i in range(k + 1):
            p = pts[seg - k + i]
            d[i] = GVec(p.x, p.y, p.z)

        for lvl in range(1, k + 1):
            for ii in range(k, lvl - 1, -1):
                idx = ii - lvl
                left = seg - k + ii
                right = left + k - lvl + 1
                kl = knots[left]
                kr = knots[right]
                denom = kr - kl
                if abs(denom) < 1.0e-12:
                    pass
                else:
                    alpha = (u - kl) / denom
                    d[idx] = linear_combination(d[idx], d[idx + 1], 1.0 - alpha, alpha)
        return d[0]

class ChaosGame:
    def __init__(self, splines, thickness=0.25):
        self.splines = splines
        self.thickness = thickness

        minx = miny = 1.0e10
        maxx = maxy = -1.0e10
        for s in splines:
            for p in s.pts:
                minx = min(minx, p.x)
                miny = min(miny, p.y)
                maxx = max(maxx, p.x)
                maxy = max(maxy, p.y)
        self.minx = minx; self.miny = miny
        self.maxx = maxx; self.maxy = maxy

        self.num_trafos = [0] * len(splines)
        self.total = 0
        for si in range(len(splines)):
            length = 0.0
            prev = splines[si].at(0.0)
            for i in range(1, 1001):
                cur = splines[si].at(i / 1000.0)
                length += prev.dist(cur)
                prev = cur
            self.num_trafos[si] = max(1, round(length * 2.0))
            self.total += self.num_trafos[si]

    def random_trafo(self):
        r = int(random.random() * self.total)
        acc = 0
        for si in range(len(self.splines)):
            acc += self.num_trafos[si]
            if r < acc:
                return (si, r - (acc - self.num_trafos[si]))
        return (len(self.splines) - 1, self.num_trafos[-1] - 1)

    def transform(self, p, si, seg):
        tt = self.thickness
        rangex = self.maxx - self.minx
        rangey = self.maxy - self.miny
        nx = (p.x - self.minx) / rangex
        ny = (p.y - self.miny) / rangey
        nt = self.num_trafos[si]
        u0 = float(seg) / float(nt)
        u1 = float(seg + 1) / float(nt)
        u = u0 + nx * (u1 - u0)

        base = self.splines[si].at(u)

        du = 1.0 / 50000.0
        deriv = vec_sub(self.splines[si].at(min(1.0, u + du)),
                        self.splines[si].at(max(0.0, u - du)))
        dmag = deriv.mag
        if dmag < 1.0e-12:
            return base

        perp = GVec(-deriv.y / dmag, deriv.x / dmag)
        offset = (ny - 0.5) * tt
        result = GVec(base.x + perp.x * offset, base.y + perp.y * offset)

        return GVec(
            max(self.minx, min(self.maxx, result.x)),
            max(self.miny, min(self.maxy, result.y))
        )

    def run(self, iterations):
        p = GVec((self.minx + self.maxx) / 2.0, (self.miny + self.maxy) / 2.0)
        count = 0
        for _ in range(iterations):
            si, seg = self.random_trafo()
            p = self.transform(p, si, seg)
            count += 1
        return count

def make_splines():
    return [
        Spline([
            GVec(1.597, 3.304), GVec(1.575, 4.630),
            GVec(1.313, 5.009), GVec(1.618, 5.876),
            GVec(1.826, 6.671), GVec(0.233, 7.953),
            GVec(2.239, 7.318)
        ]),
        Spline([
            GVec(2.239, 7.318), GVec(2.570, 6.954),
            GVec(3.706, 6.203), GVec(3.760, 5.709),
            GVec(3.503, 5.601), GVec(3.493, 5.247),
            GVec(4.028, 4.969)
        ]),
        Spline([
            GVec(4.028, 4.969), GVec(4.279, 4.842),
            GVec(4.267, 4.318), GVec(4.385, 3.843),
            GVec(3.596, 3.619), GVec(2.842, 3.490),
            GVec(1.597, 3.304)
        ]),
    ]

def chaos_game(n):
    for _ in range(n):
        game = ChaosGame(make_splines())
        count = game.run(5000)
        assert count == 5000
