import math

class Point:
    __slots__ = ('x', 'y', 'z')
    def __init__(self, i):
        fi = float(i)
        self.x = math.sin(fi)
        self.y = math.cos(fi) * 3.0
        s = math.sin(fi)
        self.z = s * s / 2.0

    def normalize(self):
        norm = math.sqrt(self.x * self.x + self.y * self.y + self.z * self.z)
        self.x /= norm
        self.y /= norm
        self.z /= norm

    def maximize(self, other):
        self.x = max(self.x, other.x)
        self.y = max(self.y, other.y)
        self.z = max(self.z, other.z)

def float_ops(n):
    for _ in range(n):
        count = 50000
        points = [Point(i) for i in range(count)]
        for p in points:
            p.normalize()
        result = points[0]
        for i in range(1, count):
            result.maximize(points[i])
