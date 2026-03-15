import math

PI = 3.14159265358979323
SOLAR_MASS = 4.0 * PI * PI
DAYS_PER_YEAR = 365.24

class Body:
    __slots__ = ('x', 'y', 'z', 'vx', 'vy', 'vz', 'mass')
    def __init__(self, x, y, z, vx, vy, vz, mass):
        self.x = x; self.y = y; self.z = z
        self.vx = vx; self.vy = vy; self.vz = vz
        self.mass = mass

def make_bodies():
    return [
        Body(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, SOLAR_MASS),
        Body(4.84143144246472090e+00, -1.16032004402742839e+00, -1.03622044471123109e-01,
             1.66007664274403694e-03 * DAYS_PER_YEAR, 7.69901118419740425e-03 * DAYS_PER_YEAR,
             -6.90460016972063023e-05 * DAYS_PER_YEAR, 9.54791938424326609e-04 * SOLAR_MASS),
        Body(8.34336671824457987e+00, 4.12479856412430479e+00, -4.03523417114321381e-01,
             -2.76742510726862411e-03 * DAYS_PER_YEAR, 4.99852801234917238e-03 * DAYS_PER_YEAR,
             2.30417297573763929e-05 * DAYS_PER_YEAR, 2.85885980666130812e-04 * SOLAR_MASS),
        Body(1.28943695621391310e+01, -1.51111514016986312e+01, -2.23307578892655734e-01,
             2.96460137564761618e-03 * DAYS_PER_YEAR, 2.37847173959480950e-03 * DAYS_PER_YEAR,
             -2.96589568540237556e-05 * DAYS_PER_YEAR, 4.36624404335156298e-05 * SOLAR_MASS),
        Body(1.53796971148509165e+01, -2.59193146099879641e+01, 1.79258772950371181e-01,
             2.68067772490389322e-03 * DAYS_PER_YEAR, 1.62824170038242295e-03 * DAYS_PER_YEAR,
             -9.51592254519715870e-05 * DAYS_PER_YEAR, 5.15138902046611451e-05 * SOLAR_MASS),
    ]

def offset_momentum(bodies):
    px = py = pz = 0.0
    for b in bodies:
        px += b.vx * b.mass
        py += b.vy * b.mass
        pz += b.vz * b.mass
    bodies[0].vx = -px / SOLAR_MASS
    bodies[0].vy = -py / SOLAR_MASS
    bodies[0].vz = -pz / SOLAR_MASS

def energy(bodies):
    e = 0.0
    nn = len(bodies)
    for i in range(nn):
        b = bodies[i]
        e += 0.5 * b.mass * (b.vx * b.vx + b.vy * b.vy + b.vz * b.vz)
        for j in range(i + 1, nn):
            b2 = bodies[j]
            dx = b.x - b2.x
            dy = b.y - b2.y
            dz = b.z - b2.z
            e -= b.mass * b2.mass / math.sqrt(dx*dx + dy*dy + dz*dz)
    return e

def advance(bodies, dt, steps):
    nbodies = len(bodies)
    for _ in range(steps):
        for i in range(nbodies):
            bi = bodies[i]
            for j in range(i + 1, nbodies):
                bj = bodies[j]
                dx = bi.x - bj.x
                dy = bi.y - bj.y
                dz = bi.z - bj.z
                d2 = dx*dx + dy*dy + dz*dz
                mag = dt / (d2 * math.sqrt(d2))
                bim = bi.mass * mag
                bjm = bj.mass * mag
                bi.vx -= dx * bjm
                bi.vy -= dy * bjm
                bi.vz -= dz * bjm
                bj.vx += dx * bim
                bj.vy += dy * bim
                bj.vz += dz * bim
        for b in bodies:
            b.x += dt * b.vx
            b.y += dt * b.vy
            b.z += dt * b.vz

def nbody(n):
    for _ in range(n):
        bodies = make_bodies()
        offset_momentum(bodies)
        advance(bodies, 0.01, 20000)
        energy(bodies)
