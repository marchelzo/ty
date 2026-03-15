import math

EPSILON = 0.00001

class Vec:
    __slots__ = ('x', 'y', 'z')
    def __init__(self, x=0.0, y=0.0, z=0.0):
        self.x = x; self.y = y; self.z = z

    @property
    def mag(self):
        return math.sqrt(self.x*self.x + self.y*self.y + self.z*self.z)

    def dot(self, o):
        return self.x*o.x + self.y*o.y + self.z*o.z

    def cross(self, o):
        return Vec(self.y*o.z - self.z*o.y, self.z*o.x - self.x*o.z, self.x*o.y - self.y*o.x)

    def normalized(self):
        m = self.mag
        return Vec(self.x/m, self.y/m, self.z/m)

    def negated(self):
        return Vec(-self.x, -self.y, -self.z)

    def scale(self, s):
        return Vec(self.x*s, self.y*s, self.z*s)

    def reflect_through(self, normal):
        d = normal.scale(self.dot(normal))
        return vec_add(self, d.scale(-2.0))

def vec_add(a, b):
    return Vec(a.x + b.x, a.y + b.y, a.z + b.z)

def vec_sub(a, b):
    return Vec(a.x - b.x, a.y - b.y, a.z - b.z)

class Ray:
    __slots__ = ('origin', 'dir')
    def __init__(self, origin, direction):
        self.origin = origin
        self.dir = direction.normalized()

    def point_at(self, t):
        return vec_add(self.origin, self.dir.scale(t))

class Sphere:
    __slots__ = ('center', 'radius')
    def __init__(self, center, radius):
        self.center = center; self.radius = radius

    def intersect(self, ray):
        cp = vec_sub(self.center, ray.origin)
        v = cp.dot(ray.dir)
        disc = self.radius * self.radius - (cp.dot(cp) - v * v)
        if disc < 0.0:
            return None
        return v - math.sqrt(disc)

    def normal_at(self, p):
        return vec_sub(p, self.center).normalized()

class Plane:
    __slots__ = ('point', 'normal')
    def __init__(self, point, normal):
        self.point = point; self.normal = normal.normalized()

    def intersect(self, ray):
        denom = ray.dir.dot(self.normal)
        if abs(denom) < EPSILON:
            return None
        t = vec_sub(self.point, ray.origin).dot(self.normal) / denom
        if t < EPSILON:
            return None
        return t

    def normal_at(self, p):
        return self.normal

def color_scale(color, s):
    return (color[0] * s, color[1] * s, color[2] * s)

def color_add(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])

class Scene:
    def __init__(self, objects, lights, camera, max_depth=3):
        self.objects = objects; self.lights = lights
        self.camera = camera; self.max_depth = max_depth

    def trace(self, ray, depth=0):
        if depth > self.max_depth:
            return (0.0, 0.0, 0.0)

        best_t = 1e30
        closest_obj = None

        for obj in self.objects:
            t = obj['shape'].intersect(ray)
            if t is not None and t > EPSILON and t < best_t:
                best_t = t
                closest_obj = obj

        if closest_obj is None:
            return (0.0, 0.0, 0.0)

        p = ray.point_at(best_t)
        n0 = closest_obj['shape'].normal_at(p)
        normal = n0.negated() if n0.dot(ray.dir) > 0.0 else n0
        color = closest_obj['color']
        result = color_scale(color, closest_obj['ambient'])

        if closest_obj['lambert'] > 0.0:
            for light in self.lights:
                to_light = vec_sub(light, p).normalized()
                shadow_ray = Ray(p, to_light)
                blocked = False
                for obj in self.objects:
                    t = obj['shape'].intersect(shadow_ray)
                    if t is not None and t > EPSILON:
                        blocked = True
                        break
                if not blocked:
                    dp = normal.dot(to_light)
                    intensity = dp if dp > 0.0 else 0.0
                    result = color_add(result, color_scale(color, closest_obj['lambert'] * intensity))

        if closest_obj['spec'] > 0.0 and depth < self.max_depth:
            reflected = ray.dir.reflect_through(normal)
            ref_ray = Ray(p, reflected)
            ref_color = self.trace(ref_ray, depth + 1)
            result = color_add(result, color_scale(ref_color, closest_obj['spec']))

        return result

    def render(self, w, h):
        aspect = float(w) / float(h)
        pixel_count = 0
        for y in range(h):
            yy = -(2.0 * (float(y) / float(h)) - 1.0)
            for x in range(w):
                xx = (2.0 * (float(x) / float(w)) - 1.0) * aspect
                direction = Vec(xx, yy, -1.0)
                ray = Ray(self.camera, direction)
                self.trace(ray)
                pixel_count += 1
        return pixel_count

def make_scene():
    objects = [
        {'shape': Sphere(Vec(1.0, 3.0, -10.0), 2.0), 'color': (1.0, 1.0, 0.0), 'spec': 0.2, 'lambert': 0.7, 'ambient': 0.1},
        {'shape': Sphere(Vec(-3.0, 2.3, -5.0), 0.4), 'color': (1.0, 0.2, 0.2), 'spec': 0.1, 'lambert': 0.8, 'ambient': 0.1},
        {'shape': Sphere(Vec(-2.0, 2.3, -5.0), 0.4), 'color': (0.2, 1.0, 0.2), 'spec': 0.1, 'lambert': 0.8, 'ambient': 0.1},
        {'shape': Sphere(Vec(-1.0, 2.3, -5.0), 0.4), 'color': (0.2, 0.2, 1.0), 'spec': 0.1, 'lambert': 0.8, 'ambient': 0.1},
        {'shape': Sphere(Vec(0.0, 2.3, -5.0), 0.4), 'color': (1.0, 0.5, 0.0), 'spec': 0.1, 'lambert': 0.8, 'ambient': 0.1},
        {'shape': Sphere(Vec(1.0, 2.3, -5.0), 0.4), 'color': (0.5, 0.0, 1.0), 'spec': 0.1, 'lambert': 0.8, 'ambient': 0.1},
        {'shape': Plane(Vec(0.0, 0.0, 0.0), Vec(0.0, 1.0, 0.0)), 'color': (0.5, 0.5, 0.5), 'spec': 0.1, 'lambert': 0.6, 'ambient': 0.3},
    ]
    lights = [Vec(30.0, 30.0, 10.0), Vec(-10.0, 100.0, 30.0)]
    return Scene(objects, lights, Vec(0.0, 1.8, 10.0))

def raytrace(n):
    scene = make_scene()
    for _ in range(n):
        pixels = scene.render(80, 80)
        assert pixels == 6400
