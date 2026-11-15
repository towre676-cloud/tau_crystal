import json
from math import gcd, lcm
from pathlib import Path
import random
import unittest

from cro import COMPLEX, make, multiply, verify
from nerve import assemble


def problem(n0, d0, residue, d1=None):
    return dict(kind=COMPLEX, n0=n0, d0=d0, d1=d1 or [], residue=residue)


class Certificates(unittest.TestCase):
    def test_fixtures(self):
        for file in sorted(Path("fixtures").glob("*.input.json")):
            data = json.loads(file.read_text())
            receipt = json.loads(file.with_name(file.name.replace(".input.", ".receipt.")).read_text())
            self.assertTrue(verify(data, receipt), file.name)
            self.assertEqual(make(data), receipt)

    def test_bad_complex(self):
        with self.assertRaisesRegex(ValueError, r"d1\*d0"):
            make(problem(1, [[2]], [1], [[1]]))

    def test_empty_shapes_and_large_ints(self):
        for data, expected in [(problem(2, [], []), "glues"),
                               (problem(0, [[], []], [0, 10**40]), "rational_obstruction"),
                               (problem(1, [[10**40]], [1]), "torsion_obstruction")]:
            receipt = make(data)
            self.assertTrue(verify(data, receipt))
            self.assertEqual(receipt["result"], expected)

    def test_tamper(self):
        data = problem(1, [[4]], [2])
        receipt = make(data)
        self.assertEqual(receipt["order"], 2)
        for candidate in [{**receipt, "order": 4, "correction": [2]},
                          {**receipt, "witnesses": [{"modulus": 2, "functional": [1]}]},
                          {**receipt, "input_sha256": "0"*64},
                          {**receipt, "correction": [True]},
                          {**receipt, "x": "extra"}]:
            self.assertFalse(verify(data, candidate))
        self.assertFalse(verify(problem(1, [[4]], [6]), receipt))

    def test_rectangular_integer_basis_changes(self):
        rng = random.Random(20251115)
        for _ in range(300):
            m, n = rng.randrange(1, 7), rng.randrange(1, 7)
            d = [rng.choice([0, -8, 1, 3, 4, 9]) for _ in range(min(m,n))]
            r = [rng.randrange(-15, 16) for _ in range(m)]
            order = lcm(*(abs(x)//gcd(x,y) for x,y in zip(d,r) if x))
            rational = any(y and (i >= len(d) or d[i] == 0) for i,y in enumerate(r))
            a = [[d[i] if i == j else 0 for j in range(n)] for i in range(m)]
            for _ in range(10):
                if m > 1:
                    i,j = rng.sample(range(m),2)
                    k = rng.randrange(-3,4)
                    a[i] = [u+k*v for u,v in zip(a[i],a[j])]
                    r[i] += k*r[j]
                if n > 1:
                    i,j = rng.sample(range(n),2)
                    k = rng.randrange(-3,4)
                    for row in a:
                        row[i] += k*row[j]
            data = problem(n,a,r)
            receipt = make(data)
            self.assertTrue(verify(data,receipt), data)
            self.assertEqual(receipt["result"], "rational_obstruction" if rational else
                             "torsion_obstruction" if order > 1 else "glues", data)
            if not rational and order > 1:
                self.assertEqual(receipt["order"], order, data)

    def test_twisted_triangle(self):
        edges = [(0,1),(0,2),(1,2)]
        transports = {e: ([[w]], [[w]]) for e,w in zip(edges,[-1,1,-1])}
        data = assemble(3,1,edges,[(0,1,2)],transports,[[3],[2],[5]])
        self.assertEqual(multiply(data["d1"], data["residue"]), [0])
        self.assertEqual(make(data)["result"], "glues")
        transports[0,2] = ([[-1]],[[-1]])
        with self.assertRaisesRegex(ValueError, r"d1\*d0"):
            assemble(3,1,edges,[(0,1,2)],transports,[[3],[2],[5]])


if __name__ == "__main__":
    unittest.main()
