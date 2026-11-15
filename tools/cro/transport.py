"""Derive integral CRO inputs from exact piecewise affine ODE transport."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from cro import COMPLEX, dot, load, make, matrix, multiply, vector, verify


def product(a, b):
    columns = list(zip(*b, strict=True))
    return [[dot(row, col) for col in columns] for row in a]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def duration(text):
    if type(text) is not int and not isinstance(text, str):
        raise ValueError("duration must be an integer or a rational string")
    t = Fraction(text)
    if t <= 0:
        raise ValueError("duration must be positive")
    return t


def integer_entries(values, label):
    if any(v.denominator != 1 for v in values):
        raise ValueError(f"{label} does not preserve the standard integral lattice")
    return [int(v) for v in values]


def window(segment, n):
    if not isinstance(segment, dict) or set(segment) != {"duration", "N", "forcing"}:
        raise ValueError("invalid window fields")
    t, a, b = duration(segment["duration"]), segment["N"], segment["forcing"]
    if not matrix(a, n, n) or not vector(b, n):
        raise ValueError("invalid generator or forcing")
    if any(any(row) for row in product(a, a)):
        raise ValueError("window requires N² = 0")
    linear = []
    inverse = []
    for i, row in enumerate(a):
        linear.append(integer_entries([int(i == j) + t * v for j, v in enumerate(row)], "linear transport"))
        inverse.append(integer_entries([int(i == j) - t * v for j, v in enumerate(row)], "inverse transport"))
    translation = integer_entries([t * v + t * t * w / 2 for v, w in zip(b, multiply(a, b))],
                                  "affine translation")
    return linear, inverse, translation


def derive(data):
    if not isinstance(data, dict) or set(data) != {"kind", "dimension", "windows"}:
        raise ValueError("invalid transport fields")
    n, windows = data["dimension"], data["windows"]
    if (data["kind"] != "tau-cro-ode-cycle/1" or type(n) is not int or n < 1
            or not isinstance(windows, list) or not windows):
        raise ValueError("invalid cycle dimension or windows")
    linear, shift = identity(n), [0] * n
    steps = []
    for segment in windows:
        a, inv, b = window(segment, n)
        shift = [v + w for v, w in zip(multiply(a, shift), b)]
        linear = product(a, linear)
        steps.append({"linear": a, "inverse": inv, "translation": b})
    coboundary = [[x - int(i == j) for j, x in enumerate(row)] for i, row in enumerate(linear)]
    problem = {"kind": COMPLEX, "n0": n, "d0": coboundary, "d1": [],
               "residue": [-x for x in shift]}
    return {"steps": steps, "monodromy": linear, "translation": shift, "complex": problem}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("make", "verify"))
    parser.add_argument("cycle", type=Path)
    parser.add_argument("bundle", nargs="?", type=Path)
    args = parser.parse_args()
    try:
        from cro import input_digest

        data = load(args.cycle)
        expected = {"kind": "tau-cro-transport-receipt/1", "cycle_sha256": input_digest(data),
                    **derive(data)}
        if args.action == "make":
            receipt = make(expected["complex"])
            if not verify(expected["complex"], receipt):
                raise RuntimeError("generated witness failed verification")
            encoded = json.dumps({**expected, "receipt": receipt}, indent=2) + "\n"
            if args.bundle:
                args.bundle.write_text(encoded, encoding="utf-8")
            else:
                print(encoded, end="")
            return
        if args.bundle is None:
            parser.error("verify requires a bundle file")
        candidate = load(args.bundle)
        if not isinstance(candidate, dict):
            raise ValueError("invalid transport receipt")
        receipt = candidate.pop("receipt", None)
        if (input_digest(candidate) != input_digest(expected)
                or not verify(expected["complex"], receipt)):
            raise ValueError("invalid transport receipt")
        print("valid", receipt["result"])
    except (OSError, ValueError, ZeroDivisionError, RuntimeError, ImportError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
