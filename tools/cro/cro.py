"""Exact finite integral CRO receipts. The verifier uses only the standard library."""
import argparse
import hashlib
import json
from math import gcd, lcm
from pathlib import Path

COMPLEX = "tau-cro-complex/1"
RECEIPT = "tau-cro-receipt/1"


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def column(a, i):
    return [row[i] for row in a]


def multiply(a, b):
    return [dot(row, b) for row in a]


def vector(values, size):
    return isinstance(values, list) and len(values) == size and all(type(x) is int for x in values)


def matrix(values, columns, rows=None):
    return (isinstance(values, list) and (rows is None or len(values) == rows)
            and all(vector(row, columns) for row in values))


def instance(data):
    if not isinstance(data, dict) or set(data) != {"kind", "n0", "d0", "d1", "residue"}:
        raise ValueError("invalid complex fields")
    n0, d0, d1, residue = (data[k] for k in ("n0", "d0", "d1", "residue"))
    if data["kind"] != COMPLEX or type(n0) is not int or n0 < 0 or not matrix(d0, n0):
        raise ValueError("invalid C0 or d0")
    n1 = len(d0)
    if not matrix(d1, n1) or not vector(residue, n1):
        raise ValueError("invalid d1 or residue")
    for i, row in enumerate(d1):
        for j in range(n0):
            value = dot(row, column(d0, j))
            if value:
                raise ValueError(f"d1*d0[{i},{j}] is {value}")
    return n0, d0, d1, residue


def input_digest(data):
    encoded = json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()


def make(data):
    n0, d0, d1, residue = instance(data)

    def receipt(result, **witness):
        return {"kind": RECEIPT, "input_sha256": input_digest(data), "result": result, **witness}

    for i, value in enumerate(multiply(d1, residue)):
        if value:
            return receipt("not_cocycle", row=i, value=value)
    if not any(residue):
        return receipt("glues", correction=[0] * n0)
    if not n0:
        i = next(i for i, value in enumerate(residue) if value)
        return receipt("rational_obstruction", functional=[int(i == j) for j in range(len(d0))])

    from sympy import Matrix
    from sympy.matrices.normalforms import smith_normal_decomp
    from sympy.polys.domains import ZZ

    diag, left, right = smith_normal_decomp(Matrix(d0), domain=ZZ)
    transformed = left * Matrix(residue)
    # Prefer an obstruction over Q when both types of obstruction occur.
    for i, value in enumerate(transformed):
        if value and (i >= n0 or not diag[i, i]):
            return receipt("rational_obstruction", functional=list(map(int, left.row(i))))
    order = 1
    witnesses = []
    divisors = []
    for i in range(min(n0, len(d0))):
        d = int(diag[i, i])
        value = int(transformed[i])
        if not d:
            continue
        divisors.append((i, d, value))
        if value % d:
            modulus = abs(d)
            order = lcm(order, modulus // gcd(modulus, value))
            witnesses.append({"modulus": modulus, "functional": list(map(int, left.row(i)))})
    solution = [0] * n0
    for i, d, value in divisors:
        solution[i] = (order * value) // d
    correction = list(map(int, right * Matrix(solution)))
    if order > 1:
        return receipt("torsion_obstruction", order=order, correction=correction, witnesses=witnesses)
    return receipt("glues", correction=correction)


def verify(data, receipt):
    n0, d0, d1, residue = instance(data)
    if not isinstance(receipt, dict):
        return False
    if receipt.get("kind") != RECEIPT or receipt.get("input_sha256") != input_digest(data):
        return False

    def fields(*extra):
        return set(receipt) == {"kind", "input_sha256", "result", *extra}

    result = receipt.get("result")
    if result == "not_cocycle":
        i, value = receipt.get("row"), receipt.get("value")
        return (fields("row", "value") and type(i) is int and 0 <= i < len(d1)
                and type(value) is int and value != 0 and dot(d1[i], residue) == value)
    if any(multiply(d1, residue)):
        return False
    if result == "glues":
        correction = receipt.get("correction")
        return fields("correction") and vector(correction, n0) and multiply(d0, correction) == residue
    if result == "rational_obstruction":
        functional = receipt.get("functional")
        return (fields("functional") and vector(functional, len(d0))
                and all(dot(functional, column(d0, j)) == 0 for j in range(n0))
                and dot(functional, residue) != 0)
    if result != "torsion_obstruction" or not fields("order", "correction", "witnesses"):
        return False
    order, correction, witnesses = (receipt[key] for key in ("order", "correction", "witnesses"))
    if (type(order) is not int or order < 2 or not vector(correction, n0)
            or not isinstance(witnesses, list) or not witnesses
            or multiply(d0, correction) != [order * value for value in residue]):
        return False
    lower = 1
    for witness in witnesses:
        if not isinstance(witness, dict) or set(witness) != {"modulus", "functional"}:
            return False
        modulus, functional = witness["modulus"], witness["functional"]
        if type(modulus) is not int or modulus < 2 or not vector(functional, len(d0)):
            return False
        if any(dot(functional, column(d0, j)) % modulus for j in range(n0)):
            return False
        lower = lcm(lower, modulus // gcd(modulus, dot(functional, residue)))
    return lower == order


def load(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key {key}")
            result[key] = value
        return result

    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("make", "verify"))
    parser.add_argument("input", type=Path)
    parser.add_argument("receipt", nargs="?", type=Path)
    args = parser.parse_args()
    try:
        data = load(args.input)
        if args.action == "make":
            receipt = make(data)
            if not verify(data, receipt):
                raise RuntimeError("generated witness failed verification")
            encoded = json.dumps(receipt, indent=2) + "\n"
            if args.receipt:
                args.receipt.write_text(encoded, encoding="utf-8")
            else:
                print(encoded, end="")
        else:
            if args.receipt is None:
                parser.error("verify requires a receipt file")
            receipt = load(args.receipt)
            if not verify(data, receipt):
                parser.exit(1, "invalid receipt\n")
            print("valid", receipt["result"])
    except (OSError, ValueError, ImportError, RuntimeError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
