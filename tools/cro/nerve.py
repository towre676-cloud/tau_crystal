"""Build a finite integral cochain complex from oriented simplicial overlaps."""
from cro import COMPLEX, column, dot, instance, matrix, vector


def assemble(vertices, rank, edges, faces, transports, residue):
    """Edges and faces are sorted tuples; transports map the first fiber to the second.

    Each transport value is a pair (matrix, inverse), checked over the integers.
    The input residue has one list of rank entries per edge, in edge order.
    """
    if type(vertices) is not int or vertices < 0 or type(rank) is not int or rank < 1:
        raise ValueError("invalid vertex count or fiber rank")
    for size, cells in ((2, edges), (3, faces)):
        if len(set(cells)) != len(cells) or any(
            len(cell) != size or tuple(sorted(set(cell))) != cell
            or any(type(v) is not int or not 0 <= v < vertices for v in cell)
            for cell in cells
        ):
            raise ValueError("invalid or duplicate simplices")
    index = {edge: i for i, edge in enumerate(edges)}
    if set(transports) != set(index):
        raise ValueError("a transport is required for each edge")
    if len(residue) != len(edges) or any(not vector(r, rank) for r in residue):
        raise ValueError("invalid edge residue")
    d0 = []
    for i, j in edges:
        t, inv = transports[i, j]
        if not matrix(t, rank, rank) or not matrix(inv, rank, rank):
            raise ValueError("invalid transport matrix")
        if any(dot(row, column(inv, a)) != int(b == a)
               for b, row in enumerate(t) for a in range(rank)):
            raise ValueError("transport and inverse disagree")
        for a, row in enumerate(t):
            coefficients = [0] * (vertices * rank)
            coefficients[i*rank:(i+1)*rank] = [-v for v in row]
            coefficients[j*rank+a] = 1
            d0.append(coefficients)
    d1 = []
    for i, j, k in faces:
        if any(edge not in index for edge in ((i,j), (j,k), (i,k))):
            raise ValueError("face boundary is missing an edge")
        for a, row in enumerate(transports[j,k][0]):
            coefficients = [0] * (len(edges) * rank)
            start = index[i,j] * rank
            coefficients[start:start+rank] = row
            coefficients[index[j,k]*rank+a] = 1
            coefficients[index[i,k]*rank+a] = -1
            d1.append(coefficients)
    data = {"kind": COMPLEX, "n0": vertices * rank, "d0": d0, "d1": d1,
            "residue": [x for edge in residue for x in edge]}
    instance(data)
    return data
