# Quad Contract: Partial 3-Tree Leaf-Only Checker

[quad_contract_partial_3tree_leaf_only.cpp](quad_contract_partial_3tree_leaf_only.cpp)
is a standalone C++17 program for testing embedded quadrangulations. It
searches for a sequence of
face-maintaining edge contractions and accepts when a graph at a search leaf
has treewidth at most 3.

The program can also produce SVG drawings of the input graph, the successful
contracted graph, and an embedding-preserving plane 3-tree completion.

## Recognition procedure

For each nonblank input line, the program:

1. Parses a graph together with the clockwise order of the neighbors at every
   vertex.
2. Checks that the adjacency lists are symmetric, contain no duplicates, and
   contain no loops or invalid vertices.
3. Traverses the rotation system and rejects the graph unless every face,
   including the outer face, has exactly four boundary vertices.
4. Sets the contraction limit to `floor(|F| / 2)`, where `|F|` is the number
   of faces.
5. Searches depth first over valid edge contractions. An edge is eligible when
   its endpoints have no common neighbor; this avoids parallel edges and the
   collapse of a triangular face. The contraction preserves the clockwise
   neighbor order.
6. Runs the partial 3-tree test only at a search leaf: either the contraction
   limit has been reached, or no valid contraction remains.
7. Returns `TRUE` if at least one leaf has treewidth at most 3. Otherwise, it
   returns `FALSE`.

The contraction search memoizes failed states using the graph state and the
remaining contraction budget. It also skips duplicate child states within a
single search node.

## Treewidth-at-most-3 test

The leaf checker performs an exact elimination-order search:

1. Choose a remaining vertex with at most three remaining neighbors.
2. Add fill edges that make those neighbors a clique.
3. Remove the chosen vertex and continue recursively.
4. Accept if some elimination order removes the entire graph.

Failed elimination states are memoized. Graphs with at most 63 active vertices
use a compact 64-bit representation; larger graphs use the equivalent
set-based implementation.

## Requirements

- A C++17 compiler such as Clang or GCC
- No external library is required for the normal checker or SVG output

## Build

From the repository directory:

```bash
mkdir -p bin
c++ -std=c++17 -O3 -Wall -Wextra -pedantic \
    quad_contract_partial_3tree_leaf_only.cpp \
    -o bin/quad_contract_partial_3tree_leaf_only
```

## Input format (ASCII CODE from PLANTRI PROGRAM)

Each nonblank line describes one embedded graph:

```text
N list(a),list(b),...,list(Nth vertex)
```

Vertices are named consecutively starting at `a`. Each comma-separated list
contains that vertex's neighbors in clockwise order. Every undirected edge
must occur in both endpoint lists.

For example, a four-cycle can be written as:

```text
4 bd,ac,bd,ac
```

This means:

- `a` has clockwise neighbors `b,d`;
- `b` has clockwise neighbors `a,c`;
- `c` has clockwise neighbors `b,d`;
- `d` has clockwise neighbors `a,c`.

Multiple graphs can be placed in one file, one graph per nonblank line.

The program treats the neighbor ordering as the supplied planar rotation
system. It checks the internal consistency of that representation, but it does
not run a separate planarity algorithm on the input.

## Run

Run without drawings:

```bash
./bin/quad_contract_partial_3tree_leaf_only --no-draw < inputs/quad14.txt
```

Run and produce SVG drawings:

```bash
./bin/quad_contract_partial_3tree_leaf_only --draw < inputs/quad14.txt
```

Measure elapsed time on macOS while preventing idle sleep:

```bash
time caffeinate -i ./bin/quad_contract_partial_3tree_leaf_only \
    --no-draw < inputs/quad14.txt
```

Closing a MacBook lid normally causes system sleep despite `caffeinate -i`.

## Output

For each graph, the program reports:

- the number of vertices and faces;
- the maximum contraction depth;
- `TRUE` or `FALSE`;
- a successful contraction sequence, when one is found;
- the contracted graph with compact and original labels; and
- drawing paths or drawing failures when `--draw` is enabled.

After all input lines have been processed, `Overall result: TRUE` means every
graph was accepted. The process exits with status `0` in that case and status
`1` if any graph was rejected or invalid. Command-line usage errors return
status `2`.

## Drawings

With `--draw`, files are written relative to the current working directory:

```text
partial3tree_drawings/
  graph_001/
    initial.svg
    contracted.svg
    completion.svg
  graph_002/
    ...
```

- `initial.svg` shows the input graph. Successful contraction edges are blue.
- `contracted.svg` shows the graph at the accepted search leaf.
- `completion.svg` shows an embedding-preserving plane 3-tree completion.
  Inserted completion edges are orange.

When `--draw` starts, the program removes and recreates the entire
`partial3tree_drawings` directory. Copy drawings elsewhere before another
drawing run if they need to be retained.

Every produced straight-line drawing is checked for edge crossings, vertex-on-
edge overlap, and consistency with the supplied rotation system. If no verified
layout is found, the program reports the failure and may write a placeholder
SVG for the completion.

Use `--no-draw` for timing the recognition algorithm because layout generation
and SVG verification add unrelated work.
