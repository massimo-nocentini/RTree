# RTree
[![CI](https://github.com/pharo-graphics/RTree/actions/workflows/tests.yml/badge.svg)](https://github.com/pharo-graphics/RTree/actions/workflows/tests.yml)

Spatial indexes for [Pharo](https://pharo.org), used by [Roassal](https://github.com/pharo-graphics/Roassal) to find the shapes at a point (hit tests) and in a rectangle (rendering only what is visible).

The package provides `RTreeCollection`, an R-tree, and several other indexes with the same protocol, so a Roassal canvas can switch between them with a single message.

## Installation

```smalltalk
Metacello new
	baseline: 'RTree';
	repository: 'github://pharo-graphics/RTree:master/src';
	load.
```

Roassal loads RTree through its own baseline, so a Roassal image already has it.

## Concepts

An **entry** is any object that uses the trait `RTEntry`. It provides:

- `encompassingRectangle`: its bounding box, which the index stores;
- `addEntriesIn:position:`: adds itself, or its children, to a collection when it accepts a point. This is the exact hit test, the box is only a filter;
- `parent` and `resetEncompassingRectangle`;
- `entryIndex`: its drawing order. Answers are ordered by it, so the topmost entry comes first at a point, as on a canvas.

Optionally, an entry can also override:

- `firstEntryAtPoint:satisfying:ifNone:`, to search its children before itself, as a composite shape does;
- `spatialSegment`, which answers `{ start. end. halfWidth }` for a straight line. The segment-aware grid uses it.

A **collection** indexes entries. It is a `Collection` (`add:`, `remove:`, `do:`, `size`, `includes:`, `copy`…) with spatial queries on top. When an entry moves or is resized, send `updateEntry:` so that the index learns its new box.

## Usage with Roassal

```smalltalk
canvas := RSCanvas new.
canvas addAll: shapes.
canvas useRTree.	"an RTreeCollection instead of the default list"

"or any other collection of this package"
canvas shapeCollection: RTGridCollection new.
canvas shapeCollection: (RTGridCollection new segmentAware: true; yourself).	"graphs with long straight edges"
```

Roassal then uses the collection for its hit tests and to cull what lies outside the window.

## Queries

All the collections answer the same thing for the same entries; only the speed differs.

| Message | Answer |
|---|---|
| `entriesAtPoint: aPoint` | the entries that accept the point, topmost first |
| `entryAtPoint: aPoint ifNone: aBlock` | the topmost entry at the point |
| `entryAtPoint: aPoint satisfying: aBlock ifNone: noneBlock` | the topmost entry at the point that satisfies `aBlock`, for example the topmost shape with an event handler. It does not collect every hit |
| `entriesAtRectangle: aRectangle` | the entries whose box meets the rectangle, in drawing order |
| `entriesInside: aRectangle` | the entries whose box lies inside the rectangle |
| `entriesNear: aPoint within: aDistance` | the entries whose box is within the distance of the point, nearest first |
| `nearestEntryTo: aPoint` / `nearestEntryTo:ifNone:` | the entry whose box is nearest to the point |
| `bounds` | the union of the boxes of the entries, or nil when empty |
| `bulkLoad: aCollection` | adds many entries at once; an empty tree is built in one pass |

Entries with a NaN or infinite coordinate are kept apart, in `outliers`, and every query still tests them: they cannot corrupt the index.

## The collections

| Collection | Structure | Use it for |
|---|---|---|
| `RTSequenceableCollection` | a list, every query is a scan | small canvases (below about 5–10k shapes); Roassal's default |
| `RTreeCollection` | binary AVL R-tree, one leaf per entry | interactive canvases with many shapes; `canvas useRTree` |
| `RTNaryTreeCollection` | n-ary R-tree (16 children per node, R*-tree splits) | the same, with a shallower tree and less memory |
| `RTPackedTreeCollection` | Hilbert-packed flat R-tree in Arrays, as in Flatbush | canvases that change little: fast queries and the least memory |
| `RTGridCollection` | uniform grid, tuned from the entries | the fastest hit tests; with `segmentAware: true`, graphs of long straight lines |
| `RTLooseQuadtreeCollection` | loose quadtree | canvases that move a lot: the cheapest adds and moves, slower hit tests |

The trait `RTSpatialIndex` holds the queries the last four collections share; a new index only implements a few primitives (see the class comment).

## What changed since v1.02

Up to v1.02 the package had `RTreeCollection` and `RTSequenceableCollection`, with `entriesAtPoint:`, `entriesAtRectangle:`, `entryAtPoint:ifNone:`, `add:`, `remove:`, `updateEntry:`, `pushFront:` and `pushBack:`, and 35 tests. `bulkLoad:` added the entries one by one.

The following was added after an audit of RTree inside Roassal on Pharo 15.

### Bugs fixed

- A removal left the boxes of the ancestors too large, and rebalanced by reinserting a whole subtree.
- `remove:` and `updateEntry:` looked for the leaf with the entry's current box. After a box changed without `updateEntry:`, the entry could not be found again (`NotFound`), and the shape could no longer be hit.
- One entry with a NaN or infinite box spoiled the boxes of its ancestors, and its healthy neighbours could no longer be found. `add:` could leave the tree half changed after an error.
- Point queries used the half-open `Rectangle>>containsPoint:`, so `useRTree` missed points on the far border of a box that the list found, such as the end point of a line.
- `copy` shared the nodes with the original. `removeAll`, `collect:`, and the answers of `add:` and `remove:` did not follow the `Collection` protocol.
- `entriesAtRectangle:` failed on entries without an `entryIndex`, and `entriesAtPoint:` misordered entries without a parent.
- The same entry could be added twice, leaving a stale leaf after `remove:`. `RTreeCollection` now holds an entry once.

### Faster

Each figure is the median of 3 runs on 100k boxes unless the row says otherwise.

| Operation | Before | After |
|---|---|---|
| Move every entry, then one query (a layout) | 3715 ms | 747 ms (5×) |
| Relayout of a 50k-shape Roassal canvas, with its first query | 1865 ms | 615 ms (3×) |
| Drag of a shape in a 50k-shape canvas | 26.1 µs | 7.1 µs (3.7×) |
| `bulkLoad:` | added one by one | built at once in Hilbert order: 204 ms |
| `entriesAtRectangle:` of a 2000×2000 window | 4954 µs | 3314 µs (1.5×) |
| Topmost entry at a point that satisfies a block, 10k long edges | 1036 µs | 392 µs (2.6×) |
| `size` and `isEmpty` of `RTSequenceableCollection` | 1005 µs | 0.2–0.4 µs |
| Nearest entry: scanning the list vs `nearestEntryTo:` | 11448 µs | 49 µs |

How:

- Removals and rotations follow AVL deletion and reuse the nodes they keep.
- Leaves are indexed by entry, and nodes know their parent, so `remove:` and `updateEntry:` walk up from the leaf without searching.
- `updateEntry:` changes the leaf in place for a small move and defers a far move to the next query. If more than 1/8 of the entries moved, that query rebuilds the tree in one pass.
- Inserts no longer allocate rectangles at every level.
- Point queries compare coordinates inline.
- `entriesAtRectangle:` takes whole subtrees inside the window without testing them.
- Large results are ordered with a radix sort on `entryIndex`.

### New

- Queries: `entryAtPoint:satisfying:ifNone:`, `entriesInside:`, `entriesNear:within:`, `nearestEntryTo:`, `bounds`.
- Entries: `RTEntry>>firstEntryAtPoint:satisfying:ifNone:` and `RTEntry>>spatialSegment`.
- Collections: `RTNaryTreeCollection`, `RTPackedTreeCollection`, `RTGridCollection` and `RTLooseQuadtreeCollection`, with the trait `RTSpatialIndex`.
- Tests: 99 test methods instead of 35. They are parametrized over every collection, so 423 tests run. `RTCollectionPropertyTest` applies 1500 random operations from fixed seeds to each collection, compares every query with brute force, and checks the tree's invariants: heights, balance, tight boxes, parents and the leaf index.

### Still to know

- `RTreeCollection` is still a binary tree. Use `RTNaryTreeCollection` or `RTPackedTreeCollection` for a shallower one.
- Long diagonal lines have large boxes that overlap most of the canvas, which defeats every bounding-box index. On such scenes the list can be faster than `RTreeCollection`. Use `RTGridCollection new segmentAware: true` for them.
- `remove:` of `RTSequenceableCollection` is still a linear search.
