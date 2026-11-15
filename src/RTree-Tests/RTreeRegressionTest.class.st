"
Regression tests for the bugs found by the audit of RTree v1.01 (November 2026).
The comment of each test describes the bug it covers.
"
Class {
	#name : 'RTreeRegressionTest',
	#superclass : 'TestCase',
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'helpers' }
RTreeRegressionTest >> assertTight: aTree [
	"every internal node is the exact union of its children, has the right height and is AVL balanced"
	aTree root withAllChildren do: [ :node |
		node isLeaf
			ifTrue: [ self assert: node rectangle equals: node contents encompassingRectangle ]
			ifFalse: [
				self assert: node rectangle equals: (node left rectangle merge: node right rectangle).
				self assert: node height equals: (node left height max: node right height) + 1.
				self assert: node isBalanced ] ]
]

{ #category : 'helpers' }
RTreeRegressionTest >> boxAt: aPoint extent: anExtent index: anInteger [
	^ RTreeBox new
		model: anInteger;
		entryIndex: anInteger;
		position: aPoint;
		extent: anExtent;
		yourself
]

{ #category : 'helpers' }
RTreeRegressionTest >> randomBoxes: aNumber seed: aSeed [
	| random |
	random := Random seed: aSeed.
	^ (1 to: aNumber) collect: [ :i |
		self boxAt: (random next * 1000) @ (random next * 1000) extent: 10 @ 10 index: i ]
]

{ #category : 'tests - removing' }
RTreeRegressionTest >> testRemoveManyKeepsTightRectangles [
	"After many removals the node rectangles were up to 2x too large"
	| tree boxes |
	tree := RTreeCollection new.
	boxes := self randomBoxes: 300 seed: 1.
	tree addAll: boxes.
	(boxes first: 290) do: [ :each | tree remove: each ].
	self assertTight: tree.
	self
		assert: tree rectangle
		equals: (Rectangle merging: ((boxes last: 10) collect: [ :each | each encompassingRectangle ]))
]

{ #category : 'tests - removing' }
RTreeRegressionTest >> testRemoveShrinksAncestorRectangles [
	"The ancestors of a removed entry kept its extent"
	| tree boxes |
	tree := RTreeCollection new.
	boxes := {
		self boxAt: 213 @ 359 extent: 21 @ 22 index: 1.
		self boxAt: 301 @ 452 extent: 38 @ 21 index: 2.
		self boxAt: 580 @ 866 extent: 32 @ 0 index: 3.
		self boxAt: 922 @ 871 extent: 27 @ 19 index: 4 }.
	tree addAll: boxes.
	tree remove: boxes first.
	self assert: tree rectangle equals: ((301 @ 452) corner: (949 @ 890)).
	self assertTight: tree
]

{ #category : 'tests - update' }
RTreeRegressionTest >> testRemoveAfterTheRectangleChangedSilently [
	"remove: searched the leaf with the current rectangle of the entry"
	| tree boxes box |
	tree := RTreeCollection new.
	boxes := self randomBoxes: 32 seed: 2.
	tree addAll: boxes.
	box := boxes at: 7.
	box position: 900 @ 50; resetEncompassingRectangle.
	self assert: (tree remove: box) identicalTo: box.
	self assert: tree size equals: 31.
	self deny: (tree includes: box)
]

{ #category : 'tests - update' }
RTreeRegressionTest >> testUpdateAfterTheRectangleChangedSilently [
	"The entry was moved and its cached rectangle reset before updateEntry:, as RSBitmap>>form: did"
	| tree boxes box |
	tree := RTreeCollection new.
	boxes := self randomBoxes: 32 seed: 2.
	tree addAll: boxes.
	box := boxes at: 5.
	box position: 900 @ 50; resetEncompassingRectangle.
	tree updateEntry: box.
	self assert: (tree entriesAtPoint: 905 @ 55) asArray equals: { box }.
	box := boxes at: 9.
	box extent: 100 @ 100; resetEncompassingRectangle.
	tree updateEntry: box.
	self assert: ((tree entriesAtPoint: box position + (95 @ 95)) includes: box).
	self assert: tree size equals: 32.
	self assertTight: tree
]

{ #category : 'tests - adding' }
RTreeRegressionTest >> testFailingAddKeepsTheTree [
	"A failing add: left a 1-element tree with a nil child"
	| tree box other |
	tree := RTreeCollection new.
	box := self boxAt: 0 @ 0 extent: 10 @ 10 index: 1.
	tree add: box.
	self should: [ tree add: nil ] raise: Error.
	self assert: tree size equals: 1.
	self assert: (tree entriesAtPoint: 5 @ 5) asArray equals: { box }.
	other := self boxAt: 20 @ 20 extent: 10 @ 10 index: 2.
	tree add: other.
	self assert: tree size equals: 2.
	self assertTight: tree
]

{ #category : 'tests - adding' }
RTreeRegressionTest >> testInfiniteRectangle [
	"An infinite extent gives a NaN corner"
	| tree boxes inf |
	tree := RTreeCollection new.
	boxes := self randomBoxes: 50 seed: 4.
	tree addAll: boxes.
	inf := self boxAt: Float infinity negated @ 0 extent: Float infinity @ 10 index: 51.
	tree add: inf.
	self assert: tree size equals: 51.
	self assert: (tree remove: inf) identicalTo: inf.
	boxes do: [ :each | self assert: ((tree entriesAtPoint: each position + (5 @ 5)) includes: each) ].
	self assertTight: tree
]

{ #category : 'tests - adding' }
RTreeRegressionTest >> testNaNRectangleDoesNotHideTheOthers [
	"One NaN rectangle turned its ancestors into NaN, and its siblings could not be found nor removed"
	| tree boxes nan |
	tree := RTreeCollection new.
	boxes := self randomBoxes: 256 seed: 3.
	tree addAll: boxes.
	nan := self boxAt: Float nan @ Float nan extent: 10 @ 10 index: 257.
	tree add: nan.
	self assert: tree size equals: 257.
	self assert: (tree includes: nan).
	boxes do: [ :each | self assert: ((tree entriesAtPoint: each position + (5 @ 5)) includes: each) ].
	"intersects: answers true for NaN, as in RTSequenceableCollection"
	self assert: ((tree entriesAtRectangle: (0 @ 0 corner: 2000 @ 2000)) includes: nan).
	self assertTight: tree.
	(boxes first: 128) do: [ :each | self assert: (tree remove: each) identicalTo: each ].
	self assert: (tree remove: nan) identicalTo: nan.
	self assert: tree size equals: 128.
	self assertTight: tree
]

{ #category : 'tests - enumerating' }
RTreeRegressionTest >> testNodeCollect [
	"RTNode>>collect: ignored its block"
	| tree |
	tree := RTreeCollection new.
	tree addAll: (self randomBoxes: 5 seed: 6).
	self assert: (tree root collect: [ :each | each model ]) asArray sort equals: #( 1 2 3 4 5 )
]

{ #category : 'tests - finding' }
RTreeRegressionTest >> testEntriesAtPointOrderWithoutParent [
	"Entries without parent had empty indexesFromRoot, so the topmost entry was not first"
	| tree list boxes random |
	tree := RTreeCollection new.
	list := RTSequenceableCollection new.
	random := Random seed: 8.
	boxes := (1 to: 60) collect: [ :i |
		self boxAt: (random next * 100) @ (random next * 100) extent: 30 @ 30 index: i ].
	boxes do: [ :each | tree add: each. list add: each ].
	0 to: 130 by: 5 do: [ :x |
		0 to: 130 by: 5 do: [ :y |
			self
				assert: (tree entriesAtPoint: x @ y) asArray
				equals: (list entriesAtPoint: x @ y) asArray ] ].
	self assert: (tree entryAtPoint: 50 @ 50) identicalTo: (list entryAtPoint: 50 @ 50)
]

{ #category : 'tests - finding' }
RTreeRegressionTest >> testEntriesAtRectangleWithoutEntryIndex [
	"The sort by entryIndex failed when no container numbered the entries"
	| tree box1 box2 |
	tree := RTreeCollection new.
	box1 := RTreeBox new size: 10; yourself.
	box2 := RTreeBox new size: 10; position: 5 @ 5; yourself.
	tree add: box1; add: box2.
	self assert: (tree entriesAtRectangle: (0 @ 0 corner: 20 @ 20)) size equals: 2.
	self assert: (tree entriesAtPoint: 7 @ 7) size equals: 2
]

{ #category : 'tests - finding' }
RTreeRegressionTest >> testEntriesOnTheBorderOfTheirRectangle [
	"The tree pruned with the half-open Rectangle>>containsPoint:, so an entry
	that accepts the far border of its rectangle (a line end point) was not found"
	| tree list boxes |
	tree := RTreeCollection new.
	list := RTSequenceableCollection new.
	boxes := (1 to: 20) collect: [ :i |
		RTreeClosedBox new position: (i * 10) @ 0; extent: 10 @ 10; entryIndex: i; yourself ].
	boxes do: [ :each | tree add: each. list add: each ].
	boxes do: [ :each | | corner |
		corner := each encompassingRectangle corner.
		{ corner. corner x @ 5. 15 @ corner y. each position } do: [ :p |
			self
				assert: (tree entriesAtPoint: p) asArray
				equals: (list entriesAtPoint: p) asArray ] ]
]

{ #category : 'tests - adding' }
RTreeRegressionTest >> testInsertionAllocatesLittle [
	"Every level of an insertion created about 1 KB of Arrays, closures, Points and Rectangles"
	| tree boxes before bytes |
	tree := RTreeCollection new.
	boxes := self randomBoxes: 3000 seed: 12.
	boxes do: [ :each | each encompassingRectangle ].
	tree addAll: (boxes first: 2000).
	Smalltalk garbageCollect.
	before := Smalltalk vm parameterAt: 34.
	(boxes last: 1000) do: [ :each | tree add: each ].
	bytes := ((Smalltalk vm parameterAt: 34) - before) / 1000.
	"v1.01: about 15 KB per entry at this size"
	self assert: bytes < 4000.
	self assertTight: tree
]

{ #category : 'tests - removing' }
RTreeRegressionTest >> testRemoveDoesNotReinsert [
	"Rebalancing after a removal inserted a whole subtree again, entry by entry.
	With rotations, at most the sibling of the removed leaf moves to another node"
	| tree boxes random |
	tree := RTreeCollection new.
	boxes := self randomBoxes: 2000 seed: 13.
	tree addAll: boxes.
	random := Random seed: 14.
	((boxes copy shuffleBy: random) first: 1500) do: [ :each | | before moved |
		before := IdentityDictionary new.
		(tree root withAllChildren select: [ :node | node isLeaf ]) do: [ :leaf | before at: leaf contents put: leaf ].
		tree remove: each.
		moved := (tree root withAllChildren select: [ :node | node isLeaf ])
			count: [ :leaf | (before at: leaf contents) ~~ leaf ].
		self assert: moved <= 1 ].
	self assert: tree size equals: 500.
	self assertTight: tree
]

{ #category : 'tests - removing' }
RTreeRegressionTest >> testRemoveKeepsAVLBalance [
	"The rotation based deletion keeps every node balanced, its height and its rectangle right"
	| tree boxes random |
	random := Random seed: 15.
	#( 7 64 513 ) do: [ :count |
		tree := RTreeCollection new.
		boxes := self randomBoxes: count seed: count.
		tree addAll: boxes.
		(boxes copy shuffleBy: random) doWithIndex: [ :each :i |
			tree remove: each.
			self assert: tree size equals: count - i.
			i \\ 16 = 0 ifTrue: [ self assertTight: tree ] ].
		self assert: tree isEmpty ]
]

{ #category : 'tests - adding' }
RTreeRegressionTest >> testAddTwiceHoldsOnce [
	"An entry added twice had two leaves, and updateEntry: moved only one of them"
	| tree boxes box |
	tree := RTreeCollection new.
	boxes := self randomBoxes: 20 seed: 16.
	tree addAll: boxes.
	box := boxes first.
	tree add: box.
	self assert: tree size equals: 20.
	box position: 1300 @ 1300.
	tree updateEntry: box.
	self assert: (tree entriesAtPoint: 1305 @ 1305) asArray equals: { box }.
	self deny: ((tree entriesAtRectangle: (1290 @ 1290 corner: 1320 @ 1320)) isEmpty).
	tree remove: box.
	self deny: (tree includes: box).
	self deny: ((tree entriesAtRectangle: (-10 @ -10 corner: 2000 @ 2000)) includes: box).
	self assertTight: tree
]

{ #category : 'tests - removing' }
RTreeRegressionTest >> testParentsAndLeaves [
	"Every node knows its parent and every entry its leaf, after adds, removals and copies"
	| tree boxes check copy |
	check := [ :aTree | | leafCount |
		leafCount := 0.
		aTree root withAllChildren do: [ :node |
			node isLeaf
				ifTrue: [
					leafCount := leafCount + 1.
					self assert: (aTree leaves at: node contents) identicalTo: node ]
				ifFalse: [
					self assert: node left parent identicalTo: node.
					self assert: node right parent identicalTo: node ] ].
		self assert: aTree root parent isNil.
		self assert: aTree leaves size equals: leafCount ].
	tree := RTreeCollection new.
	boxes := self randomBoxes: 400 seed: 17.
	tree addAll: boxes.
	check value: tree.
	(boxes first: 150) do: [ :each | tree remove: each ].
	check value: tree.
	copy := tree copy.
	check value: copy.
	(boxes last: 100) do: [ :each | copy remove: each ].
	check value: copy.
	check value: tree.
	self assert: tree size equals: 250.
	self assert: copy size equals: 150
]

{ #category : 'tests - removing' }
RTreeRegressionTest >> testRemoveDoesNotNeedTheRectangle [
	"remove: walks up from the leaf of the entry, so it reads no rectangle and costs
	O(log n) even when every entry has the same rectangle (the shapes of a builder before the layout)"
	| tree boxes box |
	tree := RTreeCollection new.
	boxes := (1 to: 1024) collect: [ :i | self boxAt: 0 @ 0 extent: 10 @ 10 index: i ].
	tree addAll: boxes.
	box := boxes at: 700.
	"the entry cannot answer its rectangle anymore"
	box position: nil; resetEncompassingRectangle.
	self should: [ box encompassingRectangle ] raise: Error.
	self assert: (tree remove: box) identicalTo: box.
	self assert: tree size equals: 1023.
	self deny: (tree includes: box).
	(boxes first: 600) do: [ :each | tree remove: each ].
	self assert: tree size equals: 423.
	self assertTight: tree
]

{ #category : 'tests - removing' }
RTreeRegressionTest >> testSubclassThatSetsTheRoot [
	"the index is rebuilt when a subclass (RTBulkLoadRTreeCollection in Roassal) sets the root itself"
	| tree other boxes |
	other := RTreeCollection new.
	boxes := self randomBoxes: 50 seed: 18.
	other addAll: boxes.
	tree := RTreeCollection new.
	tree instVarNamed: 'root' put: other root copy.
	self assert: tree size equals: 50.
	self assert: (tree remove: boxes first) identicalTo: boxes first.
	self assert: tree size equals: 49.
	self assertTight: tree
]

{ #category : 'tests - update' }
RTreeRegressionTest >> testSmallMovesUpdateInPlace [
	"Every updateEntry: removed and added the entry again"
	| tree list boxes random inPlace |
	tree := RTreeCollection new.
	list := RTSequenceableCollection new.
	boxes := self randomBoxes: 500 seed: 19.
	boxes do: [ :each | tree add: each. list add: each ].
	random := Random seed: 20.
	inPlace := 0.
	3000 timesRepeat: [ | box leaf |
		box := boxes at: (random next * boxes size) floor + 1.
		leaf := tree leaves at: box.
		box position: box position + (((random next * 6) - 3) @ ((random next * 6) - 3)).
		tree updateEntry: box.
		list updateEntry: box.
		(tree leaves at: box) == leaf ifTrue: [ inPlace := inPlace + 1 ] ].
	self assert: inPlace > 1500.
	self assertTight: tree.
	self assert: tree size equals: 500.
	0 to: 1000 by: 37 do: [ :x |
		0 to: 1000 by: 41 do: [ :y |
			self assert: (tree entriesAtPoint: x @ y) asArray equals: (list entriesAtPoint: x @ y) asArray ] ]
]

{ #category : 'tests - finding' }
RTreeRegressionTest >> testEntriesAtRectangleOrder [
	"The result is in entryIndex order, with or without the shortcut of the contained nodes
	and the placement by index"
	| tree list boxes random windows |
	tree := RTreeCollection new.
	list := RTSequenceableCollection new.
	boxes := self randomBoxes: 2000 seed: 21.
	boxes do: [ :each | list add: each ].
	random := Random seed: 22.
	(boxes copy shuffleBy: random) do: [ :each | tree add: each ].
	windows := OrderedCollection new.
	windows
		add: (-10 @ -10 corner: 1020 @ 1020);
		add: (0 @ 0 corner: 1010 @ 1010);
		add: (0 @ 0 corner: 500 @ 1010);
		add: (300 @ 300 corner: 700 @ 400);
		add: (450 @ 450 corner: 460 @ 460).
	20 timesRepeat: [ windows add: ((random next * 1000) @ (random next * 1000) extent: (random next * 600) @ (random next * 600)) ].
	windows do: [ :w |
		self assert: (tree entriesAtRectangle: w) asArray equals: (list entriesAtRectangle: w) asArray ]
]

{ #category : 'tests - finding' }
RTreeRegressionTest >> testEntriesAtRectangleWithRepeatedOrSparseIndexes [
	"The placement by index must not lose entries that share an index"
	| tree boxes all |
	tree := RTreeCollection new.
	boxes := self randomBoxes: 1000 seed: 23.
	boxes do: [ :each | each entryIndex: each model \\ 7 ].
	tree addAll: boxes.
	all := tree entriesAtRectangle: (-10 @ -10 corner: 1020 @ 1020).
	self assert: all size equals: 1000.
	self assert: all asIdentitySet size equals: 1000.
	self assert: ((1 to: 999) allSatisfy: [ :i | (all at: i) entryIndex <= (all at: i + 1) entryIndex ]).
	boxes do: [ :each | each entryIndex: each model * 1000 ].
	all := tree entriesAtRectangle: (-10 @ -10 corner: 1020 @ 1020).
	self assert: (all collect: [ :each | each model ]) asArray equals: (1 to: 1000) asArray
]

{ #category : 'tests - finding' }
RTreeRegressionTest >> testEntriesAtPointOfLongEntries [
	"entriesAtPoint: built an OrderedCollection and an Association for every hit and sorted them all.
	With long, overlapping entries (the bounding boxes of edges) the order must still be the list's"
	| tree list random boxes |
	tree := RTreeCollection new.
	list := RTSequenceableCollection new.
	random := Random seed: 24.
	boxes := (1 to: 400) collect: [ :i | | p q |
		p := (random next * 1000) @ (random next * 1000).
		q := (random next * 1000) @ (random next * 1000).
		self boxAt: (p min: q) extent: (p max: q) - (p min: q) + 1 index: i ].
	boxes do: [ :each | tree add: each. list add: each ].
	200 timesRepeat: [ | p |
		p := (random next * 1000) @ (random next * 1000).
		self assert: (tree entriesAtPoint: p) asArray equals: (list entriesAtPoint: p) asArray ]
]

{ #category : 'tests - adding' }
RTreeRegressionTest >> testBulkLoad [
	"bulkLoad: (used by useRTree) built the tree by repeated add:. It now builds a
	balanced tree in Sort-Tile-Recursive order that accepts later changes"
	| tree list boxes nan random |
	boxes := self randomBoxes: 1000 seed: 25.
	nan := self boxAt: Float nan @ 0 extent: 10 @ 10 index: 1001.
	tree := RTreeCollection new.
	tree bulkLoad: boxes , { nan. boxes first }.
	list := RTSequenceableCollection new.
	list addAll: boxes.
	self assert: tree size equals: 1001.
	self assert: tree isTotalBalanced.
	self assert: tree height <= 11.
	self assertTight: tree.
	random := Random seed: 26.
	100 timesRepeat: [ | p w |
		p := (random next * 1000) @ (random next * 1000).
		w := p extent: 50 @ 50.
		self assert: (tree entriesAtPoint: p) asArray equals: (list entriesAtPoint: p) asArray.
		self assert: ((tree entriesAtRectangle: w) copyWithout: nan) asArray equals: (list entriesAtRectangle: w) asArray ].
	(boxes first: 400) do: [ :each | tree remove: each ].
	(boxes last: 100) do: [ :each | each position: each position + (3 @ 3). tree updateEntry: each ].
	tree add: (self boxAt: 5 @ 5 extent: 10 @ 10 index: 1002).
	self assert: tree size equals: 602.
	self assertTight: tree
]
