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
