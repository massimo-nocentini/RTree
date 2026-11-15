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
