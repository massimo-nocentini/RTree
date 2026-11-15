"
Tests of the changes kept aside by RTPackedTreeCollection. RTCollectionTest and RTCollectionPropertyTest test its answers.
"
Class {
	#name : 'RTPackedTreeCollectionTest',
	#superclass : 'TestCase',
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'helpers' }
RTPackedTreeCollectionTest >> randomBoxes: count seed: seed [
	| random |
	random := Random seed: seed.
	^ (1 to: count) collect: [ :i |
		RTreeBox new
			model: i;
			entryIndex: i;
			position: (random next * 1000) @ (random next * 1000);
			extent: 10 @ 10;
			yourself ]
]

{ #category : 'tests' }
RTPackedTreeCollectionTest >> testAddsArePendingUntilThereAreMany [
	| tree boxes list |
	boxes := self randomBoxes: 3000 seed: 1.
	tree := RTPackedTreeCollection new.
	list := RTSequenceableCollection new.
	tree bulkLoad: (boxes first: 2000).
	list addAll: (boxes first: 2000).
	self assert: tree rebuilds equals: 1.
	(boxes copyFrom: 2001 to: 2100) do: [ :each | tree add: each. list add: each ].
	self assert: tree pendingCount equals: 100.
	"100 pending entries are at most 1/16 of 2000: the queries scan them"
	self assert: (tree entriesAtPoint: (boxes at: 2050) position + (5 @ 5)) asArray equals: (list entriesAtPoint: (boxes at: 2050) position + (5 @ 5)) asArray.
	self assert: tree rebuilds equals: 1.
	(boxes copyFrom: 2101 to: 2200) do: [ :each | tree add: each. list add: each ].
	self assert: (tree entriesAtRectangle: (100 @ 100 extent: 300 @ 300)) asArray equals: (list entriesAtRectangle: (100 @ 100 extent: 300 @ 300)) asArray.
	self assert: tree rebuilds equals: 2.
	self assert: tree pendingCount equals: 0
]

{ #category : 'tests' }
RTPackedTreeCollectionTest >> testSmallMovesStayInTheirSlot [
	| tree boxes list |
	boxes := self randomBoxes: 2000 seed: 2.
	tree := RTPackedTreeCollection new.
	list := RTSequenceableCollection new.
	tree bulkLoad: boxes.
	list addAll: boxes.
	boxes do: [ :each |
		each position: each position + (0.5 @ 0.5).
		tree updateEntry: each.
		list updateEntry: each ].
	self assert: tree pendingCount < 1000.
	0 to: 1000 by: 47 do: [ :x |
		0 to: 1000 by: 53 do: [ :y |
			self assert: (tree entriesAtPoint: x @ y) asArray equals: (list entriesAtPoint: x @ y) asArray ] ].
	self assert: tree size equals: 2000
]

{ #category : 'tests' }
RTPackedTreeCollectionTest >> testRemovalsBlankTheSlots [
	| tree boxes |
	boxes := self randomBoxes: 2000 seed: 3.
	tree := RTPackedTreeCollection new.
	tree bulkLoad: boxes.
	(boxes first: 100) do: [ :each | tree remove: each ].
	self assert: (tree entriesAtPoint: boxes first position + (5 @ 5)) isEmpty.
	self assert: tree rebuilds equals: 1.
	(boxes copyFrom: 101 to: 1999) do: [ :each | tree remove: each ].
	self assert: (tree entriesAtPoint: boxes last position + (5 @ 5)) asArray equals: { boxes last }.
	self assert: tree size equals: 1.
	self assert: tree rebuilds equals: 2
]
