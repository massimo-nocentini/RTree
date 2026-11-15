"
Tests of the structure of RTLooseQuadtreeCollection. RTCollectionTest and RTCollectionPropertyTest test its answers.
"
Class {
	#name : 'RTLooseQuadtreeCollectionTest',
	#superclass : 'TestCase',
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'helpers' }
RTLooseQuadtreeCollectionTest >> randomBoxes: count seed: seed [
	| random |
	random := Random seed: seed.
	^ (1 to: count) collect: [ :i |
		RTreeBox new
			model: i;
			entryIndex: i;
			position: (random next * 1000) @ (random next * 1000);
			extent: (random next * 20 + 1) @ (random next * 20 + 1);
			yourself ]
]

{ #category : 'tests' }
RTLooseQuadtreeCollectionTest >> testRemovalsPruneTheEmptyNodes [
	| tree boxes |
	boxes := self randomBoxes: 2000 seed: 1.
	tree := RTLooseQuadtreeCollection new.
	tree addAll: boxes.
	self assert: (tree root nodesDo: [ :each | ]; yourself) notNil.
	boxes allButFirst do: [ :each | tree remove: each ].
	tree root nodesDo: [ :node | self assert: (node == tree root or: [ node count > 0 ]) ].
	self assert: tree root count equals: 1.
	self assert: (tree entriesAtPoint: boxes first position + (0.5 @ 0.5)) asArray equals: { boxes first }
]

{ #category : 'tests' }
RTLooseQuadtreeCollectionTest >> testSmallMovesStayInTheirNode [
	| tree boxes stayed |
	boxes := self randomBoxes: 2000 seed: 2.
	tree := RTLooseQuadtreeCollection new.
	tree bulkLoad: boxes.
	stayed := 0.
	boxes do: [ :each | | node |
		node := (tree itemFor: each) parent.
		each position: each position + (0.5 @ 0.5).
		tree updateEntry: each.
		(tree itemFor: each) parent == node ifTrue: [ stayed := stayed + 1 ] ].
	self assert: stayed > 1800
]

{ #category : 'tests' }
RTLooseQuadtreeCollectionTest >> testTheRootGrowsTowardTheEntries [
	| tree far list |
	tree := RTLooseQuadtreeCollection new.
	list := RTSequenceableCollection new.
	tree capacity: 0.
	far := (1 to: 50) collect: [ :i |
		RTreeBox new
			entryIndex: i;
			position: (i * 1.0e6) @ (i * -3.0e5);
			extent: 10 @ 10;
			yourself ].
	far do: [ :each | tree add: each. list add: each ].
	self assert: tree root side > 5.0e7.
	far do: [ :each |
		self
			assert: (tree entriesAtPoint: each position + (5 @ 5)) asArray
			equals: (list entriesAtPoint: each position + (5 @ 5)) asArray ]
]
