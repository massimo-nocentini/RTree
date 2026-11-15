"
Tests of the structure of RTNaryTreeCollection. RTCollectionTest and RTCollectionPropertyTest test its answers.
"
Class {
	#name : 'RTNaryTreeCollectionTest',
	#superclass : 'TestCase',
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'helpers' }
RTNaryTreeCollectionTest >> leafDepthsOf: aTree [
	| depths walk |
	depths := Set new.
	walk := nil.
	walk := [ :node :depth |
		node isLeaf
			ifTrue: [ depths add: depth ]
			ifFalse: [ node children do: [ :each | walk value: each value: depth + 1 ] ] ].
	walk value: aTree root value: 1.
	^ depths
]

{ #category : 'helpers' }
RTNaryTreeCollectionTest >> randomBoxes: count seed: seed [
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
RTNaryTreeCollectionTest >> testBulkLoadPacksTheNodes [
	| tree boxes |
	boxes := self randomBoxes: 5000 seed: 1.
	tree := RTNaryTreeCollection new.
	tree bulkLoad: boxes.
	"5000 / 16 = 313 leaves, 20 nodes, 2 nodes and the root"
	self assert: tree height equals: 4.
	self assert: (self leafDepthsOf: tree) size equals: 1.
	self assert: tree size equals: 5000.
	self assert: tree bounds equals: (Rectangle merging: (boxes collect: [ :each | each encompassingRectangle ]))
]

{ #category : 'tests' }
RTNaryTreeCollectionTest >> testRemovalsCondenseTheTree [
	| tree boxes |
	boxes := self randomBoxes: 2000 seed: 2.
	tree := RTNaryTreeCollection new.
	tree maxEntries: 4.
	tree addAll: boxes.
	(boxes first: 1990) do: [ :each | tree remove: each ].
	self assert: tree size equals: 10.
	self assert: (self leafDepthsOf: tree) size equals: 1.
	tree root nodesDo: [ :node |
		node == tree root ifFalse: [ self assert: node children size >= tree minEntries ] ].
	(boxes last: 10) do: [ :each | tree remove: each ].
	self assert: tree isEmpty.
	self assert: tree height equals: 1.
	self assert: tree bounds isNil
]

{ #category : 'tests' }
RTNaryTreeCollectionTest >> testSplitsKeepTheTreeBalanced [
	| tree boxes |
	boxes := self randomBoxes: 3000 seed: 3.
	tree := RTNaryTreeCollection new.
	tree maxEntries: 4.
	tree addAll: boxes.
	self assert: (self leafDepthsOf: tree) size equals: 1.
	tree root nodesDo: [ :node |
		self assert: node children size <= 4.
		node == tree root ifFalse: [ self assert: node children size >= 2 ] ].
	self assert: tree height <= 12
]

{ #category : 'tests' }
RTNaryTreeCollectionTest >> testSmallMovesStayInTheirLeaf [
	| tree boxes leaves inPlace |
	boxes := self randomBoxes: 3000 seed: 4.
	tree := RTNaryTreeCollection new.
	tree bulkLoad: boxes.
	inPlace := 0.
	boxes do: [ :each | | leaf |
		leaf := (tree itemFor: each) parent.
		each position: each position + (1 @ 1).
		tree updateEntry: each.
		(tree itemFor: each) parent == leaf ifTrue: [ inPlace := inPlace + 1 ] ].
	self assert: inPlace > 2400.
	self assert: (tree entriesAtPoint: boxes first position + (5 @ 5)) asArray first identicalTo: boxes first
]

{ #category : 'tests' }
RTNaryTreeCollectionTest >> testLayoutPacksTheTreeAgain [
	"far moves are pending until the next query; after a layout the tree is packed again"
	| tree list boxes |
	boxes := (1 to: 3000) collect: [ :i |
		RTreeBox new model: i; entryIndex: i; position: 0 @ 0; extent: 10 @ 10; yourself ].
	tree := RTNaryTreeCollection new.
	list := RTSequenceableCollection new.
	tree addAll: boxes.
	list addAll: boxes.
	boxes doWithIndex: [ :each :i |
		each position: (i \\ 60 * 15) @ (i // 60 * 15).
		tree updateEntry: each.
		list updateEntry: each ].
	self assert: (tree entriesAtPoint: 100 @ 100) asArray equals: (list entriesAtPoint: 100 @ 100) asArray.
	"3000 / 16 = 188 leaves, 12 nodes and the root"
	self assert: tree height equals: 3.
	self assert: tree bounds equals: list bounds.
	0 to: 900 by: 37 do: [ :x |
		0 to: 750 by: 41 do: [ :y |
			self
				assert: (tree entriesAtRectangle: (x @ y extent: 40 @ 30)) asArray
				equals: (list entriesAtRectangle: (x @ y extent: 40 @ 30)) asArray ] ]
]

