"
A loose quadtree (Ulrich, Game Programming Gems 1, looseness 2). A record is kept in one node, chosen from its center and its larger side only: it goes down toward the quarter that holds its center while that quarter is at least as large as the record (and as minCellSize), and while its node is full (capacity:, 8 records) or already has quarters. The loose bounds of the node, its cell widened by half its side, then contain the record.
- add:, remove: and updateEntry: cost the depth of the tree, without splits nor rebalancing;
- updateEntry: does nothing while the center stays in the cell of the node and the record is not larger than it, which is the common small move;
- the root doubles toward a record whose center is outside it, so no world size is needed; bulkLoad: of an empty tree first sizes the root to the entries.
It has the cheapest builds and moves of the collections, and slower hit tests than the R-trees.

Use it with `aCanvas shapeCollection: RTLooseQuadtreeCollection new`.
"
Class {
	#name : 'RTLooseQuadtreeCollection',
	#superclass : 'RTAbstractCollection',
	#traits : 'RTSpatialIndex',
	#classTraits : 'RTSpatialIndex classTrait',
	#instVars : [
		'root',
		'items',
		'minCellSize',
		'capacity'
	],
	#category : 'RTree-Collections',
	#package : 'RTree',
	#tag : 'Collections'
}

{ #category : 'accessing' }
RTLooseQuadtreeCollection >> capacity [
	^ capacity
]

{ #category : 'accessing' }
RTLooseQuadtreeCollection >> capacity: anInteger [
	"0: every record goes as deep as its size allows (the classic loose quadtree); n > 0: a node
	keeps up to n records before the next ones go to its quarters"
	capacity := anInteger
]

{ #category : 'private' }
RTLooseQuadtreeCollection >> growTowardX: x y: y [
	"double the root toward x @ y"
	| side newRoot |
	side := root side.
	newRoot := RTQuadtreeNode
		left: (x < root left ifTrue: [ root left - side ] ifFalse: [ root left ])
		top: (y < root top ifTrue: [ root top - side ] ifFalse: [ root top ])
		side: side * 2.
	newRoot adoptChild: root.
	root := newRoot
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> indexEntries: anArray [
	"the root is sized to the entries first"
	| left top right bottom |
	left := top := Float infinity.
	right := bottom := Float negativeInfinity.
	anArray do: [ :each | | rectangle |
		rectangle := each encompassingRectangle.
		left := left min: rectangle origin x.
		top := top min: rectangle origin y.
		right := right max: rectangle corner x.
		bottom := bottom max: rectangle corner y ].
	root := RTQuadtreeNode left: left top: top side: ((right - left) max: (bottom - top)) * 1.001 + 1.0.
	anArray do: [ :each | self indexEntry: each rectangle: each encompassingRectangle ]
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> indexEntry: anRTEntry rectangle: aRectangle [
	| item |
	item := RTIndexItem on: anRTEntry rectangle: aRectangle.
	items at: anRTEntry put: item.
	self insertItem: item
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> indexIncludes: anRTEntry [
	^ items includesKey: anRTEntry
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> indexedEntriesAtX: x y: y do: aBlock [
	root ifNotNil: [ root entriesAtX: x y: y do: aBlock ]
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> indexedEntriesDo: aBlock [
	items keysDo: aBlock
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> indexedEntriesTouchingLeft: left top: top right: right bottom: bottom do: aBlock [
	root ifNotNil: [ root entriesTouchingLeft: left top: top right: right bottom: bottom do: aBlock ]
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> indexedSize [
	^ items size
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> initializeIndex [
	"the settings are kept"
	minCellSize ifNil: [ minCellSize := 1.0 ].
	capacity ifNil: [ capacity := 8 ].
	root := nil.
	items := IdentityDictionary new
]

{ #category : 'private' }
RTLooseQuadtreeCollection >> insertItem: anItem [
	| x y extent node |
	x := anItem left + anItem right / 2.
	y := anItem top + anItem bottom / 2.
	extent := anItem maxExtent.
	root ifNil: [ | side |
		side := extent * 2 max: 1024.0.
		root := RTQuadtreeNode left: x - (side / 2) top: y - (side / 2) side: side ].
	[ root containsCenterX: x y: y extent: extent ] whileFalse: [ self growTowardX: x y: y ].
	node := root.
	[ | half |
		half := node side / 2.
		half >= minCellSize and: [ half >= extent and: [ node canSplit and: [
			node hasChildren or: [ node itemCount >= capacity ] ] ] ] ]
				whileTrue: [ node := node childForX: x y: y ].
	node addItem: anItem
]

{ #category : 'private' }
RTLooseQuadtreeCollection >> itemFor: anRTEntry [
	"the record of anRTEntry, nil when it is not indexed"
	^ items at: anRTEntry ifAbsent: [ nil ]
]

{ #category : 'accessing' }
RTLooseQuadtreeCollection >> minCellSize: aNumber [
	"the smallest side of a cell, 1 by default"
	minCellSize := aNumber
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> reindexEntry: anRTEntry rectangle: aRectangle [
	"nothing to do while the record can stay in its node"
	| item node |
	item := items at: anRTEntry.
	item setRectangle: aRectangle.
	node := item parent.
	(node
		containsCenterX: item left + item right / 2
		y: item top + item bottom / 2
		extent: item maxExtent) ifTrue: [ ^ self ].
	node removeItem: item.
	self insertItem: item
]

{ #category : 'accessing' }
RTLooseQuadtreeCollection >> root [
	^ root
]

{ #category : 'private - index' }
RTLooseQuadtreeCollection >> unindexEntry: anRTEntry [
	| item |
	item := items removeKey: anRTEntry ifAbsent: [ ^ false ].
	item parent removeItem: item.
	^ true
]
