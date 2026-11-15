"
A node of RTLooseQuadtreeCollection: the square cell [left, left + side) x [top, top + side). Its loose bounds are the cell widened by side / 2 on every side (looseness 2), and by a tiny slack for the rounding of the coordinates. It holds the records whose center is in the cell and whose larger side is at most the side of the cell, and up to four children, the quarters of the cell. count is the number of records in the node and below.
"
Class {
	#name : 'RTQuadtreeNode',
	#superclass : 'Object',
	#instVars : [
		'left',
		'top',
		'side',
		'looseLeft',
		'looseTop',
		'looseRight',
		'looseBottom',
		'parent',
		'children',
		'items',
		'count'
	],
	#category : 'RTree-Nodes',
	#package : 'RTree',
	#tag : 'Nodes'
}

{ #category : 'instance creation' }
RTQuadtreeNode class >> left: aLeft top: aTop side: aSide [
	^ self new
		setLeft: aLeft top: aTop side: aSide;
		yourself
]

{ #category : 'adding' }
RTQuadtreeNode >> addItem: anItem [
	| node |
	items ifNil: [ items := OrderedCollection new: 4 ].
	items add: anItem.
	anItem parent: self.
	node := self.
	[ node isNil ] whileFalse: [
		node incrementCount: 1.
		node := node parent ]
]

{ #category : 'adding' }
RTQuadtreeNode >> adoptChild: aNode [
	"aNode is a quarter of the receiver, the previous root"
	| index |
	index := (aNode left = left ifTrue: [ 1 ] ifFalse: [ 2 ]) + (aNode top = top ifTrue: [ 0 ] ifFalse: [ 2 ]).
	children := Array new: 4.
	children at: index put: aNode.
	aNode parent: self.
	count := aNode count
]

{ #category : 'testing' }
RTQuadtreeNode >> canSplit [
	"the quarters of the cell have distinct coordinates"
	^ side / 2 > ((left abs max: top abs) * 1.0e-12)
]

{ #category : 'accessing' }
RTQuadtreeNode >> childForX: x y: y [
	"the quarter of the cell that holds x @ y, created when needed"
	| half index child |
	half := side / 2.
	index := (x < (left + half) ifTrue: [ 1 ] ifFalse: [ 2 ]) + (y < (top + half) ifTrue: [ 0 ] ifFalse: [ 2 ]).
	children ifNil: [ children := Array new: 4 ].
	child := children at: index.
	child ifNil: [
		child := RTQuadtreeNode
			left: (index odd ifTrue: [ left ] ifFalse: [ left + half ])
			top: (index <= 2 ifTrue: [ top ] ifFalse: [ top + half ])
			side: half.
		child parent: self.
		children at: index put: child ].
	^ child
]

{ #category : 'testing' }
RTQuadtreeNode >> containsCenterX: x y: y extent: anExtent [
	"a record with this center and this larger side can be in the receiver"
	^ anExtent <= side and: [ x >= left and: [ x < (left + side) and: [ y >= top and: [ y < (top + side) ] ] ] ]
]

{ #category : 'accessing' }
RTQuadtreeNode >> count [
	^ count
]

{ #category : 'finding/searching' }
RTQuadtreeNode >> entriesAtX: x y: y do: aBlock [
	items ifNotNil: [
		items do: [ :each |
			(each left <= x and: [ x <= each right and: [ each top <= y and: [ y <= each bottom ] ] ])
				ifTrue: [ aBlock value: each entry ] ] ].
	children ifNil: [ ^ self ].
	children do: [ :each |
		(each notNil and: [ each looselyContainsX: x y: y ])
			ifTrue: [ each entriesAtX: x y: y do: aBlock ] ]
]

{ #category : 'finding/searching' }
RTQuadtreeNode >> entriesTouchingLeft: aLeft top: aTop right: aRight bottom: aBottom do: aBlock [
	items ifNotNil: [
		items do: [ :each |
			(each left <= aRight and: [ aLeft <= each right and: [ each top <= aBottom and: [ aTop <= each bottom ] ] ])
				ifTrue: [ aBlock value: each entry ] ] ].
	children ifNil: [ ^ self ].
	children do: [ :each |
		(each notNil and: [ each looselyTouchesLeft: aLeft top: aTop right: aRight bottom: aBottom ])
			ifTrue: [ each entriesTouchingLeft: aLeft top: aTop right: aRight bottom: aBottom do: aBlock ] ]
]

{ #category : 'testing' }
RTQuadtreeNode >> hasChildren [
	^ children notNil
]

{ #category : 'accessing' }
RTQuadtreeNode >> incrementCount: anInteger [
	count := count + anInteger
]

{ #category : 'accessing' }
RTQuadtreeNode >> itemCount [
	^ items ifNil: [ 0 ] ifNotNil: [ items size ]
]

{ #category : 'accessing' }
RTQuadtreeNode >> items [
	^ items ifNil: [ #() ]
]

{ #category : 'accessing' }
RTQuadtreeNode >> left [
	^ left
]

{ #category : 'testing' }
RTQuadtreeNode >> looselyContainsX: x y: y [
	^ looseLeft <= x and: [ x <= looseRight and: [ looseTop <= y and: [ y <= looseBottom ] ] ]
]

{ #category : 'testing' }
RTQuadtreeNode >> looselyTouchesLeft: aLeft top: aTop right: aRight bottom: aBottom [
	^ looseLeft <= aRight and: [ aLeft <= looseRight and: [ looseTop <= aBottom and: [ aTop <= looseBottom ] ] ]
]

{ #category : 'enumerating' }
RTQuadtreeNode >> nodesDo: aBlock [
	aBlock value: self.
	children ifNotNil: [ children do: [ :each | each ifNotNil: [ each nodesDo: aBlock ] ] ]
]

{ #category : 'accessing' }
RTQuadtreeNode >> parent [
	^ parent
]

{ #category : 'accessing' }
RTQuadtreeNode >> parent: aNode [
	parent := aNode
]

{ #category : 'removing' }
RTQuadtreeNode >> removeChildNode: aNode [
	| index |
	index := children identityIndexOf: aNode.
	index = 0 ifTrue: [ ^ self ].
	children at: index put: nil.
	(children allSatisfy: [ :each | each isNil ]) ifTrue: [ children := nil ].
	aNode parent: nil
]

{ #category : 'removing' }
RTQuadtreeNode >> removeItem: anItem [
	"and prune the empty nodes up, never the root"
	| node |
	items remove: anItem.
	items isEmpty ifTrue: [ items := nil ].
	anItem parent: nil.
	node := self.
	[ node isNil ] whileFalse: [
		node incrementCount: -1.
		node := node parent ].
	node := self.
	[ node parent notNil and: [ node count = 0 ] ] whileTrue: [ | parentNode |
		parentNode := node parent.
		parentNode removeChildNode: node.
		node := parentNode ]
]

{ #category : 'initialization' }
RTQuadtreeNode >> setLeft: aLeft top: aTop side: aSide [
	| half slack |
	left := aLeft.
	top := aTop.
	side := aSide.
	count := 0.
	half := aSide / 2.
	"the computed coordinates of the cells are rounded: a little more than the looseness"
	slack := ((aLeft abs max: aTop abs) + aSide) * 1.0e-12.
	looseLeft := aLeft - half - slack.
	looseTop := aTop - half - slack.
	looseRight := aLeft + aSide + half + slack.
	looseBottom := aTop + aSide + half + slack
]

{ #category : 'accessing' }
RTQuadtreeNode >> side [
	^ side
]

{ #category : 'accessing' }
RTQuadtreeNode >> top [
	^ top
]
