"
An R-tree for Roassal.

Rectangle tree for roassal is a collection that allows
- find shapes in a point
- find shapes in a rectangle
The time searching this elements should be close to log(n)

The tree is balanced, then it does not have the order for the elements. User should define an index `shapeIndex` to keed the order.

Use the inspector to visualize the RTree
"
Class {
	#name : 'RTreeCollection',
	#superclass : 'RTAbstractCollection',
	#instVars : [
		'root',
		'outliers'
	],
	#category : 'RTree-Collections',
	#package : 'RTree',
	#tag : 'Collections'
}

{ #category : 'visiting' }
RTreeCollection >> accept: visitor [
	root accept: visitor
]

{ #category : 'adding' }
RTreeCollection >> add: anRTEntry [
	| rectangle |
	"ask the rectangle before touching the tree: an entry that cannot answer it must not break the tree"
	rectangle := anRTEntry encompassingRectangle.
	(self isFiniteRectangle: rectangle) ifFalse: [
		"a NaN or an infinite rectangle cannot be merged with the others, keep it aside"
		self outliers add: anRTEntry.
		^ anRTEntry ].
	root := root addChild: anRTEntry.
	^ anRTEntry
]

{ #category : 'private - removing' }
RTreeCollection >> balanceRemovedPath: path [

	(1 to: path size -2) reverseDo: [ :index | | tree |
		tree := (path at: index) value.
		"the removed entry may define the border of every ancestor: recompute the rectangle, not only the height"
		tree computeRectangle.
		tree isBalanced ifFalse: [ | toMove brother |
			tree left height < tree right height ifTrue: [
				toMove := tree left.
				brother := tree right.
			] ifFalse: [
				toMove := tree right.
				brother := tree left ].
			tree fromNode: brother.
			toMove do: [ :shape | tree addChild: shape ].
			"this means that when you remove a node,
			 in order to keep it balanced
			maybe you can move a lot of nodes"
		].
	]
]

{ #category : 'enumerating' }
RTreeCollection >> do: aBlock [
	root do: aBlock.
	outliers ifNotNil: [ outliers do: aBlock ]
]

{ #category : 'finding/searching' }
RTreeCollection >> entriesAtPoint: aPoint [

	| res |
	"very important to preserv the drawing order"
	res := OrderedCollection new.
	root nodesWithPoint: aPoint list: res.
	outliers ifNotNil: [
		outliers do: [ :each | each addEntriesIn: res position: aPoint ] ].
	res := res collect: [ :s | s -> s indexesFromRoot ].
	self sortResultList: res.
	^ res collect: [ :assoc | assoc key ]
]

{ #category : 'finding/searching' }
RTreeCollection >> entriesAtRectangle: aRectangle [
	| res |
	res := OrderedCollection new.
	root nodesIntersetcsRectangle: aRectangle list: res.
	outliers ifNotNil: [
		outliers do: [ :each |
			(each encompassingRectangle intersects: aRectangle) ifTrue: [ res add: each ] ] ].
	res sort: [:a :b | a entryIndex < b entryIndex ].
	^ res
]

{ #category : 'accessing' }
RTreeCollection >> height [
	^ root height
]

{ #category : 'initialization' }
RTreeCollection >> initialize [
	super initialize.
	root := RTNilNode new
]

{ #category : 'testing' }
RTreeCollection >> isBalanced [
	^ root isBalanced
]

{ #category : 'testing' }
RTreeCollection >> isEmpty [
	^ root isEmpty and: [ outliers isNil or: [ outliers isEmpty ] ]
]

{ #category : 'testing' }
RTreeCollection >> isFiniteRectangle: aRectangle [
	"NaN and infinities break Rectangle>>merge: and the comparisons of the tree.
	x - x = 0 holds for every finite number and fails for NaN and infinities"
	| origin corner |
	origin := aRectangle origin.
	corner := aRectangle corner.
	^ origin x - origin x = 0 and: [
		origin y - origin y = 0 and: [
		corner x - corner x = 0 and: [
		corner y - corner y = 0 ] ] ]
]

{ #category : 'testing' }
RTreeCollection >> isTotalBalanced [
	^ root isTotalBalanced
]

{ #category : 'accessing' }
RTreeCollection >> outliers [
	"entries whose rectangle is not finite, they are searched linearly"
	^ outliers ifNil: [ outliers := OrderedCollection new ]
]

{ #category : 'copying' }
RTreeCollection >> postCopy [
	"the nodes are copied, the entries are shared"
	super postCopy.
	root := root copy.
	outliers := outliers copy
]

{ #category : 'shapes - ordering' }
RTreeCollection >> pushBack: anRTEntry [
	"no need it, but the entry should update its entryIndex"
]

{ #category : 'shapes - ordering' }
RTreeCollection >> pushFront: anRTEntry [
	"no need it, but the entry should update its entryIndex"
]

{ #category : 'accessing' }
RTreeCollection >> rectangle [
	^ root rectangle
]

{ #category : 'removing' }
RTreeCollection >> remove: oldRTEntry ifAbsent: anExceptionBlock [
	| path index |
	outliers ifNotNil: [
		index := outliers identityIndexOf: oldRTEntry.
		index > 0 ifTrue: [ ^ outliers removeAt: index ] ].
	path := root searchPath: oldRTEntry.
	"the search is guided by the current rectangle of the entry. When it changed
	without the collection being told, the stored leaf is elsewhere: look everywhere"
	path ifEmpty: [ path := root searchPathIgnoringBounds: oldRTEntry ].
	path ifEmpty: [ ^ anExceptionBlock value ].
	path size = 1 ifTrue: [
		root := RTNilNode new.
	] ifFalse: [
		self removeLastNodeInPath: path.
	].

	^ path last value contents
]

{ #category : 'private - removing' }
RTreeCollection >> removeLastNodeInPath: path [
	| last parent isRight brother |
	last := path last.
	parent := path nextToLast value.
	isRight := last key.
	last := last value.
	brother := isRight
		ifTrue: [ parent left ]
		ifFalse: [ parent right ].

	parent fromNode: brother.
	path size < 3 ifTrue: [ ^ self ].
	self balanceRemovedPath: path
]

{ #category : 'removing' }
RTreeCollection >> removeAll [
	"Collection>>removeAll removes while it iterates"
	root := RTNilNode new.
	outliers := nil
]

{ #category : 'accessing' }
RTreeCollection >> root [
	^ root
]

{ #category : 'public' }
RTreeCollection >> shouldSwap: anAssociation and: anAssociation2 [

	| v1 v2 size|
	v1 := anAssociation value.
	v2 := anAssociation2 value.

	size := v1 size min: v2 size.
	1 to: size do: [ :i| |index1 index2|
		index1 := v1 at: i.
		index2 := v2 at: i.
		index1 = index2 ifFalse: [
			^ index1 > index2 ]
	].
	^ v1 size = v2 size
		ifTrue: [ false ]
		ifFalse: [ v1 size > v2 size  ]
]

{ #category : 'public' }
RTreeCollection >> sortResultList: aCollection [
	aCollection sort: [ :a :b | self shouldSwap: a and: b ]
]

{ #category : 'update' }
RTreeCollection >> updateEntry: anRTEntry [

	self remove: anRTEntry.
	anRTEntry resetEncompassingRectangle.
	self add: anRTEntry
]

{ #category : 'update' }
RTreeCollection >> updateEntry: anRTEntry before: anotherRTEntry [
	"do not needed because there is no order in this tree"
]
