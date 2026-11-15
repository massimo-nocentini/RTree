"
An axis aligned rectangle kept as four numbers, and the node that holds it. The superclass of the records of the entries in the spatial indexes (RTIndexItem) and of the nodes of RTNaryTreeCollection: their inner loops compare numbers instead of sending messages to Rectangles and Points.
"
Class {
	#name : 'RTIndexBox',
	#superclass : 'Object',
	#instVars : [
		'left',
		'top',
		'right',
		'bottom',
		'parent'
	],
	#category : 'RTree-Nodes',
	#package : 'RTree',
	#tag : 'Nodes'
}

{ #category : 'accessing' }
RTIndexBox >> area [
	^ (right - left) * (bottom - top)
]

{ #category : 'converting' }
RTIndexBox >> asRectangle [
	^ (left @ top) corner: (right @ bottom)
]

{ #category : 'accessing' }
RTIndexBox >> bottom [
	^ bottom
]

{ #category : 'testing' }
RTIndexBox >> containsBox: aBox [
	^ left <= aBox left and: [ top <= aBox top and: [ aBox right <= right and: [ aBox bottom <= bottom ] ] ]
]

{ #category : 'testing' }
RTIndexBox >> containsRectangle: aRectangle [
	| origin corner |
	origin := aRectangle origin.
	corner := aRectangle corner.
	^ left <= origin x and: [ top <= origin y and: [ corner x <= right and: [ corner y <= bottom ] ] ]
]

{ #category : 'testing' }
RTIndexBox >> containsX: x y: y [
	"borders included"
	^ left <= x and: [ x <= right and: [ top <= y and: [ y <= bottom ] ] ]
]

{ #category : 'accessing' }
RTIndexBox >> doubleCenterX [
	"twice the x of the center, enough to sort"
	^ left + right
]

{ #category : 'accessing' }
RTIndexBox >> doubleCenterY [
	^ top + bottom
]

{ #category : 'testing' }
RTIndexBox >> isEmptyBox [
	"setEmpty and nothing merged since"
	^ right < left
]

{ #category : 'accessing' }
RTIndexBox >> left [
	^ left
]

{ #category : 'accessing' }
RTIndexBox >> margin [
	^ (right - left) + (bottom - top)
]

{ #category : 'accessing' }
RTIndexBox >> maxExtent [
	^ (right - left) max: (bottom - top)
]

{ #category : 'operations' }
RTIndexBox >> mergeBox: aBox [
	left := left min: aBox left.
	top := top min: aBox top.
	right := right max: aBox right.
	bottom := bottom max: aBox bottom
]

{ #category : 'operations' }
RTIndexBox >> overlapWith: aBox [
	| width height |
	width := (right min: aBox right) - (left max: aBox left).
	width <= 0 ifTrue: [ ^ 0 ].
	height := (bottom min: aBox bottom) - (top max: aBox top).
	height <= 0 ifTrue: [ ^ 0 ].
	^ width * height
]

{ #category : 'accessing' }
RTIndexBox >> parent [
	^ parent
]

{ #category : 'accessing' }
RTIndexBox >> parent: aNode [
	parent := aNode
]

{ #category : 'accessing' }
RTIndexBox >> right [
	^ right
]

{ #category : 'initialization' }
RTIndexBox >> setEmpty [
	left := top := Float infinity.
	right := bottom := Float negativeInfinity
]

{ #category : 'initialization' }
RTIndexBox >> setRectangle: aRectangle [
	| origin corner |
	origin := aRectangle origin.
	corner := aRectangle corner.
	left := origin x.
	top := origin y.
	right := corner x.
	bottom := corner y
]

{ #category : 'accessing' }
RTIndexBox >> top [
	^ top
]

{ #category : 'testing' }
RTIndexBox >> touchesLeft: aLeft top: aTop right: aRight bottom: aBottom [
	"the closed rectangles meet"
	^ left <= aRight and: [ aLeft <= right and: [ top <= aBottom and: [ aTop <= bottom ] ] ]
]
