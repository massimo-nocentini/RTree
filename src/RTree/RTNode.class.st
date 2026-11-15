"
RTree node
"
Class {
	#name : 'RTNode',
	#superclass : 'RTAbstractNode',
	#instVars : [
		'contents',
		'left',
		'right',
		'rectangle',
		'height',
		'parent'
	],
	#category : 'RTree-Nodes',
	#package : 'RTree',
	#tag : 'Nodes'
}

{ #category : 'instance creation' }
RTNode class >> fromEntries: anArray from: start to: stop [
	"a balanced tree of the entries from start to stop, the halves differ by at most one entry"
	| middle |
	start = stop ifTrue: [ ^ self new: (anArray at: start) ].
	middle := start + stop // 2.
	^ self new
		left: (self fromEntries: anArray from: start to: middle);
		right: (self fromEntries: anArray from: middle + 1 to: stop);
		computeRectangle;
		yourself
]

{ #category : 'instance creation' }
RTNode class >> new: anRTEntry rectangle: aRectangle [
	"a leaf of anRTEntry, stored with aRectangle"
	^ self basicNew
		fromEntry: anRTEntry rectangle: aRectangle;
		yourself
]

{ #category : 'instance creation' }
RTNode class >> new: anRTEntry [
	^ self basicNew
		fromEntry: anRTEntry;
		yourself
]

{ #category : 'visiting' }
RTNode >> accept: visitor [
	visitor visitNode: self
]

{ #category : 'private' }
RTNode >> add: anRTEntry path: list [
	"adds the entry but it loose the balance"
	self isLeaf ifTrue: [ | newLeaf |
		"create the new leaf first: if anRTEntry fails, the node is unchanged"
		newLeaf := self class new: anRTEntry.
		"the previous entry keeps the rectangle the tree knows: when its update is pending, the
		ancestors contain that rectangle, not its new one"
		self left: (self class new: self contents rectangle: rectangle).
		self right: newLeaf.
		height := 2.
		contents := nil.
		rectangle := left rectangle merge: right rectangle
	]ifFalse: [ | leastEnlargementChild |
		leastEnlargementChild := self leastEnlargementChild: anRTEntry.
		list add: (right == leastEnlargementChild) -> leastEnlargementChild.
		leastEnlargementChild add: anRTEntry path: list.
		height := (left height max: right height) + 1.
		"the child grew by the rectangle of the entry. quickMerge: answers the receiver
		when it contains it already, so most levels create no rectangle"
		rectangle := rectangle quickMerge: anRTEntry encompassingRectangle
	]
]

{ #category : 'adding' }
RTNode >> addChild: anRTEntry [
	| path |
	path := OrderedCollection with: self.
	self add: anRTEntry path: path.
	self ensureBalancePath: path.
	^ self
]

{ #category : 'private' }
RTNode >> balanceZ: z y: y x: x [
	| a b c |
	c := z value.
	b := y value.
	a := x value.
	(y key and: [ x key ]) ifTrue: [
		^ self rrrotationZ: c y: b x: a ].
	(y key not and: [ x key not ]) ifTrue: [
		^ self llrotationZ: c y: b x: a ].
	(y key not and: [ x key ]) ifTrue: [
		^ self lrrotationZ: c y: b x: a ].
	^ self rlrotationZ: c y: b x: a
]

{ #category : 'accessing' }
RTNode >> children [
	^ self isLeaf
		ifTrue: [ #() ]
		ifFalse: [ { left. right } ]
]

{ #category : 'enumerating' }
RTNode >> childrenDo: aBlock [
	self isLeaf ifTrue: [ ^ self ].
	aBlock value: left.
	aBlock value: right
]

{ #category : 'enumerating' }
RTNode >> collect: aBlock [
	| list |
	list := OrderedCollection new.
	self do: [ :each | list add: (aBlock value: each) ].
	^ list
]

{ #category : 'public' }
RTNode >> computeHeight [
	"do not use it"
	height := self isLeaf
		ifTrue: [ 1 ]
		ifFalse: [ (left computeHeight max: right computeHeight) + 1 ].
	^ height
]

{ #category : 'public' }
RTNode >> areaOf: aRectangle mergedWith: anotherRectangle [
	"the area of aRectangle merge: anotherRectangle, without creating it"
	^ ((aRectangle corner x max: anotherRectangle corner x) - (aRectangle origin x min: anotherRectangle origin x))
		* ((aRectangle corner y max: anotherRectangle corner y) - (aRectangle origin y min: anotherRectangle origin y))
]

{ #category : 'public' }
RTNode >> computeRectangle [
	"the union of the rectangles of the children. The Rectangle is kept when it does not change:
	a new one stored in an old node survives the next scavenge and makes it longer"
	| leftRectangle rightRectangle originX originY cornerX cornerY |
	leftRectangle := left rectangle.
	rightRectangle := right rectangle.
	originX := leftRectangle origin x min: rightRectangle origin x.
	originY := leftRectangle origin y min: rightRectangle origin y.
	cornerX := leftRectangle corner x max: rightRectangle corner x.
	cornerY := leftRectangle corner y max: rightRectangle corner y.
	(rectangle notNil and: [
		rectangle origin x = originX and: [ rectangle origin y = originY and: [
		rectangle corner x = cornerX and: [ rectangle corner y = cornerY ] ] ] ])
			ifFalse: [ rectangle := (originX @ originY) corner: (cornerX @ cornerY) ].
	height := (left height max: right height) + 1
]

{ #category : 'accessing' }
RTNode >> contents [
	^ contents
]

{ #category : 'accessing' }
RTNode >> contents: aRSShape [
	contents := aRSShape
]

{ #category : 'enumerating' }
RTNode >> do: aBlock [
	self isLeaf
		ifTrue: [ aBlock value: self contents ]
		ifFalse: [
			self childrenDo: [ :child | child do: aBlock ].
			 ]
]

{ #category : 'finding/searching' }
RTNode >> entriesWithPoint: aPoint do: aBlock [
	"evaluates aBlock with every entry whose rectangle holds aPoint. The rectangle is closed,
	the entry decides about its border, see nodesWithPoint:list:"
	| x y origin corner |
	x := aPoint x.
	y := aPoint y.
	origin := rectangle origin.
	corner := rectangle corner.
	(origin x <= x and: [ x <= corner x and: [ origin y <= y and: [ y <= corner y ] ] ])
		ifFalse: [ ^ self ].
	left ifNil: [ ^ aBlock value: contents ].
	left entriesWithPoint: aPoint do: aBlock.
	right entriesWithPoint: aPoint do: aBlock
]

{ #category : 'finding/searching' }
RTNode >> entriesInside: aRectangle list: aCollection [
	"adds the entries whose rectangle is inside aRectangle, borders included"
	| origin corner queryOrigin queryCorner |
	origin := rectangle origin.
	corner := rectangle corner.
	queryOrigin := aRectangle origin.
	queryCorner := aRectangle corner.
	"no entry below is inside when the closed rectangles do not meet"
	(origin x <= queryCorner x and: [ queryOrigin x <= corner x and: [
		origin y <= queryCorner y and: [ queryOrigin y <= corner y ] ] ])
			ifFalse: [ ^ self ].
	"every entry below is inside, a leaf included"
	(queryOrigin x <= origin x and: [ queryOrigin y <= origin y and: [
		corner x <= queryCorner x and: [ corner y <= queryCorner y ] ] ])
			ifTrue: [ ^ self do: [ :each | aCollection add: each ] ].
	left ifNil: [ ^ self ].
	left entriesInside: aRectangle list: aCollection.
	right entriesInside: aRectangle list: aCollection
]

{ #category : 'private' }
RTNode >> ensureBalancePath: aCollection [
	| recomputeHeight |
	"ensure the balance of the tree"
	aCollection size < 3 ifTrue: [ ^ self ].
	recomputeHeight := false.
	(1 to: aCollection size - 2) reverseDo: [ :index |
		| assoc |
		assoc := aCollection at: index.
		recomputeHeight ifTrue: [
			assoc value height: (assoc value left height max: assoc value right height)+1
		] ifFalse: [
			(assoc value isBalanced) ifFalse: [ | z y x |
				z := aCollection at: index.
				y := aCollection at: index + 1.
				x := aCollection at: index + 2.
				recomputeHeight := true.
				self balanceZ: z y: y x: x.
			]
		]
	]
]

{ #category : 'private' }
RTNode >> fromEntry: anRTEntry [
	self fromEntry: anRTEntry rectangle: anRTEntry encompassingRectangle
]

{ #category : 'private' }
RTNode >> fromEntry: anRTEntry rectangle: aRectangle [
	contents := anRTEntry.
	height := 1.
	rectangle := aRectangle
]

{ #category : 'initialization' }
RTNode >> fromNode: aNode [
	contents := aNode contents.
	left := aNode left.
	right := aNode right.
	rectangle := aNode rectangle.
	height := aNode height.
	left ifNotNil: [ left parent: self ].
	right ifNotNil: [ right parent: self ]
]

{ #category : 'accessing' }
RTNode >> height [
	^ height
]

{ #category : 'accessing' }
RTNode >> height: anInteger [
	height := anInteger
]

{ #category : 'private' }
RTNode >> indexLeavesIn: aDictionary [
	left ifNil: [ ^ aDictionary at: contents put: self ].
	left parent: self.
	right parent: self.
	left indexLeavesIn: aDictionary.
	right indexLeavesIn: aDictionary
]

{ #category : 'inspector' }
RTNode >> inspectionTree: aBuilder [
    <inspectorPresentationOrder: 1 title: 'Tree Structure'>

    ^ aBuilder newTree
        roots: { self };
        children: [ :each | each children ];
        expandRoots;
        yourself
]

{ #category : 'testing' }
RTNode >> isBalanced [
	^ self isLeaf or: [ (left height - right height) abs <= 1 ]
]

{ #category : 'testing' }
RTNode >> isEmpty [
	^ false
]

{ #category : 'testing' }
RTNode >> isLeaf [
	^ right isNil and: [ left isNil ]
]

{ #category : 'testing' }
RTNode >> isTotalBalanced [
	"do not use it, only for debugging"
	^ self isBalanced
		and: [ (left isNil or: [ left isTotalBalanced ])
			and: [ right isNil or: [ right isTotalBalanced ] ] ]
]

{ #category : 'private' }
RTNode >> leastEnlargementChild: anRTEntry [
	| rect leftDiff rightDiff area1 area2 |
	"TODO you can enhance the logic of this method.
	This is called at every level of an insertion: the areas are computed without creating rectangles"
	rect := anRTEntry encompassingRectangle.
	area1 := left rectangle area.
	area2 := right rectangle area.
	leftDiff := (self areaOf: left rectangle mergedWith: rect) - area1.
	rightDiff := (self areaOf: right rectangle mergedWith: rect) - area2.
	^ rightDiff = leftDiff
		ifTrue: [ area1 < area2
				ifTrue: [ left ]
				ifFalse: [ right ] ]
		ifFalse: [
			leftDiff < rightDiff
				ifTrue: [ left ]
				ifFalse: [ right ] ]
]

{ #category : 'accessing' }
RTNode >> left [
	^ left
]

{ #category : 'accessing' }
RTNode >> left: aRSRNode [
	left := aRSRNode.
	aRSRNode ifNotNil: [ aRSRNode parent: self ]
]

{ #category : 'private' }
RTNode >> llrotationZ: z y: y x: x [
	"y, which the rotation leaves out, becomes the new right child of z"
	| a3 a4 |
	a3 := y right.
	a4 := z right.
	y left: a3; right: a4; computeRectangle.
	z left: x; right: y; computeRectangle
]

{ #category : 'private' }
RTNode >> lrrotationZ: z y: y x: x [
	"x, which the rotation leaves out, becomes the new left child of y"
	| a1 a2 a3 |
	a1 := y left.
	a2 := x left.
	a3 := x right.
	x left: a1; right: a2; computeRectangle.
	y left: x; right: a3; computeRectangle.

	self llrotationZ: z y: y x: x
]

{ #category : 'finding/searching' }
RTNode >> nodesIntersetcsRectangle: aRectangle list: aCollection [
	| origin corner queryOrigin queryCorner |
	(rectangle intersects: aRectangle) ifFalse: [ ^ self ].
	left ifNil: [ ^ aCollection add: contents ].
	"a node strictly inside aRectangle: every entry below intersects it, no need to test them.
	Zoom to fit asks for the whole tree"
	origin := rectangle origin.
	corner := rectangle corner.
	queryOrigin := aRectangle origin.
	queryCorner := aRectangle corner.
	(queryOrigin x < origin x and: [ queryOrigin y < origin y and: [
		corner x < queryCorner x and: [ corner y < queryCorner y ] ] ])
			ifTrue: [ ^ self do: [ :each | aCollection add: each ] ].
	left nodesIntersetcsRectangle: aRectangle list: aCollection.
	right nodesIntersetcsRectangle: aRectangle list: aCollection
]

{ #category : 'finding/searching' }
RTNode >> nodesWithPoint: aPoint list: aCollection [
	"The rectangle is closed here (Rectangle>>containsPoint: is not): the entry decides
	about its own border in addEntriesIn:position:, a line accepts its end points for example.
	The coordinates are compared directly, this is the inner loop of the hit test"
	| x y origin corner |
	x := aPoint x.
	y := aPoint y.
	origin := rectangle origin.
	corner := rectangle corner.
	(origin x <= x and: [ x <= corner x and: [ origin y <= y and: [ y <= corner y ] ] ])
		ifFalse: [ ^ self ].
	left ifNil: [ ^ contents addEntriesIn: aCollection position: aPoint ].
	left nodesWithPoint: aPoint list: aCollection.
	right nodesWithPoint: aPoint list: aCollection
]

{ #category : 'accessing' }
RTNode >> parent [
	^ parent
]

{ #category : 'accessing' }
RTNode >> parent: aNode [
	parent := aNode
]

{ #category : 'copying' }
RTNode >> postCopy [
	super postCopy.
	left ifNotNil: [ self left: left copy ].
	right ifNotNil: [ self right: right copy ]
]

{ #category : 'accessing' }
RTNode >> rectangle [
	^ rectangle
]

{ #category : 'accessing' }
RTNode >> rectangle: aRectangle [
	rectangle := aRectangle
]

{ #category : 'accessing' }
RTNode >> right [
	^ right
]

{ #category : 'accessing' }
RTNode >> right: aRSRNode [
	right := aRSRNode.
	aRSRNode ifNotNil: [ aRSRNode parent: self ]
]

{ #category : 'private' }
RTNode >> rlrotationZ: z y: y x: x [
	"x, which the rotation leaves out, becomes the new right child of y"
	| a2 a3 a4 |
	a2 := x left.
	a3 := x right.
	a4 := y right.
	x left: a3; right: a4; computeRectangle.
	y left: a2; right: x; computeRectangle.
	self rrrotationZ: z y: y x: x
]

{ #category : 'private' }
RTNode >> rrrotationZ: z y: y x: x [
	"right right rotation: y, which the rotation leaves out, becomes the new left child of z"
	| a1 a2 |
	a1 := z left.
	a2 := y left.
	y left: a1; right: a2; computeRectangle.
	z left: y; right: x; computeRectangle
]

{ #category : 'finding/searching' }
RTNode >> searchPath: anEntry [
	| path |
	path := OrderedCollection new.
	self searchPath: anEntry rectangle: anEntry encompassingRectangle in: path dir: nil.
	^ path
]

{ #category : 'finding/searching' }
RTNode >> searchPath: anRTEntry rectangle: entryRectangle in: path dir: aBoolean [
	"a nil entryRectangle visits every node"
	(entryRectangle isNil or: [ self rectangle containsRect: entryRectangle ])
		ifFalse: [ ^ self ].
	self isLeaf ifTrue: [
		contents == anRTEntry ifTrue: [
			path addFirst: aBoolean -> self
		] ifFalse: [  ]
	] ifFalse: [
		left searchPath: anRTEntry rectangle: entryRectangle in: path dir: false.
		path ifNotEmpty: [ path addFirst: aBoolean -> self. ^ self ].
		right searchPath: anRTEntry rectangle: entryRectangle in: path dir: true.
		path ifNotEmpty: [ path addFirst: aBoolean -> self. ].
	 ]
]

{ #category : 'finding/searching' }
RTNode >> searchPathIgnoringBounds: anEntry [
	"same as searchPath: but it does not use the rectangle of anEntry, O(n)"
	| path |
	path := OrderedCollection new.
	self searchPath: anEntry rectangle: nil in: path dir: nil.
	^ path
]

{ #category : 'accessing - children' }
RTNode >> withAllChildren [
	| children |
	children := OrderedCollection new.
	self withAllChildrenDo: [ :node | children add: node ].
	^ children
]

{ #category : 'enumerating' }
RTNode >> withAllChildrenDo: aBlock [
	aBlock value: self.
	self childrenDo: [ :child | child withAllChildrenDo: aBlock ]
]
