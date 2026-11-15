"
An R-tree for Roassal.

Rectangle tree for roassal is a collection that allows
- find shapes in a point
- find shapes in a rectangle
The time searching this elements should be close to log(n)

The tree is balanced, then it does not have the order for the elements. User should define an index `shapeIndex` to keed the order.

An entry is held once (adding it again does nothing). `leaves` maps each entry to its leaf, and every node knows its parent:
remove: and updateEntry: walk up from the leaf, they neither search the tree nor read the rectangle of the entry.

Use the inspector to visualize the RTree
"
Class {
	#name : 'RTreeCollection',
	#superclass : 'RTAbstractCollection',
	#instVars : [
		'root',
		'outliers',
		'leaves',
		'indexedRoot'
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
	"an entry is held once"
	(self includes: anRTEntry) ifTrue: [ ^ anRTEntry ].
	(self isFiniteRectangle: rectangle) ifFalse: [
		"a NaN or an infinite rectangle cannot be merged with the others, keep it aside"
		self outliers add: anRTEntry.
		^ anRTEntry ].
	self addToTree: anRTEntry.
	^ anRTEntry
]

{ #category : 'private - adding' }
RTreeCollection >> addToTree: anRTEntry [
	| path leaf |
	root isEmpty ifTrue: [
		self privateRoot: (RTNode new: anRTEntry).
		^ self leaves at: anRTEntry put: root ].
	path := OrderedCollection with: root.
	root add: anRTEntry path: path.
	"the last node of the path was a leaf, it now holds the previous entry on the left
	and anRTEntry on the right. The rotations below keep the leaves"
	leaf := path last value.
	self leaves
		at: leaf left contents put: leaf left;
		at: anRTEntry put: leaf right.
	root ensureBalancePath: path
]

{ #category : 'private - removing' }
RTreeCollection >> balanceRemovedPath: path [
	"AVL deletion: walk up from the removed leaf, recompute each ancestor and rotate the
	unbalanced ones with the rotations of the insertion. No entry is inserted again"
	(1 to: path size -2) reverseDo: [ :index | | tree |
		tree := (path at: index) value.
		"the removed entry may define the border of every ancestor: recompute the rectangle, not only the height"
		tree computeRectangle.
		tree isBalanced ifFalse: [ | y x |
			"y is the taller child, x the taller child of y; on a tie x is on the side of y (single rotation)"
			y := tree left height < tree right height
				ifTrue: [ true -> tree right ]
				ifFalse: [ false -> tree left ].
			x := y value left height = y value right height
				ifTrue: [ y key -> (y key ifTrue: [ y value right ] ifFalse: [ y value left ]) ]
				ifFalse: [ y value left height < y value right height
					ifTrue: [ true -> y value right ]
					ifFalse: [ false -> y value left ] ].
			tree balanceZ: nil -> tree y: y x: x ].
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
	"an entry without parent has no indexesFromRoot, its entryIndex orders it"
	res := res collect: [ :s | s -> (s indexesFromRoot ifEmpty: [ Array with: (s entryIndex ifNil: [ 0 ]) ]) ].
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
	"entryIndex is nil for an entry that no container numbered"
	res sort: [:a :b | (a entryIndex ifNil: [ 0 ]) <= (b entryIndex ifNil: [ 0 ]) ].
	^ res
]

{ #category : 'accessing' }
RTreeCollection >> height [
	^ root height
]

{ #category : 'testing' }
RTreeCollection >> includes: anObject [
	"identity, as remove:"
	^ (self leaves includesKey: anObject)
		or: [ outliers notNil and: [ outliers identityIncludes: anObject ] ]
]

{ #category : 'initialization' }
RTreeCollection >> initialize [
	super initialize.
	root := RTNilNode new.
	self rebuildLeaves
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

{ #category : 'accessing' }
RTreeCollection >> leaves [
	"entry -> leaf. It is rebuilt when the root was replaced without the collection
	knowing, by the bulk load of a subclass for example"
	(leaves isNil or: [ indexedRoot ~~ root ]) ifTrue: [ self rebuildLeaves ].
	^ leaves
]

{ #category : 'private - removing' }
RTreeCollection >> pathTo: aLeaf [
	"the path from the root to aLeaf, as RTNode>>searchPath: answers it, built from the parents.
	Empty when the parents do not lead to the root"
	| path node parent |
	path := OrderedCollection new.
	node := aLeaf.
	[ (parent := node parent) notNil ] whileTrue: [
		parent right == node
			ifTrue: [ path addFirst: true -> node ]
			ifFalse: [
				parent left == node ifFalse: [ ^ #() ].
				path addFirst: false -> node ].
		node := parent ].
	node == root ifFalse: [ ^ #() ].
	path addFirst: nil -> node.
	^ path
]

{ #category : 'copying' }
RTreeCollection >> postCopy [
	"the nodes are copied, the entries are shared"
	super postCopy.
	root := root copy.
	outliers := outliers copy.
	self rebuildLeaves
]

{ #category : 'private' }
RTreeCollection >> privateRoot: aNode [
	root := aNode.
	root parent: nil.
	indexedRoot := root
]

{ #category : 'shapes - ordering' }
RTreeCollection >> pushBack: anRTEntry [
	"no need it, but the entry should update its entryIndex"
]

{ #category : 'shapes - ordering' }
RTreeCollection >> pushFront: anRTEntry [
	"no need it, but the entry should update its entryIndex"
]

{ #category : 'private' }
RTreeCollection >> rebuildLeaves [
	"index the leaves and set the parent of every node, O(n)"
	leaves := IdentityDictionary new.
	root parent: nil.
	root indexLeavesIn: leaves.
	indexedRoot := root
]

{ #category : 'accessing' }
RTreeCollection >> rectangle [
	^ root rectangle
]

{ #category : 'removing' }
RTreeCollection >> remove: oldRTEntry ifAbsent: anExceptionBlock [
	| path index leaf |
	outliers ifNotNil: [
		index := outliers identityIndexOf: oldRTEntry.
		index > 0 ifTrue: [ ^ outliers removeAt: index ] ].
	leaf := self leaves removeKey: oldRTEntry ifAbsent: [ ^ anExceptionBlock value ].
	"walk up from the leaf: neither a search nor the rectangle of the entry is needed"
	path := self pathTo: leaf.
	path ifEmpty: [
		"the parents were not maintained by whoever built the nodes, search the entry"
		path := root searchPath: oldRTEntry.
		"the search is guided by the current rectangle of the entry. When it changed
		without the collection being told, the stored leaf is elsewhere: look everywhere"
		path ifEmpty: [ path := root searchPathIgnoringBounds: oldRTEntry ].
		path ifEmpty: [ ^ anExceptionBlock value ] ].
	path size = 1 ifTrue: [
		self privateRoot: RTNilNode new.
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
	brother isLeaf ifTrue: [ self leaves at: parent contents put: parent ].
	path size < 3 ifTrue: [ ^ self ].
	self balanceRemovedPath: path
]

{ #category : 'removing' }
RTreeCollection >> removeAll [
	"Collection>>removeAll removes while it iterates"
	root := RTNilNode new.
	outliers := nil.
	self rebuildLeaves
]

{ #category : 'accessing' }
RTreeCollection >> size [
	^ self leaves size + (outliers ifNil: [ 0 ] ifNotNil: [ outliers size ])
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
