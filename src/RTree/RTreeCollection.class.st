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

{ #category : 'adding' }
RTreeCollection >> bulkLoad: aCollectionOfRTEntry [
	"RSCanvas>>shapeCollection: (useRTree) gives the existing shapes here. An empty tree is
	built at once from the entries in Sort-Tile-Recursive order, halved recursively:
	a balanced tree of nearby entries, in O(n log n) without any insertion"
	| seen entries |
	self isEmpty ifFalse: [ ^ super bulkLoad: aCollectionOfRTEntry ].
	seen := IdentitySet new.
	entries := OrderedCollection new: aCollectionOfRTEntry size.
	aCollectionOfRTEntry do: [ :each |
		(seen includes: each) ifFalse: [
			seen add: each.
			(self isFiniteRectangle: each encompassingRectangle)
				ifTrue: [ entries add: each ]
				ifFalse: [ self outliers add: each ] ] ].
	entries ifEmpty: [ ^ self ].
	root := RTNode fromEntries: (self sortTileRecursive: entries) from: 1 to: entries size.
	self rebuildLeaves
]

{ #category : 'private - adding' }
RTreeCollection >> sortTileRecursive: aCollection [
	"the entries sorted by the x of their center into about sqrt(n) vertical slices, each slice sorted by y"
	| items sliceSize sorted index |
	items := (aCollection collect: [ :each | | r |
		r := each encompassingRectangle.
		Array with: r origin x + r corner x with: r origin y + r corner y with: each ]) asArray.
	items sort: [ :a :b | a first <= b first ].
	sliceSize := (items size / items size sqrt ceiling) ceiling.
	sorted := Array new: items size.
	index := 0.
	1 to: items size by: sliceSize do: [ :start | | slice |
		slice := items copyFrom: start to: (start + sliceSize - 1 min: items size).
		slice sort: [ :a :b | a second <= b second ].
		slice do: [ :each | sorted at: (index := index + 1) put: each third ] ].
	^ sorted
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
	"very important to preserv the drawing order: the topmost entry comes first.
	Every entry whose rectangle holds aPoint adds its own hits (a composite adds its children
	first). Only the entries that added something are then ordered, by entryIndex: this is the
	order of the indexesFromRoot of the hits (see sortResultList:), without computing them"
	| res groups addHits |
	res := OrderedCollection new.
	groups := OrderedCollection new.
	addHits := [ :each | | start |
		start := res size.
		each addEntriesIn: res position: aPoint.
		res size > start ifTrue: [ groups add: each -> (start + 1 to: res size) ] ].
	root entriesWithPoint: aPoint do: addHits.
	outliers ifNotNil: [ outliers do: addHits ].
	groups size < 2 ifTrue: [ ^ res ].
	groups sort: [ :a :b | (a key entryIndex ifNil: [ 0 ]) >= (b key entryIndex ifNil: [ 0 ]) ].
	^ groups
		inject: (OrderedCollection new: res size)
		into: [ :sorted :group |
			group value do: [ :index | sorted add: (res at: index) ].
			sorted ]
]

{ #category : 'finding/searching' }
RTreeCollection >> entriesAtRectangle: aRectangle [
	| res |
	res := OrderedCollection new.
	root nodesIntersetcsRectangle: aRectangle list: res.
	outliers ifNotNil: [
		outliers do: [ :each |
			(each encompassingRectangle intersects: aRectangle) ifTrue: [ res add: each ] ] ].
	^ self sortByEntryIndex: res
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
	| index leaf |
	outliers ifNotNil: [
		index := outliers identityIndexOf: oldRTEntry.
		index > 0 ifTrue: [ ^ outliers removeAt: index ] ].
	leaf := self leaves removeKey: oldRTEntry ifAbsent: [ ^ anExceptionBlock value ].
	"walk up from the leaf: neither a search nor the rectangle of the entry is needed"
	^ self removeEntry: oldRTEntry path: (self pathTo: leaf) ifAbsent: anExceptionBlock
]

{ #category : 'private - removing' }
RTreeCollection >> removeEntry: oldRTEntry path: aPath ifAbsent: anExceptionBlock [
	"remove the leaf at the end of aPath (see pathTo:), already taken out of the leaves"
	| path |
	path := aPath.
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

{ #category : 'private - finding' }
RTreeCollection >> sortByEntryIndex: aCollection [
	"The drawing order. A container numbers its entries 1..n, so a large result is placed in an
	Array indexed by entryIndex, O(n), instead of being sorted with a block, O(n log n).
	Small results, sparse or repeated indexes and entries without entryIndex are sorted"
	| min max buckets result |
	aCollection size < 256 ifTrue: [ ^ self sortWithBlock: aCollection ].
	min := SmallInteger maxVal.
	max := SmallInteger minVal.
	aCollection do: [ :each | | index |
		index := each entryIndex.
		index isInteger ifFalse: [ ^ self sortWithBlock: aCollection ].
		index < min ifTrue: [ min := index ].
		index > max ifTrue: [ max := index ] ].
	max - min >= (aCollection size * 4) ifTrue: [ ^ self sortWithBlock: aCollection ].
	buckets := Array new: max - min + 1.
	aCollection do: [ :each | | slot |
		slot := each entryIndex - min + 1.
		(buckets at: slot) ifNotNil: [ ^ self sortWithBlock: aCollection ].
		buckets at: slot put: each ].
	result := OrderedCollection new: aCollection size.
	buckets do: [ :each | each ifNotNil: [ result add: each ] ].
	^ result
]

{ #category : 'private - finding' }
RTreeCollection >> sortWithBlock: aCollection [
	"entryIndex is nil for an entry that no container numbered"
	^ aCollection sort: [ :a :b | (a entryIndex ifNil: [ 0 ]) <= (b entryIndex ifNil: [ 0 ]) ]
]

{ #category : 'update' }
RTreeCollection >> updateEntry: anRTEntry [
	"The rectangle of the entry changed. When the new rectangle stays inside the parent or the
	grandparent of its leaf, as for most moves of a drag or an animation, the leaf is updated in
	place and its ancestors are recomputed upwards. Otherwise the entry is removed and added again"
	| leaf path rectangle |
	leaf := self leaves at: anRTEntry ifAbsent: [ nil ].
	anRTEntry resetEncompassingRectangle.
	leaf ifNil: [
		self remove: anRTEntry.
		^ self add: anRTEntry ].
	rectangle := anRTEntry encompassingRectangle.
	path := self pathTo: leaf.
	((self isFiniteRectangle: rectangle) and: [ self canUpdateIn: path rectangle: rectangle ])
		ifFalse: [
			"the path is known already: remove the leaf without walking up again"
			self leaves removeKey: anRTEntry.
			self removeEntry: anRTEntry path: path ifAbsent: [ self errorNotFound: anRTEntry ].
			^ self add: anRTEntry ].
	leaf rectangle: rectangle.
	(path size - 1 to: 1 by: -1) do: [ :index | | node old |
		node := (path at: index) value.
		old := node rectangle.
		node computeRectangle.
		"the ancestors of an unchanged node do not change"
		node rectangle = old ifTrue: [ ^ self ] ]
]

{ #category : 'private - update' }
RTreeCollection >> canUpdateIn: path rectangle: aRectangle [
	"the parent or the grandparent of the leaf (the last of path) contains aRectangle,
	or the leaf is the root"
	path isEmpty ifTrue: [ ^ false ].
	path size = 1 ifTrue: [ ^ true ].
	^ ((path at: path size - 1) value rectangle containsRect: aRectangle)
		or: [ path size > 2 and: [ (path at: path size - 2) value rectangle containsRect: aRectangle ] ]
]

{ #category : 'update' }
RTreeCollection >> updateEntry: anRTEntry before: anotherRTEntry [
	"do not needed because there is no order in this tree"
]
