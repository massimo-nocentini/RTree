"
An n-ary R-tree: nodes of up to 16 children (maxEntries:), at least 40 % full after a removal.
- An entry goes down to the child whose area grows the least (ties: the smaller child).
- A full node is split as in the R*-tree: on the axis whose distributions have the smallest sum of margins, into the distribution with the least overlap, then the least area.
- remove: goes to the leaf through the record of the entry (no search, and the current rectangle of the entry does not matter), then dissolves the nodes that are less than 40 % full and inserts their entries again (CondenseTree).
- updateEntry: changes the record in place while the new rectangle stays inside the parent of its leaf. Otherwise the entry is only recorded as pending, as in RTreeCollection: the next query removes and inserts it again, or packs the whole tree again when more than 1/8 of the entries moved (a layout).
- bulkLoad: of an empty tree packs the entries in Sort-Tile-Recursive order.
The boxes are kept tight: bounds is the box of the root. With 100k entries the tree has 5 levels, and its structure takes about 125 bytes (2.2 objects) per entry, against about 220 bytes (6 objects) for RTreeCollection.

Use it with `aCanvas shapeCollection: RTNaryTreeCollection new`.
"
Class {
	#name : 'RTNaryTreeCollection',
	#superclass : 'RTAbstractCollection',
	#traits : 'RTSpatialIndex',
	#classTraits : 'RTSpatialIndex classTrait',
	#instVars : [
		'root',
		'items',
		'maxEntries',
		'minEntries',
		'pending'
	],
	#category : 'RTree-Collections',
	#package : 'RTree',
	#tag : 'Collections'
}

{ #category : 'private' }
RTNaryTreeCollection >> adjustFrom: aNode [
	"split the full nodes from aNode up, and recompute the boxes"
	| node |
	node := aNode.
	[ node isNil ] whileFalse: [
		node children size > maxEntries
			ifTrue: [ self split: node ]
			ifFalse: [ node recomputeBox ].
		node := node parent ]
]

{ #category : 'accessing' }
RTNaryTreeCollection >> bounds [
	"the box of the root is tight"
	| bounds |
	self applyPendingUpdates.
	bounds := root isEmptyBox ifTrue: [ nil ] ifFalse: [ root asRectangle ].
	outliers do: [ :each | bounds := self mergeBounds: bounds with: each encompassingRectangle ].
	^ bounds
]

{ #category : 'private' }
RTNaryTreeCollection >> applyPendingUpdates [
	"The entries of pending moved, the tree keeps the box it knows for them. Called before every
	query: when more than 1/8 of the entries moved the tree is packed again, otherwise each of them
	is removed and inserted again. An entry whose rectangle is not finite now becomes an outlier"
	| entries |
	(pending isNil or: [ pending isEmpty ]) ifTrue: [ ^ self ].
	entries := pending.
	pending := nil.
	entries size * 8 > items size ifTrue: [ | all |
		all := OrderedCollection new: items size.
		items keysDo: [ :each |
			(self isFiniteRectangle: each encompassingRectangle)
				ifTrue: [ all add: each ]
				ifFalse: [ outliers add: each ] ].
		items := IdentityDictionary new: all size.
		root := RTNaryNode newLeaf: true.
		all ifNotEmpty: [ self indexEntries: all asArray ].
		^ self ].
	entries do: [ :each | | item leaf rectangle |
		item := items at: each.
		leaf := item parent.
		leaf removeChild: item.
		self condense: leaf.
		rectangle := each encompassingRectangle.
		(self isFiniteRectangle: rectangle)
			ifTrue: [
				item setRectangle: rectangle.
				self insertItem: item ]
			ifFalse: [
				items removeKey: each.
				outliers add: each ] ]
]

{ #category : 'private' }
RTNaryTreeCollection >> condense: aLeaf [
	"CondenseTree: from aLeaf up, the nodes less than 40 % full are taken out of the tree and their
	items inserted again; the boxes of the others are recomputed"
	| node orphans |
	orphans := OrderedCollection new.
	node := aLeaf.
	[ node parent isNil ] whileFalse: [ | parentNode |
		parentNode := node parent.
		node children size < minEntries
			ifTrue: [
				parentNode removeChild: node.
				node itemsDo: [ :each | orphans add: each ] ]
			ifFalse: [ node recomputeBox ].
		node := parentNode ].
	root recomputeBox.
	[ root isLeaf not and: [ root children size = 1 ] ] whileTrue: [
		root := root children first.
		root parent: nil ].
	(root isLeaf not and: [ root children isEmpty ]) ifTrue: [ root := RTNaryNode newLeaf: true ].
	orphans do: [ :each | self insertItem: each ]
]

{ #category : 'accessing' }
RTNaryTreeCollection >> height [
	"the number of levels"
	| height node |
	self applyPendingUpdates.
	height := 1.
	node := root.
	[ node isLeaf ] whileFalse: [
		height := height + 1.
		node := node children first ].
	^ height
]

{ #category : 'private - index' }
RTNaryTreeCollection >> indexEntries: anArray [
	"Sort-Tile-Recursive packing (Leutenegger et al. 1997), level by level"
	| level |
	level := anArray collect: [ :each | | item |
		item := RTIndexItem on: each rectangle: each encompassingRectangle.
		items at: each put: item.
		item ].
	level := self pack: level leaves: true.
	[ level size > 1 ] whileTrue: [ level := self pack: level leaves: false ].
	root := level first.
	root parent: nil
]

{ #category : 'private - index' }
RTNaryTreeCollection >> indexEntry: anRTEntry rectangle: aRectangle [
	| item |
	item := RTIndexItem on: anRTEntry rectangle: aRectangle.
	items at: anRTEntry put: item.
	self insertItem: item
]

{ #category : 'private - index' }
RTNaryTreeCollection >> indexIncludes: anRTEntry [
	^ items includesKey: anRTEntry
]

{ #category : 'private - index' }
RTNaryTreeCollection >> indexedEntriesAtX: x y: y do: aBlock [
	self applyPendingUpdates.
	(root containsX: x y: y) ifTrue: [ root entriesAtX: x y: y do: aBlock ]
]

{ #category : 'private - index' }
RTNaryTreeCollection >> indexedEntriesDo: aBlock [
	items keysDo: aBlock
]

{ #category : 'private - index' }
RTNaryTreeCollection >> indexedEntriesTouchingLeft: left top: top right: right bottom: bottom do: aBlock [
	self applyPendingUpdates.
	(root touchesLeft: left top: top right: right bottom: bottom)
		ifTrue: [ root entriesTouchingLeft: left top: top right: right bottom: bottom do: aBlock ]
]

{ #category : 'private - index' }
RTNaryTreeCollection >> indexedSize [
	^ items size
]

{ #category : 'private - index' }
RTNaryTreeCollection >> initializeIndex [
	maxEntries ifNil: [ self maxEntries: 16 ].
	root := RTNaryNode newLeaf: true.
	items := IdentityDictionary new.
	pending := nil
]

{ #category : 'private' }
RTNaryTreeCollection >> insertItem: anItem [
	| leaf |
	leaf := root.
	[ leaf isLeaf ] whileFalse: [ leaf := leaf bestChildFor: anItem ].
	leaf addChild: anItem.
	self adjustFrom: leaf
]

{ #category : 'private' }
RTNaryTreeCollection >> itemFor: anRTEntry [
	"the record of anRTEntry, nil when it is not indexed"
	self applyPendingUpdates.
	^ items at: anRTEntry ifAbsent: [ nil ]
]

{ #category : 'accessing' }
RTNaryTreeCollection >> maxEntries [
	^ maxEntries
]

{ #category : 'accessing' }
RTNaryTreeCollection >> maxEntries: anInteger [
	"the most children of a node, 16 by default. Set it before adding entries"
	maxEntries := anInteger.
	minEntries := anInteger * 2 // 5 max: 2
]

{ #category : 'accessing' }
RTNaryTreeCollection >> minEntries [
	^ minEntries
]

{ #category : 'private' }
RTNaryTreeCollection >> pack: boxes leaves: aBoolean [
	"one level of Sort-Tile-Recursive packing: about sqrt(n / maxEntries) vertical slices of the
	boxes sorted by the x of their center, each sorted by y and cut into nodes of maxEntries"
	| count nodeCount sliceSize sorted nodes |
	count := boxes size.
	nodeCount := (count / maxEntries) ceiling.
	sliceSize := nodeCount sqrt ceiling * maxEntries.
	sorted := boxes copy.
	sorted sort: [ :a :b | a doubleCenterX <= b doubleCenterX ].
	nodes := OrderedCollection new: nodeCount.
	1 to: count by: sliceSize do: [ :start | | slice |
		slice := sorted copyFrom: start to: (start + sliceSize - 1 min: count).
		slice sort: [ :a :b | a doubleCenterY <= b doubleCenterY ].
		1 to: slice size by: maxEntries do: [ :first | | node |
			node := RTNaryNode newLeaf: aBoolean.
			first to: (first + maxEntries - 1 min: slice size) do: [ :k | node addChild: (slice at: k) ].
			node recomputeBox.
			nodes add: node ] ].
	^ nodes asArray
]

{ #category : 'private' }
RTNaryTreeCollection >> prefixBoxes: sorted [
	"the union of the first i boxes, for every i"
	| result box |
	result := Array new: sorted size.
	box := RTIndexBox new setEmpty; yourself.
	1 to: sorted size do: [ :i |
		box := box copy.
		box mergeBox: (sorted at: i).
		result at: i put: box ].
	^ result
]

{ #category : 'private - index' }
RTNaryTreeCollection >> reindexEntry: anRTEntry rectangle: aRectangle [
	"in place while the new box stays inside the parent of the leaf: the boxes are recomputed up
	to the first one that does not change. Otherwise the entry is pending, see applyPendingUpdates"
	| item leaf node |
	(pending notNil and: [ pending includes: anRTEntry ]) ifTrue: [ ^ self ].
	item := items at: anRTEntry.
	leaf := item parent.
	(leaf parent isNil or: [ leaf parent containsRectangle: aRectangle ]) ifFalse: [
		^ (pending ifNil: [ pending := IdentitySet new ]) add: anRTEntry ].
	item setRectangle: aRectangle.
	node := leaf.
	[ node notNil and: [ node recomputeBox ] ] whileTrue: [ node := node parent ]
]

{ #category : 'accessing' }
RTNaryTreeCollection >> root [
	self applyPendingUpdates.
	^ root
]

{ #category : 'private' }
RTNaryTreeCollection >> split: aNode [
	| groups sibling parentNode |
	groups := self splitGroups: aNode children asArray.
	sibling := RTNaryNode newLeaf: aNode isLeaf.
	aNode setChildren: groups first.
	sibling setChildren: groups second.
	aNode recomputeBox.
	sibling recomputeBox.
	parentNode := aNode parent.
	parentNode
		ifNil: [
			root := RTNaryNode newLeaf: false.
			root
				addChild: aNode;
				addChild: sibling;
				recomputeBox ]
		ifNotNil: [ parentNode addChild: sibling ]
]

{ #category : 'private' }
RTNaryTreeCollection >> splitGroups: anArray [
	"The topological split of the R*-tree: the axis with the smallest sum of margins over every
	distribution of both sort orders, then the distribution with the least overlap, then the least area"
	| count bestMargin bestSorts best bestOverlap bestArea |
	count := anArray size.
	bestMargin := nil.
	#( #x #y ) do: [ :axis | | sorts margin |
		sorts := axis = #x
			ifTrue: [ {
				anArray copy sort: [ :a :b | a left < b left or: [ a left = b left and: [ a right <= b right ] ] ].
				anArray copy sort: [ :a :b | a right < b right or: [ a right = b right and: [ a left <= b left ] ] ] } ]
			ifFalse: [ {
				anArray copy sort: [ :a :b | a top < b top or: [ a top = b top and: [ a bottom <= b bottom ] ] ].
				anArray copy sort: [ :a :b | a bottom < b bottom or: [ a bottom = b bottom and: [ a top <= b top ] ] ] } ].
		margin := 0.
		sorts do: [ :sorted | | prefixes suffixes |
			prefixes := self prefixBoxes: sorted.
			suffixes := self suffixBoxes: sorted.
			minEntries to: count - minEntries do: [ :k |
				margin := margin + (prefixes at: k) margin + (suffixes at: k + 1) margin ] ].
		(bestMargin isNil or: [ margin < bestMargin ]) ifTrue: [
			bestMargin := margin.
			bestSorts := sorts ] ].
	bestOverlap := nil.
	bestSorts do: [ :sorted | | prefixes suffixes |
		prefixes := self prefixBoxes: sorted.
		suffixes := self suffixBoxes: sorted.
		minEntries to: count - minEntries do: [ :k | | overlap area |
			overlap := (prefixes at: k) overlapWith: (suffixes at: k + 1).
			area := (prefixes at: k) area + (suffixes at: k + 1) area.
			(bestOverlap isNil or: [ overlap < bestOverlap or: [ overlap = bestOverlap and: [ area < bestArea ] ] ])
				ifTrue: [
					bestOverlap := overlap.
					bestArea := area.
					best := { sorted copyFrom: 1 to: k. sorted copyFrom: k + 1 to: count } ] ] ].
	^ best
]

{ #category : 'private' }
RTNaryTreeCollection >> suffixBoxes: sorted [
	"the union of the boxes from i to the last, for every i"
	| result box |
	result := Array new: sorted size.
	box := RTIndexBox new setEmpty; yourself.
	sorted size to: 1 by: -1 do: [ :i |
		box := box copy.
		box mergeBox: (sorted at: i).
		result at: i put: box ].
	^ result
]

{ #category : 'private - index' }
RTNaryTreeCollection >> unindexEntry: anRTEntry [
	| item leaf |
	item := items removeKey: anRTEntry ifAbsent: [ ^ false ].
	pending ifNotNil: [ pending remove: anRTEntry ifAbsent: [ ] ].
	leaf := item parent.
	leaf removeChild: item.
	self condense: leaf.
	^ true
]
