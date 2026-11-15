"
An R-tree for Roassal.

Rectangle tree for roassal is a collection that allows
- find shapes in a point
- find shapes in a rectangle
The time searching this elements should be close to log(n)

The tree is balanced, then it does not have the order for the elements. User should define an index `shapeIndex` to keed the order.

An entry is held once (adding it again does nothing). `leaves` maps each entry to its leaf, and every node knows its parent:
remove: and updateEntry: walk up from the leaf, they neither search the tree nor read the rectangle of the entry.

updateEntry: changes the leaf in place when the entry stays near. Otherwise it only records the entry in `pending`: the tree keeps
its previous rectangle until the next query, which applies the pending updates first (see applyPendingUpdates). When many entries
moved, as after a layout, the whole tree is built again at once, in Hilbert order, like bulkLoad:.

Use the inspector to visualize the RTree
"
Class {
	#name : 'RTreeCollection',
	#superclass : 'RTAbstractCollection',
	#instVars : [
		'root',
		'outliers',
		'leaves',
		'indexedRoot',
		'pending'
	],
	#category : 'RTree-Collections',
	#package : 'RTree',
	#tag : 'Collections'
}

{ #category : 'visiting' }
RTreeCollection >> accept: visitor [
	self applyPendingUpdates.
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

{ #category : 'accessing' }
RTreeCollection >> bounds [
	"the rectangle of the root is the union of the entries in the tree, see RTAbstractCollection>>bounds"
	| bounds |
	self applyPendingUpdates.
	bounds := root isEmpty ifTrue: [ nil ] ifFalse: [ root rectangle ].
	outliers ifNotNil: [
		outliers do: [ :each | bounds := self mergeBounds: bounds with: each encompassingRectangle ] ].
	^ bounds
]

{ #category : 'adding' }
RTreeCollection >> bulkLoad: aCollectionOfRTEntry [
	"RSCanvas>>shapeCollection: (useRTree) gives the existing shapes here. An empty tree is
	built at once from the entries in the order of a Hilbert curve, halved recursively:
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
	self buildTreeFrom: entries
]

{ #category : 'private - adding' }
RTreeCollection >> buildTreeFrom: aCollectionOfRTEntry [
	"a balanced tree of the entries, whose rectangles are finite, in Hilbert order"
	root := RTNode fromEntries: (self hilbertOrder: aCollectionOfRTEntry) from: 1 to: aCollectionOfRTEntry size.
	self rebuildLeaves
]

{ #category : 'private - adding' }
RTreeCollection >> hilbertOrder: aCollection [
	"The entries sorted by the Hilbert index of their center, on a curve over the rectangle of
	the centers: the halves of the sequence, then their halves, are compact groups of nearby
	entries, close to squares. The order of the curve gives about 16 cells per entry (at most
	order 16). Each index is packed with the position of its entry in one integer, sorted by a
	radix sort: three Arrays, as few as the large ones of a sort by blocks"
	| entries count minX minY maxX maxY width height order last positionBits mask codes spare |
	entries := aCollection asArray.
	count := entries size.
	minX := minY := Float infinity.
	maxX := maxY := Float negativeInfinity.
	entries do: [ :each | | rectangle x y |
		rectangle := each encompassingRectangle.
		x := rectangle origin x * 0.5 + (rectangle corner x * 0.5).
		y := rectangle origin y * 0.5 + (rectangle corner y * 0.5).
		minX := minX min: x.
		minY := minY min: y.
		maxX := maxX max: x.
		maxY := maxY max: y ].
	width := maxX - minX.
	height := maxY - minY.
	"centers spread over more than the largest Float"
	(self isFiniteRectangle: (0 @ 0 corner: width @ height)) ifFalse: [ ^ self sortTileRecursive: entries ].
	width = 0 ifTrue: [ width := 1 ].
	height = 0 ifTrue: [ height := 1 ].
	order := (count highBit + 1) // 2 + 2 min: 16.
	last := (1 bitShift: order) - 1.
	positionBits := count highBit.
	mask := (1 bitShift: positionBits) - 1.
	codes := Array new: count.
	entries doWithIndex: [ :each :i | | rectangle |
		rectangle := each encompassingRectangle.
		codes at: i put: (((self
			hilbertX: (rectangle origin x * 0.5 + (rectangle corner x * 0.5) - minX / width * last) floor
			y: (rectangle origin y * 0.5 + (rectangle corner y * 0.5) - minY / height * last) floor
			order: order)
				bitShift: positionBits) bitOr: i - 1) ].
	spare := Array new: count.
	"a stable least significant digit radix sort on the 2 * order bits of the index, 11 bits per pass"
	(0 to: 2 * order - 1 by: 11) do: [ :shift | | counts swap digitShift |
		digitShift := (positionBits + shift) negated.
		counts := Array new: 2049 withAll: 0.
		codes do: [ :code | | digit |
			digit := ((code bitShift: digitShift) bitAnd: 2047) + 2.
			counts at: digit put: (counts at: digit) + 1 ].
		2 to: 2049 do: [ :i | counts at: i put: (counts at: i) + (counts at: i - 1) ].
		codes do: [ :code | | digit position |
			digit := ((code bitShift: digitShift) bitAnd: 2047) + 1.
			position := (counts at: digit) + 1.
			counts at: digit put: position.
			spare at: position put: code ].
		swap := codes.
		codes := spare.
		spare := swap ].
	1 to: count do: [ :i | spare at: i put: (entries at: ((codes at: i) bitAnd: mask) + 1) ].
	^ spare
]

{ #category : 'private - adding' }
RTreeCollection >> hilbertX: xIn y: yIn order: anInteger [
	"the index of (x, y), two integers from 0 to 2^anInteger - 1, on the Hilbert curve of that order"
	| x y last index side rx ry swap |
	x := xIn.
	y := yIn.
	last := (1 bitShift: anInteger) - 1.
	index := 0.
	side := 1 bitShift: anInteger - 1.
	[ side > 0 ] whileTrue: [
		rx := (x bitAnd: side) > 0 ifTrue: [ 1 ] ifFalse: [ 0 ].
		ry := (y bitAnd: side) > 0 ifTrue: [ 1 ] ifFalse: [ 0 ].
		index := index + (side * side * ((3 * rx) bitXor: ry)).
		ry = 0 ifTrue: [
			rx = 1 ifTrue: [
				x := last - x.
				y := last - y ].
			swap := x.
			x := y.
			y := swap ].
		side := side bitShift: -1 ].
	^ index
]

{ #category : 'private - adding' }
RTreeCollection >> sortTileRecursive: aCollection [
	"the entries sorted by the x of their center into about sqrt(n) vertical slices, each slice
	sorted by y. Used by hilbertOrder: when the centers are too far apart for a Hilbert curve"
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

{ #category : 'private - update' }
RTreeCollection >> applyPendingUpdates [
	"The entries in pending moved without the tree knowing their new rectangle: it holds them
	with their previous one, and every node contains them. Called before every query.
	When more than 1/8 of the entries moved (a layout moves all of them), the tree is built again
	at once in Hilbert order, which also makes it tight and balanced. Otherwise each
	entry is updated in place or removed and added again"
	| entries |
	(pending isNil or: [ pending isEmpty ]) ifTrue: [ ^ self ].
	entries := pending.
	pending := nil.
	entries size * 8 > self leaves size
		ifTrue: [ self rebuildTree ]
		ifFalse: [ entries do: [ :each | self updateTreeEntry: each ] ]
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
	"very important to preserv the drawing order: the topmost entry comes first,
	see hitsAtPoint:candidates:"
	self applyPendingUpdates.
	^ self hitsAtPoint: aPoint candidates: [ :addHits |
		root entriesWithPoint: aPoint do: addHits.
		outliers ifNotNil: [ outliers do: addHits ] ]
]

{ #category : 'finding/searching' }
RTreeCollection >> entriesInside: aRectangle [
	| result |
	self applyPendingUpdates.
	result := OrderedCollection new.
	root entriesInside: aRectangle list: result.
	outliers ifNotNil: [
		outliers do: [ :each |
			(aRectangle containsRect: each encompassingRectangle) ifTrue: [ result add: each ] ] ].
	^ self sortByEntryIndex: result
]

{ #category : 'finding/searching' }
RTreeCollection >> entriesNear: aPoint within: aDistance [
	"see RTAbstractCollection>>entriesNear:within:"
	| result |
	result := OrderedCollection new.
	self nearestEntriesTo: aPoint within: aDistance do: [ :each | result add: each ].
	^ result
]

{ #category : 'finding/searching' }
RTreeCollection >> entryAtPoint: aPoint satisfying: aBlock ifNone: noneBlock [
	"Only the entries whose rectangle holds aPoint are collected, without asking for their hits.
	They are then tried from the topmost, see firstOf:atPoint:satisfying:ifNone:"
	| candidates |
	self applyPendingUpdates.
	candidates := OrderedCollection new.
	root entriesWithPoint: aPoint do: [ :each | candidates add: each ].
	outliers ifNotNil: [ candidates addAll: outliers ].
	^ self firstOf: candidates atPoint: aPoint satisfying: aBlock ifNone: noneBlock
]

{ #category : 'finding/searching' }
RTreeCollection >> entriesAtRectangle: aRectangle [
	| res |
	self applyPendingUpdates.
	res := OrderedCollection new.
	root nodesIntersetcsRectangle: aRectangle list: res.
	outliers ifNotNil: [
		outliers do: [ :each |
			(each encompassingRectangle intersects: aRectangle) ifTrue: [ res add: each ] ] ].
	^ self sortByEntryIndex: res
]

{ #category : 'accessing' }
RTreeCollection >> height [
	self applyPendingUpdates.
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
	self applyPendingUpdates.
	^ root isBalanced
]

{ #category : 'testing' }
RTreeCollection >> isEmpty [
	^ root isEmpty and: [ outliers isNil or: [ outliers isEmpty ] ]
]

{ #category : 'testing' }
RTreeCollection >> isTotalBalanced [
	self applyPendingUpdates.
	^ root isTotalBalanced
]

{ #category : 'private - finding' }
RTreeCollection >> nearItem: anArray before: anotherArray [
	"the order of the heap of nearestEntriesTo:within:do:, items are { squared distance. node. entry }"
	| distance otherDistance |
	distance := anArray first.
	otherDistance := anotherArray first.
	distance < otherDistance ifTrue: [ ^ true ].
	otherDistance < distance ifTrue: [ ^ false ].
	(anArray at: 2) ifNotNil: [ ^ true ].
	(anotherArray at: 2) ifNotNil: [ ^ false ].
	^ ((anArray at: 3) entryIndex ifNil: [ 0 ]) >= ((anotherArray at: 3) entryIndex ifNil: [ 0 ])
]

{ #category : 'finding/searching' }
RTreeCollection >> nearestEntriesTo: aPoint within: aDistance do: aBlock [
	"Best first: a heap holds the nodes and the entries met so far, by their squared distance to
	aPoint, and the nearest is expanded first. The nodes farther than aDistance are pruned.
	At the same distance a node comes before the entries: when the first entry at a distance is
	taken, every entry at that distance is in the heap already, and they come by decreasing
	entryIndex"
	| limit heap push |
	aDistance < 0 ifTrue: [ ^ self ].
	self applyPendingUpdates.
	limit := aDistance * aDistance.
	heap := Heap sortBlock: [ :a :b | self nearItem: a before: b ].
	push := [ :node | | distance |
		distance := self squaredDistanceFrom: aPoint to: node rectangle.
		distance <= limit ifTrue: [
			node isLeaf
				ifTrue: [ heap add: (Array with: distance with: nil with: node contents) ]
				ifFalse: [ heap add: (Array with: distance with: node with: nil) ] ] ].
	root isEmpty ifFalse: [ push value: root ].
	outliers ifNotNil: [
		outliers do: [ :each | | distance |
			distance := self squaredDistanceFrom: aPoint to: each encompassingRectangle.
			distance <= limit ifTrue: [ heap add: (Array with: distance with: nil with: each) ] ] ].
	[ heap isEmpty ] whileFalse: [ | item node |
		item := heap removeFirst.
		node := item at: 2.
		node
			ifNil: [ aBlock value: (item at: 3) ]
			ifNotNil: [
				push value: node left.
				push value: node right ] ]
]

{ #category : 'finding/searching' }
RTreeCollection >> nearestEntryTo: aPoint ifNone: aBlock [
	self nearestEntriesTo: aPoint within: Float infinity do: [ :each | ^ each ].
	^ aBlock value
]

{ #category : 'accessing' }
RTreeCollection >> outliers [
	"entries whose rectangle is not finite, they are searched linearly"
	self applyPendingUpdates.
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
	pending := pending copy.
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

{ #category : 'private - update' }
RTreeCollection >> rebuildTree [
	"the tree built again from its entries and their current rectangles"
	| entries |
	entries := OrderedCollection new: self leaves size.
	root do: [ :each |
		(self isFiniteRectangle: each encompassingRectangle)
			ifTrue: [ entries add: each ]
			ifFalse: [ self outliers add: each ] ].
	entries isEmpty
		ifTrue: [
			self privateRoot: RTNilNode new.
			self rebuildLeaves ]
		ifFalse: [ self buildTreeFrom: entries ]
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
	self applyPendingUpdates.
	^ root rectangle
]

{ #category : 'removing' }
RTreeCollection >> remove: oldRTEntry ifAbsent: anExceptionBlock [
	| index leaf |
	outliers ifNotNil: [
		index := outliers identityIndexOf: oldRTEntry.
		index > 0 ifTrue: [ ^ outliers removeAt: index ] ].
	leaf := self leaves removeKey: oldRTEntry ifAbsent: [ ^ anExceptionBlock value ].
	pending ifNotNil: [ pending remove: oldRTEntry ifAbsent: [ ] ].
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
	pending := nil.
	self rebuildLeaves
]

{ #category : 'accessing' }
RTreeCollection >> size [
	^ self leaves size + (outliers ifNil: [ 0 ] ifNotNil: [ outliers size ])
]

{ #category : 'accessing' }
RTreeCollection >> root [
	"the nodes hold the current rectangles of the entries"
	self applyPendingUpdates.
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
	"The rectangle of the entry changed. When the new rectangle stays inside the parent or the
	grandparent of its leaf, as for most moves of a drag or an animation, the leaf is updated in
	place and its ancestors are recomputed upwards. Otherwise the entry is recorded as pending,
	and the next query applies the update (see applyPendingUpdates): a layout moves every entry,
	and the tree is then built again at once instead of removing and adding each entry"
	| leaf rectangle |
	leaf := self leaves at: anRTEntry ifAbsent: [ nil ].
	anRTEntry resetEncompassingRectangle.
	leaf ifNil: [
		self remove: anRTEntry.
		^ self add: anRTEntry ].
	(pending notNil and: [ pending includes: anRTEntry ]) ifTrue: [ ^ self ].
	rectangle := anRTEntry encompassingRectangle.
	((self isFiniteRectangle: rectangle) and: [ self canUpdateLeaf: leaf rectangle: rectangle ])
		ifFalse: [
			(pending ifNil: [ pending := IdentitySet new ]) add: anRTEntry.
			^ self ].
	self updateLeaf: leaf rectangle: rectangle
]

{ #category : 'private - update' }
RTreeCollection >> canUpdateLeaf: aLeaf rectangle: aRectangle [
	"the parent or the grandparent of aLeaf contains aRectangle, or aLeaf is the root"
	| parent grandparent |
	parent := aLeaf parent.
	parent ifNil: [ ^ aLeaf == root ].
	(parent rectangle containsRect: aRectangle) ifTrue: [ ^ true ].
	grandparent := parent parent.
	^ grandparent notNil and: [ grandparent rectangle containsRect: aRectangle ]
]

{ #category : 'private - update' }
RTreeCollection >> updateLeaf: aLeaf rectangle: aRectangle [
	"aRectangle is inside an ancestor of aLeaf: recompute the ancestors up to the first one that does not change"
	| node |
	aLeaf rectangle: aRectangle.
	node := aLeaf parent.
	[ node isNil ] whileFalse: [ | old |
		old := node rectangle.
		node computeRectangle.
		"the ancestors of an unchanged node do not change"
		node rectangle = old ifTrue: [ ^ self ].
		node := node parent ]
]

{ #category : 'private - update' }
RTreeCollection >> updateTreeEntry: anRTEntry [
	"apply a pending update: change the leaf in place when the entry stays near, otherwise remove
	the leaf and add the entry again"
	| leaf path rectangle |
	leaf := self leaves at: anRTEntry ifAbsent: [ ^ self ].
	rectangle := anRTEntry encompassingRectangle.
	path := self pathTo: leaf.
	((self isFiniteRectangle: rectangle) and: [ self canUpdateIn: path rectangle: rectangle ])
		ifFalse: [
			"the path is known already: remove the leaf without walking up again"
			self leaves removeKey: anRTEntry.
			self removeEntry: anRTEntry path: path ifAbsent: [ self errorNotFound: anRTEntry ].
			^ self add: anRTEntry ].
	self updateLeaf: leaf rectangle: rectangle
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
