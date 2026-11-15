"
A static R-tree packed in flat Arrays, in the style of Flatbush (V. Agafonkin), for canvases that change little. The entries are sorted by the Hilbert index of their center and packed 16 per node, level by level: `boxes` holds the four coordinates of every leaf and node, `slots` the entry of a leaf or the first child of a node, `ends` the last child of a node. The queries walk the Arrays with an explicit stack, without node objects.

To stay usable on a live canvas it keeps changes aside:
- add: puts the entry in `pending`, which every query scans;
- remove: blanks the slot of the entry;
- updateEntry: changes the box of the slot in place while it stays inside the box of its node, and otherwise blanks the slot and puts the entry in pending;
- the Arrays are built again at the next query once the pending entries and the blank slots are more than 64 and more than 1/16 of the entries.
bulkLoad: builds the Arrays at once. Its structure takes about 100 bytes and one object per entry.

Use it with `aCanvas shapeCollection: RTPackedTreeCollection new`.
"
Class {
	#name : 'RTPackedTreeCollection',
	#superclass : 'RTAbstractCollection',
	#traits : 'RTSpatialIndex',
	#classTraits : 'RTSpatialIndex classTrait',
	#instVars : [
		'nodeSize',
		'numItems',
		'total',
		'slots',
		'ends',
		'boxes',
		'positions',
		'pending',
		'deleted',
		'rebuilds'
	],
	#category : 'RTree-Collections',
	#package : 'RTree',
	#tag : 'Collections'
}

{ #category : 'private' }
RTPackedTreeCollection >> buildFrom: items [
	"pack the RTIndexItems in Hilbert order, nodeSize per node, level by level up to the root"
	| count minX minY maxX maxY width height nodeCount levelCount position levelStart levelEnd |
	count := items size.
	numItems := count.
	positions := IdentityDictionary new: count * 2.
	pending := IdentityDictionary new.
	deleted := 0.
	rebuilds := rebuilds + 1.
	count = 0 ifTrue: [
		total := 0.
		slots := ends := boxes := #().
		^ self ].
	minX := minY := Float infinity.
	maxX := maxY := Float negativeInfinity.
	items do: [ :each | | x y |
		x := each doubleCenterX.
		y := each doubleCenterY.
		minX := minX min: x.
		minY := minY min: y.
		maxX := maxX max: x.
		maxY := maxY max: y ].
	width := maxX - minX.
	width = 0 ifTrue: [ width := 1 ].
	height := maxY - minY.
	height = 0 ifTrue: [ height := 1 ].
	items do: [ :each |
		each stamp: (self
			hilbertX: (65535 * (each doubleCenterX - minX) / width) floor
			y: (65535 * (each doubleCenterY - minY) / height) floor) ].
	items sort: [ :a :b | a stamp <= b stamp ].
	nodeCount := count.
	levelCount := count.
	[ levelCount > 1 ] whileTrue: [
		levelCount := levelCount + nodeSize - 1 // nodeSize.
		nodeCount := nodeCount + levelCount ].
	total := nodeCount.
	slots := Array new: total.
	ends := Array new: total.
	boxes := Array new: total * 4.
	items doWithIndex: [ :each :i |
		slots at: i put: each entry.
		positions at: each entry put: i.
		self setBox: i left: each left top: each top right: each right bottom: each bottom ].
	position := count + 1.
	levelStart := 1.
	levelEnd := count.
	[ levelEnd > levelStart ] whileTrue: [
		levelStart to: levelEnd by: nodeSize do: [ :first | | last left top right bottom |
			last := first + nodeSize - 1 min: levelEnd.
			slots at: position put: first.
			ends at: position put: last.
			left := top := Float infinity.
			right := bottom := Float negativeInfinity.
			first to: last do: [ :child | | base |
				base := child - 1 * 4.
				left := left min: (boxes at: base + 1).
				top := top min: (boxes at: base + 2).
				right := right max: (boxes at: base + 3).
				bottom := bottom max: (boxes at: base + 4) ].
			self setBox: position left: left top: top right: right bottom: bottom.
			position := position + 1 ].
		levelStart := levelEnd + 1.
		levelEnd := position - 1 ]
]

{ #category : 'private' }
RTPackedTreeCollection >> ensureIndex [
	"build the Arrays again when there are too many pending entries and blank slots"
	pending size + deleted > (64 max: numItems // 16) ifTrue: [ self rebuild ]
]

{ #category : 'private' }
RTPackedTreeCollection >> hilbertX: xIn y: yIn [
	"the index of (x, y) on the Hilbert curve of order 16"
	| x y index side rx ry swap |
	x := xIn.
	y := yIn.
	index := 0.
	side := 32768.
	[ side > 0 ] whileTrue: [
		rx := (x bitAnd: side) > 0 ifTrue: [ 1 ] ifFalse: [ 0 ].
		ry := (y bitAnd: side) > 0 ifTrue: [ 1 ] ifFalse: [ 0 ].
		index := index + (side * side * ((3 * rx) bitXor: ry)).
		ry = 0 ifTrue: [
			rx = 1 ifTrue: [
				x := 65535 - x.
				y := 65535 - y ].
			swap := x.
			x := y.
			y := swap ].
		side := side // 2 ].
	^ index
]

{ #category : 'private - index' }
RTPackedTreeCollection >> indexEntries: anArray [
	anArray do: [ :each | pending at: each put: (RTIndexItem on: each rectangle: each encompassingRectangle) ].
	self rebuild
]

{ #category : 'private - index' }
RTPackedTreeCollection >> indexEntry: anRTEntry rectangle: aRectangle [
	pending at: anRTEntry put: (RTIndexItem on: anRTEntry rectangle: aRectangle)
]

{ #category : 'private - index' }
RTPackedTreeCollection >> indexIncludes: anRTEntry [
	^ (positions includesKey: anRTEntry) or: [ pending includesKey: anRTEntry ]
]

{ #category : 'private - index' }
RTPackedTreeCollection >> indexedEntriesAtX: x y: y do: aBlock [
	self ensureIndex.
	total > 0 ifTrue: [ | stack |
		stack := OrderedCollection with: total.
		total = 1 ifTrue: [
			"the only leaf is the root"
			stack := OrderedCollection new.
			((boxes at: 1) <= x and: [ x <= (boxes at: 3) and: [ (boxes at: 2) <= y and: [ y <= (boxes at: 4) ] ] ])
				ifTrue: [ (slots at: 1) ifNotNil: [ :entry | aBlock value: entry ] ] ].
		[ stack isEmpty ] whileFalse: [ | node |
			node := stack removeLast.
			(slots at: node) to: (ends at: node) do: [ :child | | base |
				base := child - 1 * 4.
				((boxes at: base + 1) <= x and: [ x <= (boxes at: base + 3) and: [
					(boxes at: base + 2) <= y and: [ y <= (boxes at: base + 4) ] ] ])
						ifTrue: [
							child <= numItems
								ifTrue: [ (slots at: child) ifNotNil: [ :entry | aBlock value: entry ] ]
								ifFalse: [ stack addLast: child ] ] ] ] ].
	pending valuesDo: [ :each | (each containsX: x y: y) ifTrue: [ aBlock value: each entry ] ]
]

{ #category : 'private - index' }
RTPackedTreeCollection >> indexedEntriesDo: aBlock [
	positions keysDo: aBlock.
	pending keysDo: aBlock
]

{ #category : 'private - index' }
RTPackedTreeCollection >> indexedEntriesTouchingLeft: left top: top right: right bottom: bottom do: aBlock [
	self ensureIndex.
	total > 0 ifTrue: [ | stack |
		stack := OrderedCollection with: total.
		total = 1 ifTrue: [
			stack := OrderedCollection new.
			((boxes at: 1) <= right and: [ left <= (boxes at: 3) and: [ (boxes at: 2) <= bottom and: [ top <= (boxes at: 4) ] ] ])
				ifTrue: [ (slots at: 1) ifNotNil: [ :entry | aBlock value: entry ] ] ].
		[ stack isEmpty ] whileFalse: [ | node |
			node := stack removeLast.
			(slots at: node) to: (ends at: node) do: [ :child | | base |
				base := child - 1 * 4.
				((boxes at: base + 1) <= right and: [ left <= (boxes at: base + 3) and: [
					(boxes at: base + 2) <= bottom and: [ top <= (boxes at: base + 4) ] ] ])
						ifTrue: [
							child <= numItems
								ifTrue: [ (slots at: child) ifNotNil: [ :entry | aBlock value: entry ] ]
								ifFalse: [ stack addLast: child ] ] ] ] ].
	pending valuesDo: [ :each |
		(each touchesLeft: left top: top right: right bottom: bottom) ifTrue: [ aBlock value: each entry ] ]
]

{ #category : 'private - index' }
RTPackedTreeCollection >> indexedSize [
	^ positions size + pending size
]

{ #category : 'private - index' }
RTPackedTreeCollection >> initializeIndex [
	nodeSize := 16.
	rebuilds := -1.
	self buildFrom: #()
]

{ #category : 'accessing' }
RTPackedTreeCollection >> pendingCount [
	"the entries that the queries scan, until the next rebuild"
	^ pending size
]

{ #category : 'private' }
RTPackedTreeCollection >> rebuild [
	"pack the entries again, each with the box it is indexed with"
	| items |
	items := OrderedCollection new: self indexedSize.
	positions keysAndValuesDo: [ :entry :position | | base |
		base := position - 1 * 4.
		items add: (RTIndexItem
			on: entry
			left: (boxes at: base + 1)
			top: (boxes at: base + 2)
			right: (boxes at: base + 3)
			bottom: (boxes at: base + 4)) ].
	pending valuesDo: [ :each | items add: each ].
	self buildFrom: items asArray
]

{ #category : 'accessing' }
RTPackedTreeCollection >> rebuilds [
	"how many times the Arrays were built"
	^ rebuilds
]

{ #category : 'private - index' }
RTPackedTreeCollection >> reindexEntry: anRTEntry rectangle: aRectangle [
	"in place while the box stays inside the box of its node, otherwise pending"
	| position node base origin corner |
	(pending at: anRTEntry ifAbsent: [ nil ]) ifNotNil: [ :item | ^ item setRectangle: aRectangle ].
	position := positions at: anRTEntry.
	origin := aRectangle origin.
	corner := aRectangle corner.
	total = 1 ifTrue: [ ^ self setBox: 1 left: origin x top: origin y right: corner x bottom: corner y ].
	node := numItems + 1 + (position - 1 // nodeSize).
	base := node - 1 * 4.
	((boxes at: base + 1) <= origin x and: [ (boxes at: base + 2) <= origin y and: [
		corner x <= (boxes at: base + 3) and: [ corner y <= (boxes at: base + 4) ] ] ])
			ifTrue: [ ^ self setBox: position left: origin x top: origin y right: corner x bottom: corner y ].
	positions removeKey: anRTEntry.
	slots at: position put: nil.
	deleted := deleted + 1.
	pending at: anRTEntry put: (RTIndexItem on: anRTEntry rectangle: aRectangle)
]

{ #category : 'private' }
RTPackedTreeCollection >> setBox: position left: left top: top right: right bottom: bottom [
	| base |
	base := position - 1 * 4.
	boxes at: base + 1 put: left.
	boxes at: base + 2 put: top.
	boxes at: base + 3 put: right.
	boxes at: base + 4 put: bottom
]

{ #category : 'private - index' }
RTPackedTreeCollection >> unindexEntry: anRTEntry [
	| position |
	pending removeKey: anRTEntry ifAbsent: [
		position := positions removeKey: anRTEntry ifAbsent: [ ^ false ].
		slots at: position put: nil.
		deleted := deleted + 1 ].
	^ true
]
