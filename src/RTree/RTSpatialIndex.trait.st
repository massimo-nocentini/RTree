"
The queries and the protocol of RTAbstractCollection for the spatial indexes that can replace RTreeCollection, for example with `aCanvas shapeCollection: RTNaryTreeCollection new`.

A collection with this trait indexes the entries whose rectangle is finite. The others (a NaN or an infinite coordinate) are kept in `outliers` and tested by every query, as in RTreeCollection. An entry is held once.

The queries are written here on top of a few primitives of the index (category 'private - index'), which the collection implements:
- initializeIndex, an empty index;
- indexEntry:rectangle:, indexEntries: (a bulk load), unindexEntry:, reindexEntry:rectangle: (the rectangle of the entry changed);
- indexIncludes:, indexedSize, indexedEntriesDo:;
- indexedEntriesAtX:y:do: (every entry whose indexed rectangle holds the point, borders included) and indexedEntriesTouchingLeft:top:right:bottom:do: (every entry whose indexed rectangle meets the closed rectangle, each once).

The answers are in the order of RTreeCollection: by decreasing entryIndex at a point, by increasing entryIndex for the other queries, by distance for the nearest entries. pushBack:, pushFront: and updateEntry:before: do nothing, the order is the entryIndex.

`seenLeft`, `seenTop`, `seenRight` and `seenBottom` only grow: a rectangle that contains every indexed entry, for nearestEntryTo:ifNone:.
"
Trait {
	#name : 'RTSpatialIndex',
	#instVars : [
		'outliers',
		'seenLeft',
		'seenTop',
		'seenRight',
		'seenBottom'
	],
	#category : 'RTree-Traits',
	#package : 'RTree',
	#tag : 'Traits'
}

{ #category : 'adding' }
RTSpatialIndex >> add: anRTEntry [
	| rectangle |
	"ask the rectangle first: an entry that cannot answer it must not change the index"
	rectangle := anRTEntry encompassingRectangle.
	(self includes: anRTEntry) ifTrue: [ ^ anRTEntry ].
	(self isFiniteRectangle: rectangle) ifFalse: [
		outliers add: anRTEntry.
		^ anRTEntry ].
	self noteRectangle: rectangle.
	self indexEntry: anRTEntry rectangle: rectangle.
	^ anRTEntry
]

{ #category : 'adding' }
RTSpatialIndex >> bulkLoad: aCollectionOfRTEntry [
	"an empty index is built at once"
	| seen entries |
	self isEmpty ifFalse: [ ^ super bulkLoad: aCollectionOfRTEntry ].
	seen := IdentitySet new.
	entries := OrderedCollection new: aCollectionOfRTEntry size.
	aCollectionOfRTEntry do: [ :each |
		(seen includes: each) ifFalse: [ | rectangle |
			seen add: each.
			rectangle := each encompassingRectangle.
			(self isFiniteRectangle: rectangle)
				ifTrue: [
					self noteRectangle: rectangle.
					entries add: each ]
				ifFalse: [ outliers add: each ] ] ].
	entries ifNotEmpty: [ self indexEntries: entries asArray ]
]

{ #category : 'enumerating' }
RTSpatialIndex >> do: aBlock [
	self indexedEntriesDo: aBlock.
	outliers do: aBlock
]

{ #category : 'finding/searching' }
RTSpatialIndex >> entriesAtPoint: aPoint [
	"the topmost entry first, see hitsAtPoint:candidates:"
	^ self hitsAtPoint: aPoint candidates: [ :addHits |
		self indexedEntriesAtX: aPoint x y: aPoint y do: addHits.
		outliers do: addHits ]
]

{ #category : 'finding/searching' }
RTSpatialIndex >> entriesAtRectangle: aRectangle [
	^ self sortByEntryIndex: (self entriesTouching: aRectangle select: [ :rectangle |
		rectangle intersects: aRectangle ])
]

{ #category : 'finding/searching' }
RTSpatialIndex >> entriesInside: aRectangle [
	^ self sortByEntryIndex: (self entriesTouching: aRectangle select: [ :rectangle |
		aRectangle containsRect: rectangle ])
]

{ #category : 'finding/searching' }
RTSpatialIndex >> entriesNear: aPoint within: aDistance [
	"see RTAbstractCollection>>entriesNear:within:. Only the entries of the square around aPoint
	are measured, unless aDistance is infinite"
	| limit slack candidates |
	aDistance < 0 ifTrue: [ ^ OrderedCollection new ].
	limit := aDistance * aDistance.
	"an infinite square of the distance (aDistance is infinite or too large) holds every entry"
	limit = Float infinity ifTrue: [ ^ super entriesNear: aPoint within: aDistance ].
	"the square is a little larger: its sides are rounded otherwise than the distances"
	slack := aDistance + ((aPoint x abs + aPoint y abs + aDistance) * 1.0e-9).
	candidates := OrderedCollection new.
	(self
		entriesTouching: (aPoint - slack corner: aPoint + slack)
		select: [ :rectangle | true ])
			do: [ :each | | distance |
				distance := self squaredDistanceFrom: aPoint to: each encompassingRectangle.
				distance <= limit ifTrue: [ candidates add: distance -> each ] ].
	candidates sort: [ :a :b |
		a key < b key or: [
			a key = b key and: [ (a value entryIndex ifNil: [ 0 ]) >= (b value entryIndex ifNil: [ 0 ]) ] ] ].
	^ candidates collect: [ :each | each value ]
]

{ #category : 'private - finding' }
RTSpatialIndex >> entriesTouching: aRectangle select: aBlock [
	"the entries whose indexed rectangle meets aRectangle (borders included) and whose
	rectangle satisfies aBlock, and the outliers whose rectangle does"
	| result origin corner |
	result := OrderedCollection new.
	origin := aRectangle origin.
	corner := aRectangle corner.
	self
		indexedEntriesTouchingLeft: origin x top: origin y right: corner x bottom: corner y
		do: [ :each | (aBlock value: each encompassingRectangle) ifTrue: [ result add: each ] ].
	outliers do: [ :each | (aBlock value: each encompassingRectangle) ifTrue: [ result add: each ] ].
	^ result
]

{ #category : 'finding/searching' }
RTSpatialIndex >> entryAtPoint: aPoint satisfying: aBlock ifNone: noneBlock [
	"only the entries whose rectangle holds aPoint are collected, then tried from the topmost"
	| candidates |
	candidates := OrderedCollection new.
	self indexedEntriesAtX: aPoint x y: aPoint y do: [ :each | candidates add: each ].
	candidates addAll: outliers.
	^ self firstOf: candidates atPoint: aPoint satisfying: aBlock ifNone: noneBlock
]

{ #category : 'testing' }
RTSpatialIndex >> includes: anObject [
	"identity, as remove:"
	^ (self indexIncludes: anObject) or: [ outliers identityIncludes: anObject ]
]

{ #category : 'private - index' }
RTSpatialIndex >> indexEntries: anArray [
	"index the entries at once, their rectangles are finite"
	anArray do: [ :each | self indexEntry: each rectangle: each encompassingRectangle ]
]

{ #category : 'private - index' }
RTSpatialIndex >> indexEntry: anRTEntry rectangle: aRectangle [
	"aRectangle is finite"
	self explicitRequirement
]

{ #category : 'private - index' }
RTSpatialIndex >> indexIncludes: anRTEntry [
	^ self explicitRequirement
]

{ #category : 'private - index' }
RTSpatialIndex >> indexedEntriesAtX: x y: y do: aBlock [
	"every entry whose indexed rectangle holds x @ y, borders included"
	self explicitRequirement
]

{ #category : 'private - index' }
RTSpatialIndex >> indexedEntriesDo: aBlock [
	self explicitRequirement
]

{ #category : 'private - index' }
RTSpatialIndex >> indexedEntriesTouchingLeft: left top: top right: right bottom: bottom do: aBlock [
	"every entry whose indexed rectangle meets the rectangle, borders included, each once"
	self explicitRequirement
]

{ #category : 'private - index' }
RTSpatialIndex >> indexedSize [
	^ self explicitRequirement
]

{ #category : 'initialization' }
RTSpatialIndex >> initialize [
	super initialize.
	outliers := OrderedCollection new.
	self initializeIndex
]

{ #category : 'private - index' }
RTSpatialIndex >> initializeIndex [
	"an empty index"
	self explicitRequirement
]

{ #category : 'testing' }
RTSpatialIndex >> isEmpty [
	^ self indexedSize = 0 and: [ outliers isEmpty ]
]

{ #category : 'finding/searching' }
RTSpatialIndex >> nearestEntryTo: aPoint ifNone: aBlock [
	"entriesNear:within: a radius that doubles until an entry is found. The rectangle of the seen
	entries bounds the radius: every indexed entry is within the distance to its farthest corner"
	| x y farthest radius found |
	self isEmpty ifTrue: [ ^ aBlock value ].
	seenLeft ifNil: [ ^ super nearestEntryTo: aPoint ifNone: aBlock ].
	x := aPoint x.
	y := aPoint y.
	farthest := (((x - seenLeft) abs max: (x - seenRight) abs) squared
		+ ((y - seenTop) abs max: (y - seenBottom) abs) squared) sqrt.
	radius := ((seenRight - seenLeft max: seenBottom - seenTop) / (self indexedSize max: 1) sqrt) min: farthest.
	[	found := self entriesNear: aPoint within: radius.
		found isEmpty and: [ radius < farthest ] ]
			whileTrue: [ radius := (radius * 2 max: farthest / 1024) min: farthest ].
	found ifEmpty: [ ^ super nearestEntryTo: aPoint ifNone: aBlock ].
	^ found first
]

{ #category : 'private' }
RTSpatialIndex >> noteRectangle: aRectangle [
	"grow the rectangle of the seen entries"
	| origin corner |
	origin := aRectangle origin.
	corner := aRectangle corner.
	seenLeft
		ifNil: [
			seenLeft := origin x.
			seenTop := origin y.
			seenRight := corner x.
			seenBottom := corner y ]
		ifNotNil: [
			seenLeft := seenLeft min: origin x.
			seenTop := seenTop min: origin y.
			seenRight := seenRight max: corner x.
			seenBottom := seenBottom max: corner y ]
]

{ #category : 'accessing' }
RTSpatialIndex >> outliers [
	"entries whose rectangle is not finite, they are searched linearly"
	^ outliers
]

{ #category : 'copying' }
RTSpatialIndex >> postCopy [
	"the index of the copy is built again from the entries: only the entries are shared"
	| entries |
	super postCopy.
	entries := OrderedCollection new.
	self indexedEntriesDo: [ :each | entries add: each ].
	outliers := outliers copy.
	self initializeIndex.
	entries ifNotEmpty: [ self indexEntries: entries asArray ]
]

{ #category : 'shapes - ordering' }
RTSpatialIndex >> pushBack: anRTEntry [
	"the order is the entryIndex"
]

{ #category : 'shapes - ordering' }
RTSpatialIndex >> pushFront: anRTEntry [
	"the order is the entryIndex"
]

{ #category : 'private - index' }
RTSpatialIndex >> reindexEntry: anRTEntry rectangle: aRectangle [
	"the rectangle of the indexed entry is now aRectangle, which is finite"
	self explicitRequirement
]

{ #category : 'removing' }
RTSpatialIndex >> remove: anRTEntry ifAbsent: aBlock [
	| index |
	index := outliers identityIndexOf: anRTEntry.
	index > 0 ifTrue: [ ^ outliers removeAt: index ].
	(self unindexEntry: anRTEntry) ifFalse: [ ^ aBlock value ].
	^ anRTEntry
]

{ #category : 'removing' }
RTSpatialIndex >> removeAll [
	outliers := OrderedCollection new.
	self initializeIndex
]

{ #category : 'accessing' }
RTSpatialIndex >> size [
	^ self indexedSize + outliers size
]

{ #category : 'private - index' }
RTSpatialIndex >> unindexEntry: anRTEntry [
	"answer false when anRTEntry is not indexed"
	^ self explicitRequirement
]

{ #category : 'update' }
RTSpatialIndex >> updateEntry: anRTEntry [
	| rectangle |
	anRTEntry resetEncompassingRectangle.
	(self indexIncludes: anRTEntry) ifFalse: [
		"an outlier, which may be finite now, or an entry that is not here: an error, as in RTreeCollection"
		self remove: anRTEntry.
		^ self add: anRTEntry ].
	rectangle := anRTEntry encompassingRectangle.
	(self isFiniteRectangle: rectangle) ifFalse: [
		self unindexEntry: anRTEntry.
		^ outliers add: anRTEntry ].
	self noteRectangle: rectangle.
	self reindexEntry: anRTEntry rectangle: rectangle
]

{ #category : 'update' }
RTSpatialIndex >> updateEntry: anRTEntry before: anotherRTEntry [
	"the order is the entryIndex"
]
