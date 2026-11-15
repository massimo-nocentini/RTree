"
A uniform grid over the rectangle of the entries: an Array of columns x rows cells, each nil or the OrderedCollection of the records (RTIndexItem) whose box meets the cell. A coordinate outside the grid is clamped to the cells of the border, which keeps every query exact (clamping is monotone), at the price of crowded border cells until the grid is tuned again.
- The cell size is tuned from the entries (the median of their larger sides, at least their mean spacing and at most 8 times it), when the collection is bulk loaded and whenever it doubled since the last tuning; cellSize: sets it and stops the tuning.
- An entry that covers more than maxCellsPerEntry cells (64) goes to an oversize list, which every query scans.
- A rectangle query marks the records it has seen with a stamp, so it finds each once and allocates nothing but its answer.
- updateEntry: moves the record only when its set of cells changed.
- In segment aware mode (segmentAware: true), an entry that answers a spatialSegment (a straight line) is registered only in the cells that its thick segment crosses, not in every cell of its rectangle: long diagonal lines stop being oversize and stop crowding the cells they do not cross. The hit tests at a point stay exact as long as the segment contains every point the entry accepts. The rectangle queries (entriesAtRectangle:, entriesInside:, entriesNear:within:) then answer only the entries whose segment comes near the rectangle: a subset of their usual answer.

It has the fastest hit test of the collections. Use it with `aCanvas shapeCollection: RTGridCollection new`, or `RTGridCollection new segmentAware: true; yourself` for a canvas of long straight lines.
"
Class {
	#name : 'RTGridCollection',
	#superclass : 'RTAbstractCollection',
	#traits : 'RTSpatialIndex',
	#classTraits : 'RTSpatialIndex classTrait',
	#instVars : [
		'cells',
		'items',
		'oversize',
		'cellSize',
		'inverse',
		'maxCellsPerEntry',
		'stamp',
		'tunedSize',
		'segmentAware',
		'autoTune',
		'originX',
		'originY',
		'columns',
		'rows'
	],
	#category : 'RTree-Collections',
	#package : 'RTree',
	#tag : 'Collections'
}

{ #category : 'private' }
RTGridCollection >> add: anItem toCells: keys [
	keys do: [ :key |
		((cells at: key) ifNil: [ cells at: key put: (OrderedCollection new: 4) ]) add: anItem ]
]

{ #category : 'private' }
RTGridCollection >> bucketAt: aKey [
	"the records of the cell, or nil"
	^ cells ifNotNil: [ cells at: aKey ]
]

{ #category : 'accessing' }
RTGridCollection >> cellSize [
	^ cellSize
]

{ #category : 'accessing' }
RTGridCollection >> cellSize: aNumber [
	"a fixed cell size: the grid is no longer tuned"
	autoTune := false.
	cellSize := aNumber.
	inverse := 1.0 / cellSize.
	cells := nil.
	columns := rows := nil.
	self rehash
]

{ #category : 'private' }
RTGridCollection >> cellX: x [
	"compared before floor: the coordinates of a query may be infinite"
	| column |
	column := x - originX * inverse.
	(column < 1 or: [ column isNaN ]) ifTrue: [ ^ 0 ].
	column >= columns ifTrue: [ ^ columns - 1 ].
	^ column floor
]

{ #category : 'private' }
RTGridCollection >> cellY: y [
	| row |
	row := y - originY * inverse.
	(row < 1 or: [ row isNaN ]) ifTrue: [ ^ 0 ].
	row >= rows ifTrue: [ ^ rows - 1 ].
	^ row floor
]

{ #category : 'accessing' }
RTGridCollection >> dimensions [
	"columns @ rows, nil before the first entry"
	^ columns ifNotNil: [ columns @ rows ]
]

{ #category : 'private - index' }
RTGridCollection >> indexEntries: anArray [
	anArray do: [ :each | items at: each put: (RTIndexItem on: each rectangle: each encompassingRectangle) ].
	self retune
]

{ #category : 'private - index' }
RTGridCollection >> indexEntry: anRTEntry rectangle: aRectangle [
	| item |
	item := RTIndexItem on: anRTEntry rectangle: aRectangle.
	items at: anRTEntry put: item.
	self insertItem: item.
	(autoTune and: [ items size >= 256 and: [ items size > (tunedSize * 2) ] ])
		ifTrue: [ self retune ]
]

{ #category : 'private - index' }
RTGridCollection >> indexIncludes: anRTEntry [
	^ items includesKey: anRTEntry
]

{ #category : 'private - index' }
RTGridCollection >> indexedEntriesAtX: x y: y do: aBlock [
	cells ifNotNil: [
		(cells at: (self cellY: y) * columns + (self cellX: x) + 1) ifNotNil: [ :bucket |
			bucket do: [ :each |
				(each left <= x and: [ x <= each right and: [ each top <= y and: [ y <= each bottom ] ] ])
					ifTrue: [ aBlock value: each entry ] ] ] ].
	oversize do: [ :each |
		(each left <= x and: [ x <= each right and: [ each top <= y and: [ y <= each bottom ] ] ])
			ifTrue: [ aBlock value: each entry ] ]
]

{ #category : 'private - index' }
RTGridCollection >> indexedEntriesDo: aBlock [
	items keysDo: aBlock
]

{ #category : 'private - index' }
RTGridCollection >> indexedEntriesTouchingLeft: left top: top right: right bottom: bottom do: aBlock [
	| firstColumn firstRow lastColumn lastRow current |
	oversize do: [ :each |
		(each touchesLeft: left top: top right: right bottom: bottom) ifTrue: [ aBlock value: each entry ] ].
	cells ifNil: [ ^ self ].
	stamp := stamp + 1.
	current := stamp.
	firstColumn := self cellX: left.
	firstRow := self cellY: top.
	lastColumn := self cellX: right.
	lastRow := self cellY: bottom.
	firstRow to: lastRow do: [ :row | | base |
		base := row * columns + 1.
		firstColumn to: lastColumn do: [ :column |
			(cells at: base + column) ifNotNil: [ :bucket |
				bucket do: [ :each |
					each stamp = current ifFalse: [
						each stamp: current.
						(each left <= right and: [ left <= each right and: [ each top <= bottom and: [ top <= each bottom ] ] ])
							ifTrue: [ aBlock value: each entry ] ] ] ] ] ]
]

{ #category : 'private - index' }
RTGridCollection >> indexedSize [
	^ items size
]

{ #category : 'private - index' }
RTGridCollection >> initializeIndex [
	"the settings are kept"
	cellSize ifNil: [ cellSize := 64.0 ].
	maxCellsPerEntry ifNil: [ maxCellsPerEntry := 64 ].
	segmentAware ifNil: [ segmentAware := false ].
	autoTune ifNil: [ autoTune := true ].
	inverse := 1.0 / cellSize.
	tunedSize := 0.
	stamp := 0.
	cells := nil.
	columns := rows := nil.
	items := IdentityDictionary new.
	oversize := OrderedCollection new
]

{ #category : 'private' }
RTGridCollection >> insertItem: anItem [
	| keys |
	cells ifNil: [
		"no bounds yet: 64 x 64 cells around the first entry, until the grid is tuned"
		originX := anItem left - (32 * cellSize).
		originY := anItem top - (32 * cellSize).
		columns := rows := 64.
		cells := Array new: columns * rows ].
	keys := self keysFor: anItem.
	anItem keys: keys.
	keys
		ifNil: [ oversize add: anItem ]
		ifNotNil: [ self add: anItem toCells: keys ]
]

{ #category : 'private' }
RTGridCollection >> itemFor: anRTEntry [
	"the record of anRTEntry, nil when it is not indexed"
	^ items at: anRTEntry ifAbsent: [ nil ]
]

{ #category : 'private' }
RTGridCollection >> keysFor: anItem [
	"the indexes of the cells of the record in cells, or nil for the oversize list"
	| firstColumn firstRow lastColumn lastRow count keys index |
	firstColumn := self cellX: anItem left.
	firstRow := self cellY: anItem top.
	lastColumn := self cellX: anItem right.
	lastRow := self cellY: anItem bottom.
	count := (lastColumn - firstColumn + 1) * (lastRow - firstRow + 1).
	(segmentAware and: [ count > 4 ]) ifTrue: [
		(self segmentKeysFor: anItem) ifNotNil: [ :segmentKeys | ^ segmentKeys ] ].
	count > maxCellsPerEntry ifTrue: [ ^ nil ].
	keys := Array new: count.
	index := 0.
	firstColumn to: lastColumn do: [ :column |
		firstRow to: lastRow do: [ :row | keys at: (index := index + 1) put: row * columns + column + 1 ] ].
	^ keys
]

{ #category : 'accessing' }
RTGridCollection >> maxCellsPerEntry: anInteger [
	"an entry over more cells goes to the oversize list"
	maxCellsPerEntry := anInteger.
	self rehash
]

{ #category : 'accessing' }
RTGridCollection >> oversizeCount [
	"the entries that every query scans"
	^ oversize size
]

{ #category : 'private' }
RTGridCollection >> rehash [
	"register every record again"
	cells := columns ifNotNil: [ Array new: columns * rows ].
	oversize := OrderedCollection new.
	items valuesDo: [ :each | self insertItem: each ]
]

{ #category : 'private - index' }
RTGridCollection >> reindexEntry: anRTEntry rectangle: aRectangle [
	"the record moves only when its set of cells changed"
	| item keys |
	item := items at: anRTEntry.
	item setRectangle: aRectangle.
	keys := self keysFor: item.
	keys = item keys ifTrue: [ ^ self ].
	self removeItem: item.
	item keys: keys.
	keys
		ifNil: [ oversize add: item ]
		ifNotNil: [ self add: item toCells: keys ]
]

{ #category : 'private' }
RTGridCollection >> removeItem: anItem [
	anItem keys
		ifNil: [ oversize remove: anItem ]
		ifNotNil: [ :keys |
			keys do: [ :key | | bucket |
				bucket := cells at: key.
				bucket remove: anItem.
				bucket isEmpty ifTrue: [ cells at: key put: nil ] ] ]
]

{ #category : 'private' }
RTGridCollection >> retune [
	"the grid over the rectangle of the entries, with a cell size from the entries when it is
	tuned, and at most max(4096, 4n) cells"
	| left top right bottom limit |
	tunedSize := items size.
	items isEmpty ifTrue: [ ^ self ].
	autoTune ifTrue: [ cellSize := self suggestedCellSize ].
	left := top := Float infinity.
	right := bottom := Float negativeInfinity.
	items valuesDo: [ :each |
		left := left min: each left.
		top := top min: each top.
		right := right max: each right.
		bottom := bottom max: each bottom ].
	limit := 4096 max: items size * 4.
	[ ((right - left) / cellSize) floor + 1 * (((bottom - top) / cellSize) floor + 1) > limit ]
		whileTrue: [ cellSize := cellSize * 1.25 ].
	inverse := 1.0 / cellSize.
	originX := left.
	originY := top.
	columns := (right - left * inverse) floor + 1.
	rows := (bottom - top * inverse) floor + 1.
	self rehash
]

{ #category : 'accessing' }
RTGridCollection >> segmentAware [
	^ segmentAware
]

{ #category : 'accessing' }
RTGridCollection >> segmentAware: aBoolean [
	"register the straight lines only in the cells their segment crosses, see the class comment"
	segmentAware := aBoolean.
	self rehash
]

{ #category : 'private' }
RTGridCollection >> segmentKeysFor: anItem [
	"The cells crossed by the thick segment of the entry, or nil when it has none. For every column,
	the segment clipped to the column widened by the half width gives a range of y, widened again
	by the half width: a cover of every point at most the half width from the segment"
	| segment keys startX startY endX endY halfWidth firstColumn lastColumn |
	segment := anItem entry spatialSegment.
	segment ifNil: [ ^ nil ].
	startX := segment first x.
	startY := segment first y.
	endX := segment second x.
	endY := segment second y.
	halfWidth := segment third.
	startX > endX ifTrue: [ | swap |
		swap := startX. startX := endX. endX := swap.
		swap := startY. startY := endY. endY := swap ].
	keys := OrderedCollection new.
	firstColumn := self cellX: startX - halfWidth.
	lastColumn := self cellX: endX + halfWidth.
	firstColumn to: lastColumn do: [ :column | | fromX toX fromY toY |
		"the border columns extend to infinity"
		fromX := column = 0
			ifTrue: [ startX ]
			ifFalse: [ (column * cellSize + originX - halfWidth) max: startX ].
		toX := column = (columns - 1)
			ifTrue: [ endX ]
			ifFalse: [ (column + 1 * cellSize + originX + halfWidth) min: endX ].
		endX = startX
			ifTrue: [
				fromY := startY.
				toY := endY ]
			ifFalse: [
				fromY := (endY - startY) * (fromX - startX) / (endX - startX) + startY.
				toY := (endY - startY) * (toX - startX) / (endX - startX) + startY ].
		(self cellY: (fromY min: toY) - halfWidth) to: (self cellY: (fromY max: toY) + halfWidth) do: [ :row |
			keys add: row * columns + column + 1 ] ].
	^ keys asArray
]

{ #category : 'private' }
RTGridCollection >> suggestedCellSize [
	"the median of the larger sides of a sample, at least the mean spacing sqrt(area / n), at most 8 times it"
	| values sample sides median left top right bottom spacing |
	values := items values.
	values isEmpty ifTrue: [ ^ cellSize ].
	sample := values size <= 1024
		ifTrue: [ values ]
		ifFalse: [ (1 to: 1024) collect: [ :i | values at: i * values size // 1024 ] ].
	sides := (sample collect: [ :each | each maxExtent ]) asArray sort.
	median := sides at: sides size + 1 // 2.
	left := top := Float infinity.
	right := bottom := Float negativeInfinity.
	values do: [ :each |
		left := left min: each left.
		top := top min: each top.
		right := right max: each right.
		bottom := bottom max: each bottom ].
	"the square roots first: the area of extreme coordinates overflows"
	spacing := (right - left) sqrt * (bottom - top) sqrt / values size sqrt.
	"the lines of the segment aware mode are registered along their length only"
	segmentAware ifTrue: [ ^ 3 * spacing max: 1.0 ].
	^ ((median max: spacing) max: 1.0) min: 8 * spacing + 1.0
]

{ #category : 'private - index' }
RTGridCollection >> unindexEntry: anRTEntry [
	| item |
	item := items removeKey: anRTEntry ifAbsent: [ ^ false ].
	self removeItem: item.
	^ true
]
