"
RSAbstractRenderTree defines 2 methods to search shapes.

- `shapeAtPoint:`
- `shapesAtRectangle:`
- `bulkload:` when user is going to change the `shapesCollection:` in canvas

subclasses of this tree should override also Collection abstract methods
"
Class {
	#name : 'RTAbstractCollection',
	#superclass : 'Collection',
	#category : 'RTree-Collections',
	#package : 'RTree',
	#tag : 'Collections'
}

{ #category : 'testing' }
RTAbstractCollection class >> isAbstract [
	^ self == RTAbstractCollection
]

{ #category : 'examples' }
RTAbstractCollection class >> exampleList [
	"in the inspector add and remove shapes"
	^ StInspectorPresenter openOn: RTSequenceableCollection new
]

{ #category : 'examples' }
RTAbstractCollection class >> exampleRTree [
	"this has normal method collections with some new more"
	^ StInspectorPresenter openOn: RTreeCollection new
]

{ #category : 'accessing' }
RTAbstractCollection >> bounds [
	"The smallest rectangle that contains the rectangle of every entry, nil when the collection is
	empty. A renderer whose window contains it can draw every entry without a query.
	A NaN coordinate of an entry makes that coordinate NaN: then the bounds contain nothing"
	| empty left top right bottom |
	empty := true.
	self do: [ :each | | rectangle origin corner |
		rectangle := each encompassingRectangle.
		origin := rectangle origin.
		corner := rectangle corner.
		empty
			ifTrue: [
				empty := false.
				left := origin x.
				top := origin y.
				right := corner x.
				bottom := corner y ]
			ifFalse: [
				left := self minimum: left with: origin x.
				top := self minimum: top with: origin y.
				right := self maximum: right with: corner x.
				bottom := self maximum: bottom with: corner y ] ].
	empty ifTrue: [ ^ nil ].
	^ (left @ top) corner: (right @ bottom)
]

{ #category : 'adding' }
RTAbstractCollection >> bulkLoad: aCollectionOfRTEntry [
	self addAll: aCollectionOfRTEntry
]

{ #category : 'enumerating' }
RTAbstractCollection >> collect: aBlock [
	"the species cannot hold any object, only entries"
	| result |
	result := OrderedCollection new.
	self do: [ :each | result add: (aBlock value: each) ].
	^ result
]

{ #category : 'finding/searching' }
RTAbstractCollection >> entriesAtPoint: position [

	^ self subclassResponsibility
]

{ #category : 'finding/searching' }
RTAbstractCollection >> entriesAtRectangle: aRectangle [
	^ self subclassResponsibility
]

{ #category : 'finding/searching' }
RTAbstractCollection >> entryAtPoint: aPoint [
	^ self entryAtPoint: aPoint ifNone: [ self errorNotFound: aPoint ]
]

{ #category : 'finding/searching' }
RTAbstractCollection >> entryAtPoint: aPoint ifNone: aBlock [
	"the topmost entry at aPoint"
	^ self entryAtPoint: aPoint satisfying: [ :each | true ] ifNone: aBlock
]

{ #category : 'finding/searching' }
RTAbstractCollection >> entryAtPoint: aPoint satisfying: aBlock ifNone: noneBlock [
	"The topmost entry at aPoint that satisfies aBlock, the first of entriesAtPoint: aPoint that does:
	a hit test needs nothing else. Subclasses answer it without computing and ordering every hit"
	^ (self entriesAtPoint: aPoint) detect: aBlock ifNone: noneBlock
]

{ #category : 'private - finding' }
RTAbstractCollection >> firstOf: candidates atPoint: aPoint satisfying: aBlock ifNone: noneBlock [
	"candidates is a sequence of the entries whose rectangle may hold aPoint. entriesAtPoint: lets
	each of them add its hits, and orders them by decreasing entryIndex (nil counts as 0), keeping
	the order of the candidates that share an index. The same order is followed here: the topmost
	candidate is usually the answer. When it is not (long lines have many candidates and few
	hits), one pass over the others keeps the first hit that satisfies aBlock of the candidate of
	the largest index, without sorting them"
	| top topIndex hits found foundIndex |
	candidates isEmpty ifTrue: [ ^ noneBlock value ].
	top := 1.
	topIndex := (candidates at: 1) entryIndex ifNil: [ 0 ].
	2 to: candidates size do: [ :i | | index |
		index := (candidates at: i) entryIndex ifNil: [ 0 ].
		index > topIndex ifTrue: [
			top := i.
			topIndex := index ] ].
	((candidates at: top) firstEntryAtPoint: aPoint satisfying: aBlock ifNone: [ nil ])
		ifNotNil: [ :entry | ^ entry ].
	hits := OrderedCollection new.
	candidates doWithIndex: [ :each :i | | index |
		index := each entryIndex ifNil: [ 0 ].
		(i ~= top and: [ found isNil or: [ index > foundIndex ] ]) ifTrue: [ | k |
			k := hits size.
			each addEntriesIn: hits position: aPoint.
			[ (k := k + 1) <= hits size ] whileTrue: [
				(aBlock value: (hits at: k)) ifTrue: [
					found := hits at: k.
					foundIndex := index.
					k := hits size ] ] ] ].
	^ found ifNil: [ noneBlock value ]
]

{ #category : 'shapes - ordering' }
RTAbstractCollection >> pushBack: anRTEntry [
	self subclassResponsibility
]

{ #category : 'shapes - ordering' }
RTAbstractCollection >> pushFront: anRTEntry [
	self subclassResponsibility
]

{ #category : 'update' }
RTAbstractCollection >> updateEntry: anRTEntry [
	^ self subclassResponsibility
]

{ #category : 'update' }
RTAbstractCollection >> updateEntry: anRTEntry before: anotherRTEntry [
	self subclassResponsibility
]

{ #category : 'private' }
RTAbstractCollection >> mergeBounds: aRectangleOrNil with: aRectangle [
	"as Rectangle>>merge:, but a NaN coordinate wins: min: and max: would keep it or not
	depending on the order of the arguments"
	| origin corner |
	aRectangleOrNil ifNil: [ ^ aRectangle ].
	origin := aRectangleOrNil origin.
	corner := aRectangleOrNil corner.
	^ ((self minimum: origin x with: aRectangle origin x) @ (self minimum: origin y with: aRectangle origin y))
		corner: ((self maximum: corner x with: aRectangle corner x) @ (self maximum: corner y with: aRectangle corner y))
]

{ #category : 'private' }
RTAbstractCollection >> maximum: aNumber with: anotherNumber [
	aNumber isNaN ifTrue: [ ^ aNumber ].
	anotherNumber isNaN ifTrue: [ ^ anotherNumber ].
	^ aNumber max: anotherNumber
]

{ #category : 'private' }
RTAbstractCollection >> minimum: aNumber with: anotherNumber [
	aNumber isNaN ifTrue: [ ^ aNumber ].
	anotherNumber isNaN ifTrue: [ ^ anotherNumber ].
	^ aNumber min: anotherNumber
]

{ #category : 'private - finding' }
RTAbstractCollection >> radixSortByEntryIndex: aCollection max: maxIndex [
	"A stable least significant digit radix sort on the entryIndex, 11 bits per pass (two passes
	up to 4 million), O(n + 2048) per pass. The indexes are SmallIntegers from 0 to maxIndex"
	| source target counts shift |
	source := aCollection asArray.
	target := Array new: source size.
	counts := Array new: 2049.
	shift := 0.
	[ shift = 0 or: [ (maxIndex bitShift: shift negated) > 0 ] ] whileTrue: [ | swap |
		counts atAllPut: 0.
		source do: [ :each | | digit |
			digit := ((each entryIndex bitShift: shift negated) bitAnd: 2047) + 2.
			counts at: digit put: (counts at: digit) + 1 ].
		"counts at: digit + 1 is now the number of entries of a smaller digit"
		counts at: 1 put: 0.
		2 to: 2049 do: [ :i | counts at: i put: (counts at: i) + (counts at: i - 1) ].
		source do: [ :each | | digit position |
			digit := ((each entryIndex bitShift: shift negated) bitAnd: 2047) + 1.
			position := (counts at: digit) + 1.
			counts at: digit put: position.
			target at: position put: each ].
		swap := source.
		source := target.
		target := swap.
		shift := shift + 11 ].
	^ OrderedCollection withAll: source
]

{ #category : 'private - finding' }
RTAbstractCollection >> sortByEntryIndex: aCollection [
	"The drawing order. A container numbers its entries 1..n, so a large result whose indexes are
	dense is placed in an Array indexed by entryIndex, O(n), and a large result of sparse or
	repeated indexes is sorted by a radix sort, O(n). Small results and entries without an
	integer entryIndex are sorted with a block. Each way keeps the order of equal indexes"
	| min max buckets result |
	aCollection size < 256 ifTrue: [ ^ self sortWithBlock: aCollection ].
	min := SmallInteger maxVal.
	max := SmallInteger minVal.
	aCollection do: [ :each | | index |
		index := each entryIndex.
		index isInteger ifFalse: [ ^ self sortWithBlock: aCollection ].
		index < min ifTrue: [ min := index ].
		index > max ifTrue: [ max := index ] ].
	max - min >= (aCollection size * 4) ifTrue: [
		^ self sortSparseByEntryIndex: aCollection min: min max: max ].
	buckets := Array new: max - min + 1.
	aCollection do: [ :each | | slot |
		slot := each entryIndex - min + 1.
		(buckets at: slot) ifNotNil: [ ^ self sortSparseByEntryIndex: aCollection min: min max: max ].
		buckets at: slot put: each ].
	result := OrderedCollection new: aCollection size.
	buckets do: [ :each | each ifNotNil: [ result add: each ] ].
	^ result
]

{ #category : 'private - finding' }
RTAbstractCollection >> sortSparseByEntryIndex: aCollection min: min max: max [
	"the radix sort from 512 entries, when the indexes are small enough integers"
	(aCollection size >= 512 and: [ min >= 0 and: [ max class == SmallInteger ] ])
		ifTrue: [ ^ self radixSortByEntryIndex: aCollection max: max ].
	^ self sortWithBlock: aCollection
]

{ #category : 'private - finding' }
RTAbstractCollection >> sortWithBlock: aCollection [
	"entryIndex is nil for an entry that no container numbered"
	^ aCollection sort: [ :a :b | (a entryIndex ifNil: [ 0 ]) <= (b entryIndex ifNil: [ 0 ]) ]
]

{ #category : 'finding/searching' }
RTAbstractCollection >> entriesInside: aRectangle [
	"the entries whose rectangle is inside aRectangle (Rectangle>>containsRect:, borders included),
	in drawing order"
	| result |
	result := OrderedCollection new.
	self do: [ :each |
		(aRectangle containsRect: each encompassingRectangle) ifTrue: [ result add: each ] ].
	^ self sortByEntryIndex: result
]

{ #category : 'finding/searching' }
RTAbstractCollection >> entriesNear: aPoint within: aDistance [
	"The entries whose rectangle is at most aDistance from aPoint, the nearest first. The distance
	of a rectangle is 0 for the points inside it or on its border. At the same distance, the entry
	drawn on top comes first. aDistance can be Float infinity"
	| limit candidates |
	aDistance < 0 ifTrue: [ ^ OrderedCollection new ].
	limit := aDistance * aDistance.
	candidates := OrderedCollection new.
	self do: [ :each | | distance |
		distance := self squaredDistanceFrom: aPoint to: each encompassingRectangle.
		distance <= limit ifTrue: [ candidates add: distance -> each ] ].
	candidates sort: [ :a :b |
		a key < b key or: [
			a key = b key and: [ (a value entryIndex ifNil: [ 0 ]) >= (b value entryIndex ifNil: [ 0 ]) ] ] ].
	^ candidates collect: [ :each | each value ]
]

{ #category : 'finding/searching' }
RTAbstractCollection >> nearestEntryTo: aPoint [
	^ self nearestEntryTo: aPoint ifNone: [ self errorEmptyCollection ]
]

{ #category : 'finding/searching' }
RTAbstractCollection >> nearestEntryTo: aPoint ifNone: aBlock [
	"the first of entriesNear: aPoint within: Float infinity, in one pass"
	| best bestDistance bestIndex |
	self do: [ :each | | distance index |
		distance := self squaredDistanceFrom: aPoint to: each encompassingRectangle.
		index := each entryIndex ifNil: [ 0 ].
		(distance isNaN not and: [ best isNil or: [
			distance < bestDistance or: [ distance = bestDistance and: [ index > bestIndex ] ] ] ])
				ifTrue: [
					best := each.
					bestDistance := distance.
					bestIndex := index ] ].
	^ best ifNil: [ aBlock value ]
]

{ #category : 'private' }
RTAbstractCollection >> squaredDistanceFrom: aPoint to: aRectangle [
	"0 inside aRectangle or on its border. NaN when aRectangle has a NaN coordinate"
	| x y origin corner dx dy |
	x := aPoint x.
	y := aPoint y.
	origin := aRectangle origin.
	corner := aRectangle corner.
	dx := x < origin x
		ifTrue: [ origin x - x ]
		ifFalse: [ x > corner x ifTrue: [ x - corner x ] ifFalse: [ 0 ] ].
	dy := y < origin y
		ifTrue: [ origin y - y ]
		ifFalse: [ y > corner y ifTrue: [ y - corner y ] ifFalse: [ 0 ] ].
	(origin x isNaN or: [ origin y isNaN or: [ corner x isNaN or: [ corner y isNaN ] ] ])
		ifTrue: [ ^ Float nan ].
	^ dx * dx + (dy * dy)
]

{ #category : 'testing' }
RTAbstractCollection >> isFiniteRectangle: aRectangle [
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

{ #category : 'private - finding' }
RTAbstractCollection >> hitsAtPoint: aPoint candidates: aBlock [
	"aBlock is evaluated with a block to evaluate with every entry whose rectangle may hold aPoint.
	Each of them adds its own hits (a composite adds its children first). Only the entries that
	added something are then ordered, by decreasing entryIndex (nil counts as 0), keeping the order
	of the candidates that share an index: this is the order of the indexesFromRoot of the hits,
	without computing them"
	| res groups |
	res := OrderedCollection new.
	groups := OrderedCollection new.
	aBlock value: [ :each | | start |
		start := res size.
		each addEntriesIn: res position: aPoint.
		res size > start ifTrue: [ groups add: each -> (start + 1 to: res size) ] ].
	groups size < 2 ifTrue: [ ^ res ].
	groups sort: [ :a :b | (a key entryIndex ifNil: [ 0 ]) >= (b key entryIndex ifNil: [ 0 ]) ].
	^ groups
		inject: (OrderedCollection new: res size)
		into: [ :sorted :group |
			group value do: [ :index | sorted add: (res at: index) ].
			sorted ]
]
