Class {
	#name : 'RTCollectionTest',
	#superclass : 'ParametrizedTestCase',
	#instVars : [
		'entryCollection',
		'entryCollectionClass'
	],
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'building suites' }
RTCollectionTest class >> testParameters [
	"every concrete collection of the RTree package"
	| m classesToConsider |
	m := ParametrizedTestMatrix new.
	classesToConsider := (RTAbstractCollection allSubclasses select: [ :each |
		each isAbstract not and: [ each package == RTAbstractCollection package ] ])
			asSortedCollection: [ :a :b | a name <= b name ].
	classesToConsider do: [ :cls |
		m addCase: { (#entryCollectionClass: -> cls) }
	].
	^ m
]

{ #category : 'accessing' }
RTCollectionTest >> entryCollection [
	^ entryCollection
]

{ #category : 'accessing' }
RTCollectionTest >> entryCollection: anObject [

	entryCollection := anObject
]

{ #category : 'accessing' }
RTCollectionTest >> entryCollectionClass [

	^ entryCollectionClass
]

{ #category : 'accessing' }
RTCollectionTest >> entryCollectionClass: anObject [
	entryCollectionClass := anObject
]

{ #category : 'running' }
RTCollectionTest >> setUp [
	super setUp.
	entryCollection := self entryCollectionClass new
]

{ #category : 'tests' }
RTCollectionTest >> testGetEntriesFromRectangle [

	| listOfEntries box1 box2 box3 |
	box1 := RTreeBox new
		        size: 20 @ 20;
		        position: -50 @ -50;
		        entryIndex: 1;
		        yourself.
	box2 := RTreeBox new
		        size: 20 @ 20;
		        position: 50 @ 50;
		        entryIndex: 2;
		        yourself.
	box3 := RTreeBox new
		        size: 20 @ 20;
		        entryIndex: 3;
		        yourself.
	entryCollection addAll: {
			box1.
			box2.
			box3 }.
	listOfEntries := entryCollection entriesAtRectangle: (5 @ 5 corner: 60 @ 60).
	self assert: listOfEntries asArray equals: {
			box2.
			box3 }
]

{ #category : 'tests' }
RTCollectionTest >> testGetEntriesFromRectangleInParent [

	| listOfEntries box composite |
	box := RTreeBox new
		       size: 20 @ 20;
		       yourself.
	composite := RTreeBox new
		             size: 100;
		             yourself.
	composite add: box.
	entryCollection add: composite.
	listOfEntries := entryCollection entriesAtRectangle: (-5 @ -5 corner: 5 @ 5).
	self assert: listOfEntries asArray equals: { composite }
]

{ #category : 'tests' }
RTCollectionTest >> testGetEntriesFromRectangleInParentWithChildOutside [

	| listOfShapes box composite |
	box := RTreeBox new
		       size: 20 @ 20;
		       position: 120 @ 120;
		       yourself.
	composite := RTreeBox new
		             size: 100;
		             yourself.
	composite add: box.
	entryCollection add: composite.
	listOfShapes := entryCollection entriesAtRectangle: (110 @ 110 corner: 130 @ 130).
	self assert: listOfShapes asArray isEmpty
]

{ #category : 'tests' }
RTCollectionTest >> testGetEntryFromRectangle [

	| listOfEntries |
	entryCollection add: (RTreeBox new
			 size: 20 @ 20;
			 yourself).
	listOfEntries := entryCollection entriesAtRectangle: (-5 @ -5 corner: 5 @ 5).
	self assert: (listOfEntries includes: entryCollection anyOne)
]

{ #category : 'tests' }
RTCollectionTest >> testIncludes [

	| result |
	entryCollection addAll: {
			(RTreeBox new size: 10).
			(RTreeBox new
				 position: 50 @ 50;
				 size: 10 @ 10) }.
	self assert: entryCollection size equals: 2.
	result := entryCollection entriesAtPoint: -100 @ -100.
	self assert: result isEmpty.
	result := entryCollection entryAtPoint: -100 @ -100 ifNone: [ nil ].
	self assert: result isNil
]

{ #category : 'tests' }
RTCollectionTest >> testIsEmpty [

	self assert: entryCollection isEmpty
]

{ #category : 'tests' }
RTCollectionTest >> testOneElement [

	entryCollection add: (RTreeBox new size: 10).
	self deny: entryCollection isEmpty
]

{ #category : 'tests' }
RTCollectionTest >> testSortResultArray [

	| shapes a b c d tree e |
	shapes := {
		          ((a := RTreeBox model: 'a') -> { 1. 1 }).
		          ((b := RTreeBox model: 'b') -> { 1. 2 }).
		          ((c := RTreeBox model: 'c') -> { 3. 1 }).
		          ((d := RTreeBox model: 'd') -> { 1. 4 }).
		          ((e := RTreeBox model: 'e') -> { 1. 4. 1 }) }.
	tree := RTreeCollection new.
	tree sortResultList: shapes.

	self assert: (shapes collect: #key) equals: {
			c.
			e.
			d.
			b.
			a }
]

{ #category : 'tests' }
RTCollectionTest >> testCopyIsIndependent [
	"copy shared the nodes (or the OrderedCollection) with the original"
	| box1 box2 box3 copy |
	box1 := RTreeBox new size: 10; position: 0 @ 0; entryIndex: 1; yourself.
	box2 := RTreeBox new size: 10; position: 100 @ 100; entryIndex: 2; yourself.
	box3 := RTreeBox new size: 10; position: 200 @ 0; entryIndex: 3; yourself.
	entryCollection add: box1; add: box2.
	copy := entryCollection copy.
	copy add: box3.
	self assert: entryCollection size equals: 2.
	self assert: copy size equals: 3.
	self assert: (entryCollection entriesAtPoint: 205 @ 5) isEmpty.
	copy remove: box1.
	copy remove: box2.
	self assert: entryCollection size equals: 2.
	self assert: (entryCollection entriesAtPoint: 5 @ 5) asArray equals: { box1 }.
	self assert: (copy entriesAtPoint: 205 @ 5) asArray equals: { box3 }
]

{ #category : 'tests' }
RTCollectionTest >> testAddAndRemoveAnswerTheEntry [
	"RTSequenceableCollection answered itself"
	| box |
	box := RTreeBox new size: 10; entryIndex: 1; yourself.
	self assert: (entryCollection add: box) identicalTo: box.
	self assert: (entryCollection remove: box) identicalTo: box
]

{ #category : 'tests' }
RTCollectionTest >> testCollect [
	"collect: answered a collection of the receiver's species, which cannot hold any object"
	| result |
	1 to: 6 do: [ :i |
		entryCollection add: (RTreeBox new size: 10; position: (i * 20) @ 0; model: i; entryIndex: i; yourself) ].
	result := entryCollection collect: [ :each | each model ].
	self assert: result asArray sort equals: #( 1 2 3 4 5 6 )
]

{ #category : 'tests' }
RTCollectionTest >> testRemoveAll [
	"Collection>>removeAll removes while it iterates"
	1 to: 8 do: [ :i |
		entryCollection add: (RTreeBox new size: 10; position: (i * 20) @ 0; entryIndex: i; yourself) ].
	entryCollection removeAll.
	self assert: entryCollection isEmpty.
	self assert: entryCollection size equals: 0.
	self assert: (entryCollection entriesAtPoint: 25 @ 5) isEmpty
]

{ #category : 'tests' }
RTCollectionTest >> testSizeAndIncludes [
	| boxes |
	boxes := (1 to: 5) collect: [ :i |
		RTreeBox new size: 10; position: (i * 20) @ 0; entryIndex: i; yourself ].
	self assert: entryCollection size equals: 0.
	self deny: (entryCollection includes: boxes first).
	entryCollection addAll: boxes.
	self assert: entryCollection size equals: 5.
	self deny: entryCollection isEmpty.
	self assert: (boxes allSatisfy: [ :each | entryCollection includes: each ]).
	self deny: (entryCollection includes: RTreeBox new).
	entryCollection remove: boxes second.
	self assert: entryCollection size equals: 4.
	self deny: (entryCollection includes: boxes second).
	entryCollection removeAll.
	self assert: entryCollection isEmpty
]

{ #category : 'helpers' }
RTCollectionTest >> randomEntries: count seed: seed [
	"boxes and composites (nested twice at most) at random places. Most entries share their
	entryIndex with 3 others, some have none: the order of the collection breaks these ties"
	| random make |
	random := Random seed: seed.
	make := nil.
	make := [ :model :depth :origin :side | | box width height |
		width := random next * side / 4 + 1.
		height := random next * side / 4 + 1.
		box := (depth < 2 and: [ random next < 0.15 ])
			ifTrue: [
				RTreeCompositeBox new
					lazyHits: random next < 0.5;
					shapeCollection: self entryCollectionClass new;
					yourself ]
			ifFalse: [ RTreeBox new ].
		box
			model: model;
			position: origin + ((random next * side) @ (random next * side));
			extent: width @ height.
		(box isKindOf: RTreeCompositeBox) ifTrue: [
			1 to: 5 do: [ :k |
				box addShape: (make
					value: model * 10 + k
					value: depth + 1
					value: box position
					value: (width min: height)) ] ].
		box ].
	^ (1 to: count) collect: [ :i | | box |
		box := make value: i value: 0 value: 0 @ 0 value: 400.
		box entryIndex: (i \\ 11 = 0
			ifTrue: [ nil ]
			ifFalse: [ i // 4 ]).
		box ]
]

{ #category : 'tests' }
RTCollectionTest >> testEntryAtPointSatisfyingIsTheFirstHit [
	"the topmost query answers the first entry of entriesAtPoint: that satisfies the block,
	with nested composites, shared and missing entryIndexes, and an infinite entry"
	| random points blocks infinite |
	entryCollection addAll: (self randomEntries: 300 seed: 41).
	infinite := RTreeBox new
		model: 9999;
		entryIndex: 150;
		extent: Float infinity @ Float infinity;
		yourself.
	entryCollection add: infinite.
	"a pile of entries that share one index or have none, beside the others"
	1 to: 20 do: [ :k |
		entryCollection add: (RTreeBox new
			model: 10000 + k;
			entryIndex: (k odd ifTrue: [ 1000 ] ifFalse: [ nil ]);
			position: (500 + k) @ (500 - k);
			extent: 30 @ 30;
			yourself) ].
	random := Random seed: 42.
	points := (1 to: 400) collect: [ :i | (random next * 420 - 10) @ (random next * 420 - 10) ].
	points := points , ((entryCollection asArray first: 40) collect: [ :each | each position ]).
	points := points , ((500 to: 550 by: 5) flatCollect: [ :x | (480 to: 530 by: 5) collect: [ :y | x @ y ] ]).
	blocks := {
		[ :each | true ].
		[ :each | false ].
		[ :each | each model odd ].
		[ :each | each isKindOf: RTreeCompositeBox ].
		[ :each | each model \\ 3 = 0 and: [ each ~~ infinite ] ] }.
	points do: [ :point | | hits |
		hits := entryCollection entriesAtPoint: point.
		blocks do: [ :block |
			self
				assert: (entryCollection entryAtPoint: point satisfying: block ifNone: [ nil ])
				identicalTo: (hits detect: block ifNone: [ nil ]) ].
		self
			assert: (entryCollection entryAtPoint: point ifNone: [ nil ])
			identicalTo: (hits ifEmpty: [ nil ] ifNotEmpty: [ hits first ]) ]
]

{ #category : 'tests' }
RTCollectionTest >> testEntryAtPointSatisfyingIfNone [
	| box |
	box := RTreeBox new size: 10; model: 1; entryIndex: 1; yourself.
	self assert: (entryCollection entryAtPoint: 5 @ 5 satisfying: [ :each | true ] ifNone: [ #none ]) equals: #none.
	entryCollection add: box.
	self assert: (entryCollection entryAtPoint: 5 @ 5 satisfying: [ :each | true ] ifNone: [ #none ]) identicalTo: box.
	self assert: (entryCollection entryAtPoint: 5 @ 5 satisfying: [ :each | false ] ifNone: [ #none ]) equals: #none.
	self assert: (entryCollection entryAtPoint: 50 @ 5 satisfying: [ :each | true ] ifNone: [ #none ]) equals: #none
]

{ #category : 'tests' }
RTCollectionTest >> testBounds [
	| boxes union |
	self assert: entryCollection bounds isNil.
	boxes := (1 to: 200) collect: [ :i |
		RTreeBox new
			position: ((i * 37 \\ 101) - 50) @ (i * 53 \\ 97);
			extent: (i \\ 7 + 1) @ (i \\ 5 + 2);
			entryIndex: i;
			yourself ].
	union := [ :entries | Rectangle merging: (entries collect: [ :each | each encompassingRectangle ]) ].
	entryCollection add: boxes first.
	self assert: entryCollection bounds equals: boxes first encompassingRectangle.
	entryCollection addAll: boxes allButFirst.
	self assert: entryCollection bounds equals: (union value: boxes).
	"removing the entries on the border shrinks the bounds"
	(boxes select: [ :each | each position x < -40 or: [ each position y > 90 ] ])
		do: [ :each | entryCollection remove: each ].
	self assert: entryCollection bounds equals: (union value: entryCollection asArray).
	boxes first
		position: 1000 @ -1000;
		resetEncompassingRectangle.
	entryCollection updateEntry: boxes first.
	self assert: entryCollection bounds equals: (union value: entryCollection asArray).
	entryCollection removeAll.
	self assert: entryCollection bounds isNil
]

{ #category : 'tests' }
RTCollectionTest >> testBoundsOfEntriesThatAreNotFinite [
	| box infinite nan bounds |
	box := RTreeBox new size: 10; entryIndex: 1; yourself.
	infinite := RTreeBox new position: 5 @ 5; extent: Float infinity @ 1; entryIndex: 2; yourself.
	nan := RTreeBox new position: Float nan @ 5; extent: 1 @ 1; entryIndex: 3; yourself.
	entryCollection add: box; add: infinite.
	self assert: entryCollection bounds equals: (0 @ 0 corner: Float infinity @ 10).
	entryCollection add: nan.
	bounds := entryCollection bounds.
	self assert: bounds origin x isNaN.
	self deny: ((-1000 @ -1000 corner: 1000 @ 1000) containsRect: bounds).
	entryCollection remove: nan; remove: infinite.
	self assert: entryCollection bounds equals: box encompassingRectangle
]

{ #category : 'helpers' }
RTCollectionTest >> integerBoxes: count seed: seed [
	"boxes on integer coordinates, so that borders and distances coincide often; some have no
	width or no height. The entryIndex is the order of the list"
	| random |
	random := Random seed: seed.
	^ (1 to: count) collect: [ :i |
		RTreeBox new
			model: i;
			entryIndex: i;
			position: (random next * 400) rounded @ (random next * 400) rounded;
			extent: (i \\ 10 = 0 ifTrue: [ 0 ] ifFalse: [ (random next * 40) rounded ])
				@ (i \\ 15 = 0 ifTrue: [ 0 ] ifFalse: [ (random next * 40) rounded ]);
			yourself ]
]

{ #category : 'tests' }
RTCollectionTest >> testEntriesInside [
	| boxes random queries |
	boxes := self integerBoxes: 300 seed: 51.
	entryCollection addAll: boxes.
	random := Random seed: 52.
	queries := (1 to: 100) collect: [ :i |
		((random next * 400) rounded @ (random next * 400) rounded)
			extent: (random next * 200) rounded @ (random next * 200) rounded ].
	queries := queries , ((boxes first: 30) collect: [ :each | each encompassingRectangle ]).
	queries := queries , { -1000 @ -1000 corner: 1000 @ 1000. 0 @ 0 corner: 0 @ 0 }.
	queries do: [ :query |
		self
			assert: (entryCollection entriesInside: query) asArray
			equals: (boxes select: [ :each | query containsRect: each encompassingRectangle ]) asArray ].
	boxes do: [ :each | entryCollection remove: each ].
	self assert: (entryCollection entriesInside: queries last) isEmpty
]

{ #category : 'tests' }
RTCollectionTest >> testEntriesInsideWithEntriesThatAreNotFinite [
	| box infinite nan everything |
	box := RTreeBox new size: 10; entryIndex: 1; yourself.
	infinite := RTreeBox new position: 5 @ 5; extent: Float infinity @ 1; entryIndex: 2; yourself.
	nan := RTreeBox new position: Float nan @ 5; extent: 1 @ 1; entryIndex: 3; yourself.
	entryCollection add: box; add: infinite; add: nan.
	self assert: (entryCollection entriesInside: (-1 @ -1 corner: 100 @ 100)) asArray equals: { box }.
	everything := Float negativeInfinity @ Float negativeInfinity corner: Float infinity @ Float infinity.
	self assert: (entryCollection entriesInside: everything) asArray equals: { box. infinite }
]

{ #category : 'tests' }
RTCollectionTest >> testEntriesNear [
	"against brute force: by distance, then the topmost first"
	| boxes random points squaredDistance |
	boxes := self integerBoxes: 300 seed: 53.
	entryCollection addAll: boxes.
	random := Random seed: 54.
	points := (1 to: 60) collect: [ :i | (random next * 500 - 50) rounded @ (random next * 500 - 50) rounded ].
	points := points , ((boxes first: 10) collect: [ :each | each encompassingRectangle corner ]).
	squaredDistance := [ :point :rectangle | | dx dy |
		dx := (rectangle origin x - point x max: 0) max: point x - rectangle corner x.
		dy := (rectangle origin y - point y max: 0) max: point y - rectangle corner y.
		dx * dx + (dy * dy) ].
	points do: [ :point | | all |
		all := (boxes collect: [ :each | (squaredDistance value: point value: each encompassingRectangle) -> each ])
			asSortedCollection: [ :a :b | a key < b key or: [ a key = b key and: [ a value entryIndex > b value entryIndex ] ] ].
		#( 0 3 25 100 ) , { Float infinity } do: [ :distance |
			self
				assert: (entryCollection entriesNear: point within: distance) asArray
				equals: ((all select: [ :each | each key <= (distance * distance) ]) collect: [ :each | each value ]) asArray ].
		self assert: (entryCollection nearestEntryTo: point) identicalTo: all first value.
		self assert: (entryCollection entriesNear: point within: -1) isEmpty ]
]

{ #category : 'tests' }
RTCollectionTest >> testNearestEntryOfEmptyCollection [
	| box |
	self assert: (entryCollection nearestEntryTo: 0 @ 0 ifNone: [ #none ]) equals: #none.
	self should: [ entryCollection nearestEntryTo: 0 @ 0 ] raise: Error.
	self assert: (entryCollection entriesNear: 0 @ 0 within: Float infinity) isEmpty.
	box := RTreeBox new position: 10 @ 10; size: 5; entryIndex: 1; yourself.
	entryCollection add: box.
	self assert: (entryCollection nearestEntryTo: 0 @ 0) identicalTo: box.
	self assert: (entryCollection entriesNear: 0 @ 0 within: 14) isEmpty.
	self assert: (entryCollection entriesNear: 0 @ 0 within: 15) asArray equals: { box }.
	box position: Float nan @ 10; resetEncompassingRectangle.
	entryCollection remove: box; add: box.
	self assert: (entryCollection nearestEntryTo: 0 @ 0 ifNone: [ #none ]) equals: #none
]

