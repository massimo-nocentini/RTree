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
	| m classesToConsider |
	m := ParametrizedTestMatrix new.
	classesToConsider := RTAbstractCollection subclasses.
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

