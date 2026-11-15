"
A randomized differential test of every collection against a brute force model, with fixed seeds.

Each test generates a sequence of operations (adds, removes of present and absent entries, moves, copies, and every kind of query), applies it to the collection and to an OrderedCollection of the live entries, and after every operation compares their size and contents, the answers of the queries, and the invariants of the structure (for RTreeCollection: heights, AVL balance, tight rectangles, parents and the leaf index).

The coordinates are integers, floats, clustered on a few values (many coincident rectangles), negative, or of extreme magnitudes; some rectangles have no width or height.
"
Class {
	#name : 'RTCollectionPropertyTest',
	#superclass : 'ParametrizedTestCase',
	#instVars : [
		'entryCollectionClass',
		'collection',
		'model',
		'boxes',
		'checks'
	],
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'building suites' }
RTCollectionPropertyTest class >> testParameters [
	^ RTCollectionTest testParameters
]

{ #category : 'checking' }
RTCollectionPropertyTest >> assertConsistentAfter: anOperation [
	| contents |
	self assert: collection size equals: model size after: anOperation.
	self assert: collection isEmpty equals: model isEmpty after: anOperation.
	contents := OrderedCollection new.
	collection do: [ :each | contents add: each ].
	self
		assert: (contents collect: [ :each | each model ]) asArray sort
		equals: (model collect: [ :each | each model ]) asArray sort
		after: anOperation.
	"the structure is checked by assert<class name>After:. Walking an RTreeCollection applies its
	pending updates: not after every operation, so that they stay pending across the others"
	(checks \\ 25 = 0 or: [ anOperation first = #copy ]) ifTrue: [ | selector |
		selector := ('assert', collection class name, 'After:') asSymbol.
		(self respondsTo: selector) ifTrue: [ self perform: selector with: anOperation ] ].
	checks := checks + 1
]

{ #category : 'checking' }
RTCollectionPropertyTest >> assert: actual equals: expected after: anOperation [
	actual = expected ifTrue: [ ^ self ].
	self fail: 'after ', anOperation printString, ': ', actual printString, ' instead of ', expected printString
]

{ #category : 'checking' }
RTCollectionPropertyTest >> assertRTNaryTreeCollectionAfter: anOperation [
	"the leaves are at the same depth, the boxes are tight, every node has a parent link, at most
	maxEntries children and at least one, and the records are those of the leaves"
	| depths itemCount walk |
	depths := Set new.
	itemCount := 0.
	walk := nil.
	walk := [ :node :depth |
		self assert: node children size <= collection maxEntries.
		(node == collection root or: [ node children notEmpty ]) ifFalse: [ self fail: 'empty node after ', anOperation printString ].
		node children do: [ :each | self assert: each parent identicalTo: node ].
		node children ifNotEmpty: [
			self
				assert: node asRectangle
				equals: (Rectangle merging: (node children collect: [ :each | each asRectangle ]))
				after: anOperation ].
		node isLeaf
			ifTrue: [
				depths add: depth.
				node children do: [ :each |
					itemCount := itemCount + 1.
					self assert: (collection itemFor: each entry) identicalTo: each.
					self assert: each asRectangle equals: each entry encompassingRectangle after: anOperation ] ]
			ifFalse: [ node children do: [ :each | walk value: each value: depth + 1 ] ] ].
	walk value: collection root value: 1.
	self assert: depths size <= 1 description: 'leaves at different depths'.
	self assert: itemCount equals: collection size - collection outliers size
]

{ #category : 'checking' }
RTCollectionPropertyTest >> assertQuery: anOperation [
	| kind |
	kind := anOperation first.
	kind = #point ifTrue: [ ^ self assertQueryAtPoint: (anOperation second @ anOperation third) ].
	kind = #rectangle ifTrue: [ ^ self assertQueryAtRectangle: (anOperation second @ anOperation third extent: (anOperation at: 4) @ (anOperation at: 5)) ].
	kind = #near ifTrue: [ ^ self assertQueryNear: (anOperation second @ anOperation third) within: (anOperation at: 4) ].
	kind = #bounds ifTrue: [
		^ model
			ifEmpty: [ self assert: collection bounds isNil ]
			ifNotEmpty: [
				self
					assert: collection bounds
					equals: (Rectangle merging: (model collect: [ :each | each encompassingRectangle ])) ] ]
]

{ #category : 'checking' }
RTCollectionPropertyTest >> assertQueryAtPoint: aPoint [
	| expected hits |
	"RTreeBox>>addEntriesIn:position: uses the half open Rectangle>>containsPoint:"
	expected := (model select: [ :each | each encompassingRectangle containsPoint: aPoint ])
		asSortedCollection: [ :a :b | a entryIndex > b entryIndex ].
	hits := collection entriesAtPoint: aPoint.
	self assert: hits asArray equals: expected asArray.
	self
		assert: (collection entryAtPoint: aPoint satisfying: [ :each | each model odd ] ifNone: [ nil ])
		identicalTo: (expected detect: [ :each | each model odd ] ifNone: [ nil ]).
	self
		assert: (collection entryAtPoint: aPoint ifNone: [ nil ])
		identicalTo: (expected ifEmpty: [ nil ] ifNotEmpty: [ expected first ])
]

{ #category : 'checking' }
RTCollectionPropertyTest >> assertQueryAtRectangle: aRectangle [
	self
		assert: (collection entriesAtRectangle: aRectangle) asArray
		equals: ((model select: [ :each | each encompassingRectangle intersects: aRectangle ])
			asSortedCollection: [ :a :b | a entryIndex < b entryIndex ]) asArray.
	self
		assert: (collection entriesInside: aRectangle) asArray
		equals: ((model select: [ :each | aRectangle containsRect: each encompassingRectangle ])
			asSortedCollection: [ :a :b | a entryIndex < b entryIndex ]) asArray
]

{ #category : 'checking' }
RTCollectionPropertyTest >> assertQueryNear: aPoint within: aDistance [
	| all limit |
	limit := aDistance * aDistance.
	all := (model collect: [ :each | (self squaredDistanceFrom: aPoint to: each encompassingRectangle) -> each ])
		asSortedCollection: [ :a :b | a key < b key or: [ a key = b key and: [ a value entryIndex > b value entryIndex ] ] ].
	self
		assert: (collection entriesNear: aPoint within: aDistance) asArray
		equals: ((all select: [ :each | each key <= limit ]) collect: [ :each | each value ]) asArray.
	self
		assert: (collection nearestEntryTo: aPoint ifNone: [ nil ])
		identicalTo: (all ifEmpty: [ nil ] ifNotEmpty: [ all first value ])
]

{ #category : 'checking' }
RTCollectionPropertyTest >> assertRTreeCollectionAfter: anOperation [
	"heights, AVL balance, tight rectangles, parents and the leaf index"
	| aTreeCollection leafCount walk |
	aTreeCollection := collection.
	aTreeCollection root isEmpty ifTrue: [ ^ self ].
	leafCount := 0.
	walk := nil.
	walk := [ :node |
		node isLeaf
			ifTrue: [
				leafCount := leafCount + 1.
				self assert: node height equals: 1.
				self assert: node rectangle equals: node contents encompassingRectangle after: anOperation.
				self assert: (aTreeCollection leaves at: node contents) identicalTo: node ]
			ifFalse: [
				self assert: node left parent identicalTo: node.
				self assert: node right parent identicalTo: node.
				walk value: node left.
				walk value: node right.
				self assert: node height equals: (node left height max: node right height) + 1.
				self assert: node isBalanced equals: true after: anOperation.
				self
					assert: node rectangle
					equals: (node left rectangle merge: node right rectangle)
					after: anOperation ] ].
	walk value: aTreeCollection root.
	self assert: aTreeCollection root parent isNil.
	self assert: aTreeCollection leaves size equals: leafCount
]

{ #category : 'accessing' }
RTCollectionPropertyTest >> entryCollectionClass [
	^ entryCollectionClass
]

{ #category : 'accessing' }
RTCollectionPropertyTest >> entryCollectionClass: aClass [
	entryCollectionClass := aClass
]

{ #category : 'running' }
RTCollectionPropertyTest >> holdsDuplicates [
	"RTSequenceableCollection is a Bag, the others hold an entry once"
	| probe box |
	probe := entryCollectionClass new.
	box := RTreeBox new size: 1; yourself.
	probe add: box; add: box.
	^ probe size = 2
]

{ #category : 'running' }
RTCollectionPropertyTest >> operations: count mode: mode seed: seed duplicates: aBoolean [
	"#(#add id x y w h) #(#duplicate id) #(#remove id) #(#removeAbsent id) #(#move id x y w h) #(#copy)
	#(#point x y) #(#rectangle x y w h) #(#near x y distance) #(#bounds)"
	| random operations live dead nextId coordinate extent pick |
	random := Random seed: seed.
	operations := OrderedCollection new.
	live := OrderedCollection new.
	dead := OrderedCollection new.
	nextId := 0.
	coordinate := [
		mode = #int ifTrue: [ (random next * 1000) floor ] ifFalse: [
		mode = #float ifTrue: [ random next * 1000 ] ifFalse: [
		mode = #cluster ifTrue: [ (random next * 20) floor ] ifFalse: [
		mode = #huge ifTrue: [ (random next - 0.5) * (10.0 raisedTo: (random next * 410) floor - 205) ] ifFalse: [
		(random next * 1000) floor - 500 ] ] ] ] ].
	extent := [
		random next < 0.1 ifTrue: [ 0 ] ifFalse: [
		mode = #float ifTrue: [ random next * 40 ] ifFalse: [
		mode = #cluster ifTrue: [ (random next * 6) floor ] ifFalse: [
		mode = #huge ifTrue: [ random next * (10.0 raisedTo: (random next * 410) floor - 205) ] ifFalse: [
		(random next * 41) floor ] ] ] ] ].
	pick := [ :aCollection | aCollection at: (random next * aCollection size) floor + 1 ].
	1 to: count do: [ :i | | r addLimit removeLimit |
		"grow, then shrink, then mix"
		i < (count * 0.4)
			ifTrue: [ addLimit := 0.5. removeLimit := 0.62 ]
			ifFalse: [
				i < (count * 0.75)
					ifTrue: [ addLimit := 0.12. removeLimit := 0.62 ]
					ifFalse: [ addLimit := 0.3. removeLimit := 0.55 ] ].
		r := random next.
		(r < addLimit or: [ live isEmpty ])
			ifTrue: [
				nextId := nextId + 1.
				live add: nextId.
				operations add: { #add. nextId. coordinate value. coordinate value. extent value. extent value } ]
			ifFalse: [
				r < removeLimit
					ifTrue: [ | id |
						id := pick value: live.
						live remove: id.
						dead add: id.
						operations add: { #remove. id } ]
					ifFalse: [
						r < (removeLimit + 0.15)
							ifTrue: [ operations add: { #move. pick value: live. coordinate value. coordinate value. extent value. extent value } ]
							ifFalse: [
								r < (removeLimit + 0.18)
									ifTrue: [
										dead isEmpty ifFalse: [ operations add: { #removeAbsent. pick value: dead } ].
										(aBoolean and: [ random next < 0.5 ]) ifTrue: [ operations add: { #duplicate. pick value: live } ] ]
									ifFalse: [ | k |
										k := random next.
										k < 0.02 ifTrue: [ operations add: { #copy } ] ifFalse: [
										k < 0.35 ifTrue: [ operations add: { #point. coordinate value. coordinate value } ] ifFalse: [
										k < 0.65 ifTrue: [ operations add: { #rectangle. coordinate value. coordinate value. extent value * 5. extent value * 5 } ] ifFalse: [
										k < 0.95 ifTrue: [ operations add: { #near. coordinate value. coordinate value. random next < 0.2 ifTrue: [ Float infinity ] ifFalse: [ extent value * 3 ] } ] ifFalse: [
										operations add: { #bounds } ] ] ] ] ] ] ] ] ].
	^ operations asArray
]

{ #category : 'running' }
RTCollectionPropertyTest >> replay: operations [
	self reset.
	self apply: operations
]

{ #category : 'running' }
RTCollectionPropertyTest >> reset [
	collection := entryCollectionClass new.
	model := OrderedCollection new.
	boxes := Dictionary new.
	checks := 0
]

{ #category : 'running' }
RTCollectionPropertyTest >> apply: operations [
	operations do: [ :operation | | kind |
		kind := operation first.
		kind = #add ifTrue: [ | box |
			box := RTreeBox new
				model: operation second;
				entryIndex: operation second;
				position: operation third @ (operation at: 4);
				extent: (operation at: 5) @ (operation at: 6);
				yourself.
			boxes at: operation second put: box.
			self assert: (collection add: box) identicalTo: box.
			model add: box ].
		kind = #duplicate ifTrue: [ collection add: (boxes at: operation second) ].
		kind = #remove ifTrue: [ | box |
			box := boxes at: operation second.
			model remove: box.
			self assert: (collection remove: box ifAbsent: [ nil ]) identicalTo: box ].
		kind = #removeAbsent ifTrue: [
			self assert: (collection remove: (boxes at: operation second) ifAbsent: [ #absent ]) equals: #absent ].
		kind = #move ifTrue: [ | box |
			box := boxes at: operation second.
			box
				position: operation third @ (operation at: 4);
				extent: (operation at: 5) @ (operation at: 6).
			[ collection updateEntry: box ] ensure: [ box resetEncompassingRectangle ] ].
		kind = #copy ifTrue: [ | original |
			original := collection.
			collection := collection copy.
			"the copy must not share anything that changes"
			original asArray do: [ :each | original remove: each ] ].
		(#( #point #rectangle #near #bounds ) includes: kind) ifTrue: [ self assertQuery: operation ].
		self assertConsistentAfter: operation ].
	checks := 0.
	self assertConsistentAfter: #( #end )
]

{ #category : 'running' }
RTCollectionPropertyTest >> replayMode: mode seed: seed [
	self replay: (self operations: 1500 mode: mode seed: seed duplicates: self holdsDuplicates not)
]

{ #category : 'private' }
RTCollectionPropertyTest >> squaredDistanceFrom: aPoint to: aRectangle [
	"as RTAbstractCollection computes it, so that the floats round the same"
	| dx dy |
	dx := aPoint x < aRectangle origin x
		ifTrue: [ aRectangle origin x - aPoint x ]
		ifFalse: [ aPoint x > aRectangle corner x ifTrue: [ aPoint x - aRectangle corner x ] ifFalse: [ 0 ] ].
	dy := aPoint y < aRectangle origin y
		ifTrue: [ aRectangle origin y - aPoint y ]
		ifFalse: [ aPoint y > aRectangle corner y ifTrue: [ aPoint y - aRectangle corner y ] ifFalse: [ 0 ] ].
	^ dx * dx + (dy * dy)
]

{ #category : 'tests' }
RTCollectionPropertyTest >> testBulkLoadThenRandomOperations [
	| operations initial |
	operations := self operations: 1500 mode: #float seed: 7 duplicates: false.
	initial := (operations select: [ :each | each first = #add ]) first: 120.
	"the first 120 adds are given to bulkLoad: at once"
	self reset.
	initial do: [ :operation | | box |
		box := RTreeBox new
			model: operation second;
			entryIndex: operation second;
			position: operation third @ (operation at: 4);
			extent: (operation at: 5) @ (operation at: 6);
			yourself.
		boxes at: operation second put: box.
		model add: box ].
	collection bulkLoad: model copy.
	self assertConsistentAfter: #( #bulkLoad ).
	self apply: (operations copyWithoutAll: initial)
]

{ #category : 'tests' }
RTCollectionPropertyTest >> testClusteredCoordinates [
	self replayMode: #cluster seed: 3
]

{ #category : 'tests' }
RTCollectionPropertyTest >> testExtremeCoordinates [
	self replayMode: #huge seed: 4
]

{ #category : 'tests' }
RTCollectionPropertyTest >> testFloatCoordinates [
	self replayMode: #float seed: 2
]

{ #category : 'tests' }
RTCollectionPropertyTest >> testIntegerCoordinates [
	self replayMode: #int seed: 1
]

{ #category : 'tests' }
RTCollectionPropertyTest >> testNegativeCoordinates [
	self replayMode: #neg seed: 5
]
