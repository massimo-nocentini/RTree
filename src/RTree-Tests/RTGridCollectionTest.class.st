"
Tests of the tuning and of the segment aware mode of RTGridCollection. RTCollectionTest and RTCollectionPropertyTest test its answers.
"
Class {
	#name : 'RTGridCollectionTest',
	#superclass : 'TestCase',
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'helpers' }
RTGridCollectionTest >> randomSegments: count seed: seed [
	| random |
	random := Random seed: seed.
	^ (1 to: count) collect: [ :i | | from |
		from := (random next * 2000) @ (random next * 2000).
		(RTreeSegmentBox
			from: from
			to: from + (((random next * 1000) - 500) @ ((random next * 1000) - 500))
			halfWidth: 1 + (random next * 3))
				model: i;
				entryIndex: i;
				yourself ]
]

{ #category : 'tests' }
RTGridCollectionTest >> testCellSizeIsTunedFromTheEntries [
	| grid random |
	grid := RTGridCollection new.
	random := Random seed: 1.
	1 to: 1000 do: [ :i |
		grid add: (RTreeBox new
			entryIndex: i;
			position: (random next * 3000) @ (random next * 3000);
			extent: 20 @ 20;
			yourself) ].
	"tuned when the grid had 513 entries: the median side is 20, the mean spacing about 133"
	self assert: (grid cellSize between: 120 and: 145).
	self assert: grid oversizeCount equals: 0.
	grid cellSize: 10.
	self assert: grid cellSize equals: 10.
	self assert: grid size equals: 1000.
	self assert: (grid entriesAtRectangle: (0 @ 0 corner: 3100 @ 3100)) size equals: 1000
]

{ #category : 'tests' }
RTGridCollectionTest >> testLargeEntriesAreOversize [
	| grid boxes |
	boxes := (1 to: 300) collect: [ :i |
		RTreeBox new entryIndex: i; position: (i * 10) @ 0; extent: 10 @ 10; yourself ].
	grid := RTGridCollection new.
	grid bulkLoad: boxes.
	grid add: (RTreeBox new entryIndex: 301; position: 0 @ 0; extent: 3000 @ 3000; yourself).
	self assert: grid oversizeCount equals: 1.
	self assert: (grid entriesAtPoint: 1505 @ 5) size equals: 2.
	grid remove: (grid detect: [ :each | each entryIndex = 301 ]).
	self assert: grid oversizeCount equals: 0
]

{ #category : 'tests' }
RTGridCollectionTest >> testSegmentAwareHitsAreExact [
	"the lines are registered in the cells their segment crosses: no hit is lost"
	| segments grid list random |
	segments := self randomSegments: 2000 seed: 2.
	grid := RTGridCollection new segmentAware: true; yourself.
	grid bulkLoad: segments.
	list := RTSequenceableCollection new.
	list addAll: segments.
	self assert: grid oversizeCount equals: 0.
	random := Random seed: 3.
	1000 timesRepeat: [ | point |
		point := (random next * 2500 - 250) @ (random next * 2500 - 250).
		self assert: (grid entriesAtPoint: point) asArray equals: (list entriesAtPoint: point) asArray ].
	"and after moves"
	(segments first: 500) do: [ :each | | from |
		from := (random next * 2000) @ (random next * 2000).
		each from: from to: from + (300 @ -200) halfWidth: 2.
		grid updateEntry: each ].
	1000 timesRepeat: [ | point |
		point := (random next * 2500 - 250) @ (random next * 2500 - 250).
		self assert: (grid entriesAtPoint: point) asArray equals: (list entriesAtPoint: point) asArray ]
]

{ #category : 'tests' }
RTGridCollectionTest >> testSegmentAwareRectanglesFindTheNearSegments [
	"a rectangle query answers the entries whose rectangle intersects it and whose segment comes
	near it: every line that crosses the rectangle, and no line far from it"
	| segments grid list random |
	segments := self randomSegments: 1000 seed: 4.
	grid := RTGridCollection new segmentAware: true; yourself.
	grid bulkLoad: segments.
	list := RTSequenceableCollection new.
	list addAll: segments.
	random := Random seed: 5.
	100 timesRepeat: [ | window answer all |
		window := ((random next * 2000) @ (random next * 2000)) extent: 200 @ 150.
		answer := grid entriesAtRectangle: window.
		all := list entriesAtRectangle: window.
		self assert: (answer allSatisfy: [ :each | all includes: each ]).
		"the lines through the center of the window cross it"
		(list entriesAtPoint: window center) do: [ :each | self assert: (answer includes: each) ].
		self assert: answer size <= all size ].
	"the segments are registered in fewer cells than their rectangles"
	self
		assert: (segments inject: 0 into: [ :sum :each | sum + (grid itemFor: each) keys size ])
		< (segments inject: 0 into: [ :sum :each | | r | r := each encompassingRectangle. sum + ((r width / grid cellSize) ceiling + 1 * ((r height / grid cellSize) ceiling + 1)) ])
]
