"
A test entry like a Roassal line: a straight segment thickened by a half width. It accepts the points at most the half width from the segment, and answers the segment in spatialSegment.
"
Class {
	#name : 'RTreeSegmentBox',
	#superclass : 'RTreeBox',
	#instVars : [
		'from',
		'to',
		'halfWidth'
	],
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'instance creation' }
RTreeSegmentBox class >> from: aPoint to: anotherPoint halfWidth: aNumber [
	^ self new
		from: aPoint to: anotherPoint halfWidth: aNumber;
		yourself
]

{ #category : 'adding' }
RTreeSegmentBox >> addEntriesIn: aCollection position: aPoint [
	| dx dy length2 t nearest |
	dx := to x - from x.
	dy := to y - from y.
	length2 := dx * dx + (dy * dy).
	t := length2 = 0
		ifTrue: [ 0 ]
		ifFalse: [ (((aPoint x - from x) * dx + ((aPoint y - from y) * dy)) / length2 max: 0) min: 1 ].
	nearest := (from x + (t * dx)) @ (from y + (t * dy)).
	(aPoint distanceTo: nearest) <= halfWidth ifTrue: [ aCollection add: self ]
]

{ #category : 'accessing' }
RTreeSegmentBox >> encompassingRectangle [
	^ rectangle ifNil: [
		rectangle := ((from min: to) - halfWidth) corner: ((from max: to) + halfWidth) ]
]

{ #category : 'initialization' }
RTreeSegmentBox >> from: aPoint to: anotherPoint halfWidth: aNumber [
	from := aPoint.
	to := anotherPoint.
	halfWidth := aNumber.
	rectangle := nil
]

{ #category : 'accessing' }
RTreeSegmentBox >> spatialSegment [
	^ { from. to. halfWidth }
]
