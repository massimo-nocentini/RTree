"
A test entry that, like a Roassal line, also accepts the points on the border of its rectangle.
"
Class {
	#name : 'RTreeClosedBox',
	#superclass : 'RTreeBox',
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'adding' }
RTreeClosedBox >> addEntriesIn: aCollection position: aPoint [
	| r |
	r := self encompassingRectangle.
	(r origin <= aPoint and: [ aPoint <= r corner ])
		ifTrue: [ aCollection add: self ]
]
