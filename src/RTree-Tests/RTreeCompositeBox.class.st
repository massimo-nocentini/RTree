"
A test entry that holds other entries, like RSComposite in Roassal: its children are in their own collection (in the same coordinates here), and addEntriesIn:position: adds the hits of the children before itself.

With lazyHits, firstEntryAtPoint:satisfying:ifNone: searches the children with the topmost query of their collection instead of collecting every hit.
"
Class {
	#name : 'RTreeCompositeBox',
	#superclass : 'RTreeBox',
	#instVars : [
		'shapeCollection',
		'lazyHits'
	],
	#category : 'RTree-Tests',
	#package : 'RTree-Tests'
}

{ #category : 'adding' }
RTreeCompositeBox >> addEntriesIn: aCollection position: aPoint [
	(self encompassingRectangle containsPoint: aPoint) ifFalse: [ ^ self ].
	aCollection addAll: (self shapeCollection entriesAtPoint: aPoint).
	aCollection add: self
]

{ #category : 'adding' }
RTreeCompositeBox >> addShape: anEntry [
	anEntry
		parent: self;
		entryIndex: self shapeCollection size + 1.
	self shapeCollection add: anEntry.
	^ anEntry
]

{ #category : 'finding/searching' }
RTreeCompositeBox >> firstEntryAtPoint: aPoint satisfying: aBlock ifNone: noneBlock [
	lazyHits == true ifFalse: [
		^ super firstEntryAtPoint: aPoint satisfying: aBlock ifNone: noneBlock ].
	(self encompassingRectangle containsPoint: aPoint) ifFalse: [ ^ noneBlock value ].
	"the children come first, as in addEntriesIn:position:"
	^ self shapeCollection
		entryAtPoint: aPoint
		satisfying: aBlock
		ifNone: [
			(aBlock value: self)
				ifTrue: [ self ]
				ifFalse: [ noneBlock value ] ]
]

{ #category : 'accessing' }
RTreeCompositeBox >> lazyHits: aBoolean [
	lazyHits := aBoolean
]

{ #category : 'accessing' }
RTreeCompositeBox >> shapeCollection [
	^ shapeCollection ifNil: [ shapeCollection := RTSequenceableCollection new ]
]

{ #category : 'accessing' }
RTreeCompositeBox >> shapeCollection: anRTAbstractCollection [
	shapeCollection := anRTAbstractCollection
]
