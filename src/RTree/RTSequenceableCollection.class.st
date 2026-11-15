"
Internally uses an OrderedCollection/RSGroup to iterate over the shapes.
This is the reason why is a linear render tree or linear search
"
Class {
	#name : 'RTSequenceableCollection',
	#superclass : 'RTAbstractCollection',
	#instVars : [
		'entries',
		'bounds'
	],
	#category : 'RTree-Collections',
	#package : 'RTree',
	#tag : 'Collections'
}

{ #category : 'adding' }
RTSequenceableCollection >> add: anRTEntry [
	entries add: anRTEntry.
	bounds ifNotNil: [ bounds := self mergeBounds: bounds with: anRTEntry encompassingRectangle ].
	^ anRTEntry
]

{ #category : 'accessing' }
RTSequenceableCollection >> bounds [
	"computed by scanning the entries, then kept until an entry is removed or updated"
	^ bounds ifNil: [ bounds := super bounds ]
]

{ #category : 'enumerating' }
RTSequenceableCollection >> do: aBlock [
	entries do: aBlock
]

{ #category : 'finding/searching' }
RTSequenceableCollection >> entriesAtPoint: position [
	| result |
	result := OrderedCollection new.
	entries reverseDo: [ :entry |
		entry addEntriesIn: result position: position.
	].
	^ result
]

{ #category : 'finding/searching' }
RTSequenceableCollection >> entriesAtRectangle: aRectangle [
	^ entries select: [ :each | each encompassingRectangle intersects: aRectangle ]
]

{ #category : 'finding/searching' }
RTSequenceableCollection >> entryAtPoint: aPoint satisfying: aBlock ifNone: noneBlock [
	"the last entries are drawn on top, as in entriesAtPoint:"
	entries reverseDo: [ :entry |
		(entry firstEntryAtPoint: aPoint satisfying: aBlock ifNone: [ nil ])
			ifNotNil: [ :found | ^ found ] ].
	^ noneBlock value
]

{ #category : 'testing' }
RTSequenceableCollection >> includes: anObject [
	"the entries are a Bag, they match with ="
	^ entries includes: anObject
]

{ #category : 'initialization' }
RTSequenceableCollection >> initialize [
	super initialize.
	entries := OrderedCollection new
]

{ #category : 'testing' }
RTSequenceableCollection >> isEmpty [
	^ entries isEmpty
]

{ #category : 'copying' }
RTSequenceableCollection >> postCopy [
	super postCopy.
	entries := entries copy
]

{ #category : 'shapes - ordering' }
RTSequenceableCollection >> pushBack: anRTEntry [
	entries remove: anRTEntry; addFirst: anRTEntry
]

{ #category : 'shapes - ordering' }
RTSequenceableCollection >> pushFront: anRTEntry [
	entries remove: anRTEntry; add: anRTEntry
]

{ #category : 'removing' }
RTSequenceableCollection >> remove: anRTEntry ifAbsent: anExceptionBlock [
	bounds := nil.
	^ entries remove: anRTEntry ifAbsent: anExceptionBlock
]

{ #category : 'removing' }
RTSequenceableCollection >> removeAll [
	bounds := nil.
	entries removeAll
]

{ #category : 'update' }
RTSequenceableCollection >> updateEntry: anRTEntry [
	bounds := nil.
	anRTEntry resetEncompassingRectangle
]

{ #category : 'update' }
RTSequenceableCollection >> updateEntry: anRTEntry before: anotherRTEntry [
	entries remove: anRTEntry; add: anRTEntry before: anotherRTEntry
]

{ #category : 'accessing' }
RTSequenceableCollection >> size [
	"Collection>>size counts the entries with do:"
	^ entries size
]
