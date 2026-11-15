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
	the order of the candidates that share an index. The same order is followed here, lazily:
	the topmost candidate is usually the answer, the others are sorted only when it is not"
	| best bestIndex rest |
	candidates isEmpty ifTrue: [ ^ noneBlock value ].
	best := 1.
	bestIndex := (candidates at: 1) entryIndex ifNil: [ 0 ].
	2 to: candidates size do: [ :i | | index |
		index := (candidates at: i) entryIndex ifNil: [ 0 ].
		index > bestIndex ifTrue: [
			best := i.
			bestIndex := index ] ].
	((candidates at: best) firstEntryAtPoint: aPoint satisfying: aBlock ifNone: [ nil ])
		ifNotNil: [ :found | ^ found ].
	candidates size = 1 ifTrue: [ ^ noneBlock value ].
	rest := OrderedCollection new: candidates size - 1.
	candidates doWithIndex: [ :each :i | i = best ifFalse: [ rest add: each ] ].
	"a stable sort, as in entriesAtPoint:"
	rest sort: [ :a :b | (a entryIndex ifNil: [ 0 ]) >= (b entryIndex ifNil: [ 0 ]) ].
	rest do: [ :each |
		(each firstEntryAtPoint: aPoint satisfying: aBlock ifNone: [ nil ])
			ifNotNil: [ :found | ^ found ] ].
	^ noneBlock value
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
