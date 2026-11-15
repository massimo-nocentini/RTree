"
I describe graphic elements with an ecompassing rectangle in its space
"
Trait {
	#name : 'RTEntry',
	#instVars : [
		'entryIndex'
	],
	#category : 'RTree-Traits',
	#package : 'RTree',
	#tag : 'Traits'
}

{ #category : 'adding' }
RTEntry >> addEntriesIn: aCollection position: aPoint [
	self explicitRequirement
]

{ #category : 'accessing' }
RTEntry >> encompassingRectangle [
	^ self explicitRequirement
]

{ #category : 'private' }
RTEntry >> entryIndex [
	^ entryIndex
]

{ #category : 'private' }
RTEntry >> entryIndex: aNumber [
	entryIndex := aNumber
]

{ #category : 'finding/searching' }
RTEntry >> firstEntryAtPoint: aPoint satisfying: aBlock ifNone: noneBlock [
	"The first of the entries that addEntriesIn:position: adds for aPoint that satisfies aBlock.
	The collections ask it to answer entryAtPoint:satisfying:ifNone: without ordering every hit.
	A composite can override it to search its own children with entryAtPoint:satisfying:ifNone:
	before testing itself, the order of addEntriesIn:position:"
	| hits |
	hits := OrderedCollection new.
	self addEntriesIn: hits position: aPoint.
	^ hits detect: aBlock ifNone: noneBlock
]

{ #category : 'accessing - computed' }
RTEntry >> indexesFromRoot [
	"the first element is root element, second its root's children"
	| collection |
	collection := OrderedCollection new.
	self indexesFromRootIn: collection.
	^ collection
]

{ #category : 'accessing - computed' }
RTEntry >> indexesFromRootIn: aCollection [
	| aParent |
	aParent := self parent.
	aParent ifNil: [ ^ self ].

	aParent indexesFromRootIn: aCollection.
	aCollection add: self entryIndex
]

{ #category : 'accessing' }
RTEntry >> parent [
	^ self explicitRequirement
]

{ #category : 'rectangle' }
RTEntry >> resetEncompassingRectangle [
	^ self explicitRequirement
]
