"
based on nil pattern
"
Class {
	#name : 'RTAbstractNode',
	#superclass : 'Object',
	#category : 'RTree-Nodes',
	#package : 'RTree',
	#tag : 'Nodes'
}

{ #category : 'visiting' }
RTAbstractNode >> accept: visitor [
]

{ #category : 'adding' }
RTAbstractNode >> addChild: anRTEntry [
	^ self subclassResponsibility
]

{ #category : 'public' }
RTAbstractNode >> computeHeight [
	^ 0
]

{ #category : 'enumerating' }
RTAbstractNode >> do: aBlock [
]

{ #category : 'accessing' }
RTAbstractNode >> height [
	^ 0
]

{ #category : 'private' }
RTAbstractNode >> indexLeavesIn: aDictionary [
]

{ #category : 'finding/searching' }
RTAbstractNode >> entriesInside: aRectangle list: aCollection [
]

{ #category : 'finding/searching' }
RTAbstractNode >> entriesWithPoint: aPoint do: aBlock [
]

{ #category : 'testing' }
RTAbstractNode >> isBalanced [
	^ true
]

{ #category : 'testing' }
RTAbstractNode >> isEmpty [
	^ true
]

{ #category : 'testing' }
RTAbstractNode >> isNilNode [
	^ false
]

{ #category : 'testing' }
RTAbstractNode >> isTotalBalanced [
	^ true
]

{ #category : 'finding/searching' }
RTAbstractNode >> nodesIntersetcsRectangle: aRectangle list: list [
]

{ #category : 'finding/searching' }
RTAbstractNode >> nodesWithPoint: aPoint list: list [
]

{ #category : 'accessing' }
RTAbstractNode >> parent [
	^ nil
]

{ #category : 'accessing' }
RTAbstractNode >> parent: aNode [
]

{ #category : 'accessing' }
RTAbstractNode >> rectangle [
	^ 0@0 corner: 0@0
]

{ #category : 'finding/searching' }
RTAbstractNode >> searchPath: anObject [
	^ #()
]

{ #category : 'finding/searching' }
RTAbstractNode >> searchPathIgnoringBounds: anObject [
	^ #()
]

{ #category : 'accessing - children' }
RTAbstractNode >> withAllChildren [
	^ #()
]
