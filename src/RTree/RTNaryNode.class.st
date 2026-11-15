"
A node of RTNaryTreeCollection: up to maxEntries children, the RTIndexItems of the entries in a leaf, other nodes otherwise. Its box is the union of the boxes of its children.
"
Class {
	#name : 'RTNaryNode',
	#superclass : 'RTIndexBox',
	#instVars : [
		'children',
		'isLeaf'
	],
	#category : 'RTree-Nodes',
	#package : 'RTree',
	#tag : 'Nodes'
}

{ #category : 'instance creation' }
RTNaryNode class >> newLeaf: aBoolean [
	^ self new
		setLeaf: aBoolean;
		yourself
]

{ #category : 'adding' }
RTNaryNode >> addChild: aBox [
	children add: aBox.
	aBox parent: self
]

{ #category : 'private' }
RTNaryNode >> bestChildFor: aBox [
	"the child whose area grows the least, the smaller one on a tie (ChooseSubtree of Guttman)"
	| best bestEnlargement bestArea boxLeft boxTop boxRight boxBottom |
	boxLeft := aBox left.
	boxTop := aBox top.
	boxRight := aBox right.
	boxBottom := aBox bottom.
	children do: [ :each | | area enlargement |
		area := each area.
		enlargement := ((each right max: boxRight) - (each left min: boxLeft))
			* ((each bottom max: boxBottom) - (each top min: boxTop)) - area.
		(best isNil or: [ enlargement < bestEnlargement or: [ enlargement = bestEnlargement and: [ area < bestArea ] ] ])
			ifTrue: [
				best := each.
				bestEnlargement := enlargement.
				bestArea := area ] ].
	^ best
]

{ #category : 'accessing' }
RTNaryNode >> children [
	^ children
]

{ #category : 'finding/searching' }
RTNaryNode >> entriesAtX: x y: y do: aBlock [
	"the entries below whose box holds x @ y, borders included"
	isLeaf
		ifTrue: [
			children do: [ :each |
				(each left <= x and: [ x <= each right and: [ each top <= y and: [ y <= each bottom ] ] ])
					ifTrue: [ aBlock value: each entry ] ] ]
		ifFalse: [
			children do: [ :each |
				(each left <= x and: [ x <= each right and: [ each top <= y and: [ y <= each bottom ] ] ])
					ifTrue: [ each entriesAtX: x y: y do: aBlock ] ] ]
]

{ #category : 'finding/searching' }
RTNaryNode >> entriesTouchingLeft: aLeft top: aTop right: aRight bottom: aBottom do: aBlock [
	"the entries below whose box meets the closed rectangle"
	isLeaf
		ifTrue: [
			children do: [ :each |
				(each left <= aRight and: [ aLeft <= each right and: [ each top <= aBottom and: [ aTop <= each bottom ] ] ])
					ifTrue: [ aBlock value: each entry ] ] ]
		ifFalse: [
			children do: [ :each |
				(each left <= aRight and: [ aLeft <= each right and: [ each top <= aBottom and: [ aTop <= each bottom ] ] ])
					ifTrue: [ each entriesTouchingLeft: aLeft top: aTop right: aRight bottom: aBottom do: aBlock ] ] ]
]

{ #category : 'initialization' }
RTNaryNode >> initialize [
	super initialize.
	children := OrderedCollection new.
	isLeaf := true.
	self setEmpty
]

{ #category : 'testing' }
RTNaryNode >> isLeaf [
	^ isLeaf
]

{ #category : 'enumerating' }
RTNaryNode >> itemsDo: aBlock [
	isLeaf
		ifTrue: [ children do: aBlock ]
		ifFalse: [ children do: [ :each | each itemsDo: aBlock ] ]
]

{ #category : 'enumerating' }
RTNaryNode >> nodesDo: aBlock [
	aBlock value: self.
	isLeaf ifFalse: [ children do: [ :each | each nodesDo: aBlock ] ]
]

{ #category : 'operations' }
RTNaryNode >> recomputeBox [
	"the union of the boxes of the children. Answer whether it changed"
	| oldLeft oldTop oldRight oldBottom |
	oldLeft := left.
	oldTop := top.
	oldRight := right.
	oldBottom := bottom.
	self setEmpty.
	children do: [ :each | self mergeBox: each ].
	^ (oldLeft = left and: [ oldTop = top and: [ oldRight = right and: [ oldBottom = bottom ] ] ]) not
]

{ #category : 'removing' }
RTNaryNode >> removeChild: aBox [
	children remove: aBox.
	aBox parent: nil
]

{ #category : 'initialization' }
RTNaryNode >> setChildren: aCollection [
	children := OrderedCollection withAll: aCollection.
	children do: [ :each | each parent: self ]
]

{ #category : 'initialization' }
RTNaryNode >> setLeaf: aBoolean [
	isLeaf := aBoolean
]
