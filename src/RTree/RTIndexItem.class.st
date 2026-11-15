"
The record a spatial index keeps for one entry: the rectangle the entry was indexed with (so that removing it never depends on its current rectangle), the entry, and where the index keeps it: the parent is the leaf of RTNaryTreeCollection or the node of RTLooseQuadtreeCollection, the keys are the cells of RTGridCollection. The stamp marks the item as seen by the current query of a grid.
"
Class {
	#name : 'RTIndexItem',
	#superclass : 'RTIndexBox',
	#instVars : [
		'entry',
		'keys',
		'stamp'
	],
	#category : 'RTree-Nodes',
	#package : 'RTree',
	#tag : 'Nodes'
}

{ #category : 'instance creation' }
RTIndexItem class >> on: anRTEntry rectangle: aRectangle [
	^ self new
		setEntry: anRTEntry rectangle: aRectangle;
		yourself
]

{ #category : 'instance creation' }
RTIndexItem class >> on: anRTEntry left: left top: top right: right bottom: bottom [
	^ self new
		setEntry: anRTEntry left: left top: top right: right bottom: bottom;
		yourself
]

{ #category : 'accessing' }
RTIndexItem >> entry [
	^ entry
]

{ #category : 'accessing' }
RTIndexItem >> keys [
	^ keys
]

{ #category : 'accessing' }
RTIndexItem >> keys: anArrayOrNil [
	keys := anArrayOrNil
]

{ #category : 'initialization' }
RTIndexItem >> setEntry: anRTEntry left: aLeft top: aTop right: aRight bottom: aBottom [
	entry := anRTEntry.
	stamp := 0.
	self setLeft: aLeft top: aTop right: aRight bottom: aBottom
]

{ #category : 'initialization' }
RTIndexItem >> setEntry: anRTEntry rectangle: aRectangle [
	entry := anRTEntry.
	stamp := 0.
	self setRectangle: aRectangle
]

{ #category : 'accessing' }
RTIndexItem >> stamp [
	^ stamp
]

{ #category : 'accessing' }
RTIndexItem >> stamp: anInteger [
	stamp := anInteger
]
