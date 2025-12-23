# BinaryHeap

This is a toy project, with the goal to formally prove a binary heap implementation.

# MOVED

This repo is no longer updated. The current version can be found at [https://git.grois.info/BinaryHeap/](https://git.grois.info/BinaryHeap/).

# Goal

The original goal of this project was to implement a heap more or less by the book, and to show that its properties are upheld. This means, that the data is stored in a complete tree, and that the usual functions (push, pop, update) conserve the heap predicate.

## Additional Goals

While initially not within the scope of the project, it would be nice to show that not only the heap property and the completeness of the tree are conserved, but also that the functions do what they claim to do. The work on this has (at the time of writing) just started, and I do not give any guarantees that it will ever be completed. Feel free to contribute though.

Another thing that might happen are performance improvements, by showing that the current linked-tree structure is equivalent to the traditional array representation of a heap, and by showing that tail recursive versions of the functions are equivalent to them.

# Limitations (READ THIS!)

As this is a toy project, performance has not been considered important up to now. This means that the data is stored in a linked-tree, and that the functions aren't tail recursive. While I consider it highly unlikely that recursion depth is going to ever be an issue, given that it scales logarithmically with the element count, the linked-tree structure probably is, due to non-locality of the data.

So, you probably **do not** want to **use this code in a production project**. Feel free to use it as a basis for a more efficient implementation though.

# Implementation Details

The BinaryHeap (and its underlying CompleteTree) data type is an indexed family. It has the number of elements in the heap as part of its type. I am pretty sure the way it is currently written has a runtime overhead... The completeness property is passed as additional parameters to the tree's branch constructor.

The heap itself is a sigma type, with the heap predicate proof as part of its fields. In addition it stores properties about the less-than-or-equal relation.
