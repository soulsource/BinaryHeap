import BinaryHeap.CompleteTree.Basic
import BinaryHeap.HeapPredicate

namespace BinaryHeap.CompleteTree

theorem emptyIsHeap {α : Type u} (le : α → α → Bool) : HeapPredicate CompleteTree.empty le := True.intro
