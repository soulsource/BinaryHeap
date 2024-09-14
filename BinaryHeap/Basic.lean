/-
  This file contains the Binary Heap type and its basic operations.
-/
import BinaryHeap.CompleteTree

abbrev BinaryHeap.TotalAndTransitiveLe (le : α → α → Bool) : Prop := BinaryHeap.transitive_le le ∧ BinaryHeap.total_le le

structure BinaryHeap (α : Type u) (le : α → α → Bool) (n : Nat) where
  tree : BinaryHeap.CompleteTree α n
  valid : BinaryHeap.HeapPredicate tree le
  wellDefinedLe : BinaryHeap.TotalAndTransitiveLe le
deriving Repr

namespace BinaryHeap

/-- Creates an empty heap. O(1) -/
def new {α : Type u} {le : α → α → Bool} (h₁ : TotalAndTransitiveLe le) : BinaryHeap α le 0 :=
  {
    tree := CompleteTree.empty,
    valid := CompleteTree.emptyIsHeap le
    wellDefinedLe := h₁
  }

/-- Adds an element into a heap. O(log(n)) -/
def push {α : Type u} {le : α → α → Bool} {n : Nat} : α → BinaryHeap α le n → BinaryHeap α le (n+1)
| elem, .mk tree valid wellDefinedLe =>
  let valid := tree.heapPushIsHeap valid wellDefinedLe.left wellDefinedLe.right
  let tree := tree.heapPush le elem
  {tree, valid, wellDefinedLe}

/-- Removes the smallest element from the heap and returns it. O(log(n)) -/
def pop {α : Type u} {le : α → α → Bool} {n : Nat} : (BinaryHeap α le (n+1)) → (α × BinaryHeap α le n)
| {tree, valid, wellDefinedLe} =>
  let result := tree.heapPop le
  let resultValid := CompleteTree.heapPopIsHeap le tree valid wellDefinedLe
  (result.fst, { tree := result.snd, valid := resultValid, wellDefinedLe})

/-- Removes the element at the given (depth-first) index from the heap and returns it. O(log(n)) -/
def removeAt {α : Type u} {le : α → α → Bool} {n : Nat} : (BinaryHeap α le (n+1)) → (Fin (n+1)) → (α × BinaryHeap α le n)
| {tree, valid, wellDefinedLe}, index =>
  let result := tree.heapRemoveAt le index
  let resultValid := CompleteTree.heapRemoveAtIsHeap le index tree valid wellDefinedLe
  (result.fst, { tree := result.snd, valid := resultValid, wellDefinedLe})

/-- Updates the element at the given (depth-first) index and returns its previous value. O(log(n)) -/
def updateAt {α : Type u} {le : α → α → Bool} {n : Nat} : (BinaryHeap α le n) → (Fin n) → α → (BinaryHeap α le n × α)
| {tree, valid, wellDefinedLe}, index, value =>
  let result := tree.heapUpdateAt le index value
  let resultValid := CompleteTree.heapUpdateAtIsHeap le index value tree valid wellDefinedLe.left wellDefinedLe.right
  ({ tree := result.fst, valid := resultValid, wellDefinedLe}, result.snd)

/-- Searches for an element in the heap and returns its index. **O(n)** -/
def indexOf {α : Type u} {le : α → α → Bool} {n : Nat} : BinaryHeap α le n → (pred : α → Bool) → Option (Fin n)
| {tree, valid := _, wellDefinedLe := _}, pred =>
  tree.indexOf pred

instance : GetElem (BinaryHeap α le n) (Nat) α (λ _ index ↦ index < n) where
  getElem := λ heap index h₁ ↦ heap.tree.get ⟨index, h₁⟩

instance : GetElem (BinaryHeap α le n) (Fin n) α (λ _ _ ↦ True) where
  getElem := λ heap index _ ↦ heap.tree.get index
