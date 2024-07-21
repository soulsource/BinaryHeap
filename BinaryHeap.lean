import BinaryHeap.CompleteTree

structure BinaryHeap (α : Type u) (le : α → α → Bool) (n : Nat) where
  tree : BinaryHeap.CompleteTree α n
  valid : BinaryHeap.HeapPredicate tree le
  wellDefinedLe : BinaryHeap.transitive_le le ∧ BinaryHeap.total_le le
deriving Repr

namespace BinaryHeap

/-- Creates an empty heap. O(1) -/
def new (α : Type u) {le : α → α → Bool} (h₁ : BinaryHeap.transitive_le le) (h₂ : BinaryHeap.total_le le) : BinaryHeap α le 0 :=
  {
    tree := CompleteTree.empty,
    valid := CompleteTree.emptyIsHeap le
    wellDefinedLe := ⟨h₁,h₂⟩
  }

/-- Adds an element into a heap. O(log(n)) -/
def push {α : Type u} {lt : α → α → Bool} {n : Nat} : α → BinaryHeap α lt n → BinaryHeap α lt (n+1)
| elem, .mk tree valid wellDefinedLe =>
  let valid := tree.heapPushIsHeap valid wellDefinedLe.left wellDefinedLe.right
  let tree := tree.heapPush lt elem
  {tree, valid, wellDefinedLe}

/-- Removes the smallest element from the heap and returns it. O(log(n)) -/
def pop {α : Type u} {le : α → α → Bool} {n : Nat} : (BinaryHeap α le (n+1)) → (BinaryHeap α le n × α)
| {tree, valid, wellDefinedLe} =>
  let result := tree.heapPop le
  let resultValid := CompleteTree.heapPopIsHeap le tree valid wellDefinedLe
  ({ tree := result.fst, valid := resultValid, wellDefinedLe}, result.snd)

/-- Removes the element at the given (depth-first) index from the heap and returns it. O(log(n)) -/
def removeAt {α : Type u} {le : α → α → Bool} {n : Nat} : (BinaryHeap α le (n+1)) → (Fin (n+1)) → (BinaryHeap α le n × α)
| {tree, valid, wellDefinedLe}, index =>
  let result := tree.heapRemoveAt le index
  let resultValid := CompleteTree.heapRemoveAtIsHeap le index tree valid wellDefinedLe
  ({ tree := result.fst, valid := resultValid, wellDefinedLe}, result.snd)

/-- Updates the element at the given (depth-first) index and returns its previous value. O(log(n)) -/
def updateAt {α : Type u} {le : α → α → Bool} {n : Nat} : (BinaryHeap α le (n+1)) → (Fin (n+1)) → α → (BinaryHeap α le (n+1) × α)
| {tree, valid, wellDefinedLe}, index, value =>
  let result := tree.heapUpdateAt le index value $ Nat.succ_pos n
  let resultValid := CompleteTree.heapUpdateAtIsHeap le index value tree _ valid wellDefinedLe.left wellDefinedLe.right
  ({ tree := result.fst, valid := resultValid, wellDefinedLe}, result.snd)

/-- Searches for an element in the heap and returns its index. **O(n)** -/
def indexOf {α : Type u} {le : α → α → Bool} {n : Nat} : BinaryHeap α le (n+1) → (pred : α → Bool) → Option (Fin (n+1))
| {tree, valid := _, wellDefinedLe := _}, pred =>
  tree.indexOf pred
