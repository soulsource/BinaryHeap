/-
  This file contains the Binary Heap type and its basic operations.
-/
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
def push {α : Type u} {le : α → α → Bool} {n : Nat} : α → BinaryHeap α le n → BinaryHeap α le (n+1)
| elem, .mk tree valid wellDefinedLe =>
  let valid := tree.heapPushIsHeap valid wellDefinedLe.left wellDefinedLe.right
  let tree := tree.heapPush le elem
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

instance : GetElem (BinaryHeap α le n) (Nat) α (λ _ index ↦ index < n) where
  getElem := λ heap index h₁ ↦ match n, heap, index with
  | (_+1), {tree, ..}, index => tree.get' ⟨index, h₁⟩

instance : GetElem (BinaryHeap α le n) (Fin n) α (λ _ _ ↦ n > 0) where
  getElem := λ heap index _ ↦ match n, heap, index with
  | (_+1), {tree, ..}, index => tree.get' index

/--Helper for the common case of using natural numbers for sorting.-/
theorem nat_ble_to_heap_le_total : total_le Nat.ble :=
  λa b ↦ Nat.ble_eq.substr $ Nat.ble_eq.substr (Nat.le_total a b)

/--Helper for the common case of using natural numbers for sorting.-/
theorem nat_ble_to_heap_transitive_le : transitive_le Nat.ble :=
  λ a b c ↦
    Nat.le_trans (n := a) (m := b) (k := c)
    |> Nat.ble_eq.substr
    |> Nat.ble_eq.substr
    |> Nat.ble_eq.substr
    |> and_imp.mpr
