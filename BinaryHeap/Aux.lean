/-
  This file contains some additional functions for a Binary Heap. Things that deal with
  converting collections to/from a heap.
-/
import BinaryHeap.Basic

namespace BinaryHeap

def forM [Monad m] (heap : BinaryHeap α le n) (f : α → m PUnit) : m PUnit :=
  match n with
  | .zero => pure ()
  | .succ _ =>
    let a := heap.tree.root' --this is faster than pop here, in case of a break.
    f a >>= λ _ ↦ heap.pop.snd.forM f

instance : ForM m (BinaryHeap α le n) α where
  forM := BinaryHeap.forM

instance : ForIn m (BinaryHeap α le n) α where
  forIn := ForM.forIn

/-- Builds a Binary Heap from a list. -/
def ofList {α : Type u} {le : α → α → Bool} (h₁ : TotalAndTransitiveLe le) (l : List α) : BinaryHeap α le l.length :=
  let rec worker : (l : List α) → {n : Nat} → (BinaryHeap α le n) → (BinaryHeap α le (n + l.length)) := λ (l : List α) {n : Nat} (heap : BinaryHeap α le n) ↦
    match l with
    | [] => heap
    | a :: as => (Nat.add_comm_right n as.length 1).subst rfl ▸ worker as (heap.push a)
  Nat.zero_add l.length ▸ worker l $ BinaryHeap.new h₁

/- Converts the tree to a sorted list. -/
def toList (heap : BinaryHeap α le n) : List α :=
  let rec worker : (l : List α) → {n : Nat} → (BinaryHeap α le n) → List α := λ(l : List α) {n : Nat} (heap : BinaryHeap α le n) ↦
    match n with
    | 0 => l.reverse
    | (_+1) =>
      let (h, hs) := heap.pop
      worker (h :: l) hs
  worker [] heap

private def ofForInAux [ForIn Id ρ α] {le : α → α → Bool} (h₁ : TotalAndTransitiveLe le) (c : ρ) : (h : Nat) ×' BinaryHeap α le h := Id.run do
  let mut r : (h : Nat) ×' BinaryHeap α le h := ⟨0, BinaryHeap.new h₁⟩
  for e in c do
    r := ⟨r.fst.succ, r.snd.push e⟩
  r

/--
  Runs a for-loop over the input collection and creates a heap from it.
  Warning: Only terminates if the ForIn instance you call it with terminates.
  Think of this as a "this doesn't depend on mathlib" alternative to an implementation that uses Traversable
-/
def ofForIn [ForIn Id ρ α] {le : α → α → Bool} (h₁ : TotalAndTransitiveLe le) (c : ρ) : BinaryHeap α le (ofForInAux h₁ c).fst := PSigma.snd $ ofForInAux h₁ c

/--
  Folds over the heap, starting at the smallest element and yielding the elements in ascending order.
-/
def fold (f : α → β → α) (init : α) (heap : BinaryHeap β le n) : α :=
  match n with
  | 0 => init
  | (_+1) =>
    let (a, as) := heap.pop
    as.fold f (f init a)

/--
  Map operation over the heap.
  Unlike the regular map operation, this requires you to supply a new ordering relation for the result type.
  Needs to create a new heap with the mapped values.
-/
def map {α : Type u} {le₀ : α → α → Bool } {β : Type u₁} {le : β → β → Bool} (h₁ : TotalAndTransitiveLe le) (f : α → β) : (h : BinaryHeap α le₀ n) →  BinaryHeap β le n
  | { tree, .. } =>
    -- no need to do this in-order.
    let rec worker : (o p : Nat) → (CompleteTree α o) → (BinaryHeap β le p) → (BinaryHeap β le (p + o)) := λ o p t h ↦
      match o, t with
      | 0, .leaf => h
      | (q+r+1), .branch v left right _ _ _ =>
        let left_result := worker q p left h
        let right_result := worker r (p+q) right left_result
        (Nat.add_assoc _ _ _▸right_result).push (f v)
    (Nat.zero_add _)▸worker n 0 tree $ BinaryHeap.new h₁
