import BinaryHeap.CompleteTree.Basic
import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.HeapPredicate

namespace BinaryHeap

def reflexive_le {α : Type u} {le : α → α → Bool} (h₁ : total_le le) (a : α) : le a a := by
  unfold total_le at h₁
  have h₁ := h₁ a a
  cases h₁ <;> assumption

def not_le_imp_le {α : Type u} {le : α → α → Bool} (h₁ : total_le le) : ∀(a b : α), ¬le a b → le b a := by
  intros a b h₂
  have h₁ := h₁ a b
  cases h₁
  . contradiction
  . trivial

/-- Helper to rw away root, because Lean 4.9 makes it unnecessarily hard to deal with match in tactics mode... -/
theorem CompleteTree.root_unfold {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α p) (h₁ : p ≤ o) (h₂ : o < 2 * (p + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : o + p + 1 > 0): (CompleteTree.branch v l r h₁ h₂ h₃).root h₄ = v := rfl

/-- Helper to rw away left, because Lean 4.9 makes it unnecessarily hard to deal with match in tactics mode... -/
theorem CompleteTree.left_unfold {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α p) (h₁ : p ≤ o) (h₂ : o < 2 * (p + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : o + p + 1 > 0): (CompleteTree.branch v l r h₁ h₂ h₃).left h₄ = l := rfl

theorem CompleteTree.leftLen_unfold {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α p) (h₁ : p ≤ o) (h₂ : o < 2 * (p + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : o + p + 1 > 0): (CompleteTree.branch v l r h₁ h₂ h₃).leftLen h₄ = o := rfl

theorem CompleteTree.rightLen_unfold {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α p) (h₁ : p ≤ o) (h₂ : o < 2 * (p + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : o + p + 1 > 0): (CompleteTree.branch v l r h₁ h₂ h₃).rightLen h₄ = p := rfl

/-- Helper to rw away right, because Lean 4.9 makes it unnecessarily hard to deal with match in tactics mode... -/
theorem CompleteTree.right_unfold {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α p) (h₁ : p ≤ o) (h₂ : o < 2 * (p + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : o + p + 1 > 0): (CompleteTree.branch v l r h₁ h₂ h₃).right h₄ = r := rfl

theorem CompleteTree.contains_unfold {α : Type u} {o p : Nat} (element : α) (v : α) (l : CompleteTree α o) (r : CompleteTree α p) (h₁ : p ≤ o) (h₂ : o < 2 * (p + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) : (CompleteTree.branch v l r h₁ h₂ h₃).contains element = (v=element ∨ l.contains element ∨ r.contains element) := rfl

theorem CompleteTree.contains_as_root_left_right {α : Type u} {n : Nat} (tree : CompleteTree α n) (element : α) (h₁ : n > 0) : tree.contains element = (tree.root h₁ = element ∨ (tree.left h₁).contains element ∨ (tree.right h₁).contains element) := by
  unfold root
  match n, tree with
  | (_+_), .branch v l r _ _ _=>
    simp[left_unfold, right_unfold]
    rfl


theorem CompleteTree.heqSameLeftLen {α : Type u} {n m : Nat} {a : CompleteTree α n} {b : CompleteTree α m} (h₁ : n = m) (h₂ : n > 0) (h₃ : HEq a b) : a.leftLen h₂ = b.leftLen (h₁.subst h₂) := by
  subst n
  have h₃ : a = b := eq_of_heq h₃
  congr

theorem CompleteTree.heqSameRightLen {α : Type u} {n m : Nat} {a : CompleteTree α n} {b : CompleteTree α m} (h₁ : n = m) (h₂ : n > 0) (h₃ : HEq a b) : a.rightLen h₂ = b.rightLen (h₁.subst h₂) := by
  subst n
  have h₃ : a = b := eq_of_heq h₃
  congr

theorem CompleteTree.heqSameRoot {α : Type u} {n m : Nat} {a : CompleteTree α n} {b : CompleteTree α m} (h₁ : n = m) (h₂ : n > 0) (h₃ : HEq a b) : a.root h₂ = b.root (h₁.subst h₂) := by
  subst n
  have h₃ : a = b := eq_of_heq h₃
  congr

theorem CompleteTree.heqContains {α : Type u} {n m : Nat} {a : CompleteTree α n} {b : CompleteTree α m} (h₁ : n = m) (h₃ : HEq a b) : ∀(v : α), a.contains v = b.contains v := by
  intro value
  subst m
  have h₃ : a = b := eq_of_heq h₃
  congr

theorem CompleteTree.leftLenLtN {α : Type u} {n : Nat} (tree : CompleteTree α n) (h₁ : n>0) : tree.leftLen h₁ < n := by
  unfold leftLen
  split
  rw[length]
  rename_i o p _ _ _ _ _ _ _
  exact Nat.lt_of_le_of_lt (Nat.le_add_right o p) (Nat.lt_succ_self (o+p))

theorem CompleteTree.rightLenLtN {α : Type u} {n : Nat} (tree : CompleteTree α n) (h₁ : n>0) : tree.rightLen h₁ < n := by
  unfold rightLen
  split
  rw[length]
  rename_i o p _ _ _ _ _ _ _
  exact Nat.lt_of_le_of_lt (Nat.le_add_left p o) (Nat.lt_succ_self (o+p))

theorem CompleteTree.lengthEqLeftRightLenSucc {α : Type u} {n : Nat} (tree : CompleteTree α n) (h₁ : n>0) : tree.length = tree.leftLen h₁ + tree.rightLen h₁ + 1 := by
  unfold leftLen rightLen
  split
  unfold length
  rfl

theorem HeapPredicate.leOrLeaf_transitive (h₁ : transitive_le le) : le a b → HeapPredicate.leOrLeaf le b h → HeapPredicate.leOrLeaf le a h := by
  unfold HeapPredicate.leOrLeaf
  intros h₂ h₃
  rename_i n
  cases n <;> simp
  apply h₁ a b _
  exact ⟨h₂, h₃⟩
