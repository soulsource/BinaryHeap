import BinaryHeap.CompleteTree.Basic
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

/-- Helper to rw away right, because Lean 4.9 makes it unnecessarily hard to deal with match in tactics mode... -/
theorem CompleteTree.right_unfold {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α p) (h₁ : p ≤ o) (h₂ : o < 2 * (p + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : o + p + 1 > 0): (CompleteTree.branch v l r h₁ h₂ h₃).right h₄ = r := rfl

theorem CompleteTree.heqSameLeftLen {α : Type u} {n m : Nat} {a : CompleteTree α n} {b : CompleteTree α m} (h₁ : n = m) (h₂ : n > 0) (h₃ : HEq a b) : a.leftLen h₂ = b.leftLen (h₁.subst h₂) := by
  subst n
  have h₃ : a = b := eq_of_heq h₃
  subst a
  rfl

theorem CompleteTree.heqSameRightLen {α : Type u} {n m : Nat} {a : CompleteTree α n} {b : CompleteTree α m} (h₁ : n = m) (h₂ : n > 0) (h₃ : HEq a b) : a.rightLen h₂ = b.rightLen (h₁.subst h₂) := by
  subst n
  have h₃ : a = b := eq_of_heq h₃
  subst a
  rfl
