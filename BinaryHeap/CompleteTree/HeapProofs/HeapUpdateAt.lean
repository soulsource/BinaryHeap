import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.Lemmas
import BinaryHeap.CompleteTree.NatLemmas
import BinaryHeap.CompleteTree.HeapProofs.HeapUpdateRoot

namespace BinaryHeap.CompleteTree

private theorem heapUpdateAtIsHeapLeRootAux_RootLeValue {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) (h₁ : HeapPredicate heap le) (h₂ : n > 0) (h₃ : le (root heap h₂) value) (h₄ : total_le le) : HeapPredicate.leOrLeaf le (root heap h₂) (heapUpdateAt le index value heap).fst := by
  unfold heapUpdateAt heapUpdateAtAux
  split
  case isTrue => exact CompleteTree.heapUpdateRootIsHeapLeRootAux le value heap h₁ h₂ h₃
  case isFalse hi =>
    generalize heapUpdateAt.proof_1 index = h₂
    split
    rename_i o p v l r h₆ h₇ h₈ index h₁ h₅
    cases h₉ : le v value <;> simp (config := { ground := true }) only
    case false => rw[root_unfold] at h₃; exact absurd h₃ ((Bool.not_eq_true (le v value)).substr h₉)
    case true =>
      rw[root_unfold]
      split
      <;> simp![reflexive_le, h₄]

private theorem heapUpdateAtIsHeapLeRootAux_ValueLeRoot {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) (h₁ : HeapPredicate heap le) (h₂ : n > 0) (h₃ : le value (root heap h₂)) (h₄ : total_le le) (h₅ : transitive_le le) : HeapPredicate.leOrLeaf le value (heapUpdateAt le index value heap).fst := by
  unfold heapUpdateAt heapUpdateAtAux
  generalize heapUpdateAt.proof_1 index = h₂
  split
  <;> rename_i h₉
  case isTrue =>
    unfold heapUpdateRoot
    split
    rename_i o p v l r h₆ h₇ h₈ h₂
    cases o <;> cases p <;> simp only [↓reduceDIte,HeapPredicate.leOrLeaf, root_unfold, h₄, reflexive_le]
    <;> unfold HeapPredicate at h₁
    <;> have h₁₀ : le value $ l.root (by omega) := h₅ value v (l.root _) ⟨h₃, h₁.right.right.left⟩
    simp only [↓reduceIte, Nat.add_zero, h₁₀, root_unfold, h₄, reflexive_le]
    have h₁₁ : le value $ r.root (by omega) := h₅ value v (r.root _) ⟨h₃, h₁.right.right.right⟩
    simp only [↓reduceIte, h₁₀, h₁₁, and_self, root_unfold, h₄, reflexive_le]
  case isFalse =>
    split
    rename_i o p v l r h₆ h₇ h₈ index h₂ hi
    cases le v value
    <;> simp (config := { ground := true }) only [root_unfold, Nat.pred_eq_sub_one] at h₃ ⊢
    <;> split
    <;> unfold HeapPredicate.leOrLeaf
    <;> simp only [root_unfold, h₃, h₄, reflexive_le]

theorem heapUpdateAtIsHeap {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) (h₂ : HeapPredicate heap le) (h₃ : transitive_le le) (h₄ : total_le le) : HeapPredicate (heap.heapUpdateAt le index value).fst le := by
  unfold heapUpdateAt heapUpdateAtAux
  generalize heapUpdateAt.proof_1 index = h₁
  split
  case isTrue h₅ =>
    exact heapUpdateRootIsHeap le value heap _ h₂ h₃ h₄
  case isFalse h₅ =>
    split
    rename_i o p v l r h₆ h₇ h₈ index h₁ h₅
    cases h₁₀ : le v value <;> simp (config := {ground := true}) -- this could probably be solved without this split, but readability...
    <;> split
    <;> rename_i h -- h is the same name as used in the function
    <;> unfold HeapPredicate at h₂ ⊢
    <;> simp only [h₂, and_true, true_and]
    case false.isFalse =>
      have h₁₀ := not_le_imp_le h₄ v value (Bool.eq_false_iff.mp h₁₀)
      have h₁₄ : p > 0 := by cases p; exact absurd (Nat.lt_succ.mp index.isLt) h; exact Nat.zero_lt_succ _
      apply And.intro <;> try apply And.intro
      case left => exact heapUpdateAtIsHeap le ⟨index.val - o - 1, _⟩ v r h₂.right.left h₃ h₄
      case right.left => exact HeapPredicate.leOrLeaf_transitive h₃ h₁₀ h₂.right.right.left
      case right.right =>
        have h₁₁: HeapPredicate (heapUpdateAt le ⟨index.val - o - 1, (by omega)⟩ v r).fst le :=
          (heapUpdateAtIsHeap le ⟨index.val - o - 1, (by omega)⟩ v r h₂.right.left h₃ h₄)
        cases h₁₂ : le v (r.root h₁₄)
        case false =>
          cases p
          exact absurd (Nat.lt_succ.mp index.isLt) h
          exact absurd h₂.right.right.right ((Bool.eq_false_iff).mp h₁₂)
        case true =>
          have h₁₃ := heapUpdateAtIsHeapLeRootAux_ValueLeRoot le ⟨index.val - o - 1, (by omega)⟩ v r h₂.right.left (by omega) h₁₂ h₄ h₃
          apply HeapPredicate.leOrLeaf_transitive h₃ _ h₁₃
          exact h₁₀
    case false.isTrue =>
      have h₁₀ := not_le_imp_le h₄ v value (Bool.eq_false_iff.mp h₁₀)
      have h₁₄ : o > 0 := by cases o; simp at h₅ h; exact absurd (Fin.val_inj.mp h : index = 0) h₅; exact Nat.zero_lt_succ _
      apply And.intro <;> try apply And.intro
      case left => exact heapUpdateAtIsHeap le ⟨index.val - 1, _⟩ v l h₂.left h₃ h₄
      case right.right => exact HeapPredicate.leOrLeaf_transitive h₃ h₁₀ h₂.right.right.right
      case right.left =>
        have h₁₁: HeapPredicate (heapUpdateAt le ⟨index.val - 1, (_)⟩ v l).fst le :=
          (heapUpdateAtIsHeap le ⟨index.val - 1, (by omega)⟩ v l h₂.left h₃ h₄)
        cases h₁₂ : le v (l.root h₁₄)
        case false =>
          cases o
          contradiction -- h₁₄ is False
          exact absurd h₂.right.right.left ((Bool.eq_false_iff).mp h₁₂)
        case true =>
          have h₁₃ := heapUpdateAtIsHeapLeRootAux_ValueLeRoot le ⟨index.val - 1, (by omega)⟩ v l h₂.left (by omega) h₁₂ h₄ h₃
          apply HeapPredicate.leOrLeaf_transitive h₃ _ h₁₃
          exact h₁₀
    case true.isFalse =>
      have h₁₄ : p > 0 := by cases p; exact absurd (Nat.lt_succ.mp index.isLt) h; exact Nat.zero_lt_succ _
      apply And.intro
      case left => exact heapUpdateAtIsHeap le ⟨index.val - o - 1, _⟩ value r h₂.right.left h₃ h₄
      case right =>
        have h₁₁: HeapPredicate (heapUpdateAt le ⟨index.val - o - 1, (by omega)⟩ v r).fst le :=
          (heapUpdateAtIsHeap le ⟨index.val - o - 1, (by omega)⟩ v r h₂.right.left h₃ h₄)
        cases h₁₂ : le value (r.root h₁₄)
        case false =>
          have h₁₃ := heapUpdateAtIsHeapLeRootAux_RootLeValue le ⟨index.val - o - 1, (by omega)⟩ value r h₂.right.left (by omega) (not_le_imp_le h₄ value (r.root h₁₄) (Bool.eq_false_iff.mp h₁₂)) h₄
          apply HeapPredicate.leOrLeaf_transitive h₃ _ h₁₃
          cases p
          contradiction -- h₁₄ is False
          exact h₂.right.right.right
        case true =>
          have h₁₃ := heapUpdateAtIsHeapLeRootAux_ValueLeRoot le ⟨index.val - o - 1, (by omega)⟩ value r h₂.right.left (by omega) h₁₂ h₄ h₃
          apply HeapPredicate.leOrLeaf_transitive h₃ _ h₁₃
          exact h₁₀
    case true.isTrue =>
      have h₁₄ : o > 0 := by cases o; simp at h₅ h; exact absurd (Fin.val_inj.mp h : index = 0) h₅; exact Nat.zero_lt_succ _
      apply And.intro
      case left => exact heapUpdateAtIsHeap le ⟨index.val - 1, _⟩ value l h₂.left h₃ h₄
      case right =>
        have h₁₁: HeapPredicate (heapUpdateAt le ⟨index.val - 1, (by omega)⟩ v l).fst le :=
          (heapUpdateAtIsHeap le ⟨index.val - 1, (by omega)⟩ v l h₂.left h₃ h₄)
        cases h₁₂ : le value (l.root h₁₄)
        case false =>
          have h₁₃ := heapUpdateAtIsHeapLeRootAux_RootLeValue le ⟨index.val - 1, (by omega)⟩ value l h₂.left (by omega) (not_le_imp_le h₄ value (l.root h₁₄) (Bool.eq_false_iff.mp h₁₂)) h₄
          apply HeapPredicate.leOrLeaf_transitive h₃ _ h₁₃
          cases o
          contradiction -- h₁₄ is False
          exact h₂.right.right.left
        case true =>
          have h₁₃ := heapUpdateAtIsHeapLeRootAux_ValueLeRoot le ⟨index.val - 1, (by omega)⟩ value l h₂.left (by omega) h₁₂ h₄ h₃
          apply HeapPredicate.leOrLeaf_transitive h₃ _ h₁₃
          exact h₁₀
