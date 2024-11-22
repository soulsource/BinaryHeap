import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.CompleteTree.AdditionalProofs.HeapUpdateRoot
import BinaryHeap.CompleteTree.AdditionalProofs.Get

namespace BinaryHeap.CompleteTree.AdditionalProofs

theorem heapUpdatAtRootEqUpdateRoot {α : Type u} {le : α → α → Bool} : CompleteTree.heapUpdateAt le ⟨0, h₁⟩ = CompleteTree.heapUpdateRoot h₁ le := by
  funext
  unfold heapUpdateAt heapUpdateAtAux
  rfl

theorem heapUpdateAtReturnsElementAt {α : Type u} {n : Nat} (le : α → α → Bool) (val : α) (heap : CompleteTree α n) (index : Fin n) : heap.get index = (heap.heapUpdateAt le index val).snd := by
  cases index
  rename_i i isLt
  cases i
  case mk.zero =>
    rw[←get_zero_eq_root, heapUpdatAtRootEqUpdateRoot]
    exact Eq.symm $ heapUpdateRootReturnsRoot le val heap isLt
  case mk.succ j =>
    unfold heapUpdateAt heapUpdateAtAux
    generalize hj : (⟨j + 1, isLt⟩ : Fin n) = index -- otherwise split fails...
    generalize heapUpdateAt.proof_1 index = h₁ -- this sounds fragile... It's the n > 0 proof
    split
    case isTrue h => simp only [←hj, beq_iff_eq, Fin.mk.injEq, Nat.add_one_ne_zero] at h --contradiction
    case isFalse =>
      split
      subst hj -- and put it back, now that split succeeded.
      simp only [Nat.add_eq, Nat.succ_eq_add_one, Nat.pred_succ]
      split <;> simp only
      case isTrue h₂ =>
        rw[get_left]
        case h₂ => exact Nat.succ_pos j
        case h₃ =>
          rw[leftLen_unfold _ _ _ _ _ _ (Nat.succ_pos _)]
          exact h₂
        apply heapUpdateAtReturnsElementAt
      case isFalse h₂ =>
        rw[get_right]
        case h₂ =>
          simp only [Nat.not_le] at h₂
          simp only [leftLen_unfold, gt_iff_lt, h₂]
        apply heapUpdateAtReturnsElementAt

theorem heapUpdateAtContainsValue {α : Type u} {n : Nat} (le : α → α → Bool) (heap : CompleteTree α n) (value : α) (index : Fin n) : (heap.heapUpdateAt le index value).fst.contains value := by
  unfold heapUpdateAt heapUpdateAtAux
  generalize heapUpdateAt.proof_1 index = h₁
  split
  case isTrue h₂ =>
    apply heapUpdateRootContainsUpdatedElement
  case isFalse h₂ =>
    split
    rename_i o p v l r _ _ _ index h₁ h₂
    cases le v value <;> dsimp
    case false =>
      split
      <;> rewrite[contains_as_root_left_right _ _ (Nat.succ_pos _)]
      <;> left
      <;> rfl
    case true =>
      split
      <;> rewrite[contains_as_root_left_right _ _ (Nat.succ_pos _)]
      <;> right
      case' isTrue =>
        have : o < o+p+1 := Nat.lt_of_le_of_lt (Nat.le_add_right o p) (Nat.lt_succ_self (o+p)) --term
        left
        rewrite[left_unfold]
      case' isFalse =>
        have : p < o+p+1 := Nat.lt_of_le_of_lt (Nat.le_add_left p o) (Nat.lt_succ_self (o+p)) --term
        right
        rewrite[right_unfold]
      all_goals
        apply heapUpdateAtContainsValue
termination_by n

theorem heapUpdateAtOnlyUpdatesAt {α : Type u} {n : Nat} (le : α → α → Bool) (val : α) (heap : CompleteTree α n) (updateIndex : Fin n) (otherIndex : Fin n) (h₂ : updateIndex ≠ otherIndex) : (heap.heapUpdateAt le updateIndex val).fst.contains $ heap.get otherIndex :=
  have h₁ : n > 0 := Nat.zero_lt_of_lt otherIndex.isLt
  if h₃ : updateIndex = ⟨0, h₁⟩ then
    have h₄ : otherIndex ≠ ⟨0, h₁⟩ := h₃.subst h₂.symm
    heapUpdateRootOnlyUpdatesRoot le heap h₁ otherIndex h₄ val
    |> heapUpdatAtRootEqUpdateRoot.substr (p := λx↦(x val heap).fst.contains (heap.get otherIndex))
    |> h₃.substr (p := λx↦((heap.heapUpdateAt le x val).fst.contains $ heap.get otherIndex))
  else if h₄ : otherIndex = ⟨0, h₁⟩ then by
    subst h₄
    rw[←get_zero_eq_root]
    unfold heapUpdateAt heapUpdateAtAux
    generalize heapUpdateAt.proof_1 updateIndex = h₁
    --cannot use h₃ here already - it makes split fail. So, splitting twice it is...
    split
    case isTrue h => exact absurd (beq_iff_eq.mp h) h₃
    split
    rename_i d1 d2 d3 d4 d5 o p v l r _ _ _ updateIndex _ _
    clear d1 d2 d3 d4 d5
    cases le v val <;> dsimp
    case isFalse.true =>
      -- v ≤ val -> current root smaller or equal, keep current root, move val down.
      split
      <;> simp only [gt_iff_lt, Nat.zero_lt_succ, contains_as_root_left_right]
      <;> left
      <;> rewrite[root_unfold]
      <;> rw[root_unfold]
    case isFalse.false =>
      -- v > val -> repace current root by val, move current root down.
      split
      <;> simp only [gt_iff_lt, Nat.zero_lt_succ, contains_as_root_left_right]
      <;> right
      case' isTrue =>
        left
        rewrite[left_unfold]
      case' isFalse =>
        right
        rewrite[right_unfold]
      all_goals
        rewrite[root_unfold]
        apply heapUpdateAtContainsValue
  else by
    unfold heapUpdateAt heapUpdateAtAux
    generalize heapUpdateAt.proof_1 updateIndex = h₁
    split
    case isTrue hx => exact absurd (beq_iff_eq.mp hx) h₃
    case isFalse =>
      split
      rename_i d1 d2 d3 d4 d5 o p v l r olep mhd stc index _ _
      clear d1 d2 d3 d4 d5
      cases le v val
      <;> dsimp
      -- here we don'treally care if v or val gets handed down. We recurse in any case.
      -- we do care about the question if we go left or right though.
      <;> split
      all_goals
        have h₄₂ : otherIndex > 0 := Fin.pos_iff_ne_zero.mpr h₄
        rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
        right
      case false.isTrue h₅ | true.isTrue h₅ =>
        if h₆ : otherIndex ≤ o then
          have : otherIndex ≤ (branch v l r olep mhd stc).leftLen (Nat.succ_pos _) := by simp only [leftLen_unfold, h₆]
          rw[get_left _ _ h₄₂ this]
          left
          --rw[left_unfold]
          have : o < o + p + 1 := Nat.lt_of_le_of_lt (Nat.le_add_right o p) (Nat.lt_succ_self (o+p))
          apply heapUpdateAtOnlyUpdatesAt
          simp only [ne_eq, Fin.mk.injEq]
          exact (Nat.pred_ne_of_ne (Fin.pos_iff_ne_zero.mpr h₃) (Fin.pos_iff_ne_zero.mpr h₄)).mp $ Fin.val_ne_iff.mpr h₂
        else
          have : otherIndex > (branch v l r olep mhd stc).leftLen (Nat.succ_pos _) := by rw[leftLen_unfold]; exact Nat.gt_of_not_le h₆
          rw[get_right _ _ this]
          right
          --rw[right_unfold]
          --rw[right_unfold]
          simp only[leftLen_unfold]
          rw[contains_iff_index_exists]
          generalize (⟨↑otherIndex - o - 1, _⟩ : Fin _) = solution -- Allows to skip the annoying proof that Lean already has...
          exists solution
      case false.isFalse h₅ | true.isFalse h₅ =>
        if h₆ : otherIndex ≤ o then
          have : otherIndex ≤ (branch v l r olep mhd stc).leftLen (Nat.succ_pos _) := by simp only [leftLen_unfold, h₆]
          rw[get_left _ _ h₄₂ this]
          left
          --rw[left_unfold]
          --rw[left_unfold]
          rw[contains_iff_index_exists]
          generalize (⟨↑otherIndex - 1, _⟩ : Fin _) = solution
          exists solution
        else
          have h₆ : otherIndex > (branch v l r olep mhd stc).leftLen (Nat.succ_pos _) := by rw[leftLen_unfold]; exact Nat.gt_of_not_le h₆
          rw[get_right _ _ h₆]
          right
          --rw[right_unfold]
          have : p < o + p + 1 := Nat.lt_of_le_of_lt (Nat.le_add_left p o) (Nat.lt_succ_self (o+p))
          apply heapUpdateAtOnlyUpdatesAt
          simp only [ne_eq, Fin.mk.injEq]
          --rw[leftLen_unfold]
          have h₅ : index.val ≥ o + 1 := Nat.gt_of_not_le h₅
          exact (Nat.sub_ne_of_ne h₅ h₆).mp $ Fin.val_ne_iff.mpr h₂
termination_by n
