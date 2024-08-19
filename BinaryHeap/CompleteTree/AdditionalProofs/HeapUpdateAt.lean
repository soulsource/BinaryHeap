import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.CompleteTree.AdditionalProofs.HeapUpdateRoot
import BinaryHeap.CompleteTree.AdditionalProofs.Get

namespace BinaryHeap.CompleteTree.AdditionalProofs

theorem heapUpdateAtReturnsElementAt {α : Type u} {n : Nat} (le : α → α → Bool) (val : α) (heap : CompleteTree α n) (index : Fin n) (h₁ : n > 0) : heap.get index h₁ =  (heap.heapUpdateAt le index val h₁).snd := by
  cases index
  rename_i i isLt
  cases i
  case mk.zero =>
    unfold get get' heapUpdateAt
    split
    split
    case h_2 hx =>
      have hx := Fin.val_eq_of_eq hx
      contradiction
    case h_1 v l r h₂ h₃ h₄ _ _ _=>
      exact Eq.symm $ heapUpdateRootReturnsRoot le val (.branch v l r h₂ h₃ h₄) (Nat.succ_pos _)
  case mk.succ j =>
    unfold heapUpdateAt
    generalize hj : (⟨j + 1, isLt⟩ : Fin n) = index -- otherwise split fails...
    split
    case isTrue h => simp only [←hj, beq_iff_eq, Fin.mk.injEq, Nat.add_one_ne_zero] at h --contradiction
    case isFalse =>
      split
      subst hj
      simp only [Nat.add_eq, Nat.succ_eq_add_one, Nat.pred_succ]
      split <;> simp only
      case isTrue h₂ =>
        rw[get_left]
        case h₂ => exact Nat.succ_pos j
        case h₃ =>
          rw[leftLen_unfold]
          exact h₂
        apply heapUpdateAtReturnsElementAt
      case isFalse h₂ =>
        rw[get_right]
        case h₂ =>
          simp only [Nat.not_le] at h₂
          simp only [leftLen_unfold, gt_iff_lt, h₂]
        apply heapUpdateAtReturnsElementAt
