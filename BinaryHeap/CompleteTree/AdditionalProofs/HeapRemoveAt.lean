import BinaryHeap.CompleteTree.AdditionalProofs.HeapUpdateAt
import BinaryHeap.CompleteTree.AdditionalProofs.Get
import BinaryHeap.CompleteTree.AdditionalProofs.HeapPop
import BinaryHeap.CompleteTree.AdditionalProofs.HeapRemoveLast

namespace BinaryHeap.CompleteTree.AdditionalProofs

theorem heapRemoveAtReturnsElementAt {α : Type u} {n : Nat} (le : α → α → Bool) (heap : CompleteTree α (n+1)) (index : Fin (n+1)) : (heap.heapRemoveAt le index).snd = heap.get' index := by
  unfold heapRemoveAt
  if h₁ : index = 0 then
    simp only [h₁, ↓reduceDIte]
    rw[get_eq_get', ←Fin.zero_eta, ←get_zero_eq_root]
    exact heapPopReturnsRoot heap le
  else
    simp only [h₁, ↓reduceDIte, ge_iff_le]
    if h₂ : index = (Internal.heapRemoveLastWithIndex heap).2.snd then
      simp only [h₂, ↓reduceDIte]
      exact Eq.symm $ CompleteTree.AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex heap
    else
      if h₃ : (Internal.heapRemoveLastWithIndex heap).2.snd ≤ index then
        simp only[h₂, h₃, ↓reduceDIte]
        have h₄ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationGt heap index $ Nat.lt_of_le_of_ne h₃ (Fin.val_ne_iff.mpr (Ne.symm h₂))
        rewrite[get_eq_get', ←h₄]
        exact Eq.symm $ heapUpdateAtReturnsElementAt le _ _ _
      else
        simp only[h₂, h₃, ↓reduceDIte]
        have h₄ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationLt heap index (Nat.gt_of_not_le h₃)
        rewrite[get_eq_get', ←h₄]
        exact Eq.symm $ heapUpdateAtReturnsElementAt le _ _ _

theorem heapRemoveAtOnlyRemovesAt {α : Type u} {n : Nat} (le : α → α → Bool) (heap : CompleteTree α (n+1)) (removeIndex : Fin (n+1)) (otherIndex : Fin (n+1)) (h₁ : removeIndex ≠ otherIndex) : (heap.heapRemoveAt le removeIndex).fst.contains (heap.get' otherIndex) := by
  unfold heapRemoveAt
  if h₂ : removeIndex = 0 then
    subst removeIndex
    exact heapPopOnlyRemovesRoot _ _ _ h₁.symm
  else
    simp only [h₂, ↓reduceDIte, ge_iff_le]
    if h₃ : removeIndex = (Internal.heapRemoveLastWithIndex heap).2.snd then
      simp only [h₃, ↓reduceDIte]
      exact CompleteTree.AdditionalProofs.heapRemoveLastWithIndexOnlyRemovesOneElement _ _ (h₃.subst h₁.symm)
    else
      if h₄ : (Internal.heapRemoveLastWithIndex heap).2.snd ≤ removeIndex then
        simp only[h₃, h₄, ↓reduceDIte]
        have h₅ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelation heap otherIndex
        simp only [gt_iff_lt] at h₅
        split at h₅
        case isTrue h₆ =>
          rw[get_eq_get', ←h₅]
          apply heapUpdateAtOnlyUpdatesAt
          simp only [ne_eq, Fin.pred_inj, h₁, not_false_eq_true]
        case isFalse h₆ =>
          split at h₅
          case isTrue h₇ =>
            rw[get_eq_get', ←h₅]
            apply heapUpdateAtOnlyUpdatesAt
            simp only [ne_eq, Fin.ext_iff, Fin.coe_pred, Fin.coe_castLT]
            generalize (Internal.heapRemoveLastWithIndex heap).snd.snd = j at *
            omega
          case isFalse h₇ =>
            generalize h₈ : (Internal.heapRemoveLastWithIndex heap).snd.snd = j at *
            have h₉ : otherIndex = j := by omega
            subst h₉
            subst h₈
            rw[CompleteTree.AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex]
            exact heapUpdateAtContainsValue _ _ _ _
      else
        simp only [h₃, h₄, ↓reduceDIte]
        have h₅ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelation heap otherIndex
        simp only [gt_iff_lt] at h₅
        split at h₅
        case isTrue h₆ =>
          rw[get_eq_get', ←h₅]
          apply heapUpdateAtOnlyUpdatesAt
          simp[Fin.ext_iff]
          generalize (Internal.heapRemoveLastWithIndex heap).snd.snd = j at *
          omega --h₄ and h₆
        case isFalse h₆ =>
          split at h₅
          case isTrue h₇ =>
            rw[get_eq_get', ←h₅]
            apply heapUpdateAtOnlyUpdatesAt
            rw[←Fin.val_ne_iff] at h₁ ⊢
            exact h₁
          case isFalse h₇ =>
            generalize h₈ : (Internal.heapRemoveLastWithIndex heap).snd.snd = j at *
            have h₉ : otherIndex = j := by omega
            subst h₉
            subst h₈
            rw[CompleteTree.AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex]
            exact heapUpdateAtContainsValue _ _ _ _
