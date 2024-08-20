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
        exact Eq.symm $ heapUpdateAtReturnsElementAt le _ _ _ _
      else
        simp only[h₂, h₃, ↓reduceDIte]
        have h₄ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationLt heap index (Nat.gt_of_not_le h₃)
        rewrite[get_eq_get', ←h₄]
        exact Eq.symm $ heapUpdateAtReturnsElementAt le _ _ _ _
