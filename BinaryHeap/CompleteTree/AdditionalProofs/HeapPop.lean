import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.AdditionalProofs.HeapRemoveLast
import BinaryHeap.CompleteTree.AdditionalProofs.HeapUpdateRoot

namespace BinaryHeap.CompleteTree.AdditionalProofs

theorem heapPopReturnsRoot {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (le : α → α → Bool) : (tree.heapPop le).snd = tree.root (Nat.succ_pos n) := by
  unfold heapPop
  split
  <;> simp only
  case isFalse h₁ =>
    unfold Internal.heapRemoveLast Internal.heapRemoveLastAux
    split
    rename_i n m v l r _ _ _
    have h₂ : 0 = n + m := Eq.symm $  Nat.eq_zero_of_le_zero $ Nat.le_of_not_gt h₁
    simp only [h₂, ↓reduceDIte, id_eq, root_unfold]
    have : n = 0 := And.left $ Nat.add_eq_zero.mp h₂.symm
    subst n
    have : m = 0 := And.right $ Nat.add_eq_zero.mp h₂.symm
    subst m
    rfl
  case isTrue h₁ =>
    have h₂ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexLeavesRoot tree h₁
    have h₃ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameTree tree
    simp only [h₃, heapUpdateRootReturnsRoot, h₂]

/--
  Shows that each element contained before removing the root that is not the root is still contained after removing the root.
  This is not a rigorous proof that the rest of the tree remained unchanged, as (1 (1 (1 1)) (2)).heapPop = (1 (2 (2 _)) (2)) would pass it too...
  Imho it is still a good indication that there are no obvious bugs.
  -/
theorem heapPopOnlyRemovesRoot {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (le: α → α → Bool) (index : Fin (n+1)) (h₁ : index ≠ ⟨0, Nat.succ_pos _⟩) : (tree.heapPop le).fst.contains $ tree.get index := by
  unfold heapPop
  split <;> simp
  case isFalse h₃ => omega --contradiction. if n == 0 then index cannot be ≠ 0
  case isTrue h₃ =>
    if h₂ : index = (Internal.heapRemoveLastWithIndex tree).snd.snd then
      have h₃ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex tree
      rw[←h₂] at h₃
      unfold get
      simp only
      have := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameElement tree
      rw[←this] at h₃
      simp[h₃, heapUpdateRootContainsUpdatedElement]
    else
      have h₄ : (Internal.heapRemoveLastWithIndex tree).snd.snd ≠ 0 := by
        have a : n ≠ 0 := Nat.ne_of_gt h₃
        have b := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexIndexNeZeroForNGt1 tree
        simp only [ne_eq, ←b] at a
        exact a
      if h₅ : index < (Internal.heapRemoveLastWithIndex tree).snd.snd then
        have h₆ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationLt tree index h₅
        simp only at h₆
        have h₇ : index.val < n := by omega
        have : (⟨↑index, h₇⟩ : Fin n) ≠ ⟨0, h₃⟩ := by
          rewrite[←Fin.val_ne_iff] at h₁
          simp only [ne_eq, Fin.mk.injEq] at h₁ ⊢
          assumption
        have h₈ := heapUpdateRootOnlyUpdatesRoot le (Internal.heapRemoveLastWithIndex tree).fst h₃ ⟨↑index, h₇⟩ this $ (Internal.heapRemoveLastWithIndex tree).snd.fst
        rewrite[h₆] at h₈
        rewrite[←CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameElement] at h₈
        rewrite[←CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameTree] at h₈
        exact h₈
      else
        have h₅ : index > (Internal.heapRemoveLastWithIndex tree).snd.snd := by omega
        have h₆ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationGt tree index h₅
        simp only at h₆
        have : index.pred h₁ ≠ ⟨0, h₃⟩ := by
          have h₄ : (Internal.heapRemoveLastWithIndex tree).snd.snd.val > 0 := Nat.zero_lt_of_ne_zero (Fin.val_ne_of_ne h₄)
          rewrite[←Fin.val_ne_iff]
          simp only [Fin.coe_pred, ne_eq]
          omega
        have h₈ := heapUpdateRootOnlyUpdatesRoot le (Internal.heapRemoveLastWithIndex tree).fst h₃ (index.pred h₁) this $ (Internal.heapRemoveLastWithIndex tree).snd.fst
        rewrite[h₆] at h₈
        rewrite[←CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameElement] at h₈
        rewrite[←CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameTree] at h₈
        exact h₈
