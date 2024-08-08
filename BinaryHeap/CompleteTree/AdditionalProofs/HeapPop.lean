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
    simp only [h₂, ↓reduceDite, id_eq, root_unfold]
    have : n = 0 := And.left $ Nat.add_eq_zero.mp h₂.symm
    subst n
    have : m = 0 := And.right $ Nat.add_eq_zero.mp h₂.symm
    subst m
    rfl
  case isTrue h₁ =>
    have h₂ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexLeavesRoot tree h₁
    have h₃ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameTree tree
    simp only [h₃, heapUpdateRootReturnsRoot, h₂]

theorem heapPopOnlyRemovesRoot {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (le: α → α → Bool) (index : Fin (n+1)) (h₁ : index ≠ ⟨0, Nat.succ_pos _⟩) : (tree.heapPop le).fst.contains $ tree.get index (Nat.succ_pos _) := by
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
      sorry


theorem heapPopOnlyRemovesRoot2 {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (le: α → α → Bool) (index : Fin (n+1)) (h₁ : index ≠ ⟨0, Nat.succ_pos _⟩) : (tree.heapPop le).fst.contains $ tree.get index (Nat.succ_pos _) := by
  unfold heapPop
  have h₂ := CompleteTree.AdditionalProofs.heapRemoveLastEitherContainsOrReturnsElement tree index
  simp only at h₂
  split <;> simp
  case isFalse h₃ => omega --contradiction. if n == 0 then index cannot be ≠ 0
  case isTrue h₃ =>
    cases h₂
    case inr h₂ =>
      rw[h₂]
      exact heapUpdateRootContainsUpdatedElement (Internal.heapRemoveLast tree).fst le (get index tree (Nat.succ_pos _)) h₃
    case inl h₂ =>
      generalize h₄ : (Internal.heapRemoveLast tree).fst = withoutLast
      have h₅ := CompleteTree.AdditionalProofs.heapRemoveLastLeavesRoot tree h₃
      rw[h₄] at h₂ h₅
      have := heapUpdateRootOnlyUpdatesRoot le withoutLast h₃
      rw[contains_iff_index_exists _ _ h₃] at h₂
      -- to use h₂.elim we need to rewrite this into
      -- ∀ (a : Fin n), get a withoutLast h₃ = get index tree ⋯ → something
      sorry
