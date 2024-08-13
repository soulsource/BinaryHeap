import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.Lemmas
import BinaryHeap.CompleteTree.HeapProofs.EmptyIsHeap

namespace BinaryHeap.CompleteTree


--- Same as rootSeesThroughCast, but in the other direction.
private theorem rootSeesThroughCast2
  (n m : Nat)
  (h₁ : n + m + 1 = n + 1 + m)
  (h₂ : 0 < n + m + 1)
  (h₃ : 0 < n + 1 + m)
  (heap : CompleteTree α (n+m+1)) : (h₁▸heap).root h₃ = heap.root h₂ := by
  induction m generalizing n
  case zero => simp
  case succ mm mh =>
    have h₄ := mh (n+1)
    have h₅ : n + 1 + mm + 1 = n + Nat.succ mm + 1 := by simp_arith
    have h₆ : n + 1 + 1 + mm = n + 1 + Nat.succ mm := by simp_arith
    rw[h₅, h₆] at h₄
    revert heap h₁ h₂ h₃
    assumption

private theorem HeapPredicate.seesThroughCast2
  (n m : Nat)
  (lt : α → α → Bool)
  (h₁ : n+m+1=n+1+m)
  (h₂ : 0<n+1+m)
  (h₃ : 0<n+m+1)
  (heap : CompleteTree α (n+m+1)) : HeapPredicate heap lt → HeapPredicate (h₁▸heap) lt := by
  unfold HeapPredicate
  intro h₄
  induction m generalizing n
  case zero => simp[h₄]
  case succ o ho =>
    have h₅ := ho (n+1)
    have h₆ : n+1+o+1 = n+(Nat.succ o)+1 := by simp_arith
    rw[h₆] at h₅
    have h₆ : n + 1 + 1 + o = n + 1 + Nat.succ o := by simp_arith
    rewrite[h₆] at h₅
    revert heap h₁ h₂ h₃
    assumption

private theorem castZeroHeap (n m : Nat) (heap : CompleteTree α 0) (h₁ : 0=n+m) {le : α → α → Bool} : HeapPredicate (h₁ ▸ heap) le := by
  have h₂ : heap = (empty : CompleteTree α 0) := by
    simp[empty]
    match heap with
    | .leaf => trivial
  have h₂ : HeapPredicate heap le := by simp[h₂, empty, emptyIsHeap]
  cases m
  case succ => contradiction
  case zero =>
    cases n
    case succ => contradiction
    case zero =>
      simp[h₁, h₂]

-- If there is only one element left, the result is a leaf.
private theorem heapRemoveLastAuxLeaf
{α : Type u}
{β : Nat → Type u}
(heap : CompleteTree α 1)
(aux0 : α → (β 1))
(auxl : {prev_size curr_size : Nat} → β prev_size → (h₁ : prev_size < curr_size) → β curr_size)
(auxr : {prev_size curr_size : Nat} → β prev_size → (left_size : Nat) → (h₁ : prev_size + left_size < curr_size) → β curr_size)
:  (Internal.heapRemoveLastAux heap aux0 auxl auxr).fst = leaf := by
  let l := (Internal.heapRemoveLastAux heap aux0 auxl auxr).fst
  have h₁ : l = leaf := match l with
    | .leaf => rfl
  exact h₁

protected theorem heapRemoveLastAuxLeavesRoot
{α : Type u}
{β : Nat → Type u}
(heap : CompleteTree α (n+1))
(aux0 : α → (β 1))
(auxl : {prev_size curr_size : Nat} → β prev_size → (h₁ : prev_size < curr_size) → β curr_size)
(auxr : {prev_size curr_size : Nat} → β prev_size → (left_size : Nat) → (h₁ : prev_size + left_size < curr_size) → β curr_size)
(h₁ : n > 0)
: heap.root (Nat.zero_lt_of_ne_zero $ Nat.succ_ne_zero n) = (Internal.heapRemoveLastAux heap aux0 auxl auxr).fst.root (h₁) := by
  unfold CompleteTree.Internal.heapRemoveLastAux
  split
  rename_i o p v l r _ _ _
  have h₃ : (0 ≠ o + p) := Ne.symm $ Nat.not_eq_zero_of_lt h₁
  simp[h₃]
  exact
    if h₄ : p < o ∧ Nat.nextPowerOfTwo (p + 1) = p + 1 then by
      simp[h₄]
      cases o
      case zero => exact absurd h₄.left $ Nat.not_lt_zero p
      case succ oo _ _ _ =>
        simp -- redundant, but makes goal easier to read
        rw[rootSeesThroughCast2 oo p _ (by simp_arith) _]
        apply root_unfold
    else by
      simp[h₄]
      cases p
      case zero =>
        simp_arith at h₁ -- basically o ≠ 0
        simp_arith (config := {ground := true})[h₁] at h₄ -- the second term in h₄ is decidable and True. What remains is ¬(0 < o), or o = 0
      case succ pp hp =>
        simp_arith
        apply root_unfold

private theorem heapRemoveLastAuxIsHeap
{α : Type u}
{β : Nat → Type u}
{heap : CompleteTree α (o+1)}
{le : α → α → Bool}
(aux0 : α → (β 1))
(auxl : {prev_size curr_size : Nat} → β prev_size → (h₁ : prev_size < curr_size) → β curr_size)
(auxr : {prev_size curr_size : Nat} → β prev_size → (left_size : Nat) → (h₁ : prev_size + left_size < curr_size) → β curr_size)
(h₁ : HeapPredicate heap le) (h₂ : transitive_le le) (h₃ : total_le le) : HeapPredicate ((Internal.heapRemoveLastAux heap aux0 auxl auxr).fst) le := by
  unfold CompleteTree.Internal.heapRemoveLastAux
  split
  rename_i n m v l r _ _ _
  exact
    if h₄ : 0 = (n+m) then by
      simp only [h₄, reduceDIte, castZeroHeap]
    else by
      simp[h₄]
      exact
        if h₅ : (m<n ∧ Nat.nextPowerOfTwo (m+1) = m+1) then by
          simp only [h₅, and_self, ↓reduceDIte]
          cases n
          case zero =>
            exact absurd h₅.left $ Nat.not_lt_zero m
          case succ ll h₆ h₇ h₈  =>
            simp only
            apply HeapPredicate.seesThroughCast2 <;> try simp_arith
            cases ll
            case a.zero => -- if ll is zero, then (heapRemoveLast l).snd is a leaf.
              have h₆ := heapRemoveLastAuxLeaf l aux0 auxl auxr
              rw[h₆]
              unfold HeapPredicate at *
              have h₇ : HeapPredicate .leaf le := by trivial
              have h₈ : HeapPredicate.leOrLeaf le v .leaf := by trivial
              exact ⟨h₇,h₁.right.left, h₈, h₁.right.right.right⟩
            case a.succ nn => -- if ll is not zero, then the root element before and after heapRemoveLast is the same.
              unfold HeapPredicate at *
              simp only [heapRemoveLastAuxIsHeap aux0 auxl auxr h₁.left h₂ h₃, h₁.right.left, h₁.right.right.right, and_true, true_and]
              unfold HeapPredicate.leOrLeaf
              simp only
              rw[←CompleteTree.heapRemoveLastAuxLeavesRoot]
              exact h₁.right.right.left
        else by
          simp[h₅]
          cases m
          case zero =>
            simp only [Nat.add_zero] at h₄ -- n ≠ 0
            simp (config := { ground := true }) only [Nat.zero_add, and_true, Nat.not_lt, Nat.le_zero_eq, Ne.symm h₄] at h₅ -- the second term in h₅ is decidable and True. What remains is ¬(0 < n), or n = 0
          case succ mm h₆ h₇ h₈ =>
            unfold HeapPredicate at *
            simp only [h₁, heapRemoveLastAuxIsHeap aux0 auxl auxr h₁.right.left h₂ h₃, true_and]
            unfold HeapPredicate.leOrLeaf
            exact match mm with
            | 0 => rfl
            | o+1 =>
              have h₉ : le v ((Internal.heapRemoveLastAux r _ _ _).fst.root (Nat.zero_lt_succ o)) := by
                rw[←CompleteTree.heapRemoveLastAuxLeavesRoot]
                exact h₁.right.right.right
              h₉

protected theorem heapRemoveLastIsHeap {α : Type u} {heap : CompleteTree α (o+1)} {le : α → α → Bool} (h₁ : HeapPredicate heap le) (h₂ : transitive_le le) (h₃ : total_le le) : HeapPredicate (Internal.heapRemoveLast heap).fst le :=
  heapRemoveLastAuxIsHeap _ _ _ h₁ h₂ h₃

protected theorem heapRemoveLastWithIndexIsHeap {α : Type u} {heap : CompleteTree α (o+1)} {le : α → α → Bool} (h₁ : HeapPredicate heap le) (h₂ : transitive_le le) (h₃ : total_le le) : HeapPredicate ((Internal.heapRemoveLastWithIndex heap).fst) le :=
  heapRemoveLastAuxIsHeap _ _ _ h₁ h₂ h₃
