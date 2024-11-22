import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.Lemmas

namespace BinaryHeap.CompleteTree

private theorem rootSeesThroughCast
  (n m : Nat)
  (h₁ : n + 1 + m = n + m + 1)
  (h₂ : 0 < n + 1 + m)
  (h₃ : 0 < n + m + 1)
  (heap : CompleteTree α (n+1+m)) : (h₁▸heap).root h₃ = heap.root h₂ := by
  induction m generalizing n
  case zero => simp
  case succ o ho =>
    have h₄ := ho (n+1)
    have h₅ : n + 1 + 1 + o = n + 1 + (Nat.succ o) := by simp_arith
    have h₆ : n + 1 + o + 1 = n + (Nat.succ o + 1) := by simp_arith
    rewrite[h₅, h₆] at h₄
    revert heap h₁ h₂ h₃
    assumption

private theorem HeapPredicate.seesThroughCast
  (n m : Nat)
  (lt : α → α → Bool)
  (h₁ : n+1+m+1=n+m+1+1)
  (h₂ : 0<n+1+m+1)
  (h₃ : 0<n+m+1+1)
  (heap : CompleteTree α (n+1+m+1)) : HeapPredicate heap lt → HeapPredicate (h₁▸heap) lt := by
  unfold HeapPredicate
  intro h₄
  induction m generalizing n
  case zero => simp[h₄]
  case succ o ho =>
    have h₅ := ho (n+1)
    have h₆ : n+1+1+o+1 = n+1+(Nat.succ o)+1 := by simp_arith
    rw[h₆] at h₅
    have h₆ : n + 1 + o + 1 + 1 = n + (Nat.succ o + 1 + 1) := by simp_arith
    rewrite[h₆] at h₅
    revert heap h₁ h₂ h₃
    assumption

theorem heapPushRootSameOrElem (elem : α) (heap : CompleteTree α o) (lt : α → α → Bool) (h₂ : 0 < o): (root (heap.heapPush lt elem) (Nat.succ_pos o) = elem) ∨ (root (heap.heapPush lt elem) (Nat.succ_pos o) = root heap h₂) := by
  unfold heapPush
  split --match o, heap
  contradiction
  simp
  rename_i n m v l r _ _ _
  split -- if h : m < n ∧ Nat.nextPowerOfTwo (n + 1) = n + 1 then
  case h_2.isTrue h =>
    cases (lt elem v) <;> simp[instDecidableEqBool, Bool.decEq, root]
  case h_2.isFalse h =>
    rw[rootSeesThroughCast n (m+1) (by simp_arith) (by simp_arith) (by simp_arith)]
    cases (lt elem v)
     <;> simp[instDecidableEqBool, Bool.decEq, root]

theorem heapPushEmptyElem (elem : α) (heap : CompleteTree α o) (lt : α → α → Bool) (h₂ : ¬0 < o) : (root (heap.heapPush lt elem) (Nat.succ_pos o) = elem) :=
  have : o = 0 := Nat.eq_zero_of_le_zero $ (Nat.not_lt_eq 0 o).mp h₂
  match o, heap with
  | 0, .leaf => by simp[heapPush, root]

mutual
/--
  Helper for heapPushIsHeap, to make one function out of both branches.
  Sorry for the ugly signature, but this was the easiest thing to extract.
  -/
private theorem heapPushIsHeapAux {α : Type u} (le : α → α → Bool) (n m : Nat) (v elem : α) (l : CompleteTree α n) (r : CompleteTree α m) (h₁ : HeapPredicate l le ∧ HeapPredicate r le ∧ HeapPredicate.leOrLeaf le v l ∧ HeapPredicate.leOrLeaf le v r) (h₂ : transitive_le le) (h₃ : total_le le): HeapPredicate l le ∧
  let smaller := (if le elem v then elem else v)
  let larger := (if le elem v then v else elem)
  HeapPredicate (heapPush le larger r) le
  ∧ HeapPredicate.leOrLeaf le smaller l
  ∧ HeapPredicate.leOrLeaf le smaller (heapPush le larger r)
  := by
  cases h₆ : (le elem v) <;> simp only [Bool.false_eq_true, reduceIte]
  case true =>
    have h₇ : (HeapPredicate (heapPush le v r) le) := heapPushIsHeap h₁.right.left h₂ h₃
    simp only [true_and, h₁, h₇, HeapPredicate.leOrLeaf_transitive h₂ h₆ h₁.right.right.left]
    cases m
    case zero =>
      have h₈  := heapPushEmptyElem v r le (Nat.not_lt_zero 0)
      simp only [HeapPredicate.leOrLeaf, Nat.succ_eq_add_one, Nat.reduceAdd, h₈]
      assumption
    case succ _ =>
      simp only [HeapPredicate.leOrLeaf]
      cases heapPushRootSameOrElem v r le (Nat.succ_pos _)
      <;> rename_i h₇
      <;> rw[h₇]
      . assumption
      apply h₂ elem v
      exact ⟨h₆, h₁.right.right.right⟩
  case false =>
    have h₇ : (HeapPredicate (heapPush le elem r) le) := heapPushIsHeap h₁.right.left h₂ h₃
    simp only [true_and, h₁, h₇]
    have h₈ : le v elem := not_le_imp_le h₃ elem v (by simp only [h₆, Bool.false_eq_true, not_false_eq_true])
    cases m
    case zero =>
      have h₇ := heapPushEmptyElem elem r le (Nat.not_lt_zero 0)
      simp only [HeapPredicate.leOrLeaf, Nat.succ_eq_add_one, Nat.reduceAdd, h₇]
      assumption
    case succ _ =>
      cases heapPushRootSameOrElem elem r le (Nat.succ_pos _)
      <;> rename_i h₉
      <;> simp only [HeapPredicate.leOrLeaf, Nat.succ_eq_add_one, h₈, h₉]
      exact h₁.right.right.right

theorem heapPushIsHeap {α : Type u} {elem : α} {heap : CompleteTree α o} {le : α → α → Bool} (h₁ : HeapPredicate heap le) (h₂ : transitive_le le) (h₃ : total_le le) : HeapPredicate (heap.heapPush le elem) le := by
  unfold heapPush
  split -- match o, heap with
  trivial
  case h_2 n m v l r m_le_n _ _ =>
    simp
    split -- if h₅ : m < n ∧ Nat.nextPowerOfTwo (n + 1) = n + 1 then
    case' isTrue =>
      have h := heapPushIsHeapAux le n m v elem l r h₁ h₂ h₃
    case' isFalse =>
      apply HeapPredicate.seesThroughCast <;> try simp_arith[h₂] --gets rid of annoying cast.
      have h := heapPushIsHeapAux le m n v elem r l (And.intro h₁.right.left $ And.intro h₁.left $ And.intro h₁.right.right.right h₁.right.right.left) h₂ h₃
    all_goals
      unfold HeapPredicate
      cases h₆ : (le elem v)
      <;> simp only [h₆, Bool.false_eq_true, reduceIte] at h
      <;> simp only [Bool.false_eq_true, ↓reduceIte, h, and_self]
end
