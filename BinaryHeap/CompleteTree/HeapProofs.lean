import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.Lemmas

namespace BinaryHeap

theorem CompleteTree.emptyIsHeap {α : Type u} (le : α → α → Bool) : HeapPredicate CompleteTree.empty le := True.intro

----------------------------------------------------------------------------------------------
-- heapPush

private theorem CompleteTree.rootSeesThroughCast
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

theorem CompleteTree.heapPushRootSameOrElem (elem : α) (heap : CompleteTree α o) (lt : α → α → Bool) (h₂ : 0 < o): (CompleteTree.root (heap.heapPush lt elem) (Nat.succ_pos o) = elem) ∨ (CompleteTree.root (heap.heapPush lt elem) (Nat.succ_pos o) = CompleteTree.root heap h₂) := by
  unfold heapPush
  split --match o, heap
  contradiction
  simp
  rename_i n m v l r _ _ _
  split -- if h : m < n ∧ Nat.nextPowerOfTwo (n + 1) = n + 1 then
  case h_2.isTrue h =>
    cases (lt elem v) <;> simp[instDecidableEqBool, Bool.decEq, CompleteTree.root]
  case h_2.isFalse h =>
    rw[rootSeesThroughCast n (m+1) (by simp_arith) (by simp_arith) (by simp_arith)]
    cases (lt elem v)
     <;> simp[instDecidableEqBool, Bool.decEq, CompleteTree.root]

theorem CompleteTree.heapPushEmptyElem (elem : α) (heap : CompleteTree α o) (lt : α → α → Bool) (h₂ : ¬0 < o) : (CompleteTree.root (heap.heapPush lt elem) (Nat.succ_pos o) = elem) :=
  have : o = 0 := Nat.eq_zero_of_le_zero $ (Nat.not_lt_eq 0 o).mp h₂
  match o, heap with
  | 0, .leaf => by simp[CompleteTree.heapPush, root]

theorem HeapPredicate.leOrLeaf_transitive (h₁ : transitive_le le) : le a b → HeapPredicate.leOrLeaf le b h → HeapPredicate.leOrLeaf le a h := by
  unfold leOrLeaf
  intros h₂ h₃
  rename_i n
  cases n <;> simp
  apply h₁ a b _
  exact ⟨h₂, h₃⟩

mutual
/--
  Helper for CompleteTree.heapPushIsHeap, to make one function out of both branches.
  Sorry for the ugly signature, but this was the easiest thing to extract.
  -/
private theorem CompleteTree.heapPushIsHeapAux {α : Type u} (le : α → α → Bool) (n m : Nat) (v elem : α) (l : CompleteTree α n) (r : CompleteTree α m) (h₁ : HeapPredicate l le ∧ HeapPredicate r le ∧ HeapPredicate.leOrLeaf le v l ∧ HeapPredicate.leOrLeaf le v r) (h₂ : transitive_le le) (h₃ : total_le le): HeapPredicate l le ∧
  let smaller := (if le elem v then elem else v)
  let larger := (if le elem v then v else elem)
  HeapPredicate (heapPush le larger r) le
  ∧ HeapPredicate.leOrLeaf le smaller l
  ∧ HeapPredicate.leOrLeaf le smaller (heapPush le larger r)
  := by
  cases h₆ : (le elem v) <;> simp only [Bool.false_eq_true, reduceIte]
  case true =>
    have h₇ : (HeapPredicate (CompleteTree.heapPush le v r) le) := CompleteTree.heapPushIsHeap h₁.right.left h₂ h₃
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
    have h₇ : (HeapPredicate (CompleteTree.heapPush le elem r) le) := CompleteTree.heapPushIsHeap h₁.right.left h₂ h₃
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

theorem CompleteTree.heapPushIsHeap {α : Type u} {elem : α} {heap : CompleteTree α o} {le : α → α → Bool} (h₁ : HeapPredicate heap le) (h₂ : transitive_le le) (h₃ : total_le le) : HeapPredicate (heap.heapPush le elem) le := by
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
      <;> simp only [instDecidableEqBool, Bool.decEq, h, and_self]
end

----------------------------------------------------------------------------------------------
-- heapRemoveLast

--- Same as rootSeesThroughCast, but in the other direction.
private theorem CompleteTree.rootSeesThroughCast2
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

private theorem CompleteTree.castZeroHeap (n m : Nat) (heap : CompleteTree α 0) (h₁ : 0=n+m) {le : α → α → Bool} : HeapPredicate (h₁ ▸ heap) le := by
  have h₂ : heap = (CompleteTree.empty : CompleteTree α 0) := by
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
private theorem CompleteTree.heapRemoveLastAuxLeaf
{α : Type u}
{β : Nat → Type u}
(heap : CompleteTree α 1)
(aux0 : α → (β 1))
(auxl : {prev_size curr_size : Nat} → β prev_size → (h₁ : prev_size < curr_size) → β curr_size)
(auxr : {prev_size curr_size : Nat} → β prev_size → (left_size : Nat) → (h₁ : prev_size + left_size < curr_size) → β curr_size)
:  (Internal.heapRemoveLastAux heap aux0 auxl auxr).fst = CompleteTree.leaf := by
  let l := (Internal.heapRemoveLastAux heap aux0 auxl auxr).fst
  have h₁ : l = CompleteTree.leaf := match l with
    | .leaf => rfl
  exact h₁

protected theorem CompleteTree.heapRemoveLastAuxLeavesRoot
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

private theorem CompleteTree.heapRemoveLastAuxIsHeap
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
      simp only [h₄, reduceDite, castZeroHeap]
    else by
      simp[h₄]
      exact
        if h₅ : (m<n ∧ Nat.nextPowerOfTwo (m+1) = m+1) then by
          simp only [h₅, and_self, ↓reduceDite]
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

private theorem CompleteTree.heapRemoveLastIsHeap {α : Type u} {heap : CompleteTree α (o+1)} {le : α → α → Bool} (h₁ : HeapPredicate heap le) (h₂ : transitive_le le) (h₃ : total_le le) : HeapPredicate (Internal.heapRemoveLast heap).fst le :=
  heapRemoveLastAuxIsHeap _ _ _ h₁ h₂ h₃

private theorem CompleteTree.heapRemoveLastWithIndexIsHeap {α : Type u} {heap : CompleteTree α (o+1)} {le : α → α → Bool} (h₁ : HeapPredicate heap le) (h₂ : transitive_le le) (h₃ : total_le le) : HeapPredicate ((Internal.heapRemoveLastWithIndex heap).fst) le :=
  heapRemoveLastAuxIsHeap _ _ _ h₁ h₂ h₃

----------------------------------------------------------------------------------------------
-- heapUpdateRoot

private theorem CompleteTree.heapUpdateRootReturnsRoot {α : Type u} {n : Nat} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) : (heap.heapUpdateRoot le value h₁).snd = heap.root h₁ := by
  unfold heapUpdateRoot
  split
  rename_i o p v l r h₃ h₄ h₅ h₁
  simp
  cases o <;> simp
  case zero =>
    exact root_unfold v l r h₃ h₄ h₅ h₁
  case succ =>
    cases p <;> simp
    case zero =>
      cases le value (root l _)
      <;> simp only [Bool.false_eq_true, ↓reduceIte, root_unfold]
    case succ =>
      cases le value (root l _) <;> cases le value (root r _)
      <;> cases le (root l _) (root r _)
      <;> simp only [Bool.false_eq_true, and_self, and_true, and_false, ↓reduceIte, root_unfold]

private theorem CompleteTree.heapUpdateRootPossibleRootValuesAuxL {α : Type u} (heap : CompleteTree α n) (h₁ : n > 1) : 0 < heap.leftLen (Nat.lt_trans (Nat.lt_succ_self 0) h₁) :=
  match h₅: n, heap with
  | (o+p+1), .branch v l r h₂ h₃ h₄ => by
    simp[leftLen, length]
    cases o
    case zero => rewrite[(Nat.le_zero_eq p).mp h₂] at h₁; contradiction
    case succ q => exact Nat.zero_lt_succ q

private theorem CompleteTree.heapUpdateRootPossibleRootValuesAuxR {α : Type u} (heap : CompleteTree α n) (h₁ : n > 2) : 0 < heap.rightLen (Nat.lt_trans (Nat.lt_succ_self 0) $ Nat.lt_trans (Nat.lt_succ_self 1) h₁) :=
  match h₅: n, heap with
  | (o+p+1), .branch v l r h₂ h₃ h₄ => by
    simp[rightLen, length]
    cases p
    case zero => simp_arith at h₁; simp at h₃; exact absurd h₁ (Nat.not_le_of_gt h₃)
    case succ q => exact Nat.zero_lt_succ q

private theorem CompleteTree.heapUpdateRootPossibleRootValues1 {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n = 1) : (heap.heapUpdateRoot le value (h₁.substr (Nat.lt_succ_self 0))).fst.root (h₁.substr (Nat.lt_succ_self 0)) = value := by
  unfold heapUpdateRoot
  generalize (h₁.substr (Nat.lt_succ_self 0) : n > 0) = hx
  split
  rename_i o p v l r _ _ _ h₁
  have h₃ : o = 0 := (Nat.add_eq_zero.mp $ Nat.succ.inj h₁).left
  simp[h₃, root_unfold]

private theorem CompleteTree.heapUpdateRootPossibleRootValues2 {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n = 2) :
have h₂ : 0 < n := Nat.lt_trans (Nat.lt_succ_self 0) $  h₁.substr (Nat.lt_succ_self 1)
have h₃ : 0 < leftLen heap h₂ := heapUpdateRootPossibleRootValuesAuxL heap (h₁.substr (Nat.lt_succ_self 1))
(heap.heapUpdateRoot le value h₂).fst.root h₂ = value
∨ (heap.heapUpdateRoot le value h₂).fst.root h₂ = (heap.left h₂).root h₃
:= by
  simp
  unfold heapUpdateRoot
  generalize (Nat.lt_trans (Nat.lt_succ_self 0) (Eq.substr h₁ (Nat.lt_succ_self 1)) : 0 < n) = h₂
  split
  rename_i o p v l r h₃ h₄ h₅ h₂
  cases o <;> simp
  case zero => simp only[root, true_or]
  case succ oo =>
    have h₆ : p = 0 := by simp at h₁; omega
    simp only [h₆, ↓reduceDite]
    cases le value (l.root _)
    <;> simp[heapUpdateRootReturnsRoot, root_unfold, left_unfold]

private theorem CompleteTree.heapUpdateRootPossibleRootValues3 {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 2) :
have h₂ : 0 < n := Nat.lt_trans (Nat.lt_succ_self 0) $ Nat.lt_trans (Nat.lt_succ_self 1) h₁
have h₃ : 0 < leftLen heap h₂ := heapUpdateRootPossibleRootValuesAuxL heap $ Nat.lt_trans (Nat.lt_succ_self 1) h₁
have h₄ : 0 < rightLen heap h₂ := heapUpdateRootPossibleRootValuesAuxR heap h₁
(heap.heapUpdateRoot le value h₂).fst.root h₂ = value
∨ (heap.heapUpdateRoot le value h₂).fst.root h₂ = (heap.left h₂).root h₃
∨ (heap.heapUpdateRoot le value h₂).fst.root h₂ = (heap.right h₂).root h₄
:= by
  simp only
  unfold heapUpdateRoot
  generalize (Nat.lt_trans (Nat.lt_succ_self 0) (Nat.lt_trans (Nat.lt_succ_self 1) h₁) : 0 < n) = h₂
  split
  rename_i o p v l r h₃ h₄ h₅ h₂
  cases o
  case zero => simp only[root, true_or]
  case succ oo =>
    have h₆ : p ≠ 0 := by simp at h₁; omega
    simp only [Nat.add_one_ne_zero, ↓reduceDite, h₆]
    cases le value (l.root _) <;> simp
    rotate_right
    cases le value (r.root _) <;> simp
    case true.true => simp[root]
    case false | true.false =>
      cases le (l.root _) (r.root _)
      <;> simp only [Bool.false_eq_true, ↓reduceIte, heapUpdateRootReturnsRoot, root_unfold, left_unfold, right_unfold, true_or, or_true]

private theorem CompleteTree.heapUpdateRootIsHeapLeRootAux {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : HeapPredicate heap le) (h₂ : n > 0) (h₃ : le (root heap h₂) value) : HeapPredicate.leOrLeaf le (root heap h₂) (heapUpdateRoot le value heap h₂).fst :=
  if h₄ : n = 1 then by
    have h₅ : le (heap.root h₂) ( (heapUpdateRoot le value heap h₂).fst.root h₂) := by simp only[h₃, h₄, heapUpdateRootPossibleRootValues1]
    unfold HeapPredicate.leOrLeaf
    split
    · rfl
    · exact h₅
  else if h₅ : n = 2 then by
    have h₆ := heapUpdateRootPossibleRootValues2 le value heap h₅
    cases h₆
    case inl h₆ =>
      have h₇ : le (heap.root h₂) ( (heapUpdateRoot le value heap h₂).fst.root h₂) := by simp only [h₆, h₃]
      unfold HeapPredicate.leOrLeaf
      split
      · rfl
      · exact h₇
    case inr h₆ =>
      unfold HeapPredicate.leOrLeaf
      unfold HeapPredicate at h₁
      split at h₁
      case h_1 => contradiction
      case h_2 o p v l r h₇ h₈ h₉ =>
        have h₁₁ : p = 0 := by
         simp at h₅
         cases o; simp only [Nat.le_zero_eq] at h₇; exact h₇; simp_arith[Nat.add_eq_zero] at h₅; exact h₅.right
        have h₁₀ : o = 1 := by simp_arith[h₁₁] at h₅; assumption
        simp only
        rw[h₆]
        have h₁₂ := h₁.right.right.left
        unfold HeapPredicate.leOrLeaf at h₁₂
        cases o ; contradiction;
        case succ =>
          exact h₁₂
  else by
    have h₆ : n > 2 := by omega
    have h₇ := heapUpdateRootPossibleRootValues3 le value heap h₆
    simp at h₇
    unfold HeapPredicate at h₁
    cases h₇
    case inl h₇ =>
      have h₈ : le (heap.root h₂) ( (heapUpdateRoot le value heap h₂).fst.root h₂) := by simp only [h₇, h₃]
      unfold HeapPredicate.leOrLeaf
      split
      · rfl
      · exact h₈
    case inr h₇ =>
      cases h₇
      case inl h₇ | inr h₇ =>
        unfold HeapPredicate.leOrLeaf
        split at h₁
        contradiction
        simp_all
        case h_2 o p v l r _ _ _ =>
          cases o
          omega
          cases p
          omega
          have h₈ := h₁.right.right.left
          have h₉ := h₁.right.right.right
          assumption

private theorem CompleteTree.heapUpdateRootIsHeapLeRootAuxLe {α : Type u} (le : α → α → Bool) {a b c : α} (h₁ : transitive_le le) (h₂ : total_le le) (h₃ : le b c) : ¬le a c ∨ ¬ le a b → le b a
| .inr h₅ => not_le_imp_le h₂ _ _ h₅
| .inl h₅ => h₁ b c a ⟨h₃,not_le_imp_le h₂ _ _ h₅⟩

theorem CompleteTree.heapUpdateRootIsHeap {α : Type u} {n: Nat} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) (h₂ : HeapPredicate heap le) (h₃ : transitive_le le) (h₄ : total_le le) : HeapPredicate (heap.heapUpdateRoot le value h₁).fst le := by
    unfold heapUpdateRoot
    split
    rename_i o p v l r h₇ h₈ h₉ heq
    exact
      if h₁₀ : o = 0 then by
        simp only [Nat.add_eq, Nat.succ_eq_add_one, h₁₀, ↓reduceDite]
        unfold HeapPredicate at h₂ ⊢
        simp only [h₂, true_and]
        unfold HeapPredicate.leOrLeaf
        have : p = 0 := by rw[h₁₀, Nat.le_zero_eq] at h₇; assumption
        apply And.intro
        case left => match o, l with
        | Nat.zero, _ => trivial
        case right => match p, r with
        | Nat.zero, _ => trivial
      else if h₁₁ : p = 0 then by
        simp only [↓reduceDite, h₁₀, h₁₁]
        cases h₉ : le value (root l (_ : 0 < o)) <;> simp
        case true =>
          unfold HeapPredicate at *
          simp only [h₂, true_and]
          unfold HeapPredicate.leOrLeaf
          apply And.intro
          case right => match p, r with
          | Nat.zero, _ => trivial
          case left => match o, l with
          | Nat.succ _, _ => assumption
        case false =>
          rw[heapUpdateRootReturnsRoot]
          have h₁₂ : le (l.root (Nat.zero_lt_of_ne_zero h₁₀)) value := by simp[h₉, h₄, not_le_imp_le]
          have h₁₃ : o = 1 := Nat.le_antisymm (by simp_arith[h₁₁] at h₈; exact h₈) (Nat.succ_le_of_lt (Nat.zero_lt_of_ne_zero h₁₀))
          unfold HeapPredicate at *
          simp only [h₂, true_and] --closes one sub-goal
          apply And.intro <;> try apply And.intro
          case right.right => match p, r with
            | 0, .leaf => simp[HeapPredicate.leOrLeaf]
          case right.left =>
            simp only [HeapPredicate.leOrLeaf]
            cases o <;> simp only [Nat.succ_eq_add_one, heapUpdateRootPossibleRootValues1, h₁₃, h₁₂]
          case left =>
            apply heapUpdateRootIsHeap
            exact h₂.left
            exact h₃
            exact h₄
      else if h₁₂ : le value (root l (Nat.zero_lt_of_ne_zero h₁₀)) ∧ le value (root r (Nat.zero_lt_of_ne_zero h₁₁)) then by
        unfold HeapPredicate at *
        simp only [↓reduceDite, and_self, ↓reduceIte, true_and, h₁₀, h₁₁, h₁₂, h₂]
        unfold HeapPredicate.leOrLeaf
        cases o
        · contradiction
        · cases p
          · contradiction
          · assumption
      else by
        simp only [↓reduceDite, ↓reduceIte, h₁₀, h₁₁, h₁₂]
        have h₁₃ : ¬le value (root l _) ∨ ¬le value (root r _) := (Decidable.not_and_iff_or_not (le value (root l (Nat.zero_lt_of_ne_zero h₁₀)) = true) (le value (root r (Nat.zero_lt_of_ne_zero h₁₁)) = true)).mp h₁₂
        cases h₁₄ : le (root l (_ : 0 < o)) (root r (_ : 0 < p))
        <;> simp only [Bool.false_eq_true, ↓reduceIte]
        <;> unfold HeapPredicate at *
        <;> simp only [true_and, h₂]
        <;> apply And.intro
        <;> try apply And.intro
        case false.left | true.left =>
          apply heapUpdateRootIsHeap
          <;> simp only [h₂, h₃, h₄]
        case false.right.left =>
          unfold HeapPredicate.leOrLeaf
          have h₁₅ : le (r.root _) (l.root _) = true := not_le_imp_le h₄ (l.root _) (r.root _) $ (Bool.not_eq_true $ le (root l (_ : 0 < o)) (root r (_ : 0 < p))).substr h₁₄
          simp only[heapUpdateRootReturnsRoot]
          cases o <;> simp only[h₁₅]
        case true.right.right =>
          unfold HeapPredicate.leOrLeaf
          simp only[heapUpdateRootReturnsRoot]
          cases p <;> simp only[h₁₄]
        case false.right.right =>
          have h₁₅ : le (r.root _) (l.root _) = true := not_le_imp_le h₄ (l.root _) (r.root _) $ (Bool.not_eq_true $ le (root l (_ : 0 < o)) (root r (_ : 0 < p))).substr h₁₄
          have h₁₆ : le (r.root _) value := heapUpdateRootIsHeapLeRootAuxLe le h₃ h₄ h₁₅ h₁₃
          simp only [heapUpdateRootReturnsRoot, heapUpdateRootIsHeapLeRootAux, h₂, h₁₆]
        case true.right.left =>
          have h₁₆ : le (l.root _) value := heapUpdateRootIsHeapLeRootAuxLe le h₃ h₄ h₁₄ h₁₃.symm
          simp only [heapUpdateRootReturnsRoot, heapUpdateRootIsHeapLeRootAux, h₂, h₁₆]

----------------------------------------------------------------------------------------------
-- heapUpdateAt

private theorem CompleteTree.heapUpdateAtIsHeapLeRootAux_RootLeValue {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) (h₁ : HeapPredicate heap le) (h₂ : n > 0) (h₃ : le (root heap h₂) value) (h₄ : total_le le) : HeapPredicate.leOrLeaf le (root heap h₂) (heapUpdateAt le index value heap h₂).fst := by
  unfold heapUpdateAt
  split
  case isTrue => exact heapUpdateRootIsHeapLeRootAux le value heap h₁ h₂ h₃
  case isFalse hi =>
    split
    rename_i o p v l r h₆ h₇ h₈ index h₁ h₅
    cases h₉ : le v value <;> simp (config := { ground := true }) only
    case false => rw[root_unfold] at h₃; exact absurd h₃ ((Bool.not_eq_true (le v value)).substr h₉)
    case true =>
      rw[root_unfold]
      split
      <;> simp![reflexive_le, h₄]

private theorem CompleteTree.heapUpdateAtIsHeapLeRootAux_ValueLeRoot {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) (h₁ : HeapPredicate heap le) (h₂ : n > 0) (h₃ : le value (root heap h₂)) (h₄ : total_le le) (h₅ : transitive_le le) : HeapPredicate.leOrLeaf le value (heapUpdateAt le index value heap h₂).fst := by
  unfold heapUpdateAt
  split
  <;> rename_i h₉
  case isTrue =>
    unfold heapUpdateRoot
    split
    rename_i o p v l r h₆ h₇ h₈ h₂
    cases o <;> cases p <;> simp only [↓reduceDite,HeapPredicate.leOrLeaf, root_unfold, h₄, reflexive_le]
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

theorem CompleteTree.heapUpdateAtIsHeap {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) (h₂ : HeapPredicate heap le) (h₃ : transitive_le le) (h₄ : total_le le) : HeapPredicate (heap.heapUpdateAt le index value h₁).fst le := by
  unfold heapUpdateAt
  split
  case isTrue h₅ =>
    exact heapUpdateRootIsHeap le value heap h₁ h₂ h₃ h₄
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
      case left => exact heapUpdateAtIsHeap le ⟨index.val - o - 1, _⟩ v r h₁₄ h₂.right.left h₃ h₄
      case right.left => exact HeapPredicate.leOrLeaf_transitive h₃ h₁₀ h₂.right.right.left
      case right.right =>
        have h₁₁: HeapPredicate (heapUpdateAt le ⟨index.val - o - 1, (by omega)⟩ v r h₁₄).fst le :=
          (heapUpdateAtIsHeap le ⟨index.val - o - 1, (by omega)⟩ v r _ h₂.right.left h₃ h₄)
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
      case left => exact heapUpdateAtIsHeap le ⟨index.val - 1, _⟩ v l h₁₄ h₂.left h₃ h₄
      case right.right => exact HeapPredicate.leOrLeaf_transitive h₃ h₁₀ h₂.right.right.right
      case right.left =>
        have h₁₁: HeapPredicate (heapUpdateAt le ⟨index.val - 1, (_)⟩ v l h₁₄).fst le :=
          (heapUpdateAtIsHeap le ⟨index.val - 1, (by omega)⟩ v l _ h₂.left h₃ h₄)
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
      case left => exact heapUpdateAtIsHeap le ⟨index.val - o - 1, _⟩ value r h₁₄ h₂.right.left h₃ h₄
      case right =>
        have h₁₁: HeapPredicate (heapUpdateAt le ⟨index.val - o - 1, (by omega)⟩ v r (h₁₄)).fst le :=
          (heapUpdateAtIsHeap le ⟨index.val - o - 1, (by omega)⟩ v r _ h₂.right.left h₃ h₄)
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
      case left => exact heapUpdateAtIsHeap le ⟨index.val - 1, _⟩ value l h₁₄ h₂.left h₃ h₄
      case right =>
        have h₁₁: HeapPredicate (heapUpdateAt le ⟨index.val - 1, (by omega)⟩ v l h₁₄).fst le :=
          (heapUpdateAtIsHeap le ⟨index.val - 1, (by omega)⟩ v l _ h₂.left h₃ h₄)
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

----------------------------------------------------------------------------------------------
-- heapPop

theorem CompleteTree.heapPopIsHeap {α : Type u} {n : Nat} (le : α → α → Bool) (heap : CompleteTree α (n+1)) (h₁ : HeapPredicate heap le) (wellDefinedLe : transitive_le le ∧ total_le le) : HeapPredicate (heap.heapPop le).fst le := by
  have h₂ : HeapPredicate (Internal.heapRemoveLast heap).fst le := heapRemoveLastIsHeap h₁ wellDefinedLe.left wellDefinedLe.right
  unfold heapPop
  cases n <;> simp[h₂, heapUpdateRootIsHeap, wellDefinedLe]

----------------------------------------------------------------------------------------------
-- heapRemoveAt

theorem CompleteTree.heapRemoveAtIsHeap {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin (n+1)) (heap : CompleteTree α (n+1)) (h₁ : HeapPredicate heap le) (wellDefinedLe : transitive_le le ∧ total_le le) : HeapPredicate (heap.heapRemoveAt le index).fst le := by
  have h₂ : HeapPredicate (Internal.heapRemoveLastWithIndex heap).fst le := heapRemoveLastWithIndexIsHeap h₁ wellDefinedLe.left wellDefinedLe.right
  unfold heapRemoveAt
  split
  case isTrue => exact heapPopIsHeap le heap h₁ wellDefinedLe
  case isFalse h₃ =>
    cases h: (index = (Internal.heapRemoveLastWithIndex heap).snd.snd : Bool)
    <;> simp_all
    split
    <;> apply heapUpdateAtIsHeap <;> simp_all
