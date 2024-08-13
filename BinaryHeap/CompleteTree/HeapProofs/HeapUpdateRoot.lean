import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.Lemmas

namespace BinaryHeap.CompleteTree

theorem heapUpdateRootReturnsRoot {α : Type u} {n : Nat} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) : (heap.heapUpdateRoot le value h₁).snd = heap.root h₁ := by
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

private theorem heapUpdateRootPossibleRootValuesAuxL {α : Type u} (heap : CompleteTree α n) (h₁ : n > 1) : 0 < heap.leftLen (Nat.lt_trans (Nat.lt_succ_self 0) h₁) :=
  match h₅: n, heap with
  | (o+p+1), .branch v l r h₂ h₃ h₄ => by
    simp[leftLen, length]
    cases o
    case zero => rewrite[(Nat.le_zero_eq p).mp h₂] at h₁; contradiction
    case succ q => exact Nat.zero_lt_succ q

private theorem heapUpdateRootPossibleRootValuesAuxR {α : Type u} (heap : CompleteTree α n) (h₁ : n > 2) : 0 < heap.rightLen (Nat.lt_trans (Nat.lt_succ_self 0) $ Nat.lt_trans (Nat.lt_succ_self 1) h₁) :=
  match h₅: n, heap with
  | (o+p+1), .branch v l r h₂ h₃ h₄ => by
    simp[rightLen, length]
    cases p
    case zero => simp_arith at h₁; simp at h₃; exact absurd h₁ (Nat.not_le_of_gt h₃)
    case succ q => exact Nat.zero_lt_succ q

private theorem heapUpdateRootPossibleRootValues1 {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n = 1) : (heap.heapUpdateRoot le value (h₁.substr (Nat.lt_succ_self 0))).fst.root (h₁.substr (Nat.lt_succ_self 0)) = value := by
  unfold heapUpdateRoot
  generalize (h₁.substr (Nat.lt_succ_self 0) : n > 0) = hx
  split
  rename_i o p v l r _ _ _ h₁
  have h₃ : o = 0 := (Nat.add_eq_zero.mp $ Nat.succ.inj h₁).left
  simp[h₃, root_unfold]

private theorem heapUpdateRootPossibleRootValues2 {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n = 2) :
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
    simp only [h₆, ↓reduceDIte]
    cases le value (l.root _)
    <;> simp[heapUpdateRootReturnsRoot, root_unfold, left_unfold]

private theorem heapUpdateRootPossibleRootValues3 {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 2) :
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
    simp only [Nat.add_one_ne_zero, ↓reduceDIte, h₆]
    cases le value (l.root _) <;> simp
    rotate_right
    cases le value (r.root _) <;> simp
    case true.true => simp[root]
    case false | true.false =>
      cases le (l.root _) (r.root _)
      <;> simp only [Bool.false_eq_true, ↓reduceIte, heapUpdateRootReturnsRoot, root_unfold, left_unfold, right_unfold, true_or, or_true]

protected theorem heapUpdateRootIsHeapLeRootAux {α : Type u} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : HeapPredicate heap le) (h₂ : n > 0) (h₃ : le (root heap h₂) value) : HeapPredicate.leOrLeaf le (root heap h₂) (heapUpdateRoot le value heap h₂).fst :=
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

private theorem heapUpdateRootIsHeapLeRootAuxLe {α : Type u} (le : α → α → Bool) {a b c : α} (h₁ : transitive_le le) (h₂ : total_le le) (h₃ : le b c) : ¬le a c ∨ ¬ le a b → le b a
| .inr h₅ => not_le_imp_le h₂ _ _ h₅
| .inl h₅ => h₁ b c a ⟨h₃,not_le_imp_le h₂ _ _ h₅⟩

theorem heapUpdateRootIsHeap {α : Type u} {n: Nat} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) (h₂ : HeapPredicate heap le) (h₃ : transitive_le le) (h₄ : total_le le) : HeapPredicate (heap.heapUpdateRoot le value h₁).fst le := by
    unfold heapUpdateRoot
    split
    rename_i o p v l r h₇ h₈ h₉ heq
    exact
      if h₁₀ : o = 0 then by
        simp only [Nat.add_eq, Nat.succ_eq_add_one, h₁₀, ↓reduceDIte]
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
        simp only [↓reduceDIte, h₁₀, h₁₁]
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
        simp only [↓reduceDIte, and_self, ↓reduceIte, true_and, h₁₀, h₁₁, h₁₂, h₂]
        unfold HeapPredicate.leOrLeaf
        cases o
        · contradiction
        · cases p
          · contradiction
          · assumption
      else by
        simp only [↓reduceDIte, ↓reduceIte, h₁₀, h₁₁, h₁₂]
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
          simp only [heapUpdateRootReturnsRoot, CompleteTree.heapUpdateRootIsHeapLeRootAux, h₂, h₁₆]
        case true.right.left =>
          have h₁₆ : le (l.root _) value := heapUpdateRootIsHeapLeRootAuxLe le h₃ h₄ h₁₄ h₁₃.symm
          simp only [heapUpdateRootReturnsRoot, CompleteTree.heapUpdateRootIsHeapLeRootAux, h₂, h₁₆]
