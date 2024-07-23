import BinaryHeap.HeapPredicate
import BinaryHeap.CompleteTree.Basic
import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.HeapProofs
import BinaryHeap.CompleteTree.AdditionalProofs

namespace BinaryHeap

-------------------------------------------------------------------------------------------------------

/-

/--Please do not use this for anything meaningful. It's a debug function, with horrible performance. For this to work, comment out the Repr derive.-/
private instance {α : Type u} [ToString α] : ToString (CompleteTree α n) where
  toString := λt ↦
    --not very fast, doesn't matter, is for debugging
    let rec max_width := λ {m : Nat} (t : (CompleteTree α m)) ↦ match m, t with
    | 0, .leaf => 0
    | (_+_+1), CompleteTree.branch a left right _ _ _ => max (ToString.toString a).length $ max (max_width left) (max_width right)
    let max_width := max_width t
    let lines_left := Nat.log2 (n+1).nextPowerOfTwo
    let rec print_line := λ (mw : Nat) {m : Nat} (t : (CompleteTree α m)) (lines : Nat)  ↦
      match m, t with
      | 0, _ => ""
      | (_+_+1), CompleteTree.branch a left right _ _ _ =>
        let thisElem := ToString.toString a
        let thisElem := (List.replicate (mw - thisElem.length) ' ').asString ++ thisElem
        let elems_in_last_line := if lines == 0 then 0 else 2^(lines-1)
        let total_chars_this_line := elems_in_last_line * mw + 2*(elems_in_last_line)+1
        let left_offset := (total_chars_this_line - mw) / 2
        let whitespaces := max left_offset 1
        let whitespaces := List.replicate whitespaces ' '
        let thisline := whitespaces.asString ++ thisElem ++ whitespaces.asString ++"\n"
        let leftLines := (print_line mw left (lines-1) ).splitOn "\n"
        let rightLines := (print_line mw right (lines-1) ).splitOn "\n" ++ [""]
        let combined := leftLines.zip (rightLines)
        let combined := combined.map λ (a : String × String) ↦ a.fst ++ a.snd
        thisline ++ combined.foldl (· ++ "\n" ++ ·) ""
    print_line max_width t lines_left


private def TestHeap :=
  let ins : {n: Nat} → Nat → CompleteTree Nat n → CompleteTree Nat (n+1) := λ x y ↦ CompleteTree.heapPush (.≤.) x y
  ins 5 CompleteTree.empty
  |> ins 3
  |> ins 7
  |> ins 12
  |> ins 13
  |> ins 2
  |> ins 8
  |> ins 97
  |> ins 2
  |> ins 64
  |> ins 71
  |> ins 21
  |> ins 3
  |> ins 4
  |> ins 199
  |> ins 24
  |> ins 3

#eval TestHeap
#eval TestHeap.indexOf (4 = ·)

#eval TestHeap.heapRemoveAt (.≤.) 14

private def TestHeap2 :=
  let ins : {n: Nat} → Nat → CompleteTree Nat n → CompleteTree Nat (n+1) := λ x y ↦ CompleteTree.heapPush (.≤.) x y
  ins 5 CompleteTree.empty
  |> ins 1
  |> ins 2
  |> ins 3


#eval TestHeap2
#eval TestHeap2.heapRemoveAt (.≤.) 2
#eval TestHeap2.heapUpdateAt (.≤.) 3 27 (by omega)

-/
