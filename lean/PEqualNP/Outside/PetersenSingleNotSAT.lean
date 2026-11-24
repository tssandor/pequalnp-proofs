import Mathlib
import PEqualNP.Library.LRAT.Link

namespace PetersenRailLink

open PEqualNP.Library.LRAT PEqualNP.Library.LRAT.Link
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def graphValue (r : Nat) : Bool :=
  edges.any fun (u,v) => r.testBit u && r.testBit v

def target (x : Fin 9 → Bool) :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def rows : List Nat :=
  [3,13,17,33,69,133,201,261,265,321,385,518,524,536,554,562,578,616,628,644,650,672,
   712,720,776,788,800,832,914]

theorem rows_valid : ∀ r ∈ rows, r < 2 ^ 10 ∧ r.testBit 9 = !r.testBit 0 := by decide

theorem enc_on_rows (n s : Nat) (a b : Nat → Bool) (rs : List Nat)
    (agrees : ∀ r ∈ rs, a r = b r) : enc n s a rs = enc n s b rs := by
  have outputs : fOutEq n s a rs = fOutEq n s b rs := by
    induction rs with
    | nil => rfl
    | cons r rest ih =>
      have left : ∀ k, outEq n s a k r = outEq n s b k r := by
        intro k
        simp only [outEq, agrees r List.mem_cons_self]
      have restEq := ih (fun u hu => agrees u (List.mem_cons_of_mem _ hu))
      change (List.range (n + s + 1)).flatMap (fun k => outEq n s a k r) ++ fOutEq n s a rest = _
      rw [show (fun k => outEq n s a k r) = (fun k => outEq n s b k r) by funext k; exact left k,restEq]
      rfl
  simp only [enc,outputs]

theorem graph_agrees (r : Nat) : target (fun i => r.testBit i.val) = graphValue r := by
  simp [target,graphValue,edges,Bool.or_assoc]

theorem tail_implies_sat (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 14)
    (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!(x 0)]) = target x) :
    FormulaSat (enc 10 14 graphValue rows) := by
  let f := circuitFun 10 C
  have sat := link 10 14 f rows (fun r hr => (rows_valid r hr).1) C hm hs (fun _ => rfl)
  have onRows : ∀ r ∈ rows, rowFun 10 f r = graphValue r := by
    intro r hr
    let x : Fin 9 → Bool := fun i => r.testBit i.val
    have bits : List.ofFn (fun i : Fin 10 => r.testBit i.val) = List.ofFn x ++ [r.testBit 9] := rfl
    change C.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = graphValue r
    rw [bits,(rows_valid r hr).2]
    exact (correct x).trans (graph_agrees r)
  rw [enc_on_rows _ _ _ _ _ onRows] at sat
  exact sat

end PetersenRailLink

namespace PEqualNP.Outside.PetersenRailHead
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev edge (x : Fin 9 → Bool) :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
  x 6 && x 8 || x 8 && x 5

def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun t g => t ++ [g.op.eval (g.inputs.map fun i => t.getD i false)]) w

theorem keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]


theorem monotoneTail (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 15)
    (head : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 0))
    (only : ∀ g ∈ C.gates.drop 1, g.op ≠ GateOp.not)
    (correct : circuitFun 9 C = edge) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 14 ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!(x 0)]) = edge x := by
  cases h : C.gates with
  | nil =>
    have ht := head (fun _ => false)
    change (run C.gates _).getD 9 false = true at ht
    simp [h, run] at ht
  | cons g gs =>
    refine ⟨⟨gs, C.output⟩, ?_, ?_, ?_⟩
    · intro k hk
      obtain ⟨hop, hlen⟩ := fan k (h ▸ List.mem_cons_of_mem g hk)
      have hn := only k (by simpa [h] using hk)
      refine ⟨?_, hlen⟩
      rcases hop with ha | ho | hn'
      · exact Or.inl ha
      · exact Or.inr ho
      · exact False.elim (hn hn')
    · change gs.length ≤ 14
      simp [Circuit.size, h] at small
      omega
    · intro x
      let w := List.ofFn x
      let b := g.op.eval (g.inputs.map fun i => w.getD i false)
      have hh := head x
      change (run C.gates w).getD 9 false = !(x 0) at hh
      rw [h] at hh
      change (run gs (w ++ [b])).getD 9 false = !(x 0) at hh
      rw [keeps _ _ _ (by simp [w])] at hh
      have last : (w ++ [b]).getD 9 false = b := by
        rw [List.getD_append_right _ _ _ _ (by simp [w])]
        simp [w]
      have hb := last.symm.trans hh
      have hc := congrFun correct x
      change (run C.gates w).getD C.output false = edge x at hc
      rw [h] at hc
      change (run gs (w ++ [b])).getD C.output false = edge x at hc
      rw [hb] at hc
      exact hc
end PEqualNP.Outside.PetersenRailHead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Library.LRAT PEqualNP.Library.LRAT.Link

-- A certificate for the unmodified project encoding would settle the one-NOT case.
theorem PEqualNP.Outside.PetersenSingleNotSAT
    (unsat : ¬ FormulaSat (enc 10 14 PetersenRailLink.graphValue PetersenRailLink.rows))
    (C : Circuit) (fan : FanInTwo C)
    (head : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 0))
    (only : ∀ g ∈ C.gates.drop 1, g.op ≠ GateOp.not)
    (correct : circuitFun 9 C = PetersenRailLink.target) : 16 ≤ C.size := by
  by_contra! small
  obtain ⟨D, hm, hs, hc⟩ := PEqualNP.Outside.PetersenRailHead.monotoneTail C fan (by omega) head only correct
  exact unsat (PetersenRailLink.tail_implies_sat D hm hs hc)
