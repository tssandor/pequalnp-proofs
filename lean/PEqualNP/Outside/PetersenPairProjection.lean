import Mathlib
import PEqualNP.Defs

namespace PetersenPairProjection

def F (a : Bool) (y : Fin 8 → Bool) :=
  (a && y 0) || (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && a) ||
  (a && y 4) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) ||
  (y 4 && y 6) || (y 5 && y 7) || (y 7 && y 4)

def adjacent (i j : Fin 8) :=
  F false (fun k => decide (k = i ∨ k = j))

def masks : List Nat :=
  [1,5,8,9,10,16,17,18,20,21,24,25,26,40,42,48,50,52,56,58,65,69,72,73,104,129,136,137,138,193,200,201]

def bits (m : Nat) (i : Fin 8) := m.testBit i.val

theorem live : ∀ m ∈ masks, F false (bits m) = false ∧ F true (bits m) = true := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem samples : ∀ (i j : Fin 8), i ≠ j → ∀ u v : Bool,
    (adjacent i j && u && v) = false → ∃ m ∈ masks, bits m i = u ∧ bits m j = v := by decide

-- If all influence of the distinguished input enters through one AND or OR,
-- classify a nonconstant companion depending on just two other variables.
theorem companion
    (i j : Fin 8) (ne : i ≠ j) (isAnd : Bool)
    (side : Bool → Bool → Bool) (polarity : Bool → Bool)
    (rest : (Fin 8 → Bool) → Bool → Bool)
    (correct : ∀ a y, F a y = rest y
      (if isAnd then polarity a && side (y i) (y j) else polarity a || side (y i) (y j)))
    (varies : ∃ u v, side u v ≠ isAnd) :
    adjacent i j = true ∧ ∀ u v, side u v = if u && v then !isAnd else isAnd := by
  have pass (u v : Bool) (h : (adjacent i j && u && v) = false) : side u v = isAnd := by
    obtain ⟨m, hm, hu, hv⟩ := samples i j ne u v h
    obtain ⟨lo, hi⟩ := live m hm
    have f0 := correct false (bits m)
    have f1 := correct true (bits m)
    rw [lo, hu, hv] at f0
    rw [hi, hu, hv] at f1
    by_contra bad
    cases isAnd <;> cases hs : side u v <;>
      first | exact bad hs | (
        simp only [hs, Bool.false_eq_true, ite_false, ite_true, Bool.or_true, Bool.and_false] at f0 f1
        exact Bool.noConfusion (f0.trans f1.symm))
  obtain ⟨u, v, fail⟩ := varies
  have hot : (adjacent i j && u && v) = true := by
    cases h : (adjacent i j && u && v)
    · exact False.elim (fail (pass u v h))
    · rfl
  obtain ⟨⟨edge, hu⟩, hv⟩ := Bool.and_eq_true_iff.mp hot |>.imp_left Bool.and_eq_true_iff.mp
  subst u
  subst v
  refine ⟨edge, ?_⟩
  intro u v
  cases u <;> cases v
  · exact pass _ _ (by simp)
  · exact pass _ _ (by simp)
  · exact pass _ _ (by simp)
  · cases isAnd <;> cases hs : side true true <;> first | rfl | exact False.elim (fail hs)


set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem edgePresent : ∀ (i j : Fin 8), adjacent i j = true → ∀ (a : Bool) (y : Fin 8 → Bool),
    y i = true → y j = true → F a y = true := by
  intro i j hij a y h1 h2
  fin_cases i <;> fin_cases j <;> simp [adjacent, F] at hij <;>
    simp only [F, Bool.or_eq_true_iff, Bool.and_eq_true_iff] <;> tauto

theorem moveToOutput
    (i j : Fin 8) (ne : i ≠ j) (isAnd : Bool)
    (side : Bool → Bool → Bool) (polarity : Bool → Bool)
    (rest : (Fin 8 → Bool) → Bool → Bool)
    (correct : ∀ a y, F a y = rest y
      (if isAnd then polarity a && side (y i) (y j) else polarity a || side (y i) (y j)))
    (varies : ∃ u v, side u v ≠ isAnd) (a : Bool) (y : Fin 8 → Bool) :
    F a y = ((y i && y j) || rest y (polarity a)) := by
  obtain ⟨hedge, hside⟩ := companion i j ne isAnd side polarity rest correct varies
  by_cases has : (y i && y j) = true
  · obtain ⟨hi, hj⟩ := Bool.and_eq_true_iff.mp has
    rw [edgePresent i j hedge a y hi hj, has]
    rfl
  · have zero : (y i && y j) = false := by exact Bool.eq_false_iff.mpr has
    have h := correct a y
    rw [hside, zero] at h
    rw [zero]
    cases isAnd <;> simpa using h

end PetersenPairProjection
