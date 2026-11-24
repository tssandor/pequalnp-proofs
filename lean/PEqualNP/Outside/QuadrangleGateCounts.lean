import Mathlib
import PEqualNP.Defs

-- On a rejected input, one false operand suffices at every false AND.
-- Different maximal independent sets require different choices.
namespace PEqualNP.Outside.QuadrangleGateCounts
namespace SaturatedQuadrangles
open PEqualNP.HeptadCover
abbrev Pt := Fin 13
abbrev Row := Finset Pt × Finset Pt

def block0 : List Row := [
  ({0,1,2,5},{3,7,8}),
  ({0,1,2,6},{7,8,9}),
  ({0,1,2,7},{3,8,9}),
  ({0,1,2,11},{3,7,9}),
  ({0,1,4,6},{2,7,9}),
  ({0,1,4,8},{2,6,9}),
  ({0,1,4,11},{6,7,9}),
  ({0,1,4,12},{2,6,7}),
  ({0,1,5,10},{3,6,8}),
  ({0,1,5,11},{3,6,7})]
def block1 : List Row := [
  ({0,1,5,12},{6,7,8}),
  ({0,1,6,7},{2,8,9}),
  ({0,1,6,12},{2,7,8}),
  ({0,1,7,8},{2,3,9}),
  ({0,1,7,10},{2,3,8}),
  ({0,1,8,10},{2,3,6}),
  ({0,1,8,11},{3,6,9}),
  ({0,1,10,12},{2,6,8}),
  ({0,2,3,4},{5,9,11}),
  ({0,2,3,6},{8,9,11})]
def block2 : List Row := [
  ({0,2,3,7},{5,8,9}),
  ({0,2,3,10},{5,8,11}),
  ({0,2,4,6},{7,9,11}),
  ({0,2,4,9},{5,7,11}),
  ({0,2,4,11},{5,7,9}),
  ({0,2,5,6},{7,8,11}),
  ({0,2,5,9},{3,7,11}),
  ({0,2,5,10},{3,8,11}),
  ({0,2,7,10},{3,5,8}),
  ({0,2,7,11},{3,5,9})]
def block3 : List Row := [
  ({0,2,9,10},{3,5,11}),
  ({0,2,9,11},{3,5,7}),
  ({0,3,4,8},{6,9,11}),
  ({0,3,4,10},{5,6,11}),
  ({0,3,4,11},{5,6,9}),
  ({0,3,5,6},{1,8,11}),
  ({0,3,5,8},{1,6,11}),
  ({0,3,5,10},{6,8,11}),
  ({0,3,5,12},{1,6,8}),
  ({0,3,6,7},{1,8,9})]
def block4 : List Row := [
  ({0,3,6,8},{1,9,11}),
  ({0,3,7,11},{1,5,9}),
  ({0,3,7,12},{1,5,8}),
  ({0,3,8,11},{1,6,9}),
  ({0,3,10,12},{5,6,8}),
  ({0,3,11,12},{1,5,6}),
  ({0,4,6,8},{2,9,11}),
  ({0,4,6,9},{2,7,11}),
  ({0,4,8,10},{2,6,11}),
  ({0,4,9,10},{2,5,11})]
def block5 : List Row := [
  ({0,4,9,12},{2,5,7}),
  ({0,4,10,12},{2,5,6}),
  ({0,4,11,12},{5,6,7}),
  ({0,5,6,9},{1,7,11}),
  ({0,5,6,12},{1,7,8}),
  ({0,5,8,9},{1,3,11}),
  ({0,5,8,10},{3,6,11}),
  ({0,5,8,11},{1,3,6}),
  ({0,5,9,11},{1,3,7}),
  ({0,5,11,12},{1,6,7})]
def block6 : List Row := [
  ({0,6,7,8},{1,2,9}),
  ({0,6,7,12},{1,2,8}),
  ({0,6,8,9},{1,2,11}),
  ({0,6,9,12},{1,2,7}),
  ({0,7,8,9},{1,2,3}),
  ({0,7,8,11},{1,3,9}),
  ({0,7,9,10},{2,3,5}),
  ({0,7,9,11},{1,3,5}),
  ({0,7,9,12},{1,2,5}),
  ({0,7,10,12},{2,5,8})]
def block7 : List Row := [
  ({0,8,9,10},{2,3,11}),
  ({0,9,11,12},{1,5,7}),
  ({1,2,3,6},{4,8,9}),
  ({1,2,3,7},{8,9,10}),
  ({1,2,3,8},{4,9,10}),
  ({1,2,3,12},{4,8,10}),
  ({1,2,5,7},{3,8,10}),
  ({1,2,5,9},{3,7,10}),
  ({1,2,5,12},{7,8,10}),
  ({1,2,6,11},{4,7,9})]
def block8 : List Row := [
  ({1,2,6,12},{4,7,8}),
  ({1,2,7,8},{3,9,10}),
  ({1,2,8,9},{3,4,10}),
  ({1,2,8,11},{3,4,9}),
  ({1,2,9,11},{3,4,7}),
  ({1,2,9,12},{4,7,10}),
  ({1,3,4,5},{6,10,12}),
  ({1,3,4,7},{9,10,12}),
  ({1,3,4,8},{6,9,10}),
  ({1,3,4,11},{6,9,12})]
def block9 : List Row := [
  ({1,3,5,7},{8,10,12}),
  ({1,3,5,10},{6,8,12}),
  ({1,3,5,12},{6,8,10}),
  ({1,3,6,7},{8,9,12}),
  ({1,3,6,10},{4,8,12}),
  ({1,3,6,11},{4,9,12}),
  ({1,3,8,11},{4,6,9}),
  ({1,3,8,12},{4,6,10}),
  ({1,3,10,11},{4,6,12}),
  ({1,3,10,12},{4,6,8})]
def block10 : List Row := [
  ({1,4,5,9},{7,10,12}),
  ({1,4,5,11},{6,7,12}),
  ({1,4,5,12},{6,7,10}),
  ({1,4,6,7},{2,9,12}),
  ({1,4,6,9},{2,7,12}),
  ({1,4,6,11},{7,9,12}),
  ({1,4,7,8},{2,9,10}),
  ({1,4,7,9},{2,10,12}),
  ({1,4,8,12},{2,6,10}),
  ({1,4,9,12},{2,7,10})]
def block11 : List Row := [
  ({1,5,7,9},{3,10,12}),
  ({1,5,7,10},{3,8,12}),
  ({1,5,9,11},{3,7,12}),
  ({1,5,10,11},{3,6,12}),
  ({1,6,7,10},{2,8,12}),
  ({1,6,9,10},{2,4,12}),
  ({1,6,9,11},{4,7,12}),
  ({1,6,9,12},{2,4,7}),
  ({1,6,10,12},{2,4,8}),
  ({1,7,8,9},{2,3,10})]
def block12 : List Row := [
  ({1,7,9,10},{2,3,12}),
  ({1,8,9,10},{2,3,4}),
  ({1,8,9,12},{2,4,10}),
  ({1,8,10,11},{3,4,6}),
  ({1,8,10,12},{2,4,6}),
  ({1,9,10,11},{3,4,12}),
  ({2,3,4,7},{5,9,10}),
  ({2,3,4,8},{9,10,11}),
  ({2,3,4,9},{5,10,11}),
  ({2,3,6,8},{4,9,11})]
def rows : List Row := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12

def good (r : Row) : Prop :=
  IsQuadrangle singerLines3 r.1 ∧ r.1 = Finset.univ \ r.2.biUnion singerLines3
instance (r : Row) : Decidable (good r) := by unfold good; infer_instance

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid0 : block0.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid1 : block1.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid2 : block2.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid3 : block3.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid4 : block4.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid5 : block5.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid6 : block6.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid7 : block7.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid8 : block8.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid9 : block9.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid10 : block10.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid11 : block11.all (fun r => decide (good r)) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem valid12 : block12.all (fun r => decide (good r)) = true := by decide +kernel

theorem rowsGood : rows.all (fun r => decide (good r)) = true := by
  simp only [rows,List.all_append,valid0,valid1,valid2,valid3,valid4,valid5,valid6,valid7,valid8,valid9,valid10,valid11,valid12,Bool.and_self]

def q (i : Fin 130) : Finset Pt := (rows.map Prod.fst).get i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem distinct : (rows.map Prod.fst).Nodup := by decide +kernel

theorem qInj : Function.Injective q := List.nodup_iff_injective_get.mp distinct

theorem getMap (xs : List Row) (i : Fin xs.length) :
    (xs.map Prod.fst).get ⟨i.val,by simpa using i.isLt⟩ = (xs.get i).1 := by
  change (xs.map Prod.fst)[i.val]'_ = (xs[i.val]'i.isLt).1
  rw [List.getElem_map]

theorem qFacts (i : Fin 130) : IsQuadrangle singerLines3 (q i) ∧
    ∀ p ∉ q i, ∃ l ∈ missLines singerLines3 (q i), p ∈ singerLines3 l := by
  let r : Row := rows.get i
  have hr : r ∈ rows := List.get_mem ..
  have hg : good r := of_decide_eq_true (List.all_eq_true.mp rowsGood r hr)
  have hq : q i = r.1 := getMap rows i
  rw [hq]
  refine ⟨hg.1,?_⟩
  intro p hp
  have hp' : p ∈ r.2.biUnion singerLines3 := by
    by_contra hn
    exact hp (hg.2 ▸ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩)
  obtain ⟨l,hl,hp⟩ := Finset.mem_biUnion.mp hp'
  refine ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mpr ?_⟩,hp⟩
  intro a ha hq'
  rw [hg.2] at hq'
  exact (Finset.mem_sdiff.mp hq').2 (Finset.mem_biUnion.mpr ⟨l,hl,ha⟩)

theorem qMem (i : Fin 130) : q i ∈ quadrangles singerLines3 :=
  Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(qFacts i).1.1⟩,
    (qFacts i).1.2⟩
end SaturatedQuadrangles
namespace QuadrangleAndCount

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.HeptadCover

def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def step (w : List Bool) (g : Gate) := w ++ [value g w]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def nAnd (gs : List Gate) := (gs.filter fun g => isAnd g.op).length

def selector : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
    let tail := selector gs (step w g)
    if isAnd g.op then w.getD (g.inputs.getD 0 0) false :: tail else tail

theorem nselector (gs : List Gate) (w : List Bool) : (selector gs w).length = nAnd gs := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : isAnd g.op <;> simp [selector, nAnd, h, ih, List.filter]

theorem selector_transport (gs : List Gate) (x u v : List Bool)
    (lens : x.length = u.length ∧ u.length = v.length)
    (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (same : selector gs u = selector gs v)
    (covered : ∀ i, x.getD i false = true → u.getD i false = true ∨ v.getD i false = true) :
    ∀ i, (run gs x).getD i false = true →
      (run gs u).getD i false = true ∨ (run gs v).getD i false = true := by
  induction gs generalizing x u v with
  | nil => exact covered
  | cons g gs ih =>
    obtain ⟨op,len⟩ := ok g (by simp)
    obtain ⟨a,b,pins⟩ : ∃ a b, g.inputs = [a,b] := by
      rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rst⟩⟩⟩ <;> simp_all
    have agree : selector gs (step u g) = selector gs (step v g) := by
      rcases op with h | h
      · simp only [selector,h,isAnd,ite_true,List.cons.injEq] at same
        exact same.2
      · simpa [selector,h,isAnd] using same
    have out : value g x = true → value g u = true ∨ value g v = true := by
      rcases op with hop | hop
      · have heads : u.getD a false = v.getD a false := by
          simp only [selector,hop,isAnd,ite_true,List.cons.injEq] at same
          simpa [pins] using same.1
        simp only [value,hop,pins,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,Bool.and_eq_true]
        rintro ⟨xa,xb⟩
        have pa := covered a xa
        have pb := covered b xb
        rw [heads] at pa
        rcases pa with va | va <;> rcases pb with ub | vb
        · exact .inl ⟨heads.trans va,ub⟩
        · exact .inr ⟨va,vb⟩
        · exact .inl ⟨heads.trans va,ub⟩
        · exact .inr ⟨va,vb⟩
      · simp only [value,hop,pins,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true]
        rintro (h | h)
        · exact (covered a h).imp Or.inl Or.inl
        · exact (covered b h).imp Or.inr Or.inr
    apply ih (step x g) (step u g) (step v g) (by simp [step,lens]) (fun r hr => ok r (by simp [hr])) agree
    intro i
    dsimp only [step]
    by_cases low : i < x.length
    · rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact covered i
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), lens.1, lens.2]
      cases i - v.length with
      | zero => exact out
      | succ j => simp

theorem and_count {m : ℕ} (C : Circuit) (ao : IsAO2 26 C)
    (pos : List Bool → Prop) (yes : ∀ x, pos x → C.eval x = true)
    (Q : Fin m → List Bool) (no : ∀ i, C.eval (Q i) = false)
    (sep : ∀ i j, i ≠ j → ∃ x, pos x ∧ x.length = (Q i).length ∧ (Q i).length = (Q j).length ∧
      ∀ k, x.getD k false = true → (Q i).getD k false = true ∨ (Q j).getD k false = true) :
    m ≤ 2 ^ (nAnd C.gates) := by
  let code (i : Fin m) (b : Fin (nAnd C.gates)) := (selector C.gates (Q i)).getD b.val false
  have inj : Function.Injective code := by
    intro i j eq
    by_contra neq
    have eqsel : selector C.gates (Q i) = selector C.gates (Q j) := by
      apply List.ext_getElem
      · simp [nselector]
      · intro k h1 h2
        have klt : k < nAnd C.gates := by simpa [nselector] using h1
        have bit := congrFun eq ⟨k,klt⟩
        simpa only [code, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] using bit
    obtain ⟨x, hx, lu, lv, cover⟩ := sep i j neq
    have forced := selector_transport C.gates x (Q i) (Q j) ⟨lu,lv⟩ (fun g hg => ⟨ao.1 g hg, ao.2.2 g hg⟩) eqsel cover C.output (yes x hx)
    change C.eval (Q i) = true ∨ C.eval (Q j) = true at forced
    simp [no i,no j] at forced
  have bound := Fintype.card_le_of_injective code inj
  simpa using bound

end QuadrangleAndCount

namespace QuadrangleAndCount
open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.TopForm

abbrev N (S : Finset (Fin 13)) := (List.ofFn fun u : Fin 13 => decide (u ∈ S)) ++
    (List.ofFn fun v : Fin 13 => decide (v ∈ missLines singerLines3 S))
abbrev T (p l : Fin 13) := (List.ofFn fun u : Fin 13 => decide (u = p)) ++
    (List.ofFn fun v : Fin 13 => decide (v = l))

theorem mixed (A B : Finset (Fin 13)) (p l : Fin 13) (hp : p ∈ A) (hl : l ∈ missLines singerLines3 B) :
    ∀ k, (T p l).getD k false = true → (N A).getD k false = true ∨ (N B).getD k false = true := by
  let cat (x z : Fin 13 → Bool) := List.ofFn x ++ List.ofFn z
  have low (x z : Fin 13 → Bool) (k : ℕ) (hk : k < 13) : (cat x z).getD k false = x ⟨k,hk⟩ := by
    dsimp only [cat]
    rw [List.getD_append _ _ _ _ (by simpa using hk)]
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
  have high (x z : Fin 13 → Bool) (k : ℕ) (hk : 13 ≤ k) (hk' : k < 26) :
      (cat x z).getD k false = z ⟨k-13,by omega⟩ := by
    dsimp only [cat]
    rw [List.getD_append_right _ _ _ _ (by simpa using hk), List.length_ofFn]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  intro k e
  change (cat _ _).getD k false = true at e
  by_cases hk : k < 13
  · left
    change (cat _ _).getD k false = true
    rw [low _ _ _ hk] at e ⊢
    have eq := of_decide_eq_true e
    exact decide_eq_true (eq ▸ hp)
  · by_cases bound : k < 26
    · right
      change (cat _ _).getD k false = true
      rw [high _ _ _ (by omega) bound] at e ⊢
      have eq := of_decide_eq_true e
      exact decide_eq_true (eq ▸ hl)
    · rw [List.getD_eq_default _ _ (by simp [cat]; omega)] at e
      contradiction

theorem eight (q : Fin 130 → Finset (Fin 13)) (inject : Function.Injective q)
    (family : ∀ i, q i ∈ quadrangles singerLines3)
    (sat : ∀ i p, p ∉ q i → ∃ l ∈ missLines singerLines3 (q i), p ∈ singerLines3 l)
    (C : Circuit) (ao : IsAO2 26 C)
    (pos : ∀ p l : Fin 13, p ∈ singerLines3 l → C.eval (T p l) = true)
    (neg : ∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false) : 8 ≤ nAnd C.gates := by
  let ok := fun x : List Bool => ∃ p l : Fin 13, p ∈ singerLines3 l ∧ x = T p l
  have bound := and_count C ao ok (by rintro _ ⟨p,l,inc,rfl⟩; exact pos p l inc)
    (fun i => N (q i)) (fun i => neg _ (family i)) (by
      intro i j h
      have card (t : Fin 130) : (q t).card = 4 :=
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (family t)).1).2
      have hi : ¬ q i ⊆ q j := fun sub => h (inject (Finset.eq_of_subset_of_card_le sub (by rw [card,card])))
      obtain ⟨p,pi,pj⟩ := Finset.not_subset.mp hi
      obtain ⟨l,ml,inc⟩ := sat j p pj
      exact ⟨T p l, ⟨p,l,inc,rfl⟩, by simp [T,N], by simp [N], mixed _ _ p l pi ml⟩)
  by_contra! few
  have pow := Nat.pow_le_pow_right (by decide : 0 < 2) (show nAnd C.gates ≤ 7 by omega)
  norm_num at pow
  omega
end QuadrangleAndCount

namespace QuadrangleAndCount
open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.TopForm

def isOr : GateOp → Bool
  | .or => true
  | _ => false

def nOr (gs : List Gate) := (gs.filter fun g => isOr g.op).length

theorem snoc_other (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases lt : i < w.length
  · exact List.getD_append _ _ _ _ lt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem choice (g : Gate) (w : List Bool) (op : g.op = .and ∨ g.op = .or) (len : g.inputs.length = 2)
    (off : value g w = false) :
    ∃ S : Finset ℕ, S.card ≤ 1 + (if isOr g.op then 1 else 0) ∧
      (∀ i ∈ S, w.getD i false = false) ∧
      ∀ x, value g x = true → ∃ i ∈ S, x.getD i false = true := by
  obtain ⟨a,b,pins⟩ : ∃ a b, g.inputs = [a,b] := by
    rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rst⟩⟩⟩ <;> simp_all
  rcases op with h | h
  · have zero : w.getD a false = false ∨ w.getD b false = false := by
      change g.op.eval (g.inputs.map _) = false at off
      rw [h,pins] at off
      cases ha : w.getD a false <;> cases hb : w.getD b false <;> simp_all [GateOp.eval]
    rcases zero with ha | hb
    · refine ⟨{a}, by simp [h,isOr], by simpa using ha, ?_⟩
      intro x hx
      exact ⟨a, by simp, (show x.getD a false = true ∧ x.getD b false = true by simpa [value,h,pins,GateOp.eval] using hx).1⟩
    · refine ⟨{b}, by simp [h,isOr], by simpa using hb, ?_⟩
      intro x hx
      exact ⟨b, by simp, (show x.getD a false = true ∧ x.getD b false = true by simpa [value,h,pins,GateOp.eval] using hx).2⟩
  · have zero : w.getD a false = false ∧ w.getD b false = false := by simpa [value,h,pins,GateOp.eval] using off
    refine ⟨{a,b}, ?_, by simpa using zero, ?_⟩
    · simp only [h,isOr,ite_true]
      exact Finset.card_insert_le _ _ |>.trans (by simp)
    · intro x hx
      have hbits : x.getD a false = true ∨ x.getD b false = true := by simpa [value,h,pins,GateOp.eval] using hx
      rcases hbits with h | h
      · exact ⟨a,by simp,h⟩
      · exact ⟨b,by simp,h⟩

theorem zero_cover (gs : List Gate) (w : List Bool) (out : ℕ)
    (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (off : (run gs w).getD out false = false) :
    ∃ S : Finset ℕ, S.card ≤ nOr gs + 1 ∧ (∀ i ∈ S, w.getD i false = false) ∧
      ∀ x : List Bool, x.length = w.length → (run gs x).getD out false = true →
         ∃ i ∈ S, x.getD i false = true := by
  induction gs generalizing w with
  | nil =>
    exact ⟨{out}, by simp [nOr], by simpa [run] using off, fun x _ hx => ⟨out,by simp,hx⟩⟩
  | cons g gs ih =>
    change (run gs (step w g)).getD out false = false at off
    obtain ⟨R,rsize,rzero,rhit⟩ := ih (step w g) (fun g' hg => ok g' (by simp [hg])) off
    have cnt : nOr (g :: gs) = nOr gs + (if isOr g.op then 1 else 0) := by
      cases h : isOr g.op <;> simp [nOr,List.filter,h]
    have prev (x : List Bool) (len : x.length = w.length) (i : ℕ) (hi : i ≠ w.length) :
        (step x g).getD i false = x.getD i false := snoc_other _ _ _ (by omega)
    have use (x : List Bool) (len : x.length = w.length) (xhit : (run (g::gs) x).getD out false = true) :
        ∃ i ∈ R, (step x g).getD i false = true := rhit _ (by simp [step,len]) xhit
    by_cases mem : w.length ∈ R
    · have stop : value g w = false := by simpa [step] using rzero _ mem
      obtain ⟨S,slim,s0,scover⟩ := choice g w (ok g (by simp)).1 (ok g (by simp)).2 stop
      refine ⟨R.erase w.length ∪ S, ?_,?_,?_⟩
      · have hcap := Finset.card_union_le (R.erase w.length) S
        rw [Finset.card_erase_of_mem mem] at hcap
        have rpos := Finset.card_pos.mpr ⟨_,mem⟩
        rw [cnt]
        omega
      · intro i hi
        rcases Finset.mem_union.mp hi with old | new
        · obtain ⟨ne,member⟩ := Finset.mem_erase.mp old
          rw [← prev w rfl i ne]
          exact rzero i member
        · exact s0 i new
      · intro x len xhit
        obtain ⟨i,hi,hbit⟩ := use x len xhit
        by_cases new : i = w.length
        · have gate : value g x = true := by
            rw [new, ←len] at hbit
            simpa [step] using hbit
          obtain ⟨a,ha,hval⟩ := scover x gate
          exact ⟨a,Finset.mem_union_right _ ha,hval⟩
        · exact ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨new,hi⟩), (prev x len i new) ▸ hbit⟩
    · refine ⟨R, by rw [cnt]; omega,?_,?_⟩
      · intro i hi
        rw [←prev w rfl i (fun eq => mem (eq ▸ hi))]
        exact rzero _ hi
      · intro x len xhit
        obtain ⟨i,hi,hbit⟩ := use x len xhit
        exact ⟨i,hi,(prev x len i (fun eq => mem (eq ▸ hi))) ▸ hbit⟩
end QuadrangleAndCount

namespace QuadrangleAndCount
open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.TopForm

def baseQuadrangle : Finset (Fin 13) := {0,1,2,5}

def excluded : Finset (Fin 26) := Finset.univ.filter fun i => (N baseQuadrangle).getD i.val false = false

theorem baseQuad : baseQuadrangle ∈ quadrangles singerLines3 := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by decide⟩,?_⟩
  decide

theorem nineteen : excluded.card = 19 := by decide

def pointIndex (i : Fin 26) : Fin 13 := ⟨(#[0,0,0,3,4,0,6,7,8,9,10,11,12,0,1,2,0,0,1,2,0,0,5,0,1,0] : Array Nat)[i.val]?.getD 0 % 13,Nat.mod_lt _ (by decide)⟩
def lineIndex (i : Fin 26) : Fin 13 := ⟨(#[0,0,0,3,3,0,3,7,7,8,7,8,3,0,1,2,0,4,5,6,0,0,9,10,11,12] : Array Nat)[i.val]?.getD 0 % 13,Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem critical : ∀ i : Fin 26, i ∈ excluded →
    pointIndex i ∈ singerLines3 (lineIndex i) ∧ ∀ k : Fin 26,
      (T (pointIndex i) (lineIndex i)).getD k.val false = true →
        k = i ∨ (N baseQuadrangle).getD k.val false = true := by decide

theorem eighteen (C : Circuit) (ao : IsAO2 26 C)
    (pos : ∀ p l : Fin 13, p ∈ singerLines3 l → C.eval (T p l) = true)
    (neg : ∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false) : 18 ≤ nOr C.gates := by
  obtain ⟨S,sz,zero,hit⟩ := zero_cover C.gates (N baseQuadrangle) C.output
    (fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩) (neg _ baseQuad)
  have subset : excluded.image Fin.val ⊆ S := by
    intro t ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨inc,only⟩ := critical i hi
    let x := T (pointIndex i) (lineIndex i)
    have on : (run C.gates x).getD C.output false = true := pos _ _ inc
    obtain ⟨k,hk,bit⟩ := hit x (by simp [x,T,N]) on
    have bound : k < 26 := by
      by_contra! h
      rw [List.getD_eq_default _ _ (by simp [x,T]; omega)] at bit
      contradiction
    rcases only ⟨k,bound⟩ bit with eq | active
    · exact congrArg Fin.val eq ▸ hk
    · exact Bool.noConfusion ((zero k hk).symm.trans active)
  have sz19 := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ Fin.val_injective, nineteen] at sz19
  omega

end QuadrangleAndCount

end PEqualNP.Outside.QuadrangleGateCounts

open PEqualNP.Outside.QuadrangleGateCounts

theorem PEqualNP.Outside.QuadrangleGateCounts :
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 26 C →
    (∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l → C.eval
      (List.ofFn (fun k : Fin 13 => decide (k = p)) ++ List.ofFn (fun k : Fin 13 => decide (k = l))) = true) →
    (∀ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
      C.eval (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q))) = false) →
    8 ≤ PEqualNP.ReadTwo.nAnd C ∧ 18 ≤ PEqualNP.ReadTwo.nOr C := by
  intro C h p n
  have andEq : PEqualNP.ReadTwo.nAnd C = QuadrangleAndCount.nAnd C.gates := by
    unfold PEqualNP.ReadTwo.nAnd QuadrangleAndCount.nAnd
    congr 1
    apply List.filter_congr
    intro g _
    cases g with
    | mk op ins => cases op <;> rfl
  have orEq : PEqualNP.ReadTwo.nOr C = QuadrangleAndCount.nOr C.gates := by
    unfold PEqualNP.ReadTwo.nOr QuadrangleAndCount.nOr
    congr 1
    apply List.filter_congr
    intro g _
    cases g with
    | mk op ins => cases op <;> rfl
  rw [andEq,orEq]
  exact ⟨QuadrangleAndCount.eight SaturatedQuadrangles.q SaturatedQuadrangles.qInj
      SaturatedQuadrangles.qMem (fun i => (SaturatedQuadrangles.qFacts i).2) C h p n,
    QuadrangleAndCount.eighteen C h p n⟩
