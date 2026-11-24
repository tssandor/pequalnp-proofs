import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.QuadrangleStarCover
open PEqualNP.HeptadCover

def edges : Fin 26 → Fin 26 → Prop := fun i j =>
  i.val < 13 ∧ 13 ≤ j.val ∧ (i.val + 13 - (j.val-13)) % 13 ∈ ({0,1,3,9} : Finset ℕ)

def graph : SimpleGraph (Fin 26) := SimpleGraph.fromRel edges

def inputs (Q : Finset (Fin 13)) :=
  List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
  List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))

def samples : List (Finset (Fin 13)) := [
  {0,1,2,5},
  {3,4,7,9},
  {6,8,10,12},
  {0,3,8,11},
  {0,4,6,9},
  {1,9,10,11},
  {2,4,5,8},
  {2,3,10,12},
  {5,6,7,11},
  {1,4,5,12},
  {0,1,6,7},
  {0,9,11,12},
  {0,3,5,10},
  {1,2,7,8},
  {2,4,6,11},
  {0,5,8,9},
  {4,7,10,12},
  {1,3,6,7},
  {0,1,8,10},
  {0,2,3,4},
  {1,2,9,12},
  {3,5,7,12},
  {1,3,8,11},
  {1,4,5,11},
  {1,4,7,9},
  {2,5,7,10},
  {3,6,8,9},
  {4,10,11,12},
  {0,2,7,10},
  {0,6,7,8},
  {3,4,5,9}]

theorem valid : ∀ Q ∈ samples, IsQuadrangle singerLines3 Q := by
  intro Q h
  simp only [samples, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem mem_quadrangle {Q : Finset (Fin 13)} (h : IsQuadrangle singerLines3 Q) :
    Q ∈ quadrangles singerLines3 := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h.1⟩, h.2⟩

def notEdge (u v : Fin 26) : Prop := ¬ (u ≠ v ∧ (edges u v ∨ edges v u))
instance (u v : Fin 26) : Decidable (notEdge u v) := by unfold notEdge edges; infer_instance
def covered (u v : Fin 26) : Prop :=
  ∃ Q ∈ samples, (inputs Q).getD u.val false = true ∧ (inputs Q).getD v.val false = true
instance (u v : Fin 26) : Decidable (covered u v) := by unfold covered; infer_instance

theorem row0 : ∀ v : Fin 26, notEdge 0 v → covered 0 v := by decide +kernel
theorem row1 : ∀ v : Fin 26, notEdge 1 v → covered 1 v := by decide +kernel
theorem row2 : ∀ v : Fin 26, notEdge 2 v → covered 2 v := by decide +kernel
theorem row3 : ∀ v : Fin 26, notEdge 3 v → covered 3 v := by decide +kernel
theorem row4 : ∀ v : Fin 26, notEdge 4 v → covered 4 v := by decide +kernel
theorem row5 : ∀ v : Fin 26, notEdge 5 v → covered 5 v := by decide +kernel
theorem row6 : ∀ v : Fin 26, notEdge 6 v → covered 6 v := by decide +kernel
theorem row7 : ∀ v : Fin 26, notEdge 7 v → covered 7 v := by decide +kernel
theorem row8 : ∀ v : Fin 26, notEdge 8 v → covered 8 v := by decide +kernel
theorem row9 : ∀ v : Fin 26, notEdge 9 v → covered 9 v := by decide +kernel
theorem row10 : ∀ v : Fin 26, notEdge 10 v → covered 10 v := by decide +kernel
theorem row11 : ∀ v : Fin 26, notEdge 11 v → covered 11 v := by decide +kernel
theorem row12 : ∀ v : Fin 26, notEdge 12 v → covered 12 v := by decide +kernel
theorem row13 : ∀ v : Fin 26, notEdge 13 v → covered 13 v := by decide +kernel
theorem row14 : ∀ v : Fin 26, notEdge 14 v → covered 14 v := by decide +kernel
theorem row15 : ∀ v : Fin 26, notEdge 15 v → covered 15 v := by decide +kernel
theorem row16 : ∀ v : Fin 26, notEdge 16 v → covered 16 v := by decide +kernel
theorem row17 : ∀ v : Fin 26, notEdge 17 v → covered 17 v := by decide +kernel
theorem row18 : ∀ v : Fin 26, notEdge 18 v → covered 18 v := by decide +kernel
theorem row19 : ∀ v : Fin 26, notEdge 19 v → covered 19 v := by decide +kernel
theorem row20 : ∀ v : Fin 26, notEdge 20 v → covered 20 v := by decide +kernel
theorem row21 : ∀ v : Fin 26, notEdge 21 v → covered 21 v := by decide +kernel
theorem row22 : ∀ v : Fin 26, notEdge 22 v → covered 22 v := by decide +kernel
theorem row23 : ∀ v : Fin 26, notEdge 23 v → covered 23 v := by decide +kernel
theorem row24 : ∀ v : Fin 26, notEdge 24 v → covered 24 v := by decide +kernel
theorem row25 : ∀ v : Fin 26, notEdge 25 v → covered 25 v := by decide +kernel

theorem nonedge (u v : Fin 26) (h : ¬ graph.Adj u v) :
    ∃ Q ∈ quadrangles singerLines3, (inputs Q).getD u.val false = true ∧
      (inputs Q).getD v.val false = true := by
  change notEdge u v at h
  have hm : covered u v := by
    fin_cases u
    · exact row0 v h
    · exact row1 v h
    · exact row2 v h
    · exact row3 v h
    · exact row4 v h
    · exact row5 v h
    · exact row6 v h
    · exact row7 v h
    · exact row8 v h
    · exact row9 v h
    · exact row10 v h
    · exact row11 v h
    · exact row12 v h
    · exact row13 v h
    · exact row14 v h
    · exact row15 v h
    · exact row16 v h
    · exact row17 v h
    · exact row18 v h
    · exact row19 v h
    · exact row20 v h
    · exact row21 v h
    · exact row22 v h
    · exact row23 v h
    · exact row24 v h
    · exact row25 v h
  obtain ⟨Q,hmem,hq⟩ := hm
  exact ⟨Q,mem_quadrangle (valid Q hmem),hq⟩
end PEqualNP.Outside.QuadrangleStarCover
namespace PEqualNP.Outside.QuadrangleStarCover
open PEqualNP.HeptadCover

instance decEdges : DecidableRel edges := fun i j => by unfold edges; infer_instance
instance decAdj : DecidableRel graph.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (edges i j ∨ edges j i)))

def lit (S : Finset (Fin 26)) (Q : Finset (Fin 13)) : Prop :=
  ∃ i ∈ S, (inputs Q).getD i.val false = true

theorem crossAdj (A B : Finset (Fin 26))
    (clean : ∀ Q ∈ quadrangles singerLines3, ¬(lit A Q ∧ lit B Q)) :
    ∀ a ∈ A, ∀ b ∈ B, graph.Adj a b := by
  intro a ha b hb
  by_contra n
  obtain ⟨Q,hQ,hqa,hqb⟩ := nonedge a b n
  exact clean Q hQ ⟨⟨a,ha,hqa⟩, ⟨b,hb,hqb⟩⟩

def common (a b : Fin 26) : Finset (Fin 26) :=
  Finset.univ.filter (fun u => graph.Adj a u ∧ graph.Adj b u)

set_option maxHeartbeats 2000000 in
theorem commonSmall : ∀ a b : Fin 26, a ≠ b → (common a b).card ≤ 1 := by decide +kernel

theorem star (A B : Finset (Fin 26))
    (clean : ∀ Q ∈ quadrangles singerLines3, ¬(lit A Q ∧ lit B Q)) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases ha : A.card ≤ 1
  · exact Or.inl ha
  · obtain ⟨a,aa,b,bb,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have e := crossAdj A B clean
    have hs : B ⊆ common a b := fun c hc =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,e a aa c hc,e b bb c hc⟩
    exact Or.inr ((Finset.card_le_card hs).trans (commonSmall a b ne))

def incidences : Finset (Fin 26 × Fin 26) := Finset.univ.filter (fun t => edges t.1 t.2)

def touches (s : Finset (Fin 26)) (e : Fin 26 × Fin 26) : Prop := e.1 ∈ s ∨ e.2 ∈ s
instance (s : Finset (Fin 26)) (e : Fin 26 × Fin 26) : Decidable (touches s e) :=
  inferInstanceAs (Decidable (e.1 ∈ s ∨ e.2 ∈ s))

def hits (A B : Finset (Fin 26)) :=
  incidences.filter (fun e => touches A e ∧ touches B e)
def incidentAt (v : Fin 26) := incidences.filter (fun e => e.1 = v ∨ e.2 = v)

theorem planeSize : incidences.card = 52 := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem degreeFour : ∀ v : Fin 26, (incidentAt v).card = 4 := by decide +kernel

theorem pureBound (A B : Finset (Fin 26))
    (clean : ∀ Q ∈ quadrangles singerLines3, ¬(lit A Q ∧ lit B Q)) :
    ∃ v : Fin 26, hits A B ⊆ incidentAt v ∧ (hits A B).card ≤ 4 := by
  have anchor (S : Finset (Fin 26)) (hs : S.card ≤ 1)
      (ht : ∀ e ∈ hits A B, touches S e) : ∃ v, hits A B ⊆ incidentAt v := by
    obtain ⟨v,hv⟩ := Finset.card_le_one_iff_subset_singleton.mp hs
    refine ⟨v,?_⟩
    intro e he
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,?_⟩
    rcases ht e he with h | h
    · exact Or.inl (Finset.mem_singleton.mp (hv h))
    · exact Or.inr (Finset.mem_singleton.mp (hv h))
  have h : ∃ v, hits A B ⊆ incidentAt v := by
    rcases star A B clean with ha | hb
    · exact anchor A ha (fun e he => (Finset.mem_filter.mp he).2.1)
    · exact anchor B hb (fun e he => (Finset.mem_filter.mp he).2.2)
  obtain ⟨v,hv⟩ := h
  exact ⟨v,hv,(Finset.card_le_card hv).trans (degreeFour v).le⟩
end PEqualNP.Outside.QuadrangleStarCover

namespace PEqualNP.Outside.QuadrangleStarCover
open PEqualNP.HeptadCover

theorem needThirteen {ι : Type} [DecidableEq ι] (S : Finset ι)
    (A B : ι → Finset (Fin 26))
    (clean : ∀ t ∈ S, ∀ Q ∈ quadrangles singerLines3, ¬(lit (A t) Q ∧ lit (B t) Q))
    (cover : incidences ⊆ S.biUnion (fun t => hits (A t) (B t))) : 13 ≤ S.card := by
  have width : ∀ t ∈ S, (hits (A t) (B t)).card ≤ 4 := by
    intro t ht
    exact (pureBound (A t) (B t) (clean t ht)).choose_spec.2
  have lower : 52 ≤ ∑ t ∈ S, (hits (A t) (B t)).card := by
    rw [← planeSize]
    exact (Finset.card_le_card cover).trans Finset.card_biUnion_le
  have upper : (∑ t ∈ S, (hits (A t) (B t)).card) ≤ S.card * 4 := by
    calc _ ≤ ∑ _t ∈ S, 4 := Finset.sum_le_sum width
         _ = _ := by simp
  omega
end PEqualNP.Outside.QuadrangleStarCover

namespace PEqualNP.Outside.QuadrangleStarCover
open PEqualNP.HeptadCover

def pairInput (e : Fin 26 × Fin 26) : List Bool :=
  List.ofFn (fun i : Fin 26 => decide (i = e.1 ∨ i = e.2))

def rawOr (s : Finset (Fin 26)) (x : List Bool) : Bool :=
  decide (∃ i ∈ s, x.getD i.val false = true)

def accepted (f : List Bool → Bool) : Finset (Fin 26 × Fin 26) :=
  incidences.filter (fun e => f (pairInput e) = true)

def pure (f : List Bool → Bool) : Prop :=
  ∃ A B : Finset (Fin 26), ∀ x : List Bool, x.length = 26 →
    f x = (rawOr A x && rawOr B x)

theorem pairRead (e : Fin 26 × Fin 26) (i : Fin 26) :
    (pairInput e).getD i.val false = decide (i = e.1 ∨ i = e.2) := by
  unfold pairInput
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt, ↓reduceDIte,
    Option.getD_some]

theorem hitsPair (s : Finset (Fin 26)) (e : Fin 26 × Fin 26) :
    rawOr s (pairInput e) = true ↔ touches s e := by
  simp only [rawOr, pairRead, decide_eq_true_eq,touches]
  constructor
  · rintro ⟨v,hv,rfl|rfl⟩
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (ha|hb)
    · exact ⟨_,ha,Or.inl rfl⟩
    · exact ⟨_,hb,Or.inr rfl⟩

theorem negativeBound (f : List Bool → Bool)
    (clean : ∀ Q ∈ quadrangles singerLines3, f (inputs Q) = false)
    (simple : pure f) : (accepted f).card ≤ 4 := by
  obtain ⟨A,B,eval⟩ := simple
  have safe : ∀ Q ∈ quadrangles singerLines3, ¬ (lit A Q ∧ lit B Q) := by
    rintro Q hQ ⟨ha,hb⟩
    have he := eval (inputs Q) (by simp [inputs])
    have one : rawOr A (inputs Q) = true := decide_eq_true ha
    have two : rawOr B (inputs Q) = true := decide_eq_true hb
    rw [clean Q hQ,one,two] at he
    contradiction
  have sub : accepted f ⊆ hits A B := by
    intro e he
    obtain ⟨hp,hf⟩ := Finset.mem_filter.mp he
    rw [eval _ (by simp [pairInput])] at hf
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp hf
    exact Finset.mem_filter.mpr ⟨hp,(hitsPair _ _).mp a,(hitsPair _ _).mp b⟩
  exact (Finset.card_le_card sub).trans (pureBound A B safe).choose_spec.2

theorem heavyGate {ι : Type} [DecidableEq ι] (J : Finset ι) (f : ι → List Bool → Bool)
    (clean : ∀ j ∈ J, ∀ Q ∈ quadrangles singerLines3, f j (inputs Q) = false)
    (cover : ∀ e ∈ incidences, ∃ j ∈ J, f j (pairInput e) = true) :
    13 ≤ J.card ∨ ∃ j ∈ J, 5 ≤ (accepted (f j)).card ∧ ¬pure (f j) := by
  classical
  by_cases light : ∀ j ∈ J, (accepted (f j)).card ≤ 4
  · left
    have allPairs : incidences ⊆ J.biUnion (fun j => accepted (f j)) := by
      intro e he
      obtain ⟨j,hj,hit⟩ := cover e he
      exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨he,hit⟩⟩
    have sumLower : 52 ≤ ∑ j ∈ J, (accepted (f j)).card := by
      rw [← planeSize]
      exact (Finset.card_le_card allPairs).trans Finset.card_biUnion_le
    have sumUpper : (∑ j ∈ J, (accepted (f j)).card) ≤ J.card * 4 := by
      calc _ ≤ ∑ _j ∈ J, 4 := Finset.sum_le_sum light
           _ = _ := by simp
    omega
  · right
    push Not at light
    obtain ⟨j,hj,h⟩ := light
    exact ⟨j,hj,by omega, fun hp => (not_lt_of_ge (negativeBound _ (clean j hj) hp)) h⟩

end PEqualNP.Outside.QuadrangleStarCover

namespace PEqualNP.Outside.QuadrangleStarCover
open PEqualNP.HeptadCover PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

theorem castPair : ∀ p l : Fin 13,
    pairInput (Fin.castAdd 13 p, Fin.natAdd 13 l) = pointLineInput 13 13 p l := by decide +kernel

theorem circuitHeavy (C : Circuit) (J : Finset ℕ)
    (clean : ∀ j ∈ J, ∀ Q ∈ quadrangles singerLines3, wireVal C (inputs Q) (26+j) = false)
    (cover : ∀ p l : Fin 13, p ∈ singerLines3 l →
      ∃ j ∈ J, wireVal C (pointLineInput 13 13 p l) (26+j) = true) :
    13 ≤ J.card ∨ ∃ j ∈ J, 5 ≤ (accepted (fun x => wireVal C x (26+j))).card ∧
      ¬pure (fun x => wireVal C x (26+j)) := by
  apply heavyGate J (fun j x => wireVal C x (26+j)) clean
  intro e he
  have orient : edges e.1 e.2 := (Finset.mem_filter.mp he).2
  obtain ⟨hp,hl,hd⟩ := orient
  let p : Fin 13 := ⟨e.1.val,hp⟩
  let l : Fin 13 := ⟨e.2.val-13,by have := e.2.isLt; omega⟩
  have inc : p ∈ singerLines3 l := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩
  have eq : e = (Fin.castAdd 13 p, Fin.natAdd 13 l) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change e.2.val = 13+(e.2.val-13)
      omega
  rw [eq,castPair]
  exact cover p l inc
end PEqualNP.Outside.QuadrangleStarCover
