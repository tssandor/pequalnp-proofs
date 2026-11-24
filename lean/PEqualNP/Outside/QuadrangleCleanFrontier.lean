import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.QuadrangleCleanFrontier_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.HeptadCover

abbrev qInput (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
    List.ofFn fun i : Fin 13 => decide (i ∈ missLines singerLines3 Q)

abbrev qFamily := quadrangles singerLines3

abbrev wire (C : Circuit) (w : ℕ) (x : List Bool) := (C.wires x).getD w false

abbrev CleanWire (C : Circuit) (w : ℕ) : Prop := ∀ Q ∈ qFamily, wire C w (qInput Q) = false

private def seeds : Fin 5 → Finset (Fin 13) :=
  ![{0,1,2,5},{3,4,7,9},{6,8,10,12},{0,3,8,11},{0,2,3,4}]

private theorem seedMember (i : Fin 5) : seeds i ∈ qFamily := by
  simp only [quadrangles,Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and]
  revert i
  decide

private theorem seedsCover : ∀ i : Fin 26, ∃ k : Fin 5, (qInput (seeds k)).getD i.val false = true := by decide

theorem rawDirty (C : Circuit) (w : ℕ) (hw : w < 26) : ¬ CleanWire C w := by
  intro h
  obtain ⟨k,hk⟩ := seedsCover ⟨w,hw⟩
  have hf := h (seeds k) (seedMember k)
  rw [wire,wires_eq_foldl,foldl_step_getD_lt _ _ _ (by simpa [qInput] using hw)] at hf
  exact Bool.false_ne_true (hf.symm.trans hk)

theorem gateData (C : Circuit) (ao : IsAO2 26 C) (j : ℕ) (hj : j < C.size) :
    (gateAt C j ∈ C.gates) ∧ ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs.length = 2 ∧
    ∀ x : List Bool, x.length = 26 → wire C (26+j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wire C i x) := by
  have he : C.gates[j]? = some (gateAt C j) := by
    rw [gateAt,List.getD_eq_getElem _ _ hj,List.getElem?_eq_getElem hj]
  have hg := List.mem_of_getElem? he
  refine ⟨hg,ao.1 _ hg,ao.2.2 _ hg,?_⟩
  intro x len
  have hh := foldl_step_gate C.gates x j _ he
  rw [len] at hh
  change (C.gates.foldl step x).getD (26+j) false = _
  rw [hh]
  apply congrArg (gateAt C j).op.eval
  apply List.map_congr_left
  intro i hi
  simp only [ao.2.1 j hj i hi,↓reduceIte]
  rfl

theorem clean_or_inputs (C : Circuit) (ao : IsAO2 26 C) (j : ℕ) (hj : j < C.size)
    (op : (gateAt C j).op = GateOp.or) (clean : CleanWire C (26+j)) :
    ∀ i ∈ (gateAt C j).inputs, CleanWire C i := by
  intro i hi Q hQ
  have val := (gateData C ao j hj).2.2.2 (qInput Q) (by simp [qInput])
  rw [clean Q hQ,op] at val
  by_contra h
  have yes : wire C i (qInput Q) = true := by simpa using h
  have any : GateOp.or.eval ((gateAt C j).inputs.map fun w => wire C w (qInput Q)) = true := by
    change (List.map _ _).any id = true
    apply List.any_eq_true.mpr
    exact ⟨_,List.mem_map_of_mem hi,yes⟩
  exact Bool.false_ne_true (val.trans any)

theorem and_operands_split (C : Circuit) (ao : IsAO2 26 C) (j : ℕ) (hj : j < C.size)
    (op : (gateAt C j).op = GateOp.and) (a b : ℕ) (args : (gateAt C j).inputs = [a,b])
    (essential : ∀ w ∈ (gateAt C j).inputs, ∃ Q ∈ qFamily, wire C (26+j) (qInput Q) ≠ wire C w (qInput Q)) :
    (∃ Q ∈ qFamily, wire C a (qInput Q) = true ∧ wire C b (qInput Q) = false) ∧
    (∃ Q ∈ qFamily, wire C a (qInput Q) = false ∧ wire C b (qInput Q) = true) := by
  have gate (Q : Finset (Fin 13)) :
      wire C (26+j) (qInput Q) = (wire C a (qInput Q) && wire C b (qInput Q)) := by
    rw [(gateData C ao j hj).2.2.2 _ (by simp [qInput]),op,args]
    simp [GateOp.eval]
  obtain ⟨A,hA,ha⟩ := essential a (by simp [args])
  obtain ⟨B,hB,hb⟩ := essential b (by simp [args])
  rw [gate] at ha hb
  exact ⟨⟨A,hA,by cases h1 : wire C a (qInput A) <;> cases h2 : wire C b (qInput A) <;> simp_all⟩,
    ⟨B,hB,by cases h1 : wire C a (qInput B) <;> cases h2 : wire C b (qInput B) <;> simp_all⟩⟩

theorem cleanAndCover (C : Circuit) (ao : IsAO2 26 C) (x : List Bool) (len : x.length=26) :
    ∀ w : ℕ, CleanWire C w → wire C w x = true →
      ∃ j < C.size, (gateAt C j).op = GateOp.and ∧ CleanWire C (26+j) ∧ wire C (26+j) x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro clean yes
    by_cases raw : w < 26
    · exact (rawDirty C w raw clean).elim
    by_cases large : 26+C.size ≤ w
    · have no : wire C w x = false := foldl_step_getD_ge C.gates x w (by simpa [Circuit.size,len] using large)
      exact Bool.false_ne_true (no.symm.trans yes) |>.elim
    let j := w-26
    have hj : j < C.size := by dsimp [j]; omega
    have eq : w = 26+j := by dsimp [j]; omega
    obtain ⟨_,a|o,_,hv⟩ := gateData C ao j hj
    · exact ⟨j,hj,a,eq ▸ clean,eq ▸ yes⟩
    · have cs := clean_or_inputs C ao j hj o (eq ▸ clean)
      have hv' := hv x len
      rw [←eq,yes,o] at hv'
      have someval : ((gateAt C j).inputs.map fun i => wire C i x).any id = true := hv'.symm
      obtain ⟨v,mem,t⟩ := List.any_eq_true.mp someval
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
      exact ih i (eq ▸ ao.2.1 j hj i hi) (cs i hi) t


abbrev terminal (C : Circuit) (w : ℕ) := ∃ j < C.size, w = 26+j ∧ (gateAt C j).op = GateOp.and

noncomputable def cleanOrs (C : Circuit) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).filter fun j => (gateAt C j).op = GateOp.or ∧ CleanWire C (26+j)

private theorem or_count_le (C : Circuit) (k : ℕ) : (cleanOrs C k).card ≤ (cleanOrs C (k+1)).card := by
  classical
  apply Finset.card_le_card
  intro j h
  simp only [cleanOrs,Finset.mem_filter,Finset.mem_range] at h ⊢
  exact ⟨by omega,h.2⟩

private theorem or_count_more (C : Circuit) (k : ℕ) (hop : (gateAt C k).op = GateOp.or)
    (clean : CleanWire C (26+k)) : (cleanOrs C (k+1)).card = (cleanOrs C k).card + 1 := by
  classical
  simp only [cleanOrs,Finset.range_add_one,Finset.filter_insert]
  rw [ite_eq_left ⟨hop,clean⟩, Finset.card_insert_of_notMem]
  simp

private theorem frontier_aux (C : Circuit) (ao : IsAO2 26 C) (k : ℕ) (bound : k ≤ C.size) (A : Finset ℕ)
    (clean : ∀ w ∈ A, CleanWire C w) (earlier : ∀ w ∈ A, w < 26+k ∨ terminal C w) :
    ∃ B : Finset ℕ, (∀ w ∈ B, terminal C w ∧ CleanWire C w) ∧
      B.card ≤ A.card + (cleanOrs C k).card ∧ ∀ x : List Bool, x.length=26 →
        ((∃ w ∈ A, wire C w x = true) ↔ (∃ w ∈ B, wire C w x = true)) := by
  classical
  induction k generalizing A with
  | zero =>
    refine ⟨A,?_,by omega,fun _ _ => Iff.rfl⟩
    intro w hw
    have term := (earlier w hw).resolve_left (fun low => rawDirty C w (by omega) (clean w hw))
    exact ⟨term,clean w hw⟩
  | succ k ih =>
    have kb : k < C.size := by omega
    let v := 26+k
    have skip (s : v ∉ A ∨ terminal C v) : ∀ w ∈ A, w < 26+k ∨ terminal C w := by
      intro w hw
      rcases earlier w hw with e|t
      · by_cases eq : w = v
        · subst w
          exact Or.inr (s.resolve_left (fun h => h hw))
        · exact Or.inl (by dsimp [v] at eq; omega)
      · exact Or.inr t
    by_cases casesDone : v ∉ A ∨ terminal C v
    · obtain ⟨B,hB,hc,he⟩ := ih (by omega) A clean (skip casesDone)
      exact ⟨B,hB,hc.trans (Nat.add_le_add_left (or_count_le C k) _),he⟩
    push Not at casesDone
    obtain ⟨inA,nterm⟩ := casesDone
    obtain ⟨_,op,arity,hgate⟩ := gateData C ao k kb
    have hop := op.resolve_left (nterm k kb rfl)
    let ins := (gateAt C k).inputs
    let A' := A.erase v ∪ ins.toFinset
    have members (w : ℕ) : w ∈ A' ↔ ((w ≠ v ∧ w ∈ A) ∨ w ∈ ins) := by simp [A']
    have vclean := clean v inA
    have cin := clean_or_inputs C ao k kb hop vclean
    have ca : ∀ w ∈ A', CleanWire C w := by
      intro w hw
      rcases (members w).mp hw with ⟨_,ha⟩|hi
      · exact clean w ha
      · exact cin w hi
    have ea : ∀ w ∈ A', w < 26+k ∨ terminal C w := by
      intro w hw
      rcases (members w).mp hw with ⟨ne,ha⟩|hi
      · rcases earlier w ha with e|t
        · exact Or.inl (by dsimp [v] at ne; omega)
        · exact Or.inr t
      · exact Or.inl (ao.2.1 k kb w hi)
    obtain ⟨B,cb,bc,be⟩ := ih (by omega) A' ca ea
    have card : A'.card ≤ A.card+1 := by
      have hu := Finset.card_union_le (A.erase v) ins.toFinset
      have hl := List.toFinset_card_le ins
      have her := Finset.card_erase_of_mem inA
      change ins.length = 2 at arity
      change (A.erase v ∪ ins.toFinset).card ≤ _
      have hpos := Finset.card_pos.mpr ⟨v,inA⟩
      omega
    refine ⟨B,cb,?_,?_⟩
    · have more := or_count_more C k hop vclean
      omega
    intro x hx
    apply Iff.trans _ (be x hx)
    have vor : wire C v x = true ↔ ∃ i ∈ ins, wire C i x = true := by
      rw [show wire C v x = _ from hgate x hx,hop]
      simp [GateOp.eval,ins]
    constructor
    · rintro ⟨w,hw,on⟩
      by_cases e : w=v
      · subst w
        obtain ⟨i,hi,yes⟩ := vor.mp on
        exact ⟨i,(members i).mpr (.inr hi),yes⟩
      · exact ⟨w,(members w).mpr (.inl ⟨e,hw⟩),on⟩
    · rintro ⟨w,hw,yes⟩
      rcases (members w).mp hw with ⟨_,ha⟩|hi
      · exact ⟨w,ha,yes⟩
      · exact ⟨v,inA,vor.mpr ⟨w,hi,yes⟩⟩

theorem outputFrontier (C : Circuit) (ao : IsAO2 26 C)
    (clean : CleanWire C C.output) (nonzero : ∃ x : List Bool, x.length=26 ∧ C.eval x=true) :
    ∃ B : Finset ℕ, (∀ w ∈ B, terminal C w ∧ CleanWire C w) ∧
      B.card ≤ (cleanOrs C C.size).card + 1 ∧ ∀ x : List Bool, x.length=26 →
      (C.eval x=true ↔ ∃ w ∈ B, wire C w x = true) := by
  obtain ⟨y,hy,on⟩ := nonzero
  have valid : C.output < 26+C.size := by
    by_contra! high
    have off : C.eval y = false := foldl_step_getD_ge C.gates y C.output (by simpa [hy,Circuit.size] using high)
    rw [off] at on
    contradiction
  obtain ⟨B,hB,hc,he⟩ := frontier_aux C ao C.size (by rfl) {C.output}
    (by simpa using clean) (by simp [valid])
  refine ⟨B,hB,by simpa [Nat.add_comm] using hc,?_⟩
  intro x hx
  simpa only [Finset.mem_singleton,exists_eq_left,Circuit.eval,wire] using he x hx


theorem outputIndexFrontier (C : Circuit) (ao : IsAO2 26 C)
    (clean : CleanWire C C.output) (nonzero : ∃ x : List Bool, x.length=26 ∧ C.eval x=true) :
    ∃ J : Finset ℕ, (∀ j ∈ J, j < C.size ∧ (gateAt C j).op = GateOp.and ∧ CleanWire C (26+j)) ∧
      J.card ≤ (cleanOrs C C.size).card + 1 ∧ ∀ x : List Bool, x.length=26 →
      (C.eval x=true ↔ ∃ j ∈ J, wire C (26+j) x = true) := by
  classical
  obtain ⟨B,data,sz,eff⟩ := outputFrontier C ao clean nonzero
  refine ⟨B.image (fun w => w-26),?_,Finset.card_image_le.trans sz,?_⟩
  · intro j hj
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨⟨k,hk,rfl,hop⟩,c⟩ := data w hw
    simpa using And.intro hk (And.intro hop c)
  · intro x hx
    rw [eff x hx]
    constructor
    · rintro ⟨w,hw,on⟩
      obtain ⟨⟨k,_,rfl,_⟩,_⟩ := data w hw
      exact ⟨k,Finset.mem_image.mpr ⟨_,hw,by simp⟩,on⟩
    · rintro ⟨j,hj,on⟩
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨⟨k,_,rfl,_⟩,_⟩ := data w hw
      exact ⟨_,hw,by simpa using on⟩


theorem cleanBudget (C : Circuit) (J : Finset ℕ)
    (data : ∀ j ∈ J, j < C.size ∧ (gateAt C j).op = GateOp.and ∧ CleanWire C (26+j))
    (cost : J.card ≤ (cleanOrs C C.size).card + 1) :
    2 * J.card ≤ C.size + 1 := by
  classical
  have disj : Disjoint J (cleanOrs C C.size) := by
    apply Finset.disjoint_left.mpr
    intro j hj ho
    have op := (Finset.mem_filter.mp ho).2.1
    rw [(data j hj).2.1] at op
    contradiction
  have sub : J ∪ cleanOrs C C.size ⊆ Finset.range C.size := by
    intro j hj
    rcases Finset.mem_union.mp hj with h|h
    · exact Finset.mem_range.mpr (data j h).1
    · exact (Finset.mem_filter.mp h).1
  have bound := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint disj,Finset.card_range] at bound
  omega

end PEqualNP.Outside.QuadrangleCleanFrontier_aux

namespace PEqualNP.Outside.QuadrangleCleanFrontier_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.HeptadCover

abbrev pairRow (p l : Fin 13) : List Bool :=
  (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)

def profile (C : Circuit) (w : ℕ) := qFamily.filter fun Q => wire C w (qInput Q) = true

theorem clean_operands (C : Circuit) (ao : IsAO2 26 C) (j : ℕ) (hj : j < C.size)
    (op : (gateAt C j).op = GateOp.and) (a b : ℕ) (args : (gateAt C j).inputs = [a,b])
    (clean : CleanWire C (26+j))
    (essential : ∀ w ∈ (gateAt C j).inputs, ∃ Q ∈ qFamily, wire C (26+j) (qInput Q) ≠ wire C w (qInput Q)) :
    (profile C a).Nonempty ∧ (profile C b).Nonempty ∧ Disjoint (profile C a) (profile C b) := by
  obtain ⟨⟨A,hA,ha,_⟩,⟨B,hB,_,hb⟩⟩ := and_operands_split C ao j hj op a b args essential
  refine ⟨⟨A,Finset.mem_filter.mpr ⟨hA,ha⟩⟩,⟨B,Finset.mem_filter.mpr ⟨hB,hb⟩⟩,?_⟩
  apply Finset.disjoint_left.mpr
  intro Q thisA thisB
  obtain ⟨hQ,hitA⟩ := Finset.mem_filter.mp thisA
  have hitB := (Finset.mem_filter.mp thisB).2
  have v := (gateData C ao j hj).2.2.2 (qInput Q) (by simp [qInput])
  rw [clean Q hQ,op,args] at v
  simp only [List.map_cons,List.map_nil,hitA,hitB] at v
  exact Bool.noConfusion v

theorem bothActive (C : Circuit) (ao : IsAO2 26 C) (j : ℕ) (hj : j < C.size)
    (op : (gateAt C j).op = GateOp.and) (x : List Bool) (len : x.length=26) :
    wire C (26+j) x = true ↔ ∀ w ∈ (gateAt C j).inputs.toFinset, wire C w x = true := by
  rw [(gateData C ao j hj).2.2.2 x len,op]
  simp [GateOp.eval]

abbrev coversPairs (C : Circuit) (K : Finset ℕ) :=
  ∀ p l : Fin 13, p ∈ singerLines3 l → ∃ j ∈ K, wire C (26+j) (pairRow p l) = true

private theorem minimalCover (C : Circuit) (J : Finset ℕ) (coverage : coversPairs C J) :
    ∃ K ⊆ J, coversPairs C K ∧ ∀ j ∈ K, ∃ p l : Fin 13, p ∈ singerLines3 l ∧
      wire C (26+j) (pairRow p l) = true ∧ ∀ k ∈ K, k ≠ j → wire C (26+k) (pairRow p l) = false := by
  classical
  let candidates := J.powerset.filter fun K => coversPairs C K
  have start : J ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl,coverage⟩
  obtain ⟨K,hK,least⟩ := candidates.exists_min_image Finset.card ⟨J,start⟩
  obtain ⟨sub,cover⟩ := Finset.mem_filter.mp hK
  refine ⟨K,Finset.mem_powerset.mp sub,cover,?_⟩
  intro j hj
  have lost : ¬coversPairs C (K.erase j) := by
    intro still
    have allowed : K.erase j ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (fun z hz => Finset.mem_powerset.mp sub (Finset.mem_of_mem_erase hz)),still⟩
    have low := least _ allowed
    have small := Finset.card_erase_lt_of_mem hj
    omega
  unfold coversPairs at lost
  push Not at lost
  obtain ⟨p,l,hpl,off⟩ := lost
  obtain ⟨k,hk,on⟩ := cover p l hpl
  have eq : k = j := by
    by_contra ne
    exact off k (Finset.mem_erase.mpr ⟨ne,hk⟩) on
  refine ⟨p,l,hpl,eq ▸ on,?_⟩
  intro z hz ne
  exact Bool.eq_false_iff.mpr (off z (Finset.mem_erase.mpr ⟨ne,hz⟩))

theorem privateFrontier (C : Circuit) (ao : IsAO2 26 C) (J : Finset ℕ)
    (data : ∀ j ∈ J, j < C.size ∧ (gateAt C j).op = GateOp.and) (coverage : coversPairs C J) :
    ∃ K ⊆ J, coversPairs C K ∧
      (∀ j ∈ K, ∃ p l : Fin 13, p ∈ singerLines3 l ∧ wire C (26+j) (pairRow p l) = true ∧
        ∀ k ∈ K, k ≠ j → wire C (26+k) (pairRow p l) = false) ∧
      Set.InjOn (fun j => (gateAt C j).inputs.toFinset) (K : Set ℕ) := by
  obtain ⟨K,sub,cover,priv⟩ := minimalCover C J coverage
  refine ⟨K,sub,cover,priv,?_⟩
  intro i hi j hj same
  by_contra ne
  obtain ⟨p,l,_,yes,others⟩ := priv i hi
  have hno := others j hj (Ne.symm ne)
  have di := data i (sub hi)
  have dj := data j (sub hj)
  have left := (bothActive C ao i di.1 di.2 (pairRow p l) (by simp [pairRow])).mp yes
  change (gateAt C i).inputs.toFinset = (gateAt C j).inputs.toFinset at same
  rw [same] at left
  have other := (bothActive C ao j dj.1 dj.2 (pairRow p l) (by simp [pairRow])).mpr left
  exact Bool.false_ne_true (hno.symm.trans other)

end PEqualNP.Outside.QuadrangleCleanFrontier_aux

theorem PEqualNP.Outside.QuadrangleCleanFrontier :
  let N := fun Q : Finset (Fin 13) =>
    (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn fun l : Fin 13 => decide (l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.TopForm.IsAO2 26 C →
    (∀ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, C.eval (N Q) = false) →
    (∃ x : List Bool, x.length = 26 ∧ C.eval x = true) →
    ∃ J : Finset ℕ,
      (∀ j ∈ J, j < C.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, (C.wires (N Q)).getD (26+j) false = false) ∧
      2*J.card ≤ C.size+1 ∧ ∀ x : List Bool, x.length = 26 →
        (C.eval x = true ↔ ∃ j ∈ J, (C.wires x).getD (26+j) false = true) := by
  intro N C ao clean on
  obtain ⟨J,data,count,evals⟩ := PEqualNP.Outside.QuadrangleCleanFrontier_aux.outputIndexFrontier C ao clean on
  exact ⟨J,data,PEqualNP.Outside.QuadrangleCleanFrontier_aux.cleanBudget C J data count,evals⟩
