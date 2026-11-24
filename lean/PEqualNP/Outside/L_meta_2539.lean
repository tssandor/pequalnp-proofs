import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2539_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The circuit traversal and unary normalization follow L_meta_2315.

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def remap (i : ℕ) := if i = 9 then 0 else if i < 9 then i else i-1

private def conv (g : Gate) : Gate :=
  if 0 ∈ g.inputs ∧ 9 ∈ g.inputs then
    match g.op with
    | GateOp.and => ⟨GateOp.or, []⟩
    | _ => ⟨GateOp.and, []⟩
  else ⟨g.op, g.inputs.map remap⟩

private abbrev marked (g : Gate) := [0,9].any fun i => g.inputs.contains i

private lemma marked_iff (g : Gate) : marked g = true ↔ 0 ∈ g.inputs ∨ 9 ∈ g.inputs := by
  simp [marked]

private lemma short_eq {α : Type*} {x y : α} {xs : List α}
    (bound : xs.length ≤ 1) (hx : x ∈ xs) (hy : y ∈ xs) : x = y := by
  cases xs with
  | nil => simp at hx
  | cons a tail =>
    cases tail with
    | nil => simp_all
    | cons k ks => simp at bound

private theorem orientation (gs : List Gate) (h : (gs.filter marked).length ≤ 1) :
    ∃ b : Bool, ∀ g ∈ gs,
      (0 ∈ g.inputs → 9 ∉ g.inputs → b = false) ∧
      (9 ∈ g.inputs → 0 ∉ g.inputs → b = true) := by
  classical
  by_cases used : ∃ g ∈ gs, 9 ∈ g.inputs ∧ 0 ∉ g.inputs
  · obtain ⟨k,hk,km,kz⟩ := used
    refine ⟨true,fun g hg => ⟨?_,fun _ _ => rfl⟩⟩
    intro gz gm
    have same : g = k := short_eq h
      (List.mem_filter.mpr ⟨hg,(marked_iff g).mpr (.inl gz)⟩)
      (List.mem_filter.mpr ⟨hk,(marked_iff k).mpr (.inr km)⟩)
    exact False.elim (kz (same ▸ gz))
  · exact ⟨false,fun g hg => ⟨fun _ _ => rfl,fun hm hz => False.elim (used ⟨g,hg,hm,hz⟩)⟩⟩

private lemma form {xs : List ℕ} (length : xs.length ≤ 2) (a : 0 ∈ xs) (b : 9 ∈ xs) :
    xs = [0,9] ∨ xs = [9,0] := by
  rcases xs with _|⟨p,_|⟨q,_|⟨r,rs⟩⟩⟩ <;> simp_all <;> grind

private theorem conv_ok (g : Gate) (ok : NOkGate g) : OkGate (conv g) := by
  by_cases h : 0 ∈ g.inputs ∧ 9 ∈ g.inputs
  · cases a : g.op <;> simp [conv,h,a,OkGate]
  · simpa only [conv,h,↓reduceIte,OkGate,List.length_map] using ok.1

private theorem gate_eval (g : Gate) (b t : Bool) (old new : List Bool)
    (ok : NOkGate g)
    (orient : (0 ∈ g.inputs → 9 ∉ g.inputs → b = false) ∧
      (9 ∈ g.inputs → 0 ∉ g.inputs → b = true))
    (z : old.getD 0 false = t) (m : old.getD 9 false = !t)
    (znew : new.getD 0 false = (b != t))
    (agree : ∀ i : ℕ, i ≠ 0 → i ≠ 9 → old.getD i false = new.getD (remap i) false) :
    g.op.eval (g.inputs.map fun i => old.getD i false) =
      (conv g).op.eval ((conv g).inputs.map fun i => new.getD i false) := by
  by_cases both : 0 ∈ g.inputs ∧ 9 ∈ g.inputs
  · have args := form ok.1.2 both.1 both.2
    rcases ok.1.1 with hand|hor|hnot
    · change g.op = GateOp.and at hand
      rcases args with h|h <;> cases t <;> simp only [conv,hand,h,List.map_cons,List.map_nil,z,m] <;> rfl
    · change g.op = GateOp.or at hor
      rcases args with h|h <;> cases t <;> simp only [conv,hor,h,List.map_cons,List.map_nil,z,m] <;> rfl
    · have small := ok.2 hnot
      rcases args with h|h <;> simp [h] at small
  · simp only [conv,both,↓reduceIte,List.map_map]
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro i hi
    by_cases h0 : i = 0
    · subst i
      have hb := orient.1 hi (fun hm => both ⟨hi,hm⟩)
      change old.getD 0 false = new.getD 0 false
      rw [znew,z,hb]
      cases t <;> rfl
    by_cases h9 : i = 9
    · subst i
      have hb := orient.2 hi (fun hz => both ⟨hz,hi⟩)
      change old.getD 9 false = new.getD 0 false
      rw [znew,m,hb]
      cases t <;> rfl
    exact agree i h0 h9

private theorem simulate (gs : List Gate) (b t : Bool) (old new : List Bool)
    (ok : ∀ g ∈ gs, NOkGate g)
    (orient : ∀ g ∈ gs, (0 ∈ g.inputs → 9 ∉ g.inputs → b = false) ∧
      (9 ∈ g.inputs → 0 ∉ g.inputs → b = true))
    (len : old.length = new.length + 1) (long : 9 < old.length)
    (z : old.getD 0 false = t) (m : old.getD 9 false = !t)
    (znew : new.getD 0 false = (b != t))
    (agree : ∀ i : ℕ, i ≠ 0 → i ≠ 9 → old.getD i false = new.getD (remap i) false) :
    ∀ i : ℕ, i ≠ 0 → i ≠ 9 → (wiresFrom gs old).getD i false =
      (wiresFrom (gs.map conv) new).getD (remap i) false := by
  induction gs generalizing old new with
  | nil => exact agree
  | cons g gs ih =>
    let run (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
    have eq : run g old = run (conv g) new := gate_eval _ _ _ _ _ (ok g List.mem_cons_self)
      (orient g List.mem_cons_self) z m znew agree
    simp only [List.map_cons,wiresFrom_cons]
    apply ih (old ++ [run g old]) (new ++ [run (conv g) new]) (fun k hk => ok k (List.mem_cons_of_mem _ hk))
      (fun k hk => orient k (List.mem_cons_of_mem _ hk)) (by simp; omega) (by simp; omega)
      ((getD_snoc_lt _ _ _ _ (by omega)).trans z) ((getD_snoc_lt _ _ _ _ long).trans m)
      ((getD_snoc_lt _ _ _ _ (by omega)).trans znew)
    intro i h0 h9
    by_cases atEnd : i = old.length
    · have atEnd' : remap i = new.length := by simp only [remap,h9,↓reduceIte]; split <;> omega
      rw [getD_snoc_eq _ _ _ _ atEnd,getD_snoc_eq _ _ _ _ atEnd']
      exact eq
    · have away : remap i ≠ new.length := by simp only [remap,h9,↓reduceIte]; split <;> omega
      rw [getD_snoc_ne _ _ _ _ atEnd,getD_snoc_ne _ _ _ _ away]
      exact agree i h0 h9

private lemma shift_zero (i : ℕ) (h : remap i = 0) : i = 0 ∨ i = 9 := by
  simp only [remap] at h
  by_cases h9 : i = 9
  · exact .inr h9
  · simp only [h9,↓reduceIte] at h
    split at h <;> omega

private theorem reader_count (gs : List Gate) :
    ((gs.map conv).filter (fun g => g.inputs.contains 0)).length ≤ (gs.filter marked).length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have le : (conv g).inputs.contains 0 = true → marked g = true := by
      intro h
      apply (marked_iff _).mpr
      by_cases both : 0 ∈ g.inputs ∧ 9 ∈ g.inputs
      · exact .inl both.1
      · have hh : 0 ∈ g.inputs.map remap := by simpa [conv,both] using h
        obtain ⟨i,mem,hi⟩ := List.mem_map.mp hh
        rcases shift_zero i hi with rfl|rfl
        · exact .inl mem
        · exact .inr mem
    simp only [List.map_cons,List.filter_cons]
    by_cases h0 : (conv g).inputs.contains 0 = true
    · have hm := le h0
      simp only [h0,hm,↓reduceIte,List.length_cons]
      omega
    · have hz : (conv g).inputs.contains 0 = false := Bool.eq_false_iff.mpr h0
      rw [hz]
      cases hm : marked g with
      | false => exact ih
      | true => exact Nat.le_succ_of_le ih

private lemma ofFn_at {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i,hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private abbrev transform (b : Bool) (x : Fin 9 → Bool) (i : Fin 9) :=
  if i = 0 then b != x 0 else x i

private def rawTrim (g : Gate) : Gate := ⟨g.op,
  if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩

private theorem trim_eq (g : Gate) (ok : OkGate g) : rawTrim g = normGate g := by
  obtain ⟨op,ins⟩ := g
  rcases ok.1 with h|h|h
  · change op = GateOp.and at h
    subst op
    rfl
  · change op = GateOp.or at h
    subst op
    rfl
  · change op = GateOp.not at h
    subst op
    rfl

private theorem directEmpty (b : Bool) (x : Fin 9 → Bool) :
    circuitFun 9 (⟨[],0⟩ : Circuit) (transform b x) = (b != x 0) := by
  change (List.ofFn (transform b x)).getD 0 false = _
  simp [List.getD_eq_getElem?_getD,transform]

private theorem contract (C : Circuit) (fan : FanInTwo C)
    (head : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 0))
    (bound : (((C.gates.drop 1).map rawTrim).filter marked).length ≤ 1) :
    ∃ D : Circuit, ∃ b : Bool, FanInTwo D ∧ D.size < C.size ∧
      (D.gates.filter fun g => g.inputs.contains 0).length ≤ 1 ∧
      ∀ x : Fin 9 → Bool, circuitFun 9 C x = circuitFun 9 D (transform b x) := by
  cases cc : C.gates with
  | nil =>
    have ht := head (fun _ => false)
    change (wiresFrom C.gates _).getD 9 false = true at ht
    rw [cc,wiresFrom_nil,List.getD_eq_default _ _ (by simp)] at ht
    contradiction
  | cons g gs =>
    have less : (⟨[],0⟩ : Circuit).size < C.size := by simp [Circuit.size,cc]
    have empty : FanInTwo (⟨[],0⟩ : Circuit) := by simp [FanInTwo]
    by_cases out0 : C.output = 0
    · refine ⟨⟨[],0⟩,false,empty,less,by decide,?_⟩
      intro x
      rw [directEmpty]
      change (wiresFrom C.gates (List.ofFn x)).getD C.output false = _
      rw [out0,wiresFrom_getD_lt _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    by_cases out9 : C.output = 9
    · refine ⟨⟨[],0⟩,true,empty,less,by decide,?_⟩
      intro x
      rw [directEmpty]
      change (C.wires (List.ofFn x)).getD C.output false = _
      rw [out9,head]
      cases x 0 <;> rfl
    let tail := gs.map normGate
    have originalOk (k : Gate) (hk : k ∈ gs) : OkGate k := fan k (cc ▸ List.mem_cons_of_mem _ hk)
    have good : ∀ k ∈ tail, NOkGate k := by
      intro k hk
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hk
      exact normGate_nok v (originalOk v hv)
    have teq : gs.map rawTrim = tail := List.map_congr_left (fun k hk => trim_eq k (originalOk k hk))
    rw [cc] at bound
    change ((gs.map rawTrim).filter marked).length ≤ 1 at bound
    rw [teq] at bound
    obtain ⟨b,pol⟩ := orientation tail bound
    let D : Circuit := ⟨tail.map conv, remap C.output⟩
    refine ⟨D,b,?_,?_,(reader_count tail).trans bound,?_⟩
    · intro k hk
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hk
      exact conv_ok v (good v hv)
    · simp [D,tail,Circuit.size,cc]
    · intro x
      let u := List.ofFn x ++ [!(x 0)]
      let v := List.ofFn (transform b x)
      have hh := head x
      change (wiresFrom C.gates (List.ofFn x)).getD 9 false = !(x 0) at hh
      rw [cc,wiresFrom_cons,wiresFrom_getD_lt _ _ _ (by simp),getD_snoc_eq _ _ _ _ (by simp)] at hh
      have agr (i : ℕ) (h0 : i ≠ 0) (h9 : i ≠ 9) : u.getD i false = v.getD (remap i) false := by
        by_cases small : i < 9
        · rw [List.getD_append _ _ _ _ (by simpa using small)]
          have nz : (⟨i,small⟩ : Fin 9) ≠ 0 := fun e => h0 (congrArg Fin.val e)
          simp only [v,remap,h9,small,↓reduceIte]
          rw [ofFn_at _ _ small,ofFn_at _ _ small]
          simp [transform,nz]
        · rw [List.getD_eq_default u _ (by simp [u]; omega),
              List.getD_eq_default v _ (by simp [v,remap,h9,small]; omega)]
      have sim := simulate tail b (x 0) u v good pol (by simp [u,v]) (by simp [u])
        (by simp [u,List.getD_eq_getElem?_getD])
        (getD_snoc_eq _ _ _ _ (by simp))
        (by simp [v,transform,List.getD_eq_getElem?_getD]) agr C.output out0 out9
      change (wiresFrom (gs.map normGate) u).getD C.output false =
        (wiresFrom (tail.map conv) v).getD (remap C.output) false at sim
      rw [wiresFrom_norm] at sim
      change (wiresFrom C.gates (List.ofFn x)).getD C.output false = _
      rw [cc,wiresFrom_cons,hh]
      exact sim

end PEqualNP.Outside.L_meta_2539_aux

theorem PEqualNP.Outside.L_meta_2539 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = !x4 (0 : Fin (9 : ℕ))) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x6 : ℕ) => x5.inputs.contains x6) x2).length ≤ (1 : ℕ) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Bool), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size < x1.size ∧ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (0 : ℕ)) x6.gates).length ≤ (1 : ℕ) ∧ ∀ (x8 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x6 fun (x9 : Fin (9 : ℕ)) => if x9 = (0 : Fin (9 : ℕ)) then x7 != x8 (0 : Fin (9 : ℕ)) else x8 x9 := by
  exact PEqualNP.Outside.L_meta_2539_aux.contract
