import Mathlib
import PEqualNP.Defs

-- The finite branch argument adapts L-meta-2165 and the monotone case adapts L-meta-616.
-- A sole reader of the inverted pivot can be bypassed on one of two promises.
-- Each promise still requires thirteen binary gates.
namespace PEqualNP.Outside.L_petersen_inverted_single_reader_aux
-- The branching and gate-elimination arguments are adapted from L-meta-616.
namespace SparseBranchBound

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

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < m

lemma statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hk => lt_of_lt_of_le hk h

lemma statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s → statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr k, hk => getD_append_left_lt w t k hk

def simpMono (op : GateOp) (m : ℕ) (ins : List Stat) : Stat × Option Gate :=
  match op with
  | GateOp.and =>
    match ins with
    | [] => (Sum.inl true, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl false, _ => (Sum.inl false, none)
      | _, Sum.inl false => (Sum.inl false, none)
      | Sum.inl true, s => (s, none)
      | s, Sum.inl true => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.and, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | GateOp.or =>
    match ins with
    | [] => (Sum.inl false, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl true, _ => (Sum.inl true, none)
      | _, Sum.inl true => (Sum.inl true, none)
      | Sum.inl false, s => (s, none)
      | s, Sum.inl false => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.or, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | _ => (Sum.inl false, none)

lemma simpMono_ok (op : GateOp) (m : ℕ) (ins : List Stat)
    (hins : ∀ s ∈ ins, statValid m s) :
    let res := simpMono op m ins
    statValid (m + res.2.toList.length) res.1 ∧
    ∀ g, res.2 = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  cases op with
  | and =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · simp [simpMono, statValid]
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
        | inr b =>
          simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | or =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
          · simp [simpMono, statValid]
        | inr b =>
          simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | not => simp [simpMono, statValid]
  | mod _ => simp [simpMono, statValid]
  | maj => simp [simpMono, statValid]

lemma simpMono_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2) :
    let res := simpMono op w.length ins
    statVal (res.2.toList.foldl step w) res.1 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval] | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step, statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval] | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step, statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen

def elimPass (n j0 : ℕ) (repl : List Stat → Stat) (gs : List Gate) : List Stat × List Gate :=
  (gs.zipIdx).foldl (fun acc p =>
    let tbl := acc.1
    let outG := acc.2
    if p.2 = j0 then
      (tbl ++ [repl tbl], outG)
    else
      let ins := p.1.inputs.map (fun i => if i < n + p.2 then tbl.getD i (Sum.inl false) else Sum.inl false)
      let res := simpMono p.1.op (n + outG.length) ins
      (tbl ++ [res.1], outG ++ res.2.toList))
    (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat)), [])

lemma elim_step_core (n j0 : ℕ) (repl : List Stat → Stat)
    (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C) (hj0 : j0 < C.gates.length)
    (skip : Bool)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_val : skip = false → ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) →
      statVal w' (repl tbl) = (C.wires (List.ofFn x)).getD (n + j0) false)
    (hunused : skip = true → ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → j ≠ j0 → n + j0 ∉ g.inputs) :
    let res := elimPass n j0 repl C.gates
    res.1.length = n + C.gates.length ∧
    res.2.length < C.gates.length ∧
    (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ i < n + C.gates.length, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
    (∀ (x : Fin n → Bool) (i : ℕ), i < n + C.gates.length → (skip = true → i ≠ n + j0) →
      statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) := by
  have hpref : ∀ k ≤ C.gates.length,
      let res := elimPass n j0 repl (C.gates.take k)
      res.1.length = n + k ∧
      res.2.length ≤ (if j0 < k then k - 1 else k) ∧
      (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ i < n + k, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
      (∀ (x : Fin n → Bool) (i : ℕ), i < n + k → (skip = true → i ≠ n + j0) →
        statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.take_zero, elimPass, List.zipIdx_nil, List.foldl_nil, List.length_ofFn, add_zero, List.length_nil, Nat.not_lt_zero, ↓reduceIte, le_refl, List.not_mem_nil, IsEmpty.forall_iff, imp_true_iff, true_and]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, ↓reduceDIte, Option.getD_some, statValid, hi]
      · intro x i hi _
        have hget : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).getD i (Sum.inl false) = Sum.inr i := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
        rw [hget]
        simp only [statVal, wires_input C x i hi, ofFn_getD_lt x i hi]
    | succ k ih =>
      obtain ⟨hlen, hsz, hgm, hval, hsnd⟩ := ih (by omega)
      have hklt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]'hklt] := List.take_succ_eq_append_getElem hklt
      have hzip : (C.gates.take (k + 1)).zipIdx = (C.gates.take k).zipIdx ++ [(C.gates[k]'hklt, k)] := by
        rw [htake, List.zipIdx_append]
        simp [List.length_take, Nat.min_eq_left (by omega : k ≤ C.gates.length)]
      set prev := elimPass n j0 repl (C.gates.take k)
      have hstep : elimPass n j0 repl (C.gates.take (k + 1)) =
          if k = j0 then
            (prev.1 ++ [repl prev.1], prev.2)
          else
            let ins := (C.gates[k]'hklt).inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
            let res := simpMono (C.gates[k]'hklt).op (n + prev.2.length) ins
            (prev.1 ++ [res.1], prev.2 ++ res.2.toList) := by
        show ((C.gates.take (k + 1)).zipIdx).foldl _ _ = _
        rw [hzip, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      rw [hstep]
      by_cases hkj : k = j0
      · subst hkj
        simp only [↓reduceIte, lt_irrefl, Nat.lt_succ_self] at hsz ⊢
        refine ⟨by simp [hlen]; omega, by omega, hgm, ?_, ?_⟩
        · intro i hi
          by_cases hik : i < n + k
          · rw [getD_append_left_lt_stat]
            · exact hval i hik
            · omega
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            exact hrepl_valid prev.1 hlen hval
        · intro x i hi hsk
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [repl prev.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            exact hsnd x i hik hsk
          · have heq : i = n + k := by omega
            subst heq
            have hskf : skip = false := by
              cases h : skip
              · rfl
              · exact absurd rfl (hsk h)
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            exact hrepl_val hskf x prev.1 (prev.2.foldl step (List.ofFn x)) hlen (fun i hi => hsnd x i hi (by intro h; rw [hskf] at h; cases h))
      · simp only [hkj, ↓reduceIte]
        set g := C.gates[k]'hklt
        set ins := g.inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
        set sm := simpMono g.op (n + prev.2.length) ins
        have hsm_ok := simpMono_ok g.op (n + prev.2.length) ins (fun s hs => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
          by_cases hi : i < n + k
          · simp only [hi, ↓reduceIte]; exact hval i hi
          · simp only [hi, ↓reduceIte, statValid])
        have htolen : sm.2.toList.length ≤ 1 := by cases sm.2 <;> simp
        refine ⟨by simp [hlen]; omega, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append]
          split_ifs at hsz ⊢ <;> omega
        · intro g' hg'
          rcases List.mem_append.mp hg' with hm | hm
          · exact hgm g' hm
          · cases h2 : sm.2 with
            | none => rw [h2] at hm; simp at hm
            | some g0 =>
              rw [h2] at hm
              simp only [Option.toList_some, List.mem_singleton] at hm
              subst hm
              exact hsm_ok.2 g' h2
        · intro i hi
          simp only [List.length_append]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            exact statValid_mono (by omega) _ (hval i hik)
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            rw [← Nat.add_assoc]
            exact hsm_ok.1
        · intro x i hi hsk
          rw [List.foldl_append]
          have hprevlen : (prev.2.foldl step (List.ofFn x)).length = n + prev.2.length := by
            rw [foldl_step_len, List.length_ofFn]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            have hkeep : statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) (prev.1.getD i (Sum.inl false)) =
                statVal (prev.2.foldl step (List.ofFn x)) (prev.1.getD i (Sum.inl false)) := by
              have hvi := hval i hik
              cases hs : prev.1.getD i (Sum.inl false) with
              | inl b => rfl
              | inr m =>
                rw [hs] at hvi
                exact foldl_step_getD_lt sm.2.toList _ m (by rw [hprevlen]; exact hvi)
            rw [hkeep]
            exact hsnd x i hik hsk
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            have hgmem : g ∈ C.gates := List.getElem_mem hklt
            have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g hgmem).1
            have hglen : ins.length ≤ 2 := by simp only [ins, List.length_map]; exact (hmono g hgmem).2
            have hsms := simpMono_sound g.op hgop (prev.2.foldl step (List.ofFn x)) ins hglen
            rw [hprevlen] at hsms
            change statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) sm.1 = _
            rw [hsms]
            have hgetk : C.gates[k]? = some g := List.getElem?_eq_getElem hklt
            rw [wires_gate_ofFn C x k g hgetk]
            congr 1
            simp only [ins, List.map_map]
            apply List.map_congr_left
            intro u hu
            simp only [Function.comp_apply]
            by_cases hu_lt : u < n + k
            · simp only [hu_lt, ↓reduceIte]
              apply hsnd x u hu_lt
              intro hskt hequ
              subst hequ
              exact hunused hskt k g hgetk hkj hu
            · simp only [hu_lt, ↓reduceIte, statVal]
  have hfull := hpref C.gates.length (le_refl _)
  rw [List.take_length] at hfull
  simp only [hj0, ↓reduceIte] at hfull
  exact ⟨hfull.1, by omega, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2⟩
where
  getD_append_left_lt_stat (w t : List Stat) (i : ℕ) (hi : i < w.length) :
      (w ++ t).getD i (Sum.inl false) = w.getD i (Sum.inl false) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma elim_smaller_circuit {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (F : (Fin n → Bool) → Prop)
    (positive : ∀ x, (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → F x)
    (negative : ∀ (x : Fin n → Bool), (∃ a b : Fin n, ∀ i, x i = true → i = a ∨ i = b) →
      F x → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ F x)
    (hedge : ∃ u v : Fin n, G.Adj u v)
    (j0 : ℕ) (hj0 : j0 < C.gates.length)
    (repl : List Stat → Stat) (skip : Bool)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_val : skip = false → ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) →
      statVal w' (repl tbl) = (C.wires (List.ofFn x)).getD (n + j0) false)
    (hunused : skip = true → (C.output ≠ n + j0 ∧ ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → j ≠ j0 → n + j0 ∉ g.inputs)) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size < C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hcore := elim_step_core n j0 repl C hmono hj0 skip hrepl_valid hrepl_val (fun h => (hunused h).2)
  set res := elimPass n j0 repl C.gates
  obtain ⟨u0, v0, huv0⟩ := hedge
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
      (hfun _).mpr (positive _ ⟨u0, v0, huv0, by simp, by simp⟩)
    unfold Circuit.eval at ht
    rw [wires_oob C _ C.output (by omega)] at ht
    exact absurd ht (by decide)
  have hzero : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
    cases h : C.eval (List.ofFn (fun _ : Fin n => false)) with
    | false => rfl
    | true =>
      obtain ⟨_, _, _, hu, _⟩ := negative _ ⟨u0, u0, by simp⟩ ((hfun _).mp h)
      exact absurd hu (by decide)
  have hout_ne : skip = true → C.output ≠ n + j0 := fun h => (hunused h).1
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b
    · have ht := hcore.2.2.2.2 (fun t : Fin n => decide (t = u0 ∨ t = v0)) C.output hout_lt hout_ne
      rw [hout] at ht
      change false = C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) at ht
      have ht2 : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
        (hfun _).mpr (positive _ ⟨u0, v0, huv0, by simp, by simp⟩)
      rw [ht2] at ht; exact absurd ht (by decide)
    · have ht := hcore.2.2.2.2 (fun _ : Fin n => false) C.output hout_lt hout_ne
      rw [hout] at ht
      change true = C.eval (List.ofFn (fun _ : Fin n => false)) at ht
      rw [hzero] at ht; exact absurd ht (by decide)
  | inr wout =>
    refine ⟨⟨res.2, wout⟩, ?_, hcore.2.1, ?_⟩
    · intro g hg
      have := hcore.2.2.1 g hg
      exact ⟨by simpa using this.1, this.2⟩
    · intro x
      have hx := hcore.2.2.2.2 x C.output hout_lt hout_ne
      rw [hout] at hx
      exact hx

lemma large_indep_set {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 1 ≤ n)
    (hcubic : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hno4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) :
    ∃ J : Finset (Fin n), (∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) ∧ n + 1 ≤ 4 * J.card := by
  classical
  have hdeg3 : ∀ v : Fin n, G.degree v = 3 := by
    intro v
    have h := hcubic v
    rw [Set.ncard_eq_toFinset_card'] at h
    have heq : (G.neighborSet v).toFinset = G.neighborFinset v := by
      ext u; simp
    rw [heq] at h
    exact h
  let closedN : Finset (Fin n) → Finset (Fin n) := fun J => J.biUnion (fun u => insert u (G.neighborFinset u))
  have hclosedN_card : ∀ u : Fin n, (insert u (G.neighborFinset u)).card = 4 := by
    intro u
    rw [Finset.card_insert_of_notMem, ← SimpleGraph.degree, hdeg3 u]
    rw [SimpleGraph.mem_neighborFinset]
    exact G.loopless.irrefl u
  have hstep : ∀ k : ℕ, ∀ J : Finset (Fin n), (Finset.univ \ closedN J).card = k →
      (∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) → (closedN J).card + 1 ≤ 4 * J.card →
      ∃ J' : Finset (Fin n), (∀ u ∈ J', ∀ v ∈ J', ¬ G.Adj u v) ∧ n + 1 ≤ 4 * J'.card := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro J hk hind hcard
      by_cases hemp : (Finset.univ \ closedN J).Nonempty
      · obtain ⟨u, hu⟩ := hemp
        have huNot : u ∉ closedN J := (Finset.mem_sdiff.mp hu).2
        have huNotJ : u ∉ J := fun huJ => huNot (Finset.mem_biUnion.mpr ⟨u, huJ, Finset.mem_insert_self u _⟩)
        have huNoAdj : ∀ v ∈ J, ¬ G.Adj u v := fun v hv huv =>
          huNot (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset G v u).mpr huv.symm)⟩)
        set J1 := insert u J
        have hind1 : ∀ a ∈ J1, ∀ b ∈ J1, ¬ G.Adj a b := by
          intro a ha b hb
          rcases Finset.mem_insert.mp ha with rfl | haJ <;> rcases Finset.mem_insert.mp hb with rfl | hbJ
          · exact G.loopless.irrefl _
          · exact huNoAdj b hbJ
          · exact fun h => huNoAdj a haJ h.symm
          · exact hind a haJ b hbJ
        have hJ1card : J1.card = J.card + 1 := Finset.card_insert_of_notMem huNotJ
        have hcl1 : closedN J1 = insert u (G.neighborFinset u) ∪ closedN J := Finset.biUnion_insert
        have hcl1_card : (closedN J1).card + 1 ≤ 4 * J1.card := by
          rw [hcl1, hJ1card]
          have hun := Finset.card_union_le (insert u (G.neighborFinset u)) (closedN J)
          rw [hclosedN_card u] at hun
          omega
        have hsub : Finset.univ \ closedN J1 ⊂ Finset.univ \ closedN J := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro x hx
            rw [Finset.mem_sdiff] at hx ⊢
            refine ⟨hx.1, fun hxcl => hx.2 ?_⟩
            rw [hcl1]; exact Finset.mem_union_right _ hxcl
          · intro heq
            have hu1 : u ∈ Finset.univ \ closedN J1 := heq ▸ hu
            have hu_in : u ∈ closedN J1 := by rw [hcl1]; exact Finset.mem_union_left _ (Finset.mem_insert_self u _)
            exact (Finset.mem_sdiff.mp hu1).2 hu_in
        have hklt : (Finset.univ \ closedN J1).card < k := by
          rw [← hk]; exact Finset.card_lt_card hsub
        exact ih _ hklt J1 rfl hind1 hcl1_card
      · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
        have heq : closedN J = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun x => hemp (Finset.mem_univ x))
        rw [heq, Finset.card_univ, Fintype.card_fin] at hcard
        exact ⟨J, hind, hcard⟩
  let v0 : Fin n := ⟨0, by omega⟩
  have hv0deg : (G.neighborFinset v0).card = 3 := hdeg3 v0
  rw [Finset.card_eq_three] at hv0deg
  obtain ⟨u1, u2, u3, h12, h13, h23, hN0⟩ := hv0deg
  have hu1 : G.Adj v0 u1 := (SimpleGraph.mem_neighborFinset G v0 u1).mp (hN0 ▸ by simp)
  have hu2 : G.Adj v0 u2 := (SimpleGraph.mem_neighborFinset G v0 u2).mp (hN0 ▸ by simp)
  have hu3 : G.Adj v0 u3 := (SimpleGraph.mem_neighborFinset G v0 u3).mp (hN0 ▸ by simp)
  obtain ⟨a, b, hab, hna, hvb1, hvb2⟩ : ∃ a b : Fin n, a ≠ b ∧ ¬ G.Adj a b ∧ G.Adj v0 a ∧ G.Adj v0 b := by
    by_cases h : G.Adj u1 u2
    · by_cases h' : G.Adj u2 u3
      · exfalso
        exact hno4 v0 u1 u2 u3 (G.ne_of_adj hu1) (G.ne_of_adj hu2) (G.ne_of_adj hu3) h12 h13 h23 hu1 h h' hu3.symm
      · exact ⟨u2, u3, h23, h', hu2, hu3⟩
    · exact ⟨u1, u2, h12, h, hu1, hu2⟩
  set J0 : Finset (Fin n) := {a, b}
  have hind0 : ∀ u ∈ J0, ∀ v ∈ J0, ¬ G.Adj u v := by
    intro u hu v hv
    simp only [J0, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact G.loopless.irrefl _
    · exact hna
    · exact fun h => hna h.symm
    · exact G.loopless.irrefl _
  have hcl0 : (closedN J0).card + 1 ≤ 4 * J0.card := by
    have hJ0c : J0.card = 2 := Finset.card_pair hab
    have hcl_eq : closedN J0 = insert a (G.neighborFinset a) ∪ insert b (G.neighborFinset b) := by
      simp [closedN, J0]
    have hv0_inter : v0 ∈ insert a (G.neighborFinset a) ∩ insert b (G.neighborFinset b) := by
      rw [Finset.mem_inter]
      exact ⟨Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset G a v0).mpr hvb1.symm),
             Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset G b v0).mpr hvb2.symm)⟩
    have hinter_pos : 1 ≤ (insert a (G.neighborFinset a) ∩ insert b (G.neighborFinset b)).card :=
      Finset.card_pos.mpr ⟨v0, hv0_inter⟩
    have hun := Finset.card_union_add_card_inter (insert a (G.neighborFinset a)) (insert b (G.neighborFinset b))
    rw [hclosedN_card a, hclosedN_card b] at hun
    rw [hcl_eq, hJ0c]
    omega
  exact hstep _ J0 rfl hind0 hcl0

def orEndAux (n s : ℕ) (C : Circuit) (outdeg nextOf : ℕ → ℕ)
    (hnext : ∀ w, w < n + s - 1 → outdeg w = 1 → w < n + nextOf w) (w : ℕ) : ℕ :=
  if _h : w < n + s - 1 ∧ outdeg w = 1 then
    if hlt : nextOf w < C.gates.length then
      match (C.gates[nextOf w]'hlt).op with
      | GateOp.or => orEndAux n s C outdeg nextOf hnext (n + nextOf w)
      | _ => w
    else w
  else w
termination_by n + s - w
decreasing_by
  have := hnext w _h.1 _h.2
  omega

def orChainAux (n s : ℕ) (C : Circuit) (outdeg nextOf : ℕ → ℕ)
    (hnext : ∀ w, w < n + s - 1 → outdeg w = 1 → w < n + nextOf w) (w : ℕ) : Finset ℕ :=
  if _h : w < n + s - 1 ∧ outdeg w = 1 then
    if hlt : nextOf w < C.gates.length then
      match (C.gates[nextOf w]'hlt).op with
      | GateOp.or => insert w (orChainAux n s C outdeg nextOf hnext (n + nextOf w))
      | _ => ∅
    else ∅
  else ∅
termination_by n + s - w
decreasing_by
  have := hnext w _h.1 _h.2
  omega

set_option maxHeartbeats 2000000 in
lemma main_bound (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (degree : ∀ v, 2 ≤ G.degree v)
    (hdistinct_nbrs : ∀ v w : Fin n, v ≠ w → ∃ u, G.Adj v u ∧ ¬ G.Adj w u)
    (coverWitness : ∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S →
      S.card = t → ∃ v ∈ S, 3 ≤ G.degree v ∧ 2 ≤ (G.neighborFinset v ∩ (Finset.univ \ S)).card)
    (F : (Fin n → Bool) → Prop)
    (positive : ∀ x, (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → F x)
    (negative : ∀ (x : Fin n → Bool), (∃ a b : Fin n, ∀ i, x i = true → i = a ∨ i = b) →
      F x → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (ht_min : ∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) :
    ∀ s : ℕ, ∀ C : Circuit, C.size = s →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ F x) →
      n + t ≤ s := by
  classical
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro C hCsize hmono hfun
    have hCglen : C.gates.length = s := hCsize
    by_cases hn0 : n = 0
    · subst hn0
      have ht0 : t ≤ 0 := ht_min ∅ (fun u => Fin.elim0 u)
      omega
    have hn1 : 1 ≤ n := by omega
    have hedge : ∃ u v : Fin n, G.Adj u v := by
      let v0 : Fin n := ⟨0, hn1⟩
      have hpos : 0 < (G.neighborFinset v0).card := by have := degree v0; change 2 ≤ (G.neighborFinset v0).card at this; omega
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      exact ⟨v0, u, (SimpleGraph.mem_neighborFinset G v0 u).mp hu⟩
    have hmin : ∀ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' → C'.size < s →
        (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) → n + t ≤ s := by
      intro C' hC'm hC'sz hC'eq
      have hC'fun : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = true ↔ F x := by
        intro x; rw [hC'eq x, hfun x]
      have := ih C'.size hC'sz C' rfl hC'm hC'fun
      omega
    by_contra hlt_goal
    have hnot_smaller : ∀ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' → C'.size < s →
        (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) → False :=
      fun C' hm hsz heq => hlt_goal (hmin C' hm hsz heq)
    have hno_const_or_copy : ∀ (j0 : ℕ), j0 < s →
        (¬ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j0) false = false) ∧
        (¬ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j0) false = true) ∧
        (∀ w0 < n + j0, ¬ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j0) false = (C.wires (List.ofFn x)).getD w0 false) := by
      intro j0 hj0
      have hj0len : j0 < C.gates.length := by omega
      refine ⟨?_, ?_, ?_⟩
      · intro hf
        obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono F positive negative hfun hedge j0 hj0len (fun _ => Sum.inl false) false
          (fun _ _ _ => trivial) (fun _ x _ _ _ _ => (hf x).symm) (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
      · intro ht
        obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono F positive negative hfun hedge j0 hj0len (fun _ => Sum.inl true) false
          (fun _ _ _ => trivial) (fun _ x _ _ _ _ => (ht x).symm) (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
      · intro w0 hw0 heqw
        obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono F positive negative hfun hedge j0 hj0len (fun tbl => tbl.getD w0 (Sum.inl false)) false
          (fun tbl _ hv => hv w0 hw0)
          (fun _ x tbl w' _ hvals => (hvals w0 hw0).trans (heqw x).symm)
          (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
    have hgate_shape : ∀ (j : ℕ) (hj : j < C.gates.length),
        ∃ p q : ℕ, (C.gates[j]'hj).inputs = [p, q] ∧ p < n + j ∧ q < n + j ∧ p ≠ q := by
      intro j hj
      have hj_s : j < s := by omega
      have hg : C.gates[j]? = some (C.gates[j]'hj) := List.getElem?_eq_getElem hj
      have hgop : (C.gates[j]'hj).op = GateOp.and ∨ (C.gates[j]'hj).op = GateOp.or := by
        simpa using (hmono _ (List.getElem_mem hj)).1
      have hglen : (C.gates[j]'hj).inputs.length ≤ 2 := (hmono _ (List.getElem_mem hj)).2
      obtain ⟨hnc0, hnc1, hncw⟩ := hno_const_or_copy j hj_s
      rcases hinp : (C.gates[j]'hj).inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · rcases hgop with hand | hor
        · exfalso; apply hnc1; intro x; rw [wires_gate_ofFn C x j _ hg, hand, hinp]; rfl
        · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; rfl
      · by_cases hp : p < n + j
        · exfalso; apply hncw p hp; intro x
          rw [wires_gate_ofFn C x j _ hg, hinp]
          rcases hgop with hand | hor
          · simp [hand, GateOp.eval, hp]
          · simp [hor, GateOp.eval, hp]
        · exfalso; apply hnc0; intro x
          rw [wires_gate_ofFn C x j _ hg, hinp]
          rcases hgop with hand | hor
          · simp [hand, GateOp.eval, hp]
          · simp [hor, GateOp.eval, hp]
      · by_cases hp : p < n + j
        · by_cases hq : q < n + j
          · by_cases hpq : p = q
            · subst hpq
              exfalso; apply hncw p hp; intro x
              rw [wires_gate_ofFn C x j _ hg, hinp]
              rcases hgop with hand | hor
              · simp [hand, GateOp.eval, hp]
              · simp [hor, GateOp.eval, hp]
            · exact ⟨p, q, rfl, hp, hq, hpq⟩
          · rcases hgop with hand | hor
            · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hand, hinp]; simp [GateOp.eval, hq]
            · exfalso; apply hncw p hp; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; simp [GateOp.eval, hp, hq]
        · rcases hgop with hand | hor
          · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hand, hinp]; simp [GateOp.eval, hp]
          · by_cases hq : q < n + j
            · exfalso; apply hncw q hq; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; simp [GateOp.eval, hp, hq]
            · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; simp [GateOp.eval, hp, hq]
      · rw [hinp] at hglen; simp at hglen
    have hout_bounds : n ≤ C.output ∧ C.output < n + s := by
      refine ⟨?_, ?_⟩
      · by_contra hlt
        have hw : C.output < n := by omega
        let v : Fin n := ⟨C.output, hw⟩
        have hfv : C.eval (List.ofFn (fun t : Fin n => decide (t = v))) = false := by
          cases h : C.eval (List.ofFn (fun t : Fin n => decide (t = v))) with
          | false => rfl
          | true =>
            obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨v, v, by simp⟩ ((hfun _).mp h)
            simp only [decide_eq_true_eq] at ha hb
            subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
        unfold Circuit.eval at hfv
        rw [wires_input C _ C.output hw] at hfv
        simp [v] at hfv
      · by_contra hge
        obtain ⟨u0, v0, huv0⟩ := hedge
        have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
          (hfun _).mpr (positive _ ⟨u0, v0, huv0, by simp, by simp⟩)
        unfold Circuit.eval at ht
        rw [wires_oob C _ C.output (by omega)] at ht
        exact absurd ht (by decide)
    have hs_pos : 1 ≤ s := by omega
    have hgate_used : ∀ j < s, n + j ≠ C.output → ∃ j' : Fin C.gates.length, n + j ∈ (C.gates[j'.val]).inputs := by
      intro j hjs hne
      by_contra hnone
      have hjlen : j < C.gates.length := by omega
      obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono F positive negative hfun hedge j hjlen (fun _ => Sum.inl false) true
        (fun _ _ _ => trivial) (by intro h; cases h)
        (fun _ => ⟨hne.symm, fun j' g' hg' _ hmem => by
          have hj'lt : j' < C.gates.length := by
            by_contra hge; rw [List.getElem?_eq_none (by omega)] at hg'; cases hg'
          rw [List.getElem?_eq_getElem hj'lt, Option.some.injEq] at hg'
          subst hg'
          exact hnone ⟨⟨j', hj'lt⟩, hmem⟩⟩)
      exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
    have hout_last : C.output = n + s - 1 := by
      by_contra hne
      have hlast_ne : n + (s - 1) ≠ C.output := by omega
      obtain ⟨j', hj'mem⟩ := hgate_used (s - 1) (by omega) hlast_ne
      obtain ⟨p, q, hpq, hp, hq, _⟩ := hgate_shape j'.val j'.isLt
      rw [hpq] at hj'mem
      have hj's : j'.val < s := by have := j'.isLt; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'mem
      rcases hj'mem with h | h <;> omega
    let outdeg : ℕ → ℕ := fun w => ∑ j : Fin C.gates.length, (C.gates[j.val]).inputs.count w
    have hcount_mem : ∀ (j : Fin C.gates.length) (w : ℕ),
        (C.gates[j.val]).inputs.count w = if w ∈ (C.gates[j.val]).inputs then 1 else 0 := by
      intro j w
      obtain ⟨p, q, hpq, _, _, hne⟩ := hgate_shape j.val j.isLt
      rw [hpq]
      by_cases hwp : w = p
      · subst hwp; simp [hne]
      · by_cases hwq : w = q
        · subst hwq; simp [hwp, Ne.symm hwp]
        · simp [hwp, Ne.symm hwp, hwq, Ne.symm hwq]
    have houtdeg_card : ∀ w : ℕ, outdeg w = (Finset.univ.filter (fun j : Fin C.gates.length => w ∈ (C.gates[j.val]).inputs)).card := by
      intro w
      simp only [outdeg, hcount_mem, Finset.sum_boole, Nat.cast_id]
    have hinput_used : ∀ v : Fin n, 1 ≤ outdeg v.val := by
      intro v
      by_contra h0
      have hzero : outdeg v.val = 0 := by omega
      rw [houtdeg_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hzero
      have hno_read : ∀ j : Fin C.gates.length, v.val ∉ (C.gates[j.val]).inputs := fun j hj =>
        hzero j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hpos : 0 < (G.neighborFinset v).card := by have := degree v; change 2 ≤ (G.neighborFinset v).card at this; omega
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      have hvu : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp hu
      have hvu_ne : v ≠ u := G.ne_of_adj hvu
      let x : Fin n → Bool := fun t => decide (t = u)
      let x' : Fin n → Bool := Function.update x v true
      have hind : ∀ w : ℕ, w ≠ v.val → (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn x')).getD w false := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ihw =>
          intro hwv
          by_cases hw1 : w < n
          · rw [wires_input C x w hw1, wires_input C x' w hw1]
            have hne : (⟨w, hw1⟩ : Fin n) ≠ v := fun h => hwv (congrArg Fin.val h)
            exact (Function.update_of_ne hne true x).symm
          · by_cases hw2 : n + C.gates.length ≤ w
            · rw [wires_oob C x w hw2, wires_oob C x' w hw2]
            · have hjlt : w - n < C.gates.length := by omega
              set j := w - n
              have hwj : w = n + j := by omega
              have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C x' j _ hg]
              congr 1
              apply List.map_congr_left
              intro k hk
              have hkv : k ≠ v.val := fun h => hno_read ⟨j, hjlt⟩ (h ▸ hk)
              by_cases hklt : k < n + j
              · simp only [hklt, ↓reduceIte]; exact ihw k (by omega) hkv
              · simp only [hklt, ↓reduceIte]
      have heq := hind C.output (by omega)
      change C.eval (List.ofFn x) = C.eval (List.ofFn x') at heq
      have hf1 : C.eval (List.ofFn x) = false := by
        cases h : C.eval (List.ofFn x) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨u, u, by simp [x]⟩ ((hfun x).mp h)
          simp only [x, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf2 : C.eval (List.ofFn x') = true := by
        rw [hfun]
        apply positive
        exact ⟨v, u, hvu, by simp [x'], by simp [x', x, hvu_ne.symm]⟩
      rw [hf1, hf2] at heq; exact absurd heq (by decide)
    have houtdeg_ge1 : ∀ w < n + s - 1, 1 ≤ outdeg w := by
      intro w hw
      by_cases hwn : w < n
      · exact hinput_used ⟨w, hwn⟩
      · have hj : w - n < s := by omega
        have hwj : w = n + (w - n) := by omega
        obtain ⟨j', hj'm⟩ := hgate_used (w - n) hj (by omega)
        rw [houtdeg_card]
        exact Finset.card_pos.mpr ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ j', hwj ▸ hj'm⟩⟩
    have houtdeg_sum : ∑ w ∈ Finset.range (n + s - 1), outdeg w = 2 * s := by
      have hswap : ∑ w ∈ Finset.range (n + s - 1), outdeg w =
          ∑ j : Fin C.gates.length, ∑ w ∈ Finset.range (n + s - 1), (C.gates[j.val]).inputs.count w :=
        Finset.sum_comm
      rw [hswap]
      have heach : ∀ j : Fin C.gates.length, ∑ w ∈ Finset.range (n + s - 1), (C.gates[j.val]).inputs.count w = 2 := by
        intro j
        obtain ⟨p, q, hpq, hp, hq, hne⟩ := hgate_shape j.val j.isLt
        have hj_s : j.val < s := by have := j.isLt; omega
        have hp_mem : p ∈ Finset.range (n + s - 1) := Finset.mem_range.mpr (by omega)
        have hq_mem : q ∈ Finset.range (n + s - 1) := Finset.mem_range.mpr (by omega)
        have hsub : ({p, q} : Finset ℕ) ⊆ Finset.range (n + s - 1) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_pair hne, hpq]
          simp [hne, Ne.symm hne]
        · intro w _ hw
          rw [hpq]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
          simp [Ne.symm hw.1, Ne.symm hw.2]
      simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hlen : C.gates.length = s := hCsize
      omega
    have hsurplus_sum : (∑ w ∈ Finset.range (n + s - 1), (outdeg w - 1)) + n = s + 1 := by
      have hadd : ∑ w ∈ Finset.range (n + s - 1), (outdeg w - 1) + ∑ _w ∈ Finset.range (n + s - 1), 1 =
          ∑ w ∈ Finset.range (n + s - 1), outdeg w := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        have := houtdeg_ge1 w (Finset.mem_range.mp hw)
        omega
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, houtdeg_sum] at hadd
      omega
    have hnext_uniq : ∀ w < n + s - 1, outdeg w = 1 →
        ∃! j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs := by
      intro w _ h1
      rw [houtdeg_card, Finset.card_eq_one] at h1
      obtain ⟨j, hj⟩ := h1
      have hjmem : j ∈ Finset.univ.filter (fun j : Fin C.gates.length => w ∈ (C.gates[j.val]).inputs) :=
        hj ▸ Finset.mem_singleton_self j
      refine ⟨j, (Finset.mem_filter.mp hjmem).2, ?_⟩
      intro j' hj'
      have hj'mem : j' ∈ ({j} : Finset (Fin C.gates.length)) :=
        hj ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j', hj'⟩
      exact Finset.mem_singleton.mp hj'mem
    let nextOf : (w : ℕ) → ℕ := fun w =>
      if h : w < n + s - 1 ∧ outdeg w = 1 then
        (hnext_uniq w h.1 h.2).choose.val
      else
        0
    have hnextOf_spec : ∀ w, w < n + s - 1 → outdeg w = 1 →
        ∃ hlt : nextOf w < C.gates.length, w ∈ (C.gates[nextOf w]'hlt).inputs ∧
          ∀ j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs → j.val = nextOf w := by
      intro w hw h1
      have hdef : nextOf w = (hnext_uniq w hw h1).choose.val := by simp [nextOf, hw, h1]
      have hsp := (hnext_uniq w hw h1).choose_spec
      refine ⟨by rw [hdef]; exact (hnext_uniq w hw h1).choose.isLt, ?_, ?_⟩
      · simpa [hdef] using hsp.1
      · intro j hj; rw [hdef]; exact congrArg Fin.val (hsp.2 j hj)
    have hnextOf_gt : ∀ w, w < n + s - 1 → outdeg w = 1 → w < n + nextOf w := by
      intro w hw h1
      obtain ⟨hlt, hmem, _⟩ := hnextOf_spec w hw h1
      obtain ⟨p, q, hpq, hp, hq, _⟩ := hgate_shape (nextOf w) hlt
      rw [hpq] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> assumption
    let orEnd : ℕ → ℕ := orEndAux n s C outdeg nextOf hnextOf_gt
    let orChain : ℕ → Finset ℕ := orChainAux n s C outdeg nextOf hnextOf_gt
    have horEnd_ge : ∀ w, w ≤ orEnd w := by
      intro w
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hrec := ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) rfl
            change w ≤ orEnd (n + nextOf w)
            omega
          | and => exact le_refl w
          | not => exact le_refl w
          | mod _ => exact le_refl w
          | maj => exact le_refl w
        · exact le_refl w
        · exact le_refl w
    have horEnd_lt : ∀ w, w < n + s → orEnd w < n + s := by
      intro w hw
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hns : nextOf w < s := by omega
            exact ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) rfl
          | and => exact hw
          | not => exact hw
          | mod _ => exact hw
          | maj => exact hw
        · exact hw
        · exact hw
    have horEnd_true : ∀ (w : ℕ) (x : Fin n → Bool), w < n + s → (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn x)).getD (orEnd w) false = true := by
      intro w x hw hwt
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hns : nextOf w < s := by omega
            obtain ⟨hlt', hmem, _⟩ := hnextOf_spec w h.1 h.2
            have hg : C.gates[nextOf w]? = some (C.gates[nextOf w]'hlt) := List.getElem?_eq_getElem hlt
            have hnext_t : (C.wires (List.ofFn x)).getD (n + nextOf w) false = true := by
              rw [wires_gate_ofFn C x (nextOf w) _ hg, hop]
              change ((C.gates[nextOf w]'hlt).inputs.map fun i => if i < n + nextOf w then (C.wires (List.ofFn x)).getD i false else false).any id = true
              rw [List.any_eq_true]
              exact ⟨_, List.mem_map_of_mem hmem, by simp only [id_eq, hgt, ↓reduceIte, hwt]⟩
            exact ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) hnext_t rfl
          | and => exact hwt
          | not => exact hwt
          | mod _ => exact hwt
          | maj => exact hwt
        · exact hwt
        · exact hwt
    have horEnd_stop : ∀ w, w < n + s - 1 →
        (orEnd w = n + s - 1) ∨
        (orEnd w < n + s - 1 ∧ 2 ≤ outdeg (orEnd w)) ∨
        (orEnd w < n + s - 1 ∧ outdeg (orEnd w) = 1 ∧
          ∃ hlt : nextOf (orEnd w) < C.gates.length, (C.gates[nextOf (orEnd w)]'hlt).op = GateOp.and) := by
      intro w hw
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        by_cases h1 : w < n + s - 1 ∧ outdeg w = 1
        · obtain ⟨hlt, _, _⟩ := hnextOf_spec w h1.1 h1.2
          simp only [h1, ↓reduceDIte, hlt]
          have hgop : (C.gates[nextOf w]'hlt).op = GateOp.and ∨ (C.gates[nextOf w]'hlt).op = GateOp.or := by
            simpa using (hmono _ (List.getElem_mem hlt)).1
          rcases hgop with hand | hor
          · simp only [hand]
            exact Or.inr (Or.inr ⟨hw, h1.2, hlt, hand⟩)
          · simp only [hor]
            have hgt := hnextOf_gt w h1.1 h1.2
            have hns : nextOf w < s := by omega
            by_cases hlast : n + nextOf w = n + s - 1
            · left
              rw [hlast]
              rw [orEndAux]
              simp
            · exact ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) rfl
        · simp only [h1, ↓reduceDIte]
          have hge1 := houtdeg_ge1 w hw
          have hne1 : outdeg w ≠ 1 := fun h => h1 ⟨hw, h⟩
          exact Or.inr (Or.inl ⟨hw, by omega⟩)
    have horChain_props : ∀ w, w < n + s →
        (w ∉ orChain w → w = orEnd w) ∧
        (∀ u ∈ orChain w, u < orEnd w ∧ u < n + s - 1 ∧ outdeg u = 1 ∧
          (n + nextOf u ∈ orChain w ∨ n + nextOf u = orEnd w)) := by
      intro w hw
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orChain, orEnd]; rw [orChainAux, orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hns : nextOf w < s := by omega
            obtain ⟨hrec1, hrec2⟩ := ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) rfl
            refine ⟨fun hnot => absurd (Finset.mem_insert_self w _) hnot, ?_⟩
            intro u hu
            rcases Finset.mem_insert.mp hu with huw | hu'
            · subst huw
              have hge := horEnd_ge (n + nextOf u)
              refine ⟨by change u < orEnd (n + nextOf u); omega, h.1, h.2, ?_⟩
              by_cases hmem : n + nextOf u ∈ orChain (n + nextOf u)
              · exact Or.inl (Finset.mem_insert_of_mem hmem)
              · exact Or.inr (hrec1 hmem)
            · obtain ⟨h1, h2, h3, h4⟩ := hrec2 u hu'
              exact ⟨h1, h2, h3, h4.imp Finset.mem_insert_of_mem id⟩
          | and => simp
          | not => simp
          | mod _ => simp
          | maj => simp
        · simp
        · simp
    have horChain_in : ∀ w u, u ∈ orChain w → w ≤ u := by
      intro w u hu
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orChain] at hu; rw [orChainAux] at hu
        split_ifs at hu with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            rw [hop] at hu
            rcases Finset.mem_insert.mp hu with rfl | hu'
            · exact le_refl u
            · have hgt := hnextOf_gt w h.1 h.2
              have hrec := ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) hu' rfl
              omega
          | and => rw [hop] at hu; simp at hu
          | not => rw [hop] at hu; simp at hu
          | mod _ => rw [hop] at hu; simp at hu
          | maj => rw [hop] at hu; simp at hu
        · simp at hu
        · simp at hu
    have horChain_self_or : ∀ w, w < n + s → w ∈ orChain w ∨ w = orEnd w := by
      intro w hw
      by_cases h : w ∈ orChain w
      · exact Or.inl h
      · exact Or.inr ((horChain_props w hw).1 h)
    have horEnd_sole_exit : ∀ (v : Fin n) (x y : Fin n → Bool),
        (∀ t : Fin n, t ≠ v → x t = y t) →
        (C.wires (List.ofFn x)).getD (orEnd v.val) false = (C.wires (List.ofFn y)).getD (orEnd v.val) false →
        ∀ u : ℕ, u < n + s → u ∉ orChain v.val →
          (C.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn y)).getD u false := by
      intro v x y hxy hseq u hu
      induction u using Nat.strong_induction_on with
      | ind u ihu =>
        intro hunot
        by_cases hueq : u = orEnd v.val
        · rw [hueq]; exact hseq
        · by_cases hu1 : u < n
          · rw [wires_input C x u hu1, wires_input C y u hu1]
            have hne : (⟨u, hu1⟩ : Fin n) ≠ v := by
              intro h
              have huv : u = v.val := congrArg Fin.val h
              subst huv
              rcases horChain_self_or v.val (by omega) with hm | he
              · exact hunot hm
              · exact hueq he
            exact hxy ⟨u, hu1⟩ hne
          · have hjlt : u - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
            set j := u - n
            have huj : u = n + j := by omega
            have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
            rw [huj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
            congr 1
            apply List.map_congr_left
            intro k hk
            by_cases hklt : k < n + j
            · simp only [hklt, ↓reduceIte]
              apply ihu k (by omega) (by omega)
              intro hkch
              obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props v.val (by omega)).2 k hkch
              obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
              have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
              rw [hjeq] at huj
              rcases hknxt with h1 | h2
              · exact hunot (huj ▸ h1)
              · exact hueq (huj ▸ h2)
            · simp only [hklt, ↓reduceIte]
    have hs_ne_out : ∀ v : Fin n, orEnd v.val < n + s - 1 := by
      intro v
      have hlt := horEnd_lt v.val (by omega)
      by_contra hge
      have heq : orEnd v.val = C.output := by omega
      have h1 : (C.wires (List.ofFn (fun t : Fin n => decide (t = v)))).getD (orEnd v.val) false = true := by
        apply horEnd_true v.val _ (by omega)
        rw [wires_input C _ v.val v.isLt]; simp
      rw [heq] at h1
      change C.eval (List.ofFn (fun t : Fin n => decide (t = v))) = true at h1
      obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨v, v, by simp⟩ ((hfun _).mp h1)
      simp only [decide_eq_true_eq] at ha hb
      subst ha; subst hb; exact G.loopless.irrefl _ hab
    have hs_zero_other : ∀ v q : Fin n, q ≠ v →
        (C.wires (List.ofFn (fun t : Fin n => decide (t = q)))).getD (orEnd v.val) false = false := by
      intro v q hqv
      by_contra hne
      have htrue : (C.wires (List.ofFn (fun t : Fin n => decide (t = q)))).getD (orEnd v.val) false = true := by
        cases h : (C.wires (List.ofFn (fun t : Fin n => decide (t = q)))).getD (orEnd v.val) false
        · exact absurd h hne
        · rfl
      have hout_not_ch : C.output ∉ orChain v.val := by
        intro hmem
        have := (horChain_props v.val (by omega)).2 C.output hmem
        omega
      by_cases hadj : G.Adj v q
      · let x : Fin n → Bool := fun t => decide (t = q)
        let y : Fin n → Bool := Function.update x v true
        have hy_true : (C.wires (List.ofFn y)).getD (orEnd v.val) false = true := by
          apply horEnd_true v.val y (by omega)
          rw [wires_input C y v.val v.isLt]
          have : (⟨v.val, v.isLt⟩ : Fin n) = v := Fin.ext rfl
          rw [this]; simp [y]
        have heq := horEnd_sole_exit v x y (fun t ht => (Function.update_of_ne ht true x).symm)
          (htrue.trans hy_true.symm) C.output (by omega) hout_not_ch
        change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heq
        have hf0 : C.eval (List.ofFn x) = false := by
          cases h : C.eval (List.ofFn x) with
          | false => rfl
          | true =>
            obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨q, q, by simp [x]⟩ ((hfun x).mp h)
            simp only [x, decide_eq_true_eq] at ha hb
            subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
        have hf1 : C.eval (List.ofFn y) = true := by
          rw [hfun]
          apply positive
          exact ⟨v, q, hadj, by simp [y], by simp [y, x, hqv]⟩
        rw [hf0, hf1] at heq; exact absurd heq (by decide)
      · obtain ⟨u, hvu, hnw⟩ := hdistinct_nbrs v q hqv.symm
        have huv : u ≠ v := (G.ne_of_adj hvu).symm
        let x : Fin n → Bool := fun t => decide (t = q ∨ t = u)
        let y : Fin n → Bool := Function.update x v true
        have hx_true : (C.wires (List.ofFn x)).getD (orEnd v.val) false = true :=
          wires_mono C hmono (fun t => decide (t = q)) x (fun t ht => by simp only [x, decide_eq_true_eq] at ht ⊢; exact Or.inl ht) (orEnd v.val) htrue
        have hy_true : (C.wires (List.ofFn y)).getD (orEnd v.val) false = true := by
          apply horEnd_true v.val y (by omega)
          rw [wires_input C y v.val v.isLt]
          have : (⟨v.val, v.isLt⟩ : Fin n) = v := Fin.ext rfl
          rw [this]; simp [y]
        have heq := horEnd_sole_exit v x y (fun t ht => (Function.update_of_ne ht true x).symm)
          (hx_true.trans hy_true.symm) C.output (by omega) hout_not_ch
        change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heq
        have hf0 : C.eval (List.ofFn x) = false := by
          cases h : C.eval (List.ofFn x) with
          | false => rfl
          | true =>
            obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨q, u, by simp [x]⟩ ((hfun x).mp h)
            simp only [x, decide_eq_true_eq] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact absurd hab (G.loopless.irrefl _)
            · exact absurd hab hnw
            · exact absurd hab.symm hnw
            · exact absurd hab (G.loopless.irrefl _)
        have hf1 : C.eval (List.ofFn y) = true := by
          rw [hfun]
          apply positive
          exact ⟨v, u, hvu, by simp [y], by simp [y, x, huv]⟩
        rw [hf0, hf1] at heq; exact absurd heq (by decide)
    have hs_inj : Function.Injective (fun v : Fin n => orEnd v.val) := by
      intro v w hvw
      by_contra hne
      have h1 : (C.wires (List.ofFn (fun t : Fin n => decide (t = v)))).getD (orEnd v.val) false = true := by
        apply horEnd_true v.val _ (by omega)
        rw [wires_input C _ v.val v.isLt]; simp
      have h2 := hs_zero_other w v hne
      dsimp only at hvw
      rw [hvw, h2] at h1
      exact absurd h1 (by decide)
    set Tbranch : Finset (Fin n) := Finset.univ.filter (fun v : Fin n => 2 ≤ outdeg (orEnd v.val))
    have hand_exit : ∀ v : Fin n, v ∉ Tbranch →
        outdeg (orEnd v.val) = 1 ∧
        ∃ hlt : nextOf (orEnd v.val) < C.gates.length, (C.gates[nextOf (orEnd v.val)]'hlt).op = GateOp.and := by
      intro v hv
      have hnot2 : ¬ 2 ≤ outdeg (orEnd v.val) := fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
      have hlt := hs_ne_out v
      rcases horEnd_stop v.val (by omega) with h1 | h2 | h3
      · omega
      · omega
      · exact ⟨h3.2.1, h3.2.2⟩
    have hand_sole_exit : ∀ (v : Fin n) (hv : v ∉ Tbranch) (x y : Fin n → Bool),
        (∀ t : Fin n, t ≠ v → x t = y t) →
        (C.wires (List.ofFn x)).getD (n + nextOf (orEnd v.val)) false =
        (C.wires (List.ofFn y)).getD (n + nextOf (orEnd v.val)) false →
        ∀ u : ℕ, u < n + s → u ∉ orChain v.val → u ≠ orEnd v.val →
          (C.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn y)).getD u false := by
      intro v hv x y hxy haeq u hu
      obtain ⟨h1, hlt_a, _⟩ := hand_exit v hv
      have hlt_s := hs_ne_out v
      induction u using Nat.strong_induction_on with
      | ind u ihu =>
        intro hunot hune
        by_cases hueq : u = n + nextOf (orEnd v.val)
        · rw [hueq]; exact haeq
        · by_cases hu1 : u < n
          · rw [wires_input C x u hu1, wires_input C y u hu1]
            have hne : (⟨u, hu1⟩ : Fin n) ≠ v := by
              intro h
              have huv : u = v.val := congrArg Fin.val h
              subst huv
              rcases horChain_self_or v.val (by omega) with hm | he
              · exact hunot hm
              · exact hune he
            exact hxy ⟨u, hu1⟩ hne
          · have hjlt : u - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
            set j := u - n
            have huj : u = n + j := by omega
            have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
            rw [huj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
            congr 1
            apply List.map_congr_left
            intro k hk
            by_cases hklt : k < n + j
            · simp only [hklt, ↓reduceIte]
              apply ihu k (by omega) (by omega)
              · intro hkch
                obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props v.val (by omega)).2 k hkch
                obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
                have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
                rw [hjeq] at huj
                rcases hknxt with h1' | h2'
                · exact hunot (huj ▸ h1')
                · exact hune (huj ▸ h2')
              · intro hks
                subst hks
                obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd v.val) hlt_s h1
                have hjeq : j = nextOf (orEnd v.val) := huniq ⟨j, hjlt⟩ hk
                exact hueq (by rw [huj, hjeq])
            · simp only [hklt, ↓reduceIte]
    have hother_input_and : ∀ (v : Fin n) (hv : v ∉ Tbranch),
        let j := nextOf (orEnd v.val)
        ∃ (hlt : j < C.gates.length) (z : ℕ),
          ((C.gates[j]'hlt).inputs = [orEnd v.val, z] ∨ (C.gates[j]'hlt).inputs = [z, orEnd v.val]) ∧
          z < n + j ∧ z ≠ orEnd v.val ∧ z ∉ orChain v.val := by
      intro v hv
      obtain ⟨h1, hlt, hand⟩ := hand_exit v hv
      obtain ⟨_, hmem, _⟩ := hnextOf_spec (orEnd v.val) (hs_ne_out v) h1
      obtain ⟨p, q, hpq, hp, hq, hne⟩ := hgate_shape (nextOf (orEnd v.val)) hlt
      rw [hpq] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      have hnot_ch : ∀ z, z ∈ (C.gates[nextOf (orEnd v.val)]'hlt).inputs → z ∉ orChain v.val := by
        intro z hz hch
        obtain ⟨_, zlt1, z1, _⟩ := (horChain_props v.val (by omega)).2 z hch
        obtain ⟨_, _, huniq⟩ := hnextOf_spec z zlt1 z1
        have hjeq : nextOf (orEnd v.val) = nextOf z := huniq ⟨nextOf (orEnd v.val), hlt⟩ hz

        have : (C.gates[nextOf z]'(hjeq ▸ hlt)).op = GateOp.or := by
          have hzprops : ∀ w0, w0 < n + s → ∀ u ∈ orChain w0,
              ∃ hlt' : nextOf u < C.gates.length, (C.gates[nextOf u]'hlt').op = GateOp.or := by
            intro w0 hw0
            induction hrem : n + s - w0 using Nat.strong_induction_on generalizing w0 with
            | ind rem ihr =>
              intro u hu
              dsimp only [orChain] at hu; rw [orChainAux] at hu
              split_ifs at hu with h' hlt'
              · cases hop' : (C.gates[nextOf w0]'hlt').op with
                | or =>
                  rw [hop'] at hu
                  rcases Finset.mem_insert.mp hu with rfl | hu'
                  · exact ⟨hlt', hop'⟩
                  · have hgt := hnextOf_gt w0 h'.1 h'.2
                    have hns : nextOf w0 < s := by omega
                    exact ihr (n + s - (n + nextOf w0)) (by omega) (n + nextOf w0) (by omega) rfl u hu'
                | and => rw [hop'] at hu; simp at hu
                | not => rw [hop'] at hu; simp at hu
                | mod _ => rw [hop'] at hu; simp at hu
                | maj => rw [hop'] at hu; simp at hu
              · simp at hu
              · simp at hu
          obtain ⟨hlt', hor'⟩ := hzprops v.val (by omega) z hch
          exact hor'
        have hbad : (C.gates[nextOf (orEnd v.val)]'hlt).op = GateOp.or := by
          simpa [hjeq] using this
        rw [hand] at hbad; cases hbad
      rcases hmem with rfl | rfl
      · exact ⟨hlt, q, Or.inl hpq, hq, hne.symm, hnot_ch q (by rw [hpq]; simp)⟩
      · exact ⟨hlt, p, Or.inr hpq, hp, hne, hnot_ch p (by rw [hpq]; simp)⟩
    have hand_z_true : ∀ (v : Fin n) (hv : v ∉ Tbranch) (u : Fin n), G.Adj v u →
        ∀ (hlt : nextOf (orEnd v.val) < C.gates.length) (z : ℕ),
          ((C.gates[nextOf (orEnd v.val)]'hlt).inputs = [orEnd v.val, z] ∨
           (C.gates[nextOf (orEnd v.val)]'hlt).inputs = [z, orEnd v.val]) →
          z < n + nextOf (orEnd v.val) → z ≠ orEnd v.val → z ∉ orChain v.val →
          (C.wires (List.ofFn (fun t : Fin n => decide (t = u)))).getD z false = true := by
      intro v hv u hvu hlt z hord hzlt hzne hzch
      obtain ⟨h1, _, hand⟩ := hand_exit v hv
      have hvu_ne : v ≠ u := G.ne_of_adj hvu
      let x : Fin n → Bool := fun t => decide (t = u)
      let y : Fin n → Bool := Function.update x v true
      have hzeq : (C.wires (List.ofFn x)).getD z false = (C.wires (List.ofFn y)).getD z false := by
        have hrec : ∀ w < n + nextOf (orEnd v.val), w ∉ orChain v.val → w ≠ orEnd v.val →
            (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ihw =>
            intro hwlt hwch hwne
            by_cases hw1 : w < n
            · rw [wires_input C x w hw1, wires_input C y w hw1]
              have hne : (⟨w, hw1⟩ : Fin n) ≠ v := by
                intro h
                have hwv : w = v.val := congrArg Fin.val h
                subst hwv
                rcases horChain_self_or v.val (by omega) with hm | he
                · exact hwch hm
                · exact hwne he
              exact (Function.update_of_ne hne true x).symm
            · have hjlt : w - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
              set j := w - n
              have hwj : w = n + j := by omega
              have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
              congr 1
              apply List.map_congr_left
              intro k hk
              by_cases hklt : k < n + j
              · simp only [hklt, ↓reduceIte]
                apply ihw k (by omega) (by omega)
                · intro hkch
                  obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props v.val (by omega)).2 k hkch
                  obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
                  have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
                  rw [hjeq] at hwj
                  rcases hknxt with h1' | h2'
                  · exact hwch (hwj ▸ h1')
                  · exact hwne (hwj ▸ h2')
                · intro hks
                  subst hks
                  obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd v.val) (hs_ne_out v) h1
                  have hjeq : j = nextOf (orEnd v.val) := huniq ⟨j, hjlt⟩ hk
                  omega
              · simp only [hklt, ↓reduceIte]
        exact hrec z hzlt hzch hzne
      by_contra hzf
      have hz0 : (C.wires (List.ofFn x)).getD z false = false := by
        cases h : (C.wires (List.ofFn x)).getD z false
        · rfl
        · exact absurd h hzf
      have hz0' : (C.wires (List.ofFn y)).getD z false = false := hzeq.symm.trans hz0
      have hg : C.gates[nextOf (orEnd v.val)]? = some (C.gates[nextOf (orEnd v.val)]'hlt) := List.getElem?_eq_getElem hlt
      have ha0 : (C.wires (List.ofFn x)).getD (n + nextOf (orEnd v.val)) false = false := by
        rw [wires_gate_ofFn C x _ _ hg, hand]
        rcases hord with h | h <;> rw [h] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hzlt, ↓reduceIte, hz0, Bool.false_and, Bool.and_false]
      have ha0' : (C.wires (List.ofFn y)).getD (n + nextOf (orEnd v.val)) false = false := by
        rw [wires_gate_ofFn C y _ _ hg, hand]
        rcases hord with h | h <;> rw [h] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hzlt, ↓reduceIte, hz0', Bool.false_and, Bool.and_false]
      have hout_ch : C.output ∉ orChain v.val := fun hm => by
        have := (horChain_props v.val (by omega)).2 C.output hm; omega
      have hout_ne : C.output ≠ orEnd v.val := by have := hs_ne_out v; omega
      have heval := hand_sole_exit v hv x y (fun t ht => (Function.update_of_ne ht true x).symm)
        (ha0.trans ha0'.symm) C.output (by omega) hout_ch hout_ne
      change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heval
      have hf0 : C.eval (List.ofFn x) = false := by
        cases h : C.eval (List.ofFn x) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨u, u, by simp [x]⟩ ((hfun x).mp h)
          simp only [x, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf1 : C.eval (List.ofFn y) = true := by
        rw [hfun]
        apply positive
        exact ⟨v, u, hvu, by simp [y], by simp [y, x, hvu_ne.symm]⟩
      rw [hf0, hf1] at heval; exact absurd heval (by decide)
    have hvc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G Tbranch := by
      intro v w hvw
      by_contra hneither
      have hv : v ∉ Tbranch := fun h => hneither (Or.inl h)
      have hw : w ∉ Tbranch := fun h => hneither (Or.inr h)
      have hvw_ne : v ≠ w := G.ne_of_adj hvw
      have hstep_le : ∀ (a b : Fin n) (ha : a ∉ Tbranch) (hb : b ∉ Tbranch),
          G.Adj a b → nextOf (orEnd a.val) ≤ nextOf (orEnd b.val) → False := by
        intro a b ha hb hab hle
        have hab_ne : a ≠ b := G.ne_of_adj hab
        obtain ⟨hlta, za, horda, hzalt, hzane, hzach⟩ := hother_input_and a ha
        obtain ⟨h1a, _, handa⟩ := hand_exit a ha
        obtain ⟨h1b, hltb, handb⟩ := hand_exit b hb
        by_cases heq_gate : nextOf (orEnd a.val) = nextOf (orEnd b.val)
        · obtain ⟨hltb', hmemb, _⟩ := hnextOf_spec (orEnd b.val) (hs_ne_out b) h1b
          have hmemb' : orEnd b.val ∈ (C.gates[nextOf (orEnd a.val)]'hlta).inputs := by
            simpa only [heq_gate] using hmemb
          have hza_eq : za = orEnd b.val := by
            rcases horda with h | h <;> rw [h] at hmemb' <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hmemb'
            · rcases hmemb' with h' | h'
              · exact absurd (hs_inj h'.symm) hab_ne
              · exact h'.symm
            · rcases hmemb' with h' | h'
              · exact h'.symm
              · exact absurd (hs_inj h'.symm) hab_ne
          have hpos : 1 < (G.neighborFinset a).card := by have := degree a; change 2 ≤ (G.neighborFinset a).card at this; omega
          obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp hpos
          obtain ⟨u, hua, hub⟩ : ∃ u : Fin n, G.Adj a u ∧ u ≠ b := by
            by_cases h1 : u1 = b
            · exact ⟨u2, (SimpleGraph.mem_neighborFinset G a u2).mp hu2, fun h => hu12 (h1.trans h.symm)⟩
            · exact ⟨u1, (SimpleGraph.mem_neighborFinset G a u1).mp hu1, h1⟩
          have hzt := hand_z_true a ha u hua hlta za horda hzalt hzane hzach
          rw [hza_eq] at hzt
          have hz0 := hs_zero_other b u hub
          rw [hz0] at hzt; exact absurd hzt (by decide)
        · have hlt_ab : nextOf (orEnd a.val) < nextOf (orEnd b.val) := by omega
          have hzt := hand_z_true a ha b hab hlta za horda hzalt hzane hzach
          have hza_not_sb : za ≠ orEnd b.val := by
            intro h
            subst h
            obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd b.val) (hs_ne_out b) h1b
            have hmemza : orEnd b.val ∈ (C.gates[nextOf (orEnd a.val)]'hlta).inputs := by
              rcases horda with h1 | h1 <;> rw [h1] <;> simp
            exact heq_gate (huniq ⟨nextOf (orEnd a.val), hlta⟩ hmemza)
          have hza_not_chb : za ∉ orChain b.val := by
            intro hch
            obtain ⟨_, zlt1, z1, hznxt⟩ := (horChain_props b.val (by omega)).2 za hch
            obtain ⟨_, _, huniq⟩ := hnextOf_spec za zlt1 z1
            have hmemza : za ∈ (C.gates[nextOf (orEnd a.val)]'hlta).inputs := by
              rcases horda with h1 | h1 <;> rw [h1] <;> simp
            have heq : nextOf (orEnd a.val) = nextOf za := huniq ⟨nextOf (orEnd a.val), hlta⟩ hmemza
            have hgt_b := horChain_props b.val (by omega)
            have hlt_sb : n + nextOf za ≤ orEnd b.val := by
              rcases hznxt with h1' | h2'
              · exact le_of_lt (hgt_b.2 _ h1').1
              · exact le_of_eq h2'
            have hlt_a' : orEnd a.val < n + nextOf (orEnd a.val) := hnextOf_gt _ (hs_ne_out a) h1a
            have hlt_b' : orEnd b.val < n + nextOf (orEnd b.val) := hnextOf_gt _ (hs_ne_out b) h1b
            have hba_lt : nextOf (orEnd a.val) < C.gates.length := hlta
            have hnot_and : (C.gates[nextOf za]'(heq ▸ hlta)).op = GateOp.or := by
              have hzprops : ∀ w0, w0 < n + s → ∀ u ∈ orChain w0,
                  ∃ hlt' : nextOf u < C.gates.length, (C.gates[nextOf u]'hlt').op = GateOp.or := by
                intro w0 hw0
                induction hrem : n + s - w0 using Nat.strong_induction_on generalizing w0 with
                | ind rem ihr =>
                  intro u hu
                  dsimp only [orChain] at hu; rw [orChainAux] at hu
                  split_ifs at hu with h' hlt'
                  · cases hop' : (C.gates[nextOf w0]'hlt').op with
                    | or =>
                      rw [hop'] at hu
                      rcases Finset.mem_insert.mp hu with rfl | hu'
                      · exact ⟨hlt', hop'⟩
                      · have hgt := hnextOf_gt w0 h'.1 h'.2
                        have hns : nextOf w0 < s := by omega
                        exact ihr (n + s - (n + nextOf w0)) (by omega) (n + nextOf w0) (by omega) rfl u hu'
                    | and => rw [hop'] at hu; simp at hu
                    | not => rw [hop'] at hu; simp at hu
                    | mod _ => rw [hop'] at hu; simp at hu
                    | maj => rw [hop'] at hu; simp at hu
                  · simp at hu
                  · simp at hu
              obtain ⟨_, hor'⟩ := hzprops b.val (by omega) za hch
              exact hor'
            have : (C.gates[nextOf (orEnd a.val)]'hlta).op = GateOp.or := by simpa [heq] using hnot_and
            rw [handa] at this; cases this
          have hza_indep_b : ∀ u < n + nextOf (orEnd b.val), u ∉ orChain b.val → u ≠ orEnd b.val →
              (C.wires (List.ofFn (fun _ : Fin n => false))).getD u false =
              (C.wires (List.ofFn (fun t : Fin n => decide (t = b)))).getD u false := by
            intro u
            induction u using Nat.strong_induction_on with
            | ind u ihu =>
              intro hult huch hune
              by_cases hu1 : u < n
              · rw [wires_input C _ u hu1, wires_input C _ u hu1]
                have hne : (⟨u, hu1⟩ : Fin n) ≠ b := by
                  intro h
                  have hub : u = b.val := congrArg Fin.val h
                  subst hub
                  rcases horChain_self_or b.val (by omega) with hm | he
                  · exact huch hm
                  · exact hune he
                simp [hne]
              · have hjlt : u - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
                set j := u - n
                have huj : u = n + j := by omega
                have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
                rw [huj, wires_gate_ofFn C _ j _ hg, wires_gate_ofFn C _ j _ hg]
                congr 1
                apply List.map_congr_left
                intro k hk
                by_cases hklt : k < n + j
                · simp only [hklt, ↓reduceIte]
                  apply ihu k (by omega) (by omega)
                  · intro hkch
                    obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props b.val (by omega)).2 k hkch
                    obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
                    have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
                    rw [hjeq] at huj
                    rcases hknxt with h1' | h2'
                    · exact huch (huj ▸ h1')
                    · exact hune (huj ▸ h2')
                  · intro hks
                    subst hks
                    obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd b.val) (hs_ne_out b) h1b
                    have hjeq : j = nextOf (orEnd b.val) := huniq ⟨j, hjlt⟩ hk
                    omega
                · simp only [hklt, ↓reduceIte]
          have hza0 : (C.wires (List.ofFn (fun _ : Fin n => false))).getD za false = true :=
            (hza_indep_b za (by omega) hza_not_chb hza_not_sb).trans hzt
          have hza_all : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD za false = true := fun x =>
            wires_mono C hmono (fun _ => false) x (fun _ h => absurd h (by decide)) za hza0
          have ha_copy : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + nextOf (orEnd a.val)) false =
              (C.wires (List.ofFn x)).getD (orEnd a.val) false := by
            intro x
            have hg : C.gates[nextOf (orEnd a.val)]? = some (C.gates[nextOf (orEnd a.val)]'hlta) := List.getElem?_eq_getElem hlta
            have hs_lt : orEnd a.val < n + nextOf (orEnd a.val) := hnextOf_gt _ (hs_ne_out a) h1a
            rw [wires_gate_ofFn C x _ _ hg, handa]
            rcases horda with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hs_lt, hzalt, ↓reduceIte, hza_all x, Bool.true_and, Bool.and_true]
          have hja_s : nextOf (orEnd a.val) < s := by omega
          exact (hno_const_or_copy (nextOf (orEnd a.val)) hja_s).2.2 (orEnd a.val) (hnextOf_gt _ (hs_ne_out a) h1a) ha_copy
      rcases le_total (nextOf (orEnd v.val)) (nextOf (orEnd w.val)) with hle | hle
      · exact hstep_le v w hv hw hvw hle
      · exact hstep_le w v hw hv hvw.symm hle
    have ht_le_T : t ≤ Tbranch.card := ht_min Tbranch hvc
    set Simg : Finset ℕ := Tbranch.image (fun v : Fin n => orEnd v.val)
    have hSimg_sub : Simg ⊆ Finset.range (n + s - 1) := by
      intro w hw
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_range.mpr (hs_ne_out v)
    have hSimg_card : Simg.card = Tbranch.card := Finset.card_image_of_injective Tbranch hs_inj
    have hsum_ge_T : Tbranch.card ≤ ∑ w ∈ Simg, (outdeg w - 1) := by
      have hle1 : ∀ w ∈ Simg, 1 ≤ outdeg w - 1 := by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        have := (Finset.mem_filter.mp hv).2
        omega
      have := Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hSimg_card] at this
      exact this
    have hsum_le_all : ∑ w ∈ Simg, (outdeg w - 1) ≤ ∑ w ∈ Finset.range (n + s - 1), (outdeg w - 1) :=
      Finset.sum_le_sum_of_subset hSimg_sub
    have hs_eq : s = n + t - 1 := by omega
    have hT_eq : Tbranch.card = t := by omega
    have houtdeg_eq2 : ∀ w ∈ Simg, outdeg w = 2 := by
      intro w hw
      have hge2 : 2 ≤ outdeg w := by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hv).2
      by_contra hne2
      have hgt1 : 1 < outdeg w - 1 := by omega
      have hstrict : ∑ _u ∈ Simg, 1 < ∑ u ∈ Simg, (outdeg u - 1) :=
        Finset.sum_lt_sum (fun u hu => by
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
          have := (Finset.mem_filter.mp hv).2; omega) ⟨w, hw, hgt1⟩
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hSimg_card] at hstrict
      omega
    have houtdeg_eq1_outside : ∀ w < n + s - 1, w ∉ Simg → outdeg w = 1 := by
      intro w hw hwNot
      have hge1 := houtdeg_ge1 w hw
      by_contra hne1
      have hpos : 0 < outdeg w - 1 := by omega
      have hadd : (∑ u ∈ Simg, (outdeg u - 1)) + (outdeg w - 1) ≤ ∑ u ∈ Finset.range (n + s - 1), (outdeg u - 1) := by
        have hsub2 : insert w Simg ⊆ Finset.range (n + s - 1) :=
          Finset.insert_subset (Finset.mem_range.mpr hw) hSimg_sub
        have := Finset.sum_le_sum_of_subset (f := fun u => outdeg u - 1) hsub2
        rw [Finset.sum_insert hwNot] at this
        omega
      omega
    set I : Finset (Fin n) := Finset.univ \ Tbranch
    have hI_card : I.card = n - t := by
      have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Tbranch)
      change I.card + Tbranch.card = (Finset.univ : Finset (Fin n)).card at this
      simp only [Finset.card_univ, Fintype.card_fin, hT_eq] at this
      omega
    have hT_nbr_I : ∀ v ∈ Tbranch, 3 ≤ G.degree v → (G.neighborFinset v ∩ I).card ≤ 1 := by
      intro v hv hThree
      let ev : Fin n → Bool := fun t => decide (t = v)
      set Tv : Finset ℕ := (Finset.range (n + s)).filter (fun w => (C.wires (List.ofFn ev)).getD w false = true)
      have hv_in_Tv : v.val ∈ Tv := by
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [wires_input C ev v.val v.isLt]; simp [ev]
      have hsv_in_Tv : orEnd v.val ∈ Tv := by
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by have := hs_ne_out v; omega, ?_⟩
        apply horEnd_true v.val ev (by omega)
        rw [wires_input C ev v.val v.isLt]; simp [ev]
      have hout_not_Tv : n + s - 1 ∉ Tv := by
        intro hm
        have ht := (Finset.mem_filter.mp hm).2
        rw [← hout_last] at ht
        change C.eval (List.ofFn ev) = true at ht
        obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨v, v, by simp [ev]⟩ ((hfun ev).mp ht)
        simp only [ev, decide_eq_true_eq] at ha hb
        subst ha; subst hb; exact G.loopless.irrefl _ hab
      have hTv_lt : ∀ w ∈ Tv, w < n + s - 1 := by
        intro w hw
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
        have hne : w ≠ n + s - 1 := fun h => hout_not_Tv (h ▸ hw)
        omega
      have hTv_outdeg : ∀ w ∈ Tv, outdeg w = if w = orEnd v.val then 2 else 1 := by
        intro w hw
        by_cases heq : w = orEnd v.val
        · simp only [heq, ↓reduceIte]
          exact houtdeg_eq2 _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        · simp only [heq, ↓reduceIte]
          apply houtdeg_eq1_outside w (hTv_lt w hw)
          intro hS
          obtain ⟨v', _, hv'eq⟩ := Finset.mem_image.mp hS
          have hv'ne : v' ≠ v := fun h => heq (hv'eq.symm.trans (congrArg (fun x : Fin n => orEnd x.val) h))
          have h0 := hs_zero_other v' v hv'ne.symm
          have h1 := (Finset.mem_filter.mp hw).2
          rw [← hv'eq, h0] at h1
          exact absurd h1 (by decide)
      have hsum_Tv_outdeg : ∑ w ∈ Tv, outdeg w = Tv.card + 1 := by
        have hrew : ∑ w ∈ Tv, outdeg w = ∑ w ∈ Tv, (if w = orEnd v.val then 2 else 1) :=
          Finset.sum_congr rfl hTv_outdeg
        rw [hrew, ← Finset.add_sum_erase _ _ hsv_in_Tv]
        simp only [↓reduceIte]
        have hrest : ∑ w ∈ Tv.erase (orEnd v.val), (if w = orEnd v.val then 2 else 1) = (Tv.erase (orEnd v.val)).card := by
          trans ∑ _w ∈ Tv.erase (orEnd v.val), 1
          · apply Finset.sum_congr rfl
            intro w hw; simp [(Finset.mem_erase.mp hw).1]
          · simp
        rw [hrest]
        have := Finset.card_erase_add_one hsv_in_Tv
        omega
      let Ev : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∉ Tv ∧ ∃ i ∈ (C.gates[j.val]).inputs, i ∈ Tv)
      have hmem_Ev : ∀ j : Fin C.gates.length, j ∈ Ev ↔ n + j.val ∉ Tv ∧ ∃ i ∈ (C.gates[j.val]'j.isLt).inputs, i ∈ Tv := fun j => by
        simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and]
      have hEv_le2 : Ev.card ≤ 2 := by
        let din : ℕ → ℕ := fun w => (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv ∧ w ∈ (C.gates[j.val]).inputs)).card
        let dout : ℕ → ℕ := fun w => (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∉ Tv ∧ w ∈ (C.gates[j.val]).inputs)).card
        have hsplit : ∀ w, din w + dout w = outdeg w := by
          intro w
          rw [houtdeg_card]
          have := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun j : Fin C.gates.length => w ∈ (C.gates[j.val]).inputs))
            (p := fun j : Fin C.gates.length => n + j.val ∈ Tv)
          simpa only [din, dout, Finset.filter_filter, and_comm] using this
        have hdin_sum : Tv.card - 1 ≤ ∑ w ∈ Tv, din w := by
          have hswap : ∑ w ∈ Tv, din w =
              ∑ j ∈ Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv),
                (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            simp only [din, Finset.card_eq_sum_ones]
            have h1 : ∀ j : Fin C.gates.length,
                (∑ w ∈ Tv, if n + j.val ∈ Tv ∧ w ∈ (C.gates[j.val]).inputs then 1 else 0) =
                if n + j.val ∈ Tv then (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card else 0 := by
              intro j
              by_cases hj : n + j.val ∈ Tv
              · simp [hj, Finset.sum_boole]
              · simp [hj]
            trans ∑ j : Fin C.gates.length, ∑ w ∈ Tv, if n + j.val ∈ Tv ∧ w ∈ (C.gates[j.val]).inputs then 1 else 0
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro w _; simp only [Finset.sum_filter]
            · trans ∑ j : Fin C.gates.length, if n + j.val ∈ Tv then (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card else 0
              · exact Finset.sum_congr rfl (fun j _ => h1 j)
              · rw [← Finset.sum_filter]; simp only [Finset.card_eq_sum_ones]
          rw [hswap]
          have hge1 : ∀ j ∈ Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv),
              1 ≤ (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            intro j hj
            have hjTv : n + j.val ∈ Tv := (Finset.mem_filter.mp hj).2
            have hjt : (C.wires (List.ofFn ev)).getD (n + j.val) false = true := (Finset.mem_filter.mp hjTv).2
            have hg : C.gates[j.val]? = some (C.gates[j.val]'j.isLt) := List.getElem?_eq_getElem j.isLt
            obtain ⟨p, q, hpq, hp, hq, _⟩ := hgate_shape j.val j.isLt
            have hgop : (C.gates[j.val]'j.isLt).op = GateOp.and ∨ (C.gates[j.val]'j.isLt).op = GateOp.or := by
              simpa using (hmono _ (List.getElem_mem j.isLt)).1
            rw [wires_gate_ofFn C ev j.val _ hg, hpq] at hjt
            have hex : (C.wires (List.ofFn ev)).getD p false = true ∨ (C.wires (List.ofFn ev)).getD q false = true := by
              rcases hgop with hand | hor
              · rw [hand] at hjt; simp [GateOp.eval, hp, hq] at hjt; exact Or.inl hjt.1
              · rw [hor] at hjt; simp [GateOp.eval, hp, hq] at hjt; exact hjt
            have hjs : j.val < s := by have := j.isLt; omega
            rcases hex with hpt | hqt
            · exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpt⟩, by rw [hpq]; simp⟩⟩
            · exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hqt⟩, by rw [hpq]; simp⟩⟩
          have hsum_j := Finset.sum_le_sum hge1
          simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum_j
          have hcard_j : Tv.card - 1 ≤ (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv)).card := by
            have hsub_inj : (Tv.erase v.val).card ≤ (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv)).card := by
              refine Finset.card_le_card_of_injOn
                (fun w => if h : w - n < C.gates.length then ⟨w - n, h⟩ else ⟨0, by omega⟩) ?_ ?_
              · intro w hw
                have hwTv := Finset.mem_of_mem_erase hw
                have hne_v := (Finset.mem_erase.mp hw).1
                have hw_lt := hTv_lt w hwTv
                have hge_n : n ≤ w := by
                  by_contra hlt
                  have hwt := (Finset.mem_filter.mp hwTv).2
                  rw [wires_input C ev w (by omega)] at hwt
                  simp only [ev, decide_eq_true_eq] at hwt
                  exact hne_v (congrArg Fin.val hwt)
                have hsub_lt : w - n < C.gates.length := by omega
                simp only [hsub_lt, ↓reduceDIte, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
                rwa [show n + (w - n) = w by omega]
              · intro w1 hw1 w2 hw2 heq
                have h1Tv := Finset.mem_of_mem_erase hw1
                have h2Tv := Finset.mem_of_mem_erase hw2
                have hw1_lt := hTv_lt w1 h1Tv
                have hw2_lt := hTv_lt w2 h2Tv
                have hge1 : n ≤ w1 := by
                  by_contra hlt
                  have hwt := (Finset.mem_filter.mp h1Tv).2
                  rw [wires_input C ev w1 (by omega)] at hwt
                  simp only [ev, decide_eq_true_eq] at hwt
                  exact (Finset.mem_erase.mp hw1).1 (congrArg Fin.val hwt)
                have hge2 : n ≤ w2 := by
                  by_contra hlt
                  have hwt := (Finset.mem_filter.mp h2Tv).2
                  rw [wires_input C ev w2 (by omega)] at hwt
                  simp only [ev, decide_eq_true_eq] at hwt
                  exact (Finset.mem_erase.mp hw2).1 (congrArg Fin.val hwt)
                have hlt1 : w1 - n < C.gates.length := by omega
                have hlt2 : w2 - n < C.gates.length := by omega
                simp only [hlt1, hlt2, ↓reduceDIte] at heq
                have hv_eq : w1 - n = w2 - n := congrArg Fin.val heq
                omega
            have := Finset.card_erase_add_one hv_in_Tv
            omega
          omega
        have hdout_ge : Ev.card ≤ ∑ w ∈ Tv, dout w := by
          have hswap : ∑ w ∈ Tv, dout w =
              ∑ j ∈ Ev, (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            trans ∑ j : Fin C.gates.length, ∑ w ∈ Tv, if n + j.val ∉ Tv ∧ w ∈ (C.gates[j.val]).inputs then 1 else 0
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro w _; simp [dout]
            · rw [← Finset.sum_subset (Finset.subset_univ Ev)]
              · apply Finset.sum_congr rfl
                intro j hj
                have hjnot : n + j.val ∉ Tv := ((hmem_Ev j).mp hj).1
                simp [hjnot, Finset.sum_boole]
              · intro j _ hjnot
                simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_exists] at hjnot
                by_cases hntv : n + j.val ∉ Tv
                · apply Finset.sum_eq_zero
                  intro w hw
                  have : w ∉ (C.gates[j.val]).inputs := fun hm => hjnot hntv w hm hw
                  simp [hntv, this]
                · simp [hntv]
          rw [hswap]
          have hge1 : ∀ j ∈ Ev, 1 ≤ (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            intro j hj
            obtain ⟨i, hi_mem, hi_Tv⟩ := ((hmem_Ev j).mp hj).2
            exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi_Tv, hi_mem⟩⟩
          have := Finset.sum_le_sum hge1
          simpa using this
        have htot : (∑ w ∈ Tv, din w) + (∑ w ∈ Tv, dout w) = ∑ w ∈ Tv, outdeg w := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun w _ => hsplit w)
        have hTv_pos : 1 ≤ Tv.card := Finset.card_pos.mpr ⟨v.val, hv_in_Tv⟩
        omega
      have hu_maps_Ev : ∀ u ∈ G.neighborFinset v ∩ I,
          ∃ hlt : nextOf (orEnd u.val) < C.gates.length, (⟨nextOf (orEnd u.val), hlt⟩ : Fin C.gates.length) ∈ Ev := by
        intro u hu
        have hvu : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp (Finset.mem_inter.mp hu).1
        have huNotT : u ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu).2).2
        obtain ⟨hlt, z, hord, hzlt, hzne, hzch⟩ := hother_input_and u huNotT
        obtain ⟨_, _, handu⟩ := hand_exit u huNotT
        have hzt : (C.wires (List.ofFn ev)).getD z false = true :=
          hand_z_true u huNotT v hvu.symm hlt z hord hzlt hzne hzch
        have hsu0 : (C.wires (List.ofFn ev)).getD (orEnd u.val) false = false :=
          hs_zero_other u v (G.ne_of_adj hvu)
        have ha0 : (C.wires (List.ofFn ev)).getD (n + nextOf (orEnd u.val)) false = false := by
          have hg : C.gates[nextOf (orEnd u.val)]? = some (C.gates[nextOf (orEnd u.val)]'hlt) := List.getElem?_eq_getElem hlt
          have h1u := (hand_exit u huNotT).1
          have hsult : orEnd u.val < n + nextOf (orEnd u.val) := hnextOf_gt _ (hs_ne_out u) h1u
          rw [wires_gate_ofFn C ev _ _ hg, handu]
          rcases hord with h | h <;> rw [h] <;>
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hsult, ↓reduceIte, hsu0, Bool.false_and, Bool.and_false]
        refine ⟨hlt, (hmem_Ev ⟨nextOf (orEnd u.val), hlt⟩).mpr ⟨?_, z, ?_, ?_⟩⟩
        · intro hm
          have h1 := (Finset.mem_filter.mp hm).2
          rw [ha0] at h1; exact absurd h1 (by decide)
        · rcases hord with h | h <;> rw [h] <;> simp
        · have hj_s : nextOf (orEnd u.val) < s := by omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hzt⟩
      have hu_inj : ∀ u1 ∈ G.neighborFinset v ∩ I, ∀ u2 ∈ G.neighborFinset v ∩ I,
          nextOf (orEnd u1.val) = nextOf (orEnd u2.val) → u1 = u2 := by
        intro u1 hu1 u2 hu2 heq
        have hvu1 : G.Adj v u1 := (SimpleGraph.mem_neighborFinset G v u1).mp (Finset.mem_inter.mp hu1).1
        have hvu2 : G.Adj v u2 := (SimpleGraph.mem_neighborFinset G v u2).mp (Finset.mem_inter.mp hu2).1
        have hu1NotT : u1 ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu1).2).2
        have hu2NotT : u2 ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu2).2).2
        obtain ⟨hlt1, z1, hord1, hz1lt, hz1ne, hz1ch⟩ := hother_input_and u1 hu1NotT
        have hz1t : (C.wires (List.ofFn ev)).getD z1 false = true :=
          hand_z_true u1 hu1NotT v hvu1.symm hlt1 z1 hord1 hz1lt hz1ne hz1ch
        have hsu20 : (C.wires (List.ofFn ev)).getD (orEnd u2.val) false = false :=
          hs_zero_other u2 v (G.ne_of_adj hvu2)
        have h1u2 := (hand_exit u2 hu2NotT).1
        obtain ⟨_, hm2, _⟩ := hnextOf_spec (orEnd u2.val) (hs_ne_out u2) h1u2
        have hm2' : orEnd u2.val ∈ (C.gates[nextOf (orEnd u1.val)]'hlt1).inputs := by
          simpa only [heq] using hm2
        rcases hord1 with h | h <;> rw [h] at hm2' <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2'
        · rcases hm2' with h' | h'
          · exact hs_inj h'.symm
          · rw [h', hz1t] at hsu20; exact absurd hsu20 (by decide)
        · rcases hm2' with h' | h'
          · rw [h', hz1t] at hsu20; exact absurd hsu20 (by decide)
          · exact hs_inj h'.symm
      have hcard_le2 : (G.neighborFinset v ∩ I).card ≤ 2 := by
        have hle := Finset.card_le_card_of_injOn
          (s := G.neighborFinset v ∩ I) (t := Ev)
          (fun u => if h : nextOf (orEnd u.val) < C.gates.length then ⟨nextOf (orEnd u.val), h⟩ else ⟨0, by omega⟩)
          (fun u hu => by
            obtain ⟨hlt, hmem⟩ := hu_maps_Ev u hu
            simp only [hlt, ↓reduceDIte, Finset.mem_coe]
            exact hmem)
          (fun u1 hu1 u2 hu2 heq => by
            have hlt1 := (hu_maps_Ev u1 hu1).1
            have hlt2 := (hu_maps_Ev u2 hu2).1
            simp only [hlt1, hlt2, ↓reduceDIte] at heq
            exact hu_inj u1 hu1 u2 hu2 (congrArg Fin.val heq))
        omega
      by_contra hgt1
      have hcard_eq2 : (G.neighborFinset v ∩ I).card = 2 := by omega
      rw [Finset.card_eq_two] at hcard_eq2
      obtain ⟨u1, u2, hu12, hN_I⟩ := hcard_eq2
      have hu1_in : u1 ∈ G.neighborFinset v ∩ I := hN_I ▸ by simp
      have hu2_in : u2 ∈ G.neighborFinset v ∩ I := hN_I ▸ by simp
      obtain ⟨hlt1, hEv1⟩ := hu_maps_Ev u1 hu1_in
      obtain ⟨hlt2, hEv2⟩ := hu_maps_Ev u2 hu2_in
      have hEv_ne : (⟨nextOf (orEnd u1.val), hlt1⟩ : Fin C.gates.length) ≠ ⟨nextOf (orEnd u2.val), hlt2⟩ :=
        fun h => hu12 (hu_inj u1 hu1_in u2 hu2_in (congrArg Fin.val h))
      have hEv_eq : Ev = {⟨nextOf (orEnd u1.val), hlt1⟩, ⟨nextOf (orEnd u2.val), hlt2⟩} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · rw [Finset.card_pair hEv_ne]; exact hEv_le2
      have hdegv : 3 ≤ (G.neighborFinset v).card := hThree
      have hdiff_pos : 0 < (G.neighborFinset v \ (G.neighborFinset v ∩ I)).card := by
        have h1 := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁ := G.neighborFinset v) (s₂ := I))
        have h2 : (G.neighborFinset v ∩ I).card = 2 := by rw [hN_I, Finset.card_pair hu12]
        omega
      obtain ⟨v', hv'⟩ := Finset.card_pos.mp hdiff_pos
      have hvv' : G.Adj v v' := (SimpleGraph.mem_neighborFinset G v v').mp (Finset.mem_sdiff.mp hv').1
      have hv'not : v' ∉ G.neighborFinset v ∩ I := (Finset.mem_sdiff.mp hv').2
      have hv'ne1 : v' ≠ u1 := fun h => hv'not (h ▸ hu1_in)
      have hv'ne2 : v' ≠ u2 := fun h => hv'not (h ▸ hu2_in)
      have hvv'_ne : v ≠ v' := G.ne_of_adj hvv'
      let x0 : Fin n → Bool := fun t => decide (t = v')
      let x1 : Fin n → Bool := Function.update x0 v true
      have hnot_Tv_eq : ∀ w < n + s, w ∉ Tv →
          (C.wires (List.ofFn x0)).getD w false = (C.wires (List.ofFn x1)).getD w false := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ihw =>
          intro hwlt hwNot
          by_cases hw1 : w < n
          · rw [wires_input C x0 w hw1, wires_input C x1 w hw1]
            have hne : (⟨w, hw1⟩ : Fin n) ≠ v := by
              intro h
              have hwv : w = v.val := congrArg Fin.val h
              exact hwNot (hwv ▸ hv_in_Tv)
            exact (Function.update_of_ne hne true x0).symm
          · have hjlt : w - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
            set j := w - n
            have hwj : w = n + j := by omega
            by_cases hjEv : (⟨j, hjlt⟩ : Fin C.gates.length) ∈ Ev
            · rw [hEv_eq, Finset.mem_insert, Finset.mem_singleton] at hjEv
              have hand_zero : ∀ (uk : Fin n), uk ∈ G.neighborFinset v ∩ I → v' ≠ uk →
                  j = nextOf (orEnd uk.val) →
                  (C.wires (List.ofFn x0)).getD w false = (C.wires (List.ofFn x1)).getD w false := by
                intro uk huk hv'uk hjeq
                have huk_notT : uk ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp huk).2).2
                have hvuk : G.Adj v uk := (SimpleGraph.mem_neighborFinset G v uk).mp (Finset.mem_inter.mp huk).1
                obtain ⟨h1uk, _, handuk⟩ := hand_exit uk huk_notT
                obtain ⟨_, hmem_su, _⟩ := hnextOf_spec (orEnd uk.val) (hs_ne_out uk) h1uk
                have hsu_lt : orEnd uk.val < n + j := by rw [hjeq]; exact hnextOf_gt _ (hs_ne_out uk) h1uk
                have hsu_not_Tv : orEnd uk.val ∉ Tv := by
                  intro hm
                  have h1 := (Finset.mem_filter.mp hm).2
                  have h0 := hs_zero_other uk v (G.ne_of_adj hvuk)
                  rw [h0] at h1; exact absurd h1 (by decide)
                have hsu_eq := ihw (orEnd uk.val) (by omega) (by omega) hsu_not_Tv
                have hsu_x0 : (C.wires (List.ofFn x0)).getD (orEnd uk.val) false = false :=
                  hs_zero_other uk v' hv'uk
                have hsu_x1 : (C.wires (List.ofFn x1)).getD (orEnd uk.val) false = false :=
                  hsu_eq.symm.trans hsu_x0
                have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
                have hgop : (C.gates[j]'hjlt).op = GateOp.and := by
                  simpa only [hjeq] using handuk
                have hmem_su' : orEnd uk.val ∈ (C.gates[j]'hjlt).inputs := by
                  simpa only [hjeq] using hmem_su
                have hf_and : ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD (orEnd uk.val) false = false →
                    (C.wires (List.ofFn y)).getD w false = false := by
                  intro y hy0
                  rw [hwj, wires_gate_ofFn C y j _ hg, hgop]
                  change ((C.gates[j]'hjlt).inputs.map fun i => if i < n + j then (C.wires (List.ofFn y)).getD i false else false).all id = false
                  cases hv_all : ((C.gates[j]'hjlt).inputs.map fun i => if i < n + j then (C.wires (List.ofFn y)).getD i false else false).all id with
                  | false => rfl
                  | true =>
                    have ht := List.all_eq_true.mp hv_all _ (List.mem_map_of_mem hmem_su')
                    simp only [id_eq, hsu_lt, ↓reduceIte, hy0] at ht
                    exact absurd ht (by decide)
                exact (hf_and x0 hsu_x0).trans (hf_and x1 hsu_x1).symm
              rcases hjEv with h1 | h2
              · exact hand_zero u1 hu1_in hv'ne1 (congrArg Fin.val h1)
              · exact hand_zero u2 hu2_in hv'ne2 (congrArg Fin.val h2)
            · have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hwj, wires_gate_ofFn C x0 j _ hg, wires_gate_ofFn C x1 j _ hg]
              congr 1
              apply List.map_congr_left
              intro i hi
              by_cases hilt : i < n + j
              · simp only [hilt, ↓reduceIte]
                have hiNot : i ∉ Tv := fun hiTv => hjEv ((hmem_Ev ⟨j, hjlt⟩).mpr ⟨hwj ▸ hwNot, i, hi, hiTv⟩)
                exact ihw i (by omega) (by omega) hiNot
              · simp only [hilt, ↓reduceIte]
      have heval := hnot_Tv_eq C.output (by omega) (hout_last ▸ hout_not_Tv)
      change C.eval (List.ofFn x0) = C.eval (List.ofFn x1) at heval
      have hf0 : C.eval (List.ofFn x0) = false := by
        cases h : C.eval (List.ofFn x0) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨v', v', by simp [x0]⟩ ((hfun x0).mp h)
          simp only [x0, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf1 : C.eval (List.ofFn x1) = true := by
        rw [hfun]
        apply positive
        exact ⟨v, v', hvv', by simp [x1], by simp [x1, x0, hvv'_ne.symm]⟩
      rw [hf0, hf1] at heval; exact absurd heval (by decide)
    obtain ⟨v, hv, deg, many⟩ := coverWitness Tbranch hvc hT_eq
    have few := hT_nbr_I v hv deg
    change 2 ≤ (G.neighborFinset v ∩ I).card at many
    omega

end SparseBranchBound

-- Monotone wire evaluation is taken from the checked proof of L-meta-1716.
namespace PartialPetersenMonotone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem eval_mono_fn {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (o : ℕ)
    (h : Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  refine mono gates _ _ (by simp) hg ?_ o h
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · exact hxy _
  · exact id


def dest (N i : ℕ) := if i < 9 then i else if i = 9 then 9+N else i-1
def mapGate (N : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (dest N)⟩
def project (C : Circuit) : Circuit := ⟨C.gates.map (mapGate C.size),dest C.size C.output⟩

lemma align {N : ℕ} (A t : List Bool) (hA : A.length = 9) (ht : t.length ≤ N) (i : ℕ) :
    ((A++[false])++t).getD i false = (A++t).getD (dest N i) false := by
  by_cases low : i < 9
  · rw [List.getD_append _ _ _ _ (by simp [hA]; omega),List.getD_append _ _ _ _ (by omega)]
    simp only [dest,low,↓reduceIte]
    rw [List.getD_append _ _ _ _ (by omega)]
  · by_cases eq : i = 9
    · subst i
      have h : ((A++[false])++t).getD 9 false = false := by
        rw [List.getD_append _ _ _ _ (by simp [hA]),List.getD_append_right _ _ _ _ (by omega),hA]
        rfl
      rw [h,List.getD_eq_default _ _ (by simp [dest,hA]; omega)]
    · simp only [dest,low,eq,↓reduceIte]
      rw [List.getD_append_right _ _ _ _ (by simp [hA]; omega),
        List.getD_append_right _ _ _ _ (by omega)]
      have h : i-1-A.length = i-(A++[false]).length := by simp [hA]; omega
      rw [h]

lemma sim {N : ℕ} (gs : List Gate) (A : List Bool) (hA : A.length=9) (t : List Bool)
    (hn : t.length+gs.length ≤ N) :
    ∃ T, T.length ≤ N ∧ gs.foldl stp ((A++[false])++t) = (A++[false])++T ∧
      (gs.map (mapGate N)).foldl stp (A++t) = A++T := by
  induction gs generalizing t with
  | nil => exact ⟨t,by simpa using hn,rfl,rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => ((A++[false])++t).getD i false)
    have same : (mapGate N g).op.eval ((mapGate N g).inputs.map (fun i => (A++t).getD i false)) = v := by
      unfold v mapGate
      rw [List.map_map]
      apply congrArg
      apply List.map_congr_left
      intro i _
      exact (align A t hA (by simpa using (show t.length ≤ N by simp at hn; omega)) i).symm
    obtain ⟨T,hlen,hx,hy⟩ := ih (t++[v]) (by simp at hn ⊢; omega)
    refine ⟨T,hlen,?_,?_⟩
    · simpa only [List.foldl_cons,stp,v,List.append_assoc] using hx
    · simpa only [List.map_cons,List.foldl_cons,stp,same,List.append_assoc] using hy

theorem sameEval (C : Circuit) (x : Fin 9 → Bool) :
    C.eval (List.ofFn x ++ [false]) = (project C).eval (List.ofFn x) := by
  let A := List.ofFn x
  obtain ⟨T,hT,hx,hy⟩ := sim (N:=C.size) C.gates A (by simp [A]) [] (by simp [Circuit.size])
  have hx' : C.gates.foldl stp (A++[false]) = (A++[false])++T := by simpa only [List.append_nil] using hx
  have hy' : (C.gates.map (mapGate C.size)).foldl stp A = A++T := by simpa only [List.append_nil] using hy
  change (C.gates.foldl stp (A++[false])).getD C.output false =
    ((C.gates.map (mapGate C.size)).foldl stp A).getD (dest C.size C.output) false
  rw [hx',hy']
  exact align _ _ (by simp [A]) hT _

theorem sameSize (C : Circuit) : (project C).size = C.size := by simp [project,Circuit.size]

theorem staysMonotone (C : Circuit) (h : Monotone2 C) : Monotone2 (project C) := by
  intro g hg
  obtain ⟨k,km,rfl⟩ := List.mem_map.mp hg
  simpa [mapGate] using h k km

abbrev V := Fin 9
abbrev Input := V → Bool
def target (x : Input) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
  x 6 && x 8 || x 8 && x 5

def edgeList (b : Bool) : List (V × V) :=
  (if b then [(0,1)] else []) ++
  [(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def graph (b : Bool) := SimpleGraph.fromRel (fun i j : V => (i,j) ∈ edgeList b)
instance (b : Bool) : DecidableRel (graph b).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ((i,j) ∈ edgeList b ∨ (j,i) ∈ edgeList b)))
def pair (u v : V) (i : V) := decide (i=u ∨ i=v)
def selected (C : Circuit) := C.eval (List.ofFn (pair 0 1))

set_option maxHeartbeats 2000000 in
theorem geomDeg : ∀ b v, 2 ≤ (graph b).degree v := by decide +kernel
set_option maxHeartbeats 2000000 in
theorem geomSep : ∀ b v w, v ≠ w → ∃ u, (graph b).Adj v u ∧ ¬(graph b).Adj w u := by decide +kernel
set_option maxHeartbeats 2000000 in
theorem geomNoFour : ∀ k (a b c d : V), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (graph k).Adj a b → (graph k).Adj b c → (graph k).Adj c d → ¬(graph k).Adj d a := by decide +kernel

instance decCover (b : Bool) (s : Finset V) : Decidable (IsVertexCover (graph b) s) := by
  unfold IsVertexCover
  infer_instance

theorem geomEx : ∀ b, ∃ S : Finset V, IsVertexCover (graph b) S ∧ S.card = 5 := by
  intro b
  refine ⟨{0,1,3,7,8},?_⟩
  cases b <;> decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem geomMin : ∀ b (S : Finset V), IsVertexCover (graph b) S → 5 ≤ S.card := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem geomBoundary : ∀ b (S : Finset V), IsVertexCover (graph b) S → S.card = 5 →
    ∃ v ∈ S, 3 ≤ (graph b).degree v ∧ 2 ≤ ((graph b).neighborFinset v ∩ (Finset.univ \ S)).card := by decide +kernel


set_option maxHeartbeats 500000 in
theorem edgeClass : ∀ k u v, (graph k).Adj u v →
    (((pair u v 0 && pair u v 1) = false ∧ target (pair u v) = true) ∨
      (pair u v = pair 0 1 ∧ k = true)) := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
theorem ordinaryEdges : ∀ (k : Bool) (x : Input), (x 0 && x 1) = false → target x = true →
    ∃ u v, (graph k).Adj u v ∧ x u = true ∧ x v = true := by decide +kernel

theorem sparse01 (x : Input) (sparse : ∃ a b : V, ∀ i, x i = true → i=a ∨ i=b)
    (both : (x 0 && x 1) = true) : x = pair 0 1 := by
  obtain ⟨a,b,hab⟩ := sparse
  obtain ⟨h0,h1⟩ := Bool.and_eq_true_iff.mp both
  have onlyTwo (i : V) : (0=a ∨ 0=b) → (1=a ∨ 1=b) → (i=a ∨ i=b) → i=0 ∨ i=1 := by
    exact (by decide +kernel : ∀ (a b i : V), (0=a ∨ 0=b) → (1=a ∨ 1=b) → (i=a ∨ i=b) → i=0 ∨ i=1) a b i
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [pair,decide_eq_true_eq]
  exact ⟨fun hi => onlyTwo i (hab 0 h0) (hab 1 h1) (hab i hi), fun e => e.elim (fun h => h ▸ h0) (fun h => h ▸ h1)⟩

def agreesD (D : Circuit) := ∀ x : Input, (x 0 && x 1) = false → D.eval (List.ofFn x) = target x

theorem positive (D : Circuit) (monoD : Monotone2 D) (correct : agreesD D) (x : Input) :
    (∃ u v, (graph (selected D)).Adj u v ∧ x u = true ∧ x v = true) →
    D.eval (List.ofFn x) = true := by
  rintro ⟨u,v,edge,hu,hv⟩
  have eq : D.eval (List.ofFn (pair u v)) = true := by
    rcases edgeClass _ _ _ edge with ⟨allowed,hit⟩|⟨same,yes⟩
    · exact (correct _ allowed).trans hit
    · rw [same]
      exact yes
  apply eval_mono_fn D.gates (fun g hg => (monoD g hg).1) (pair u v) x _ D.output eq
  intro i hi
  rcases (of_decide_eq_true hi : i=u ∨ i=v) with rfl|rfl
  · exact hu
  · exact hv

theorem negative (D : Circuit) (correct : agreesD D) (x : Input)
    (sparse : ∃ a b : V, ∀ i, x i = true → i=a ∨ i=b) (hit : D.eval (List.ofFn x) = true) :
    ∃ u v, (graph (selected D)).Adj u v ∧ x u = true ∧ x v = true := by
  cases both : x 0 && x 1 with
  | false => exact ordinaryEdges _ x both ((correct x both).symm.trans hit)
  | true =>
    have eq := sparse01 x sparse both
    have chosen : selected D = true := by simpa only [eq,selected] using hit
    exact ⟨0,1,(by rw [chosen]; decide), (Bool.and_eq_true_iff.mp both).1,
      (Bool.and_eq_true_iff.mp both).2⟩

end PartialPetersenMonotone
namespace PartialPetersenMonotone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem monotoneLower (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 9 → Bool, (x 0 && x 1) = false →
      C.eval (List.ofFn x ++ [false]) = target x) : 14 ≤ C.size := by
  let D := project C
  have hD : Monotone2 D := staysMonotone C mono
  have ok : agreesD D := fun x hx => (sameEval C x).symm.trans (correct x hx)
  have bound := SparseBranchBound.main_bound 9 5 (graph (selected D)) (geomDeg _)
    (geomSep _) (geomBoundary _) (fun x => D.eval (List.ofFn x) = true)
    (positive D hD ok) (negative D ok) (geomMin _) D.size D rfl hD (fun _ => Iff.rfl)
  simpa only [D,sameSize] using bound
end PartialPetersenMonotone

namespace SignedDirectCancel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def relabel (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map ρ⟩

lemma sim (ρ : ℕ → ℕ) (gs : List Gate) (A B u : List Bool)
    (matchInput : ∀ g ∈ gs, ∀ v : List Bool, ∀ i ∈ g.inputs,
      (A++v).getD i false = (B++v).getD (ρ i) false) :
    ∃ T, gs.foldl step (A++u) = A++T ∧
      (gs.map (relabel ρ)).foldl step (B++u) = B++T := by
  induction gs generalizing u with
  | nil => exact ⟨u,rfl,rfl⟩
  | cons g gs ih =>
    let val := g.op.eval (g.inputs.map fun i => (A++u).getD i false)
    have sg : (relabel ρ g).op.eval ((relabel ρ g).inputs.map fun i => (B++u).getD i false) = val := by
      unfold relabel val
      rw [List.map_map]
      apply congrArg
      exact List.map_congr_left (fun i hi => (matchInput g List.mem_cons_self u i hi).symm)
    obtain ⟨T,ha,hb⟩ := ih (u++[val]) (fun g' h => matchInput g' (List.mem_cons_of_mem _ h))
    refine ⟨T,?_,?_⟩
    · simpa only [List.foldl_cons,step,val,List.append_assoc] using ha
    · simpa only [List.map_cons,List.foldl_cons,step,sg,List.append_assoc] using hb

def splice (cut i : ℕ) := if i = cut then 0 else if i < cut then i else i-1

lemma relate (a : Bool) (ys v : List Bool) (i : ℕ) (nz : i ≠ 0) :
  ((((!a)::ys)++[a])++v).getD i false =
    ((a::ys)++v).getD (splice (ys.length+1) i) false := by
  by_cases eq : i = ys.length+1
  · subst i
    simp [splice,List.append_assoc,List.getD_eq_getElem?_getD]
  by_cases lt : i < ys.length+1
  · simp only [splice,eq,lt,↓reduceIte,List.append_assoc,List.cons_append]
    cases i with
    | zero => contradiction
    | succ i =>
      simp only [List.getD_cons_succ]
      have hi : i < ys.length := by omega
      rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ hi]
  · simp only [splice,eq,lt,↓reduceIte]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1
    simp
    omega

def after (pre post : List Gate) (out : ℕ) : Circuit :=
  let ρ := splice (9+pre.length)
  ⟨pre ++ post.map (relabel ρ), ρ out⟩

lemma stepsLength (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,step]; omega

theorem cancel (pre post : List Gate) (rest : List ℕ) (o : ℕ)
    (unused : ∀ g ∈ pre++post, 0 ∉ g.inputs) (no : o ≠ 0)
    (a : Bool) (ys : List Bool) (hys : ys.length = 8) :
    Circuit.eval ⟨pre++⟨.not,0::rest⟩::post,o⟩ ((!a)::ys) =
      (after pre post o).eval (a::ys) := by
  obtain ⟨u,hu,hv⟩ := sim id pre ((!a)::ys) (a::ys) [] (by
    intro g hg v i hi
    have h := unused g (List.mem_append_left _ hg)
    cases i with
    | zero => exact False.elim (h hi)
    | succ i => rfl)
  have old : pre.foldl step ((!a)::ys) = (!a)::(ys++u) := by simpa using hu
  have hmap : relabel id = id := by funext g; cases g; simp [relabel]
  have new : pre.foldl step (a::ys) = a::(ys++u) := by simpa [hmap] using hv
  have len := congrArg List.length old
  rw [stepsLength] at len
  simp at len
  let ρ := splice (9+pre.length)
  have align (v : List Bool) (i : Nat) (hi : i ≠ 0) :
      ((((!a)::(ys++u))++[a])++v).getD i false =
        ((a::(ys++u))++v).getD (ρ i) false := by
    have he : (ys++u).length+1 = 9+pre.length := by simp; omega
    unfold ρ
    rw [← he]
    exact relate a (ys++u) v i hi
  obtain ⟨T,hw,hz⟩ := sim ρ post (((!a)::(ys++u))++[a]) (a::(ys++u)) [] (by
    intro g hg v i hi
    exact align v i (fun eq => unused g (List.mem_append_right _ hg) (eq ▸ hi)))
  change ((pre++⟨.not,0::rest⟩::post).foldl step ((!a)::ys)).getD o false =
    ((pre++post.map (relabel ρ)).foldl step (a::ys)).getD (ρ o) false
  rw [List.foldl_append,List.foldl_cons,List.foldl_append,old,new]
  have hg : step ((!a)::(ys++u)) ⟨.not,0::rest⟩ = ((!a)::(ys++u))++[a] := by
    simp [step,GateOp.eval]
  rw [hg]
  simp only [List.append_nil] at hw hz
  rw [hw,hz]
  exact align T _ no

theorem sizeAfter (pre post : List Gate) (o : ℕ) :
    (after pre post o).size = pre.length+post.length := by simp [after,Circuit.size]

theorem monoAfter (pre post : List Gate) (o : ℕ)
    (mono : ∀ g ∈ pre++post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Monotone2 (after pre post o) := by
  intro g hg
  rcases List.mem_append.mp hg with hp|hq
  · exact mono g (List.mem_append_left _ hp)
  · obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hq
    simpa [relabel] using mono g' (List.mem_append_right _ hg')

end SignedDirectCancel
namespace SignedDirectCancel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PartialPetersenMonotone

lemma zeroSaved (gs : List Gate) (w : List Bool) (h : 0 < w.length) :
    (gs.foldl step w).getD 0 false = w.getD 0 false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step])]
    exact List.getD_append _ _ _ _ h

theorem directReaderImpossible (pre post : List Gate) (rest : List ℕ) (o : ℕ)
    (unused : ∀ g ∈ pre++post, 0 ∉ g.inputs)
    (mono : ∀ g ∈ pre++post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (small : pre.length+post.length ≤ 13)
    (correct : ∀ x : Fin 9 → Bool, circuitFun 9 ⟨pre ++ ⟨.not,0::rest⟩ :: post,o⟩
      (fun i => if i=0 then !(x 0) else x i) = target x) : False := by
  let D := after pre post o
  have mo : Monotone2 D := monoAfter pre post o mono
  have no : o ≠ 0 := by
    intro ho
    have h := correct (fun _ => false)
    change ((pre ++ ⟨.not,0::rest⟩ :: post).foldl step
      (List.ofFn (fun i : Fin 9 => if i=0 then true else false))).getD o false = false at h
    rw [ho,zeroSaved _ _ (by simp),List.ofFn_succ] at h
    contradiction
  have ok : agreesD D := by
    intro x _
    let ys : List Bool := List.ofFn (fun i : Fin 8 => x i.succ)
    have hp : List.ofFn x = x 0 :: ys := List.ofFn_succ
    have hn : List.ofFn (fun i : Fin 9 => if i=0 then !(x 0) else x i) = (!(x 0)) :: ys := by
      rw [List.ofFn_succ]
      simp [ys]
    have hc := correct x
    change Circuit.eval ⟨pre++⟨.not,0::rest⟩::post,o⟩
      (List.ofFn (fun i : Fin 9 => if i=0 then !(x 0) else x i)) = target x at hc
    rw [hn,cancel pre post rest o unused no _ _ (by simp [ys])] at hc
    simpa only [D,hp] using hc
  have hbound := SparseBranchBound.main_bound 9 5 (graph (selected D)) (geomDeg _)
    (geomSep _) (geomBoundary _) (fun x => D.eval (List.ofFn x) = true)
    (positive D mo ok) (negative D ok) (geomMin _) D.size D rfl mo (fun _ => Iff.rfl)
  have hlen : D.size = pre.length+post.length := sizeAfter _ _ _
  omega

end SignedDirectCancel

namespace NegativePivotCut

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl


abbrev Y := Fin 8 → Bool
def edge (a : Bool) (y : Y) :=
  (a && y 0) || (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && a) ||
  (a && y 4) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) ||
  (y 4 && y 6) || (y 5 && y 7) || (y 7 && y 4)
def pivotal (y : Y) : Prop := edge false y = false ∧ edge true y = true
def blocked (i : Fin 8) := decide (i=2 ∨ i=5 ∨ i=6)
def below (x y : Y) : Prop := ∀ i, x i = true → y i = true
instance (x y : Y) : Decidable (below x y) := by unfold below; infer_instance
instance (x : Y) : Decidable (pivotal x) := by unfold pivotal; infer_instance

def mask (n : Nat) (i : Fin 8) := n.testBit i.val
def pivots := [1,5,8,9,10,16,17,18,20,21,24,25,26,40,42,48,50,52,56,58,65,69,72,73,104,129,136,137,138,193,200,201]

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
theorem downClosure : ∀ y : Y, edge false y = false → y ≠ blocked →
    ∃ k ∈ pivots, below y (mask k) ∧ pivotal (mask k) := by decide +kernel

def grow (g : Gate) := g.op = GateOp.and ∨ g.op = GateOp.or
def takeWire (ws : List Bool) (pins : List ℕ) := (pins.map fun i => ws.getD i false).headD false
def seed (a : Bool) (y : Y) := List.ofFn (Fin.cons a y)
def operand (pre : List Gate) (pins : List ℕ) (a : Bool) (y : Y) :=
  takeWire (pre.foldl stp (seed a y)) pins

def evalAfter (pre post : List Gate) (pins : List ℕ) (o : ℕ) (a : Bool) (y : Y) :=
  Circuit.eval ⟨pre ++ ⟨.not,pins⟩ :: post,o⟩ (seed a y)

theorem seedOrder {a b : Bool} {x y : Y} (ab : a=true → b=true) (xy : below x y) :
    ∀ i, (seed a x).getD i false = true → (seed b y).getD i false = true := by
  intro i
  simp only [seed,ofFn_getD]
  split
  · rename_i h
    let q : Fin 9 := ⟨i,h⟩
    change (Fin.cons (α := fun _ => Bool) a x q) = true → (Fin.cons (α := fun _ => Bool) b y q) = true
    exact Fin.cases ab (fun j => xy j) q
  · exact id

theorem operandMono (pre : List Gate) (ok : ∀ g ∈ pre, grow g) (pins : List ℕ)
    {a b : Bool} {x y : Y} (ab : a=true → b=true) (xy : below x y) :
    operand pre pins a x = true → operand pre pins b y = true := by
  have w := mono pre (seed a x) (seed b y) (by simp [seed]) ok (seedOrder ab xy)
  cases pins with
  | nil => exact id
  | cons i is => exact w i

theorem prefixLength (gs : List Gate) (ws : List Bool) :
    (gs.foldl stp ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,stp]; omega

theorem cutMustFlip (pre post : List Gate) (pins : List ℕ) (o : ℕ)
    (preOK : ∀ g ∈ pre, grow g) (postOK : ∀ g ∈ post, grow g) (y : Y)
    (high : evalAfter pre post pins o false y = true)
    (low : evalAfter pre post pins o true y = false) :
    operand pre pins false y = false ∧ operand pre pins true y = true := by
  let A := pre.foldl stp (seed false y)
  let B := pre.foldl stp (seed true y)
  have hl : A.length = B.length := by simp [A,B,prefixLength,seed]
  have rows : ∀ i, A.getD i false = true → B.getD i false = true :=
    mono pre _ _ (by simp [seed]) preOK (seedOrder (by simp) (fun _ h => h))
  have bad : ¬ ((!takeWire A pins) = true → (!takeWire B pins) = true) := by
    intro h
    have whole : ∀ i, (A++[!takeWire A pins]).getD i false = true →
      (B++[!takeWire B pins]).getD i false = true := by
      intro i
      simp only [getD_snoc,hl]
      split
      · exact h
      · exact rows i
    have terminal := mono post _ _ (by simp [hl]) postOK whole o
    rw [evalAfter, eval_eq,List.foldl_append,List.foldl_cons] at high low
    change (post.foldl stp (A++[!takeWire A pins])).getD o false = true at high
    change (post.foldl stp (B++[!takeWire B pins])).getD o false = false at low
    exact Bool.noConfusion ((terminal high).symm.trans low)
  change takeWire A pins = false ∧ takeWire B pins = true
  cases ha : takeWire A pins <;> cases hb : takeWire B pins <;> simp_all

theorem necessary (pre post : List Gate) (pins : List ℕ) (o : ℕ)
    (preOK : ∀ g ∈ pre, grow g) (postOK : ∀ g ∈ post, grow g)
    (correct : ∀ a y, evalAfter pre post pins o (!a) y = edge a y) :
    (∀ y, pivotal y → operand pre pins false y = false ∧ operand pre pins true y = true) ∧
    (∀ y, edge false y = false → y ≠ blocked → operand pre pins false y = false) := by
  have live (y : Y) (h : pivotal y) := cutMustFlip pre post pins o preOK postOK y
    ((correct true y).trans h.2) ((correct false y).trans h.1)
  refine ⟨live,?_⟩
  intro y h ne
  obtain ⟨n,_,subset,piv⟩ := downClosure y h ne
  cases hy : operand pre pins false y with
  | false => rfl
  | true =>
    have contradiction := operandMono pre preOK pins (a:=false) (b:=false)
      id subset hy
    rw [(live _ piv).1] at contradiction
    contradiction

def seesNeighbor (y : Y) := y 0 || y 3 || y 4

theorem upClosure : ∀ y : Y, seesNeighbor y = true →
    ∃ k ∈ [1,8,16], below (mask k) y ∧ pivotal (mask k) := by decide +kernel

theorem upperNecessary (pre post : List Gate) (pins : List ℕ) (o : ℕ)
    (preOK : ∀ g ∈ pre, grow g) (postOK : ∀ g ∈ post, grow g)
    (correct : ∀ a y, evalAfter pre post pins o (!a) y = edge a y) :
    ∀ y, seesNeighbor y = true → operand pre pins true y = true := by
  intro y h
  obtain ⟨k,_,sub,act⟩ := upClosure y h
  have hcut := (necessary pre post pins o preOK postOK correct).1 _ act
  exact operandMono pre preOK pins id sub hcut.2

-- If a unique OR reader accepts its companion, both polarities of the
-- distinguished input produce the same wire. This cannot happen on pivotal rows.
theorem orCompanion (s : Y → Bool) (r : Y → Bool → Bool)
    (hmono : ∀ {x y}, below x y → s x = true → s y = true)
    (correct : ∀ a y, edge a y = r y ((!a) || s y)) :
    (∀ y, edge false y = false → y ≠ blocked → s y = false) ∧
    (∀ a y, y ≠ blocked → edge a y = (s y || r y (!a))) := by
  have off (y : Y) (h : pivotal y) : s y = false := by
    cases hs : s y
    · rfl
    · have lo := correct false y
      have hi := correct true y
      simp only [hs,Bool.or_true,h.1,h.2] at lo hi
      exact False.elim (Bool.noConfusion (lo.trans hi.symm))
  have narrow (y : Y) (h : edge false y = false) (ne : y ≠ blocked) : s y = false := by
    obtain ⟨n,_,sub,act⟩ := downClosure y h ne
    cases hs : s y
    · rfl
    · have bad := hmono sub hs
      rw [off _ act] at bad
      contradiction
  refine ⟨narrow,?_⟩
  intro a y ne
  cases hs : s y
  · simpa [hs] using correct a y
  · have ep : edge false y = true := by
      cases he : edge false y
      · have hf := narrow y he ne
        rw [hs] at hf
        contradiction
      · rfl
    have hconst := correct a y
    have hlo := correct false y
    simp only [hs,Bool.or_true,ep] at hconst hlo
    simpa [hs] using hconst.trans hlo.symm

def emptyRow : Y := fun _ => false
def singleton (i : Fin 8) : Y := fun j => decide (j=i)
def relevant (s : Y → Bool) (i : Fin 8) : Prop :=
  ∃ x y, (∀ j, j ≠ i → x j = y j) ∧ s x ≠ s y
theorem andCompanion (s : Y → Bool) (r : Y → Bool → Bool)
    (hmono : ∀ {x y}, below x y → s x = true → s y = true)
    (correct : ∀ a y, edge a y = r y ((!a) && s y))
    (nonconstant : ∃ y, s y = false) :
    (∀ y, seesNeighbor y = true → s y = true) ∧
    (∀ i : Fin 8, i ∈ [0,3,4] → relevant s i) := by
  have on (y : Y) (h : pivotal y) : s y = true := by
    cases hs : s y
    · have lo := correct false y
      have hi := correct true y
      simp only [hs,Bool.and_false,h.1,h.2] at lo hi
      exact False.elim (Bool.noConfusion (lo.trans hi.symm))
    · rfl
  have upper (y : Y) (h : seesNeighbor y = true) : s y = true := by
    obtain ⟨k,_,sub,act⟩ := upClosure y h
    exact hmono sub (on _ act)
  have hempty : s emptyRow = false := by
    obtain ⟨y,hy⟩ := nonconstant
    cases h : s emptyRow
    · rfl
    · have hf := hmono (x:=emptyRow) (y:=y) (by simp [below,emptyRow]) h
      rw [hy] at hf
      contradiction
  refine ⟨upper,?_⟩
  intro i hi
  refine ⟨emptyRow,singleton i,?_,?_⟩
  · intro j hj
    simp [emptyRow,singleton,hj]
  · have hseen : ∀ j : Fin 8, j ∈ [0,3,4] → seesNeighbor (singleton j) = true := by decide
    simp [hempty,upper _ (hseen i hi)]

theorem isolatedOrCancellation (s : Y → Bool) (r : Y → Bool → Bool)
    (ms : ∀ {x y}, below x y → s x=true → s y=true)
    (mr : ∀ y, r y false=true → r y true=true)
    (correct : ∀ a y, edge a y = r y (!((!a) || s y))) :
    ∀ a y, y ≠ blocked → edge a y = r y a := by
  have narrowed := (orCompanion s (fun y b => r y (!b)) ms correct).1
  intro a y ne
  cases hs : s y
  · simpa [hs] using correct a y
  · have hf : edge false y = true := by
      cases he : edge false y
      · have h := narrowed y he ne
        rw [hs] at h
        contradiction
      · rfl
    have hit : r y false = true := by simpa using (correct false y).symm.trans hf
    have accepted : r y a = true := by cases a; exact hit; exact mr y hit
    simpa [hs,hit,accepted] using correct a y

end NegativePivotCut
namespace SignedOrBypass
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open SignedDirectCancel (step relabel splice after sim stepsLength)
open NegativePivotCut (edge seed Y below blocked)

def join (conj t s : Bool) := if conj then (t && s) else (t || s)

def reader (conj rev : Bool) (i : Nat) : Gate :=
  ⟨if conj then .and else .or, if rev then [i,0] else [0,i]⟩

lemma rid : relabel id = id := by funext g; cases g; simp [relabel]

lemma matchRaw (a b : Bool) (ws : List Bool) (i : Nat) (h : i ≠ 0) :
    (a::ws).getD i false = (b::ws).getD i false := by cases i <;> simp_all

lemma sameTail (gs : List Gate) (un : ∀ g ∈ gs, 0 ∉ g.inputs) (a b : Bool) (ws : List Bool) :
    ∃ W, gs.foldl step (a::ws) = a::W ∧ gs.foldl step (b::ws) = b::W := by
  obtain ⟨u,ha,hb⟩ := sim id gs (a::ws) (b::ws) [] (by
    intro g hg v i hi
    exact matchRaw a b (ws++v) i (fun eq => un g hg (eq ▸ hi)))
  exact ⟨ws++u, by simpa using ha, by simpa [rid] using hb⟩

def prefixRow (pre : List Gate) (y : Y) := (pre.foldl step (seed false y)).tail

lemma preAt (pre : List Gate) (un : ∀ g ∈ pre, 0 ∉ g.inputs) (t : Bool) (y : Y) :
    pre.foldl step (seed t y) = t::prefixRow pre y := by
  obtain ⟨W,ha,hb⟩ := sameTail pre un t false (List.ofFn y)
  simp only [prefixRow,seed,List.ofFn_cons,hb,List.tail_cons]
  exact ha

def partner (pre : List Gate) (conj : Bool) (i : Nat) (y : Y) : Bool :=
  if i = 0 then conj else (pre.foldl step (seed false y)).getD i false

lemma sideRead (pre : List Gate) (up : ∀ g ∈ pre, 0 ∉ g.inputs) (conj rev : Bool)
    (i : Nat) (t : Bool) (y : Y) :
    (reader conj rev i).op.eval ((reader conj rev i).inputs.map
      (fun k => (pre.foldl step (seed t y)).getD k false)) = (join conj t (partner pre conj i y)) := by
  rw [preAt pre up]
  unfold partner
  cases i with
  | zero => cases conj <;> cases rev <;> cases t <;> rfl
  | succ i => rw [preAt pre up]; cases conj <;> cases rev <;> simp [reader,join,GateOp.eval,Bool.or_comm,Bool.and_comm]

lemma partnerMono (pre : List Gate) (mp : ∀ g ∈ pre, NegativePivotCut.grow g) (conj : Bool) (i : Nat) :
    ∀ {x y}, below x y → partner pre conj i x = true → partner pre conj i y = true := by
  intro x y sub
  by_cases h : i=0
  · simp [partner,h]
  simp only [partner,h,ite_false]
  exact NegativePivotCut.mono pre _ _ (by simp [seed]) mp
    (NegativePivotCut.seedOrder (a:=false) (b:=false) id sub) i

def continuation (pre post : List Gate) (o : Nat) (y : Y) (z : Bool) :=
  (post.foldl step (false::(prefixRow pre y ++ [z]))).getD o false

lemma factor (pre post : List Gate) (conj rev : Bool) (i o : Nat) (no : o ≠ 0)
    (up : ∀ g ∈ pre, 0 ∉ g.inputs) (uq : ∀ g ∈ post, 0 ∉ g.inputs)
    (t : Bool) (y : Y) :
    Circuit.eval ⟨pre ++ reader conj rev i :: post,o⟩ (seed t y) =
    continuation pre post o y (join conj t (partner pre conj i y)) := by
  change ((pre++reader conj rev i::post).foldl step (seed t y)).getD o false = _
  rw [List.foldl_append,List.foldl_cons]
  have hstep : step (pre.foldl step (seed t y)) (reader conj rev i) =
      t::(prefixRow pre y++[join conj t (partner pre conj i y)]) := by
    change (pre.foldl step (seed t y)) ++ [_] = _
    rw [sideRead pre up,preAt pre up]
    rfl
  rw [hstep]
  obtain ⟨W,ha,hb⟩ := sameTail post uq t false (prefixRow pre y++[join conj t (partner pre conj i y)])
  change (post.foldl _ (t::(prefixRow pre y++[join conj t (partner pre conj i y)]))).getD o false = _
  unfold continuation
  rw [ha,hb]
  exact matchRaw t false W o no

lemma aliasRead (w tail : List Bool) (hi : 0 < w.length) (i : Nat) :
    ((w++[w.getD 0 false])++tail).getD i false = (w++tail).getD (splice w.length i) false := by
  by_cases eq : i=w.length
  · subst i
    rw [List.getD_append _ _ _ _ (by simp)]
    rw [NegativePivotCut.getD_snoc]
    simp only [splice,ite_true]
    exact (List.getD_append _ _ _ _ hi).symm
  by_cases low : i<w.length
  · simp only [splice,eq,low,↓reduceIte]
    rw [List.getD_append _ _ _ _ (by simp; omega),List.getD_append _ _ _ _ low,
      List.getD_append _ _ _ _ low]
  · simp only [splice,eq,low,↓reduceIte]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    simp
    omega

theorem bypassAt (pre post : List Gate) (g : Gate) (o : Nat) (w : List Bool) (hw : w.length=9)
    (aliasValue : g.op.eval (g.inputs.map fun i => (pre.foldl step w).getD i false) =
      (pre.foldl step w).getD 0 false) :
    Circuit.eval ⟨pre++g::post,o⟩ w = (after pre post o).eval w := by
  let A := pre.foldl step w
  have hl : A.length=9+pre.length := by simp [A,stepsLength,hw]
  let ρ := splice (9+pre.length)
  have same (tail : List Bool) (i : Nat) :
      ((A++[A.getD 0 false])++tail).getD i false = (A++tail).getD (ρ i) false := by
    unfold ρ; rw [←hl]; exact aliasRead _ _ (by omega) _
  obtain ⟨T,ha,hb⟩ := sim ρ post (A++[A.getD 0 false]) A [] (fun _ _ v i _ => same v i)
  change ((pre++g::post).foldl step w).getD o false =
    ((pre++post.map (relabel ρ)).foldl step w).getD (ρ o) false
  rw [List.foldl_append,List.foldl_cons,List.foldl_append]
  have hg : step (pre.foldl step w) g = A++[A.getD 0 false] := by
    change (pre.foldl step w)++[_] = (pre.foldl step w)++[_]
    rw [aliasValue]
  rw [hg]
  change (post.foldl step _).getD o false = ((post.map (relabel ρ)).foldl step A).getD (ρ o) false
  simp only [List.append_nil] at ha hb
  rw [ha,hb]
  exact same T o

def isNot : GateOp → Bool | .not => true | _ => false
def Count (gs : List Gate) := gs.countP (fun g => !(isNot g.op))
def NotCount (gs : List Gate) := gs.countP (fun g => isNot g.op)

theorem cost (pre post : List Gate) (conj rev : Bool) (i o : Nat) :
    Count (after pre post o).gates + 1 = Count (pre++reader conj rev i::post) := by
  cases conj <;> simp [Count,after,List.countP_map,relabel,reader,isNot,Function.comp_def]
  all_goals omega

def safe (conj a : Bool) (y : Y) : Prop :=
  if conj then (a=true ∨ NegativePivotCut.seesNeighbor y=true)
  else (a=false ∨ (edge false y=false ∧ y ≠ blocked))

theorem safeEquivalence (pre post : List Gate) (conj rev : Bool) (i o : Nat)
    (no : o ≠ 0) (up : ∀ g ∈ pre, 0 ∉ g.inputs) (uq : ∀ g ∈ post, 0 ∉ g.inputs)
    (mp : ∀ g ∈ pre, NegativePivotCut.grow g)
    (correct : ∀ a y, Circuit.eval ⟨pre++reader conj rev i::post,o⟩ (seed (!a) y) = edge a y) :
    ∀ a y, safe conj a y → (after pre post o).eval (seed (!a) y) = edge a y := by
  have functor (a y) : edge a y = continuation pre post o y (join conj (!a) (partner pre conj i y)) :=
    (correct a y).symm.trans (factor pre post conj rev i o no up uq (!a) y)
  intro a y valid
  refine (bypassAt pre post _ o (seed (!a) y) (by simp [seed]) ?_).symm.trans (correct a y)
  rw [sideRead pre up,preAt pre up]
  change join conj (!a) (partner pre conj i y) = !a
  cases conj
  · have off := (NegativePivotCut.orCompanion (partner pre false i) (continuation pre post o)
      (partnerMono pre mp false i) functor).1
    rcases valid with rfl|⟨he,hne⟩
    · simp [join]
    · simp [join,off y he hne]
  · rcases valid with rfl|hs
    · simp [join]
    · by_cases all : ∀ v, partner pre true i v = true
      · simp [join,all]
      push_neg at all
      obtain ⟨v,hv⟩ := all
      have hh : partner pre true i v = false := by cases h : partner pre true i v <;> simp_all
      have on := (NegativePivotCut.andCompanion (partner pre true i) (continuation pre post o)
        (partnerMono pre mp true i) functor ⟨v,hh⟩).1
      simp [join,on y hs]

end SignedOrBypass
namespace SignedOrBypass
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open SignedDirectCancel (step relabel after)
open NegativePivotCut (edge seed Y below blocked)

lemma firstRead (gs : List Gate) (w : List Bool) (h : 0 < w.length) :
    (gs.foldl step w).getD 0 false = w.getD 0 false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step])]
    exact List.getD_append _ _ _ _ h

lemma outputNonzero (gs : List Gate) (o : Nat)
    (correct : ∀ a y, Circuit.eval ⟨gs,o⟩ (seed (!a) y) = edge a y) : o ≠ 0 := by
  intro eq
  have h := correct false (fun _ => false)
  change (gs.foldl step (seed true (fun _ => false))).getD o false = false at h
  rw [eq,firstRead _ _ (by simp [seed])] at h
  contradiction

lemma contMono (pre post : List Gate) (o : Nat) (y : Y) (up : ∀ g ∈ post, NegativePivotCut.grow g)
    (b c : Bool) (bc : b=true → c=true) :
    continuation pre post o y b=true → continuation pre post o y c=true := by
  let w := false :: prefixRow pre y
  change (post.foldl _ (w++[b])).getD o false = true → (post.foldl _ (w++[c])).getD o false = true
  apply NegativePivotCut.mono post _ _ (by simp) up _ o
  intro j
  rw [NegativePivotCut.getD_snoc,NegativePivotCut.getD_snoc]
  split
  · exact bc
  · exact id

lemma hasTailNot (pre post : List Gate) (conj rev : Bool) (i o : Nat) (no : o ≠ 0)
    (up : ∀ g ∈ pre, 0 ∉ g.inputs) (uq : ∀ g ∈ post, 0 ∉ g.inputs)
    (fan : FanInTwo ⟨pre++reader conj rev i::post,o⟩)
    (correct : ∀ a y, Circuit.eval ⟨pre++reader conj rev i::post,o⟩ (seed (!a) y) = edge a y) :
    ∃ g ∈ post, g.op = GateOp.not := by
  by_contra nh
  have mon (g) (hg : g ∈ post) : NegativePivotCut.grow g := by
    obtain ⟨hop,_⟩ := fan g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
    rcases hop with ha|ho|hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact False.elim (nh ⟨g,hg,hn⟩)
  let y := NegativePivotCut.mask 1
  have low : edge false y = false := by decide
  have high : edge true y = true := by decide
  have h (a : Bool) := (factor pre post conj rev i o no up uq (!a) y).symm.trans (correct a y)
  have hc := contMono pre post o y mon (join conj false (partner pre conj i y))
    (join conj true (partner pre conj i y)) (by cases conj <;> simp [join]) ((h true).trans high)
  exact Bool.noConfusion (hc.symm.trans ((h false).trans low))

lemma notePos {g : Gate} {gs : List Gate} (hg : g ∈ gs) (hn : g.op = .not) :
    0 < NotCount gs := by
  induction gs with
  | nil => simp at hg
  | cons x xs ih =>
    rcases List.mem_cons.mp hg with rfl|hg
    · simp [NotCount,List.countP_cons,hn,isNot]
    · have ht := ih hg
      simp only [NotCount,List.countP_cons] at *
      omega

lemma preGrowth (pre post : List Gate) (conj rev : Bool) (i o : Nat)
    (up : ∀ g ∈ pre, 0 ∉ g.inputs) (uq : ∀ g ∈ post, 0 ∉ g.inputs)
    (fan : FanInTwo ⟨pre++reader conj rev i::post,o⟩)
    (one : NotCount (pre++reader conj rev i::post) ≤ 1)
    (correct : ∀ a y, Circuit.eval ⟨pre++reader conj rev i::post,o⟩ (seed (!a) y) = edge a y) :
    ∀ g ∈ pre, NegativePivotCut.grow g := by
  obtain ⟨n,hn,hop⟩ := hasTailNot pre post conj rev i o (outputNonzero _ _ correct) up uq fan correct
  have tail := notePos hn hop
  intro g hg
  obtain ⟨op,_⟩ := fan g (List.mem_append_left _ hg)
  rcases op with ha|ho|hn
  · exact Or.inl ha
  · exact Or.inr ho
  · have front := notePos hg hn
    simp only [NotCount,List.countP_append,List.countP_cons] at one front tail
    omega

lemma keepFan (pre post : List Gate) (conj rev : Bool) (i o : Nat)
    (fan : FanInTwo ⟨pre++reader conj rev i::post,o⟩) : FanInTwo (after pre post o) := by
  intro g hg
  rcases List.mem_append.mp hg with hp|hq
  · exact fan g (List.mem_append_left _ hp)
  · obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hq
    simpa [relabel] using fan g' (List.mem_append_right _ (List.mem_cons_of_mem _ hg'))

theorem bypassReader (pre post : List Gate) (conj rev : Bool) (i o : Nat)
    (up : ∀ g ∈ pre, 0 ∉ g.inputs) (uq : ∀ g ∈ post, 0 ∉ g.inputs)
    (fan : FanInTwo ⟨pre++reader conj rev i::post,o⟩)
    (one : NotCount (pre++reader conj rev i::post) ≤ 1)
    (correct : ∀ a y, Circuit.eval ⟨pre++reader conj rev i::post,o⟩ (seed (!a) y) = edge a y) :
    ∃ B : Circuit, FanInTwo B ∧ Count B.gates + 1 = Count (pre++reader conj rev i::post) ∧
      ∀ a y, safe conj a y → B.eval (seed (!a) y) = edge a y := by
  exact ⟨after pre post o,keepFan pre post conj rev i o fan,cost pre post conj rev i o,
    safeEquivalence pre post conj rev i o (outputNonzero _ _ correct) up uq
      (preGrowth pre post conj rev i o up uq fan one correct) correct⟩
end SignedOrBypass
namespace SignedReaderExclusion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open NegativePivotCut (edge seed Y)
open SignedDirectCancel (after step)
open SignedOrBypass (Count NotCount safe isNot reader)

lemma countSum (gs : List Gate) : Count gs + NotCount gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [Count,NotCount,List.countP_cons,List.length_cons] at *
    cases h : isNot g.op <;> simp [h] <;> omega

def correct (D : Circuit) : Prop := ∀ a y, D.eval (seed (!a) y) = edge a y

lemma essential (D : Circuit) (h : correct D) : ∃ g ∈ D.gates, 0 ∈ g.inputs := by
  have nz := SignedOrBypass.outputNonzero D.gates D.output h
  by_contra no
  have unused (g) (hg : g ∈ D.gates) : 0 ∉ g.inputs := fun hm => no ⟨g,hg,hm⟩
  let y := NegativePivotCut.mask 1
  obtain ⟨W,ha,hb⟩ := SignedOrBypass.sameTail D.gates unused false true (List.ofFn y)
  have same := SignedOrBypass.matchRaw false true W D.output nz
  have lo := h false y
  have hi := h true y
  change (D.gates.foldl step (seed false y)).getD D.output false = true at hi
  change (D.gates.foldl step (seed true y)).getD D.output false = false at lo
  simp only [seed,List.ofFn_cons,ha,hb] at hi lo
  exact Bool.noConfusion (hi.symm.trans (same.trans lo))

lemma needsNot (D : Circuit) (fan : FanInTwo D) (h : correct D) : 0 < NotCount D.gates := by
  by_contra! none
  have mono (g) (hg : g ∈ D.gates) : NegativePivotCut.grow g := by
    rcases (fan g hg).1 with ha|ho|hn
    · exact Or.inl ha
    · exact Or.inr ho
    · have hp := SignedOrBypass.notePos hg hn
      omega
  let y := NegativePivotCut.mask 1
  have high : D.eval (seed false y)=true := (h true y).trans (by decide)
  have low : D.eval (seed true y)=false := (h false y).trans (by decide)
  have hit := NegativePivotCut.mono D.gates _ _ (by simp [seed]) mono
    (NegativePivotCut.seedOrder (a:=false) (b:=true) (x:=y) (y:=y) (by simp) (fun _ h=>h)) D.output high
  exact Bool.noConfusion (hit.symm.trans low)

lemma splitReader (gs : List Gate) (yes : ∃ g ∈ gs, 0 ∈ g.inputs)
    (one : (gs.filter (fun g => g.inputs.contains 0)).length ≤ 1) :
    ∃ pre g post, gs=pre++g::post ∧ 0∈g.inputs ∧
      (∀ t ∈ pre, 0 ∉ t.inputs) ∧ ∀ t ∈ post, 0 ∉ t.inputs := by
  induction gs with
  | nil => simp at yes
  | cons g gs ih =>
    by_cases hg : 0 ∈ g.inputs
    · refine ⟨[],g,gs,rfl,hg,by simp,?_⟩
      have hz : (gs.filter (fun t => t.inputs.contains 0)).length = 0 := by simpa [hg] using one
      have empty := List.length_eq_zero_iff.mp hz
      intro t ht bad
      have ht' : t ∈ gs.filter (fun v => v.inputs.contains 0) := List.mem_filter.mpr ⟨ht,by simpa⟩
      rw [empty] at ht'
      contradiction
    · have hy : ∃ t ∈ gs, 0 ∈ t.inputs := by
        obtain ⟨t,ht,h0⟩ := yes
        rcases List.mem_cons.mp ht with rfl|ht
        · exact False.elim (hg h0)
        · exact ⟨t,ht,h0⟩
      obtain ⟨p,t,q,eq,ht,up,uq⟩ := ih hy (by simpa [hg] using one)
      refine ⟨g::p,t,q,by simp [eq],ht,?_,uq⟩
      intro k hk
      rcases List.mem_cons.mp hk with rfl|hk
      · exact hg
      · exact up _ hk

lemma mustToggle (pre post : List Gate) (g : Gate) (o : Nat)
    (up : ∀ g ∈ pre, 0 ∉ g.inputs) (uq : ∀ g ∈ post, 0 ∉ g.inputs)
    (ok : correct ⟨pre++g::post,o⟩) :
    let y := NegativePivotCut.mask 1
    g.op.eval (g.inputs.map fun i => (pre.foldl step (seed false y)).getD i false) ≠
    g.op.eval (g.inputs.map fun i => (pre.foldl step (seed true y)).getD i false) := by
  dsimp only
  intro eq
  let y := NegativePivotCut.mask 1
  let P := SignedOrBypass.prefixRow pre y
  let v := g.op.eval (g.inputs.map fun i => (pre.foldl step (seed false y)).getD i false)
  have nz := SignedOrBypass.outputNonzero _ _ ok
  have ha : step (pre.foldl step (seed false y)) g = false::(P++[v]) := by
    change (pre.foldl step (seed false y))++[v] = _
    rw [SignedOrBypass.preAt pre up]; rfl
  have hb : step (pre.foldl step (seed true y)) g = true::(P++[v]) := by
    change (pre.foldl step (seed true y))++[_] = _
    rw [←eq,SignedOrBypass.preAt pre up true]; rfl
  obtain ⟨w,hw,hv⟩ := SignedOrBypass.sameTail post uq false true (P++[v])
  have same := SignedOrBypass.matchRaw false true w o nz
  have lo := ok false y
  have hi := ok true y
  change ((pre++g::post).foldl step (seed false y)).getD o false = true at hi
  change ((pre++g::post).foldl step (seed true y)).getD o false = false at lo
  rw [List.foldl_append,List.foldl_cons,ha,hw] at hi
  rw [List.foldl_append,List.foldl_cons,hb,hv] at lo
  exact Bool.noConfusion (hi.symm.trans (same.trans lo))

lemma monoOthers (pre post : List Gate) (pins : List Nat) (o : Nat)
    (fan : FanInTwo ⟨pre++⟨.not,pins⟩::post,o⟩)
    (one : NotCount (pre++⟨.not,pins⟩::post) ≤ 1) :
    ∀ g ∈ pre++post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  rcases List.mem_append.mp hg with hp|hq
  · obtain ⟨hop,len⟩ := fan g (List.mem_append_left _ hp)
    refine ⟨?_,len⟩
    rcases hop with ha|ho|hn
    · exact Or.inl ha
    · exact Or.inr ho
    · have pos := SignedOrBypass.notePos hp hn
      have upper : NotCount pre + (NotCount post + 1) ≤ 1 := by
        simpa only [NotCount,List.countP_append,List.countP_cons,show isNot .not=true from rfl,ite_true] using one
      omega
  · obtain ⟨hop,len⟩ := fan g (List.mem_append_right _ (List.mem_cons_of_mem _ hq))
    refine ⟨?_,len⟩
    rcases hop with ha|ho|hn
    · exact Or.inl ha
    · exact Or.inr ho
    · have pos := SignedOrBypass.notePos hq hn
      have upper : NotCount pre + (NotCount post + 1) ≤ 1 := by
        simpa only [NotCount,List.countP_append,List.countP_cons,show isNot .not=true from rfl,ite_true] using one
      omega

def DomainBound (conj : Bool) : Prop := ∀ C : Circuit, FanInTwo C →
  (∀ a y, safe conj a y → C.eval (seed (!a) y) = edge a y) → 13 ≤ Count C.gates

lemma generalReader (pre post : List Gate) (conj rev : Bool) (i o : Nat)
    (up : ∀ g ∈ pre, 0 ∉ g.inputs) (uq : ∀ g ∈ post, 0 ∉ g.inputs)
    (fan : FanInTwo ⟨pre++reader conj rev i::post,o⟩)
    (one : NotCount (pre++reader conj rev i::post) ≤ 1)
    (small : (pre++reader conj rev i::post).length ≤ 14)
    (ok : correct ⟨pre++reader conj rev i::post,o⟩) (lower : DomainBound conj) : False := by
  obtain ⟨B,bf,bc,be⟩ := SignedOrBypass.bypassReader pre post conj rev i o up uq fan one ok
  have h := lower B bf be
  have hn := needsNot _ fan ok
  have hsum := countSum (pre++reader conj rev i::post)
  change 0 < NotCount (pre++reader conj rev i::post) at hn
  omega

end SignedReaderExclusion
namespace SignedReaderExclusion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open NegativePivotCut (edge seed Y)
open SignedDirectCancel (after step)
open SignedOrBypass (Count NotCount safe isNot reader)

lemma toNine (C : Circuit) (ok : correct C) (x : Fin 9 → Bool) :
    circuitFun 9 C (fun i => if i=0 then !(x 0) else x i) = PartialPetersenMonotone.target x := by
  let y := fun i : Fin 8 => x i.succ
  have hn : List.ofFn (fun i : Fin 9 => if i=0 then !(x 0) else x i) = seed (!(x 0)) y := by
    rw [List.ofFn_succ,seed,List.ofFn_cons]
    simp [y]
  change C.eval _ = _
  rw [hn]
  exact ok _ y

lemma unaryCase (pre post : List Gate) (conj : Bool) (o : Nat)
    (fan : FanInTwo ⟨pre++⟨if conj then .and else .or,[0]⟩::post,o⟩)
    (small : (pre++⟨if conj then .and else .or,[0]⟩::post).length ≤ 14)
    (ok : correct ⟨pre++⟨if conj then .and else .or,[0]⟩::post,o⟩) (lower : DomainBound false) : False := by
  let g : Gate := ⟨if conj then .and else .or,[0]⟩
  have bf : FanInTwo (after pre post o) := by
    intro k hk
    rcases List.mem_append.mp hk with hp|hq
    · exact fan k (List.mem_append_left _ hp)
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
      simpa [SignedDirectCancel.relabel] using fan j (List.mem_append_right _ (List.mem_cons_of_mem _ hj))
  have agree (a y) : (after pre post o).eval (seed (!a) y) = edge a y := by
    refine (SignedOrBypass.bypassAt pre post g o _ (by simp [seed]) ?_).symm.trans (ok a y)
    cases conj <;> simp [g,GateOp.eval]
  have lb := lower _ bf (fun a y _ => agree a y)
  have extra : Count (after pre post o).gates + 1 = Count (pre++g::post) := by
    cases conj <;> simp [Count,after,g,isNot,List.countP_map,Function.comp_def,SignedDirectCancel.relabel]
    all_goals omega
  have nt := needsNot _ fan ok
  change 0 < NotCount (pre++g::post) at nt
  have ct := countSum (pre++g::post)
  change (pre++g::post).length ≤ 14 at small
  omega

lemma binaryCase (pre post : List Gate) (conj : Bool) (pins : List Nat) (o : Nat)
    (up : ∀ g ∈ pre, 0 ∉ g.inputs) (uq : ∀ g ∈ post, 0 ∉ g.inputs)
    (fan : FanInTwo ⟨pre++⟨if conj then .and else .or,pins⟩::post,o⟩)
    (one : NotCount (pre++⟨if conj then .and else .or,pins⟩::post) ≤ 1)
    (small : (pre++⟨if conj then .and else .or,pins⟩::post).length ≤ 14)
    (ok : correct ⟨pre++⟨if conj then .and else .or,pins⟩::post,o⟩)
    (pin : 0 ∈ pins) (lb : ∀ b, DomainBound b) : False := by
  have size := (fan ⟨if conj then .and else .or,pins⟩ (List.mem_append_right _ List.mem_cons_self)).2
  change pins.length ≤ 2 at size
  rcases pins with _|⟨j,_|⟨k,_|⟨m,ms⟩⟩⟩
  · simp at pin
  · have h : 0 = j := by simpa using pin
    subst j
    exact unaryCase pre post conj o fan small ok (lb false)
  · rcases List.mem_cons.mp pin with he|he
    · subst j
      exact generalReader pre post conj false k o up uq fan one small ok (lb conj)
    · have h : 0 = k := by simpa using he
      subst k
      exact generalReader pre post conj true j o up uq fan one small ok (lb conj)
  · simp at size

theorem signedReaderExclusion (D : Circuit) (fan : FanInTwo D) (small : D.size ≤ 14)
    (one : NotCount D.gates ≤ 1) (few : (D.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    (ok : correct D) (lb : ∀ b, DomainBound b) : False := by
  obtain ⟨pre,g,post,eq,mem,up,uq⟩ := splitReader D.gates (essential D ok) few
  obtain ⟨gs,o⟩ := D
  change gs = _ at eq
  subst gs
  obtain ⟨op,pins⟩ := g
  change 0 ∈ pins at mem
  have ops := (fan ⟨op,pins⟩ (List.mem_append_right _ List.mem_cons_self)).1
  rcases ops with ha|ho|hn
  · change op = .and at ha
    subst op
    exact binaryCase pre post true pins o up uq fan one small ok mem lb
  · change op = .or at ho
    subst op
    exact binaryCase pre post false pins o up uq fan one small ok mem lb
  · change op = .not at hn
    subst op
    rcases pins with _|⟨j,rest⟩
    · simp at mem
    · by_cases hj : j=0
      · subst j
        apply SignedDirectCancel.directReaderImpossible pre post rest o
          (by intro t ht; exact (List.mem_append.mp ht).elim (up t) (uq t))
          (monoOthers pre post _ o fan one) _ (toNine _ ok)
        simp [Circuit.size] at small
        omega
      · have ne := mustToggle pre post ⟨.not,j::rest⟩ o up uq ok
        apply ne
        change (!((pre.foldl step (seed false (NegativePivotCut.mask 1))).getD j false)) =
          (!((pre.foldl step (seed true (NegativePivotCut.mask 1))).getD j false))
        rw [SignedOrBypass.preAt pre up,SignedOrBypass.preAt pre up]
        exact congrArg Bool.not (SignedOrBypass.matchRaw false true _ j hj)
end SignedReaderExclusion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace BranchBound

-- The branch-group argument and circuit simplifier are adapted from L_meta_1549.
-- The simplifier tracks the number of non-NOT gates independently of length.

namespace BranchGraph

variable {V : Type*} [DecidableEq V]

def containsEdge (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∃ a ∈ I, ∃ b ∈ I, G.Adj a b

omit [DecidableEq V] in
lemma singleton_no_edge (G : SimpleGraph V) (w : V) : ¬ containsEdge G {w} := by
  rintro ⟨a, ha, b, hb, hab⟩
  rw [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl w hab

lemma pair_contains_edge (G : SimpleGraph V) (u w : V) : containsEdge G {u,w} ↔ G.Adj u w := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u, by simp, w, by simp, h⟩

def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

section FiniteGraph

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def neighborsAfter (removed : Finset V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v ∧ v ∉ removed)

lemma neighborsAfter_subset {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u := by
  intro v membership
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at membership ⊢
  exact ⟨membership.1, fun vIn => membership.2 (h vIn)⟩

lemma neighbor_equality_survives {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u = neighborsAfter G A w) :
    neighborsAfter G B u = neighborsAfter G B w := by
  have e (v : V) : neighborsAfter G B v = (neighborsAfter G A v).filter (· ∉ B) := by
    ext z
    simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hz => ⟨⟨hz.1, fun zIn => hz.2 (h zIn)⟩, hz.2⟩, fun hz => ⟨hz.1.1, hz.2⟩⟩
  rw [e u, e w, same]

def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group, ∀ w ∈ group, (neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty → neighborsAfter G removed u = neighborsAfter G removed w

def isolates (removed : Finset V) : Finset V :=
  Finset.univ.filter (fun v => neighborsAfter G removed v = ∅)

def maximalClass (removed : Finset V) (root : V) : Finset V :=
  if root ∉ removed ∧ (neighborsAfter G removed root).Nonempty then
    Finset.univ.filter (fun v => v ∉ removed ∧ neighborsAfter G removed v = neighborsAfter G removed root)
  else ∅

def closeIsolates (removed : Finset V) : Finset V := removed ∪ isolates G removed

def removeClass (removed : Finset V) (root : V) : Finset V :=
  closeIsolates G (removed ∪ maximalClass G removed root)

lemma subset_removeClass (removed : Finset V) (root : V) : removed ⊆ removeClass G removed root := by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)

lemma isolate_mem_removeClass {removed : Finset V} (root u : V)
    (h : ¬ (neighborsAfter G removed u).Nonempty) : u ∈ removeClass G removed root := by
  have hn : ¬ (neighborsAfter G (removed ∪ maximalClass G removed root) u).Nonempty := by
    intro existsNeighbor
    exact h (existsNeighbor.mono (neighborsAfter_subset G Finset.subset_union_left u))
  have hu : u ∈ isolates G (removed ∪ maximalClass G removed root) := by
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp hn]
  exact Finset.mem_union_right _ hu

theorem dominates_step [Nonempty V] {A B Q : Finset V} (smaller : A ⊆ B)
    (twins : TwinGroup G A Q) : ∃ root : V, A ∪ Q ⊆ removeClass G B root := by
  classical
  by_cases someActive : ∃ root ∈ Q, root ∉ B ∧ (neighborsAfter G B root).Nonempty
  · obtain ⟨root, rootQ, rootOut, rootLive⟩ := someActive
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    by_cases live : (neighborsAfter G B u).Nonempty
    · have oldU := live.mono (neighborsAfter_subset G smaller u)
      have oldRoot := rootLive.mono (neighborsAfter_subset G smaller root)
      have same := neighbor_equality_survives G smaller (twins u hu root rootQ oldU oldRoot)
      have covered : u ∈ maximalClass G B root := by simp [maximalClass, rootOut, rootLive, uIn, same]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ covered)
    · exact isolate_mem_removeClass G root u live
  · let root : V := Classical.choice inferInstance
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    exact isolate_mem_removeClass G root u (fun live => someActive ⟨u, hu, uIn, live⟩)

lemma retained_after_close {removed : Finset V} {u : V} (out : u ∉ closeIsolates G removed) :
    (neighborsAfter G (closeIsolates G removed) u).Nonempty := by
  have uOut : u ∉ removed := fun h => out (Finset.mem_union_left _ h)
  have old : (neighborsAfter G removed u).Nonempty := by
    by_contra empty
    apply out
    apply Finset.mem_union_right
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp empty]
  obtain ⟨v, hv⟩ := old
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  refine ⟨v, ?_⟩
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hv.1, fun dropped => ?_⟩
  rcases Finset.mem_union.mp dropped with h | h
  · exact hv.2 h
  · have witness : u ∈ neighborsAfter G removed v := by
      simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hv.1.symm, uOut⟩
    have none : neighborsAfter G removed v = ∅ := by simpa [isolates] using h
    rw [none] at witness
    exact Finset.notMem_empty _ witness

lemma closeIsolates_idempotent (removed : Finset V) :
    closeIsolates G (closeIsolates G removed) = closeIsolates G removed := by
  apply Finset.Subset.antisymm
  · intro u hu
    rcases Finset.mem_union.mp hu with already | isolated
    · exact already
    by_contra out
    have live := retained_after_close G out
    have noNeighbors : neighborsAfter G (closeIsolates G removed) u = ∅ := by
      simpa [isolates] using isolated
    simpa [noNeighbors] using live
  · exact Finset.subset_union_left

def TwinSteps : Finset V → List (Finset V) → Prop
  | _, [] => True
  | removed, group :: rest => TwinGroup G removed group ∧ TwinSteps (removed ∪ group) rest

def removedThrough : Finset V → List (Finset V) → Finset V
  | removed, [] => removed
  | removed, group :: rest => removedThrough (removed ∪ group) rest

def ClassSteps : ℕ → Finset V → Finset V → Prop
  | 0, start, finish => finish = start
  | k + 1, start, finish => ∃ root : V, ClassSteps k (removeClass G start root) finish

theorem dominates_steps [Nonempty V] {A B : Finset V} (groups : List (Finset V))
    (smaller : A ⊆ B) (steps : TwinSteps G A groups) :
    ∃ finish : Finset V, ClassSteps G groups.length B finish ∧ removedThrough A groups ⊆ finish := by
  induction groups generalizing A B with
  | nil => exact ⟨B, rfl, smaller⟩
  | cons group rest ih =>
    obtain ⟨twins, next⟩ := steps
    obtain ⟨root, subset⟩ := dominates_step G smaller twins
    obtain ⟨finish, walk, covered⟩ := ih subset next
    exact ⟨finish, ⟨root, walk⟩, covered⟩

def EdgelessAfter (removed : Finset V) : Prop :=
  ∀ u v, u ∉ removed → v ∉ removed → ¬ G.Adj u v

omit [Fintype V] [DecidableRel G.Adj] in
lemma edgeless_mono {A B : Finset V} (subset : A ⊆ B) (noEdges : EdgelessAfter G A) :
    EdgelessAfter G B := by
  intro u v uOut vOut
  exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))

lemma closed_edgeless_all {D : Finset V} (noEdges : EdgelessAfter G (closeIsolates G D)) :
    closeIsolates G D = Finset.univ := by
  ext u
  simp only [Finset.mem_univ, iff_true]
  by_contra out
  obtain ⟨v, hv⟩ := retained_after_close G out
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact noEdges u v out hv.2 hv.1

lemma classSteps_finish_closed {k : ℕ} {start finish : Finset V} (walk : ClassSteps G k start finish)
    (closed : ∃ D : Finset V, start = closeIsolates G D) : ∃ D : Finset V, finish = closeIsolates G D := by
  induction k generalizing start with
  | zero =>
    change finish = start at walk
    rw [walk]
    exact closed
  | succ k ih =>
    obtain ⟨root, after⟩ := walk
    exact ih after ⟨_, rfl⟩

theorem covering_sequence_reaches_univ [Nonempty V] (groups : List (Finset V))
    (twins : TwinSteps G ∅ groups) (finished : EdgelessAfter G (removedThrough ∅ groups)) :
    ClassSteps G groups.length (closeIsolates G ∅) Finset.univ := by
  obtain ⟨D, steps, subset⟩ := dominates_steps G groups (Finset.empty_subset (closeIsolates G ∅)) twins
  have noEdges := edgeless_mono G subset finished
  obtain ⟨A, hD⟩ := classSteps_finish_closed G steps ⟨∅, rfl⟩
  rw [hD] at noEdges
  rwa [hD, closed_edgeless_all G noEdges] at steps

end FiniteGraph

end BranchGraph

namespace BranchGroupsLean

open BranchGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat}

def bucket (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v = r)

def below (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v < r)

def coveredBy (label : V → Fin m) (done : List (Fin m)) : Finset V :=
  Finset.univ.filter (fun v => label v ∈ done)

omit [DecidableEq V] in
@[simp] lemma coveredBy_nil (label : V → Fin m) : coveredBy label [] = ∅ := by
  ext v
  simp [coveredBy]

lemma coveredBy_append_singleton (label : V → Fin m) (done : List (Fin m)) (r : Fin m) :
    coveredBy label (done ++ [r]) = coveredBy label done ∪ bucket label r := by
  ext v
  simp [coveredBy, bucket, List.mem_append]

omit [DecidableEq V] in
lemma covered_before_of_sorted (label : V → Fin m) (out : Fin m) (done rest : List (Fin m)) (r : Fin m)
    (sorted : (done ++ r :: rest).Pairwise (· < ·))
    (roots : ∀ v : V, label v = out ∨ label v ∈ done ++ r :: rest)
    (beforeOut : r < out) : coveredBy label done = below label r := by
  have facts := List.pairwise_append.mp sorted
  ext v
  simp only [coveredBy, below, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro member
    exact facts.2.2 _ member r (by simp)
  · intro earlier
    rcases roots v with isOut | member
    · rw [isOut] at earlier
      exact (lt_asymm earlier beforeOut).elim
    rcases List.mem_append.mp member with doneMember | coming
    · exact doneMember
    rcases List.mem_cons.mp coming with atRoot | later
    · exact (ne_of_lt earlier atRoot).elim
    have after := (List.pairwise_cons.mp facts.2.1).1 _ later
    exact (lt_asymm earlier after).elim

section Graph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sorted_tail_twin_steps (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (sorted : roots.Pairwise (· < ·)) (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (beforeOut : ∀ r ∈ roots, r < out)
    (twinAt : ∀ r ∈ roots, TwinGroup G (below label r) (bucket label r))
    (done pending : List (Fin m)) (complete : done ++ pending = roots) :
    TwinSteps G (coveredBy label done) (pending.map (bucket label)) := by
  induction pending generalizing done with
  | nil => exact True.intro
  | cons r tail ih =>
    have rMember : r ∈ roots := complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
    have prev := covered_before_of_sorted label out done tail r (by simpa only [complete] using sorted)
      (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
    have next := ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
    refine ⟨?_, ?_⟩
    · rw [prev]
      exact twinAt r rMember
    · rwa [coveredBy_append_singleton] at next

lemma removedThrough_coveredBy (label : V → Fin m) (done pending : List (Fin m)) :
    removedThrough (coveredBy label done) (pending.map (bucket label)) = coveredBy label (done ++ pending) := by
  induction pending generalizing done with
  | nil => simp [removedThrough]
  | cons r tail ih =>
    change removedThrough (coveredBy label done ∪ bucket label r) (tail.map (bucket label)) = _
    rw [← coveredBy_append_singleton, ih]
    simp [List.append_assoc]

omit [DecidableRel G.Adj] in
lemma no_edges_after_branches (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (outputIndependent : Independent G (bucket label out)) :
    EdgelessAfter G (removedThrough ∅ (roots.map (bucket label))) := by
  rw [← coveredBy_nil label, removedThrough_coveredBy, List.nil_append]
  intro u v uNot vNot
  have hu : label u = out := (allRoots u).resolve_right (by simpa [coveredBy] using uNot)
  have hv : label v = out := (allRoots v).resolve_right (by simpa [coveredBy] using vNot)
  exact outputIndependent u (by simp [bucket, hu]) v (by simp [bucket, hv])

theorem roots_required (label : V → Fin m) (out : Fin m) (branches : Finset (Fin m)) (k : Nat)
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ branches)
    (beforeOut : ∀ r ∈ branches, r < out)
    (twinAt : ∀ r ∈ branches, TwinGroup G (below label r) (bucket label r))
    (outputIndependent : Independent G (bucket label out))
    (required : ∀ groups : List (Finset V), TwinSteps G ∅ groups →
      EdgelessAfter G (removedThrough ∅ groups) → k ≤ groups.length) : k ≤ branches.card := by
  let roots := branches.sort
  have sorted : roots.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v = out ∨ label v ∈ roots := by simpa [roots] using allRoots v
  have early (r) (member : r ∈ roots) : r < out := beforeOut r (by simpa [roots] using member)
  have twins (r) (member : r ∈ roots) : TwinGroup G (below label r) (bucket label r) :=
    twinAt r (by simpa [roots] using member)
  have valid : TwinSteps G ∅ (roots.map (bucket label)) := by
    simpa using sorted_tail_twin_steps G label out roots sorted covers early twins [] roots rfl
  have last := no_edges_after_branches G label out roots covers outputIndependent
  simpa [roots] using required (roots.map (bucket label)) valid last

end Graph

end BranchGroupsLean

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Stat.const false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc



end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem


def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp


theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩


theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_, ?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using elim_nonNotCount k pre (idStats k, [])) _)
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
    simp [nonNotCount]
  rw [hcount]
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]


end CircuitProof

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩

end PetersenCutTrace

namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x


structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)


theorem clean_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧ ∀ x, vl gs x o = f x := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]
    rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount, hacc] using elim_nonNotCount n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y

theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, Least n f gs o ∧ nonNotCount gs ≤ nonNotCount C.gates := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, count, he⟩ := clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, count, he, rfl⟩
  obtain ⟨gs', o', hc, hb, he', hl⟩ := Nat.find_spec existsAdmissible
  refine ⟨gs', o', ⟨hc, he', ?_⟩, hb⟩
  intro testGates testOut testClean testEval testCost
  have lower := Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates, testOut, testClean, testCost.trans hb, testEval, rfl⟩)
  exact hl.trans_le lower


theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount gs ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', hcost, he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs := by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'', o'', hc'', by omega, hcost.trans hkeep, fun y => by rw [he'' y, hagree y o ho]⟩

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩


theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
  omega

theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end LocalSection1

end CircuitProof.Readers

namespace CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

open CircuitProof.Readers

theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b]) : a ≠ b := by
  rintro rfl
  have hcl := L.hcl p g hg
  have hlt : a < m + p := by
    rcases hcl with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, hj, hk, h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg, hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]


end CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open CircuitProof.RunAsm

theorem least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w ≠ out) :
    ∃ p, Reads gs p w := by
  by_cases isInput : w < n
  · let v : Fin n := ⟨w, isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p := w - n
    have wire : w = n + p := by dsimp [p]; omega
    have pLt : p < gs.length := by omega
    have notOut : out ≠ n + p := by omega
    obtain ⟨q, _, read⟩ := least.live nonconstant p pLt notOut
    exact ⟨q, wire.symm ▸ read⟩

theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup := by
  obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [args]
  · have distinct := pq2f_nodup least nonconstant atSlot ops args
    simp [args, distinct]

theorem least_wire_readers_in_range {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val ≠ out) :
    ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ w.val ∈ g.inputs ∧ n + p < n + gs.length := by
  obtain ⟨p, g, hit, reads⟩ := least_wire_used least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound := (List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p, g, hit, reads, by omega⟩

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers

def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []

theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]

theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]

theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate

theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega

theorem predecessors_nodup {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y) (b : Fin (n + gs.length)) :
    (predecessors least.hcl b).Nodup := by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [predecessors_values least.hcl b internal]
    exact BranchBound.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have := b.isLt; omega))
  · simp [predecessors, internal]

end PetersenCutTrace

namespace PetersenScratch

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)

def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b

noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q

noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)

private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]

private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b

private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩

private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩

private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl

private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]

private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq

theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool := by
  classical
  exact decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

private theorem edgeValue_true {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true := by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u, v, h, hu, hv⟩

private theorem edgeValue_false_pair {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w, x w = true → w = u ∨ w = v) :
    edgeValue G x = false := by
  classical
  unfold edgeValue
  apply decide_eq_false
  rintro ⟨s, t, es, hs, ht⟩
  rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
  · exact G.irrefl es
  · exact h es
  · exact h es.symm
  · exact G.irrefl es

private theorem edge_pair_and {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (pairInput i j (fun _ => false) a b) = (a && b) := by
  cases a <;> cases b
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    simp [pairInput] at hk
  · apply edgeValue_false_pair (u := j) (v := j) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
    assumption
  · exact edgeValue_true h (by simp [pairInput]) (by simp [pairInput, h.ne.symm])

private theorem edge_pair_or {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i ≠ j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (pairInput i j (fun k => decide (k = u ∨ k = v)) a b) = (a || b) := by
  have hu : pairInput i j (fun k => decide (k = u ∨ k = v)) a b u = true := by
    simp [pairInput, hiu.ne.symm, huj]
  have hv : pairInput i j (fun k => decide (k = u ∨ k = v)) a b v = true := by
    simp [pairInput, hvi, hjv.ne.symm]
  cases a <;> cases b
  · apply edgeValue_false_pair huv
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk
    exact hk
  · exact edgeValue_true hjv (by simp [pairInput, hij.symm]) hv
  · exact edgeValue_true hiu (by simp [pairInput]) hu
  · exact edgeValue_true hiu (by simp [pairInput]) hu

theorem adjacent_cut_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (factors : ∀ base : Fin n → Bool, ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue i j base p a b) = edgeValue G (pairInput i j base a b)) : False := by
  obtain ⟨outerA, ha⟩ := factors (fun _ => false)
  obtain ⟨outerO, ho⟩ := factors (fun k => decide (k = u ∨ k = v))
  exact fixed_pair_invariant i j p hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (edge_pair_and hij a b))
    (fun a b => (ho a b).trans (edge_pair_or hij.ne hiu hjv huj hvi huv a b))

end PetersenScratch

namespace PetersenCutFormula

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl

end PetersenCutFormula

namespace PetersenCutIndependent

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch

theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]

theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

theorem adjacent_cut_excluded {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (hi : occurrences i (wireFormula i gs cut.val) ≤ 1)
    (hj : occurrences j (wireFormula i gs cut.val) ≤ 1)
    (controlled : cut = out ∨ ∀ k : Fin n, (k = i ∨ k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out) : False := by
  refine adjacent_cut_invariant G i j u v hij hiu hjv huj hvi huv
    (wireFormula i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f, hf⟩ := cut_factors hcl cut out (fun k => k = i ∨ k = j) base controlled
  refine ⟨f, fun a b => ?_⟩
  have agree : ∀ k, ¬ (k = i ∨ k = j) → pairInput i j base a b k = base k := by
    intro k hk
    simp [pairInput, show k ≠ i from fun e => hk (Or.inl e),
      show k ≠ j from fun e => hk (Or.inr e)]
  unfold pairValue
  rw [wireFormula_eval i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)

end PetersenCutIndependent

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b

def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v

def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)

variable (forward : ∀ {v w : Fin m}, reads v w → v < w)
variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)

include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩

include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB

noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)

theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩

theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩

lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)

section Count

variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)

include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge

include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)

end Count

end FirstBranchRoute

namespace PetersenFirstGroup

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch

noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)

noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut

theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]

theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w

theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl

theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path

theorem firstInputGroup_independent {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (witnesses : ∀ i j, G.Adj i j → ∃ u v,
      G.Adj i u ∧ G.Adj j v ∧ u ≠ j ∧ v ≠ i ∧ ¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut) := by
  intro i iIn j jIn adjacent
  obtain ⟨u, v, hiu, hjv, huj, hvi, huv⟩ := witnesses i j adjacent
  have iFirst := (mem_firstInputGroup clean out live cut i).mp iIn
  have jFirst := (mem_firstInputGroup clean out live cut j).mp jIn
  have iCount := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have jCount := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [iFirst] at iCount
  rw [jFirst] at jCount
  refine adjacent_cut_excluded clean G cut out computes i j u v adjacent hiu hjv huj hvi
    huv iCount jCount ?_
  rcases firstInputGroup_controlled clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))

end PetersenFirstGroup

namespace PetersenNine

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


abbrev Vertex := Fin 9
abbrev Edges := List (Vertex × Vertex)


def edges : Edges := [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)]

def edgeFun (es : Edges) (x : Vertex → Bool) : Bool :=
  es.any (fun edge => x edge.1 && x edge.2)


lemma noLoops : ∀ e ∈ edges, e.1 ≠ e.2 := by decide

lemma edgeFun_true (es : Edges) (x : Vertex → Bool) :
    edgeFun es x = true ↔ ∃ a b, (a, b) ∈ es ∧ x a = true ∧ x b = true := by
  simp only [edgeFun, List.any_eq_true, Bool.and_eq_true, Prod.exists]


def graph (es : Edges) (noSelf : ∀ e ∈ es, e.1 ≠ e.2) : SimpleGraph Vertex where
  Adj a b := (a, b) ∈ es ∨ (b, a) ∈ es
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun he => noSelf (v, v) he rfl) (fun he => noSelf (v, v) he rfl)⟩

end PetersenNine

namespace PetersenGroupBFS

structure MaskGraph where
  width : Nat
  adjacency : Nat → Nat

def bit (vertex : Nat) : Nat :=
  Nat.shiftLeft 1 vertex

def fullMask (g : MaskGraph) : Nat :=
  bit g.width - 1

def residualNeighbors (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  Nat.land (g.adjacency vertex) (Nat.xor (fullMask g) deleted)

def closeIsolates (g : MaskGraph) (deleted : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if residualNeighbors g deleted v = 0 then Nat.lor mask (bit v) else mask)
    deleted

def twinClass (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if !(Nat.testBit deleted v) &&
        (residualNeighbors g deleted v == residualNeighbors g deleted vertex)
      then Nat.lor mask (bit v) else mask)
    0

theorem bit_at (v w : Nat) : (bit v).testBit w = decide (v = w) := by
  simp [bit, Nat.shiftLeft_eq, Nat.testBit_two_pow]

theorem full_at (g : MaskGraph) (w : Nat) :
    (fullMask g).testBit w = decide (w < g.width) := by
  simp [fullMask, bit, Nat.shiftLeft_eq]

theorem neighbor_at (g : MaskGraph) (deleted v w : Nat) (hw : w < g.width) :
    (residualNeighbors g deleted v).testBit w =
      ((g.adjacency v).testBit w && !(deleted.testBit w)) := by
  simp [residualNeighbors, Nat.testBit_xor, full_at, hw]

private theorem fold_mask_at (vertices : List Nat) (p : Nat → Prop) [DecidablePred p]
    (initial w : Nat) :
    (vertices.foldl (fun m v => if p v then Nat.lor m (bit v) else m) initial).testBit w =
      (initial.testBit w || (vertices.any fun v => decide (p v) && (v == w))) := by
  induction vertices generalizing initial with
  | nil => simp
  | cons v vertices ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]
    by_cases h : p v <;> simp [h, bit_at, Bool.or_assoc, Bool.beq_eq_decide_eq]

private theorem any_mask_at (p : Nat → Prop) [DecidablePred p] (n w : Nat) :
    ((List.range n).any fun v => decide (p v) && (v == w)) =
      (decide (w < n) && decide (p w)) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, Bool.and_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨v, hv, hp, rfl⟩
    exact ⟨hv, hp⟩
  · rintro ⟨hw, hp⟩
    exact ⟨w, hw, hp, rfl⟩

theorem close_at (g : MaskGraph) (deleted w : Nat) :
    (closeIsolates g deleted).testBit w =
      (deleted.testBit w || (decide (w < g.width) && decide (residualNeighbors g deleted w = 0))) := by
  unfold closeIsolates
  rw [fold_mask_at, any_mask_at]

theorem class_at (g : MaskGraph) (deleted v w : Nat) :
    (twinClass g deleted v).testBit w =
      (decide (w < g.width) &&
        (!(deleted.testBit w) && (residualNeighbors g deleted w == residualNeighbors g deleted v))) := by
  unfold twinClass
  rw [fold_mask_at, any_mask_at]
  simp [Bool.beq_eq_decide_eq]

theorem bit_eq_power (width : Nat) : bit width = 2 ^ width := by
  simp [bit, Nat.shiftLeft_eq]

theorem lor_bounded {width a b : Nat} (ha : a < bit width) (hb : b < bit width) :
    Nat.lor a b < bit width := by
  rw [bit_eq_power] at ha hb ⊢
  exact Nat.or_lt_two_pow ha hb

theorem high_false {width m w : Nat} (hm : m < bit width) (hw : width ≤ w) :
    m.testBit w = false := by
  rw [bit_eq_power] at hm
  exact Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) hw))

theorem mask_ext {width a b : Nat} (ha : a < bit width) (hb : b < bit width)
    (same : ∀ w < width, a.testBit w = b.testBit w) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro w
  by_cases hw : w < width
  · exact same w hw
  · rw [high_false ha (Nat.le_of_not_gt hw), high_false hb (Nat.le_of_not_gt hw)]

theorem neighbor_bounded (g : MaskGraph) (deleted v : Nat) (hd : deleted < bit g.width) :
    residualNeighbors g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [residualNeighbors, full_at, Nat.not_lt_of_ge hw, high_false hd hw]

theorem close_bounded (g : MaskGraph) (deleted : Nat) (hd : deleted < bit g.width) :
    closeIsolates g deleted < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [close_at, Nat.not_lt_of_ge hw, high_false hd hw]

theorem class_bounded (g : MaskGraph) (deleted v : Nat) :
    twinClass g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [class_at, Nat.not_lt_of_ge hw]

def step (g : MaskGraph) (deleted : Nat) : List Nat :=
  deleted :: (List.range g.width).filterMap fun v =>
    if !(Nat.testBit deleted v) && (residualNeighbors g deleted v != 0)
    then some (closeIsolates g (Nat.lor deleted (twinClass g deleted v)))
    else none

def frontier (g : MaskGraph) : Nat → List Nat
  | 0 => [closeIsolates g 0]
  | depth + 1 => ((frontier g depth).flatMap (step g)).eraseDups

theorem advance {g : MaskGraph} {depth deleted next : Nat}
    (hd : deleted ∈ frontier g depth) (hs : next ∈ step g deleted) :
    next ∈ frontier g (depth + 1) := by
  rw [frontier, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨deleted, hd, hs⟩

theorem stay {g : MaskGraph} {depth deleted : Nat} (hd : deleted ∈ frontier g depth) :
    deleted ∈ frontier g (depth + 1) :=
  advance hd (by simp [step])

theorem advance_class {g : MaskGraph} {depth deleted vertex : Nat}
    (hd : deleted ∈ frontier g depth) (hv : vertex < g.width)
    (hlive : Nat.testBit deleted vertex = false)
    (hne : residualNeighbors g deleted vertex ≠ 0) :
    closeIsolates g (Nat.lor deleted (twinClass g deleted vertex)) ∈ frontier g (depth + 1) := by
  apply advance hd
  apply List.mem_cons_of_mem
  rw [List.mem_filterMap]
  refine ⟨vertex, List.mem_range.mpr hv, ?_⟩
  simp [hlive, hne]

def petersenNine : MaskGraph :=
  ⟨9, fun v => (#[50, 69, 138, 276, 9, 385, 258, 36, 104] : Array Nat)[v]?.getD 0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem petersen_nine_no_four : fullMask petersenNine ∉ frontier petersenNine 4 := by
  decide +kernel

end PetersenGroupBFS

namespace PetersenMaskBridge

open PetersenGroupBFS
open BranchGraph

def decode (g : MaskGraph) (mask : Nat) : Finset (Fin g.width) :=
  Finset.univ.filter (fun v => mask.testBit v.val)

@[simp] lemma mem_decode (g : MaskGraph) (mask : Nat) (v : Fin g.width) :
    v ∈ decode g mask ↔ mask.testBit v.val = true := by
  simp [decode]

@[simp] lemma decode_zero (g : MaskGraph) : decode g 0 = ∅ := by
  ext v
  simp

@[simp] lemma decode_full (g : MaskGraph) : decode g (fullMask g) = Finset.univ := by
  ext v
  simp [full_at, v.isLt]

lemma decode_or (g : MaskGraph) (a b : Nat) :
    decode g (Nat.lor a b) = decode g a ∪ decode g b := by
  ext v
  simp [Bool.or_eq_true]

lemma decode_inj (g : MaskGraph) {a b : Nat} (ha : a < bit g.width) (hb : b < bit g.width)
    (same : decode g a = decode g b) : a = b := by
  apply mask_ext ha hb
  intro w hw
  have hm : (⟨w, hw⟩ : Fin g.width) ∈ decode g a ↔ (⟨w, hw⟩ : Fin g.width) ∈ decode g b := by
    rw [same]
  simp only [mem_decode] at hm
  exact Bool.eq_iff_iff.mpr hm

lemma bit_pos (n : Nat) : 0 < bit n := by
  rw [bit_eq_power]
  exact Nat.two_pow_pos n

lemma full_bounded (g : MaskGraph) : fullMask g < bit g.width := by
  unfold fullMask
  have := bit_pos g.width
  omega

section Graph

variable (g : MaskGraph) (G : SimpleGraph (Fin g.width)) [DecidableRel G.Adj]
variable (adj : ∀ u v : Fin g.width, G.Adj u v ↔ (g.adjacency u.val).testBit v.val = true)

include adj in
lemma decode_neighbors (deleted : Nat) (u : Fin g.width) :
    decode g (residualNeighbors g deleted u.val) = neighborsAfter G (decode g deleted) u := by
  ext v
  cases h : deleted.testBit v.val <;>
    simp [mem_decode, neighborsAfter, neighbor_at g deleted u.val v.val v.isLt, adj, h]

include adj in
lemma residual_zero_iff (deleted : Nat) (bound : deleted < bit g.width) (u : Fin g.width) :
    residualNeighbors g deleted u.val = 0 ↔ neighborsAfter G (decode g deleted) u = ∅ := by
  constructor
  · intro h
    rw [← decode_neighbors g G adj, h, decode_zero]
  · intro h
    apply decode_inj g (neighbor_bounded g deleted u.val bound) (bit_pos g.width)
    rw [decode_neighbors g G adj, h, decode_zero]

include adj in
lemma decode_close (deleted : Nat) (bound : deleted < bit g.width) :
    decode g (PetersenGroupBFS.closeIsolates g deleted) = BranchGraph.closeIsolates G (decode g deleted) := by
  ext v
  simp [close_at, v.isLt, BranchGraph.closeIsolates, isolates, Bool.or_eq_true,
    residual_zero_iff g G adj deleted bound]

include adj in
lemma decode_class (deleted : Nat) (bound : deleted < bit g.width) (root : Fin g.width)
    (outside : root ∉ decode g deleted) (live : (neighborsAfter G (decode g deleted) root).Nonempty) :
    decode g (twinClass g deleted root.val) = maximalClass G (decode g deleted) root := by
  have same (u : Fin g.width) : residualNeighbors g deleted u.val = residualNeighbors g deleted root.val ↔
      neighborsAfter G (decode g deleted) u = neighborsAfter G (decode g deleted) root := by
    rw [← decode_neighbors g G adj deleted u, ← decode_neighbors g G adj deleted root]
    exact ⟨congrArg (decode g), decode_inj g (neighbor_bounded g deleted u.val bound)
      (neighbor_bounded g deleted root.val bound)⟩
  ext v
  cases h : deleted.testBit v.val <;>
    simp [class_at, v.isLt, maximalClass, outside, live, h, same, Bool.beq_eq_decide_eq]

def Represented (depth : Nat) (removed : Finset (Fin g.width)) : Prop :=
  ∃ m, m ∈ frontier g depth ∧ m < bit g.width ∧ decode g m = removed

include adj in
lemma initial_rep : Represented g 0 (BranchGraph.closeIsolates G ∅) := by
  refine ⟨PetersenGroupBFS.closeIsolates g 0, ?_,
    close_bounded g 0 (bit_pos g.width), ?_⟩
  · change PetersenGroupBFS.closeIsolates g 0 ∈ [PetersenGroupBFS.closeIsolates g 0]
    exact List.mem_cons_self
  · rw [decode_close g G adj _ (bit_pos g.width), decode_zero]

include adj in
lemma advance_rep {depth : Nat} {removed : Finset (Fin g.width)} (root : Fin g.width)
    (rep : Represented g depth removed) (closed : BranchGraph.closeIsolates G removed = removed) :
    Represented g (depth + 1) (removeClass G removed root) := by
  obtain ⟨m, hm, bounded, same⟩ := rep
  subst removed
  by_cases active : root ∉ decode g m ∧ (neighborsAfter G (decode g m) root).Nonempty
  · have live : m.testBit root.val = false := by
      cases h : m.testBit root.val
      · rfl
      · exact (active.1 ((mem_decode g m root).mpr h)).elim
    have someNeighbor : residualNeighbors g m root.val ≠ 0 := by
      intro h
      have none := (residual_zero_iff g G adj m bounded root).mp h
      simpa [none] using active.2
    have united := lor_bounded bounded (class_bounded g m root.val)
    refine ⟨PetersenGroupBFS.closeIsolates g (Nat.lor m (twinClass g m root.val)),
      advance_class hm root.isLt live someNeighbor, close_bounded g _ united, ?_⟩
    rw [decode_close g G adj _ united, decode_or, decode_class g G adj m bounded root active.1 active.2,
      removeClass]
  · have sameRemoval : removeClass G (decode g m) root = decode g m := by
      have emptyClass : maximalClass G (decode g m) root = ∅ := ite_eq_right active
      simp only [removeClass, emptyClass, Finset.union_empty, closed]
    exact ⟨m, stay hm, bounded, sameRemoval.symm⟩

include adj in
lemma simulate {count depth : Nat} {start finish : Finset (Fin g.width)}
    (walk : ClassSteps G count start finish) (initial : Represented g depth start)
    (closed : BranchGraph.closeIsolates G start = start) : Represented g (depth + count) finish := by
  induction count generalizing depth start with
  | zero =>
    change finish = start at walk
    simpa only [walk, Nat.add_zero] using initial
  | succ count ih =>
    obtain ⟨root, next⟩ := walk
    have nextClosed : BranchGraph.closeIsolates G (removeClass G start root) = removeClass G start root :=
      closeIsolates_idempotent G _
    have rest := ih next (advance_rep g G adj root initial closed) nextClosed
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using rest

lemma frontier_up {m k r : Nat} (reached : m ∈ frontier g k) (budget : k ≤ r) : m ∈ frontier g r := by
  induction r with
  | zero =>
    have : k = 0 := by omega
    simpa only [this] using reached
  | succ r ih =>
    by_cases eq : k = r + 1
    · simpa [eq] using reached
    · exact stay (ih (by omega))

include adj in
theorem groups_exceed_budget [Nonempty (Fin g.width)] (k : Nat) (noFinish : fullMask g ∉ frontier g k)
    (groups : List (Finset (Fin g.width))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : k < groups.length := by
  by_contra! budget
  have walk := covering_sequence_reaches_univ G groups twins finished
  obtain ⟨m, reached, bound, allGone⟩ :=
    simulate g G adj walk (initial_rep g G adj) (closeIsolates_idempotent G ∅)
  have equal : m = fullMask g := decode_inj g bound (full_bounded g) (by simpa using allGone)
  rw [equal, Nat.zero_add] at reached
  exact noFinish (frontier_up g reached budget)

end Graph

theorem petersen_nine_groups_need_five (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (adj : ∀ u v : Fin 9, G.Adj u v ↔ (petersenNine.adjacency u.val).testBit v.val = true)
    (groups : List (Finset (Fin 9))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : 5 ≤ groups.length :=
  @groups_exceed_budget petersenNine G (inferInstance : DecidableRel G.Adj) adj
    (inferInstance : Nonempty (Fin 9)) 4 petersen_nine_no_four groups twins finished

end PetersenMaskBridge

open PetersenNine

def petersenGraph : SimpleGraph Vertex := graph edges noLoops

def petersenAdjDecidable : DecidableRel petersenGraph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges ∨ (b, a) ∈ edges))

theorem petersen_graph_marked_edges (S : Finset Vertex) :
    edgeFun edges (fun i => decide (i ∈ S)) = true ↔
      BranchGraph.containsEdge petersenGraph S := by
  constructor
  · intro h
    obtain ⟨a, b, edge, ha, hb⟩ := (edgeFun_true edges _).mp h
    exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, Or.inl edge⟩
  · rintro ⟨a, ha, b, hb, adjacent⟩
    change (a, b) ∈ edges ∨ (b, a) ∈ edges at adjacent
    apply (edgeFun_true edges _).mpr
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, decide_eq_true ha, decide_eq_true hb⟩
    · exact ⟨b, a, edge, decide_eq_true hb, decide_eq_true ha⟩

theorem petersen_graph_matches_mask :
    ∀ a b : Vertex, petersenGraph.Adj a b ↔
      (PetersenGroupBFS.petersenNine.adjacency a.val).testBit b.val = true := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide

theorem petersen_graph_alternate_neighbors :
    ∀ i j : Vertex, petersenGraph.Adj i j →
      ∃ u v, petersenGraph.Adj i u ∧ petersenGraph.Adj j v ∧
        u ≠ j ∧ v ≠ i ∧ ¬ petersenGraph.Adj u v := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs


def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length

theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩

theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega

theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega

theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]

theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound

theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace

theorem least_read_edge_live {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length), w ≠ (⟨out, outValid⟩ : Fin (n + gs.length)) → ∃ v, readEdge gs w v := by
  intro w notOutput
  have notSame : w.val ≠ out := fun eq => notOutput (Fin.ext eq)
  obtain ⟨p, g, atSlot, reads, bound⟩ :=
    least_wire_readers_in_range least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p, bound⟩, p, g, atSlot, rfl, reads⟩

theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))

noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w

theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]


def classAt {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut

def classesBefore {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut

theorem class_mem {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ classAt label cut ↔ label v = cut := by
  simp [classAt]

theorem classes_before_mem {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ classesBefore label cut ↔ label v < cut := by
  simp [classesBefore]

theorem class_twins_of_later_factor {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → W) (cut : W)
    (independent : BranchGraph.Independent G (classAt label cut))
    (code : Finset V → Bool) (decode : Bool → Finset V → Prop)
    (factors : ∀ I O : Finset V, (∀ i ∈ I, label i = cut) →
      (∀ i ∈ O, cut < label i) → (BranchGraph.containsEdge G (I ∪ O) ↔ decode (code I) O)) :
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ classAt label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ classesBefore label cut) : cut < label y := by
    have ne : label y ≠ cut := fun equal =>
      independent x xGroup y ((class_mem label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut := fun h => notEarlier ((classes_before_mem label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ classAt label cut) (yLater : cut < label y) :
      (G.Adj x y ↔ decode (code {x}) {y}) := by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut := by
      have eq : i = x := Finset.mem_singleton.mp mem
      subst i
      exact (class_mem label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i := by
      have eq : i = y := Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ classAt label cut)
      (active : (BranchGraph.neighborsAfter G (classesBefore label cut) x).Nonempty) :
      code {x} ≠ code ∅ := by
    obtain ⟨y, neighbor⟩ := active
    simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at neighbor
    have yLater := later xGroup neighbor.1 neighbor.2
    have yes := (single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one := (factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a := cannot u uGroup uActive
  have b := cannot v vGroup vActive
  have sameCode : code {u} = code {v} := by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨edge, remains⟩
    have pos := later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_, remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge, remains⟩
    have pos := later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_, remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds CircuitProof
open Relation

theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i, ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val := by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n := ⟨w.val, input⟩
      have name : inputWire gs i = w := Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w := by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a := agree i atInput
      simpa only [vl_input gs x w.val input, vl_input gs y w.val input] using a
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore := (clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length) := ⟨a, by have := w.isLt; omega⟩
      have read : readEdge gs wire w := ⟨p, g, atGate, gateWire, inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)

end PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation

def setInput {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)

theorem finite_branch_bit_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool, ∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I, label i = cut) → (∀ i ∈ O, cut < label i) →
        (vl gs (setInput (I ∪ O)) out.val = true ↔ decode (code I) O) := by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)) := vl gs (setInput I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n), (∀ j ∈ J, label j = cut) ∧ code J = b ∧
      vl gs (setInput (J ∪ O)) out.val = true
  refine ⟨code, decode, ?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I, label i = cut) at groupI
  change (∀ i ∈ O, cut < label i) at afterO
  change (_ ↔ decode (code I) O)
  constructor
  · exact fun yes => ⟨I, groupI, rfl, yes⟩
  · rintro ⟨J, groupJ, sameCode, yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (K ∪ O)) cut.val = code K := by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O := fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput, absent]
    have sameCut : vl gs (setInput (I ∪ O)) cut.val = vl gs (setInput (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out := lt_of_le_of_ne prior atOutput
    have eq := circuit_cut_agreement clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut := by
        by_contra offGroup
        have notI : i ∉ I := fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J := fun mem => offGroup (groupJ i mem)
        exact diff (by simp [setInput, notI, notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
          (inputWire gs i) = cut := isGroup
      have forbid := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
        (v := inputWire gs i) (w := out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b, avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
        fun _ _ h => ⟨h.1, h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]

open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace

theorem circuit_branch_class_twins {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n), vl gs (setInput S) out.val = true ↔ BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (independent : BranchGraph.Independent G
      (classAt (fun i => FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)) cut)) :
    let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  obtain ⟨code, decode, factors⟩ := finite_branch_bit_factor clean out live cut prior terminal
  change BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut)
  exact class_twins_of_later_factor G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

abbrev petersenF := edgeFun edges

private theorem petersen_dependency_samples : ∀ v : Vertex, ∃ w : Vertex,
    petersenF (Function.update (fun i => decide (i = w)) v
      (!(decide (v = w)))) ≠ petersenF (fun i => decide (i = w)) := by
  decide +kernel

theorem petersen_depends (v : Vertex) : Dep petersenF v := by
  obtain ⟨w, hw⟩ := petersen_dependency_samples v
  exact ⟨fun i => decide (i = w), hw⟩

theorem petersen_nonconstant : ∃ x y : Vertex → Bool, petersenF x ≠ petersenF y :=
  dep_nc (petersen_depends 0)

private theorem petersen_cofactor_samples : ∀ (v : Vertex) (b : Bool),
    petersenF (Function.update (fun _ => false) v b) = false ∧
    petersenF (Function.update (fun _ => true) v b) = true := by
  decide +kernel

theorem petersen_restrict_nonconstant (v : Vertex) (b : Bool) :
    ∃ x y, petersenF (Function.update x v b) ≠ petersenF (Function.update y v b) := by
  obtain ⟨no, yes⟩ := petersen_cofactor_samples v b
  exact ⟨fun _ => false, fun _ => true, by rw [no, yes]; decide⟩


lemma petersenF_graph_edges (x : Fin 9 → Bool) : petersenF x = true ↔
    ∃ u v : Fin 9, petersenGraph.Adj u v ∧ x u = true ∧ x v = true := by
  change PetersenNine.edgeFun PetersenNine.edges x = true ↔ _
  rw [PetersenNine.edgeFun_true]
  constructor
  · rintro ⟨a, b, edge, ha, hb⟩
    exact ⟨a, b, Or.inl edge, ha, hb⟩
  · rintro ⟨a, b, adjacent, ha, hb⟩
    change (a, b) ∈ PetersenNine.edges ∨ (b, a) ∈ PetersenNine.edges at adjacent
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, ha, hb⟩
    · exact ⟨b, a, edge, hb, ha⟩

lemma least_petersen_output_valid {gs : List Gate} {out : Nat} (least : Least 9 petersenF gs out) :
    out < 9 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv petersen_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

theorem least_petersen_five_branches (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    : 5 ≤ (circuitBranchWires (n := 9) gs).card := by
  classical
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  have outValid := least_petersen_output_valid least
  let outWire : Fin (9 + gs.length) := ⟨out, outValid⟩
  have live := least_read_edge_live least petersen_nonconstant petersen_depends petersen_restrict_nonconstant outValid
  let label : Fin 9 → Fin (9 + gs.length) := firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (9 + gs.length)) := circuitBranchWires gs
  have computes (x : Fin 9 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue petersenGraph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, petersenF_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset (Fin 9)) : vl gs (setInput S) outWire.val = true ↔
      BranchGraph.containsEdge petersenGraph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev]
    exact petersen_graph_marked_edges S
  have independent (r) : BranchGraph.Independent petersenGraph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least petersen_nonconstant)
      petersenGraph computes petersen_graph_alternate_neighbors r
  have labels (v : Fin 9) : label v = outWire ∨ label v ∈ branches := by
    have stopped := FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (in_circuit_branches.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup petersenGraph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live petersenGraph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp member)) (independent r)
  exact BranchGroupsLean.roots_required petersenGraph label outWire branches 5 labels before twins
    (independent outWire) (PetersenMaskBridge.petersen_nine_groups_need_five petersenGraph petersen_graph_matches_mask)

lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega

lemma nonNotCount_replace_not (gs : List Gate) (p : ℕ) (hp : p < gs.length)
    (hn : gs[p].op = .not) :
    nonNotCount (gs.set p ⟨.and, []⟩) = nonNotCount gs + 1 := by
  simp [nonNotCount, List.countP_set hp, hn, isNotGate]

lemma nonNotCount_three_not (gs : List Gate) (i j k : Fin gs.length)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : (gs.get i).op = .not) (hj : (gs.get j).op = .not)
    (hk : (gs.get k).op = .not) : nonNotCount gs + 3 ≤ gs.length := by
  let g : Gate := ⟨.and, []⟩
  let gs' := gs.set i.val g
  let gs'' := gs'.set j.val g
  let gs''' := gs''.set k.val g
  have hj' : j.val < gs'.length := by simpa [gs'] using j.isLt
  have hk' : k.val < gs'.length := by simpa [gs'] using k.isLt
  have hk'' : k.val < gs''.length := by simpa [gs''] using hk'
  have cmp_i := nonNotCount_replace_not gs i.val i.isLt hi
  have cmp_j := nonNotCount_replace_not gs' j.val hj' (by
    rw [show gs'[j.val] = gs[j.val] from List.getElem_set_ne (fun h => hij (Fin.ext h)) hj']
    exact hj)
  have cmp_k := nonNotCount_replace_not gs'' k.val hk'' (by
    rw [show gs''[k.val] = gs'[k.val] from List.getElem_set_ne (fun h => hjk (Fin.ext h)) hk'',
        show gs'[k.val] = gs[k.val] from List.getElem_set_ne (fun h => hik (Fin.ext h)) hk']
    exact hk)
  change nonNotCount gs' = nonNotCount gs + 1 at cmp_i
  change nonNotCount gs'' = nonNotCount gs' + 1 at cmp_j
  change nonNotCount gs''' = nonNotCount gs'' + 1 at cmp_k
  have hbound : nonNotCount gs''' ≤ gs.length := by
    simpa [nonNotCount, gs''', gs'', gs', g] using
      (List.countP_le_length (p := fun q : Gate => !(isNotGate q.op)) (l := gs'''))
  omega

theorem petersen_binary_lower (C : Circuit) (hfan : FanInTwo C)
    (he : ∀ x : Vertex → Bool, C.eval (List.ofFn x) = petersenF x) :
    13 ≤ nonNotCount C.gates := by
  obtain ⟨gs, o, least, budget⟩ := least_with_budget C hfan he petersen_nonconstant
  have valid := least_petersen_output_valid least
  have live := least_read_edge_live least petersen_nonconstant petersen_depends
    petersen_restrict_nonconstant valid
  let branches := circuitBranchWires (n := 9) gs
  have branchLower : 5 ≤ branches.card := least_petersen_five_branches gs o least
  have branchBudget := branching_budget least.hcl valid (fun w hw hne => by
      let wire : Fin (9 + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
  have countTotal := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at countTotal
  omega


namespace PetersenScratch
theorem three_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, (a && b) = false → outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    simp only [hO false false rfl, hO true false rfl] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    simp only [hO false false rfl, hO false true rfl] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    simp only [hO false false rfl, hO false true rfl] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

end PetersenScratch
theorem thin_twins {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → W) (cut : W)
    (independent : BranchGraph.Independent G (classAt label cut))
    (code : Finset V → Bool) (decode : Bool → Finset V → Prop)
    (factors : ∀ I O : Finset V, I.card ≤ 1 → O.card ≤ 1 → (∀ i ∈ I, label i = cut) →
      (∀ i ∈ O, cut < label i) → (BranchGraph.containsEdge G (I ∪ O) ↔ decode (code I) O)) :
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ classAt label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ classesBefore label cut) : cut < label y := by
    have ne : label y ≠ cut := fun equal =>
      independent x xGroup y ((class_mem label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut := fun h => notEarlier ((classes_before_mem label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ classAt label cut) (yLater : cut < label y) :
      (G.Adj x y ↔ decode (code {x}) {y}) := by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut := by
      have eq : i = x := Finset.mem_singleton.mp mem
      subst i
      exact (class_mem label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i := by
      have eq : i = y := Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} (by simp) (by simp) g h
  have cannot (x : V) (xGroup : x ∈ classAt label cut)
      (active : (BranchGraph.neighborsAfter G (classesBefore label cut) x).Nonempty) :
      code {x} ≠ code ∅ := by
    obtain ⟨y, neighbor⟩ := active
    simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at neighbor
    have yLater := later xGroup neighbor.1 neighbor.2
    have yes := (single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one := (factors ∅ {y} (by simp) (by simp) (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a := cannot u uGroup uActive
  have b := cannot v vGroup vActive
  have sameCode : code {u} = code {v} := by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨edge, remains⟩
    have pos := later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_, remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge, remains⟩
    have pos := later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_, remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge

end BranchBound


namespace BranchBound
open BranchGroupsLean

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

theorem output_complement (label : V → Fin m) (out : Fin m) (branches : Finset (Fin m))
    (labels : ∀ v, label v = out ∨ label v ∈ branches)
    (before : ∀ r ∈ branches, r < out) :
    Finset.univ \ below label out = bucket label out := by
  ext v
  simp only [below,bucket,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
  rcases labels v with h|h
  · simp [h]
  · have lt := before (label v) h
    simp [lt,ne_of_lt lt]

theorem ordered_rank_required (label : V → Fin m) (out : Fin m) (branches : Finset (Fin m))
    (P : ℕ → Finset V → Prop) (k : ℕ)
    (labels : ∀ v, label v = out ∨ label v ∈ branches)
    (before : ∀ r ∈ branches, r < out)
    (initial : P 0 ∅)
    (advance : ∀ d < k, ∀ r ∈ branches, P d (below label r) →
      P (d+1) (below label r ∪ bucket label r))
    (exclude : ∀ d ≤ k, P d (below label out) → False) : k < branches.card := by
  by_contra! budget
  let roots := branches.sort
  have sorted : roots.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v = out ∨ label v ∈ roots := by simpa [roots] using labels v
  have whole : coveredBy label roots = below label out := by
    ext v
    simp only [coveredBy,below,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h
      exact before _ (by simpa [roots] using h)
    · intro h
      exact (covers v).resolve_left (ne_of_lt h)
  have step (done todo : List (Fin m)) (complete : done ++ todo = roots)
      (rank : P done.length (coveredBy label done)) : False := by
    induction todo generalizing done with
    | nil =>
      simp only [List.append_nil] at complete
      subst done
      rw [whole] at rank
      exact exclude roots.length (by simpa [roots] using budget) rank
    | cons r rs ih =>
      have mem : r ∈ roots := complete ▸ List.mem_append_right done List.mem_cons_self
      have member : r ∈ branches := by simpa [roots] using mem
      have late := covered_before_of_sorted label out done rs r (by simpa only [complete] using sorted)
        (fun v => by simpa only [complete] using covers v) (before r member)
      have len := congrArg List.length complete
      have total : roots.length = branches.card := by simp [roots]
      simp only [List.length_append,List.length_cons] at len
      have next := advance done.length (by omega) r member (late ▸ rank)
      apply ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
      simpa [coveredBy_append_singleton,late] using next
  exact step [] roots (by simp) (by simpa using initial)

end BranchBound

namespace BranchBound
open PetersenNine PetersenCutTrace PetersenFirstGroup CircuitProof CircuitProof.Readers PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PartialAND
open PetersenScratch PetersenCutFormula PetersenCutIndependent Relation
def good (x : Vertex → Bool) := x 0 || x 1 || x 4 || x 5
local instance : DecidableRel petersenGraph.Adj := petersenAdjDecidable
def compatible (f : (Vertex → Bool) → Bool) := ∀ x, good x = true → f x = petersenF x

private def uni (p : Bool → Bool → Bool) :=
  (∀ b, p false b ≤ p true b) ∨ (∀ b, p true b ≤ p false b)

private theorem mergeUni : ∀ (s : Bool) (p q : Bool → Bool → Bool),
    ((∀ b, p false b=p true b) ∧ uni q ∨ uni p ∧ (∀ b, q false b=q true b)) →
    uni (fun a b => binOp s (p a b) (q a b)) := by unfold uni binOp; decide

private theorem invariant {n} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (count : occurrences i p ≤ 1) : uni (pairValue i j base p) := by
  induction p with
  | lit k sign =>
    by_cases eq : k=i
    · subst k
      cases sign <;> simp [uni,pairValue,DMFormula.eval,pairInput]
    · left
      intro b
      simp [pairValue,DMFormula.eval,pairInput,eq]
  | and p q ihp ihq =>
    change uni (fun a b => binOp true (pairValue i j base p a b) (pairValue i j base q a b))
    apply mergeUni
    change occurrences i p + occurrences i q ≤ 1 at count
    by_cases e : occurrences i p=0
    · exact Or.inl ⟨fun b => PetersenScratch.absent_left e false true b,ihq (by omega)⟩
    · exact Or.inr ⟨ihp (by omega),fun b => PetersenScratch.absent_left (by omega) false true b⟩
  | or p q ihp ihq =>
    change uni (fun a b => binOp false (pairValue i j base p a b) (pairValue i j base q a b))
    apply mergeUni
    change occurrences i p + occurrences i q ≤ 1 at count
    by_cases e : occurrences i p=0
    · exact Or.inl ⟨fun b => PetersenScratch.absent_left e false true b,ihq (by omega)⟩
    · exact Or.inr ⟨ihp (by omega),fun b => PetersenScratch.absent_left (by omega) false true b⟩

private theorem completeCorner : ∀ (p : Bool → Bool → Bool) (o : Bool → Bool), uni p →
    (∀ a b : Bool, (a || b) = true → o (p a b) = (a && b)) →
    ∀ a b, o (p a b) = (a && b) := by unfold uni; decide

private def baseOf (m : Nat) (i : Vertex) := m.testBit i.val
private def andBase (i j : Vertex) : Nat := (#[0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,16,0,0,0,16,0,1,0,0,0,1,0,0,0,1,0,2,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,16,0,0,0,0,0,0,1,0,0,1,0,0,2,0,0,0,0,0,0,1,0,2,1,0,0] : Array Nat)[i.val*9+j.val]?.getD 0
private def orBase (i j : Vertex) : Nat := (#[0,20,2,16,10,130,2,20,10,20,0,9,5,1,1,257,5,9,2,9,0,18,9,9,2,34,9,16,5,18,0,5,5,18,5,36,10,1,9,5,0,1,10,5,9,130,1,9,5,1,0,130,5,9,2,257,2,18,10,130,0,34,10,20,5,34,5,5,5,34,0,32,10,9,9,36,9,9,10,32,0] : Array Nat)[i.val*9+j.val]?.getD 0

private theorem tests : ∀ i j : Vertex, petersenGraph.Adj i j →
    (∀ a b : Bool, (a || b) = true → let x := pairInput i j (baseOf (andBase i j)) a b; good x = true ∧ petersenF x = (a && b)) ∧
    (∀ a b : Bool, (a && b) = false → let x := pairInput i j (baseOf (orBase i j)) a b; good x = true ∧ petersenF x = (a || b)) := by decide +kernel
theorem independent {gs : List Gate} (clean : CleanL 9 gs) (out : Fin (9 + gs.length))
    (live : ∀ w, w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    {f} (correct : compatible f) (ev : ∀ x, vl gs x out.val = f x)
    (cut : Fin (9+gs.length)) :
    BranchGraph.Independent petersenGraph (firstInputGroup clean out live cut) := by
  intro i iIn j jIn adj
  obtain ⟨ands,ors⟩ := tests _ _ adj
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [(mem_firstInputGroup clean out live cut i).mp iIn] at hi
  rw [(mem_firstInputGroup clean out live cut j).mp jIn] at hj
  have controlled : cut = out ∨ ∀ k : Vertex, (k = i ∨ k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with eq | block
    · exact Or.inl eq
    · exact Or.inr (fun k hk => block k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))
  have fact (base : Vertex → Bool) : ∃ o : Bool → Bool, ∀ a c,
      o (pairValue i j base (wireFormula i gs cut.val) a c) =
        f (pairInput i j base a c) := by
    obtain ⟨o,ho⟩ := cut_factors clean cut out (fun k => k=i ∨ k=j) base controlled
    refine ⟨o,fun a c => ?_⟩
    unfold pairValue
    rw [wireFormula_eval i clean _ cut.val cut.isLt, ← ev]
    apply ho
    intro k hk
    simp [pairInput,show k ≠ i from fun e => hk (Or.inl e),
      show k ≠ j from fun e => hk (Or.inr e)]
  obtain ⟨oA,hA⟩ := fact (baseOf (andBase i j))
  obtain ⟨oO,hO⟩ := fact (baseOf (orBase i j))
  exact three_pair_invariant i j _ hi hj _ _ oA oO
    (completeCorner _ _ (invariant i j _ _ hi) (fun a c h => (hA a c).trans ((correct _ (ands a c h).1).trans (ands a c h).2)))
    (fun a c h => (hO a c).trans ((correct _ (ors a c h).1).trans (ors a c h).2))
theorem factorWithBase {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut) (Z : Finset (Fin n)) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool, ∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I, label i = cut) → (∀ i ∈ O, cut < label i) →
        (vl gs (setInput (Z ∪ I ∪ O)) out.val = true ↔ decode (code I) O) := by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)) := vl gs (setInput (Z ∪ I)) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n), (∀ j ∈ J, label j = cut) ∧ code J = b ∧
      vl gs (setInput (Z ∪ J ∪ O)) out.val = true
  refine ⟨code, decode, ?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I, label i = cut) at groupI
  change (∀ i ∈ O, cut < label i) at afterO
  change (_ ↔ decode (code I) O)
  constructor
  · exact fun yes => ⟨I, groupI, rfl, yes⟩
  · rintro ⟨J, groupJ, sameCode, yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (Z ∪ K ∪ O)) cut.val = code K := by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O := fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput, absent]
    have sameCut : vl gs (setInput (Z ∪ I ∪ O)) cut.val = vl gs (setInput (Z ∪ J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out := lt_of_le_of_ne prior atOutput
    have eq := circuit_cut_agreement clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut := by
        by_contra offGroup
        have notI : i ∉ I := fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J := fun mem => offGroup (groupJ i mem)
        exact diff (by simp [setInput, notI, notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
          (inputWire gs i) = cut := isGroup
      have forbid := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
        (v := inputWire gs i) (w := out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b, avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
        fun _ _ h => ⟨h.1, h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]

open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace


open PetersenGroupBFS
abbrev dec (n : Nat) : Finset Vertex := PetersenMaskBridge.decode petersenNine n

@[simp] private theorem inDec (v : Vertex) (a : Nat) : v∈dec a ↔ a.testBit v.val=true := PetersenMaskBridge.mem_decode _ _ _
private theorem unionDec (a b : Nat) : dec (a|||b)=dec a ∪ dec b := PetersenMaskBridge.decode_or _ _ _
private theorem orLt {a b : Nat} (ha : a < 512) (hb : b < 512) : a|||b < 512 := Nat.or_lt_two_pow (n:=9) ha hb
private theorem encodable (s : Finset Vertex) : ∃ n < 512, dec n=s := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by decide,PetersenMaskBridge.decode_zero _⟩
  | @insert v s hv ih =>
    obtain ⟨n,hn,rfl⟩ := ih
    refine ⟨bit v.val ||| n,orLt (by rw [bit_eq_power]; exact Nat.pow_lt_pow_right (by decide) v.isLt) hn,?_⟩
    rw [unionDec]
    have e : dec (bit v.val) = {v} := by
      ext z; rw [inDec,bit_at,decide_eq_true_eq,Finset.mem_singleton]; exact ⟨fun h => Fin.ext h.symm,fun h => congrArg Fin.val h.symm⟩
    rw [e]; simp

private def positiveBits : Nat := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
private def val (n : Nat) := positiveBits.testBit n
private def safe (n : Nat) := (n &&& 51) != 0
private theorem observations : ∀ m : Fin 512, good (setInput (dec m.val)) = safe m.val ∧
    petersenF (setInput (dec m.val)) = val m.val := by decide +kernel

private theorem isIndep : ∀ m : Fin 512, BranchGraph.Independent petersenGraph (dec m.val) ↔ val m.val = false := by
  unfold BranchGraph.Independent; decide +kernel

private theorem subDec {a b : Nat} (h : a &&& b=a) : dec a ⊆ dec b := by
  intro v hv
  rw [inDec] at hv ⊢
  have q := congrArg (fun n : Nat => n.testBit v.val) h
  simp [Nat.testBit_and,hv] at q
  exact q

private theorem disjDec {a b : Nat} (h : a &&& b=0) : Disjoint (dec a) (dec b) := by
  apply Finset.disjoint_left.mpr
  intro v ha hb
  rw [inDec] at ha hb
  have q := congrArg (fun n : Nat => n.testBit v.val) h
  simp [Nat.testBit_and,ha,hb] at q

private def fits (a b : Nat) := (a &&& b)==a
private def word (w i : Nat) := (w >>> (9*i)) &&& 511
private def diff (a b : Nat) := safe a && safe b && (val a != val b)
private def clash (e s w : Nat) : Bool :=
  let z := word w 0
  let a := word w 1
  let b := word w 2
  let c := word w 3
  let u := word w 4
  let v := word w 5
  let t := word w 6
  fits z e && fits a s && fits b s && fits c s &&
    ((u &&& (e|||s))==0) && ((v &&& (e|||s))==0) && ((t &&& (e|||s))==0) &&
    diff (z|||a|||u) (z|||b|||u) && diff (z|||a|||v) (z|||c|||v) &&
    diff (z|||b|||t) (z|||c|||t)

private theorem wordLt (w i : Nat) : word w i < 512 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide : 511 < 512)

private theorem conflictSound {f} (correct : compatible f) {e s w : Nat}
    (check : clash e s w = true)
    (code : Finset Vertex → Bool) (decode : Bool → Finset Vertex → Prop)
    (fact : ∀ I O, I ⊆ dec s → Disjoint O (dec e ∪ dec s) →
      (f (setInput (dec (word w 0) ∪ I ∪ O))=true ↔ decode (code I) O)) : False := by
  simp only [clash,fits,Bool.and_eq_true,beq_iff_eq] at check
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_,sa⟩,sb⟩,sc⟩,tu⟩,tv⟩,tt⟩,dab⟩,dac⟩,dbc⟩ := check
  let z := word w 0
  have unequal (a b c : Nat) (ha : a < 512) (hb : b < 512) (hc : c < 512)
      (asub : fits a s = true) (bsub : fits b s = true) (outside : c &&& (e|||s) = 0)
      (dif : diff (z|||a|||c) (z|||b|||c)=true) : code (dec a) ≠ code (dec b) := by
    have safeA := observations ⟨z|||a|||c,orLt (orLt (wordLt _ _) ha) hc⟩
    have safeB := observations ⟨z|||b|||c,orLt (orLt (wordLt _ _) hb) hc⟩
    simp only [diff,Bool.and_eq_true,bne_iff_ne] at dif
    have fa := correct _ (safeA.1.trans dif.1.1)
    have fb := correct _ (safeB.1.trans dif.1.2)
    have ac := fact (dec a) (dec c) (subDec (beq_iff_eq.mp asub)) (unionDec e s ▸ disjDec outside)
    have bc := fact (dec b) (dec c) (subDec (beq_iff_eq.mp bsub)) (unionDec e s ▸ disjDec outside)
    intro eq
    rw [eq] at ac
    have same := Bool.eq_iff_iff.mpr (ac.trans bc.symm)
    rw [←unionDec,←unionDec,←unionDec,←unionDec] at same
    exact dif.2 ((fa.trans safeA.2).symm.trans (same.trans (fb.trans safeB.2)))
  have ab := unequal _ _ _ (wordLt _ _) (wordLt _ _) (wordLt _ _) (beq_iff_eq.mpr sa) (beq_iff_eq.mpr sb) tu dab
  have ac := unequal _ _ _ (wordLt _ _) (wordLt _ _) (wordLt _ _) (beq_iff_eq.mpr sa) (beq_iff_eq.mpr sc) tv dac
  have bc := unequal _ _ _ (wordLt _ _) (wordLt _ _) (wordLt _ _) (beq_iff_eq.mpr sb) (beq_iff_eq.mpr sc) tt dbc
  exact (by decide : ∀ a b c : Bool, a ≠ b → a ≠ c → b ≠ c → False) _ _ _ ab ac bc

def rankMask : Nat → Nat
  | 0 => 0x1
  | 1 => 0x10000000000000000000000000000000100000000000000010000000100010117
  | 2 => 0x100000000000000010000000100010117000000000000000100000001000101170000000100010117000101170117177f
  | 3 => 0x10000000100010117000000010001011f000101170117177f0000000100010117000101370117177f000101170117177f0117177f177f7fff
  | 4 => 0x150001015f000101370117177f0101031f071f1fff0117177f377f7fff000101770117177f133737ff777fffff0117177f1f7f7fff1f7f7fff7fffffff
  | _ => 0

def witnessCodes : Nat → Nat → Nat
  | 0, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000200201100400000,0x410010200200000080405200200000000000000000000000000000000000002002010100200000240402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x40205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000000000000000000000000000000000000040401200800000,0x40202080100000000000000000000000000000000000000000000000000000200201100400000,0x1028041002000000410010200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x410010200200000080405200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000080a02401000000,0x40401200400000,0x0,0x0,0x200201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000141205802000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 1, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004140902002000000000000000000000000000000000000,0x10080501002000000000000000000000410410100200000000000000000000000000000000000000000000000000000090402100100000000000000000000004480504002000000000000000000000000000000000000,0x8140208010000000000000000000000802010401001000000000000000000021040a100400000,0x80410200200000000000000000000000000000000000000000000000000000a00402200100000000000000000000000000000000000000000000000000000000000000000000,0x8140208010000000000000000000000000000000000000000000000000000008040a200400000,0x410410100200000000000000000000000000000000000000000000000000000090402100100000000000000000000000000000000000000000000000000000080482200800000,0x8140208010000000000000000000000000000000000000000000000000000021040a100400000,0x100805010020000000000000000000004028104002000000000000000000000000000000000000000000000000000000000000000000000000000000000000200a0510002000000000000000000000000000000000000,0x414090200200000000000000000000028400a400400000,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000082802401000000,0x8040a200400000,0x0,0x0,0x81402800100000000000000000000014100520002000000000000000000000000000000000000,0x8140208010000000000000000000000414090200200000000000000000000080140a800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x200a0510002000000000000000000000281414802000000,0x414090200200000000000000000000028400a400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 2, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000002028080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x4010080200200000160205200200000000000000000000000000000000000002028080100200000260209200100000000000000000000000000000000000002110081000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000060201200400000,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000060201200800000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x4010080200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x4010080200200000160205200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002110081000200000140b01401000000,0x60201200400000,0x0,0x0,0x2028080100200000801209800100000000000000000000000000000000000002020084000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2014082000200000141205802000000,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 3, x => ((#[0x0,0x8080100001000000000000000000000000000000000000000000000000000000000000000,0x412010100200000000000000000000000000000000000000000000000000004412090100100000000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000210008100400002,0x422010200200000000000000000000000000000000000000000000000000000a22028200100000000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000020000200400001,0x412010100200000000000000000000000000000000000000000000000000004412090100100000000000000000000000000000000000000000000000000002422090200800000,0x8080100001000000000000000000000000000000000000000000000000020000200400001,0x402810400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x804028400400000,0x0,0x0,0x422010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000502910401000000,0x804028400400000,0x0,0x0,0x804028800100000000000000000000000000000000000000000000000000000000000000000000,0x804028800100000000000000000000000000000000000000000000000000000804028800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x504014802000000,0x804028400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 4, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x1080041002000000000000000000000040210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040008044002000000000000000000000000000000000000,0x8008042002000000000000000000000200201100400000,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000000000000000000,0x40401200400000,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040401200800000,0x200201100400000,0x1080041002000000410010200200000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001100050002000000420012000200000000000000000000,0x8008042002000000000000000000000044001400400000,0x0,0x0,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000084002401000000,0x40401200400000,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x8008042002000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1100050002000000420012000200000241220802000000,0x8008042002000000000000000000000044001400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 5, x => ((#[0x10081401002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8141802002000000000000000000000000000000000000,0x10081401002000000000000000000000410410100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040481404002000000000000000000000000000000000000,0x820020401001000000000000000000021040a100400000,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8040a200400000,0x410410100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080482200800000,0x21040a100400000,0x10081401002000000000000000000000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000020101410002000000000000000000000000000000000000,0x814180200200000000000000000000028400a400400000,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084002401000000,0x8040a200400000,0x0,0x0,0x20101420002000000000000000000000000000000000000,0x814180200200000000000000000000080140a800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x20101410002000000000000000000000281420802000000,0x814180200200000000000000000000028400a400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 6, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x200201100400000,0x4010080200200000420210200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002110081000200000000000000000000,0x60201200400000,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060201200800000,0x200201100400000,0x4010080200200000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002020082000200000000000000000000,0x44001400400000,0x0,0x0,0x4010080200200000420210200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002110081000200000804101401000000,0x60201200400000,0x0,0x0,0x2020084000200000000000000000000,0x41201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2020082000200000241220802000000,0x44001400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 7, x => ((#[0x0,0x0,0x412010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x210008100400002,0x422010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x20000200400001,0x412010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002422090200800000,0x20000200400001,0x404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x804028400400000,0x0,0x0,0x422010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000804110401000000,0x804028400400000,0x0,0x0,0x0,0x804028800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1404020802000000,0x804028400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 8, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000002000201100400000,0x2002010100200002040402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x40202100100000000000000000000000000000000000000000000000000000040401200800000,0x40202080100000000000000000000000000000000000000000000000000002000201100400000,0x1028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x2002011000200000080a02401000000,0x40401200400000,0x0,0x0,0x2002010100200000084002800100000000000000000000001100060002000000420014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000044001800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000144005802000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 9, x => ((#[0x0,0x80080100001000000000000000000101802002000200000000000000000000000000000000,0x90402100100000000000000000000004480504002000000000000000000000000000000000000,0x90402100100000000000000000000080020104010010000000000000000000010402100400008,0x2400402200100000000000000000000000000000000000000000000000000000000000000000000,0x80080100001000000000000000000000000000000000000000000000000020000200400001,0x90402100100000000000000000000000000000000000000000000000000000080482200800000,0x90402100100000000000000000000000000000000000000000000000000000080482200800000,0x200a0510002000000000000000000000000000000000000,0x20100910002000000000000000000000000800400400001,0x0,0x0,0x82802401000000,0x84002401000000,0x0,0x0,0x84002800100000000000000000000014100520002000000000000000000000000000000000000,0x84002800100000000000000000000020100920002000000000000000000000008000800400001,0x0,0x0,0x0,0x0,0x0,0x0,0x200a0510002000000000000000000000504014802000000,0x20100910002000000000000000000000000800400400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 10, x => ((#[0x2090080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000000000000000000,0x40281100100000000000000000000000000000000000000000000000000000000000000000000,0x40281080100000000000000000000000000000000000000000000000000002000201100400000,0x2090080100200002060281200100000000000000000000000000000000000002110081000200000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000060201200400000,0x40281100100000000000000000000000000000000000000000000000000000060201200800000,0x40281080100000000000000000000000000000000000000000000000000002000201100400000,0x2014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x2110081000200000140b01401000000,0x60201200400000,0x0,0x0,0x2090080100200000804081800100000000000000000000000000000000000002020084000200000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000044001800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2014082000200000144005802000000,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 11, x => ((#[0x0,0x80080100001000000000000000000000000000000000000000000000000000000000000000,0x4412090100100000000000000000000000000000000000000000000000000000000000000000000,0x80080100001000000000000000000000000000000000000000000000000000000000000000,0x2422090200100000000000000000000000000000000000000000000000000000000000000000000,0x80080100001000000000000000000000000000000000000000000000000020000200400001,0x4412090100100000000000000000000000000000000000000000000000000002422090200800000,0x80080100001000000000000000000000000000000000000000000000000020000200400001,0x0,0x800400400001,0x0,0x0,0x502910401000000,0x20000200400001,0x0,0x0,0x804090800100000000000000000000000000000000000000000000000000000000000000000000,0x80080100001000000000000000000000000000000000000000000000000008000800400001,0x0,0x0,0x0,0x0,0x0,0x0,0x504014802000000,0x800400400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 12, x => ((#[0x0,0x40008042002000000000000000000000000000000000000,0x40008044002000000000000000000000000000000000000,0x40008042002000000000000000000002000201100400000,0x2002011000200000000000000000000,0x40401200400000,0x40401200800000,0x2000201100400000,0x1100050002000000420012000200000000000000000000,0x40008042002000000000000000000000044001400400000,0x0,0x0,0x2002011000200000084002401000000,0x40401200400000,0x0,0x0,0x1100060002000000420014000200000000000000000000,0x40008042002000000000000000000000044001800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1100050002000000420012000200001044020802000000,0x40008042002000000000000000000000044001400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 13, x => ((#[0x0,0x101802002000200000000000000000000000000000000,0x40481404002000000000000000000000000000000000000,0x80201004010010000000000000000000010402100400008,0x0,0x20000200400001,0x80482200800000,0x80482200800000,0x20101410002000000000000000000000000000000000000,0x20101810002000000000000000000000084002400400008,0x0,0x0,0x84002401000000,0x84002401000000,0x0,0x0,0x20101420002000000000000000000000000000000000000,0x20101820002000000000000000000000008000800400001,0x0,0x0,0x0,0x0,0x0,0x0,0x20101410002000000000000000000001404020802000000,0x20101810002000000000000000000000008000800400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 14, x => ((#[0x0,0x0,0x0,0x2000201100400000,0x2110081000200000000000000000000,0x60201200400000,0x60201200800000,0x2000201100400000,0x2020082000200000000000000000000,0x44001400400000,0x0,0x0,0x2110081000200000804101401000000,0x60201200400000,0x0,0x0,0x2020084000200000000000000000000,0x44001800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2020082000200001044020802000000,0x44001400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 16, x => ((#[0x1028041002000000424010200200000000000000000000000000000000000000000000000000004002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x424010200200000080405200200000000000000000000000000000000000004002010100200000240402200100000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000000000000000000000000000000000000040401200800000,0x0,0x1028041002000000424010200200000800a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000420012000200000000000000000000,0x0,0x0,0x0,0x424010200200000080405200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004002011000200000080a02401000000,0x0,0x0,0x0,0x400201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000420012000200000141205802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 17, x => ((#[0x60120901002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x20001002000040000000000000002090502100200000000000000000000000000000000000000000000000000000090402100100000000000000000000004400104002000400000000000000000000000000000000,0x0,0x80424200200000000000000000000000000000000000000000000000000000a00402200100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x2090502100200000000000000000000000000000000000000000000000000000090402100100000000000000000000000000000000000000000000000000000080482200800000,0x0,0x60120901002000000000000000000000804024400200000000000000000000000000000000000000000000000000000000000000000000000000000000000020100910002000000000000000000000000000000000000,0x0,0x0,0x0,0x80424200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084002401000000,0x0,0x0,0x0,0x81402800100000000000000000000020100920002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20100910002000000000000000000000281420802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 18, x => ((#[0x4024100200200000000000000000000000000000000000000000000000000004028100100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x4024100200200000160205200200000000000000000000000000000000000004028100100200000260209200100000000000000000000000000000000000000100001000200080000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000060201200800000,0x0,0x4024100200200000800a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020002000200010000000000000000,0x0,0x0,0x0,0x4024100200200000160205200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020002000200010140b01401000000,0x0,0x0,0x0,0x4028100100200000801209800100000000000000000000000000000000000000008004000200010000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20002000200010141205802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 19, x => ((#[0x0,0x0,0x4100200001000000000000000000000000000000000000000000000000000008100100001000000000000000000000000000000000000000000000000000000000000000,0x0,0x120004200200001000000000000000000000000000000000000000000000000220008200100001000000000000000000000000000000000000000000000000000000000000000,0x0,0x4100200001000000000000000000000000000000000000000000000000000008100100001000000000000000000000000000000000000000000000000020000200800001,0x0,0x804024400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x804024400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100900401000001,0x0,0x0,0x0,0x804028800100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101004802000001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 20, x => ((#[0x1808041002000000502010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1808041002000000000000000000000040301100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040008044002000000000000000000000000000000000000,0x0,0x502010200200000080501200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40301100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040401200800000,0x0,0x1808041002000000502010200200000804101400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001100050002000000420012000200000000000000000000,0x0,0x0,0x0,0x502010200200000080501200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004002011000200000084002401000000,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1100050002000000420012000200000241220802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 21, x => ((#[0x800001002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x800001002000040000000000000002090502100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040401004002000400000000000000000000000000000000,0x0,0x80502200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x2090502100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080482200800000,0x0,0x20101810002000000000000000000000804102400200000000000000000000000000000000000000000000000000000000000000000000000000000000000020101810002000000000000000000000000000000000000,0x0,0x0,0x0,0x80502200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084002401000000,0x0,0x0,0x0,0x20101820002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20101810002000000000000000000000281420802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 22, x => ((#[0x100000200200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40301100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x100000200200010000100200200002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100001000200080000000000000000,0x0,0x40301100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060201200800000,0x0,0x100000200200010804101400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020002000200010000000000000000,0x0,0x0,0x0,0x100000200200010804101400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020002000200010804101401000000,0x0,0x0,0x0,0x8004000200010000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20002000200010241220802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 24, x => ((#[0x4002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x4002010100200002040402200100000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40202100100000000000000000000000000000000000000000000000000000040401200800000,0x0,0x1028050002000000420012000200000000000000000000,0x0,0x0,0x0,0x4002011000200000080a02401000000,0x0,0x0,0x0,0x4002010100200000084002800100000000000000000000001100060002000000420014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000420012000200000144005802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 25, x => ((#[0x0,0x0,0x90402100100000000000000000000004400104002000400000000000000000000000000000000,0x0,0x2020080200100001000000000000000000000000000000000000000000000000000000000000000,0x0,0x90402100100000000000000000000000000000000000000000000000000000080482200800000,0x0,0x20100910002000000000000000000000000000000000000,0x0,0x0,0x0,0x84002401000000,0x0,0x0,0x0,0x84002800100000000000000000000020100920002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20100910002000000000000000000000108004802000001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 26, x => ((#[0x80000100200080000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40281100100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x80000100200082060281200100000000000000000000000000000000000000100001000200080000000000000000,0x0,0x40281100100000000000000000000000000000000000000000000000000000060201200800000,0x0,0x20002000200010000000000000000,0x0,0x0,0x0,0x20002000200010140b01401000000,0x0,0x0,0x0,0x20004000200010804081800100000000000000000000000000000000000000020004000200010000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20002000200010144005802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 28, x => ((#[0x0,0x0,0x40008044002000000000000000000000000000000000000,0x0,0x4002011000200000000000000000000,0x0,0x40401200800000,0x0,0x1100050002000000420012000200000000000000000000,0x0,0x0,0x0,0x4002011000200000084002401000000,0x0,0x0,0x0,0x1100060002000000420014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1100050002000000420012000200001044020802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 32, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x410010200200000080405200200000000000000000000000000000000000002002010100200000240402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x0,0x0,0x1028041002000000410010200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x410010200200000080405200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000080a02401000000,0x40401200400000,0x0,0x0,0x200201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000141205802000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 33, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004040102002000800000000000000000000000000000000,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000002400402200100000000000000000000000000000000000000000000000000000000000000000000,0x8140208010000000000000000000000000000000000000000000000000000008040a200400000,0x0,0x0,0x100805010020000000000000000000004028104002000000000000000000000000000000000000000000000000000000000000000000000000000000000000500a0510002000000000000000000000000000000000000,0x20010002000040000000000000000000800400400001,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000082802401000000,0x8040a200400000,0x0,0x0,0x81402800100000000000000000000014280520002000000000000000000000000000000000000,0x81402080100000000000000000000000040020002000040000000000000000001000800400001,0x0,0x0,0x0,0x0,0x0,0x0,0x500a0510002000000000000000000000281414802000000,0x20010002000040000000000000000000800400400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 34, x => ((#[0x10000200200010000000000000000000000000000000000000000000000002090080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x2110081000200000160205200200000000000000000000000000000000000002090080100200000260209200100000000000000000000000000000000000002110081000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000060201200400000,0x0,0x0,0x2014082000200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x2110081000200000160205200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002110081000200000140b01401000000,0x60201200400000,0x0,0x0,0x2090080100200001041209800100000000000000000000000000000000000002050084000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2014082000200000141205802000000,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 35, x => ((#[0x0,0x8080100001000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x422010200200000000000000000000000000000000000000000000000000002422090200100000000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000020000200400001,0x0,0x0,0x402810400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x800400400001,0x0,0x0,0x422010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000502910401000000,0x20000200400001,0x0,0x0,0x140a090800100000000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000001000800400001,0x0,0x0,0x0,0x0,0x0,0x0,0x50a014802000000,0x800400400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 36, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x0,0x0,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000000000000000000,0x40401200400000,0x0,0x0,0x1080041002000000410010200200000000010400200020000000000000000000000000000000000000000000000000000000000000000000000000000000000001010002000800000000000000000000000000000000,0x8008042002000000000000000000000000008400400020,0x0,0x0,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000040301401000004,0x40401200400000,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x8008042002000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000048201802000004,0x8008042002000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 37, x => ((#[0x10081401002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8041002002000800000000000000000000000000000000,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8040a200400000,0x0,0x0,0x10081401002000000000000000000000000010400200020000000000000000000000000000000000000000000000000000000000000000000000000000000000001010002000800000000000000000000000000000000,0x8041002002000800000000000000000000008400400020,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000402110401000004,0x8040a200400000,0x0,0x0,0x40020002000040000000000000000000000000000000,0x40020002000040000000000000000001000800400001,0x0,0x0,0x0,0x0,0x0,0x0,0x4002000200004000000000000000040a010802000004,0x40020002000040000000000000000001000800400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 38, x => ((#[0x10000200200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x2110081000200000420210200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002110081000200000000000000000000,0x60201200400000,0x0,0x0,0x10000200200010000010400200020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8400400020,0x0,0x0,0x2110081000200000420210200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002110081000200000040301401000004,0x60201200400000,0x0,0x0,0x2050084000200000000000000000000,0x41201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2050084000200000048201802000004,0x41201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 40, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x2002010100200002040402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x0,0x0,0x1028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x2002011000200000080a02401000000,0x40401200400000,0x0,0x0,0x2002010100200000088202800100000000000000000000001208060002000000450014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000048201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000148205802000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 41, x => ((#[0x0,0x80080100001000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x2400402200100000000000000000000000000000000000000000000000000000000000000000000,0x80080100001000000000000000000000000000000000000000000000000020000200400001,0x0,0x0,0x500a0510002000000000000000000000000000000000000,0x20010002000040000000000000000000800400400001,0x0,0x0,0x82802401000000,0x20000200400001,0x0,0x0,0x8a002800100000000000000000000014280520002000000000000000000000000000000000000,0x80080100001000000000000000000200020002000040000000000000000008000800400001,0x0,0x0,0x0,0x0,0x0,0x0,0x500a051000200000000000000000000050a014802000000,0x20010002000040000000000000000000800400400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 42, x => ((#[0x2090080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x2090080100200002060281200100000000000000000000000000000000000002110081000200000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000060201200400000,0x0,0x0,0x2014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x2110081000200000140b01401000000,0x60201200400000,0x0,0x0,0x2090080100200001048281800100000000000000000000000000000000000002050084000200000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000048201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2014082000200000148205802000000,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 44, x => ((#[0x0,0x40008042002000000000000000000000000000000000000,0x0,0x0,0x2002011000200000000000000000000,0x40401200400000,0x0,0x0,0x1010002000800000000000000000000000000000000,0x40008042002000000000000000000000000000000000000,0x0,0x0,0x2002011000200000040301401000004,0x40401200400000,0x0,0x0,0x1208060002000000450014000200000000000000000000,0x40008042002000000000000000000000048201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1208060002000000450014000200000048201802000004,0x40008042002000000000000000000000048201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 48, x => ((#[0x1028041002000000502010200200000000000000000000000000000000000000000000000000000002000100200080000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x502010200200000080405200200000000000000000000000000000000000000002000100200080240402200100000000000000000000000000000000000000002001000200080000000000000000,0x0,0x0,0x0,0x1028041002000000502010200200004040a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000004002000200080000000000000000,0x0,0x0,0x0,0x502010200200000080405200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002001000200080080a02401000000,0x0,0x0,0x0,0x40a01400020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x102805000200000040a014000200000141205802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 49, x => ((#[0x20001002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x80502200200000000000000000000000000000000000000000000000000000220008200100001000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x20001002000040000000000000004000804400200001000000000000000000000000000000000000000000000000000000000000000000000000000000000020010002000040000000000000000000000000000000,0x0,0x0,0x0,0x80502200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100900401000001,0x0,0x0,0x0,0x81402800100000000000000000000000040020002000040000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20010002000040000000000000000101004802000001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 50, x => ((#[0x100000200200010000000000000000000000000000000000000000000000000080000100200080000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x100000200200010160205200200000000000000000000000000000000000000080000100200080260209200100000000000000000000000000000000000000100001000200080000000000000000,0x0,0x0,0x0,0x100000200200014040a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004002000200080000000000000000,0x0,0x0,0x0,0x100000200200010160205200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100001000200080140b01401000000,0x0,0x0,0x0,0x8004000200011041209800100000000000000000000000000000000000000008004000200010000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8004000200010141205802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 52, x => ((#[0x1808041002000000502010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x502010200200000080501200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002001000200080000000000000000,0x0,0x0,0x0,0x1808041002000000502010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001010002000800000000000000000000000000000000,0x0,0x0,0x0,0x502010200200000080501200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002001000200080040301401000004,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000048201802000004] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 56, x => ((#[0x2000100200080000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x2000100200082040402200100000000000000000000000000000000000000002001000200080000000000000000,0x0,0x0,0x0,0x1028050002000000004002000200080000000000000000,0x0,0x0,0x0,0x2001000200080080a02401000000,0x0,0x0,0x0,0x2000100200080088202800100000000000000000000001208060002000000040004000200080000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000004002000200080148205802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 64, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x1028041002000000410010200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x200201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000141205802000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 65, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004140902002000000000000000000000000000000000000,0x10080501002000000000000000000000410410100200000000000000000000000000000000000000000000000000000090402100100000000000000000000004480504002000000000000000000000000000000000000,0x8140208010000000000000000000000802010401001000000000000000000021040a100400000,0x0,0x0,0x0,0x0,0x100805010020000000000000000000004028104002000000000000000000000000000000000000000000000000000000000000000000000000000000000000200a0510002000000000000000000000000000000000000,0x414090200200000000000000000000028400a400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x81402800100000000000000000000014100520002000000000000000000000000000000000000,0x8140208010000000000000000000000414090200200000000000000000000080140a800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x200a0510002000000000000000000000281414802000000,0x414090200200000000000000000000028400a400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 66, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000002028080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x4010080200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2028080100200000801209800100000000000000000000000000000000000002020084000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2014082000200000141205802000000,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 67, x => ((#[0x0,0x8080100001000000000000000000000000000000000000000000000000000000000000000,0x412010100200000000000000000000000000000000000000000000000000004412090100100000000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000210008100400002,0x0,0x0,0x0,0x0,0x402810400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x804028400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x804028800100000000000000000000000000000000000000000000000000000000000000000000,0x804028800100000000000000000000000000000000000000000000000000000804028800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x504014802000000,0x804028400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 68, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x1080041002000000000000000000000040210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000080008044002000000000000000000000000000000000000,0x8008042002000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x1080041002000000410010200200000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001100050002000000420012000200000000000000000000,0x8008042002000000000000000000000044001400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x8008042002000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1100050002000000420012000200000241220802000000,0x8008042002000000000000000000000044001400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 69, x => ((#[0x800001002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x140802002001000000000000000000000000000000000,0x10480404008000000000000000000000410410100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000880404002000100000000000000000000000000000000,0x840020401001000000000000000000021040a100400000,0x0,0x0,0x0,0x0,0x10100410008000000000000000000000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000010100410002001000000000000000000000000000000000,0x20100a1001000000000000000000000028400a400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x40020002000040000000000000000000000000000000,0x20100a2001000000000000000000000080140a800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x40020002000040000000000000000281420802000000,0x20100a1001000000000000000000000028400a400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 70, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x200201100400000,0x0,0x0,0x0,0x0,0x4010080200200000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002020082000200000000000000000000,0x44001400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2020084000200000000000000000000,0x41201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2020082000200000241220802000000,0x44001400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 72, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000002000201100400000,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2002010100200000084002800100000000000000000000001100060002000000420014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000044001800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000144005802000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 73, x => ((#[0x0,0x80080100001000000000000000000000000000000000000000000000000000000000000000,0x90402100100000000000000000000004480504002000000000000000000000000000000000000,0x90402100100000000000000000000080020104010010000000000000000000010402100400008,0x0,0x0,0x0,0x0,0x200a0510002000000000000000000000000000000000000,0x20100910002000000000000000000000000800400400001,0x0,0x0,0x0,0x0,0x0,0x0,0x84002800100000000000000000000014100520002000000000000000000000000000000000000,0x84002800100000000000000000000020100920002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x200a0510002000000000000000000000504014802000000,0x20100910002000000000000000000000000800400400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 74, x => ((#[0x2090080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000000000000000000,0x40281100100000000000000000000000000000000000000000000000000000000000000000000,0x40281080100000000000000000000000000000000000000000000000000002000201100400000,0x0,0x0,0x0,0x0,0x2014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2090080100200000804081800100000000000000000000000000000000000002020084000200000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000044001800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2014082000200000144005802000000,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 76, x => ((#[0x0,0x8042002000100000000000000000000000000000000,0x80008044002000000000000000000000000000000000000,0x80008044002000000000000000000002000201100400000,0x0,0x0,0x0,0x0,0x1100050002000000420012000200000000000000000000,0x1100050002000000000000000000000044001400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1100060002000000420014000200000000000000000000,0x1100060002000000000000000000000044001800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1100050002000000420012000200000044001802000004,0x1100050002000000000000000000000044001400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 80, x => ((#[0x1028041002000000424010200200000000000000000000000000000000000000000000000000004002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x1028041002000000424010200200000800a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000420012000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000420012000200000141205802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 81, x => ((#[0x20001002000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x20001002000040000000000000002090502100200000000000000000000000000000000000000000000000000000090402100100000000000000000000004400104002000400000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x20100910002000000000000000000000804024400200000000000000000000000000000000000000000000000000000000000000000000000000000000000020100910002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81402800100000000000000000000020100920002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20100910002000000000000000000000281420802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 82, x => ((#[0x4024100200200000000000000000000000000000000000000000000000000004028100100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x4024100200200000800a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020002000200010000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4028100100200000801209800100000000000000000000000000000000000000008004000200010000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20002000200010141205802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 84, x => ((#[0x1808041002000000502010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1808041002000000000000000000000040301100200000000000000000000000000000000000000000000000000000000000000000000000000000000000080008044002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x1808041002000000502010200200000804101400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001100050002000000420012000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1100050002000000420012000200000241220802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 88, x => ((#[0x4002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x1028050002000000420012000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4002010100200000084002800100000000000000000000001100060002000000420014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000420012000200000144005802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 96, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028041002000000410010200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x200201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000141205802000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 97, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004040102002000800000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x10080501002000000000000000000000402810400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000020010002000040000000000000000000000000000000,0x20010002000040000000000000000000800400400001,0x0,0x0,0x0,0x0,0x0,0x0,0x81402800100000000000000000000000040020002000040000000000000000000000000000000,0x81402080100000000000000000000000040020002000040000000000000000001000800400001,0x0,0x0,0x0,0x0,0x0,0x0,0x20010002000040000000000000000281414802000000,0x20010002000040000000000000000000800400400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 98, x => ((#[0x10000200200010000000000000000000000000000000000000000000000002090080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x2014082000200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2090080100200002041209800100000000000000000000000000000000000000008004000200010000000000000000,0x40209080100000000000000000000000000000000000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2014082000200000141205802000000,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 100, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x1080041002000000410010200200000000010400200020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000008400400020,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x8008042002000000000000000000000041201800400000,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x8008042002000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 104, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x0,0x0,0x0,0x0,0x2002010100200000000002800100020000000000000000000000120002000800000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000040205802000040,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 112, x => ((#[0x1028041002000000502010200200000000000000000000000000000000000000000000000000000002000100200080000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1028041002000000502010200200004040a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000004002000200080000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40a01400020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x102805000200000040a014000200000141205802000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 128, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000200201100400000,0x410010200200000080405200200000000000000000000000000000000000002002010100200000240402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x40205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000000000000000000000000000000000000040401200800000,0x40202080100000000000000000000000000000000000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 129, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004140902002000000000000000000000000000000000000,0x100805010020000000000000000000004204101002000000000000000000000000000000000000000000000000000000a0402100100000000000000000000004880504002000000000000000000000000000000000000,0x8140208010000000000000000000000802010401001000000000000000000022040a100400000,0x80410200200000000000000000000000000000000000000000000000000000a00402200100000000000000000000000000000000000000000000000000000000000000000000,0x8140208010000000000000000000000000000000000000000000000000000008040a200400000,0x4204101002000000000000000000000000000000000000000000000000000000a0402100100000000000000000000000000000000000000000000000000000080502200800000,0x8140208010000000000000000000000000000000000000000000000000000022040a100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81402800100000000000000000000014100520002000000000000000000000000000000000000,0x8140208010000000000000000000000414090200200000000000000000000080140a800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 130, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000002028080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x4010080200200000160205200200000000000000000000000000000000000002028080100200000260209200100000000000000000000000000000000000002110081000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000060201200400000,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000060201200800000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2028080100200000801209800100000000000000000000000000000000000002020084000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 131, x => ((#[0x0,0x8080100001000000000000000000000000000000000000000000000000000000000000000,0x422010100200000000000000000000000000000000000000000000000000000000008100100001000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000220008100400002,0x422010200200000000000000000000000000000000000000000000000000000a22028200100000000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000020000200400001,0x422010100200000000000000000000000000000000000000000000000000000000008100100001000000000000000000000000000000000000000000000000020000200800001,0x8080100001000000000000000000000000000000000000000000000000020000200400001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x804028800100000000000000000000000000000000000000000000000000000000000000000000,0x804028800100000000000000000000000000000000000000000000000000000804028800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 132, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x1080041002000000000000000000000040210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040008044002000000000000000000000000000000000000,0x8008042002000000000000000000000200201100400000,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000000000000000000,0x40401200400000,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040401200800000,0x200201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x8008042002000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 133, x => ((#[0x10081401002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8141802002000000000000000000000000000000000000,0x10081401002000000000000000000000420410100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040881404002000000000000000000000000000000000000,0x820020401001000000000000000000022040a100400000,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8040a200400000,0x420410100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080502200800000,0x22040a100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20101420002000000000000000000000000000000000000,0x814180200200000000000000000000080140a800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 134, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x200201100400000,0x4010080200200000420210200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002110081000200000000000000000000,0x60201200400000,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060201200800000,0x200201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2020084000200000000000000000000,0x41201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 136, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000004000201100400000,0x2002010100200004040402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x40202100100000000000000000000000000000000000000000000000000000040401200800000,0x40202080100000000000000000000000000000000000000000000000000004000201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2002010100200000084002800100000000000000000000001100060002000000420014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000044001800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 137, x => ((#[0x0,0x101802002000200000000000000000000000000000000,0xa0402100100000000000000000000004880504002000000000000000000000000000000000000,0xa0402100100000000000000000000100020104010010000000000000000000000000000000000,0x4400402200100000000000000000000000000000000000000000000000000000000000000000000,0x20000200400001000000000000000000000000000000000000000000000000020000200400001,0xa0402100100000000000000000000000000000000000000000000000000000080502200800000,0xa0402100100000000000000000000000000000000000000000000000000000080502200800000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x84002800100000000000000000000014100520002000000000000000000000000000000000000,0x84002800100000000000000000000020100920002000000000000000000000008000800400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 138, x => ((#[0x0,0x0,0x20000100100002000000000000000000000000000000000000000000000000000000000000000,0x4000201100400000000000000000000000000000000000000000000000000004000201100400000,0x2110081000200000060201200100080000000000000000000000000000000002110081000200000000000000000000,0x60201200400000000000000000000000000000000000000000000000000000060201200400000,0x60201200800000000000000000000000000000000000000000000000000000060201200800000,0x4000201100400000000000000000000000000000000000000000000000000004000201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2020084000200000004000800100002000000000000000000000000000000002020084000200000000000000000000,0x44001800400000000000000000000000000000000000000000000000000000044001800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 140, x => ((#[0x0,0x40008042002000000000000000000000000000000000000,0x40008044002000000000000000000000000000000000000,0x40008042002000000000000000000004000201100400000,0x2002011000200000000000000000000,0x40401200400000,0x40401200800000,0x4000201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1100060002000000420014000200000000000000000000,0x40008042002000000000000000000000044001800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 144, x => ((#[0x1028041002000000424010200200000000000000000000000000000000000000000000000000004002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x424010200200000080405200200000000000000000000000000000000000004002010100200000240402200100000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000000000000000000000000000000000000040401200800000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 145, x => ((#[0x60120901002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x200010020000400000000000000000000041002000010000000000000000000000000000000000000000000000000a0402100100000000000000000000004800104002000400000000000000000000000000000000,0x0,0x80424200200000000000000000000000000000000000000000000000000000a00402200100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x805022002000000000000000000000000000000000000000000000000000000a0402100100000000000000000000000000000000000000000000000000000080502200800000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81402800100000000000000000000020100920002000000000000000000000000000000000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 146, x => ((#[0x4024100200200000000000000000000000000000000000000000000000000004028100100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x4024100200200000160205200200000000000000000000000000000000000004028100100200000260209200100000000000000000000000000000000000000100001000200080000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000060201200800000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4028100100200000801209800100000000000000000000000000000000000000008004000200010000000000000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 148, x => ((#[0x1808041002000000502010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1808041002000000000000000000000040301100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040008044002000000000000000000000000000000000000,0x0,0x502010200200000080501200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40301100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040401200800000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 152, x => ((#[0x4002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x4002010100200004040402200100000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40202100100000000000000000000000000000000000000000000000000000040401200800000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4002010100200000084002800100000000000000000000001100060002000000420014000200000000000000000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 160, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x410010200200000080405200200000000000000000000000000000000000002002010100200000240402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 161, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004040102002000800000000000000000000000000000000,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000004400402200100000000000000000000000000000000000000000000000000000000000000000000,0x8140208010000000000000000000000000000000000000000000000000000008040a200400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81402800100000000000000000000014280520002000000000000000000000000000000000000,0x81402080100000000000000000000000040020002000040000000000000000001000800400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 162, x => ((#[0x10000200200010000000000000000000000000000000000000000000000000008000100200100000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x2110081000200000160205200200000000000000000000000000000000000002110081000200000260209200100000000000000000000000000000000000002110081000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000060201200400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2050084000200001041209800100000000000000000000000000000000000002050084000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 164, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x0,0x0,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000000000000000000,0x40401200400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x8008042002000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 165, x => ((#[0x10081401002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8041002002000800000000000000000000000000000000,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8040a200400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40020002000040000000000000000000000000000000,0x40020002000040000000000000000001000800400001] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 168, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x2002010100200004040402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2002010100200000088202800100000000000000000000001208060002000000450014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000048201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 176, x => ((#[0x1028041002000000502010200200000000000000000000000000000000000000000000000000000002000100200080000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x502010200200000080405200200000000000000000000000000000000000000002000100200080240402200100000000000000000000000000000000000000002001000200080000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40a01400020000008120280010000000000000000000000104806000200000040a014000200000000000000000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 192, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 193, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004140902002000000000000000000000000000000000000,0x100805010020000000000000000000004204101002000000000000000000000000000000000000000000000000000000a0402100100000000000000000000004880504002000000000000000000000000000000000000,0x8140208010000000000000000000000802010401001000000000000000000022040a100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81402800100000000000000000000014100520002000000000000000000000000000000000000,0x8140208010000000000000000000000414090200200000000000000000000080140a800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 194, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000002028080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2028080100200000801209800100000000000000000000000000000000000002020084000200000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 196, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x1080041002000000000000000000000040210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000100008044002000000000000000000000000000000000000,0x8008042002000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x104806000200000040a014000200000000000000000000,0x8008042002000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 200, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000004000201100400000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2002010100200000084002800100000000000000000000001100060002000000420014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000044001800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 208, x => ((#[0x1028041002000000424010200200000000000000000000000000000000000000000000000000004002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 224, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200201010020000008120280010000000000000000000000104806000200000040a014000200000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000041201800400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 256, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000200201100400000,0x410010200200000080405200200000000000000000000000000000000000002002010100200000240402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x40205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000000000000000000000000000000000000040401200800000,0x40202080100000000000000000000000000000000000000000000000000000200201100400000,0x1028041002000000410010200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x410010200200000080405200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000080a02401000000,0x40401200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 257, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004140902002000000000000000000000000000000000000,0x10080501002000000000000000000000410410100200000000000000000000000000000000000000000000000000000090402100100000000000000000000004480504002000000000000000000000000000000000000,0x8140208010000000000000000000000802010401001000000000000000000021040a100400000,0x80410200200000000000000000000000000000000000000000000000000000a00402200100000000000000000000000000000000000000000000000000000000000000000000,0x8140208010000000000000000000000000000000000000000000000000000008040a200400000,0x410410100200000000000000000000000000000000000000000000000000000090402100100000000000000000000000000000000000000000000000000000080482200800000,0x8140208010000000000000000000000000000000000000000000000000000021040a100400000,0x100805010020000000000000000000004028104002000000000000000000000000000000000000000000000000000000000000000000000000000000000000200a0510002000000000000000000000000000000000000,0x414090200200000000000000000000028400a400400000,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000082802401000000,0x8040a200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 258, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000002028080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x4010080200200000000010200200002000000000000000000000000000000002028080100200000040281200100100000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000008200400002,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000080200800002,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x4010080200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x4010080200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002014082000200000004000401000002,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 259, x => ((#[0x0,0x8080100001000000000000000000000000000000000000000000000000000000000000000,0x412010100200000000000000000000000000000000000000000000000000000000008100100001000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000210008100400002,0x10200200002000000000000000000000000000000000000000000000000402090200100100000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000000008200400002,0x412010100200000000000000000000000000000000000000000000000000000000008100100001000000000000000000000000000000000000000000000000000080200800002,0x8080100001000000000000000000000000000000000000000000000000210008100400002,0x402810400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x804028400400000,0x0,0x0,0x402810400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000401000002,0x804028400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 260, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x1080041002000000000000000000000040210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040008044002000000000000000000000000000000000000,0x8008042002000000000000000000000200201100400000,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000000000000000000,0x40401200400000,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040401200800000,0x200201100400000,0x1080041002000000410010200200000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001100050002000000420012000200000000000000000000,0x8008042002000000000000000000000044001400400000,0x0,0x0,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000084002401000000,0x40401200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 261, x => ((#[0x10081401002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8141802002000000000000000000000000000000000000,0x10081401002000000000000000000000410410100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040481404002000000000000000000000000000000000000,0x820020401001000000000000000000021040a100400000,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8040a200400000,0x410410100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080482200800000,0x21040a100400000,0x10081401002000000000000000000000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000020101410002000000000000000000000000000000000000,0x814180200200000000000000000000028400a400400000,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084002401000000,0x8040a200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 262, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x200201100400000,0x4010080200200000000010200200002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8200400002,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080200800002,0x200201100400000,0x4010080200200000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002020082000200000000000000000000,0x44001400400000,0x0,0x0,0x4010080200200000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002020082000200000004000401000002,0x44001400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 264, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000002000201100400000,0x2002010100200002040402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x40202100100000000000000000000000000000000000000000000000000000040401200800000,0x40202080100000000000000000000000000000000000000000000000000002000201100400000,0x1028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x2002011000200000080a02401000000,0x40401200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 265, x => ((#[0x0,0x80080100001000000000000000000101802002000200000000000000000000000000000000,0x90402100100000000000000000000004480504002000000000000000000000000000000000000,0x90402100100000000000000000000080020104010010000000000000000000010402100400008,0x2400402200100000000000000000000000000000000000000000000000000000000000000000000,0x80080100001000000000000000000000000000000000000000000000000800402200400008,0x90402100100000000000000000000000000000000000000000000000000000080482200800000,0x90402100100000000000000000000000000000000000000000000000000000080482200800000,0x200a0510002000000000000000000000000000000000000,0x20100910002000000000000000000000000800400400001,0x0,0x0,0x82802401000000,0x84002401000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 266, x => ((#[0x2090080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000000000000000000,0x40281100100000000000000000000000000000000000000000000000000000000000000000000,0x40281080100000000000000000000000000000000000000000000000000002000201100400000,0x2090080100200000040281200100100000000000000000000000000000000000000000000000000000000000000000,0x40281080100000000000000000000000000000000000000000000000000000000000000000000,0x40281100100000000000000000000000000000000000000000000000000000000080200800002,0x40281080100000000000000000000000000000000000000000000000000002000201100400000,0x2014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x2014082000200000004000401000002,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 268, x => ((#[0x0,0x40008042002000000000000000000000000000000000000,0x40008044002000000000000000000000000000000000000,0x40008042002000000000000000000002000201100400000,0x2002011000200000000000000000000,0x40401200400000,0x40401200800000,0x2000201100400000,0x1100050002000000420012000200000000000000000000,0x40008042002000000000000000000000044001400400000,0x0,0x0,0x2002011000200000084002401000000,0x40401200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 272, x => ((#[0x1028041002000000424010200200000000000000000000000000000000000000000000000000004002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x424010200200000080405200200000000000000000000000000000000000004002010100200000240402200100000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000000000000000000000000000000000000040401200800000,0x0,0x1028041002000000424010200200000800a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000420012000200000000000000000000,0x0,0x0,0x0,0x424010200200000080405200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004002011000200000080a02401000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 273, x => ((#[0x60120901002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x20001002000040000000000000000000004100200001000000000000000000000000000000000000000000000000090402100100000000000000000000004400104002000400000000000000000000000000000000,0x0,0x80424200200000000000000000000000000000000000000000000000000000a00402200100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x80482200800000000000000000000000000000000000000000000000000000090402100100000000000000000000000000000000000000000000000000000080482200800000,0x0,0x60120901002000000000000000000000804024400200000000000000000000000000000000000000000000000000000000000000000000000000000000000020100910002000000000000000000000000000000000000,0x0,0x0,0x0,0x80424200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084002401000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 274, x => ((#[0x4024100200200000000000000000000000000000000000000000000000000004028100100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x4024100200200000000000000000000000000000000000000000000000000004028100100200000040281200100100000000000000000000000000000000000000000000000000000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000080200800002,0x0,0x4024100200200000800a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020002000200010000000000000000,0x0,0x0,0x0,0x4024100200200000800a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020002000200010004000401000002] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 276, x => ((#[0x1001002000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40008044002000000000000000000000010000100200010000000000000000000000000000000000000000000000000000000000000000000000000000000040008044002000000000000000000000000000000000000,0x0,0x4002011000200000000400200200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40401200800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040401200800000,0x0,0x1100050002000000420012000200000004000400200010000000000000000000000000000000000000000000000000000000000000000000000000000000001100050002000000420012000200000000000000000000,0x0,0x0,0x0,0x4002011000200000084002401000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004002011000200000084002401000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 280, x => ((#[0x4002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x4002010100200002040402200100000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40202100100000000000000000000000000000000000000000000000000000040401200800000,0x0,0x1028050002000000420012000200000000000000000000,0x0,0x0,0x0,0x4002011000200000080a02401000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 288, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x410010200200000080405200200000000000000000000000000000000000002002010100200000240402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x0,0x0,0x1028041002000000410010200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x410010200200000080405200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000080a02401000000,0x40401200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 289, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004040102002000800000000000000000000000000000000,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000002400402200100000000000000000000000000000000000000000000000000000000000000000000,0x8140208010000000000000000000000000000000000000000000000000000008040a200400000,0x0,0x0,0x100805010020000000000000000000004028104002000000000000000000000000000000000000000000000000000000000000000000000000000000000000500a0510002000000000000000000000000000000000000,0x20010002000040000000000000000000800400400001,0x0,0x0,0x80410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000082802401000000,0x8040a200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 290, x => ((#[0x10000200200010000000000000000000000000000000000000000000000002090080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x10000200200010000010200200002000000000000000000000000000000002090080100200000040281200100100000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000008200400002,0x0,0x0,0x2014082000200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002014082000200000000000000000000,0x40a01400400000,0x0,0x0,0x2014082000200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002014082000200000040a01401000100,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 292, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x0,0x0,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000000000000000000,0x40401200400000,0x0,0x0,0x1080041002000000410010200200000000010400200020000000000000000000000000000000000000000000000000000000000000000000000000000000000001010002000800000000000000000000000000000000,0x8008042002000000000000000000000000008400400020,0x0,0x0,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000000002401000020,0x40401200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 296, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x2002010100200002040402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x0,0x0,0x1028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000,0x0,0x0,0x2002011000200000080a02401000000,0x40401200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 304, x => ((#[0x1028041002000000004000200200100000000000000000000000000000000000000000000000000002000100200080000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x2001000200080080405200200000000000000000000000000000000000000002000100200080240402200100000000000000000000000000000000000000002001000200080000000000000000,0x0,0x0,0x0,0x1028041002000000004002000200080000800400200010000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000004002000200080000000000000000,0x0,0x0,0x0,0x2001000200080080405200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002001000200080080a02401000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 320, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x1028041002000000410010200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 321, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004140902002000000000000000000000000000000000000,0x10080501002000000000000000000000410410100200000000000000000000000000000000000000000000000000000090402100100000000000000000000004480504002000000000000000000000000000000000000,0x8140208010000000000000000000000802010401001000000000000000000021040a100400000,0x0,0x0,0x0,0x0,0x100805010020000000000000000000004028104002000000000000000000000000000000000000000000000000000000000000000000000000000000000000200a0510002000000000000000000000000000000000000,0x414090200200000000000000000000028400a400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 322, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000002028080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x4010080200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002014082000200000000000000000000,0x40a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 323, x => ((#[0x0,0x8080100001000000000000000000000000000000000000000000000000000000000000000,0x412010100200000000000000000000000000000000000000000000000000000000008100100001000000000000000000000000000000000000000000000000000000000000000,0x8080100001000000000000000000000000000000000000000000000000210008100400002,0x0,0x0,0x0,0x0,0x402810400200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x804028400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 324, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x1080041002000000000000000000000040210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000080008044002000000000000000000000000000000000000,0x8008042002000000000000000000000200201100400000,0x0,0x0,0x0,0x0,0x1080041002000000410010200200000404010400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001100050002000000420012000200000000000000000000,0x8008042002000000000000000000000044001400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 328, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000002000201100400000,0x0,0x0,0x0,0x0,0x1028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 336, x => ((#[0x1028041002000000424010200200000000000000000000000000000000000000000000000000004002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x1028041002000000424010200200000800a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000420012000200000000000000000000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 352, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x1028041002000000410010200200000400a05400200000000000000000000000000000000000000000000000000000000000000000000000000000000000001028050002000000414012000200000000000000000000,0x4008042002000000000000000000000040a01400400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 384, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000200201100400000,0x410010200200000080405200200000000000000000000000000000000000002002010100200000240402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x40205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000000000000000000000000000000000000040401200800000,0x40202080100000000000000000000000000000000000000000000000000000200201100400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 385, x => ((#[0x10080501002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81402080100000000000000000000004140902002000000000000000000000000000000000000,0x10080501002000000000000000000000000004100200001000000000000000000000000000000000000000000000000000008100100001000000000000000000081404002002000000000000000000000000000000000,0x8140208010000000000000000000000802010401001000000000000000000000040a100400080,0x80410200200000000000000000000000000000000000000000000000000000a00402200100000000000000000000000000000000000000000000000000000000000000000000,0x8140208010000000000000000000000000000000000000000000000000000008040a200400000,0x80410200200000000000000000000000000000000000000000000000000000000008100100001000000000000000000000000000000000000000000000000400402200800080,0x8140208010000000000000000000000000000000000000000000000000000008040a200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 386, x => ((#[0x4010080200200000000000000000000000000000000000000000000000000002028080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000000000000000,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000,0x4010080200200000000010200200002000000000000000000000000000000002028080100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000000008200400002,0x40205100200000000000000000000000000000000000000000000000000000040209100100000000000000000000000000000000000000000000000000000000000000000000,0x40209080100000000000000000000000000000000000000000000000000000200201100400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 388, x => ((#[0x1080041002000000410010200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x8008042002000000000000000000000000000000000000,0x1080041002000000000000000000000040210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000040008044002000000000000000000000000000000000000,0x8008042002000000000000000000000200201100400000,0x410010200200000080410200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002002011000200000000000000000000,0x40401200400000,0x40210100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040401200800000,0x200201100400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 392, x => ((#[0x2002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x40202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000201100400008,0x2002010100200000040401200100008000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000,0x40202100100000000000000000000000000000000000000000000000000000040401200800000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 400, x => ((#[0x1028041002000000424010200200000000000000000000000000000000000000000000000000004002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x0,0x424010200200000080405200200000000000000000000000000000000000004002010100200000240402200100000000000000000000000000000000000004002011000200000000000000000000,0x0,0x40205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000000000000000000000000000000000000040401200800000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 416, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x0,0x0,0x410010200200000080405200200000000000000000000000000000000000002002010100200000240402200100000000000000000000000000000000000002002011000200000000000000000000,0x40202080100000000000000000000000000000000000000000000000000000040401200400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | 448, x => ((#[0x1028041002000000410010200200000000000000000000000000000000000000000000000000002002010100200000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000000000000000000,0x1028041002000000000000000000000040205100200000000000000000000000000000000000000000000000000000040202100100000000000000000000004008044002000000000000000000000000000000000000,0x40202080100000000000000000000004008042002000000000000000000000200201100400000] : Array Nat)[x/16]?.getD 0) >>> (x % 16 * 63)
  | _, _ => 0

private def stepOK (d e s : Nat) :=
  ((e &&& s) != 0) || val s || (rankMask (d+1)).testBit (e|||s) || clash e s (witnessCodes e s)

private def rowOK (d e : Nat) :=
  !(rankMask d).testBit e || (List.range 512).all (stepOK d e)

private def doneOK (d e : Nat) :=
  !(rankMask d).testBit e || val (511 ^^^ e)

private def layer (d : Nat) (R : Finset Vertex) : Prop := ∃ m : Fin 512, (rankMask d).testBit m.val=true ∧ dec m.val=R

private theorem initialLayer : layer 0 ∅ := ⟨0,rfl,PetersenMaskBridge.decode_zero _⟩

private theorem finalLayer (d : Nat) (hd : d ≤ 4) (R : Finset Vertex) (h : layer d R) :
    ¬ BranchGraph.Independent petersenGraph (Finset.univ \ R) := by
  obtain ⟨⟨e,he⟩,re,rfl⟩ := h
  have verify : ∀ k : Fin 5, (List.range 512).all (doneOK k.val) = true := by decide +kernel
  have endState := List.all_eq_true.mp (verify ⟨d,by omega⟩) e (List.mem_range.mpr he)
  simp [doneOK,re] at endState
  have xorBound : 511 ^^^ e < 512 := Nat.xor_lt_two_pow (by decide : 511 < 2^9) he
  have cmp : Finset.univ \ dec e = dec (511 ^^^ e) := by
    ext v
    have ones : Nat.testBit 511 v.val = true := by
      exact (PetersenGroupBFS.full_at petersenNine v.val).trans (decide_eq_true v.isLt)
    simp [PetersenMaskBridge.mem_decode,Nat.testBit_xor,ones]
  rw [cmp,isIndep ⟨_,xorBound⟩]
  simp [endState]

private theorem sepBits {e s : Nat} (h : Disjoint (dec e) (dec s)) (he : e<512) :
    e &&& s = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and,Nat.zero_testBit]
  by_cases hj : j<9
  · by_contra! both
    have pair := Bool.and_eq_true_iff.mp (Bool.eq_true_of_not_eq_false both)
    exact Finset.disjoint_left.mp h (PetersenMaskBridge.mem_decode _ _ ⟨j,hj⟩ |>.mpr pair.1)
      (PetersenMaskBridge.mem_decode _ _ ⟨j,hj⟩ |>.mpr pair.2)
  · have off : e.testBit j = false := PetersenGroupBFS.high_false (width:=9) he (by omega)
    simp [off]


private def spanRows (d start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => rowOK d (start+n) && spanRows d start n

private theorem rowsHold (d start n : Nat) (h : spanRows d start n=true) (e : Nat)
    (lo : start≤e) (hi : e<start+n) : rowOK d e=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨last,prev⟩ := Bool.and_eq_true_iff.mp h
    by_cases eq : e=start+n
    · simpa [eq] using last
    · exact ih prev (by omega)
private theorem c0_0 : spanRows 0 0 32 = true := by decide +kernel
private theorem c0_1 : spanRows 0 32 32 = true := by decide +kernel
private theorem c0_2 : spanRows 0 64 32 = true := by decide +kernel
private theorem c0_3 : spanRows 0 96 32 = true := by decide +kernel
private theorem c0_4 : spanRows 0 128 32 = true := by decide +kernel
private theorem c0_5 : spanRows 0 160 32 = true := by decide +kernel
private theorem c0_6 : spanRows 0 192 32 = true := by decide +kernel
private theorem c0_7 : spanRows 0 224 32 = true := by decide +kernel
private theorem c0_8 : spanRows 0 256 32 = true := by decide +kernel
private theorem c0_9 : spanRows 0 288 32 = true := by decide +kernel
private theorem c0_10 : spanRows 0 320 32 = true := by decide +kernel
private theorem c0_11 : spanRows 0 352 32 = true := by decide +kernel
private theorem c0_12 : spanRows 0 384 32 = true := by decide +kernel
private theorem c0_13 : spanRows 0 416 32 = true := by decide +kernel
private theorem c0_14 : spanRows 0 448 32 = true := by decide +kernel
private theorem c0_15 : spanRows 0 480 32 = true := by decide +kernel
private theorem check0 (e : Nat) (he : e<512) : rowOK 0 e=true := by
  by_cases lim32 : e < 32
  · exact rowsHold _ _ _ c0_0 e (by omega) (by omega)
  by_cases lim64 : e < 64
  · exact rowsHold _ _ _ c0_1 e (by omega) (by omega)
  by_cases lim96 : e < 96
  · exact rowsHold _ _ _ c0_2 e (by omega) (by omega)
  by_cases lim128 : e < 128
  · exact rowsHold _ _ _ c0_3 e (by omega) (by omega)
  by_cases lim160 : e < 160
  · exact rowsHold _ _ _ c0_4 e (by omega) (by omega)
  by_cases lim192 : e < 192
  · exact rowsHold _ _ _ c0_5 e (by omega) (by omega)
  by_cases lim224 : e < 224
  · exact rowsHold _ _ _ c0_6 e (by omega) (by omega)
  by_cases lim256 : e < 256
  · exact rowsHold _ _ _ c0_7 e (by omega) (by omega)
  by_cases lim288 : e < 288
  · exact rowsHold _ _ _ c0_8 e (by omega) (by omega)
  by_cases lim320 : e < 320
  · exact rowsHold _ _ _ c0_9 e (by omega) (by omega)
  by_cases lim352 : e < 352
  · exact rowsHold _ _ _ c0_10 e (by omega) (by omega)
  by_cases lim384 : e < 384
  · exact rowsHold _ _ _ c0_11 e (by omega) (by omega)
  by_cases lim416 : e < 416
  · exact rowsHold _ _ _ c0_12 e (by omega) (by omega)
  by_cases lim448 : e < 448
  · exact rowsHold _ _ _ c0_13 e (by omega) (by omega)
  by_cases lim480 : e < 480
  · exact rowsHold _ _ _ c0_14 e (by omega) (by omega)
  exact rowsHold _ _ _ c0_15 e (by omega) (by omega)
private theorem c1_0 : spanRows 1 0 32 = true := by decide +kernel
private theorem c1_1 : spanRows 1 32 32 = true := by decide +kernel
private theorem c1_2 : spanRows 1 64 32 = true := by decide +kernel
private theorem c1_3 : spanRows 1 96 32 = true := by decide +kernel
private theorem c1_4 : spanRows 1 128 32 = true := by decide +kernel
private theorem c1_5 : spanRows 1 160 32 = true := by decide +kernel
private theorem c1_6 : spanRows 1 192 32 = true := by decide +kernel
private theorem c1_7 : spanRows 1 224 32 = true := by decide +kernel
private theorem c1_8 : spanRows 1 256 32 = true := by decide +kernel
private theorem c1_9 : spanRows 1 288 32 = true := by decide +kernel
private theorem c1_10 : spanRows 1 320 32 = true := by decide +kernel
private theorem c1_11 : spanRows 1 352 32 = true := by decide +kernel
private theorem c1_12 : spanRows 1 384 32 = true := by decide +kernel
private theorem c1_13 : spanRows 1 416 32 = true := by decide +kernel
private theorem c1_14 : spanRows 1 448 32 = true := by decide +kernel
private theorem c1_15 : spanRows 1 480 32 = true := by decide +kernel
private theorem check1 (e : Nat) (he : e<512) : rowOK 1 e=true := by
  by_cases lim32 : e < 32
  · exact rowsHold _ _ _ c1_0 e (by omega) (by omega)
  by_cases lim64 : e < 64
  · exact rowsHold _ _ _ c1_1 e (by omega) (by omega)
  by_cases lim96 : e < 96
  · exact rowsHold _ _ _ c1_2 e (by omega) (by omega)
  by_cases lim128 : e < 128
  · exact rowsHold _ _ _ c1_3 e (by omega) (by omega)
  by_cases lim160 : e < 160
  · exact rowsHold _ _ _ c1_4 e (by omega) (by omega)
  by_cases lim192 : e < 192
  · exact rowsHold _ _ _ c1_5 e (by omega) (by omega)
  by_cases lim224 : e < 224
  · exact rowsHold _ _ _ c1_6 e (by omega) (by omega)
  by_cases lim256 : e < 256
  · exact rowsHold _ _ _ c1_7 e (by omega) (by omega)
  by_cases lim288 : e < 288
  · exact rowsHold _ _ _ c1_8 e (by omega) (by omega)
  by_cases lim320 : e < 320
  · exact rowsHold _ _ _ c1_9 e (by omega) (by omega)
  by_cases lim352 : e < 352
  · exact rowsHold _ _ _ c1_10 e (by omega) (by omega)
  by_cases lim384 : e < 384
  · exact rowsHold _ _ _ c1_11 e (by omega) (by omega)
  by_cases lim416 : e < 416
  · exact rowsHold _ _ _ c1_12 e (by omega) (by omega)
  by_cases lim448 : e < 448
  · exact rowsHold _ _ _ c1_13 e (by omega) (by omega)
  by_cases lim480 : e < 480
  · exact rowsHold _ _ _ c1_14 e (by omega) (by omega)
  exact rowsHold _ _ _ c1_15 e (by omega) (by omega)
private theorem c2_0 : spanRows 2 0 32 = true := by decide +kernel
private theorem c2_1 : spanRows 2 32 32 = true := by decide +kernel
private theorem c2_2 : spanRows 2 64 32 = true := by decide +kernel
private theorem c2_3 : spanRows 2 96 32 = true := by decide +kernel
private theorem c2_4 : spanRows 2 128 32 = true := by decide +kernel
private theorem c2_5 : spanRows 2 160 32 = true := by decide +kernel
private theorem c2_6 : spanRows 2 192 32 = true := by decide +kernel
private theorem c2_7 : spanRows 2 224 32 = true := by decide +kernel
private theorem c2_8 : spanRows 2 256 32 = true := by decide +kernel
private theorem c2_9 : spanRows 2 288 32 = true := by decide +kernel
private theorem c2_10 : spanRows 2 320 32 = true := by decide +kernel
private theorem c2_11 : spanRows 2 352 32 = true := by decide +kernel
private theorem c2_12 : spanRows 2 384 32 = true := by decide +kernel
private theorem c2_13 : spanRows 2 416 32 = true := by decide +kernel
private theorem c2_14 : spanRows 2 448 32 = true := by decide +kernel
private theorem c2_15 : spanRows 2 480 32 = true := by decide +kernel
private theorem check2 (e : Nat) (he : e<512) : rowOK 2 e=true := by
  by_cases lim32 : e < 32
  · exact rowsHold _ _ _ c2_0 e (by omega) (by omega)
  by_cases lim64 : e < 64
  · exact rowsHold _ _ _ c2_1 e (by omega) (by omega)
  by_cases lim96 : e < 96
  · exact rowsHold _ _ _ c2_2 e (by omega) (by omega)
  by_cases lim128 : e < 128
  · exact rowsHold _ _ _ c2_3 e (by omega) (by omega)
  by_cases lim160 : e < 160
  · exact rowsHold _ _ _ c2_4 e (by omega) (by omega)
  by_cases lim192 : e < 192
  · exact rowsHold _ _ _ c2_5 e (by omega) (by omega)
  by_cases lim224 : e < 224
  · exact rowsHold _ _ _ c2_6 e (by omega) (by omega)
  by_cases lim256 : e < 256
  · exact rowsHold _ _ _ c2_7 e (by omega) (by omega)
  by_cases lim288 : e < 288
  · exact rowsHold _ _ _ c2_8 e (by omega) (by omega)
  by_cases lim320 : e < 320
  · exact rowsHold _ _ _ c2_9 e (by omega) (by omega)
  by_cases lim352 : e < 352
  · exact rowsHold _ _ _ c2_10 e (by omega) (by omega)
  by_cases lim384 : e < 384
  · exact rowsHold _ _ _ c2_11 e (by omega) (by omega)
  by_cases lim416 : e < 416
  · exact rowsHold _ _ _ c2_12 e (by omega) (by omega)
  by_cases lim448 : e < 448
  · exact rowsHold _ _ _ c2_13 e (by omega) (by omega)
  by_cases lim480 : e < 480
  · exact rowsHold _ _ _ c2_14 e (by omega) (by omega)
  exact rowsHold _ _ _ c2_15 e (by omega) (by omega)
private theorem c3_0 : spanRows 3 0 32 = true := by decide +kernel
private theorem c3_1 : spanRows 3 32 32 = true := by decide +kernel
private theorem c3_2 : spanRows 3 64 32 = true := by decide +kernel
private theorem c3_3 : spanRows 3 96 32 = true := by decide +kernel
private theorem c3_4 : spanRows 3 128 32 = true := by decide +kernel
private theorem c3_5 : spanRows 3 160 32 = true := by decide +kernel
private theorem c3_6 : spanRows 3 192 32 = true := by decide +kernel
private theorem c3_7 : spanRows 3 224 32 = true := by decide +kernel
private theorem c3_8 : spanRows 3 256 32 = true := by decide +kernel
private theorem c3_9 : spanRows 3 288 32 = true := by decide +kernel
private theorem c3_10 : spanRows 3 320 32 = true := by decide +kernel
private theorem c3_11 : spanRows 3 352 32 = true := by decide +kernel
private theorem c3_12 : spanRows 3 384 32 = true := by decide +kernel
private theorem c3_13 : spanRows 3 416 32 = true := by decide +kernel
private theorem c3_14 : spanRows 3 448 32 = true := by decide +kernel
private theorem c3_15 : spanRows 3 480 32 = true := by decide +kernel
private theorem check3 (e : Nat) (he : e<512) : rowOK 3 e=true := by
  by_cases lim32 : e < 32
  · exact rowsHold _ _ _ c3_0 e (by omega) (by omega)
  by_cases lim64 : e < 64
  · exact rowsHold _ _ _ c3_1 e (by omega) (by omega)
  by_cases lim96 : e < 96
  · exact rowsHold _ _ _ c3_2 e (by omega) (by omega)
  by_cases lim128 : e < 128
  · exact rowsHold _ _ _ c3_3 e (by omega) (by omega)
  by_cases lim160 : e < 160
  · exact rowsHold _ _ _ c3_4 e (by omega) (by omega)
  by_cases lim192 : e < 192
  · exact rowsHold _ _ _ c3_5 e (by omega) (by omega)
  by_cases lim224 : e < 224
  · exact rowsHold _ _ _ c3_6 e (by omega) (by omega)
  by_cases lim256 : e < 256
  · exact rowsHold _ _ _ c3_7 e (by omega) (by omega)
  by_cases lim288 : e < 288
  · exact rowsHold _ _ _ c3_8 e (by omega) (by omega)
  by_cases lim320 : e < 320
  · exact rowsHold _ _ _ c3_9 e (by omega) (by omega)
  by_cases lim352 : e < 352
  · exact rowsHold _ _ _ c3_10 e (by omega) (by omega)
  by_cases lim384 : e < 384
  · exact rowsHold _ _ _ c3_11 e (by omega) (by omega)
  by_cases lim416 : e < 416
  · exact rowsHold _ _ _ c3_12 e (by omega) (by omega)
  by_cases lim448 : e < 448
  · exact rowsHold _ _ _ c3_13 e (by omega) (by omega)
  by_cases lim480 : e < 480
  · exact rowsHold _ _ _ c3_14 e (by omega) (by omega)
  exact rowsHold _ _ _ c3_15 e (by omega) (by omega)
private theorem checkAll (d e : Nat) (hd : d<4) (he : e<512) : rowOK d e=true := by
  interval_cases d
  · exact check0 e he
  · exact check1 e he
  · exact check2 e he
  · exact check3 e he

theorem branchBound {gs : List Gate} (clean : CleanL 9 gs) (out : Fin (9+gs.length))
    (live : ∀ w, w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup) {f} (correct : compatible f)
    (ev : ∀ x, vl gs x out.val=f x) : 5 ≤ (circuitBranchWires (n:=9) gs).card := by
  let label : Vertex → Fin (9+gs.length) := firstInputBoundary clean out live
  let branches := circuitBranchWires (n:=9) gs
  have indep (r) : BranchGraph.Independent petersenGraph (BranchGroupsLean.bucket label r) :=
    independent clean out live distinct correct ev r
  have labels (v : Vertex) : label v = out ∨ label v ∈ branches := by
    have h := FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs v)
    exact h.imp_right in_circuit_branches.mpr
  have before (r) (mem : r ∈ branches) : r < out := by
    obtain ⟨a,_,path,_⟩ := in_circuit_branches.mp mem
    exact lt_of_lt_of_le (read_order clean path) (wire_le_output clean out live a)
  apply ordered_rank_required label out branches layer 4 labels before initialLayer
  · intro d hd r hr pred
    let E := BranchGroupsLean.below label r
    let S := BranchGroupsLean.bucket label r
    obtain ⟨⟨e,he⟩,re,es⟩ := pred
    change dec e=E at es
    obtain ⟨s,hs,ss⟩ := encodable S
    have dis : Disjoint E S := by
      apply Finset.disjoint_left.mpr
      intro v hv hs
      have lt : label v < r := (Finset.mem_filter.mp hv).2
      have eq : label v = r := (Finset.mem_filter.mp hs).2
      omega
    have dj := sepBits (es ▸ ss ▸ dis) he
    have si : val s=false := (isIndep ⟨s,hs⟩).mp (ss ▸ indep r)
    have ck := checkAll d e hd he
    simp only [rowOK,re,Bool.not_true,Bool.false_or,List.all_eq_true] at ck
    have st := ck s (List.mem_range.mpr hs)
    simp [stepOK,dj,si] at st
    rcases st with accepted|conflict
    · exact ⟨⟨e|||s,orLt he hs⟩,accepted,by rw [unionDec,es,ss]⟩
    · let w := witnessCodes e s
      obtain ⟨code,decode,ff⟩ := factorWithBase clean out live r (before r hr).le
        (Or.inr (in_circuit_branches.mp hr)) (dec (word w 0))
      exact False.elim (conflictSound correct conflict code decode (by
        intro I O inS outside
        rw [←ev]
        apply ff
        · intro v hv
          exact (Finset.mem_filter.mp (ss ▸ inS hv : v∈S)).2
        · intro v hv
          have abst := (Finset.disjoint_left.mp outside hv)
          have lt : ¬label v < r := fun h => abst (Finset.mem_union_left _ (es ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
          have eq : label v ≠ r := fun h => abst (Finset.mem_union_right _ (ss ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
          exact lt_of_le_of_ne (le_of_not_gt lt) (Ne.symm eq)))
  · intro d hd reaches
    apply finalLayer d hd _ reaches
    rw [output_complement label out branches labels before]
    exact indep out

private theorem depTable : ∀ v : Vertex, ∃ w : Vertex,
    let x := fun i : Vertex => decide (i=w)
    let y := Function.update x v (!x v)
    good x = true ∧ good y = true ∧ petersenF y ≠ petersenF x := by decide +kernel

private theorem dep {f} (c : compatible f) (v : Vertex) : Dep f v := by
  obtain ⟨w,hx,hy,ne⟩ := depTable v
  refine ⟨fun i => decide (i=w),?_⟩
  rw [c _ hy,c _ hx]
  exact ne

private theorem coTable : ∀ (v : Vertex) (b : Bool), ∃ a u w : Vertex,
    let x := Function.update (fun i => decide (i=a)) v b
    let y := Function.update (fun i => decide (i=u ∨ i=w)) v b
    good x = true ∧ good y = true ∧ petersenF x ≠ petersenF y := by decide +kernel

private theorem ncRestr {f} (c : compatible f) (v : Vertex) (b : Bool) :
    ∃ x y, f (Function.update x v b) ≠ f (Function.update y v b) := by
  obtain ⟨a,u,w,hx,hy,ne⟩ := coTable v b
  refine ⟨fun i => decide (i=a),fun i => decide (i=u ∨ i=w),?_⟩
  rw [c _ hx,c _ hy]
  exact ne

theorem leastBranches {f} (c : compatible f) (gs : List Gate) (out : ℕ)
    (least : Least 9 f gs out) : 5 ≤ (circuitBranchWires (n:=9) gs).card := by
  classical
  have nonconstant := dep_nc (dep c 0)
  have valid : out < 9 + gs.length := by
    by_contra! after
    obtain ⟨x,y,different⟩ := least.ncv nonconstant
    exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)
  let outWire : Fin (9 + gs.length) := ⟨out,valid⟩
  have live := least_read_edge_live least nonconstant (dep c) (ncRestr c) valid
  exact branchBound least.hcl outWire live (predecessors_nodup least nonconstant) c least.hev

theorem binary (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Vertex → Bool, good x = true → C.eval (List.ofFn x) = petersenF x) :
    13 ≤ nonNotCount C.gates := by
  let f (x : Vertex → Bool) := C.eval (List.ofFn x)
  have c : compatible f := correct
  have nc := dep_nc (dep c 0)
  obtain ⟨gs,o,least,budget⟩ := least_with_budget C fan (show ∀ x, C.eval (List.ofFn x) = f x by intro; rfl) nc
  have valid : o < 9 + gs.length := by
    by_contra! after
    obtain ⟨x,y,different⟩ := least.ncv nc
    exact different ((vl_beyond gs x o after).trans (vl_beyond gs y o after).symm)
  have live := least_read_edge_live least nc (dep c) (ncRestr c) valid
  let branches := circuitBranchWires (n:=9) gs
  have bl : 5 ≤ branches.card := leastBranches c gs o least
  have bb := branching_budget least.hcl valid (fun w hw hne => by
      let wire : Fin (9 + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at bb
  have total := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at total
  omega



end PartialAND
end BranchBound

namespace BranchBound
open PetersenNine PetersenCutTrace PetersenFirstGroup CircuitProof CircuitProof.Readers PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PartialOR
open PetersenScratch PetersenCutFormula PetersenCutIndependent
def blocked8 (i : Fin 8) := decide (i=2 ∨ i=5 ∨ i=6)
def good (x : Vertex → Bool) : Prop :=
  x 0 = false ∨ (petersenF (Fin.cons false (Fin.tail x)) = false ∧ Fin.tail x ≠ blocked8)
instance (x : Vertex → Bool) : Decidable (good x) := by unfold good; infer_instance
def compatible (f : (Vertex → Bool) → Bool) := ∀ x, good x → f x = petersenF x
def cutEdge (i j : Vertex) : Prop := (i=3 ∧ j=4) ∨ (i=4 ∧ j=3)
instance (i j : Vertex) : Decidable (cutEdge i j) := by unfold cutEdge; infer_instance
def kept := edges.filter (fun e => decide (e ≠ (3,4)))
def gg (b : Bool) : SimpleGraph Vertex :=
  if b then petersenGraph else PetersenNine.graph kept (by
    intro e he
    exact noLoops e (List.mem_filter.mp he).1)
instance ggDec (b : Bool) : DecidableRel (gg b).Adj := by
  cases b
  · exact fun i j => inferInstanceAs (Decidable ((i,j) ∈ kept ∨ (j,i) ∈ kept))
  · exact petersenAdjDecidable
local instance sourceDec : DecidableRel petersenGraph.Adj := petersenAdjDecidable
private theorem graphRel : ∀ (b : Bool) (i j : Vertex), (gg b).Adj i j ↔
    petersenGraph.Adj i j ∧ (b = true ∨ ¬ cutEdge i j) := by
  decide
private def maskBase (u v : Vertex) (k : Vertex) := decide (k=u ∨ k=v)

set_option maxHeartbeats 0 in
private theorem edgeTests : ∀ (i j : Vertex), petersenGraph.Adj i j → ¬ cutEdge i j →
    (∀ a c : Bool, good (pairInput i j (fun _ => false) a c) ∧
      petersenF (pairInput i j (fun _ => false) a c) = (a && c)) ∧
    ∃ u v : Vertex, ∀ a c : Bool, (a && c) = false →
      good (pairInput i j (maskBase u v) a c) ∧
      petersenF (pairInput i j (maskBase u v) a c) = (a || c) := by
  decide +kernel

theorem independent {gs : List Gate} (clean : CleanL 9 gs) (out : Fin (9 + gs.length))
    (live : ∀ w, w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    {f} (correct : compatible f) (ev : ∀ x, vl gs x out.val = f x)
    (cut : Fin (9+gs.length)) (b : Bool)
    (splitLabel : b = true → firstInputBoundary clean out live 3 ≠ firstInputBoundary clean out live 4) :
    BranchGraph.Independent (gg b) (firstInputGroup clean out live cut) := by
  intro i iIn j jIn adj
  obtain ⟨adj,disj⟩ := (graphRel b i j).mp adj
  have ie := (mem_firstInputGroup clean out live cut i).mp iIn
  have je := (mem_firstInputGroup clean out live cut j).mp jIn
  have notCut : ¬ cutEdge i j := by
    intro e
    have distinct := splitLabel (disj.resolve_right (fun h => h e))
    rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact distinct (ie.trans je.symm)
    · exact distinct (je.trans ie.symm)
  obtain ⟨ands,u,v,ors⟩ := edgeTests _ _ adj notCut
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [(mem_firstInputGroup clean out live cut i).mp iIn] at hi
  rw [(mem_firstInputGroup clean out live cut j).mp jIn] at hj
  have controlled : cut = out ∨ ∀ k : Vertex, (k = i ∨ k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with eq | block
    · exact Or.inl eq
    · exact Or.inr (fun k hk => block k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))
  have fact (base : Vertex → Bool) : ∃ o : Bool → Bool, ∀ a c,
      o (pairValue i j base (wireFormula i gs cut.val) a c) =
        f (pairInput i j base a c) := by
    obtain ⟨o,ho⟩ := cut_factors clean cut out (fun k => k=i ∨ k=j) base controlled
    refine ⟨o,fun a c => ?_⟩
    unfold pairValue
    rw [wireFormula_eval i clean _ cut.val cut.isLt, ← ev]
    apply ho
    intro k hk
    simp [pairInput,show k ≠ i from fun e => hk (Or.inl e),
      show k ≠ j from fun e => hk (Or.inr e)]
  obtain ⟨oA,hA⟩ := fact (fun _ => false)
  obtain ⟨oO,hO⟩ := fact (maskBase u v)
  exact three_pair_invariant i j _ hi hj _ _ oA oO
    (fun a c => (hA a c).trans ((correct _ (ands a c).1).trans (ands a c).2))
    (fun a c h => (hO a c).trans ((correct _ (ors a c h).1).trans (ors a c h).2))


private def one : Option Vertex → Finset Vertex
  | none => ∅
  | some i => {i}

private theorem one_rep {s : Finset Vertex} (h : s.card ≤ 1) : ∃ v, s = one v := by
  by_cases e : s = ∅
  · exact ⟨none,e⟩
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr e)
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show s.card=1 by omega)
    exact ⟨some v,hv⟩


private theorem tinyTable : ∀ (b : Bool) (i j : Option Vertex),
    let s := one i ∪ one j
    (b = true ∨ ¬ (3 ∈ s ∧ 4 ∈ s)) →
    good (setInput s) ∧ (petersenF (setInput s) = true ↔
      ∃ u ∈ s, ∃ v ∈ s, (gg b).Adj u v) := by decide +kernel

private theorem tinySplit : ∀ i j : Option Vertex, 3 ∈ one i ∪ one j → 4 ∈ one i ∪ one j →
    (3 ∈ one i ∧ 4 ∈ one j) ∨ (4 ∈ one i ∧ 3 ∈ one j) := by decide
private theorem depTable : ∀ v : Vertex, ∃ w : Vertex,
    let x := fun i : Vertex => decide (i=w)
    let y := Function.update x v (!x v)
    good x ∧ good y ∧ petersenF y ≠ petersenF x := by decide +kernel

private theorem dep {f} (c : compatible f) (v : Vertex) : Dep f v := by
  obtain ⟨w,hx,hy,ne⟩ := depTable v
  refine ⟨fun i => decide (i=w),?_⟩
  rw [c _ hy,c _ hx]
  exact ne

private theorem coTable : ∀ (v : Vertex) (b : Bool), ∃ u w : Vertex,
    let x := Function.update (fun _ => false) v b
    let y := Function.update (fun i => decide (i=u ∨ i=w)) v b
    good x ∧ good y ∧ petersenF x ≠ petersenF y := by decide +kernel

private theorem ncRestr {f} (c : compatible f) (v : Vertex) (b : Bool) :
    ∃ x y, f (Function.update x v b) ≠ f (Function.update y v b) := by
  obtain ⟨u,w,hx,hy,ne⟩ := coTable v b
  refine ⟨fun _ => false,fun i => decide (i=u ∨ i=w),?_⟩
  rw [c _ hx,c _ hy]
  exact ne

open PetersenGroupBFS in
private def no34 : MaskGraph :=
  ⟨9, fun v => (#[50, 69, 138, 260, 1, 385, 258, 36, 104] : Array Nat)[v]?.getD 0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem noFour : PetersenGroupBFS.fullMask no34 ∉ PetersenGroupBFS.frontier no34 4 := by
  decide +kernel

private theorem minusMatch : ∀ a b : Vertex, (gg false).Adj a b ↔
    (no34.adjacency a.val).testBit b.val = true := by decide

private theorem groupBound (b : Bool) (groups : List (Finset Vertex))
    (t : BranchGraph.TwinSteps (gg b) ∅ groups)
    (ended : BranchGraph.EdgelessAfter (gg b) (BranchGraph.removedThrough ∅ groups)) :
    5 ≤ groups.length := by
  cases b
  · exact @PetersenMaskBridge.groups_exceed_budget no34 (gg false) (ggDec false) minusMatch
      (inferInstance : Nonempty Vertex) 4 noFour groups t ended
  · exact @PetersenMaskBridge.petersen_nine_groups_need_five (gg true) (ggDec true) petersen_graph_matches_mask groups t ended

theorem leastBranches {f} (c : compatible f) (gs : List Gate) (out : ℕ)
    (least : Least 9 f gs out) : 5 ≤ (circuitBranchWires (n:=9) gs).card := by
  classical
  have nonconstant := dep_nc (dep c 0)
  have valid : out < 9 + gs.length := by
    by_contra! after
    obtain ⟨x,y,different⟩ := least.ncv nonconstant
    exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)
  let outWire : Fin (9 + gs.length) := ⟨out,valid⟩
  have live := least_read_edge_live least nonconstant (dep c) (ncRestr c) valid
  let label : Vertex → Fin (9 + gs.length) := firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (9 + gs.length)) := circuitBranchWires gs
  let b : Bool := decide (label 3 ≠ label 4)
  let G := gg b
  have indep (r) : BranchGraph.Independent G (BranchGroupsLean.bucket label r) :=
    independent least.hcl outWire live (predecessors_nodup least nonconstant) c least.hev r b (by simp [b]; exact id)
  have labels (v : Fin 9) : label v = outWire ∨ label v ∈ branches := by
    have stopped := FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v)
    exact stopped.imp_right in_circuit_branches.mpr
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup G
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) := by
    obtain ⟨code,decode,factors⟩ := finite_branch_bit_factor least.hcl outWire live r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp member))
    apply thin_twins G label r (indep r) code decode
    intro I O hi ho group later
    obtain ⟨i,rfl⟩ := one_rep hi
    obtain ⟨j,rfl⟩ := one_rep ho
    have ok : b = true ∨ ¬ (3 ∈ one i ∪ one j ∧ 4 ∈ one i ∪ one j) := by
      by_cases eq : label 3 = label 4
      · right
        rintro ⟨l,h⟩
        rcases tinySplit i j l h with ⟨ai,aj⟩|⟨ai,aj⟩
        · have e1 := group 3 ai
          have e2 := later 4 aj
          omega
        · have e1 := group 4 ai
          have e2 := later 3 aj
          omega
      · exact Or.inl (by simp [b,eq])
    have rows := tinyTable b i j ok
    change (∃ u ∈ _, ∃ v ∈ _, G.Adj u v) ↔ _
    rw [← rows.2, ← c _ rows.1, ← least.hev]
    exact factors _ _ group later
  exact BranchGroupsLean.roots_required G label outWire branches 5 labels before twins
    (indep outWire) (groupBound _)

theorem binary (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Vertex → Bool, good x → C.eval (List.ofFn x) = petersenF x) :
    13 ≤ nonNotCount C.gates := by
  let f (x : Vertex → Bool) := C.eval (List.ofFn x)
  have c : compatible f := correct
  have nc := dep_nc (dep c 0)
  obtain ⟨gs,o,least,budget⟩ := least_with_budget C fan (show ∀ x, C.eval (List.ofFn x) = f x by intro; rfl) nc
  have valid : o < 9 + gs.length := by
    by_contra! after
    obtain ⟨x,y,different⟩ := least.ncv nc
    exact different ((vl_beyond gs x o after).trans (vl_beyond gs y o after).symm)
  have live := least_read_edge_live least nc (dep c) (ncRestr c) valid
  let branches := circuitBranchWires (n:=9) gs
  have bl : 5 ≤ branches.card := leastBranches c gs o least
  have bb := branching_budget least.hcl valid (fun w hw hne => by
      let wire : Fin (9 + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at bb
  have total := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at total
  omega


end PartialOR
end BranchBound

namespace SignedPivotProject
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def route (flip : Bool) (i : ℕ) := if i < 9 then (if flip && (i == 0) then 9 else i) else i+1

def transport (flip : Bool) (g : Gate) : Gate := ⟨g.op, g.inputs.map (route flip)⟩

theorem run (flip : Bool) (gs : List Gate) (a b : List Bool) (n : 9 ≤ a.length)
    (len : b.length = a.length+1)
    (aligned : ∀ i, a.getD i false = b.getD (route flip i) false) :
    ∀ i, (gs.foldl step a).getD i false =
      ((gs.map (transport flip)).foldl step b).getD (route flip i) false := by
  induction gs generalizing a b with
  | nil => exact aligned
  | cons g gs ih =>
    have val : g.op.eval (g.inputs.map (fun i => a.getD i false)) =
        (transport flip g).op.eval ((transport flip g).inputs.map (fun i => b.getD i false)) := by
      change _ = g.op.eval ((g.inputs.map (route flip)).map _)
      apply congrArg g.op.eval
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => aligned i)
    apply ih (step a g) (step b (transport flip g)) (by simp [step]; omega)
      (by simp [step, len])
    intro i
    dsimp only [step]
    rw [val]
    by_cases earlier : i < a.length
    · have h : route flip i < b.length := by
        simp only [route]
        split
        · split <;> omega
        · omega
      rw [List.getD_append _ _ _ _ earlier, List.getD_append _ _ _ _ h]
      exact aligned i
    · have h : route flip i = i+1 := by simp [route, show ¬i<9 by omega]
      rw [h,List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      omega

def flipInput (x : Fin 9 → Bool) (i : Fin 9) := if i=0 then !(x 0) else x i

def routedInput (flip : Bool) (x : Fin 9 → Bool) : Fin 9 → Bool :=
  if flip then flipInput x else x

def extraBit (flip : Bool) (x : Fin 9 → Bool) := flip && !(x 0)

theorem alignedInput (flip : Bool) (x : Fin 9 → Bool) (i : ℕ) :
    (List.ofFn (routedInput flip x)).getD i false =
      (List.ofFn x ++ [extraBit flip x]).getD (route flip i) false := by
  by_cases h : i < 9
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    by_cases z : i = 0
    · subst i
      cases flip <;> simp [route, routedInput, flipInput, extraBit, List.getD_eq_getElem?_getD,
        List.getElem?_append, List.getElem?_ofFn]
    · rw [show route flip i = i by simp [route, h, z], List.getD_append _ _ _ _ (by simpa using h),
        List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
      cases flip <;> simp [routedInput, flipInput, Fin.ext_iff, z]
  · have hs : route flip i = i+1 := by simp [route, h]
    rw [hs, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def padded (D : Circuit) : Circuit := ⟨D.gates.map (transport false), route false D.output⟩

def prepended (D : Circuit) : Circuit :=
  ⟨⟨.not,[0]⟩ :: D.gates.map (transport true), route true D.output⟩

theorem padEval (D : Circuit) (x : Fin 9 → Bool) :
    D.eval (List.ofFn x) = (padded D).eval (List.ofFn x ++ [false]) :=
  run false D.gates _ _ (by simp) (by simp) (alignedInput false x) D.output

theorem prependEval (D : Circuit) (x : Fin 9 → Bool) :
    D.eval (List.ofFn (flipInput x)) = (prepended D).eval (List.ofFn x) := by
  have eq := run true D.gates _ _ (by simp) (by simp) (alignedInput true x) D.output
  have bit : step (List.ofFn x) ⟨.not,[0]⟩ = List.ofFn x ++ [extraBit true x] := by
    simp [step, GateOp.eval, extraBit, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  change _ = ((D.gates.map (transport true)).foldl step (step (List.ofFn x) ⟨.not,[0]⟩)).getD _ false
  rw [bit]
  exact eq

theorem fanMap (D : Circuit) (f : FanInTwo D) (b : Bool) :
    FanInTwo ⟨D.gates.map (transport b), route b D.output⟩ := by
  intro g hg
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
  simpa [transport] using f q hq

theorem padFan (D : Circuit) (f : FanInTwo D) : FanInTwo (padded D) := fanMap D f false

theorem prependFan (D : Circuit) (f : FanInTwo D) : FanInTwo (prepended D) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl|h
  · simp
  · exact fanMap D f true g h

theorem padSize (D : Circuit) : (padded D).size = D.size := by simp [Circuit.size,padded]

theorem count (D : Circuit) (q : GateOp → Bool) (skip : q .not = false) :
    (prepended D).gates.countP (fun g => q g.op) = D.gates.countP (fun g => q g.op) := by
  simp [prepended, List.countP_cons, List.countP_map, skip,transport,Function.comp_def]

end SignedPivotProject
namespace SignedReaderExclusion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open BranchBound
open BranchBound.PetersenScratch
open BranchBound.CircuitProof
open NegativePivotCut (seed edge Y)
open SignedOrBypass (safe Count)
open SignedPivotProject (prepended prependEval prependFan flipInput)
open PartialPetersenMonotone (target)

set_option maxHeartbeats 2000000 in
theorem samePetersen : ∀ x : Fin 9 → Bool, petersenF x = target x := by decide +kernel

theorem seedTail (x : Fin 9 → Bool) :
    seed (!(x 0)) (Fin.tail x) = List.ofFn (flipInput x) := by
  rw [seed,List.ofFn_cons,List.ofFn_succ (f := flipInput x)]
  simp [flipInput,Fin.tail]

theorem rawCorrect (D : Circuit)
    (hd : ∀ x : Fin 9 → Bool, D.eval (List.ofFn (flipInput x)) = target x) : correct D := by
  intro a y
  let x : Fin 9 → Bool := Fin.cons a y
  have hx : Fin.tail x = y := Fin.tail_cons _ _
  have h0 : x 0 = a := rfl
  have eq := hd x
  rw [←seedTail x,hx,h0] at eq
  exact eq

theorem binaryDomains (b : Bool) : DomainBound b := by
  intro D fan agrees
  have hf := prependFan D fan
  have evaluated (x : Fin 9 → Bool) (hs : safe b (x 0) (Fin.tail x)) :
      (prepended D).eval (List.ofFn x) = petersenF x := by
    rw [←prependEval,←seedTail,samePetersen]
    exact agrees (x 0) (Fin.tail x) hs
  have budget : 13 ≤ nonNotCount (prepended D).gates := by
    cases b
    · apply PartialOR.binary _ hf
      intro x h
      apply evaluated
      rcases h with h|⟨independent,ne⟩
      · exact Or.inl h
      · exact Or.inr ⟨(samePetersen (Fin.cons false (Fin.tail x))).symm.trans independent,ne⟩
    · apply PartialAND.binary _ hf
      intro x h
      apply evaluated
      simpa [PartialAND.good,safe,NegativePivotCut.seesNeighbor,Fin.tail,
        Bool.or_eq_true_iff,or_assoc] using h
  have n := SignedPivotProject.count D (fun op => !(SignedOrBypass.isNot op)) rfl
  change 13 ≤ (prepended D).gates.countP (fun g => !(SignedOrBypass.isNot g.op)) at budget
  rw [n] at budget
  exact budget

theorem excludeSigned (D : Circuit) (fan : FanInTwo D) (small : D.size ≤ 14)
    (one : SignedOrBypass.NotCount D.gates ≤ 1)
    (few : (D.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    (hd : ∀ x : Fin 9 → Bool, D.eval (List.ofFn (flipInput x)) = target x) : False :=
  signedReaderExclusion D fan small one few (rawCorrect D hd) binaryDomains
end SignedReaderExclusion

namespace SingleReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open BranchBound
open BranchBound.CircuitProof

def target (x : Fin 9 → Bool) :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

theorem budget (D : Circuit) (fan : FanInTwo D) (small : D.size ≤ 14)
    (correct : ∀ x, D.eval (List.ofFn (SignedPivotProject.flipInput x)) = target x) :
    D.gates.countP (fun g => isNotGate g.op) ≤ 1 := by
  have bin := petersen_binary_lower (SignedPivotProject.prepended D)
    (SignedPivotProject.prependFan D fan) (fun x => by
      rw [← SignedPivotProject.prependEval, correct]
      simp only [target, petersenF, PetersenNine.edgeFun, PetersenNine.edges,
        List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc])
  unfold nonNotCount at bin
  rw [SignedPivotProject.count D (fun op => !isNotGate op) rfl] at bin
  have total := nonNotCount_add_notCount D.gates
  rw [← List.countP_eq_length_filter] at total
  change D.gates.length ≤ 14 at small
  unfold nonNotCount at total
  omega

theorem result : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
    (D.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 →
    (∀ x : Fin 9 → Bool, D.eval (List.ofFn (fun i : Fin 9 => if i=0 then !(x 0) else x i)) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → False := by
  intro D fan small few correct
  have one := budget D fan small correct
  exact SignedReaderExclusion.excludeSigned D fan small one few correct
end SingleReader

end PEqualNP.Outside.L_petersen_inverted_single_reader_aux

theorem PEqualNP.Outside.L_petersen_inverted_single_reader : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
    (D.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 →
    (∀ x : Fin 9 → Bool, D.eval (List.ofFn (fun i : Fin 9 => if i=0 then !(x 0) else x i)) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → False :=
  PEqualNP.Outside.L_petersen_inverted_single_reader_aux.SingleReader.result
