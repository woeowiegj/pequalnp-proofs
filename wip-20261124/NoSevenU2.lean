import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

namespace NoSevenU2

def M6 (s : Fin 6 → Bool) : Bool :=
  (s 0 && s 2) || (s 1 && s 4) || (s 3 && s 5)

def A6 (k : Fin 4) (s : Fin 6 → Bool) : Bool :=
  match k with
  | 0 => s 0 || s 1 || s 3
  | 1 => s 1 || s 2 || s 5
  | 2 => s 0 || s 4 || s 5
  | 3 => s 2 || s 3 || s 4

def NonZeroNonMatch (s : Fin 6 → Bool) : Prop :=
  M6 s = false ∧ ∃ i : Fin 6, s i = true

def isSing (i : Fin 6) (s : Fin 6 → Bool) : Bool :=
  (List.finRange 6).all fun j => decide (s j = decide (j = i))

def Active (mode : Nat) (k : Fin 4) (s : Fin 6 → Bool) : Prop :=
  NonZeroNonMatch s ∧
  (if mode = 0 then True
   else if mode = 1 then (k = 0 ∨ k = 1 → isSing 4 s = false)
   else (k = 0 ∨ k = 1 → isSing 4 s = false) ∧ (k = 2 ∨ k = 3 → isSing 1 s = false))

def maskToFn (m : Fin 64) : Fin 6 → Bool := fun i => m.val.testBit i.val

def ActiveM (mode : Nat) (k : Fin 4) (m : Fin 64) : Bool :=
  let s := maskToFn m
  !(M6 s) && decide (m.val ≠ 0) &&
  (if mode = 0 then true
   else if mode = 1 then (!(decide (k = 0 ∨ k = 1)) || !(isSing 4 s))
   else (!(decide (k = 0 ∨ k = 1)) || !(isSing 4 s)) &&
        (!(decide (k = 2 ∨ k = 3)) || !(isSing 1 s)))

lemma maskToFn_nz : ∀ m : Fin 64, m.val ≠ 0 → ∃ i : Fin 6, (maskToFn m) i = true := by
  decide +kernel

lemma active_of_activeM (mode : Nat) (k : Fin 4) (m : Fin 64)
    (hm : ActiveM mode k m = true) : Active mode k (maskToFn m) := by
  simp only [ActiveM, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hm
  rcases hm with ⟨⟨hm0, hne⟩, hmode⟩
  refine ⟨⟨hm0, maskToFn_nz m hne⟩, ?_⟩
  by_cases h0 : mode = 0
  · simp [h0]
  · by_cases h1 : mode = 1
    · rw [if_neg h0, if_pos h1] at hmode ⊢
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hmode
      intro hk
      exact hmode.resolve_left (fun h => h hk)
    · rw [if_neg h0, if_neg h1] at hmode ⊢
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hmode
      exact ⟨fun hk => hmode.1.resolve_left (fun h => h hk),
             fun hk => hmode.2.resolve_left (fun h => h hk)⟩

structure U2Gate where
  isOr : Bool
  in1 : Nat
  p1 : Bool
  in2 : Nat
  p2 : Bool

def u2Step (w : List Bool) (g : U2Gate) : List Bool :=
  let a := Bool.xor (w.getD g.in1 false) g.p1
  let b := Bool.xor (w.getD g.in2 false) g.p2
  w ++ [if g.isOr then (a || b) else (a && b)]

def evalU2 (gs : List U2Gate) (s : Fin 6 → Bool) : List Bool :=
  gs.foldl u2Step (List.ofFn s)

def wireU2 (gs : List U2Gate) (w : Nat) (s : Fin 6 → Bool) : Bool :=
  (evalU2 gs s).getD w false

def ValidU2 (gs : List U2Gate) : Prop :=
  ∀ j : Fin gs.length, (gs.get j).in1 < 6 + j.val ∧ (gs.get j).in2 < 6 + j.val

lemma u2Step_len (w : List Bool) (g : U2Gate) : (u2Step w g).length = w.length + 1 := by
  simp [u2Step]

lemma foldl_u2Step_len (gs : List U2Gate) (w : List Bool) :
    (gs.foldl u2Step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, u2Step_len, List.length_cons]; omega

lemma foldl_u2Step_getD_lt (gs : List U2Gate) (w : List Bool) (k : Nat) (hk : k < w.length) :
    (gs.foldl u2Step w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [u2Step_len]; omega)]
    unfold u2Step
    exact List.getD_append _ _ _ _ hk

lemma wireU2_input (gs : List U2Gate) (i : Fin 6) (s : Fin 6 → Bool) :
    wireU2 gs i.val s = s i := by
  unfold wireU2 evalU2
  rw [foldl_u2Step_getD_lt gs (List.ofFn s) i.val (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

lemma wireU2_gate (gs : List U2Gate) (hv : ValidU2 gs) (j : Fin gs.length) (s : Fin 6 → Bool) :
    let g := gs.get j
    wireU2 gs (6 + j.val) s =
      let a := Bool.xor (wireU2 gs g.in1 s) g.p1
      let b := Bool.xor (wireU2 gs g.in2 s) g.p2
      if g.isOr then (a || b) else (a && b) := by
  have hsplit : gs = gs.take j.val ++ gs.get j :: gs.drop (j.val + 1) := by
    have h1 := List.take_append_drop j.val gs
    rw [List.drop_eq_getElem_cons j.isLt] at h1
    exact h1.symm
  let pre := (gs.take j.val).foldl u2Step (List.ofFn s)
  have hpreLen : pre.length = 6 + j.val := by
    rw [foldl_u2Step_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  have hfold : gs.foldl u2Step (List.ofFn s) =
      (gs.take j.val ++ gs.get j :: gs.drop (j.val + 1)).foldl u2Step (List.ofFn s) :=
    congrArg (fun l => l.foldl u2Step (List.ofFn s)) hsplit
  have hpreGet (k : Nat) (hk : k < 6 + j.val) : wireU2 gs k s = pre.getD k false := by
    unfold wireU2 evalU2
    rw [hfold, List.foldl_append]
    exact foldl_u2Step_getD_lt (gs.get j :: gs.drop (j.val + 1)) pre k (by omega)
  have h1 := (hv j).1
  have h2 := (hv j).2
  dsimp only
  rw [hpreGet _ h1, hpreGet _ h2]
  unfold wireU2 evalU2
  rw [hfold, List.foldl_append, List.foldl_cons]
  rw [foldl_u2Step_getD_lt (gs.drop (j.val + 1)) (u2Step pre (gs.get j)) (6 + j.val) (by rw [u2Step_len]; omega)]
  unfold u2Step
  rw [List.getD_append_right _ _ _ _ (by omega), hpreLen, Nat.sub_self, List.getD_cons_zero]

lemma not_literal (mode : Nat) (hm : mode ≤ 2) (k : Fin 4) (i : Fin 6) (p : Bool) :
    ∃ m : Fin 64, ActiveM mode k m = true ∧ Bool.xor ((maskToFn m) i) p ≠ A6 k (maskToFn m) := by
  interval_cases mode <;> revert k i p <;> decide +kernel

lemma not_two_literals (mode : Nat) (hm : mode ≤ 2) (k : Fin 4)
    (isOr : Bool) (i1 i2 : Fin 6) (p1 p2 pOut : Bool) :
    ∃ m : Fin 64, ActiveM mode k m = true ∧
      let a := Bool.xor ((maskToFn m) i1) p1
      let b := Bool.xor ((maskToFn m) i2) p2
      Bool.xor (if isOr then (a || b) else (a && b)) pOut ≠ A6 k (maskToFn m) := by
  interval_cases mode <;> revert k isOr i1 i2 p1 p2 pOut <;> decide +kernel

def NotDcPair (mode : Nat) (a b : Fin 4) : Prop :=
  a ≠ b ∧
  (mode = 0 ∨
   (mode = 1 ∧ ¬((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0))) ∨
   (mode = 2 ∧ ¬((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2))))

lemma all_four_values (mode : Nat) (hm : mode ≤ 2) (a b : Fin 4) (hnd : NotDcPair mode a b) (va vb : Bool) :
    ∃ m : Fin 64, ActiveM mode a m = true ∧ ActiveM mode b m = true ∧
      A6 a (maskToFn m) = va ∧ A6 b (maskToFn m) = vb := by
  interval_cases mode
  · have hab : a ≠ b := hnd.1
    clear hnd
    revert a b hab va vb; decide +kernel
  · have hab : a ≠ b ∧ ¬((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by
      rcases hnd with ⟨h1, h2 | ⟨_, h2⟩ | ⟨h2, _⟩⟩ <;> simp_all
    clear hnd
    revert a b hab va vb; decide +kernel
  · have hab : a ≠ b ∧ ¬((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) := by
      rcases hnd with ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, h2⟩⟩ <;> simp_all
    clear hnd
    revert a b hab va vb; decide +kernel

lemma master_lemma (mode : Nat) (hm : mode ≤ 2) (a b : Fin 4) (hab : a ≠ b) (pa pb : Bool) (i : Fin 6) (pl : Bool) :
    (∃ m : Fin 64, ActiveM mode a m = true ∧ Bool.xor ((maskToFn m) i) pl = true ∧ Bool.xor (A6 a (maskToFn m)) pa = false) ∨
    (∃ m : Fin 64, ActiveM mode a m = true ∧ ActiveM mode b m = true ∧
      Bool.xor (A6 a (maskToFn m)) pa = true ∧ Bool.xor ((maskToFn m) i) pl = false ∧
      Bool.xor (A6 b (maskToFn m)) pb = false) := by
  interval_cases mode <;> revert a b hab pa pb i pl <;> decide +kernel

lemma targets_distinct (mode : Nat) (hm : mode ≤ 2) (a b : Fin 4) (hab : a ≠ b) (p : Bool) :
    ∃ m : Fin 64, ActiveM mode a m = true ∧ ActiveM mode b m = true ∧
      Bool.xor (A6 a (maskToFn m)) p ≠ A6 b (maskToFn m) := by
  interval_cases mode <;> revert a b hab p <;> decide +kernel

lemma target_takes_false (mode : Nat) (hm : mode ≤ 2) (k : Fin 4) (tf : Bool) :
    ∃ m : Fin 64, ActiveM mode k m = true ∧ Bool.xor (A6 k (maskToFn m)) tf = false := by
  interval_cases mode <;> revert k tf <;> decide +kernel

lemma gate_to_or_form (isOr pa pb pOut : Bool) :
    ∃ tf q1 q2 : Bool, ∀ a b : Bool,
      Bool.xor (if isOr then (Bool.xor a pa || Bool.xor b pb) else (Bool.xor a pa && Bool.xor b pb)) pOut =
      Bool.xor (Bool.xor a q1 || Bool.xor b q2) tf := by
  cases isOr <;> cases pa <;> cases pb <;> cases pOut <;>
    first
    | exact ⟨false, false, false, by decide⟩
    | exact ⟨false, false, true, by decide⟩
    | exact ⟨false, true, false, by decide⟩
    | exact ⟨false, true, true, by decide⟩
    | exact ⟨true, false, false, by decide⟩
    | exact ⟨true, false, true, by decide⟩
    | exact ⟨true, true, false, by decide⟩
    | exact ⟨true, true, true, by decide⟩

def ComputesTarget (gs : List U2Gate) (mode : Nat) (k : Fin 4) (w : Nat) (p : Bool) : Prop :=
  ∀ s : Fin 6 → Bool, Active mode k s → Bool.xor (wireU2 gs w s) p = A6 k s

lemma computes_at_m {gs : List U2Gate} {mode : Nat} {k : Fin 4} {w : Nat} {p : Bool}
    (hc : ComputesTarget gs mode k w p) (m : Fin 64) (hm : ActiveM mode k m = true) :
    Bool.xor (wireU2 gs w (maskToFn m)) p = A6 k (maskToFn m) :=
  hc (maskToFn m) (active_of_activeM mode k m hm)

lemma out_ge_six {gs : List U2Gate} {mode : Nat} (hm : mode ≤ 2) {k : Fin 4} {w : Nat} {p : Bool}
    (hc : ComputesTarget gs mode k w p) : 6 ≤ w := by
  by_contra hlt
  have hlt' : w < 6 := by omega
  obtain ⟨m, hma, hne⟩ := not_literal mode hm k ⟨w, hlt'⟩ p
  have eq := computes_at_m hc m hma
  rw [wireU2_input gs ⟨w, hlt'⟩ (maskToFn m)] at eq
  exact hne eq

lemma outs_distinct {gs : List U2Gate} {mode : Nat} (hm : mode ≤ 2)
    {a b : Fin 4} (hab : a ≠ b) {wa wb : Nat} {pa pb : Bool}
    (ha : ComputesTarget gs mode a wa pa) (hb : ComputesTarget gs mode b wb pb) : wa ≠ wb := by
  intro heq
  subst heq
  obtain ⟨m, hma, hmb, hne⟩ := targets_distinct mode hm a b hab (Bool.xor pa pb)
  have ea := computes_at_m ha m hma
  have eb := computes_at_m hb m hmb
  apply hne
  rw [← ea, ← eb]
  cases wireU2 gs wa (maskToFn m) <;> cases pa <;> cases pb <;> rfl

lemma same_polarity_on_not_dc {gs : List U2Gate} {mode : Nat} (hm : mode ≤ 2)
    {a b : Fin 4} (hnd : NotDcPair mode a b) (w : Nat) (qa qb tfa tfb : Bool)
    (ha : ∀ m : Fin 64, ActiveM mode a m = true → Bool.xor (wireU2 gs w (maskToFn m)) qa = true →
      Bool.xor (A6 a (maskToFn m)) tfa = true)
    (hb : ∀ m : Fin 64, ActiveM mode b m = true → Bool.xor (wireU2 gs w (maskToFn m)) qb = true →
      Bool.xor (A6 b (maskToFn m)) tfb = true) : qa = qb := by
  by_contra hne
  obtain ⟨m, hma, hmb, hva, hvb⟩ := all_four_values mode hm a b hnd tfa tfb
  have h1 := ha m hma
  have h2 := hb m hmb
  rw [hva] at h1
  rw [hvb] at h2
  cases hw : wireU2 gs w (maskToFn m) <;> cases qa <;> cases qb <;> cases tfa <;> cases tfb <;> simp_all

lemma no_wire_imp_not_dc {gs : List U2Gate} {mode : Nat} (hm : mode ≤ 2)
    {a b : Fin 4} (hnd : NotDcPair mode a b) {wb : Nat} {pb q tfa : Bool}
    (hb : ∀ m : Fin 64, ActiveM mode b m = true → Bool.xor (wireU2 gs wb (maskToFn m)) pb = A6 b (maskToFn m))
    (himp : ∀ m : Fin 64, ActiveM mode a m = true →
      Bool.xor (wireU2 gs wb (maskToFn m)) q = true → Bool.xor (A6 a (maskToFn m)) tfa = true) : False := by
  obtain ⟨m, hma, hmb, hva, hvb⟩ := all_four_values mode hm a b hnd tfa (!(Bool.xor pb q))
  have h1 := himp m hma
  have h2 := hb m hmb
  rw [hva] at h1
  rw [hvb] at h2
  cases hw : wireU2 gs wb (maskToFn m) <;> cases pb <;> cases q <;> cases tfa <;> simp_all

lemma no_shared_with_lit {gs : List U2Gate} {mode : Nat} (hm : mode ≤ 2)
    {a b : Fin 4} (hab : a ≠ b) (w : Nat) (q tfa tfb : Bool) (i : Fin 6) (ql : Bool)
    (ha : ∀ m : Fin 64, ActiveM mode a m = true →
      (Bool.xor (wireU2 gs w (maskToFn m)) q || Bool.xor ((maskToFn m) i) ql) = Bool.xor (A6 a (maskToFn m)) tfa)
    (hb : ∀ m : Fin 64, ActiveM mode b m = true →
      Bool.xor (wireU2 gs w (maskToFn m)) q = true → Bool.xor (A6 b (maskToFn m)) tfb = true) : False := by
  rcases master_lemma mode hm a b hab tfa tfb i ql with ⟨m, hma, hl, hAf⟩ | ⟨m, hma, hmb, hAt, hlf, hBf⟩
  · have ho := ha m hma
    rw [hl, Bool.or_true, hAf] at ho
    exact Bool.noConfusion ho
  · have ho := ha m hma
    rw [hlf, Bool.or_false, hAt] at ho
    have h1 := hb m hmb ho
    rw [hBf] at h1
    exact Bool.noConfusion h1

lemma gate_has_non_input {gs : List U2Gate} (hv : ValidU2 gs) {mode : Nat} (hm : mode ≤ 2)
    {a : Fin 4} {j : Fin gs.length} {pa : Bool}
    (ha : ComputesTarget gs mode a (6 + j.val) pa) :
    6 ≤ (gs.get j).in1 ∨ 6 ≤ (gs.get j).in2 := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨m, hma, hne⟩ := not_two_literals mode hm a (gs.get j).isOr ⟨_, h1⟩ ⟨_, h2⟩ (gs.get j).p1 (gs.get j).p2 pa
  have eq := computes_at_m ha m hma
  rw [wireU2_gate gs hv j (maskToFn m), wireU2_input gs ⟨_, h1⟩, wireU2_input gs ⟨_, h2⟩] at eq
  exact hne eq

-- Unified pigeonhole core:
-- Given S_out : Finset (Fin 4) of pairwise NotDcPair outputs, and H : Finset (Fin gs.length)
-- containing all >=6 operands of {outJ x | x in S_out}, we must have S_out.card <= H.card!
lemma helpers_ge_pairwise_outputs {mode : Nat} (hm : mode ≤ 2) {gs : List U2Gate} (hv : ValidU2 gs)
    (outJ : Fin 4 → Fin gs.length) (outP : Fin 4 → Bool)
    (hcompJ : ∀ k : Fin 4, ComputesTarget gs mode k (6 + (outJ k).val) (outP k))
    (S_out : Finset (Fin 4))
    (hpair : ∀ a ∈ S_out, ∀ b ∈ S_out, a ≠ b → NotDcPair mode a b)
    (H : Finset (Fin gs.length))
    (hinH1 : ∀ a ∈ S_out, ∀ h6 : 6 ≤ (gs.get (outJ a)).in1,
      (⟨(gs.get (outJ a)).in1 - 6, by have := (hv (outJ a)).1; omega⟩ : Fin gs.length) ∈ H)
    (hinH2 : ∀ a ∈ S_out, ∀ h6 : 6 ≤ (gs.get (outJ a)).in2,
      (⟨(gs.get (outJ a)).in2 - 6, by have := (hv (outJ a)).2; omega⟩ : Fin gs.length) ∈ H) :
    S_out.card ≤ H.card := by
  classical
  have getOrForm (k : Fin 4) : ∃ tf q1 q2 : Bool,
      ∀ m : Fin 64, ActiveM mode k m = true →
        (Bool.xor (wireU2 gs (gs.get (outJ k)).in1 (maskToFn m)) q1 ||
         Bool.xor (wireU2 gs (gs.get (outJ k)).in2 (maskToFn m)) q2) = Bool.xor (A6 k (maskToFn m)) tf := by
    obtain ⟨tf, q1, q2, hform⟩ := gate_to_or_form (gs.get (outJ k)).isOr (gs.get (outJ k)).p1 (gs.get (outJ k)).p2 (outP k)
    refine ⟨tf, q1, q2, fun m hmk => ?_⟩
    have eq := computes_at_m (hcompJ k) m hmk
    rw [wireU2_gate gs hv (outJ k) (maskToFn m)] at eq
    have hf := hform (wireU2 gs (gs.get (outJ k)).in1 (maskToFn m)) (wireU2 gs (gs.get (outJ k)).in2 (maskToFn m))
    rw [hf] at eq
    cases hlhs : (Bool.xor (wireU2 gs (gs.get (outJ k)).in1 (maskToFn m)) q1 ||
                  Bool.xor (wireU2 gs (gs.get (outJ k)).in2 (maskToFn m)) q2) <;>
      cases hA : A6 k (maskToFn m) <;> cases tf <;> simp_all
  choose tf q1 q2 hOr using getOrForm
  -- Define Hx k : Finset (Fin gs.length) = helper indices read by outJ k
  let Hx (k : Fin 4) : Finset (Fin gs.length) :=
    H.filter fun h => (gs.get (outJ k)).in1 = 6 + h.val ∨ (gs.get (outJ k)).in2 = 6 + h.val
  have hHx_sub (k : Fin 4) : Hx k ⊆ H := Finset.filter_subset _ _
  have hHx_le2 (k : Fin 4) : (Hx k).card ≤ 2 := by
    have hsub : Hx k ⊆
        (if h1 : (gs.get (outJ k)).in1 ≥ 6 then {⟨(gs.get (outJ k)).in1 - 6, by have := (hv (outJ k)).1; omega⟩} else ∅) ∪
        (if h2 : (gs.get (outJ k)).in2 ≥ 6 then {⟨(gs.get (outJ k)).in2 - 6, by have := (hv (outJ k)).2; omega⟩} else ∅) := by
      intro h hh
      rcases (Finset.mem_filter.mp hh).2 with h1 | h2
      · apply Finset.mem_union_left
        rw [dif_pos (by omega)]
        rw [Finset.mem_singleton]
        ext; change h.val = (gs.get (outJ k)).in1 - 6; omega
      · apply Finset.mem_union_right
        rw [dif_pos (by omega)]
        rw [Finset.mem_singleton]
        ext; change h.val = (gs.get (outJ k)).in2 - 6; omega
    have hc1 : (if h1 : (gs.get (outJ k)).in1 ≥ 6 then ({⟨(gs.get (outJ k)).in1 - 6, by have := (hv (outJ k)).1; omega⟩} : Finset (Fin gs.length)) else ∅).card ≤ 1 := by
      split_ifs <;> simp
    have hc2 : (if h2 : (gs.get (outJ k)).in2 ≥ 6 then ({⟨(gs.get (outJ k)).in2 - 6, by have := (hv (outJ k)).2; omega⟩} : Finset (Fin gs.length)) else ∅).card ≤ 1 := by
      split_ifs <;> simp
    have hle := Finset.card_le_card hsub
    have hun := Finset.card_union_le
      (if h1 : (gs.get (outJ k)).in1 ≥ 6 then ({⟨(gs.get (outJ k)).in1 - 6, by have := (hv (outJ k)).1; omega⟩} : Finset (Fin gs.length)) else ∅)
      (if h2 : (gs.get (outJ k)).in2 ≥ 6 then ({⟨(gs.get (outJ k)).in2 - 6, by have := (hv (outJ k)).2; omega⟩} : Finset (Fin gs.length)) else ∅)
    omega
  have hHx_ne (k : Fin 4) (hk : k ∈ S_out) : (Hx k).Nonempty := by
    rcases gate_has_non_input hv hm (hcompJ k) with h1 | h2
    · refine ⟨⟨(gs.get (outJ k)).in1 - 6, by have := (hv (outJ k)).1; omega⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hinH1 k hk h1, Or.inl (Nat.add_sub_of_le h1).symm⟩
    · refine ⟨⟨(gs.get (outJ k)).in2 - 6, by have := (hv (outJ k)).2; omega⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hinH2 k hk h2, Or.inr (Nat.add_sub_of_le h2).symm⟩
  -- For any h in Hx k, there is a polarity q such that (wire (6+h) ^^ q = true -> A6 k ^^ tf k = true)
  have hHx_imp (k : Fin 4) (h : Fin gs.length) (hh : h ∈ Hx k) :
      ∃ q : Bool, ∀ m : Fin 64, ActiveM mode k m = true →
        Bool.xor (wireU2 gs (6 + h.val) (maskToFn m)) q = true → Bool.xor (A6 k (maskToFn m)) (tf k) = true := by
    rcases (Finset.mem_filter.mp hh).2 with h1 | h2
    · refine ⟨q1 k, fun m hmk hw => ?_⟩
      have ho := hOr k m hmk; rw [h1, hw, Bool.true_or] at ho; exact ho.symm
    · refine ⟨q2 k, fun m hmk hw => ?_⟩
      have ho := hOr k m hmk; rw [h2, hw, Bool.or_true] at ho; exact ho.symm
  -- Key privacy lemma: if (Hx a).card = 1 and h in Hx a, then for all b in S_out with b != a, h not in Hx b!
  have hD1_private (a b : Fin 4) (ha : a ∈ S_out) (hb : b ∈ S_out) (hab : a ≠ b)
      (hcard1 : (Hx a).card = 1) (h : Fin gs.length) (hha : h ∈ Hx a) (hhb : h ∈ Hx b) : False := by
    obtain ⟨qb, himpb⟩ := hHx_imp b h hhb
    have hnd := hpair a ha b hb hab
    -- Look at in1 and in2 of outJ a:
    by_cases h1lt : (gs.get (outJ a)).in1 < 6
    · -- in1 is a literal, so in2 must be 6 + h!
      have h2eq : (gs.get (outJ a)).in2 = 6 + h.val := by
        rcases (Finset.mem_filter.mp hha).2 with h1 | h2
        · omega
        · exact h2
      have hqa : ∀ m : Fin 64, ActiveM mode a m = true →
          Bool.xor (wireU2 gs (6 + h.val) (maskToFn m)) (q2 a) = true →
          Bool.xor (A6 a (maskToFn m)) (tf a) = true := by
        intro m hma hw; have ho := hOr a m hma; rw [h2eq, hw, Bool.or_true] at ho; exact ho.symm
      have hqeq : q2 a = qb := same_polarity_on_not_dc hm hnd (6 + h.val) (q2 a) qb (tf a) (tf b) hqa himpb
      apply no_shared_with_lit hm hab (6 + h.val) qb (tf a) (tf b) ⟨_, h1lt⟩ (q1 a)
      · intro m hma
        have ho := hOr a m hma
        rw [h2eq, hqeq, wireU2_input gs ⟨_, h1lt⟩ (maskToFn m)] at ho
        rw [Bool.or_comm] at ho
        exact ho
      · exact himpb
    · by_cases h2lt : (gs.get (outJ a)).in2 < 6
      · -- in2 is a literal, so in1 must be 6 + h!
        have h1eq : (gs.get (outJ a)).in1 = 6 + h.val := by
          rcases (Finset.mem_filter.mp hha).2 with h1 | h2
          · exact h1
          · omega
        have hqa : ∀ m : Fin 64, ActiveM mode a m = true →
            Bool.xor (wireU2 gs (6 + h.val) (maskToFn m)) (q1 a) = true →
            Bool.xor (A6 a (maskToFn m)) (tf a) = true := by
          intro m hma hw; have ho := hOr a m hma; rw [h1eq, hw, Bool.true_or] at ho; exact ho.symm
        have hqeq : q1 a = qb := same_polarity_on_not_dc hm hnd (6 + h.val) (q1 a) qb (tf a) (tf b) hqa himpb
        apply no_shared_with_lit hm hab (6 + h.val) qb (tf a) (tf b) ⟨_, h2lt⟩ (q2 a)
        · intro m hma
          have ho := hOr a m hma
          rw [h1eq, hqeq, wireU2_input gs ⟨_, h2lt⟩ (maskToFn m)] at ho
          exact ho
        · exact himpb
      · -- Both in1 >= 6 and in2 >= 6, and (Hx a).card = 1, so both equal 6 + h!
        have h1ge : 6 ≤ (gs.get (outJ a)).in1 := by omega
        have h2ge : 6 ≤ (gs.get (outJ a)).in2 := by omega
        let idx1 : Fin gs.length := ⟨(gs.get (outJ a)).in1 - 6, by have := (hv (outJ a)).1; omega⟩
        let idx2 : Fin gs.length := ⟨(gs.get (outJ a)).in2 - 6, by have := (hv (outJ a)).2; omega⟩
        have hm1 : idx1 ∈ Hx a := Finset.mem_filter.mpr ⟨hinH1 a ha h1ge, Or.inl (Nat.add_sub_of_le h1ge).symm⟩
        have hm2 : idx2 ∈ Hx a := Finset.mem_filter.mpr ⟨hinH2 a ha h2ge, Or.inr (Nat.add_sub_of_le h2ge).symm⟩
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard1
        have heq1 : idx1 = h := by
          have e1 : idx1 = u := by simpa [hu] using hm1
          have e2 : h = u := by simpa [hu] using hha
          exact e1.trans e2.symm
        have heq2 : idx2 = h := by
          have e1 : idx2 = u := by simpa [hu] using hm2
          have e2 : h = u := by simpa [hu] using hha
          exact e1.trans e2.symm
        have h1eq : (gs.get (outJ a)).in1 = 6 + h.val := by
          have hv1 : (gs.get (outJ a)).in1 - 6 = h.val := congrArg Fin.val heq1
          omega
        have h2eq : (gs.get (outJ a)).in2 = 6 + h.val := by
          have hv2 : (gs.get (outJ a)).in2 - 6 = h.val := congrArg Fin.val heq2
          omega
        by_cases hq : q1 a = q2 a
        · -- Then wireU2 (6 + h) ^^ (Bool.xor (q1 a) (tf a)) = A6 a on active(a)!
          have hcompH (m : Fin 64) (hma : ActiveM mode a m = true) :
              Bool.xor (wireU2 gs (6 + h.val) (maskToFn m)) (Bool.xor (q1 a) (tf a)) = A6 a (maskToFn m) := by
            have ho := hOr a m hma
            rw [h1eq, h2eq, hq, Bool.or_self] at ho
            rw [hq]
            revert ho
            generalize wireU2 gs (6 + h.val) (maskToFn m) = x
            generalize q2 a = y
            generalize tf a = z
            generalize A6 a (maskToFn m) = w
            revert x y z w; decide
          exact no_wire_imp_not_dc hm (hpair b hb a ha hab.symm) hcompH himpb
        · -- q1 a != q2 a => LHS is always true, contradicting target_takes_false!
          obtain ⟨m, hma, hmf⟩ := target_takes_false mode hm a (tf a)
          have ho := hOr a m hma
          rw [h1eq, h2eq, hmf] at ho
          revert ho hq
          generalize wireU2 gs (6 + h.val) (maskToFn m) = x
          generalize q1 a = y
          generalize q2 a = z
          revert x y z; decide
  -- Now partition S_out into D1 (card 1) and D2 (card 2)!
  let D1 := S_out.filter fun a => (Hx a).card = 1
  let D2 := S_out \ D1
  have hD1_sub : D1 ⊆ S_out := Finset.filter_subset _ _
  have hD_sum : D2.card + D1.card = S_out.card := Finset.card_sdiff_add_card_eq_card hD1_sub
  let H1 := D1.biUnion Hx
  have hH1_sub : H1 ⊆ H := by
    intro h hh
    obtain ⟨a, _, hha⟩ := Finset.mem_biUnion.mp hh
    exact hHx_sub a hha
  have hH1_card : H1.card = D1.card := by
    let f : {a : Fin 4 // a ∈ D1} → Fin gs.length := fun a =>
      (Finset.card_eq_one.mp (Finset.mem_filter.mp a.2).2).choose
    have hf_eq (a : {a : Fin 4 // a ∈ D1}) : Hx a.1 = {f a} :=
      (Finset.card_eq_one.mp (Finset.mem_filter.mp a.2).2).choose_spec
    have hImgEq : H1 = D1.attach.image f := by
      ext h
      simp only [H1, Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨a, ha, hha⟩
        refine ⟨a, ha, ?_⟩
        rw [hf_eq ⟨a, ha⟩, Finset.mem_singleton] at hha
        exact hha.symm
      · rintro ⟨a, ha, rfl⟩
        refine ⟨a, ha, ?_⟩
        rw [hf_eq ⟨a, ha⟩]
        exact Finset.mem_singleton_self _
    have hf_inj : Function.Injective f := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ heq
      by_contra hne
      have hab : a ≠ b := fun h => hne (Subtype.ext h)
      have hha : f ⟨a, ha⟩ ∈ Hx a := by rw [hf_eq ⟨a, ha⟩]; exact Finset.mem_singleton_self _
      have hhb : f ⟨a, ha⟩ ∈ Hx b := by rw [heq, hf_eq ⟨b, hb⟩]; exact Finset.mem_singleton_self _
      exact hD1_private a b (hD1_sub ha) (hD1_sub hb) hab (Finset.mem_filter.mp ha).2 (f ⟨a, ha⟩) hha hhb
    rw [hImgEq, Finset.card_image_of_injective _ hf_inj, Finset.card_attach]
  let H2 := H \ H1
  have hH_sum : H2.card + H1.card = H.card := Finset.card_sdiff_add_card_eq_card hH1_sub
  -- Every b in D2 has (Hx b).card = 2 and Hx b ⊆ H2!
  have hD2_card2 (b : Fin 4) (hb : b ∈ D2) : (Hx b).card = 2 := by
    have hbS : b ∈ S_out := (Finset.mem_sdiff.mp hb).1
    have hne1 : (Hx b).card ≠ 1 := fun h1 => (Finset.mem_sdiff.mp hb).2 (Finset.mem_filter.mpr ⟨hbS, h1⟩)
    have hpos : 0 < (Hx b).card := Finset.card_pos.mpr (hHx_ne b hbS)
    have hle2 : (Hx b).card ≤ 2 := hHx_le2 b
    omega
  have hD2_sub (b : Fin 4) (hb : b ∈ D2) : Hx b ⊆ H2 := by
    intro h hhb
    rw [Finset.mem_sdiff]
    refine ⟨hHx_sub b hhb, ?_⟩
    intro hh1
    obtain ⟨a, ha1, hha⟩ := Finset.mem_biUnion.mp hh1
    have hab : a ≠ b := fun heq => (Finset.mem_sdiff.mp hb).2 (heq ▸ ha1)
    exact hD1_private a b (hD1_sub ha1) (Finset.mem_sdiff.mp hb).1 hab (Finset.mem_filter.mp ha1).2 h hha hhb
  -- Also no two distinct a, b in D2 can have Hx a = Hx b!
  have hD2_inj : Set.InjOn Hx (D2 : Set (Fin 4)) := by
    intro a ha b hb heq
    by_contra hab
    have haS := (Finset.mem_sdiff.mp ha).1
    have hbS := (Finset.mem_sdiff.mp hb).1
    have hnd := hpair a haS b hbS hab
    -- Both outJ a and outJ b have BOTH inputs in Hx a = Hx b (distinct pair {h1, h2})!
    have ha2 : (Hx a).card = 2 := hD2_card2 a ha
    have hb2 : (Hx b).card = 2 := hD2_card2 b hb
    -- Since (Hx a).card = 2, both in1 and in2 of outJ a must be >= 6 and distinct!
    have getPair (k : Fin 4) (hk : k ∈ S_out) (hk2 : (Hx k).card = 2) :
        ∃ h1 h2 : Fin gs.length, h1 ≠ h2 ∧ Hx k = {h1, h2} ∧
          (gs.get (outJ k)).in1 = 6 + h1.val ∧ (gs.get (outJ k)).in2 = 6 + h2.val := by
      have h1ge : 6 ≤ (gs.get (outJ k)).in1 := by
        by_contra hlt
        have hsub : Hx k ⊆ if h2 : 6 ≤ (gs.get (outJ k)).in2 then
            {⟨(gs.get (outJ k)).in2 - 6, by have := (hv (outJ k)).2; omega⟩} else ∅ := by
          intro h hh
          rcases (Finset.mem_filter.mp hh).2 with h1 | h2
          · omega
          · rw [dif_pos (by omega), Finset.mem_singleton]
            ext; change h.val = (gs.get (outJ k)).in2 - 6; omega
        have hc : (Hx k).card ≤ 1 := (Finset.card_le_card hsub).trans (by split_ifs <;> simp)
        omega
      have h2ge : 6 ≤ (gs.get (outJ k)).in2 := by
        by_contra hlt
        have hsub : Hx k ⊆ {⟨(gs.get (outJ k)).in1 - 6, by have := (hv (outJ k)).1; omega⟩} := by
          intro h hh
          rcases (Finset.mem_filter.mp hh).2 with h1 | h2
          · rw [Finset.mem_singleton]
            ext; change h.val = (gs.get (outJ k)).in1 - 6; omega
          · omega
        have hc : (Hx k).card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
        omega
      let idx1 : Fin gs.length := ⟨(gs.get (outJ k)).in1 - 6, by have := (hv (outJ k)).1; omega⟩
      let idx2 : Fin gs.length := ⟨(gs.get (outJ k)).in2 - 6, by have := (hv (outJ k)).2; omega⟩
      have hm1 : idx1 ∈ Hx k := Finset.mem_filter.mpr ⟨hinH1 k hk h1ge, Or.inl (Nat.add_sub_of_le h1ge).symm⟩
      have hm2 : idx2 ∈ Hx k := Finset.mem_filter.mpr ⟨hinH2 k hk h2ge, Or.inr (Nat.add_sub_of_le h2ge).symm⟩
      have hsub : Hx k ⊆ {idx1, idx2} := by
        intro h hh
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases (Finset.mem_filter.mp hh).2 with h1 | h2
        · left; ext; change h.val = (gs.get (outJ k)).in1 - 6; omega
        · right; ext; change h.val = (gs.get (outJ k)).in2 - 6; omega
      have hne : idx1 ≠ idx2 := by
        intro heqi
        rw [heqi] at hsub
        have : (Hx k).card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
        omega
      have hEq : Hx k = {idx1, idx2} := by
        apply Finset.eq_of_subset_of_card_le hsub
        rw [Finset.card_pair hne, hk2]
      exact ⟨idx1, idx2, hne, hEq, (Nat.add_sub_of_le h1ge).symm, (Nat.add_sub_of_le h2ge).symm⟩
    obtain ⟨a1, a2, ha12, hHa, ha1eq, ha2eq⟩ := getPair a haS ha2
    obtain ⟨b1, b2, hb12, hHb, hb1eq, hb2eq⟩ := getPair b hbS hb2
    -- {a1, a2} = {b1, b2}, so either (a1=b1 ∧ a2=b2) or (a1=b2 ∧ a2=b1)!
    have hmem1 : b1 ∈ ({a1, a2} : Finset (Fin gs.length)) := by rw [← hHa, heq, hHb]; simp
    have hmem2 : b2 ∈ ({a1, a2} : Finset (Fin gs.length)) := by rw [← hHa, heq, hHb]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2
    have hsame (w1 w2 : Nat) (p1a p2a p1b p2b : Bool)
        (hOa : ∀ m : Fin 64, ActiveM mode a m = true →
          (Bool.xor (wireU2 gs w1 (maskToFn m)) p1a || Bool.xor (wireU2 gs w2 (maskToFn m)) p2a) = Bool.xor (A6 a (maskToFn m)) (tf a))
        (hOb : ∀ m : Fin 64, ActiveM mode b m = true →
          (Bool.xor (wireU2 gs w1 (maskToFn m)) p1b || Bool.xor (wireU2 gs w2 (maskToFn m)) p2b) = Bool.xor (A6 b (maskToFn m)) (tf b)) : False := by
      have hp1 : p1a = p1b := same_polarity_on_not_dc hm hnd w1 p1a p1b (tf a) (tf b)
        (fun m hma hw => by have h := hOa m hma; rw [hw, Bool.true_or] at h; exact h.symm)
        (fun m hmb hw => by have h := hOb m hmb; rw [hw, Bool.true_or] at h; exact h.symm)
      have hp2 : p2a = p2b := same_polarity_on_not_dc hm hnd w2 p2a p2b (tf a) (tf b)
        (fun m hma hw => by have h := hOa m hma; rw [hw, Bool.or_true] at h; exact h.symm)
        (fun m hmb hw => by have h := hOb m hmb; rw [hw, Bool.or_true] at h; exact h.symm)
      obtain ⟨m, hma, hmb, hne⟩ := targets_distinct mode hm a b hab (Bool.xor (tf a) (tf b))
      have ea := hOa m hma
      have eb := hOb m hmb
      rw [hp1, hp2] at ea
      have heq' := ea.symm.trans eb
      apply hne
      revert heq'
      generalize A6 a (maskToFn m) = xa
      generalize A6 b (maskToFn m) = xb
      generalize tf a = ta
      generalize tf b = tb
      revert xa xb ta tb; decide
    rcases hmem1 with rfl | rfl <;> rcases hmem2 with rfl | rfl
    · exact hb12 rfl
    · exact hsame (6 + b1.val) (6 + b2.val) (q1 a) (q2 a) (q1 b) (q2 b)
        (fun m hma => by simpa only [ha1eq, ha2eq] using hOr a m hma)
        (fun m hmb => by simpa only [hb1eq, hb2eq] using hOr b m hmb)
    · exact hsame (6 + b2.val) (6 + b1.val) (q1 a) (q2 a) (q2 b) (q1 b)
        (fun m hma => by simpa only [ha1eq, ha2eq] using hOr a m hma)
        (fun m hmb => by simpa only [hb1eq, hb2eq, Bool.or_comm] using hOr b m hmb)
    · exact hb12 rfl
  -- Now D2.image Hx ⊆ H2.powersetCard 2, so D2.card ≤ Nat.choose H2.card 2!
  have hD2_le_choose : D2.card ≤ Nat.choose H2.card 2 := by
    have himg : D2.image Hx ⊆ H2.powersetCard 2 := by
      intro s hs
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_powersetCard.mpr ⟨hD2_sub b hb, hD2_card2 b hb⟩
    calc D2.card = (D2.image Hx).card := (Finset.card_image_of_injOn hD2_inj).symm
      _ ≤ (H2.powersetCard 2).card := Finset.card_le_card himg
      _ = Nat.choose H2.card 2 := Finset.card_powersetCard 2 H2
  have hD2_le4 : D2.card ≤ 4 := by
    calc D2.card ≤ S_out.card := by omega
      _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_le_univ S_out
      _ = 4 := by decide
  -- For D2.card ≤ 4: D2.card ≤ Nat.choose H2.card 2 implies D2.card ≤ H2.card!
  have hD2_le_H2 : D2.card ≤ H2.card := by
    by_contra hgt
    have hlt : H2.card < D2.card := by omega
    have hH2_lt4 : H2.card < 4 := by omega
    have hch : Nat.choose H2.card 2 ≤ H2.card := by
      generalize hH : H2.card = n at hH2_lt4 ⊢
      interval_cases n <;> decide
    omega
  omega

lemma mode1_nd (a0 x y : Fin 4) (ha : a0 = 0 ∨ a0 = 1)
    (hx : x = a0 ∨ x = 2 ∨ x = 3) (hy : y = a0 ∨ y = 2 ∨ y = 3) (hxy : x ≠ y) : NotDcPair 1 x y := by
  unfold NotDcPair; revert a0 x y ha hx hy hxy; decide

lemma mode1_avoid (a0 x b : Fin 4) (ha : a0 = 0 ∨ a0 = 1)
    (hx : x = a0 ∨ x = 2 ∨ x = 3) (hbx : b ≠ x) (hnd : ¬ NotDcPair 1 x b) :
    (a0 = 0 ∧ x = 0 ∧ b = 1) ∨ (a0 = 1 ∧ x = 1 ∧ b = 0) := by
  rcases ha with rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> fin_cases b <;> simp_all [NotDcPair]

lemma mode2_nd (a0 c0 x y : Fin 4) (ha : a0 = 0 ∨ a0 = 1) (hc : c0 = 2 ∨ c0 = 3)
    (hx : x = a0 ∨ x = c0) (hy : y = a0 ∨ y = c0) (hxy : x ≠ y) : NotDcPair 2 x y := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all [NotDcPair]

lemma mode2_avoid (a0 c0 x b : Fin 4) (ha : a0 = 0 ∨ a0 = 1) (hc : c0 = 2 ∨ c0 = 3)
    (hx : x = a0 ∨ x = c0) (hbx : b ≠ x) (hnd : ¬ NotDcPair 2 x b) :
    (a0 = 0 ∧ x = 0 ∧ b = 1) ∨ (a0 = 1 ∧ x = 1 ∧ b = 0) ∨
    (c0 = 2 ∧ x = 2 ∧ b = 3) ∨ (c0 = 3 ∧ x = 3 ∧ b = 2) := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hx with rfl | rfl <;> fin_cases b <;> simp_all [NotDcPair]

theorem no_u2_circuit (mode : Nat) (hm : mode ≤ 2) (gs : List U2Gate) (hv : ValidU2 gs)
    (hsz : gs.length ≤ 7 - mode)
    (outW : Fin 4 → Nat) (outP : Fin 4 → Bool)
    (hout_lt : ∀ k : Fin 4, outW k < 6 + gs.length)
    (hcomp : ∀ k : Fin 4, ComputesTarget gs mode k (outW k) (outP k)) : False := by
  classical
  have hge (k : Fin 4) : 6 ≤ outW k := out_ge_six hm (hcomp k)
  let outJ (k : Fin 4) : Fin gs.length := ⟨outW k - 6, by have := hout_lt k; have := hge k; omega⟩
  have houtEq (k : Fin 4) : 6 + (outJ k).val = outW k := by simp [outJ]; have := hge k; omega
  have hcompJ (k : Fin 4) : ComputesTarget gs mode k (6 + (outJ k).val) (outP k) := by
    rw [houtEq k]; exact hcomp k
  have houtInj : Function.Injective outJ := by
    intro a b hab
    by_contra hne
    have hwd := outs_distinct hm hne (hcomp a) (hcomp b)
    have : outW a = outW b := by
      have hval := congrArg Fin.val hab
      have := houtEq a; have := houtEq b; omega
    exact hwd this
  let OutSet : Finset (Fin gs.length) := Finset.univ.image outJ
  have hOutCard : OutSet.card = 4 := by
    rw [Finset.card_image_of_injective _ houtInj]; decide
  let H : Finset (Fin gs.length) := Finset.univ \ OutSet
  have hHCard : H.card ≤ 3 - mode := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ OutSet)
    simp only [Finset.card_univ, Fintype.card_fin, hOutCard] at h
    change H.card + 4 = gs.length at h
    omega
  -- Helper: if outJ a cannot read any outJ b (for b != a), then any operand >= 6 of outJ a is in H!
  have noOutRead (a : Fin 4)
      (havoid : ∀ b : Fin 4, b ≠ a → NotDcPair mode a b ∨ outJ a ≤ outJ b) :
      (∀ h6 : 6 ≤ (gs.get (outJ a)).in1,
        (⟨(gs.get (outJ a)).in1 - 6, by have := (hv (outJ a)).1; omega⟩ : Fin gs.length) ∈ H) ∧
      (∀ h6 : 6 ≤ (gs.get (outJ a)).in2,
        (⟨(gs.get (outJ a)).in2 - 6, by have := (hv (outJ a)).2; omega⟩ : Fin gs.length) ∈ H) := by
    obtain ⟨tf, q1, q2, hform⟩ := gate_to_or_form (gs.get (outJ a)).isOr (gs.get (outJ a)).p1 (gs.get (outJ a)).p2 (outP a)
    have hOr (m : Fin 64) (hma : ActiveM mode a m = true) :
        (Bool.xor (wireU2 gs (gs.get (outJ a)).in1 (maskToFn m)) q1 ||
         Bool.xor (wireU2 gs (gs.get (outJ a)).in2 (maskToFn m)) q2) = Bool.xor (A6 a (maskToFn m)) tf := by
      have eq := computes_at_m (hcompJ a) m hma
      rw [wireU2_gate gs hv (outJ a) (maskToFn m)] at eq
      have hf := hform (wireU2 gs (gs.get (outJ a)).in1 (maskToFn m)) (wireU2 gs (gs.get (outJ a)).in2 (maskToFn m))
      rw [hf] at eq
      cases hlhs : (Bool.xor (wireU2 gs (gs.get (outJ a)).in1 (maskToFn m)) q1 ||
                    Bool.xor (wireU2 gs (gs.get (outJ a)).in2 (maskToFn m)) q2) <;>
        cases hA : A6 a (maskToFn m) <;> cases tf <;> simp_all
    constructor
    · intro h6
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hmem => ?_⟩
      obtain ⟨b, _, hbj⟩ := Finset.mem_image.mp hmem
      have hlt : (gs.get (outJ a)).in1 < 6 + (outJ a).val := (hv (outJ a)).1
      have hbjv : (outJ b).val = (gs.get (outJ a)).in1 - 6 := congrArg Fin.val hbj
      have hba : b ≠ a := by intro heq; subst heq; omega
      rcases havoid b hba with hnd | hle
      · apply no_wire_imp_not_dc hm hnd (fun m hmb => computes_at_m (hcomp b) m hmb) (q := q1) (tfa := tf)
        intro m hma hw
        have ho := hOr m hma
        have hweq : outW b = (gs.get (outJ a)).in1 := by rw [← houtEq b, hbjv]; omega
        rw [← hweq, hw, Bool.true_or] at ho
        exact ho.symm
      · have : (outJ a).val ≤ (outJ b).val := hle
        omega
    · intro h6
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hmem => ?_⟩
      obtain ⟨b, _, hbj⟩ := Finset.mem_image.mp hmem
      have hlt : (gs.get (outJ a)).in2 < 6 + (outJ a).val := (hv (outJ a)).2
      have hbjv : (outJ b).val = (gs.get (outJ a)).in2 - 6 := congrArg Fin.val hbj
      have hba : b ≠ a := by intro heq; subst heq; omega
      rcases havoid b hba with hnd | hle
      · apply no_wire_imp_not_dc hm hnd (fun m hmb => computes_at_m (hcomp b) m hmb) (q := q2) (tfa := tf)
        intro m hma hw
        have ho := hOr m hma
        have hweq : outW b = (gs.get (outJ a)).in2 := by rw [← houtEq b, hbjv]; omega
        rw [← hweq, hw, Bool.or_true] at ho
        exact ho.symm
      · have : (outJ a).val ≤ (outJ b).val := hle
        omega
  -- Now instantiate S_out for mode = 0, 1, 2!
  interval_cases mode
  · -- mode = 0: S_out = univ (card 4), H.card ≤ 3
    have hle := helpers_ge_pairwise_outputs (mode := 0) (by omega) hv outJ outP hcompJ Finset.univ
      (fun a _ b _ hab => ⟨hab, Or.inl rfl⟩) H
      (fun a _ => (noOutRead a (fun b hba => Or.inl ⟨hba.symm, Or.inl rfl⟩)).1)
      (fun a _ => (noOutRead a (fun b hba => Or.inl ⟨hba.symm, Or.inl rfl⟩)).2)
    have hc : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    omega
  · -- mode = 1: pick earlier a ∈ {0, 1}, S_out = {a, 2, 3} (card 3), H.card ≤ 2
    let a : Fin 4 := if outJ 0 ≤ outJ 1 then 0 else 1
    have ha01 : a = 0 ∨ a = 1 := by dsimp [a]; split_ifs <;> simp
    have ha_le : (a = 0 → outJ 0 ≤ outJ 1) ∧ (a = 1 → outJ 1 ≤ outJ 0) := by
      dsimp [a]; split_ifs with h
      · exact ⟨fun _ => h, fun h1 => by simp at h1⟩
      · exact ⟨fun h0 => by simp at h0, fun _ => le_of_not_ge h⟩
    let S_out : Finset (Fin 4) := {a, 2, 3}
    have hcard : S_out.card = 3 := by
      have ha2 : a ≠ 2 := by rcases ha01 with h | h <;> rw [h] <;> decide
      have ha3 : a ≠ 3 := by rcases ha01 with h | h <;> rw [h] <;> decide
      have h23 : (2 : Fin 4) ≠ 3 := by decide
      rw [Finset.card_insert_of_notMem (by simp [ha2, ha3]), Finset.card_pair h23]
    have hnd_of (x y : Fin 4) (hx : x ∈ S_out) (hy : y ∈ S_out) (hxy : x ≠ y) : NotDcPair 1 x y := by
      simp only [S_out, Finset.mem_insert, Finset.mem_singleton] at hx hy
      exact mode1_nd a x y ha01 hx hy hxy
    have havoid (x : Fin 4) (hx : x ∈ S_out) (b : Fin 4) (hbx : b ≠ x) : NotDcPair 1 x b ∨ outJ x ≤ outJ b := by
      by_cases hnd : NotDcPair 1 x b
      · exact Or.inl hnd
      · right
        simp only [S_out, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases mode1_avoid a x b ha01 hx hbx hnd with ⟨ha0, rfl, rfl⟩ | ⟨ha1, rfl, rfl⟩
        · exact ha_le.1 ha0
        · exact ha_le.2 ha1
    have hle := helpers_ge_pairwise_outputs (mode := 1) (by omega) hv outJ outP hcompJ S_out
      (fun a ha b hb => hnd_of a b ha hb) H
      (fun x hx => (noOutRead x (havoid x hx)).1)
      (fun x hx => (noOutRead x (havoid x hx)).2)
    omega
  · -- mode = 2: pick earlier a ∈ {0, 1} and earlier c ∈ {2, 3}, S_out = {a, c} (card 2), H.card ≤ 1
    let a : Fin 4 := if outJ 0 ≤ outJ 1 then 0 else 1
    let c : Fin 4 := if outJ 2 ≤ outJ 3 then 2 else 3
    have ha01 : a = 0 ∨ a = 1 := by dsimp [a]; split_ifs <;> simp
    have hc23 : c = 2 ∨ c = 3 := by dsimp [c]; split_ifs <;> simp
    have ha_le : (a = 0 → outJ 0 ≤ outJ 1) ∧ (a = 1 → outJ 1 ≤ outJ 0) := by
      dsimp [a]; split_ifs with h
      · exact ⟨fun _ => h, fun h1 => by simp at h1⟩
      · exact ⟨fun h0 => by simp at h0, fun _ => le_of_not_ge h⟩
    have hc_le : (c = 2 → outJ 2 ≤ outJ 3) ∧ (c = 3 → outJ 3 ≤ outJ 2) := by
      dsimp [c]; split_ifs with h
      · exact ⟨fun _ => h, fun h1 => by simp at h1⟩
      · exact ⟨fun h0 => by simp at h0, fun _ => le_of_not_ge h⟩
    let S_out : Finset (Fin 4) := {a, c}
    have hcard : S_out.card = 2 := by
      have hac : a ≠ c := by rcases ha01 with ha | ha <;> rcases hc23 with hc | hc <;> rw [ha, hc] <;> decide
      exact Finset.card_pair hac
    have hnd_of (x y : Fin 4) (hx : x ∈ S_out) (hy : y ∈ S_out) (hxy : x ≠ y) : NotDcPair 2 x y := by
      simp only [S_out, Finset.mem_insert, Finset.mem_singleton] at hx hy
      exact mode2_nd a c x y ha01 hc23 hx hy hxy
    have havoid (x : Fin 4) (hx : x ∈ S_out) (b : Fin 4) (hbx : b ≠ x) : NotDcPair 2 x b ∨ outJ x ≤ outJ b := by
      by_cases hnd : NotDcPair 2 x b
      · exact Or.inl hnd
      · right
        simp only [S_out, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases mode2_avoid a c x b ha01 hc23 hx hbx hnd with ⟨ha0, rfl, rfl⟩ | ⟨ha1, rfl, rfl⟩ | ⟨hc2, rfl, rfl⟩ | ⟨hc3, rfl, rfl⟩
        · exact ha_le.1 ha0
        · exact ha_le.2 ha1
        · exact hc_le.1 hc2
        · exact hc_le.2 hc3
    have hle := helpers_ge_pairwise_outputs (mode := 2) (by omega) hv outJ outP hcompJ S_out
      (fun a ha b hb => hnd_of a b ha hb) H
      (fun x hx => (noOutRead x (havoid x hx)).1)
      (fun x hx => (noOutRead x (havoid x hx)).2)
    omega

end NoSevenU2
