import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ProveLowBin
import NoSevenU2

namespace TreeExtract

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.ProveLowBin
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup PetersenTen
open NoSevenU2 Relation

/-!
  Part 1: Ordered 4-independent-set isomorphism for Petersen P_10
  and finite Boolean helper lemmas on M6 / A6.
-/

def fnToMask (s : Fin 6 → Bool) : Fin 64 :=
  ⟨(if s 0 then 1 else 0) + (if s 1 then 2 else 0) + (if s 2 then 4 else 0) +
   (if s 3 then 8 else 0) + (if s 4 then 16 else 0) + (if s 5 then 32 else 0), by
    cases s 0 <;> cases s 1 <;> cases s 2 <;> cases s 3 <;> cases s 4 <;> cases s 5 <;> decide⟩

lemma maskToFn_fnToMask (s : Fin 6 → Bool) : maskToFn (fnToMask s) = s := by
  funext i
  have h : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ j : Fin 6,
      maskToFn (fnToMask ![b0, b1, b2, b3, b4, b5]) j = ![b0, b1, b2, b3, b4, b5] j := by
    decide +kernel
  have hseq : s = ![s 0, s 1, s 2, s 3, s 4, s 5] := by
    funext j; fin_cases j <;> rfl
  conv_lhs => rw [hseq]
  conv_rhs => rw [hseq]
  exact h (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) i

lemma fnToMask_ne_zero {s : Fin 6 → Bool} (h : ∃ i : Fin 6, s i = true) :
    (fnToMask s).val ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  intro hz
  have h0 : maskToFn (fnToMask s) i = false := by
    simp [maskToFn, hz]
  rw [maskToFn_fnToMask s, hi] at h0
  exact Bool.noConfusion h0

lemma a6_any_three (a b c : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : Fin 6 → Bool) (hm : M6 s = false) (hnz : ∃ i : Fin 6, s i = true) :
    A6 a s = true ∨ A6 b s = true ∨ A6 c s = true := by
  have h : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c → ∀ m : Fin 64,
      M6 (maskToFn m) = false → m.val ≠ 0 →
      A6 a (maskToFn m) = true ∨ A6 b (maskToFn m) = true ∨ A6 c (maskToFn m) = true := by
    decide +kernel
  have hm' : M6 (maskToFn (fnToMask s)) = false := by rwa [maskToFn_fnToMask]
  have res := h a b c hab hac hbc (fnToMask s) hm' (fnToMask_ne_zero hnz)
  rwa [maskToFn_fnToMask] at res

lemma a6_pair_01 (s : Fin 6 → Bool) (hm : M6 s = false) (hnz : ∃ i : Fin 6, s i = true)
    (hs : isSing 4 s = false) : A6 0 s = true ∨ A6 1 s = true := by
  have h : ∀ m : Fin 64, M6 (maskToFn m) = false → m.val ≠ 0 → isSing 4 (maskToFn m) = false →
      A6 0 (maskToFn m) = true ∨ A6 1 (maskToFn m) = true := by
    decide +kernel
  have res := h (fnToMask s) (by rwa [maskToFn_fnToMask]) (fnToMask_ne_zero hnz) (by rwa [maskToFn_fnToMask])
  rwa [maskToFn_fnToMask] at res

lemma a6_pair_23 (s : Fin 6 → Bool) (hm : M6 s = false) (hnz : ∃ i : Fin 6, s i = true)
    (hs : isSing 1 s = false) : A6 2 s = true ∨ A6 3 s = true := by
  have h : ∀ m : Fin 64, M6 (maskToFn m) = false → m.val ≠ 0 → isSing 1 (maskToFn m) = false →
      A6 2 (maskToFn m) = true ∨ A6 3 (maskToFn m) = true := by
    decide +kernel
  have res := h (fnToMask s) (by rwa [maskToFn_fnToMask]) (fnToMask_ne_zero hnz) (by rwa [maskToFn_fnToMask])
  rwa [maskToFn_fnToMask] at res

lemma a6_common_nbr (a b : Fin 4) :
    ∃ s : Fin 6 → Bool, M6 s = false ∧ A6 a s = true ∧ A6 b s = true := by
  have h : ∀ a b : Fin 4, ∃ m : Fin 64, M6 (maskToFn m) = false ∧
      A6 a (maskToFn m) = true ∧ A6 b (maskToFn m) = true := by
    decide +kernel
  obtain ⟨m, hm⟩ := h a b
  exact ⟨maskToFn m, hm⟩

def commonNbr (u v : V10) : V10 :=
  ((List.finRange 10).find? fun w => p10Adj u w && p10Adj v w).getD 0

def sigmaOf (ι : Fin 4 → V10) : Fin 6 → V10
  | 0 => commonNbr (ι 0) (ι 2)
  | 1 => commonNbr (ι 0) (ι 1)
  | 2 => commonNbr (ι 1) (ι 3)
  | 3 => commonNbr (ι 0) (ι 3)
  | 4 => commonNbr (ι 2) (ι 3)
  | 5 => commonNbr (ι 1) (ι 2)

def m6Adj (j1 j2 : Fin 6) : Bool :=
  (j1 == 0 && j2 == 2) || (j1 == 2 && j2 == 0) ||
  (j1 == 1 && j2 == 4) || (j1 == 4 && j2 == 1) ||
  (j1 == 3 && j2 == 5) || (j1 == 5 && j2 == 3)

def a6Adj (k : Fin 4) (j : Fin 6) : Bool :=
  A6 k (fun i => decide (i = j))

def validIndep4 (a0 a1 a2 a3 : V10) : Bool :=
  let ι : Fin 4 → V10 := ![a0, a1, a2, a3]
  (List.finRange 4).all fun p =>
    (List.finRange 4).all fun q =>
      if p == q then true else (ι p != ι q) && !(p10Adj (ι p) (ι q))

def sigmaProps (a0 a1 a2 a3 : V10) : Bool :=
  let ι : Fin 4 → V10 := ![a0, a1, a2, a3]
  let σ := sigmaOf ι
  ((List.finRange 6).all fun j1 =>
    (List.finRange 6).all fun j2 =>
      (if j1 == j2 then true else σ j1 != σ j2) &&
      (p10Adj (σ j1) (σ j2) == m6Adj j1 j2)) &&
  ((List.finRange 4).all fun k =>
    (List.finRange 6).all fun j =>
      (ι k != σ j) && (p10Adj (ι k) (σ j) == a6Adj k j)) &&
  ((List.finRange 10).all fun v =>
    (List.finRange 4).any (fun k => ι k == v) ||
    (List.finRange 6).any (fun j => σ j == v))

lemma p10_indep4_sigma_ok :
    ∀ a0 a1 a2 a3 : V10, validIndep4 a0 a1 a2 a3 = true → sigmaProps a0 a1 a2 a3 = true := by
  decide +kernel

def combine (ι : Fin 4 → V10) (σ : Fin 6 → V10) (u : Fin 4 → Bool) (s : Fin 6 → Bool) (v : V10) : Bool :=
  match (List.finRange 4).find? (fun k => ι k == v) with
  | some k => u k
  | none =>
    match (List.finRange 6).find? (fun j => σ j == v) with
    | some j => s j
    | none => false

lemma ordered_indep4_iso (ι : Fin 4 → V10) (hinj : Function.Injective ι)
    (hind : ∀ p q : Fin 4, ¬ p10Graph.Adj (ι p) (ι q)) :
    let σ := sigmaOf ι
    Function.Injective σ ∧
    (∀ k : Fin 4, ∀ j : Fin 6, ι k ≠ σ j) ∧
    (∀ v : V10, (∃ k : Fin 4, ι k = v) ∨ (∃ j : Fin 6, σ j = v)) ∧
    (∀ u s k, combine ι σ u s (ι k) = u k) ∧
    (∀ u s j, combine ι σ u s (σ j) = s j) ∧
    (∀ u s, p10F (combine ι σ u s) =
      (M6 s || (u 0 && A6 0 s) || (u 1 && A6 1 s) || (u 2 && A6 2 s) || (u 3 && A6 3 s))) := by
  have hι_eq : ι = ![ι 0, ι 1, ι 2, ι 3] := by
    funext k; fin_cases k <;> rfl
  have hval : validIndep4 (ι 0) (ι 1) (ι 2) (ι 3) = true := by
    simp only [validIndep4, List.all_eq_true, List.mem_finRange, true_implies]
    intro p q
    by_cases hpq : p = q
    · simp [hpq]
    · simp only [beq_iff_eq, hpq, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
      have h1 : ![ι 0, ι 1, ι 2, ι 3] p = ι p := by rw [← hι_eq]
      have h2 : ![ι 0, ι 1, ι 2, ι 3] q = ι q := by rw [← hι_eq]
      rw [h1, h2]
      refine ⟨fun h => hpq (hinj h), ?_⟩
      cases ha : p10Adj (ι p) (ι q)
      · rfl
      · exact False.elim (hind p q ha)
  have hsp := p10_indep4_sigma_ok (ι 0) (ι 1) (ι 2) (ι 3) hval
  simp only [sigmaProps, ← hι_eq, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, true_implies, beq_iff_eq, bne_iff_ne] at hsp
  clear hι_eq
  rcases hsp with ⟨⟨hSS, hIS⟩, hcov⟩
  let σ := sigmaOf ι
  have hσ_inj : Function.Injective σ := by
    intro j1 j2 heq
    by_contra hne
    have h1 := (hSS j1 j2).1
    simp only [hne, ↓reduceIte, bne_iff_ne] at h1
    exact h1 heq
  have hdisj : ∀ k : Fin 4, ∀ j : Fin 6, ι k ≠ σ j := fun k j => (hIS k j).1
  have hcover : ∀ v : V10, (∃ k : Fin 4, ι k = v) ∨ (∃ j : Fin 6, σ j = v) := by
    intro v
    rcases Bool.or_eq_true_iff.mp (hcov v) with h1 | h2
    · simp only [List.any_eq_true, List.mem_finRange, true_and, beq_iff_eq] at h1
      exact Or.inl h1
    · simp only [List.any_eq_true, List.mem_finRange, true_and, beq_iff_eq] at h2
      exact Or.inr h2
  have hcombI : ∀ u s k, combine ι σ u s (ι k) = u k := by
    intro u s k
    unfold combine
    cases hf : (List.finRange 4).find? (fun k' => ι k' == ι k) with
    | none =>
      have hnone := List.find?_eq_none.mp hf k (List.mem_finRange k)
      simp at hnone
    | some k' =>
      have hsome := List.find?_some hf
      simp only [beq_iff_eq] at hsome
      rw [hinj hsome]
  have hcombS : ∀ u s j, combine ι σ u s (σ j) = s j := by
    intro u s j
    unfold combine
    have hnoneI : (List.finRange 4).find? (fun k' => ι k' == σ j) = none := by
      rw [List.find?_eq_none]
      intro k' _
      simp [hdisj k' j]
    rw [hnoneI]
    cases hf : (List.finRange 6).find? (fun j' => σ j' == σ j) with
    | none =>
      have hnone := List.find?_eq_none.mp hf j (List.mem_finRange j)
      simp at hnone
    | some j' =>
      have hsome := List.find?_some hf
      simp only [beq_iff_eq] at hsome
      rw [hσ_inj hsome]
  have hAdjSS : ∀ j1 j2 : Fin 6, p10Adj (σ j1) (σ j2) = m6Adj j1 j2 := fun j1 j2 => (hSS j1 j2).2
  have hAdjIS : ∀ k : Fin 4, ∀ j : Fin 6, p10Adj (ι k) (σ j) = a6Adj k j := fun k j => (hIS k j).2
  have hA6_iff : ∀ k : Fin 4, ∀ s : Fin 6 → Bool,
      A6 k s = true ↔ ∃ j : Fin 6, a6Adj k j = true ∧ s j = true := by
    intro k s
    fin_cases k <;> simp only [A6, a6Adj, Bool.or_eq_true]
    · constructor
      · rintro ((h | h) | h)
        · exact ⟨0, by decide, h⟩
        · exact ⟨1, by decide, h⟩
        · exact ⟨3, by decide, h⟩
      · rintro ⟨j, hj, hs⟩; fin_cases j <;> simp_all
    · constructor
      · rintro ((h | h) | h)
        · exact ⟨1, by decide, h⟩
        · exact ⟨2, by decide, h⟩
        · exact ⟨5, by decide, h⟩
      · rintro ⟨j, hj, hs⟩; fin_cases j <;> simp_all
    · constructor
      · rintro ((h | h) | h)
        · exact ⟨0, by decide, h⟩
        · exact ⟨4, by decide, h⟩
        · exact ⟨5, by decide, h⟩
      · rintro ⟨j, hj, hs⟩; fin_cases j <;> simp_all
    · constructor
      · rintro ((h | h) | h)
        · exact ⟨2, by decide, h⟩
        · exact ⟨3, by decide, h⟩
        · exact ⟨4, by decide, h⟩
      · rintro ⟨j, hj, hs⟩; fin_cases j <;> simp_all
  have hM6_iff : ∀ s : Fin 6 → Bool,
      M6 s = true ↔ ∃ j1 j2 : Fin 6, m6Adj j1 j2 = true ∧ s j1 = true ∧ s j2 = true := by
    intro s
    simp only [M6, Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact ⟨0, 2, by decide, h1, h2⟩
      · exact ⟨1, 4, by decide, h1, h2⟩
      · exact ⟨3, 5, by decide, h1, h2⟩
    · rintro ⟨j1, j2, hm, h1, h2⟩
      fin_cases j1 <;> fin_cases j2 <;> simp_all [m6Adj]
  refine ⟨hσ_inj, hdisj, hcover, hcombI, hcombS, ?_⟩
  intro u s
  rw [Bool.eq_iff_iff, p10F_eq_edgeValue]
  simp only [PetersenScratch.edgeValue, decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨v1, v2, hadj, hv1, hv2⟩
    rcases hcover v1 with ⟨k1, rfl⟩ | ⟨j1, rfl⟩ <;> rcases hcover v2 with ⟨k2, rfl⟩ | ⟨j2, rfl⟩
    · exact False.elim (hind k1 k2 hadj)
    · rw [hcombI] at hv1; rw [hcombS] at hv2
      have ha : a6Adj k1 j2 = true := by rw [← hAdjIS]; exact hadj
      have hA : A6 k1 s = true := (hA6_iff k1 s).mpr ⟨j2, ha, hv2⟩
      fin_cases k1
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hv1, hA⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨hv1, hA⟩))
      · exact Or.inl (Or.inr ⟨hv1, hA⟩)
      · exact Or.inr ⟨hv1, hA⟩
    · rw [hcombS] at hv1; rw [hcombI] at hv2
      have ha : a6Adj k2 j1 = true := by rw [← hAdjIS]; exact p10Adj_symm _ _ hadj
      have hA : A6 k2 s = true := (hA6_iff k2 s).mpr ⟨j1, ha, hv1⟩
      fin_cases k2
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hv2, hA⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨hv2, hA⟩))
      · exact Or.inl (Or.inr ⟨hv2, hA⟩)
      · exact Or.inr ⟨hv2, hA⟩
    · rw [hcombS] at hv1 hv2
      have hm : m6Adj j1 j2 = true := by rw [← hAdjSS]; exact hadj
      exact Or.inl (Or.inl (Or.inl (Or.inl ((hM6_iff s).mpr ⟨j1, j2, hm, hv1, hv2⟩))))
  · intro hrhs
    have ofK : ∀ k : Fin 4, u k = true → A6 k s = true →
        ∃ v1 v2 : V10, p10Graph.Adj v1 v2 ∧ combine ι σ u s v1 = true ∧ combine ι σ u s v2 = true := by
      intro k huk hAk
      obtain ⟨j, haj, hsj⟩ := (hA6_iff k s).mp hAk
      refine ⟨ι k, σ j, ?_, by rw [hcombI]; exact huk, by rw [hcombS]; exact hsj⟩
      change p10Adj (ι k) (σ j) = true
      rw [hAdjIS]; exact haj
    rcases hrhs with (((hM | ⟨hu0, hA0⟩) | ⟨hu1, hA1⟩) | ⟨hu2, hA2⟩) | ⟨hu3, hA3⟩
    · obtain ⟨j1, j2, hm, h1, h2⟩ := (hM6_iff s).mp hM
      refine ⟨σ j1, σ j2, ?_, by rw [hcombS]; exact h1, by rw [hcombS]; exact h2⟩
      change p10Adj (σ j1) (σ j2) = true
      rw [hAdjSS]; exact hm
    · exact ofK 0 hu0 hA0
    · exact ofK 1 hu1 hA1
    · exact ofK 2 hu2 hA2
    · exact ofK 3 hu3 hA3

/-!
  Part 2: Tree extraction, edge counting, active-high monotonicity,
  and reduction to NoSevenU2.no_u2_circuit.
-/

lemma nonNotCount_eq_card_filter (gs : List Gate) :
    nonNotCount gs = (Finset.univ.filter fun p : Fin gs.length => !(isNotGate (gs.get p).op)).card := by
  unfold nonNotCount
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.countP_cons, ih]
    let f : Fin (g :: gs).length → Bool := fun p => !(isNotGate ((g :: gs).get p).op)
    let S := Finset.univ.filter fun p : Fin (g :: gs).length => f p = true
    let S0 := Finset.univ.filter fun p : Fin gs.length => !(isNotGate (gs.get p).op) = true
    have hbij : S = (if !(isNotGate g.op) then {(0 : Fin (g :: gs).length)} else ∅) ∪
        S0.image Fin.succ := by
      ext p
      cases p using Fin.cases with
      | zero =>
        simp only [S, f, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image, Fin.succ_ne_zero, and_false, exists_false, or_false]
        split_ifs with h
        · simp [h]
        · simp [h]
      | succ q =>
        simp only [S, S0, f, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image, List.get_eq_getElem, List.getElem_cons_succ]
        constructor
        · intro hq
          exact Or.inr ⟨q, hq, rfl⟩
        · rintro (h0 | ⟨q', hq', heq⟩)
          · split_ifs at h0
            · simp only [Finset.mem_singleton] at h0
              exact False.elim (Fin.succ_ne_zero q h0)
            · simp at h0
          · have : q' = q := Fin.succ_injective _ heq
            subst this; exact hq'
    have hdisj : Disjoint
        (if !(isNotGate g.op) then ({(0 : Fin (g :: gs).length)} : Finset _) else ∅)
        (S0.image Fin.succ) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp2
      split_ifs at hp1
      · simp only [Finset.mem_singleton] at hp1
        exact Fin.succ_ne_zero q hp1
      · simp at hp1
    have hcard : S.card = (if !(isNotGate g.op) then 1 else 0) + S0.card := by
      rw [hbij, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (Fin.succ_injective _)]
      split_ifs <;> simp
    change S0.card + (if !(isNotGate g.op) then 1 else 0) = S.card
    omega

lemma gate_read_inputs {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (p : Fin gs.length) (u : Fin (n + gs.length)) :
    readEdge gs u ⟨n + p.val, by omega⟩ ↔ u.val ∈ (gs.get p).inputs := by
  constructor
  · rintro ⟨p', g', hp', heq, hmem⟩
    dsimp at heq
    have hp'eq : p' = p.val := by omega
    subst hp'eq
    rw [List.getElem?_eq_getElem p.isLt] at hp'
    cases hp'
    simpa [List.get_eq_getElem] using hmem
  · intro hmem
    refine ⟨p.val, gs.get p, ?_, rfl, hmem⟩
    rw [List.getElem?_eq_getElem p.isLt, List.get_eq_getElem]

lemma no_read_into_input {n : Nat} {gs : List Gate} (u v : Fin (n + gs.length)) (hv : v.val < n) :
    ¬ readEdge gs u v := by
  rintro ⟨p, g, _, heq, _⟩
  omega

-- Fold a nonempty list of (wire, pol) into a single AND-output by appending (L.length - 1) AND gates.
def foldAndAcc (base : List U2Gate) (acc : Nat × Bool) : List (Nat × Bool) → List U2Gate × (Nat × Bool)
  | [] => (base, acc)
  | x :: rest =>
    let nextW := 6 + base.length
    let base' := base ++ [⟨false, acc.1, acc.2, x.1, x.2⟩]
    foldAndAcc base' (nextW, false) rest

def foldAndList (base : List U2Gate) : List (Nat × Bool) → List U2Gate × (Nat × Bool)
  | [] => (base, (0, false))
  | x :: rest => foldAndAcc base x rest

lemma foldAndAcc_spec (rest : List (Nat × Bool)) :
    ∀ (base : List U2Gate) (acc : Nat × Bool),
      ValidU2 base → acc.1 < 6 + base.length →
      (∀ x ∈ rest, x.1 < 6 + base.length) →
      let res := foldAndAcc base acc rest
      ValidU2 res.1 ∧
      res.1.length = base.length + rest.length ∧
      (∃ ext : List U2Gate, res.1 = base ++ ext) ∧
      res.2.1 < 6 + res.1.length ∧
      (∀ s : Fin 6 → Bool,
        Bool.xor (wireU2 res.1 res.2.1 s) res.2.2 =
          (Bool.xor (wireU2 base acc.1 s) acc.2 &&
           rest.all (fun x => Bool.xor (wireU2 base x.1 s) x.2))) := by
  induction rest with
  | nil =>
    intro base acc hv hacc _
    refine ⟨hv, by simp [foldAndAcc], ⟨[], by simp [foldAndAcc]⟩, hacc, fun s => by simp [foldAndAcc]⟩
  | cons x tl ih =>
    intro base acc hv hacc hbound
    let gNew : U2Gate := ⟨false, acc.1, acc.2, x.1, x.2⟩
    let base' := base ++ [gNew]
    have hlen' : base'.length = base.length + 1 := by simp [base']
    have hx1 : x.1 < 6 + base.length := hbound x List.mem_cons_self
    have hv' : ValidU2 base' := by
      intro j
      by_cases hj : j.val < base.length
      · have hget : base'.get j = base.get ⟨j.val, hj⟩ := by
          simp [base', List.get_eq_getElem, List.getElem_append_left hj]
        rw [hget]
        exact hv ⟨j.val, hj⟩
      · have hjeq : j.val = base.length := by have := j.isLt; omega
        have hget : base'.get j = gNew := by
          simp [base', List.get_eq_getElem, List.getElem_append_right (by omega : base.length ≤ j.val), hjeq]
        rw [hget, hjeq]
        exact ⟨hacc, hx1⟩
    have hpre_eq : ∀ w < 6 + base.length, ∀ s, wireU2 base' w s = wireU2 base w s := by
      intro w hw s
      unfold wireU2 evalU2
      rw [List.foldl_append]
      exact foldl_u2Step_getD_lt [gNew] (base.foldl u2Step (List.ofFn s)) w (by
        rw [foldl_u2Step_len, List.length_ofFn]; exact hw)
    have hnew_val : ∀ s, wireU2 base' (6 + base.length) s =
        (Bool.xor (wireU2 base acc.1 s) acc.2 && Bool.xor (wireU2 base x.1 s) x.2) := by
      intro s
      let jLast : Fin base'.length := ⟨base.length, by omega⟩
      have hget : base'.get jLast = gNew := by
        simp [base', jLast, List.get_eq_getElem]
      have hwg := wireU2_gate base' hv' jLast s
      dsimp only at hwg
      rw [hget] at hwg
      dsimp [gNew, jLast] at hwg
      rw [hwg, hpre_eq acc.1 hacc s, hpre_eq x.1 hx1 s]
    have hbound' : ∀ y ∈ tl, y.1 < 6 + base'.length := by
      intro y hy
      have := hbound y (List.mem_cons_of_mem _ hy); omega
    obtain ⟨hv_res, hlen_res, ⟨ext, hext⟩, hlt_res, heval_res⟩ :=
      ih base' (6 + base.length, false) hv' (by omega) hbound'
    refine ⟨hv_res, ?_, ⟨gNew :: ext, ?_⟩, hlt_res, ?_⟩
    · change (foldAndAcc base' (6 + base.length, false) tl).1.length = _
      rw [hlen_res, hlen', List.length_cons]; omega
    · change (foldAndAcc base' (6 + base.length, false) tl).1 = _
      rw [hext]; simp [base', List.append_assoc]
    · intro s
      change Bool.xor (wireU2 (foldAndAcc base' (6 + base.length, false) tl).1
        (foldAndAcc base' (6 + base.length, false) tl).2.1 s)
        (foldAndAcc base' (6 + base.length, false) tl).2.2 = _
      rw [heval_res s]
      simp only [List.all_cons, Bool.xor_false, hnew_val s, Bool.and_assoc]
      have hall : tl.all (fun y => Bool.xor (wireU2 base' y.1 s) y.2) =
          tl.all (fun y => Bool.xor (wireU2 base y.1 s) y.2) := by
        have hgo : ∀ l : List (Nat × Bool), (∀ y ∈ l, y.1 < 6 + base.length) →
            l.all (fun y => Bool.xor (wireU2 base' y.1 s) y.2) =
            l.all (fun y => Bool.xor (wireU2 base y.1 s) y.2) := by
          intro l hl
          induction l with
          | nil => rfl
          | cons z zs ihz =>
            simp only [List.all_cons, hpre_eq z.1 (hl z List.mem_cons_self) s,
              ihz (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
        exact hgo tl (fun y hy => hbound y (List.mem_cons_of_mem _ hy))
      rw [hall]

lemma foldAndList_spec (base : List U2Gate) (L : List (Nat × Bool)) (hL : L ≠ [])
    (hv : ValidU2 base) (hbound : ∀ x ∈ L, x.1 < 6 + base.length) :
    let res := foldAndList base L
    ValidU2 res.1 ∧
    res.1.length = base.length + (L.length - 1) ∧
    (∃ ext : List U2Gate, res.1 = base ++ ext) ∧
    res.2.1 < 6 + res.1.length ∧
    (∀ s : Fin 6 → Bool,
      Bool.xor (wireU2 res.1 res.2.1 s) res.2.2 =
        L.all (fun x => Bool.xor (wireU2 base x.1 s) x.2)) := by
  cases L with
  | nil => exact False.elim (hL rfl)
  | cons x rest =>
    have h := foldAndAcc_spec rest base x hv (hbound x List.mem_cons_self)
      (fun y hy => hbound y (List.mem_cons_of_mem _ hy))
    simpa [foldAndList] using h

def inactAux {m : Nat} (inSet : Fin m → Prop) [DecidablePred inSet] (outW : Fin m)
    (parent : Fin m → Fin m) (isNot : Fin m → Bool) : Nat → Fin m → Bool
  | 0, _ => false
  | d + 1, w =>
    if inSet w ∧ w ≠ outW then
      Bool.xor (isNot (parent w)) (inactAux inSet outW parent isNot d (parent w))
    else false

lemma inactAux_irrel {m : Nat} (inSet : Fin m → Prop) [DecidablePred inSet] (outW : Fin m)
    (parent : Fin m → Fin m) (isNot : Fin m → Bool)
    (hinc : ∀ w, inSet w → w ≠ outW → w.val < (parent w).val) :
    ∀ d1 d2 w, m - w.val ≤ d1 → m - w.val ≤ d2 →
      inactAux inSet outW parent isNot d1 w = inactAux inSet outW parent isNot d2 w := by
  intro d1
  induction d1 with
  | zero => intro d2 w h1 _; have := w.isLt; omega
  | succ d1 ih =>
    intro d2 w h1 h2
    cases d2 with
    | zero => have := w.isLt; omega
    | succ d2 =>
      unfold inactAux
      split_ifs with h
      · have hlt := hinc w h.1 h.2
        congr 1
        exact ih d2 (parent w) (by have := (parent w).isLt; omega) (by have := (parent w).isLt; omega)
      · rfl

def baseOfAux (gs : List Gate) (sigmaIdx : V10 → Nat) (posFn : Fin gs.length → Nat) :
    Nat → Fin (10 + gs.length) → Nat × Bool
  | 0, w => if h : w.val < 10 then (sigmaIdx ⟨w.val, h⟩, false) else (0, false)
  | n + 1, w =>
    if hlt10 : w.val < 10 then
      (sigmaIdx ⟨w.val, hlt10⟩, false)
    else
      let p : Fin gs.length := ⟨w.val - 10, by have := w.isLt; omega⟩
      if isNotGate (gs.get p).op then
        let j := (gs.get p).inputs.headD 0
        if hj : j < w.val then
          let r := baseOfAux gs sigmaIdx posFn n ⟨j, by have := w.isLt; omega⟩
          (r.1, !r.2)
        else (0, false)
      else
        (6 + posFn p, false)

lemma baseOfAux_irrel (gs : List Gate) (sigmaIdx : V10 → Nat) (posFn : Fin gs.length → Nat) :
    ∀ n1 n2 w, w.val ≤ n1 → w.val ≤ n2 →
      baseOfAux gs sigmaIdx posFn n1 w = baseOfAux gs sigmaIdx posFn n2 w := by
  intro n1
  induction n1 with
  | zero =>
    intro n2 w h1 h2
    have hlt : w.val < 10 := by omega
    cases n2 with
    | zero => rfl
    | succ n2 => unfold baseOfAux; simp [hlt]
  | succ n1 ih =>
    intro n2 w h1 h2
    cases n2 with
    | zero =>
      have hlt : w.val < 10 := by omega
      unfold baseOfAux; simp [hlt]
    | succ n2 =>
      unfold baseOfAux
      by_cases hlt10 : w.val < 10
      · simp only [hlt10, ↓reduceDIte]
      · simp only [hlt10, ↓reduceDIte]
        by_cases hnot : isNotGate (gs.get ⟨w.val - 10, by have := w.isLt; omega⟩).op = true
        · simp only [hnot, ↓reduceIte]
          let j := (gs.get ⟨w.val - 10, by have := w.isLt; omega⟩).inputs.headD 0
          by_cases hj : j < w.val
          · change (if h : j < w.val then _ else _) = (if h : j < w.val then _ else _)
            simp only [hj, ↓reduceDIte]
            have hrec := ih n2 ⟨j, by have := w.isLt; omega⟩ (by dsimp; omega) (by dsimp; omega)
            rw [hrec]
          · change (if h : j < w.val then _ else _) = (if h : j < w.val then _ else _)
            simp only [hj, ↓reduceDIte]
        · rw [if_neg hnot, if_neg hnot]

lemma mkIota_aux (I : Finset V10) (a0 a1 a2 a3 : V10) (h01 : a0 ≠ a1) (h23 : a2 ≠ a3)
    (hd : Disjoint ({a0, a1} : Finset V10) {a2, a3})
    (hEq : ({a0, a1} : Finset V10) ∪ {a2, a3} = I) :
    ∃ ι : Fin 4 → V10, Function.Injective ι ∧ Finset.univ.image ι = I ∧
      ι 0 = a0 ∧ ι 1 = a1 ∧ ι 2 = a2 ∧ ι 3 = a3 := by
  let ι : Fin 4 → V10 := ![a0, a1, a2, a3]
  have h02 : a0 ≠ a2 := fun h => Finset.disjoint_left.mp hd (Finset.mem_insert_self a0 {a1}) (by rw [h]; exact Finset.mem_insert_self a2 {a3})
  have h03 : a0 ≠ a3 := fun h => Finset.disjoint_left.mp hd (Finset.mem_insert_self a0 {a1}) (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self a3))
  have h12 : a1 ≠ a2 := fun h => Finset.disjoint_left.mp hd (Finset.mem_insert_of_mem (Finset.mem_singleton_self a1)) (by rw [h]; exact Finset.mem_insert_self a2 {a3})
  have h13 : a1 ≠ a3 := fun h => Finset.disjoint_left.mp hd (Finset.mem_insert_of_mem (Finset.mem_singleton_self a1)) (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self a3))
  refine ⟨ι, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all [ι]
  · rw [← hEq]; ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨k, rfl⟩; fin_cases k <;> simp [ι]
    · rintro ((rfl | rfl) | (rfl | rfl))
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩

lemma wireU2_append_lt (gs ext : List U2Gate) (w : Nat) (hw : w < 6 + gs.length) (s : Fin 6 → Bool) :
    wireU2 (gs ++ ext) w s = wireU2 gs w s := by
  unfold wireU2 evalU2
  rw [List.foldl_append]
  exact foldl_u2Step_getD_lt ext (gs.foldl u2Step (List.ofFn s)) w (by
    rw [foldl_u2Step_len, List.length_ofFn]; exact hw)

lemma validU2_of_append_left (gs ext : List U2Gate) (hv : ValidU2 (gs ++ ext)) : ValidU2 gs := by
  intro j
  have h := hv ⟨j.val, by simp; omega⟩
  simpa [List.get_eq_getElem, List.getElem_append_left j.isLt] using h

-- Main theorem: no 15-binary-gate clean least circuit computes P_10!
theorem p10_not_fifteen_bin {gs : List Gate} {out : Nat} (least : Least 10 p10F gs out)
    (h15 : nonNotCount gs = 15) : False := by
  classical
  have outValid := least_p10_output_valid least
  let outWire : Fin (10 + gs.length) := ⟨out, outValid⟩
  have live := least_read_edge_live least p10_nonconstant p10_depends p10_restrict_nonconstant outValid
  have hnd := PEqualNP.Outside.ProveLowBin.least_gate_inputs_nodup least p10_nonconstant
  have hstruc := p10_six_branches_and_structure least
  obtain ⟨I, hI4, hI_indep, hI_out⟩ := hstruc.2.2 h15
  let W := Fin (10 + gs.length)
  -- T_wires: wires reachable from I
  let inT (w : W) : Prop := ∃ v ∈ I, ReflTransGen (readEdge gs) (inputWire gs v) w
  let T_wires : Finset W := Finset.univ.filter inT
  have hmemT (w : W) : w ∈ T_wires ↔ inT w := by simp [T_wires]
  have hinI_T (v : V10) (hv : v ∈ I) : inputWire gs v ∈ T_wires :=
    (hmemT _).mpr ⟨v, hv, ReflTransGen.refl⟩
  have hT_le_out (w : W) : w ≤ outWire := wire_le_output least.hcl outWire live w
  have hT_first (w : W) (hw : w ∈ T_wires) :
      FirstBranchRoute.first (readEdge gs) outWire (read_order least.hcl) live w = outWire := by
    obtain ⟨v, hv, hpath⟩ := (hmemT w).mp hw
    have hlab : FirstBranchRoute.first (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v) = outWire :=
      hI_out v hv
    have hrb := FirstBranchRoute.read_before (readEdge gs) outWire (read_order least.hcl) live hpath
      (by rw [hlab]; exact hT_le_out w)
    exact hrb.2.trans hlab
  have hT_closed (u v : W) (hu : u ∈ T_wires) (he : readEdge gs u v) : v ∈ T_wires := by
    obtain ⟨a, ha, hpath⟩ := (hmemT u).mp hu
    exact (hmemT v).mpr ⟨a, ha, hpath.tail he⟩
  have hout_inT : outWire ∈ T_wires := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
    have hfp := FirstBranchRoute.first_path (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v)
    have hlab : FirstBranchRoute.first (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v) = outWire :=
      hI_out v hv
    rw [hlab] at hfp
    exact (hmemT outWire).mpr ⟨v, hv, FirstBranchRoute.follows_is_read_path _ _ hfp⟩
  have hT_unique_out (u : W) (hu : u ∈ T_wires) (hne : u ≠ outWire) :
      ∃! v : W, readEdge gs u v := by
    obtain ⟨v, hv⟩ := live u hne
    refine ⟨v, hv, fun v' hv' => ?_⟩
    by_contra hdiff
    have hterm : FirstBranchRoute.Terminal (readEdge gs) outWire u :=
      Or.inr ⟨v', v, hv', hv, hdiff⟩
    have hfirst := FirstBranchRoute.first_of_terminal (readEdge gs) outWire (read_order least.hcl) live hterm
    exact hne (hfirst.symm.trans (hT_first u hu))
  have hout_no_out (v : W) : ¬ readEdge gs outWire v := by
    intro he
    have hlt : outWire < v := read_order least.hcl he
    have hle : v ≤ outWire := hT_le_out v
    exact not_lt_of_ge hle hlt
  -- Reachable leaf set in I for each wire w
  let reachI (w : W) : Finset V10 := I.filter fun v => ReflTransGen (readEdge gs) (inputWire gs v) w
  have hreachI_nonempty (w : W) (hw : w ∈ T_wires) : (reachI w).Nonempty := by
    obtain ⟨v, hv, hp⟩ := (hmemT w).mp hw
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hp⟩⟩
  have hreachI_input (v : V10) (hv : v ∈ I) : reachI (inputWire gs v) = {v} := by
    ext a
    simp only [reachI, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hp⟩
      rcases hp.cases_tail with h | ⟨u, _, he⟩
      · exact Fin.ext (by simpa [inputWire] using (congrArg Fin.val h).symm)
      · exact False.elim (no_read_into_input u (inputWire gs v) v.isLt he)
    · rintro rfl
      exact ⟨hv, ReflTransGen.refl⟩
  have hread_before_I (v : V10) (hv : v ∈ I) (w : W) (hp : ReflTransGen (readEdge gs) (inputWire gs v) w) :
      ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) (inputWire gs v) w := by
    have hlab : FirstBranchRoute.first (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v) = outWire :=
      hI_out v hv
    exact (FirstBranchRoute.read_before (readEdge gs) outWire (read_order least.hcl) live hp
      (by rw [hlab]; exact hT_le_out w)).1
  have hfollow_subpath (start a b : W)
      (pa : ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) start a)
      (pb : ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) start b)
      (hab : a ≤ b) :
      ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) a b := by
    induction pa generalizing b with
    | refl => exact pb
    | tail pa' step ih =>
      rename_i x y
      rcases pb.cases_tail with rfl | ⟨z, pz, stepz⟩
      · have hlt := read_order least.hcl step.1
        have hle := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl)
          (FirstBranchRoute.follows_is_read_path _ _ pa')
        exact False.elim (not_lt_of_ge hab (lt_of_le_of_lt hle hlt))
      · by_cases hxy : y = b
        · subst hxy; exact ReflTransGen.refl
        · have hlt_yb : y < b := lt_of_le_of_ne hab hxy
          have hstep_from_x := ih b (pz.tail stepz) (le_of_lt (lt_trans (read_order least.hcl step.1) hlt_yb))
          rcases hstep_from_x.cases_head with rfl | ⟨y', step', tail'⟩
          · exact False.elim (not_lt_of_ge (le_of_lt hlt_yb) (read_order least.hcl step.1))
          · have heqy := FirstBranchRoute.follow_unique (readEdge gs) outWire step step'
            subst heqy; exact tail'
  -- Tree property: if u1 != u2 both have readEdge to the same gate, reachI u1 and reachI u2 are disjoint!
  have hT_tree_disj (u1 u2 : W) (hne : u1 ≠ u2)
      (h1 : u1 ∈ T_wires) (h2 : u2 ∈ T_wires)
      (w : W) (he1 : readEdge gs u1 w) (he2 : readEdge gs u2 w) :
      Disjoint (reachI u1) (reachI u2) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    have hp1 := (Finset.mem_filter.mp hv1).2
    have hp2 := (Finset.mem_filter.mp hv2).2
    have hvI := (Finset.mem_filter.mp hv1).1
    have hf1 := hread_before_I v hvI u1 hp1
    have hf2 := hread_before_I v hvI u2 hp2
    have hcontra (a b : W) (ha : a ∈ T_wires) (hea : readEdge gs a w) (heb : readEdge gs b w)
        (hfa : ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) (inputWire gs v) a)
        (hfb : ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) (inputWire gs v) b)
        (hlt : a < b) : False := by
      have hab := hfollow_subpath (inputWire gs v) a b hfa hfb (le_of_lt hlt)
      rcases hab.cases_head with rfl | ⟨y, step, tail⟩
      · exact lt_irrefl _ hlt
      · have ha_ne_out : a ≠ outWire := ne_of_lt (lt_of_lt_of_le (read_order least.hcl hea) (hT_le_out w))
        obtain ⟨_, _, huniq⟩ := hT_unique_out a ha ha_ne_out
        have hyw : y = w := (huniq y step.1).trans (huniq w hea).symm
        subst hyw
        have hwb := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl)
          (FirstBranchRoute.follows_is_read_path _ _ tail)
        have hbw := read_order least.hcl heb
        exact not_lt_of_ge hwb hbw
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hcontra u1 u2 h1 he1 he2 hf1 hf2 hlt
    · exact hcontra u2 u1 h2 he2 he1 hf2 hf1 hgt

  -- Helper: gateWire p
  let gateWire (p : Fin gs.length) : W := ⟨10 + p.val, by omega⟩
  have hgateWire_inj : Function.Injective gateWire := by
    intro p q h; exact Fin.ext (by have := congrArg Fin.val h; dsimp [gateWire] at this; omega)
  have hgate_pred_mem (p : Fin gs.length) (a : Nat) (ha : a ∈ (gs.get p).inputs) :
      ∃ u : W, u.val = a ∧ readEdge gs u (gateWire p) := by
    have hcl_p := least.hcl p.val (gs.get p) (by rw [List.getElem?_eq_getElem p.isLt, List.get_eq_getElem])
    have hlt := hcl_p.lt a ha
    refine ⟨⟨a, by omega⟩, rfl, ?_⟩
    exact (gate_read_inputs least.hcl p ⟨a, by omega⟩).mpr ha

  -- Partition binary gates into GS, Gating, Merges
  let BinIdx : Finset (Fin gs.length) := Finset.univ.filter fun p => !(isNotGate (gs.get p).op)
  have hBinCard : BinIdx.card = 15 := by rw [← nonNotCount_eq_card_filter, h15]
  let inDegT (w : W) : Nat := (T_wires.filter fun u => readEdge gs u w).card
  let GS : Finset (Fin gs.length) := BinIdx.filter fun p => gateWire p ∉ T_wires
  let Gating : Finset (Fin gs.length) := BinIdx.filter fun p => gateWire p ∈ T_wires ∧ inDegT (gateWire p) = 1
  let Merges : Finset (Fin gs.length) := BinIdx.filter fun p => gateWire p ∈ T_wires ∧ inDegT (gateWire p) = 2
  let NotT : Finset (Fin gs.length) := Finset.univ.filter fun p => isNotGate (gs.get p).op ∧ gateWire p ∈ T_wires

  -- Every gate in T_wires has at least 1 predecessor in T_wires
  have hT_gate_inDeg_pos (p : Fin gs.length) (hp : gateWire p ∈ T_wires) : 1 ≤ inDegT (gateWire p) := by
    obtain ⟨v, hv, hpath⟩ := (hmemT _).mp hp
    rcases hpath.cases_tail with heq | ⟨u, hpu, he⟩
    · have := congrArg Fin.val heq; dsimp [inputWire, gateWire] at this; omega
    · exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨(hmemT u).mpr ⟨v, hv, hpu⟩, he⟩⟩

  have hNot_inDeg1 (p : Fin gs.length) (hp : p ∈ NotT) : inDegT (gateWire p) = 1 := by
    obtain ⟨hnot, hT⟩ := (Finset.mem_filter.mp hp).2
    have hpos := hT_gate_inDeg_pos p hT
    have hcl_p := least.hcl p.val (gs.get p) (by rw [List.getElem?_eq_getElem p.isLt, List.get_eq_getElem])
    rcases hcl_p with ⟨_, j, hj, hinp⟩ | ⟨hop | hop, _⟩
    · have hle : inDegT (gateWire p) ≤ 1 := by
        have hsub : (T_wires.filter fun u => readEdge gs u (gateWire p)) ⊆ {⟨j, by omega⟩} := by
          intro u hu
          have hmem := (gate_read_inputs least.hcl p u).mp (Finset.mem_filter.mp hu).2
          rw [hinp, List.mem_singleton] at hmem
          exact Finset.mem_singleton.mpr (Fin.ext hmem)
        exact (Finset.card_le_card hsub).trans (by simp)
      omega
    · rw [hop] at hnot; exact Bool.noConfusion hnot
    · rw [hop] at hnot; exact Bool.noConfusion hnot

  have hBin_inDeg_le2 (p : Fin gs.length) (hp : p ∈ BinIdx) : inDegT (gateWire p) ≤ 2 := by
    have hbn := (Finset.mem_filter.mp hp).2
    have hcl_p := least.hcl p.val (gs.get p) (by rw [List.getElem?_eq_getElem p.isLt, List.get_eq_getElem])
    rcases hcl_p with ⟨hop, _⟩ | ⟨_, j, k, hj, hk, hinp⟩
    · rw [hop] at hbn; exact Bool.noConfusion hbn
    · have hsub : (T_wires.filter fun u => readEdge gs u (gateWire p)) ⊆ {⟨j, by omega⟩, ⟨k, by omega⟩} := by
        intro u hu
        have hmem := (gate_read_inputs least.hcl p u).mp (Finset.mem_filter.mp hu).2
        rw [hinp] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
        exact hmem
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

  have hBin_part : GS.card + Gating.card + Merges.card = 15 := by
    have hdisj1 : Disjoint GS Gating := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2.1
    have hdisj2 : Disjoint (GS ∪ Gating) Merges := by
      rw [Finset.disjoint_left]; intro p h1 h2
      rcases Finset.mem_union.mp h1 with h1 | h1
      · exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2.1
      · have e1 := (Finset.mem_filter.mp h1).2.2
        have e2 := (Finset.mem_filter.mp h2).2.2
        omega
    have hunion : GS ∪ Gating ∪ Merges = BinIdx := by
      ext p
      simp only [Finset.mem_union, GS, Gating, Merges, Finset.mem_filter]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro hp
        by_cases hT : gateWire p ∈ T_wires
        · have h1 := hT_gate_inDeg_pos p hT
          have h2 := hBin_inDeg_le2 p hp
          have : inDegT (gateWire p) = 1 ∨ inDegT (gateWire p) = 2 := by omega
          rcases this with hd | hd
          · exact Or.inl (Or.inr ⟨hp, hT, hd⟩)
          · exact Or.inr ⟨hp, hT, hd⟩
        · exact Or.inl (Or.inl ⟨hp, hT⟩)
    rw [← hBinCard, ← hunion, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]

  -- Edge counting inside T_wires gives Merges.card = 3 and GS.card + Gating.card = 12!
  have hMerges_eq3 : Merges.card = 3 := by
    -- Partition T_wires into T_in, NotT.image, Gating.image, Merges.image
    let T_in := I.image (inputWire gs)
    let T_not := NotT.image gateWire
    let T_gat := Gating.image gateWire
    let T_mrg := Merges.image gateWire
    have hTin_card : T_in.card = 4 := by
      dsimp [T_in]
      rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa [inputWire] using congrArg Fin.val h)), hI4]
    have hT_part : T_wires = T_in ∪ T_not ∪ T_gat ∪ T_mrg := by
      ext w
      simp only [Finset.mem_union, T_in, T_not, T_gat, T_mrg, Finset.mem_image,
        NotT, Gating, Merges, BinIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hw
        by_cases hlt : w.val < 10
        · obtain ⟨v, hvI, hp⟩ := (hmemT w).mp hw
          rcases hp.cases_tail with rfl | ⟨u, _, he⟩
          · exact Or.inl (Or.inl (Or.inl ⟨v, hvI, rfl⟩))
          · exact False.elim (no_read_into_input u w hlt he)
        · let p : Fin gs.length := ⟨w.val - 10, by have := w.isLt; omega⟩
          have hgw : gateWire p = w := Fin.ext (by dsimp [gateWire, p]; omega)
          rw [← hgw] at hw
          cases hnot : isNotGate (gs.get p).op
          · have hnotT : (!(isNotGate (gs.get p).op)) = true := by rw [hnot]; rfl
            have hpBin : p ∈ BinIdx := Finset.mem_filter.mpr ⟨Finset.mem_univ p, hnotT⟩
            have h1 := hT_gate_inDeg_pos p hw
            have h2 := hBin_inDeg_le2 p hpBin
            rcases (by omega : inDegT (gateWire p) = 1 ∨ inDegT (gateWire p) = 2) with hd | hd
            · exact Or.inl (Or.inr ⟨p, ⟨hnotT, hw, hd⟩, hgw⟩)
            · exact Or.inr ⟨p, ⟨hnotT, hw, hd⟩, hgw⟩
          · exact Or.inl (Or.inl (Or.inr ⟨p, ⟨hnot, hw⟩, hgw⟩))
      · rintro (((⟨v, hv, rfl⟩ | ⟨p, ⟨_, hw⟩, rfl⟩) | ⟨p, ⟨_, hw, _⟩, rfl⟩) | ⟨p, ⟨_, hw, _⟩, rfl⟩)
        · exact hinI_T v hv
        · exact hw
        · exact hw
        · exact hw
    have hd_in_not : Disjoint T_in T_not := by
      rw [Finset.disjoint_left]; intro w h1 h2
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨p, _, hgw⟩ := Finset.mem_image.mp h2
      have := congrArg Fin.val hgw; dsimp [inputWire, gateWire] at this; omega
    have hd_innot_gat : Disjoint (T_in ∪ T_not) T_gat := by
      rw [Finset.disjoint_left]; intro w h1 h2
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h2
      rcases Finset.mem_union.mp h1 with h1 | h1
      · obtain ⟨v, _, hgw⟩ := Finset.mem_image.mp h1
        have := congrArg Fin.val hgw; dsimp [inputWire, gateWire] at this; omega
      · obtain ⟨q, hq, hgw⟩ := Finset.mem_image.mp h1
        have := hgateWire_inj hgw; subst this
        have hnot := (Finset.mem_filter.mp hq).2.1
        have hbn := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        rw [hnot] at hbn; exact Bool.noConfusion hbn
    have hd_all_mrg : Disjoint (T_in ∪ T_not ∪ T_gat) T_mrg := by
      rw [Finset.disjoint_left]; intro w h1 h2
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h2
      rcases Finset.mem_union.mp h1 with h1 | h1
      · rcases Finset.mem_union.mp h1 with h1 | h1
        · obtain ⟨v, _, hgw⟩ := Finset.mem_image.mp h1
          have := congrArg Fin.val hgw; dsimp [inputWire, gateWire] at this; omega
        · obtain ⟨q, hq, hgw⟩ := Finset.mem_image.mp h1
          have := hgateWire_inj hgw; subst this
          have hnot := (Finset.mem_filter.mp hq).2.1
          have hbn := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          rw [hnot] at hbn; exact Bool.noConfusion hbn
      · obtain ⟨q, hq, hgw⟩ := Finset.mem_image.mp h1
        have := hgateWire_inj hgw; subst this
        have e1 := (Finset.mem_filter.mp hq).2.2
        have e2 := (Finset.mem_filter.mp hp).2.2
        omega
    have hT_card : T_wires.card = 4 + NotT.card + Gating.card + Merges.card := by
      rw [hT_part, Finset.card_union_of_disjoint hd_all_mrg,
        Finset.card_union_of_disjoint hd_innot_gat,
        Finset.card_union_of_disjoint hd_in_not,
        hTin_card,
        Finset.card_image_of_injective _ hgateWire_inj,
        Finset.card_image_of_injective _ hgateWire_inj,
        Finset.card_image_of_injective _ hgateWire_inj]
    -- Define parent function on T_wires \ {outWire}
    let parentOf (u : W) : W :=
      if h : u ∈ T_wires ∧ u ≠ outWire then (hT_unique_out u h.1 h.2).choose else outWire
    have hparent_edge (u : W) (hu : u ∈ T_wires.erase outWire) :
        readEdge gs u (parentOf u) ∧ parentOf u ∈ T_wires := by
      have huT : u ∈ T_wires := Finset.mem_of_mem_erase hu
      have hne : u ≠ outWire := Finset.ne_of_mem_erase hu
      have he : readEdge gs u (parentOf u) := by
        dsimp only [parentOf]
        rw [dite_eq_left ⟨huT, hne⟩]
        exact (hT_unique_out u huT hne).choose_spec.1
      exact ⟨he, hT_closed u (parentOf u) huT he⟩
    have hfiber_eq (v : W) (hv : v ∈ T_wires) :
        (T_wires.erase outWire).filter (fun u => parentOf u = v) =
          T_wires.filter (fun u => readEdge gs u v) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, huT⟩, rfl⟩
        exact ⟨huT, (hparent_edge u (Finset.mem_erase.mpr ⟨hne, huT⟩)).1⟩
      · rintro ⟨huT, he⟩
        have hne : u ≠ outWire := fun h => hout_no_out v (h ▸ he)
        refine ⟨⟨hne, huT⟩, ?_⟩
        have hpe := (hparent_edge u (Finset.mem_erase.mpr ⟨hne, huT⟩)).1
        obtain ⟨_, _, huniq⟩ := hT_unique_out u huT hne
        exact (huniq _ hpe).trans (huniq v he).symm
    have hsum_edges : ∑ v ∈ T_wires, inDegT v = (T_wires.erase outWire).card := by
      have hfib := Finset.sum_card_fiberwise_eq_card_filter (s := T_wires.erase outWire) (t := T_wires)
        (g := parentOf)
      have hall : (T_wires.erase outWire).filter (fun u => parentOf u ∈ T_wires) = T_wires.erase outWire := by
        ext u; simp only [Finset.mem_filter, and_iff_left_iff_imp]
        intro hu; exact (hparent_edge u hu).2
      rw [hall] at hfib
      rw [← hfib]
      apply Finset.sum_congr rfl
      intro v hv
      dsimp [inDegT]
      rw [← hfiber_eq v hv]
    have hsum_part : ∑ v ∈ T_wires, inDegT v = NotT.card + Gating.card + 2 * Merges.card := by
      rw [hT_part, Finset.sum_union hd_all_mrg, Finset.sum_union hd_innot_gat, Finset.sum_union hd_in_not]
      have s_in : ∑ v ∈ T_in, inDegT v = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
        have hemp : (T_wires.filter fun u => readEdge gs u (inputWire gs a)) = ∅ := by
          ext u; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro _; exact no_read_into_input u (inputWire gs a) a.isLt
        simp [inDegT, hemp]
      have s_not : ∑ v ∈ T_not, inDegT v = NotT.card := by
        rw [Finset.sum_image (fun a _ b _ h => hgateWire_inj h)]
        rw [Finset.sum_congr rfl (fun p hp => hNot_inDeg1 p hp)]
        simp
      have s_gat : ∑ v ∈ T_gat, inDegT v = Gating.card := by
        rw [Finset.sum_image (fun a _ b _ h => hgateWire_inj h)]
        rw [Finset.sum_congr rfl (fun p hp => (Finset.mem_filter.mp hp).2.2)]
        simp
      have s_mrg : ∑ v ∈ T_mrg, inDegT v = 2 * Merges.card := by
        rw [Finset.sum_image (fun a _ b _ h => hgateWire_inj h)]
        rw [Finset.sum_congr rfl (fun p hp => (Finset.mem_filter.mp hp).2.2)]
        simp [mul_comm]
      rw [s_in, s_not, s_gat, s_mrg, zero_add]
    have herase : (T_wires.erase outWire).card + 1 = T_wires.card :=
      Finset.card_erase_add_one hout_inT
    omega

  have hGS_Gating : GS.card + Gating.card = 12 := by omega

  -- Now define path NOT-parity inact(w) on T_wires by well-founded downward recursion from outWire!
  -- Even simpler: define inact(w) for all w : W by reverse recursion on (10 + gs.length - w.val)!
  let parentOf (u : W) : W :=
    if h : u ∈ T_wires ∧ u ≠ outWire then (hT_unique_out u h.1 h.2).choose else outWire
  have hparent_spec (u : W) (hu : u ∈ T_wires) (hne : u ≠ outWire) :
      readEdge gs u (parentOf u) ∧ parentOf u ∈ T_wires ∧ u.val < (parentOf u).val := by
    have he : readEdge gs u (parentOf u) := by
      dsimp only [parentOf]
      rw [dite_eq_left ⟨hu, hne⟩]
      exact (hT_unique_out u hu hne).choose_spec.1
    exact ⟨he, hT_closed u _ hu he, read_order least.hcl he⟩
  have hparent_eq (u v : W) (hu : u ∈ T_wires) (he : readEdge gs u v) : parentOf u = v := by
    have hne : u ≠ outWire := fun h => hout_no_out v (h ▸ he)
    have hpe := (hparent_spec u hu hne).1
    obtain ⟨_, _, huniq⟩ := hT_unique_out u hu hne
    exact (huniq _ hpe).trans (huniq v he).symm

  let isNotWire (w : W) : Bool :=
    if h : 10 ≤ w.val then isNotGate (gs.get ⟨w.val - 10, by have := w.isLt; omega⟩).op else false

  have hinact_inc (w : W) (hw : w ∈ T_wires) (hne : w ≠ outWire) : w.val < (parentOf w).val :=
    (hparent_spec w hw hne).2.2

  let inact (w : W) : Bool := inactAux (fun u => u ∈ T_wires) outWire parentOf isNotWire (10 + gs.length) w

  have hinact_out : inact outWire = false := by
    have h := inactAux_irrel (fun u => u ∈ T_wires) outWire parentOf isNotWire hinact_inc
      (10 + gs.length) (10 + gs.length + 1) outWire (by omega) (by omega)
    dsimp only [inact]
    rw [h]
    unfold inactAux
    simp

  have hinact_step (u : W) (hu : u ∈ T_wires) (hne : u ≠ outWire) :
      inact u = Bool.xor (isNotWire (parentOf u)) (inact (parentOf u)) := by
    have h1 := inactAux_irrel (fun u => u ∈ T_wires) outWire parentOf isNotWire hinact_inc
      (10 + gs.length) (10 + gs.length + 1) u (by omega) (by omega)
    dsimp only [inact]
    rw [h1]
    conv_lhs => unfold inactAux
    split_ifs with h
    · rfl
    · exact False.elim (h ⟨hu, hne⟩)

  -- Classify each Gating gate p as Q_active vs Q_passive:
  -- For p ∈ Gating: let (a, b) be its two inputs with a ∈ T_wires, b ∉ T_wires.
  -- absOp(p) := false for AND, true for OR.
  -- p ∈ Q_active iff absOp p = inact (gateWire p).
  let absOp (p : Fin gs.length) : Bool := match (gs.get p).op with | GateOp.or => true | _ => false
  let Q_active : Finset (Fin gs.length) := Gating.filter fun p => absOp p = inact (gateWire p)
  let Q_passive : Finset (Fin gs.length) := Gating.filter fun p => absOp p ≠ inact (gateWire p)

  have hQ_part : Q_active.card + Q_passive.card = Gating.card := by
    have hdisj : Disjoint Q_active Q_passive := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : Q_active ∪ Q_passive = Gating := by
      ext p; simp only [Finset.mem_union, Q_active, Q_passive, Finset.mem_filter]
      tauto
    rw [← Finset.card_union_of_disjoint hdisj, hunion]

  -- For any binary gate p ∈ T_wires, extract its two distinct inputs as wires
  have hBin_two_inputs (p : Fin gs.length) (hp : p ∈ BinIdx) :
      ∃ u1 u2 : W, u1 ≠ u2 ∧ (gs.get p).inputs = [u1.val, u2.val] ∧
        ((gs.get p).op = GateOp.and ∨ (gs.get p).op = GateOp.or) ∧
        readEdge gs u1 (gateWire p) ∧ readEdge gs u2 (gateWire p) := by
    have hbn := (Finset.mem_filter.mp hp).2
    have hget : gs[p.val]? = some (gs.get p) := by rw [List.getElem?_eq_getElem p.isLt, List.get_eq_getElem]
    have hcl_p := least.hcl p.val (gs.get p) hget
    rcases hcl_p with ⟨hop, _⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · rw [hop] at hbn; exact Bool.noConfusion hbn
    · have hndp := hnd (gs.get p) (List.get_mem _ _)
      rw [hinp, List.nodup_cons, List.mem_singleton] at hndp
      let u1 : W := ⟨j, by omega⟩
      let u2 : W := ⟨k, by omega⟩
      have hne : u1 ≠ u2 := fun h => hndp.1 (congrArg Fin.val h)
      refine ⟨u1, u2, hne, hinp, hop,
        (gate_read_inputs least.hcl p u1).mpr (by rw [hinp]; simp [u1]),
        (gate_read_inputs least.hcl p u2).mpr (by rw [hinp]; simp [u2])⟩

  have hGating_split (p : Fin gs.length) (hp : p ∈ Gating) :
      ∃ a b : W, a ∈ T_wires ∧ b ∉ T_wires ∧
        readEdge gs a (gateWire p) ∧ readEdge gs b (gateWire p) ∧
        (∀ x : V10 → Bool,
          vl gs x (gateWire p).val =
            if absOp p then (vl gs x a.val || vl gs x b.val) else (vl gs x a.val && vl gs x b.val)) := by
    have hpBin : p ∈ BinIdx := (Finset.mem_filter.mp hp).1
    have hpT : gateWire p ∈ T_wires := (Finset.mem_filter.mp hp).2.1
    have hdeg1 : inDegT (gateWire p) = 1 := (Finset.mem_filter.mp hp).2.2
    obtain ⟨u1, u2, hne, hinp, hop, he1, he2⟩ := hBin_two_inputs p hpBin
    have hget : gs[p.val]? = some (gs.get p) := by rw [List.getElem?_eq_getElem p.isLt, List.get_eq_getElem]
    have hev (x : V10 → Bool) : vl gs x (gateWire p).val =
        if absOp p then (vl gs x u1.val || vl gs x u2.val) else (vl gs x u1.val && vl gs x u2.val) := by
      change vl gs x (10 + p.val) = _
      rw [vl_gate gs least.hcl x p.val (gs.get p) hget, hinp]
      rcases hop with hop | hop
      · simp only [absOp, hop, List.map_cons, List.map_nil]
        generalize vl gs x u1.val = b1; generalize vl gs x u2.val = b2
        cases b1 <;> cases b2 <;> rfl
      · simp only [absOp, hop, List.map_cons, List.map_nil]
        generalize vl gs x u1.val = b1; generalize vl gs x u2.val = b2
        cases b1 <;> cases b2 <;> rfl
    by_cases h1 : u1 ∈ T_wires
    · have h2 : u2 ∉ T_wires := by
        intro h2
        have hsub : ({u1, u2} : Finset W) ⊆ T_wires.filter (fun u => readEdge gs u (gateWire p)) := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨h1, he1⟩
          · exact Finset.mem_filter.mpr ⟨h2, he2⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_pair hne] at hle
        change 2 ≤ inDegT (gateWire p) at hle
        omega
      exact ⟨u1, u2, h1, h2, he1, he2, hev⟩
    · have h2 : u2 ∈ T_wires := by
        obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < inDegT (gateWire p))
        have hvT := (Finset.mem_filter.mp hv).1
        have hve := (gate_read_inputs least.hcl p v).mp (Finset.mem_filter.mp hv).2
        rw [hinp] at hve
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hve
        rcases hve with hve | hve
        · exact False.elim (h1 (Fin.ext hve ▸ hvT))
        · exact Fin.ext hve ▸ hvT
      refine ⟨u2, u1, h2, h1, he2, he1, fun x => ?_⟩
      rw [hev x]; cases absOp p <;> simp [Bool.or_comm, Bool.and_comm]

  have hMerge_split (p : Fin gs.length) (hp : p ∈ Merges) :
      ∃ a1 a2 : W, a1 ≠ a2 ∧ a1 ∈ T_wires ∧ a2 ∈ T_wires ∧
        readEdge gs a1 (gateWire p) ∧ readEdge gs a2 (gateWire p) ∧
        (∀ x : V10 → Bool,
          vl gs x (gateWire p).val =
            if absOp p then (vl gs x a1.val || vl gs x a2.val) else (vl gs x a1.val && vl gs x a2.val)) := by
    have hpBin : p ∈ BinIdx := (Finset.mem_filter.mp hp).1
    have hdeg2 : inDegT (gateWire p) = 2 := (Finset.mem_filter.mp hp).2.2
    obtain ⟨u1, u2, hne, hinp, hop, he1, he2⟩ := hBin_two_inputs p hpBin
    have hget : gs[p.val]? = some (gs.get p) := by rw [List.getElem?_eq_getElem p.isLt, List.get_eq_getElem]
    have hsub : T_wires.filter (fun u => readEdge gs u (gateWire p)) ⊆ {u1, u2} := by
      intro u hu
      have hmem := (gate_read_inputs least.hcl p u).mp (Finset.mem_filter.mp hu).2
      rw [hinp] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      exact hmem
    have hEq : T_wires.filter (fun u => readEdge gs u (gateWire p)) = {u1, u2} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne]; exact hdeg2.ge)
    have h1 : u1 ∈ T_wires := (Finset.mem_filter.mp (hEq ▸ Finset.mem_insert_self u1 {u2})).1
    have h2 : u2 ∈ T_wires := (Finset.mem_filter.mp (hEq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u2))).1
    refine ⟨u1, u2, hne, h1, h2, he1, he2, fun x => ?_⟩
    change vl gs x (10 + p.val) = _
    rw [vl_gate gs least.hcl x p.val (gs.get p) hget, hinp]
    rcases hop with hop | hop
    · simp only [absOp, hop, List.map_cons, List.map_nil]
      generalize vl gs x u1.val = b1; generalize vl gs x u2.val = b2
      cases b1 <;> cases b2 <;> rfl
    · simp only [absOp, hop, List.map_cons, List.map_nil]
      generalize vl gs x u1.val = b1; generalize vl gs x u2.val = b2
      cases b1 <;> cases b2 <;> rfl

  -- Any two distinct 2-element reachI sets of wires in T_wires are disjoint!
  have hT_reachI_tree (u v : W) (hu : u ∈ T_wires) (hv : v ∈ T_wires) :
      Disjoint (reachI u) (reachI v) ∨ reachI u ⊆ reachI v ∨ reachI v ⊆ reachI u := by
    by_cases hdisj : Disjoint (reachI u) (reachI v)
    · exact Or.inl hdisj
    · rw [Finset.not_disjoint_iff] at hdisj
      obtain ⟨a, ha1, ha2⟩ := hdisj
      have haI := (Finset.mem_filter.mp ha1).1
      have hp1 := (Finset.mem_filter.mp ha1).2
      have hp2 := (Finset.mem_filter.mp ha2).2
      -- Both u and v lie on the unique Follow path from inputWire a to outWire!
      have hf1 := hread_before_I a haI u hp1
      have hf2 := hread_before_I a haI v hp2
      have hpath_le : ∀ x y : W,
          ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) (inputWire gs a) x →
          ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) (inputWire gs a) y →
          x ≤ y → ReflTransGen (readEdge gs) x y := by
        intro x y px py hxy
        have hfol : ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) x y := by
          induction px generalizing y with
          | refl => exact py
          | tail px' step ih =>
            rename_i p q
            rcases py.cases_tail with rfl | ⟨z, pz, stepz⟩
            · have hlt := read_order least.hcl step.1
              have hle := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl)
                (FirstBranchRoute.follows_is_read_path _ _ px')
              exact False.elim (not_lt_of_ge hxy (lt_of_le_of_lt hle hlt))
            · by_cases hqy : q = y
              · subst hqy; exact ReflTransGen.refl
              · have hlt_qy : q < y := lt_of_le_of_ne hxy hqy
                have hstep := ih y (pz.tail stepz) (le_of_lt (lt_trans (read_order least.hcl step.1) hlt_qy))
                rcases hstep.cases_head with rfl | ⟨q', step', tail'⟩
                · exact False.elim (not_lt_of_ge (le_of_lt hlt_qy) (read_order least.hcl step.1))
                · have heq := FirstBranchRoute.follow_unique (readEdge gs) outWire step step'
                  subst heq; exact tail'
        exact FirstBranchRoute.follows_is_read_path _ _ hfol
      rcases le_total u v with huv | hvu
      · right; left
        have hpuv := hpath_le u v hf1 hf2 huv
        intro b hb
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2.trans hpuv⟩
      · right; right
        have hpvu := hpath_le v u hf2 hf1 hvu
        intro b hb
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2.trans hpvu⟩

  -- Now choose the optimal ordering ι : Fin 4 → V10 of I based on PairSets of Q_active!
  let PairSets : Finset (Finset V10) :=
    (Q_active.filter fun p => (reachI (gateWire p)).card = 2).image (fun p => reachI (gateWire p))
  have hPair_sub (P : Finset V10) (hP : P ∈ PairSets) : P ⊆ I ∧ P.card = 2 := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨Finset.filter_subset _ _, (Finset.mem_filter.mp hp).2⟩
  have hPair_disj (P1 P2 : Finset V10) (h1 : P1 ∈ PairSets) (h2 : P2 ∈ PairSets) (hne : P1 ≠ P2) :
      Disjoint P1 P2 := by
    obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨p2, hp2, rfl⟩ := Finset.mem_image.mp h2
    have hT1 : gateWire p1 ∈ T_wires := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).1).2.1
    have hT2 : gateWire p2 ∈ T_wires := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1).2.1
    have hc1 : (reachI (gateWire p1)).card = 2 := (Finset.mem_filter.mp hp1).2
    have hc2 : (reachI (gateWire p2)).card = 2 := (Finset.mem_filter.mp hp2).2
    rcases hT_reachI_tree (gateWire p1) (gateWire p2) hT1 hT2 with hd | hsub | hsub
    · exact hd
    · exact False.elim (hne (Finset.eq_of_subset_of_card_le hsub (by omega)))
    · exact False.elim (hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm)

  have hPair_le2 : PairSets.card ≤ 2 := by
    by_contra hgt
    have hge3 : 3 ≤ PairSets.card := by omega
    obtain ⟨P1, hP1, P2, hP2, P3, hP3, h12, h13, h23⟩ :
        ∃ P1 ∈ PairSets, ∃ P2 ∈ PairSets, ∃ P3 ∈ PairSets, P1 ≠ P2 ∧ P1 ≠ P3 ∧ P2 ≠ P3 := by
      obtain ⟨P1, hP1⟩ := Finset.card_pos.mp (by omega : 0 < PairSets.card)
      have hc2 : 0 < (PairSets.erase P1).card := by rw [Finset.card_erase_of_mem hP1]; omega
      obtain ⟨P2, hP2'⟩ := Finset.card_pos.mp hc2
      have hP2 := Finset.mem_of_mem_erase hP2'
      have h12 : P1 ≠ P2 := (Finset.ne_of_mem_erase hP2').symm
      have hc3 : 0 < ((PairSets.erase P1).erase P2).card := by
        rw [Finset.card_erase_of_mem hP2', Finset.card_erase_of_mem hP1]; omega
      obtain ⟨P3, hP3''⟩ := Finset.card_pos.mp hc3
      have hP3' := Finset.mem_of_mem_erase hP3''
      have hP3 := Finset.mem_of_mem_erase hP3'
      exact ⟨P1, hP1, P2, hP2, P3, hP3, h12, (Finset.ne_of_mem_erase hP3').symm, (Finset.ne_of_mem_erase hP3'').symm⟩
    have hsub : P1 ∪ P2 ∪ P3 ⊆ I :=
      Finset.union_subset (Finset.union_subset (hPair_sub P1 hP1).1 (hPair_sub P2 hP2).1) (hPair_sub P3 hP3).1
    have hd12 := hPair_disj P1 P2 hP1 hP2 h12
    have hd12_3 : Disjoint (P1 ∪ P2) P3 :=
      Finset.disjoint_union_left.mpr ⟨hPair_disj P1 P3 hP1 hP3 h13, hPair_disj P2 P3 hP2 hP3 h23⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd12_3, Finset.card_union_of_disjoint hd12,
      (hPair_sub P1 hP1).2, (hPair_sub P2 hP2).2, (hPair_sub P3 hP3).2, hI4] at hcard
    omega

  -- Build bijection ι : Fin 4 → V10 onto I aligning PairSets with {0,1} and {2,3}!
  have hex_iota : ∃ ι : Fin 4 → V10,
      Function.Injective ι ∧ Finset.univ.image ι = I ∧
      (∀ P ∈ PairSets,
        (PairSets.card = 1 → P = {ι 0, ι 1}) ∧
        (PairSets.card = 2 → P = {ι 0, ι 1} ∨ P = {ι 2, ι 3})) := by
    have splitPair (S : Finset V10) (hS : S.card = 2) : ∃ a b : V10, a ≠ b ∧ S = {a, b} :=
      Finset.card_eq_two.mp hS
    have mkIota := mkIota_aux I
    by_cases hc0 : PairSets.card = 0
    · obtain ⟨a0, ha0⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
      obtain ⟨a1, ha1'⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha0]; omega : 0 < (I.erase a0).card)
      have ha1 := Finset.mem_of_mem_erase ha1'
      have h01 : a0 ≠ a1 := (Finset.ne_of_mem_erase ha1').symm
      let R := I \ {a0, a1}
      have hRsub : ({a0, a1} : Finset V10) ⊆ I := by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      have hRcard : R.card = 2 := by
        have h := Finset.card_sdiff_add_card_eq_card hRsub
        rw [Finset.card_pair h01, hI4] at h
        change R.card + 2 = 4 at h; omega
      obtain ⟨a2, a3, h23, hReq⟩ := splitPair R hRcard
      have hd : Disjoint ({a0, a1} : Finset V10) {a2, a3} := by rw [← hReq]; exact disjoint_sdiff_self_right
      have hEq : ({a0, a1} : Finset V10) ∪ {a2, a3} = I := by rw [← hReq]; exact Finset.union_sdiff_of_subset hRsub
      obtain ⟨ι, hinj, himg, _⟩ := mkIota a0 a1 a2 a3 h01 h23 hd hEq
      exact ⟨ι, hinj, himg, fun P hP => ⟨fun h => by omega, fun h => by omega⟩⟩
    · by_cases hc1 : PairSets.card = 1
      · obtain ⟨P1, hP1eq⟩ := Finset.card_eq_one.mp hc1
        have hP1 : P1 ∈ PairSets := by rw [hP1eq]; simp
        obtain ⟨a0, a1, h01, hP1ab⟩ := splitPair P1 (hPair_sub P1 hP1).2
        let R := I \ P1
        have hRcard : R.card = 2 := by
          have h := Finset.card_sdiff_add_card_eq_card (hPair_sub P1 hP1).1
          rw [(hPair_sub P1 hP1).2, hI4] at h
          change R.card + 2 = 4 at h; omega
        obtain ⟨a2, a3, h23, hReq⟩ := splitPair R hRcard
        have hd : Disjoint ({a0, a1} : Finset V10) {a2, a3} := by
          rw [← hP1ab, ← hReq]; exact disjoint_sdiff_self_right
        have hEq : ({a0, a1} : Finset V10) ∪ {a2, a3} = I := by
          rw [← hP1ab, ← hReq]; exact Finset.union_sdiff_of_subset (hPair_sub P1 hP1).1
        obtain ⟨ι, hinj, himg, h0, h1, _, _⟩ := mkIota a0 a1 a2 a3 h01 h23 hd hEq
        refine ⟨ι, hinj, himg, fun P hP => ⟨fun _ => ?_, fun h => by omega⟩⟩
        rw [hP1eq, Finset.mem_singleton] at hP
        rw [hP, hP1ab, h0, h1]
      · have hc2 : PairSets.card = 2 := by omega
        obtain ⟨P1, P2, hne, hP12eq⟩ := Finset.card_eq_two.mp hc2
        have hP1 : P1 ∈ PairSets := by rw [hP12eq]; simp
        have hP2 : P2 ∈ PairSets := by rw [hP12eq]; simp
        obtain ⟨a0, a1, h01, hP1ab⟩ := splitPair P1 (hPair_sub P1 hP1).2
        obtain ⟨a2, a3, h23, hP2ab⟩ := splitPair P2 (hPair_sub P2 hP2).2
        have hd : Disjoint ({a0, a1} : Finset V10) {a2, a3} := by
          rw [← hP1ab, ← hP2ab]; exact hPair_disj P1 P2 hP1 hP2 hne
        have hEq : ({a0, a1} : Finset V10) ∪ {a2, a3} = I := by
          apply Finset.eq_of_subset_of_card_le
          · rw [← hP1ab, ← hP2ab]; exact Finset.union_subset (hPair_sub P1 hP1).1 (hPair_sub P2 hP2).1
          · rw [Finset.card_union_of_disjoint hd, Finset.card_pair h01, Finset.card_pair h23, hI4]
        obtain ⟨ι, hinj, himg, h0, h1, h2, h3⟩ := mkIota a0 a1 a2 a3 h01 h23 hd hEq
        refine ⟨ι, hinj, himg, fun P hP => ⟨fun h => by omega, fun _ => ?_⟩⟩
        rw [hP12eq, Finset.mem_insert, Finset.mem_singleton] at hP
        rcases hP with rfl | rfl
        · exact Or.inl (by rw [hP1ab, h0, h1])
        · exact Or.inr (by rw [hP2ab, h2, h3])

  obtain ⟨ι, hι_inj, hι_img, hPair_align⟩ := hex_iota
  have hι_mem (k : Fin 4) : ι k ∈ I := by rw [← hι_img]; exact Finset.mem_image_of_mem ι (Finset.mem_univ k)
  have hι_ind : ∀ p q : Fin 4, ¬ p10Graph.Adj (ι p) (ι q) :=
    fun p q => hI_indep (ι p) (hι_mem p) (ι q) (hι_mem q)
  obtain ⟨hσ_inj, hI_S_disj, hcover, hcombI, hcombS, hp10_comb⟩ :=
    ordered_indep4_iso ι hι_inj hι_ind
  let σ := sigmaOf ι

  -- Inputs x0 s (all I = false) and x1 k s (only ι k = true)
  let x0 (s : Fin 6 → Bool) : V10 → Bool := combine ι σ (fun _ => false) s
  let x1 (k : Fin 4) (s : Fin 6 → Bool) : V10 → Bool := combine ι σ (fun j => decide (j = k)) s

  have hx0_eval (s : Fin 6 → Bool) : vl gs (x0 s) outWire.val = M6 s := by
    change vl gs (x0 s) out = M6 s
    rw [least.hev, hp10_comb]; simp
  have hx1_eval (k : Fin 4) (s : Fin 6 → Bool) : vl gs (x1 k s) outWire.val = (M6 s || A6 k s) := by
    change vl gs (x1 k s) out = _
    rw [least.hev, hp10_comb]
    fin_cases k <;> simp

  -- Every wire w ∉ T_wires depends ONLY on s (independent of u on I)!
  have hS_indep (w : W) (hw : w ∉ T_wires) (u1 u2 : Fin 4 → Bool) (s : Fin 6 → Bool) :
      vl gs (combine ι σ u1 s) w.val = vl gs (combine ι σ u2 s) w.val := by
    apply agree_on_input_ancestors least.hcl
    intro v hpath
    have hv_notI : v ∉ I := fun hvI => hw ((hmemT w).mpr ⟨v, hvI, hpath⟩)
    rcases hcover v with ⟨k, rfl⟩ | ⟨j, rfl⟩
    · exact False.elim (hv_notI (hι_mem k))
    · rw [hcombS, hcombS]

  -- Also for any k : Fin 4 and wire w with ι k ∉ reachI w, vl(x1 k s, w) = vl(x0 s, w)!
  have hNoReach_eq (k : Fin 4) (w : W) (hno : ι k ∉ reachI w) (s : Fin 6 → Bool) :
      vl gs (x1 k s) w.val = vl gs (x0 s) w.val := by
    apply agree_on_input_ancestors least.hcl
    intro v hpath
    dsimp only [x1, x0]
    rcases hcover v with ⟨k', rfl⟩ | ⟨j, rfl⟩
    · rw [hcombI, hcombI]
      by_cases hk' : k' = k
      · subst hk'
        exact False.elim (hno (Finset.mem_filter.mpr ⟨hι_mem k', hpath⟩))
      · simp [hk']
    · rw [hcombS, hcombS]

  -- Any wire w on the path from ι k to outWire separates x1 k s from x0 s whenever M6 s = false ∧ A6 k s = true!
  have hPath_diff (k : Fin 4) (w : W) (hk : ι k ∈ reachI w)
      (s : Fin 6 → Bool) (hm : M6 s = false) (hAk : A6 k s = true) :
      vl gs (x1 k s) w.val ≠ vl gs (x0 s) w.val := by
    intro hsame
    have heq := circuit_cut_agreement least.hcl w outWire (x1 k s) (x0 s) hsame (by
      intro v hvdiff hpath
      dsimp only [x1, x0] at hvdiff
      rcases hcover v with ⟨k', rfl⟩ | ⟨j, rfl⟩
      · rw [hcombI, hcombI] at hvdiff
        have hk' : k' = k := by by_contra hne; simp [hne] at hvdiff
        subst k'
        -- Every path from inputWire (ι k) to outWire goes through w!
        have hwT : w ∈ T_wires := (hmemT w).mpr ⟨ι k, hι_mem k, (Finset.mem_filter.mp hk).2⟩
        -- Walk along hpath avoiding w: since inputWire (ι k) has unique Follow path reaching w then outWire,
        -- avoiding w cannot reach outWire!
        have hstep_avoid : ∀ z : W, ReflTransGen (avoid (readEdge gs) w) (inputWire gs (ι k)) z →
            ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) (inputWire gs (ι k)) z := by
          intro z hz
          have hrz : ReflTransGen (readEdge gs) (inputWire gs (ι k)) z :=
            ReflTransGen.mono (fun _ _ h => h.1) _ _ hz
          exact hread_before_I (ι k) (hι_mem k) z hrz
        have hfw := hread_before_I (ι k) (hι_mem k) w (Finset.mem_filter.mp hk).2
        -- Show w must be visited on any avoid-path from inputWire (ι k) to outWire:
        have hno_skip : ∀ z : W, ReflTransGen (avoid (readEdge gs) w) (inputWire gs (ι k)) z →
            z ≠ outWire → z < w := by
          intro z hz
          induction hz with
          | refl =>
            intro _
            have hle := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl)
              (FirstBranchRoute.follows_is_read_path _ _ hfw)
            by_cases hweq : inputWire gs (ι k) = w
            · -- Then hpath avoids w so hpath must be refl, meaning inputWire (ι k) = outWire = w
              rcases hpath.cases_head with heqo | ⟨_, ha, _⟩
              · rw [hweq] at heqo
                rw [heqo] at hsame
                rw [hx1_eval k s, hx0_eval s, hm, hAk] at hsame
                exact Bool.noConfusion hsame
              · exact False.elim (ha.2.1 hweq)
            · exact lt_of_le_of_ne hle hweq
          | @tail x y hz' ha ih =>
            intro _
            have hx_lt : x < w := by
              by_cases hxo : x = outWire
              · exact False.elim (hout_no_out y (hxo ▸ ha.1))
              · exact ih hxo
            -- x is on the unique Follow-path from inputWire (ι k) to w!
            have hfx := hstep_avoid x hz'
            have hfx_w := hfollow_subpath (inputWire gs (ι k)) x w hfx hfw (le_of_lt hx_lt)
            rcases hfx_w.cases_head with rfl | ⟨y', st', tl'⟩
            · exact False.elim (lt_irrefl _ hx_lt)
            · have hxT : x ∈ T_wires := (hmemT x).mpr ⟨ι k, hι_mem k,
                ReflTransGen.mono (fun _ _ h => h.1) _ _ hz'⟩
              have hxne : x ≠ outWire := ne_of_lt (lt_of_lt_of_le hx_lt (hT_le_out w))
              obtain ⟨_, _, huniq⟩ := hT_unique_out x hxT hxne
              have hy_eq : y = y' := (huniq y ha.1).trans (huniq y' st'.1).symm
              subst hy_eq
              have hle_yw := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl)
                (FirstBranchRoute.follows_is_read_path _ _ tl')
              exact lt_of_le_of_ne hle_yw ha.2.2
        rcases hpath.cases_tail with heqo | ⟨x, hx, ha⟩
        · have hle_iw := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl)
            (FirstBranchRoute.follows_is_read_path _ _ hfw)
          rw [← heqo] at hle_iw
          have hwo : w = outWire := le_antisymm (hT_le_out w) hle_iw
          rw [hwo] at hsame
          rw [hx1_eval k s, hx0_eval s, hm, hAk] at hsame
          exact Bool.noConfusion hsame
        · have hxne : x ≠ outWire := fun h => hout_no_out outWire (h ▸ ha.1)
          have hx_lt : x < w := hno_skip x hx hxne
          have hfx := hstep_avoid x hx
          have hxT : x ∈ T_wires := (hmemT x).mpr ⟨ι k, hι_mem k,
            ReflTransGen.mono (fun _ _ h => h.1) _ _ hx⟩
          have hfx_w := hfollow_subpath (inputWire gs (ι k)) x w hfx hfw (le_of_lt hx_lt)
          rcases hfx_w.cases_head with rfl | ⟨y', st', tl'⟩
          · exact lt_irrefl _ hx_lt
          · obtain ⟨_, _, huniq⟩ := hT_unique_out x hxT hxne
            have hout_eq : outWire = y' := (huniq outWire ha.1).trans (huniq y' st'.1).symm
            rw [← hout_eq] at tl'
            have hle_ow := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl)
              (FirstBranchRoute.follows_is_read_path _ _ tl')
            have hwo : w = outWire := le_antisymm (hT_le_out w) hle_ow
            exact ha.2.2 hwo.symm
      · rw [hcombS, hcombS] at hvdiff; exact hvdiff rfl)
    rw [hx1_eval k s, hx0_eval s, hm, hAk] at heq
    exact Bool.noConfusion heq

  -- Top-Down Constant-on-Active-Support Theorem:
  -- For EVERY w ∈ T_wires, k ∈ Fin 4 with ι k ∈ reachI w, and s with M6 s = false ∧ A6 k s = true:
  --   vl gs (x0 s) w.val = inact w !
  have hinact_active : ∀ d : Nat, ∀ w : W, 10 + gs.length - w.val ≤ d →
      w ∈ T_wires → ∀ k : Fin 4, ι k ∈ reachI w →
      ∀ s : Fin 6 → Bool, M6 s = false → A6 k s = true →
      vl gs (x0 s) w.val = inact w := by
    intro d
    induction d with
    | zero => intro w hd; have := w.isLt; omega
    | succ d ih =>
      intro w hd hwT k hk s hm hAk
      by_cases hwo : w = outWire
      · subst hwo
        rw [hx0_eval s, hm, hinact_out]
      · obtain ⟨he, hpT, hlt⟩ := hparent_spec w hwT hwo
        let p := parentOf w
        have hkp : ι k ∈ reachI p :=
          Finset.mem_filter.mpr ⟨hι_mem k, (Finset.mem_filter.mp hk).2.tail he⟩
        have hIHp : vl gs (x0 s) p.val = inact p :=
          ih p (by have := p.isLt; omega) hpT k hkp s hm hAk
        have hp_diff : vl gs (x1 k s) p.val ≠ vl gs (x0 s) p.val :=
          hPath_diff k p hkp s hm hAk
        have hpgt : 10 ≤ p.val := by
          by_contra hlt10
          exact no_read_into_input w p (by omega) he
        let pidx : Fin gs.length := ⟨p.val - 10, by have := p.isLt; omega⟩
        have hpeq : gateWire pidx = p := Fin.ext (by dsimp [gateWire, pidx]; omega)
        have hget : gs[pidx.val]? = some (gs.get pidx) := by
          rw [List.getElem?_eq_getElem pidx.isLt, List.get_eq_getElem]
        have hcl_p := least.hcl pidx.val (gs.get pidx) hget
        have hstep := hinact_step w hwT hwo
        change inact w = Bool.xor (isNotWire p) (inact p) at hstep
        have hw_mem : w.val ∈ (gs.get pidx).inputs := by
          change readEdge gs w p at he
          rw [← hpeq] at he
          exact (gate_read_inputs least.hcl pidx w).mp he
        rcases hcl_p with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k', hj, hk', hinp⟩
        · -- NOT gate
          rw [hinp, List.mem_singleton] at hw_mem
          have hisNot : isNotWire p = true := by
            simp only [isNotWire, hpgt, ↓reduceDIte]
            change isNotGate (gs.get pidx).op = true
            rw [hop]; rfl
          rw [hstep, hisNot, Bool.true_xor, ← hIHp]
          have hv0 : vl gs (x0 s) p.val = !(vl gs (x0 s) w.val) := by
            rw [← hpeq]; change vl gs (x0 s) (10 + pidx.val) = _
            rw [vl_gate gs least.hcl (x0 s) pidx.val (gs.get pidx) hget, hinp, hop, hw_mem]
            rfl
          rw [hv0, Bool.not_not]
        · -- Binary AND/OR gate with inputs j, k'
          have hisNot : isNotWire p = false := by
            simp only [isNotWire, hpgt, ↓reduceDIte]
            change isNotGate (gs.get pidx).op = false
            rcases hop with hop | hop <;> (rw [hop]; rfl)
          rw [hstep, hisNot, Bool.false_xor, ← hIHp]
          let uj : W := ⟨j, by omega⟩
          let uk : W := ⟨k', by omega⟩
          have hndp := hnd (gs.get pidx) (List.get_mem _ _)
          rw [hinp, List.nodup_cons, List.mem_singleton] at hndp
          have hne_jk : uj ≠ uk := fun h => hndp.1 (congrArg Fin.val h)
          have hej : readEdge gs uj p := by
            rw [← hpeq]; exact (gate_read_inputs least.hcl pidx uj).mpr (by rw [hinp]; simp [uj])
          have hek : readEdge gs uk p := by
            rw [← hpeq]; exact (gate_read_inputs least.hcl pidx uk).mpr (by rw [hinp]; simp [uk])
          have hother : ∃ u : W, u ≠ w ∧ readEdge gs u p ∧
              (∀ x : V10 → Bool, vl gs x p.val =
                if absOp pidx then (vl gs x w.val || vl gs x u.val) else (vl gs x w.val && vl gs x u.val)) := by
            rw [hinp] at hw_mem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hw_mem
            rcases hw_mem with hmj | hmk
            · have hweq : w = uj := Fin.ext hmj
              refine ⟨uk, hweq ▸ hne_jk.symm, hek, fun x => ?_⟩
              rw [← hpeq]; change vl gs x (10 + pidx.val) = _
              rw [vl_gate gs least.hcl x pidx.val (gs.get pidx) hget, hinp, hweq]
              rcases hop with hop | hop
              · simp only [absOp, hop, List.map_cons, List.map_nil, uj, uk]
                generalize vl gs x j = b1; generalize vl gs x k' = b2
                cases b1 <;> cases b2 <;> rfl
              · simp only [absOp, hop, List.map_cons, List.map_nil, uj, uk]
                generalize vl gs x j = b1; generalize vl gs x k' = b2
                cases b1 <;> cases b2 <;> rfl
            · have hweq : w = uk := Fin.ext hmk
              refine ⟨uj, hweq ▸ hne_jk, hej, fun x => ?_⟩
              rw [← hpeq]; change vl gs x (10 + pidx.val) = _
              rw [vl_gate gs least.hcl x pidx.val (gs.get pidx) hget, hinp, hweq]
              rcases hop with hop | hop
              · simp only [absOp, hop, List.map_cons, List.map_nil, uj, uk]
                generalize vl gs x j = b1; generalize vl gs x k' = b2
                cases b1 <;> cases b2 <;> rfl
              · simp only [absOp, hop, List.map_cons, List.map_nil, uj, uk]
                generalize vl gs x j = b1; generalize vl gs x k' = b2
                cases b1 <;> cases b2 <;> rfl
          obtain ⟨u, huw, heu, hp_eval⟩ := hother
          have hu_no_k : ι k ∉ reachI u := by
            intro hku
            have huT : u ∈ T_wires := (hmemT u).mpr ⟨ι k, hι_mem k, (Finset.mem_filter.mp hku).2⟩
            exact Finset.disjoint_left.mp (hT_tree_disj u w huw huT hwT p heu he) hku hk
          have hu_same : vl gs (x1 k s) u.val = vl gs (x0 s) u.val := hNoReach_eq k u hu_no_k s
          rw [hp_eval (x1 k s), hp_eval (x0 s), hu_same] at hp_diff
          rw [hp_eval (x0 s)]
          revert hp_diff
          generalize absOp pidx = ab
          generalize vl gs (x0 s) u.val = vu
          generalize vl gs (x0 s) w.val = vw0
          generalize vl gs (x1 k s) w.val = vw1
          revert ab vu vw0 vw1; decide

  -- Corollary 1: Every leaf has inact = false!
  have hinact_leaf (k : Fin 4) : inact (inputWire gs (ι k)) = false := by
    obtain ⟨s, hm, hAk, _⟩ := a6_common_nbr k k
    have h := hinact_active (10 + gs.length) (inputWire gs (ι k)) (by omega)
      (hinI_T (ι k) (hι_mem k)) k (by rw [hreachI_input (ι k) (hι_mem k)]; simp) s hm hAk
    rw [← h]
    change vl gs (x0 s) (ι k).val = false
    rw [vl_input gs (x0 s) (ι k).val (ι k).isLt]
    dsimp only [x0]; rw [hcombI]

  -- Corollary 2: Every Merge gate m satisfies absOp m != inact (gateWire m)!
  have hMerge_abs_ne (p : Fin gs.length) (hp : p ∈ Merges) : absOp p ≠ inact (gateWire p) := by
    obtain ⟨a1, a2, hne, ha1T, ha2T, he1, he2, heval⟩ := hMerge_split p hp
    obtain ⟨v1, hv1⟩ := hreachI_nonempty a1 ha1T
    obtain ⟨v2, hv2⟩ := hreachI_nonempty a2 ha2T
    have hv1I := (Finset.mem_filter.mp hv1).1
    have hv2I := (Finset.mem_filter.mp hv2).1
    rw [← hι_img] at hv1I hv2I
    obtain ⟨k1, _, rfl⟩ := Finset.mem_image.mp hv1I
    obtain ⟨k2, _, rfl⟩ := Finset.mem_image.mp hv2I
    obtain ⟨s, hm, hA1, hA2⟩ := a6_common_nbr k1 k2
    have hact_a2 := hinact_active (10 + gs.length) a2 (by omega) ha2T k2 hv2 s hm hA2
    have ha2_inact : inact a2 = inact (gateWire p) := by
      have ha2_ne : a2 ≠ outWire := fun h => hout_no_out (gateWire p) (h ▸ he2)
      have hst := hinact_step a2 ha2T ha2_ne
      rw [hparent_eq a2 (gateWire p) ha2T he2] at hst
      have hpBin : p ∈ BinIdx := (Finset.mem_filter.mp hp).1
      have hbn := (Finset.mem_filter.mp hpBin).2
      have hisNot : isNotWire (gateWire p) = false := by
        simp only [isNotWire, gateWire, Nat.le_add_right, ↓reduceDIte]
        have heq : (⟨10 + p.val - 10, by omega⟩ : Fin gs.length) = p := Fin.ext (by dsimp; omega)
        rw [heq]
        cases h : isNotGate (gs.get p).op
        · rfl
        · rw [h] at hbn; exact Bool.noConfusion hbn
      rw [hisNot, Bool.false_xor] at hst
      exact hst
    -- Since k1 ∈ reachI (gateWire p) and k1 ∉ reachI a2, gateWire p separates x1 k1 s from x0 s, so vl(x0 s, a2) != absOp p!
    have hk1p : ι k1 ∈ reachI (gateWire p) :=
      Finset.mem_filter.mpr ⟨hι_mem k1, (Finset.mem_filter.mp hv1).2.tail he1⟩
    have hdiff := hPath_diff k1 (gateWire p) hk1p s hm hA1
    have hk1_not_a2 : ι k1 ∉ reachI a2 :=
      Finset.disjoint_left.mp (hT_tree_disj a1 a2 hne ha1T ha2T (gateWire p) he1 he2) hv1
    have ha2_same := hNoReach_eq k1 a2 hk1_not_a2 s
    rw [heval (x1 k1 s), heval (x0 s), ha2_same, hact_a2, ha2_inact] at hdiff
    intro heq
    rw [heq] at hdiff
    revert hdiff
    generalize inact (gateWire p) = iw
    generalize vl gs (x1 k1 s) a1.val = v1
    generalize vl gs (x0 s) a1.val = v0
    revert iw v1 v0; decide

  -- Active-high coordinate: act(w, x) := Bool.xor (vl gs x w.val) (inact w)
  let act (w : W) (x : V10 → Bool) : Bool := Bool.xor (vl gs x w.val) (inact w)

  -- Corollary 3: Q_passive is nonempty, so GS.card + Q_active.card <= 11!
  have hQ_passive_pos : 1 ≤ Q_passive.card := by
    by_contra h0
    have hQ_empty : Q_passive = ∅ := Finset.card_eq_zero.mp (by omega)
    -- Show by induction on w.val that for ALL w ∈ T_wires and ALL s, act w (x0 s) = false!
    have hall_false : ∀ n : Nat, ∀ w : W, w.val ≤ n → w ∈ T_wires → ∀ s : Fin 6 → Bool, act w (x0 s) = false := by
      intro n
      induction n with
      | zero =>
        intro w hwn hwT s
        obtain ⟨v, hvI, hp⟩ := (hmemT w).mp hwT
        rcases hp.cases_tail with rfl | ⟨u, _, he⟩
        · rw [← hι_img] at hvI
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hvI
          dsimp [act]
          rw [hinact_leaf k, Bool.xor_false]
          change vl gs (x0 s) (ι k).val = false
          rw [vl_input gs (x0 s) (ι k).val (ι k).isLt]
          dsimp only [x0]; rw [hcombI]
        · exact False.elim (no_read_into_input u w (by omega) he)
      | succ n ih =>
        intro w hwn hwT s
        by_cases hlt10 : w.val < 10
        · obtain ⟨v, hvI, hp⟩ := (hmemT w).mp hwT
          rcases hp.cases_tail with rfl | ⟨u, _, he⟩
          · rw [← hι_img] at hvI
            obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hvI
            dsimp [act]
            rw [hinact_leaf k, Bool.xor_false]
            change vl gs (x0 s) (ι k).val = false
            rw [vl_input gs (x0 s) (ι k).val (ι k).isLt]
            dsimp only [x0]; rw [hcombI]
          · exact False.elim (no_read_into_input u w hlt10 he)
        · let pidx : Fin gs.length := ⟨w.val - 10, by have := w.isLt; omega⟩
          have hweq : gateWire pidx = w := Fin.ext (by dsimp [gateWire, pidx]; omega)
          have hget : gs[pidx.val]? = some (gs.get pidx) := by
            rw [List.getElem?_eq_getElem pidx.isLt, List.get_eq_getElem]
          cases hnot : isNotGate (gs.get pidx).op
          · -- Binary gate in T_wires: either Gating (must be Q_active!) or Merges!
            have hpBin : pidx ∈ BinIdx := Finset.mem_filter.mpr ⟨Finset.mem_univ pidx, by rw [hnot]; rfl⟩
            have hpT : gateWire pidx ∈ T_wires := hweq.symm ▸ hwT
            have h1 := hT_gate_inDeg_pos pidx hpT
            have h2 := hBin_inDeg_le2 pidx hpBin
            rcases (by omega : inDegT (gateWire pidx) = 1 ∨ inDegT (gateWire pidx) = 2) with hd | hd
            · -- Gating: since Q_passive = ∅, absOp pidx = inact w!
              have hpGat : pidx ∈ Gating := Finset.mem_filter.mpr ⟨hpBin, hpT, hd⟩
              have habs_eq : absOp pidx = inact w := by
                by_contra hne
                have hmem : pidx ∈ Q_passive := Finset.mem_filter.mpr ⟨hpGat, by rwa [hweq]⟩
                rw [hQ_empty] at hmem; exact Finset.notMem_empty _ hmem
              obtain ⟨a, b, haT, _, hea, _, heval⟩ := hGating_split pidx hpGat
              have halt : a.val < w.val := hweq ▸ read_order least.hcl hea
              have ha_f : act a (x0 s) = false := ih a (by omega) haT s
              have ha_ne : a ≠ outWire := fun h => hout_no_out (gateWire pidx) (h ▸ hea)
              have ha_inact : inact a = inact w := by
                have hst := hinact_step a haT ha_ne
                rw [hparent_eq a (gateWire pidx) haT hea, hweq] at hst
                have hisNot : isNotWire w = false := by
                  simp only [isNotWire, show 10 ≤ w.val by omega, ↓reduceDIte]
                  exact hnot
                rw [hisNot, Bool.false_xor] at hst; exact hst
              have hva : vl gs (x0 s) a.val = inact w := by
                dsimp [act] at ha_f; rw [ha_inact] at ha_f
                revert ha_f; generalize vl gs (x0 s) a.val = va; generalize inact w = iw
                revert va iw; decide
              dsimp [act]
              rw [← hweq, heval (x0 s), hweq, habs_eq, hva]
              cases inact w <;> cases vl gs (x0 s) b.val <;> rfl
            · -- Merge: absOp pidx != inact w!
              have hpMrg : pidx ∈ Merges := Finset.mem_filter.mpr ⟨hpBin, hpT, hd⟩
              have habs_ne : absOp pidx ≠ inact w := hweq ▸ hMerge_abs_ne pidx hpMrg
              obtain ⟨a1, a2, _, ha1T, ha2T, he1, he2, heval⟩ := hMerge_split pidx hpMrg
              have ha1_f := ih a1 (by have := hweq ▸ read_order least.hcl he1; omega) ha1T s
              have ha2_f := ih a2 (by have := hweq ▸ read_order least.hcl he2; omega) ha2T s
              have ha_inact (a : W) (haT : a ∈ T_wires) (hea : readEdge gs a (gateWire pidx)) : inact a = inact w := by
                have hne : a ≠ outWire := fun h => hout_no_out (gateWire pidx) (h ▸ hea)
                have hst := hinact_step a haT hne
                rw [hparent_eq a (gateWire pidx) haT hea, hweq] at hst
                have hisNot : isNotWire w = false := by
                  simp only [isNotWire, show 10 ≤ w.val by omega, ↓reduceDIte]; exact hnot
                rw [hisNot, Bool.false_xor] at hst; exact hst
              have hv1 : vl gs (x0 s) a1.val = inact w := by
                dsimp [act] at ha1_f; rw [ha_inact a1 ha1T he1] at ha1_f
                revert ha1_f; generalize vl gs (x0 s) a1.val = va; generalize inact w = iw
                revert va iw; decide
              have hv2 : vl gs (x0 s) a2.val = inact w := by
                dsimp [act] at ha2_f; rw [ha_inact a2 ha2T he2] at ha2_f
                revert ha2_f; generalize vl gs (x0 s) a2.val = va; generalize inact w = iw
                revert va iw; decide
              dsimp [act]
              rw [← hweq, heval (x0 s), hweq, hv1, hv2]
              revert habs_ne; generalize absOp pidx = ab; generalize inact w = iw
              revert ab iw; decide
          · -- NOT gate in T_wires
            have hcl_p := least.hcl pidx.val (gs.get pidx) hget
            rcases hcl_p with ⟨hop, j, hj, hinp⟩ | ⟨hop | hop, _⟩
            · let a : W := ⟨j, by omega⟩
              have hea : readEdge gs a (gateWire pidx) :=
                (gate_read_inputs least.hcl pidx a).mpr (by rw [hinp]; simp [a])
              have haT : a ∈ T_wires := by
                have hpos : 0 < (T_wires.filter fun u => readEdge gs u (gateWire pidx)).card :=
                  lt_of_lt_of_le Nat.zero_lt_one (hT_gate_inDeg_pos pidx (hweq.symm ▸ hwT))
                obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
                have huT := (Finset.mem_filter.mp hu).1
                have hmem := (gate_read_inputs least.hcl pidx u).mp (Finset.mem_filter.mp hu).2
                rw [hinp, List.mem_singleton] at hmem
                have hua : u = a := Fin.ext hmem
                exact hua ▸ huT
              have ha_f := ih a (by have := hweq ▸ read_order least.hcl hea; omega) haT s
              have hne : a ≠ outWire := fun h => hout_no_out (gateWire pidx) (h ▸ hea)
              have hst := hinact_step a haT hne
              rw [hparent_eq a (gateWire pidx) haT hea, hweq] at hst
              have hisNot : isNotWire w = true := by
                simp only [isNotWire, show 10 ≤ w.val by omega, ↓reduceDIte]; exact hnot
              rw [hisNot, Bool.true_xor] at hst
              have hvw : vl gs (x0 s) w.val = !(vl gs (x0 s) a.val) := by
                rw [← hweq]; change vl gs (x0 s) (10 + pidx.val) = _
                rw [vl_gate gs least.hcl (x0 s) pidx.val (gs.get pidx) hget, hinp, hop]; rfl
              dsimp [act] at ha_f ⊢
              rw [hvw]
              rw [hst] at ha_f
              revert ha_f; generalize vl gs (x0 s) a.val = va; generalize inact w = iw
              revert va iw; decide
            · rw [hop] at hnot; exact Bool.noConfusion hnot
            · rw [hop] at hnot; exact Bool.noConfusion hnot
    -- Contradiction at s = (s0=true, s2=true) where M6 s = true!
    let sM : Fin 6 → Bool := ![true, false, true, false, false, false]
    have hact_out := hall_false (10 + gs.length) outWire (by omega) hout_inT sM
    dsimp [act] at hact_out
    rw [hx0_eval sM, hinact_out, Bool.xor_false] at hact_out
    have hMtrue : M6 sM = true := rfl
    rw [hMtrue] at hact_out
    exact Bool.noConfusion hact_out

  have hGS_Qact : GS.card + Q_active.card ≤ 11 := by omega

  -- For each p ∈ Q_active, pick its S-input wire bOf p ∉ T_wires and pass polarity!
  -- pass(p, s) = Bool.xor (vl gs (x0 s) (bOf p).val) (absOp p) (true iff bOf p != absOp p!).
  let bOf (p : Fin gs.length) : W :=
    if h : p ∈ Gating then (hGating_split p h).choose_spec.choose else outWire
  have hbOf_spec (p : Fin gs.length) (hp : p ∈ Gating) :
      ∃ a : W, a ∈ T_wires ∧ bOf p ∉ T_wires ∧
        readEdge gs a (gateWire p) ∧ readEdge gs (bOf p) (gateWire p) ∧
        (∀ x : V10 → Bool,
          vl gs x (gateWire p).val =
            if absOp p then (vl gs x a.val || vl gs x (bOf p).val)
            else (vl gs x a.val && vl gs x (bOf p).val)) := by
    let a := (hGating_split p hp).choose
    have hspec := (hGating_split p hp).choose_spec.choose_spec
    have hbeq : bOf p = (hGating_split p hp).choose_spec.choose := by
      dsimp only [bOf]; rw [dite_eq_left hp]
    rw [hbeq]
    exact ⟨a, hspec⟩

  let passOf (p : Fin gs.length) (s : Fin 6 → Bool) : Bool :=
    Bool.xor (vl gs (x0 s) (bOf p).val) (absOp p)

  -- MASTER TREE EQUIVALENCE THEOREM:
  -- For every k : Fin 4 and every s with M6 s = false:
  --   A6 k s = true ↔ ∀ p ∈ Q_active, ι k ∈ reachI (gateWire p) → passOf p s = true !
  have hMaster_equiv (k : Fin 4) (s : Fin 6 → Bool) (hm : M6 s = false) :
      A6 k s = true ↔ ∀ p ∈ Q_active, ι k ∈ reachI (gateWire p) → passOf p s = true := by
    constructor
    · intro hAk p hp hkp
      have hpGat : p ∈ Gating := (Finset.mem_filter.mp hp).1
      obtain ⟨a, _, hbNotT, _, _, heval⟩ := hbOf_spec p hpGat
      have hdiff := hPath_diff k (gateWire p) hkp s hm hAk
      have hbsame : vl gs (x1 k s) (bOf p).val = vl gs (x0 s) (bOf p).val :=
        hS_indep (bOf p) hbNotT _ _ s
      rw [heval (x1 k s), heval (x0 s), hbsame] at hdiff
      dsimp [passOf]
      revert hdiff
      generalize absOp p = ab; generalize vl gs (x0 s) (bOf p).val = vb
      generalize vl gs (x1 k s) a.val = va1; generalize vl gs (x0 s) a.val = va0
      revert ab vb va1 va0; decide
    · intro hall
      -- Walk UP from inputWire (ι k) to outWire, proving act w (x1 k s) = true for all w on the path!
      have hup : ∀ d : Nat, ∀ w : W, 10 + gs.length - w.val ≤ d →
          w ∈ T_wires → ι k ∈ reachI w → act w (x1 k s) = true → act outWire (x1 k s) = true := by
        intro d
        induction d with
        | zero => intro w hd; have := w.isLt; omega
        | succ d ih =>
          intro w hd hwT hkw hact_w
          by_cases hwo : w = outWire
          · exact hwo ▸ hact_w
          · obtain ⟨he, hpT, hlt⟩ := hparent_spec w hwT hwo
            let p := parentOf w
            have hkp : ι k ∈ reachI p :=
              Finset.mem_filter.mpr ⟨hι_mem k, (Finset.mem_filter.mp hkw).2.tail he⟩
            apply ih p (by have := p.isLt; omega) hpT hkp
            have hpgt : 10 ≤ p.val := by
              by_contra hlt10; exact no_read_into_input w p (by omega) he
            let pidx : Fin gs.length := ⟨p.val - 10, by have := p.isLt; omega⟩
            have hpeq : gateWire pidx = p := Fin.ext (by dsimp [gateWire, pidx]; omega)
            have he' : readEdge gs w (gateWire pidx) := by
              change readEdge gs w p at he; rwa [hpeq]
            have hget : gs[pidx.val]? = some (gs.get pidx) := by
              rw [List.getElem?_eq_getElem pidx.isLt, List.get_eq_getElem]
            have hst := hinact_step w hwT hwo
            change inact w = Bool.xor (isNotWire p) (inact p) at hst
            cases hnot : isNotGate (gs.get pidx).op
            · have hisNot : isNotWire p = false := by
                simp only [isNotWire, hpgt, ↓reduceDIte]; exact hnot
              rw [hisNot, Bool.false_xor] at hst
              have hvw_ne : vl gs (x1 k s) w.val = !(inact p) := by
                dsimp [act] at hact_w; rw [hst] at hact_w
                revert hact_w; generalize vl gs (x1 k s) w.val = vw; generalize inact p = ip
                revert vw ip; decide
              have hpBin : pidx ∈ BinIdx := Finset.mem_filter.mpr ⟨Finset.mem_univ pidx, by rw [hnot]; rfl⟩
              have hpT' : gateWire pidx ∈ T_wires := hpeq.symm ▸ hpT
              have h1 := hT_gate_inDeg_pos pidx hpT'
              have h2 := hBin_inDeg_le2 pidx hpBin
              rcases (by omega : inDegT (gateWire pidx) = 1 ∨ inDegT (gateWire pidx) = 2) with hd1 | hd2
              · have hpGat : pidx ∈ Gating := Finset.mem_filter.mpr ⟨hpBin, hpT', hd1⟩
                obtain ⟨a, haT, hbNotT, hea, _, heval⟩ := hbOf_spec pidx hpGat
                -- Since inDegT = 1 and both a and w are in T_wires with readEdge to gateWire pidx, a = w!
                have haw : a = w := by
                  have hcard1 : (T_wires.filter fun u => readEdge gs u (gateWire pidx)).card = 1 := hd1
                  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard1
                  have hmA : a ∈ T_wires.filter (fun u => readEdge gs u (gateWire pidx)) :=
                    Finset.mem_filter.mpr ⟨haT, hea⟩
                  have hmW : w ∈ T_wires.filter (fun u => readEdge gs u (gateWire pidx)) :=
                    Finset.mem_filter.mpr ⟨hwT, he'⟩
                  rw [hu, Finset.mem_singleton] at hmA hmW
                  exact hmA.trans hmW.symm
                subst haw
                have hbsame : vl gs (x1 k s) (bOf pidx).val = vl gs (x0 s) (bOf pidx).val :=
                  hS_indep (bOf pidx) hbNotT _ _ s
                by_cases hact_p : absOp pidx = inact p
                · -- Q_active! Use hall!
                  have hpQ : pidx ∈ Q_active := Finset.mem_filter.mpr ⟨hpGat, by rw [hpeq]; exact hact_p⟩
                  have hpass := hall pidx hpQ (by rw [hpeq]; exact hkp)
                  dsimp [passOf] at hpass
                  dsimp [act]
                  rw [← hpeq, heval (x1 k s), hpeq, hbsame, hvw_ne]
                  revert hact_p hpass
                  generalize absOp pidx = ab; generalize inact p = ip; generalize vl gs (x0 s) (bOf pidx).val = vb
                  revert ab ip vb; decide
                · -- Q_passive! absOp pidx != inact p, so it is OR in act-coords!
                  dsimp [act]
                  rw [← hpeq, heval (x1 k s), hpeq, hvw_ne]
                  revert hact_p
                  generalize absOp pidx = ab; generalize inact p = ip; generalize vl gs (x1 k s) (bOf pidx).val = vb
                  revert ab ip vb; decide
              · -- Merge gate! absOp pidx != inact p, so it is OR in act-coords!
                have hpMrg : pidx ∈ Merges := Finset.mem_filter.mpr ⟨hpBin, hpT', hd2⟩
                have habs_ne : absOp pidx ≠ inact p := hpeq ▸ hMerge_abs_ne pidx hpMrg
                obtain ⟨a1, a2, hne12, _, _, he1, he2, heval⟩ := hMerge_split pidx hpMrg
                have hw_eq : w = a1 ∨ w = a2 := by
                  have hcl_p := least.hcl pidx.val (gs.get pidx) hget
                  rcases hcl_p with ⟨hop, _⟩ | ⟨_, j, k', hj, hk', hinp⟩
                  · rw [hop] at hnot; exact Bool.noConfusion hnot
                  · have hm1 := (gate_read_inputs least.hcl pidx a1).mp he1
                    have hm2 := (gate_read_inputs least.hcl pidx a2).mp he2
                    have hmw := (gate_read_inputs least.hcl pidx w).mp he'
                    rw [hinp] at hm1 hm2 hmw
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1 hm2 hmw
                    have hne_val : a1.val ≠ a2.val := fun h => hne12 (Fin.ext h)
                    rcases hmw with hwj | hwk
                    · rcases hm1 with h1j | h1k
                      · exact Or.inl (Fin.ext (hwj.trans h1j.symm))
                      · rcases hm2 with h2j | h2k
                        · exact Or.inr (Fin.ext (hwj.trans h2j.symm))
                        · exact False.elim (hne_val (h1k.trans h2k.symm))
                    · rcases hm1 with h1j | h1k
                      · rcases hm2 with h2j | h2k
                        · exact False.elim (hne_val (h1j.trans h2j.symm))
                        · exact Or.inr (Fin.ext (hwk.trans h2k.symm))
                      · exact Or.inl (Fin.ext (hwk.trans h1k.symm))
                dsimp [act]
                rw [← hpeq, heval (x1 k s), hpeq]
                rcases hw_eq with rfl | rfl
                · rw [hvw_ne]
                  revert habs_ne
                  generalize absOp pidx = ab; generalize inact p = ip; generalize vl gs (x1 k s) a2.val = v2
                  revert ab ip v2; decide
                · rw [hvw_ne]
                  revert habs_ne
                  generalize absOp pidx = ab; generalize inact p = ip; generalize vl gs (x1 k s) a1.val = v1
                  revert ab ip v1; decide
            · -- NOT gate
              have hcl_p := least.hcl pidx.val (gs.get pidx) hget
              rcases hcl_p with ⟨hop, j, hj, hinp⟩ | ⟨hop | hop, _⟩
              · have hmw := (gate_read_inputs least.hcl pidx w).mp he'
                rw [hinp, List.mem_singleton] at hmw
                have hisNot : isNotWire p = true := by
                  simp only [isNotWire, hpgt, ↓reduceDIte]; exact hnot
                rw [hisNot, Bool.true_xor] at hst
                have hvp : vl gs (x1 k s) p.val = !(vl gs (x1 k s) w.val) := by
                  rw [← hpeq]; change vl gs (x1 k s) (10 + pidx.val) = _
                  rw [vl_gate gs least.hcl (x1 k s) pidx.val (gs.get pidx) hget, hinp, hop, hmw]; rfl
                dsimp [act] at hact_w ⊢
                rw [hvp]
                rw [hst] at hact_w
                revert hact_w; generalize vl gs (x1 k s) w.val = vw; generalize inact p = ip
                revert vw ip; decide
              · rw [hop] at hnot; exact Bool.noConfusion hnot
              · rw [hop] at hnot; exact Bool.noConfusion hnot
      have hact_leaf : act (inputWire gs (ι k)) (x1 k s) = true := by
        dsimp [act]
        rw [hinact_leaf k, Bool.xor_false]
        change vl gs (x1 k s) (ι k).val = true
        rw [vl_input gs (x1 k s) (ι k).val (ι k).isLt]
        dsimp only [x1]; rw [hcombI]
        simp
      have hact_out := hup (10 + gs.length) (inputWire gs (ι k)) (by omega)
        (hinI_T (ι k) (hι_mem k)) (by rw [hreachI_input (ι k) (hι_mem k)]; simp) hact_leaf
      dsimp [act] at hact_out
      rw [hx1_eval k s, hm, Bool.false_or, hinact_out, Bool.xor_false] at hact_out
      exact hact_out

  -- Partition Q_active into Q_priv (|reachI| = 1) and Q_shared (|reachI| >= 2)!
  let Q_priv : Finset (Fin gs.length) := Q_active.filter fun p => (reachI (gateWire p)).card = 1
  let Q_shared : Finset (Fin gs.length) := Q_active.filter fun p => 2 ≤ (reachI (gateWire p)).card
  have hQp_Qs : Q_priv.card + Q_shared.card = Q_active.card := by
    have hdisj : Disjoint Q_priv Q_shared := by
      rw [Finset.disjoint_left]; intro p h1 h2
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      omega
    have hunion : Q_priv ∪ Q_shared = Q_active := by
      ext p; simp only [Finset.mem_union, Q_priv, Q_shared, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hp
        have hpT : gateWire p ∈ T_wires := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
        have hpos : 1 ≤ (reachI (gateWire p)).card := Finset.card_pos.mpr (hreachI_nonempty _ hpT)
        rcases (by omega : (reachI (gateWire p)).card = 1 ∨ 2 ≤ (reachI (gateWire p)).card) with h | h
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr ⟨hp, h⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]

  let mode : Nat := PairSets.card
  have hmode_le_Qs : mode ≤ Q_shared.card := by
    have hsub : Q_active.filter (fun p => (reachI (gateWire p)).card = 2) ⊆ Q_shared := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, by have := (Finset.mem_filter.mp hp).2; omega⟩
    exact Finset.card_image_le.trans (Finset.card_le_card hsub)

  -- For each k : Fin 4, Q_priv_k = {p ∈ Q_priv | ι k ∈ reachI (gateWire p)}
  let Q_priv_k (k : Fin 4) : Finset (Fin gs.length) :=
    Q_priv.filter fun p => ι k ∈ reachI (gateWire p)

  -- Key reduction: on Active mode k s, A6 k s = true ↔ ∀ p ∈ Q_priv_k k, passOf p s = true!
  have hActive_equiv (k : Fin 4) (s : Fin 6 → Bool) (hact : Active mode k s) :
      A6 k s = true ↔ ∀ p ∈ Q_priv_k k, passOf p s = true := by
    obtain ⟨⟨hm, hnz⟩, hmode_cond⟩ := hact
    rw [hMaster_equiv k s hm]
    constructor
    · intro h p hp
      exact h p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1 (Finset.mem_filter.mp hp).2
    · intro h p hp hkp
      have hpT : gateWire p ∈ T_wires := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      have hpos : 1 ≤ (reachI (gateWire p)).card := Finset.card_pos.mpr (hreachI_nonempty _ hpT)
      by_cases hc1 : (reachI (gateWire p)).card = 1
      · exact h p (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp, hc1⟩, hkp⟩)
      · by_cases hc2 : (reachI (gateWire p)).card = 2
        · -- Then reachI (gateWire p) ∈ PairSets!
          have hPmem : reachI (gateWire p) ∈ PairSets :=
            Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp, hc2⟩)
          have hmode_pos : mode ≠ 0 := by
            intro h0; exact Finset.notMem_empty _ (Finset.card_eq_zero.mp h0 ▸ hPmem)
          have hpair_true : ∃ k' : Fin 4, ι k' ∈ reachI (gateWire p) ∧ A6 k' s = true := by
            by_cases h1 : mode = 1
            · have hPeq := (hPair_align _ hPmem).1 h1
              have hk01 : k = 0 ∨ k = 1 := by
                rw [hPeq, Finset.mem_insert, Finset.mem_singleton] at hkp
                rcases hkp with heq | heq
                · exact Or.inl (hι_inj heq)
                · exact Or.inr (hι_inj heq)
              rw [ite_eq_right hmode_pos, ite_eq_left h1] at hmode_cond
              rcases a6_pair_01 s hm hnz (hmode_cond hk01) with h0 | h1'
              · exact ⟨0, by rw [hPeq]; simp, h0⟩
              · exact ⟨1, by rw [hPeq]; simp, h1'⟩
            · have h2 : mode = 2 := by omega
              rw [ite_eq_right hmode_pos, ite_eq_right h1] at hmode_cond
              rcases (hPair_align _ hPmem).2 h2 with hPeq | hPeq
              · have hk01 : k = 0 ∨ k = 1 := by
                  rw [hPeq, Finset.mem_insert, Finset.mem_singleton] at hkp
                  rcases hkp with heq | heq
                  · exact Or.inl (hι_inj heq)
                  · exact Or.inr (hι_inj heq)
                rcases a6_pair_01 s hm hnz (hmode_cond.1 hk01) with h0 | h1'
                · exact ⟨0, by rw [hPeq]; simp, h0⟩
                · exact ⟨1, by rw [hPeq]; simp, h1'⟩
              · have hk23 : k = 2 ∨ k = 3 := by
                  rw [hPeq, Finset.mem_insert, Finset.mem_singleton] at hkp
                  rcases hkp with heq | heq
                  · exact Or.inl (hι_inj heq)
                  · exact Or.inr (hι_inj heq)
                rcases a6_pair_23 s hm hnz (hmode_cond.2 hk23) with h2' | h3'
                · exact ⟨2, by rw [hPeq]; simp, h2'⟩
                · exact ⟨3, by rw [hPeq]; simp, h3'⟩
          obtain ⟨k', hk'p, hAk'⟩ := hpair_true
          exact (hMaster_equiv k' s hm).mp hAk' p hp hk'p
        · -- |reachI| >= 3! Pick 3 distinct elements in reachI (gateWire p)!
          have hge3 : 3 ≤ (reachI (gateWire p)).card := by omega
          let R := reachI (gateWire p)
          change 3 ≤ R.card at hge3
          obtain ⟨v1, hv1⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
          obtain ⟨v2, hv2'⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hv1]; omega : 0 < (R.erase v1).card)
          have hv2 := Finset.mem_of_mem_erase hv2'
          have h12 : v1 ≠ v2 := (Finset.ne_of_mem_erase hv2').symm
          obtain ⟨v3, hv3''⟩ := Finset.card_pos.mp (by
            rw [Finset.card_erase_of_mem hv2', Finset.card_erase_of_mem hv1]; omega : 0 < ((R.erase v1).erase v2).card)
          have hv3' := Finset.mem_of_mem_erase hv3''
          have hv3 := Finset.mem_of_mem_erase hv3'
          have h13 : v1 ≠ v3 := (Finset.ne_of_mem_erase hv3').symm
          have h23 : v2 ≠ v3 := (Finset.ne_of_mem_erase hv3'').symm
          have hsubI : R ⊆ I := Finset.filter_subset _ _
          have hi1 := hsubI hv1; have hi2 := hsubI hv2; have hi3 := hsubI hv3
          rw [← hι_img] at hi1 hi2 hi3
          obtain ⟨k1, _, rfl⟩ := Finset.mem_image.mp hi1
          obtain ⟨k2, _, rfl⟩ := Finset.mem_image.mp hi2
          obtain ⟨k3, _, rfl⟩ := Finset.mem_image.mp hi3
          rcases a6_any_three k1 k2 k3 (fun h => h12 (congrArg ι h))
              (fun h => h13 (congrArg ι h)) (fun h => h23 (congrArg ι h)) s hm hnz with h1 | h2 | h3
          · exact (hMaster_equiv k1 s hm).mp h1 p hp hv1
          · exact (hMaster_equiv k2 s hm).mp h2 p hp hv2
          · exact (hMaster_equiv k3 s hm).mp h3 p hp hv3

  -- Each Q_priv_k k is nonempty, and pairwise disjoint, summing to Q_priv.card!
  have hQpk_ne (k : Fin 4) : (Q_priv_k k).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨m, hma, hmf⟩ := target_takes_false mode hPair_le2 k false
    have hact := active_of_activeM mode k m hma
    have htrue : A6 k (maskToFn m) = true := (hActive_equiv k (maskToFn m) hact).mpr (by simp [hemp])
    rw [htrue] at hmf
    exact Bool.noConfusion hmf

  have hQpk_sum : (Q_priv_k 0).card + (Q_priv_k 1).card + (Q_priv_k 2).card + (Q_priv_k 3).card = Q_priv.card := by
    have hdisj (a b : Fin 4) (hab : a ≠ b) : Disjoint (Q_priv_k a) (Q_priv_k b) := by
      rw [Finset.disjoint_left]; intro p ha hb
      have hc1 : (reachI (gateWire p)).card = 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc1
      have e1 : ι a = u := by simpa [hu] using (Finset.mem_filter.mp ha).2
      have e2 : ι b = u := by simpa [hu] using (Finset.mem_filter.mp hb).2
      exact hab (hι_inj (e1.trans e2.symm))
    have hunion : Q_priv_k 0 ∪ Q_priv_k 1 ∪ Q_priv_k 2 ∪ Q_priv_k 3 = Q_priv := by
      ext p
      simp only [Finset.mem_union, Q_priv_k, Finset.mem_filter]
      constructor
      · rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro hp
        have hpT : gateWire p ∈ T_wires :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2.1
        obtain ⟨v, hv⟩ := hreachI_nonempty _ hpT
        have hvI : v ∈ I := (Finset.mem_filter.mp hv).1
        rw [← hι_img] at hvI
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hvI
        fin_cases k
        · exact Or.inl (Or.inl (Or.inl ⟨hp, hv⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hp, hv⟩))
        · exact Or.inl (Or.inr ⟨hp, hv⟩)
        · exact Or.inr ⟨hp, hv⟩
    rw [← hunion,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
        ⟨hdisj 0 3 (by decide), hdisj 1 3 (by decide)⟩, hdisj 2 3 (by decide)⟩),
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
        ⟨hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩),
      Finset.card_union_of_disjoint (hdisj 0 1 (by decide))]

  -- Now build the U2Gate circuit gs_S for all gates in GS!
  -- Sort GS as an increasing list gsList : List (Fin gs.length)
  let gsList : List (Fin gs.length) := GS.sort (· ≤ ·)
  have hgsList_len : gsList.length = GS.card := Finset.length_sort _
  have hgsList_nd : gsList.Nodup := Finset.sort_nodup _ _
  have hgsList_sorted : gsList.Pairwise (· < ·) := by
    have hle := Finset.pairwise_sort GS (· ≤ ·)
    exact (List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
      have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
      have hne : gsList[i] ≠ gsList[j] := fun h => by
        have heq := (List.Nodup.getElem_inj_iff hgsList_nd).mp h
        omega
      exact lt_of_le_of_ne h1 hne)
  have hgsList_mem (p : Fin gs.length) : p ∈ gsList ↔ p ∈ GS := Finset.mem_sort _

  -- Position of p ∈ GS in gsList: posOf p = gsList.idxOf p
  have hpos_lt (p : Fin gs.length) (hp : p ∈ GS) : gsList.idxOf p < gsList.length :=
    List.idxOf_lt_length_iff.mpr ((hgsList_mem p).mpr hp)
  have hpos_mono (p q : Fin gs.length) (hp : p ∈ GS) (hq : q ∈ GS) (hlt : p < q) :
      gsList.idxOf p < gsList.idxOf q := by
    by_contra hge
    have hle : gsList.idxOf q ≤ gsList.idxOf p := by omega
    by_cases heq : gsList.idxOf q = gsList.idxOf p
    · have : q = p := by
        have e1 := List.getElem_idxOf (hpos_lt q hq)
        have e2 := List.getElem_idxOf (hpos_lt p hp)
        rw [← e1, ← e2]; simp [heq]
      exact ne_of_lt hlt this.symm
    · have hlt' : gsList.idxOf q < gsList.idxOf p := lt_of_le_of_ne hle heq
      have hqp := List.pairwise_iff_getElem.mp hgsList_sorted (gsList.idxOf q) (gsList.idxOf p)
        (hpos_lt q hq) (hpos_lt p hp) hlt'
      rw [List.getElem_idxOf (hpos_lt q hq), List.getElem_idxOf (hpos_lt p hp)] at hqp
      exact not_lt_of_gt hlt hqp

  -- For every wire w ∉ T_wires, compute (baseW w, baseP w) by recursion on w.val!
  let sigmaIdx (v : V10) : Nat :=
    match (List.finRange 6).find? (fun j => σ j == v) with
    | some j => j.val
    | none => 0
  have hsigmaIdx_lt (v : V10) : sigmaIdx v < 6 := by
    dsimp only [sigmaIdx]
    cases hf : (List.finRange 6).find? (fun j => σ j == v) with
    | none => decide
    | some j => exact j.isLt
  have hsigmaIdx_spec (v : V10) (hv : v ∉ I) :
      sigmaIdx v < 6 ∧ σ ⟨sigmaIdx v, hsigmaIdx_lt v⟩ = v := by
    refine ⟨hsigmaIdx_lt v, ?_⟩
    rcases hcover v with ⟨k, rfl⟩ | ⟨j, rfl⟩
    · exact False.elim (hv (hι_mem k))
    · have hf_some : ∃ j', (List.finRange 6).find? (fun j'' => σ j'' == σ j) = some j' := by
        cases hf : (List.finRange 6).find? (fun j'' => σ j'' == σ j) with
        | none =>
          have := List.find?_eq_none.mp hf j (List.mem_finRange j); simp at this
        | some j' => exact ⟨j', rfl⟩
      obtain ⟨j', hf⟩ := hf_some
      have hs := List.find?_some hf; simp only [beq_iff_eq] at hs
      have hidx : (⟨sigmaIdx (σ j), hsigmaIdx_lt (σ j)⟩ : Fin 6) = j' := by
        ext; dsimp only [sigmaIdx]; rw [hf]
      rw [hidx, hs]

  let baseOf (w : W) : Nat × Bool := baseOfAux gs sigmaIdx (fun p => gsList.idxOf p) (10 + gs.length) w

  have hbaseOf_input (w : W) (hlt : w.val < 10) : baseOf w = (sigmaIdx ⟨w.val, hlt⟩, false) := by
    have h := baseOfAux_irrel gs sigmaIdx (fun p => gsList.idxOf p) (10 + gs.length) (10 + gs.length + 1) w (by omega) (by omega)
    dsimp only [baseOf]; rw [h]; unfold baseOfAux; simp [hlt]

  have hbaseOf_not (p : Fin gs.length) (j : Nat) (hj : j < 10 + p.val)
      (hop : (gs.get p).op = GateOp.not) (hinp : (gs.get p).inputs = [j]) :
      let r := baseOf ⟨j, by omega⟩
      baseOf (gateWire p) = (r.1, !r.2) := by
    have h := baseOfAux_irrel gs sigmaIdx (fun p => gsList.idxOf p) (10 + gs.length) (10 + gs.length + 1) (gateWire p) (by omega) (by omega)
    dsimp only [baseOf]; rw [h]; conv_lhs => unfold baseOfAux
    have hge10 : ¬ (gateWire p).val < 10 := by dsimp [gateWire]; omega
    have hpeq : (⟨(gateWire p).val - 10, by omega⟩ : Fin gs.length) = p := Fin.ext (by dsimp [gateWire]; omega)
    simp only [hge10, ↓reduceDIte, hpeq, hop, isNotGate, ↓reduceIte, hinp, List.headD_cons]
    have hj' : j < (gateWire p).val := hj
    simp only [hj', ↓reduceDIte]

  have hbaseOf_bin (p : Fin gs.length) (hbn : isNotGate (gs.get p).op = false) :
      baseOf (gateWire p) = (6 + gsList.idxOf p, false) := by
    have h := baseOfAux_irrel gs sigmaIdx (fun p => gsList.idxOf p) (10 + gs.length) (10 + gs.length + 1) (gateWire p) (by omega) (by omega)
    dsimp only [baseOf]; rw [h]; unfold baseOfAux
    have hge10 : ¬ (gateWire p).val < 10 := by dsimp [gateWire]; omega
    have hpeq : (⟨(gateWire p).val - 10, by omega⟩ : Fin gs.length) = p := Fin.ext (by dsimp [gateWire]; omega)
    simp only [hge10, ↓reduceDIte, hpeq, hbn, Bool.false_eq_true, ↓reduceIte]

  -- Bound on (baseOf w).1 for w ∉ T_wires:
  have hbaseOf_lt_all : ∀ n : Nat, ∀ w : W, w.val ≤ n → w ∉ T_wires →
      (baseOf w).1 < 6 + gsList.length ∧
      (∀ p : Fin gs.length, p ∈ GS → w.val < 10 + p.val → (baseOf w).1 < 6 + gsList.idxOf p) := by
    intro n
    induction n with
    | zero =>
      intro w hwn hwNot
      have hlt : w.val < 10 := by omega
      rw [hbaseOf_input w hlt]
      have hvNotI : (⟨w.val, hlt⟩ : V10) ∉ I := fun hI => hwNot (by
        have : inputWire gs ⟨w.val, hlt⟩ = w := Fin.ext rfl
        rw [← this]; exact hinI_T _ hI)
      have hsig := (hsigmaIdx_spec ⟨w.val, hlt⟩ hvNotI).1
      exact ⟨by omega, fun p _ _ => by omega⟩
    | succ n ih =>
      intro w hwn hwNot
      by_cases hlt : w.val < 10
      · rw [hbaseOf_input w hlt]
        have hvNotI : (⟨w.val, hlt⟩ : V10) ∉ I := fun hI => hwNot (by
          have : inputWire gs ⟨w.val, hlt⟩ = w := Fin.ext rfl
          rw [← this]; exact hinI_T _ hI)
        have hsig := (hsigmaIdx_spec ⟨w.val, hlt⟩ hvNotI).1
        exact ⟨by omega, fun p _ _ => by omega⟩
      · let q : Fin gs.length := ⟨w.val - 10, by have := w.isLt; omega⟩
        have hweq : gateWire q = w := Fin.ext (by dsimp [gateWire, q]; omega)
        have hqv : 10 + q.val = w.val := congrArg Fin.val hweq
        have hget : gs[q.val]? = some (gs.get q) := by
          rw [List.getElem?_eq_getElem q.isLt, List.get_eq_getElem]
        have hcl_q := least.hcl q.val (gs.get q) hget
        rcases hcl_q with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
        · rw [← hweq, hbaseOf_not q j hj hop hinp]
          let u : W := ⟨j, by omega⟩
          have heu : readEdge gs u w := by
            rw [← hweq]; exact (gate_read_inputs least.hcl q u).mpr (by rw [hinp]; simp [u])
          have huNot : u ∉ T_wires := fun huT => hwNot (hT_closed u w huT heu)
          have hIH := ih u (by dsimp [u]; omega) huNot
          exact ⟨hIH.1, fun p hp hltp => hIH.2 p hp (by dsimp [u, gateWire] at hltp ⊢; omega)⟩
        · have hbn : isNotGate (gs.get q).op = false := by rcases hop with h | h <;> (rw [h]; rfl)
          rw [← hweq, hbaseOf_bin q hbn]
          have hqGS : q ∈ GS := Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ q, by rw [hbn]; rfl⟩, hweq.symm ▸ hwNot⟩
          refine ⟨by have := hpos_lt q hqGS; omega, fun p hp hltp => ?_⟩
          have hqp : q < p := by dsimp [gateWire] at hltp; change q.val < p.val; omega
          have := hpos_mono q p hqGS hp hqp
          omega

  -- Build gs_S : List U2Gate by mapping gsList!
  let mkU2Gate (p : Fin gs.length) : U2Gate :=
    let j := (gs.get p).inputs.getD 0 0
    let k := (gs.get p).inputs.getD 1 0
    let r1 := if hj : j < 10 + gs.length then baseOf ⟨j, hj⟩ else (0, false)
    let r2 := if hk : k < 10 + gs.length then baseOf ⟨k, hk⟩ else (0, false)
    ⟨absOp p, r1.1, r1.2, r2.1, r2.2⟩

  let gs_S : List U2Gate := gsList.map mkU2Gate
  have hgs_S_len : gs_S.length = GS.card := by simp [gs_S, hgsList_len]

  have hgs_S_valid : ValidU2 gs_S := by
    intro idx
    have hidx : idx.val < gsList.length := by simpa [gs_S] using idx.isLt
    let p := gsList[idx.val]'hidx
    have hpGS : p ∈ GS := (hgsList_mem p).mp (List.getElem_mem hidx)
    have hpos_eq : gsList.idxOf p = idx.val := by
      have he : gsList[gsList.idxOf p]'(hpos_lt p hpGS) = gsList[idx.val]'hidx :=
        List.getElem_idxOf (hpos_lt p hpGS)
      exact (List.Nodup.getElem_inj_iff hgsList_nd).mp he
    have hget : gs[p.val]? = some (gs.get p) := by
      rw [List.getElem?_eq_getElem p.isLt, List.get_eq_getElem]
    have hpBin : p ∈ BinIdx := (Finset.mem_filter.mp hpGS).1
    have hpNotT : gateWire p ∉ T_wires := (Finset.mem_filter.mp hpGS).2
    obtain ⟨u1, u2, _, hinp, _, he1, he2⟩ := hBin_two_inputs p hpBin
    have hu1Not : u1 ∉ T_wires := fun h => hpNotT (hT_closed u1 (gateWire p) h he1)
    have hu2Not : u2 ∉ T_wires := fun h => hpNotT (hT_closed u2 (gateWire p) h he2)
    have hlt1 : u1.val < 10 + p.val := read_order least.hcl he1
    have hlt2 : u2.val < 10 + p.val := read_order least.hcl he2
    have hb1 := (hbaseOf_lt_all u1.val u1 le_rfl hu1Not).2 p hpGS hlt1
    have hb2 := (hbaseOf_lt_all u2.val u2 le_rfl hu2Not).2 p hpGS hlt2
    rw [hpos_eq] at hb1 hb2
    have hgetS : gs_S.get idx = mkU2Gate p := by
      simp [gs_S, p, List.get_eq_getElem]
    rw [hgetS]
    dsimp only [mkU2Gate]
    rw [hinp]
    simp only [List.getD_cons_zero, List.getD_cons_succ, u1.isLt, u2.isLt, ↓reduceDIte]
    exact ⟨hb1, hb2⟩

  -- Semantics of gs_S: for EVERY w ∉ T_wires and EVERY s : Fin 6 → Bool:
  --   Bool.xor (wireU2 gs_S (baseOf w).1 s) (baseOf w).2 = vl gs (x0 s) w.val !
  have hgs_S_eval : ∀ n : Nat, ∀ w : W, w.val ≤ n → w ∉ T_wires → ∀ s : Fin 6 → Bool,
      Bool.xor (wireU2 gs_S (baseOf w).1 s) (baseOf w).2 = vl gs (x0 s) w.val := by
    intro n
    induction n with
    | zero =>
      intro w hwn hwNot s
      have hlt : w.val < 10 := by omega
      rw [hbaseOf_input w hlt]
      have hvNotI : (⟨w.val, hlt⟩ : V10) ∉ I := fun hI => hwNot (by
        have : inputWire gs ⟨w.val, hlt⟩ = w := Fin.ext rfl
        rw [← this]; exact hinI_T _ hI)
      have hsig := hsigmaIdx_spec ⟨w.val, hlt⟩ hvNotI
      dsimp
      rw [Bool.xor_false, wireU2_input gs_S ⟨sigmaIdx ⟨w.val, hlt⟩, hsig.1⟩ s,
        vl_input gs (x0 s) w.val hlt]
      have hwv : x0 s ⟨w.val, hlt⟩ = s ⟨sigmaIdx ⟨w.val, hlt⟩, hsig.1⟩ := by
        conv_lhs => rw [← hsig.2]
        dsimp only [x0]; rw [hcombS]
      exact hwv.symm
    | succ n ih =>
      intro w hwn hwNot s
      by_cases hlt : w.val < 10
      · rw [hbaseOf_input w hlt]
        have hvNotI : (⟨w.val, hlt⟩ : V10) ∉ I := fun hI => hwNot (by
          have : inputWire gs ⟨w.val, hlt⟩ = w := Fin.ext rfl
          rw [← this]; exact hinI_T _ hI)
        have hsig := hsigmaIdx_spec ⟨w.val, hlt⟩ hvNotI
        dsimp
        rw [Bool.xor_false, wireU2_input gs_S ⟨sigmaIdx ⟨w.val, hlt⟩, hsig.1⟩ s,
          vl_input gs (x0 s) w.val hlt]
        have hwv : x0 s ⟨w.val, hlt⟩ = s ⟨sigmaIdx ⟨w.val, hlt⟩, hsig.1⟩ := by
          conv_lhs => rw [← hsig.2]
          dsimp only [x0]; rw [hcombS]
        exact hwv.symm
      · let q : Fin gs.length := ⟨w.val - 10, by have := w.isLt; omega⟩
        have hweq : gateWire q = w := Fin.ext (by dsimp [gateWire, q]; omega)
        have hqv : 10 + q.val = w.val := congrArg Fin.val hweq
        have hget : gs[q.val]? = some (gs.get q) := by
          rw [List.getElem?_eq_getElem q.isLt, List.get_eq_getElem]
        have hcl_q := least.hcl q.val (gs.get q) hget
        rcases hcl_q with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
        · rw [← hweq, hbaseOf_not q j hj hop hinp]
          let u : W := ⟨j, by omega⟩
          have heu : readEdge gs u w := by
            rw [← hweq]; exact (gate_read_inputs least.hcl q u).mpr (by rw [hinp]; simp [u])
          have huNot : u ∉ T_wires := fun huT => hwNot (hT_closed u w huT heu)
          have hIH := ih u (by dsimp [u]; omega) huNot s
          have hvw : vl gs (x0 s) (gateWire q).val = !(vl gs (x0 s) u.val) := by
            change vl gs (x0 s) (10 + q.val) = _
            rw [vl_gate gs least.hcl (x0 s) q.val (gs.get q) hget, hinp, hop]; rfl
          rw [hvw, ← hIH]
          cases wireU2 gs_S (baseOf u).1 s <;> cases (baseOf u).2 <;> rfl
        · have hbn : isNotGate (gs.get q).op = false := by rcases hop with h | h <;> (rw [h]; rfl)
          rw [← hweq, hbaseOf_bin q hbn]
          have hqGS : q ∈ GS := Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ q, by rw [hbn]; rfl⟩, hweq.symm ▸ hwNot⟩
          let idx : Fin gs_S.length := ⟨gsList.idxOf q, by simp [gs_S]; exact hpos_lt q hqGS⟩
          have hgetS : gs_S.get idx = mkU2Gate q := by
            simp only [gs_S, idx, List.get_eq_getElem, List.getElem_map]
            rw [List.getElem_idxOf (hpos_lt q hqGS)]
          let u1 : W := ⟨j, by omega⟩
          let u2 : W := ⟨k, by omega⟩
          have he1 : readEdge gs u1 w := by
            rw [← hweq]; exact (gate_read_inputs least.hcl q u1).mpr (by rw [hinp]; simp [u1])
          have he2 : readEdge gs u2 w := by
            rw [← hweq]; exact (gate_read_inputs least.hcl q u2).mpr (by rw [hinp]; simp [u2])
          have hu1Not : u1 ∉ T_wires := fun h => hwNot (hT_closed u1 w h he1)
          have hu2Not : u2 ∉ T_wires := fun h => hwNot (hT_closed u2 w h he2)
          have hIH1 := ih u1 (by dsimp [u1]; omega) hu1Not s
          have hIH2 := ih u2 (by dsimp [u2]; omega) hu2Not s
          dsimp
          rw [Bool.xor_false]
          have hwg := wireU2_gate gs_S hgs_S_valid idx s
          dsimp only [idx] at hwg
          rw [hwg, hgetS]
          dsimp only [mkU2Gate]
          rw [hinp]
          have hjlt : j < 10 + gs.length := u1.isLt
          have hklt : k < 10 + gs.length := u2.isLt
          simp only [List.getD_cons_zero, List.getD_cons_succ, hjlt, hklt, ↓reduceDIte]
          change (if absOp q then
              (Bool.xor (wireU2 gs_S (baseOf u1).1 s) (baseOf u1).2 ||
               Bool.xor (wireU2 gs_S (baseOf u2).1 s) (baseOf u2).2)
            else
              (Bool.xor (wireU2 gs_S (baseOf u1).1 s) (baseOf u1).2 &&
               Bool.xor (wireU2 gs_S (baseOf u2).1 s) (baseOf u2).2)) = vl gs (x0 s) (gateWire q).val
          rw [hIH1, hIH2]
          change _ = vl gs (x0 s) (10 + q.val)
          rw [vl_gate gs least.hcl (x0 s) q.val (gs.get q) hget, hinp]
          rcases hop with hop | hop
          · simp only [absOp, hop, List.map_cons, List.map_nil, u1, u2]
            generalize vl gs (x0 s) j = b1; generalize vl gs (x0 s) k = b2
            cases b1 <;> cases b2 <;> rfl
          · simp only [absOp, hop, List.map_cons, List.map_nil, u1, u2]
            generalize vl gs (x0 s) j = b1; generalize vl gs (x0 s) k = b2
            cases b1 <;> cases b2 <;> rfl

  -- Now fold each leaf k ∈ Fin 4's private Q_active gates onto gs_S!
  let pairFor (p : Fin gs.length) : Nat × Bool :=
    ((baseOf (bOf p)).1, Bool.xor (baseOf (bOf p)).2 (absOp p))

  have hpairFor_spec (p : Fin gs.length) (hp : p ∈ Q_active) :
      (pairFor p).1 < 6 + gs_S.length ∧
      ∀ s : Fin 6 → Bool, Bool.xor (wireU2 gs_S (pairFor p).1 s) (pairFor p).2 = passOf p s := by
    have hpGat : p ∈ Gating := (Finset.mem_filter.mp hp).1
    obtain ⟨_, _, hbNotT, _, _, _⟩ := hbOf_spec p hpGat
    have hlt := (hbaseOf_lt_all (bOf p).val (bOf p) le_rfl hbNotT).1
    refine ⟨by rw [hgs_S_len, ← hgsList_len]; exact hlt, fun s => ?_⟩
    have hev := hgs_S_eval (bOf p).val (bOf p) le_rfl hbNotT s
    dsimp [pairFor, passOf]
    rw [← hev]
    cases wireU2 gs_S (baseOf (bOf p)).1 s <;> cases (baseOf (bOf p)).2 <;> cases absOp p <;> rfl

  let L (k : Fin 4) : List (Nat × Bool) := (Q_priv_k k).toList.map pairFor
  have hL_len (k : Fin 4) : (L k).length = (Q_priv_k k).card := by simp [L]
  have hL_ne (k : Fin 4) : L k ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    rw [hL_len, List.length_nil] at hlen
    have := Finset.card_pos.mpr (hQpk_ne k)
    omega
  have hL_bound (k : Fin 4) (x : Nat × Bool) (hx : x ∈ L k) : x.1 < 6 + gs_S.length := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hpQ : p ∈ Q_active := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).1).1
    exact (hpairFor_spec p hpQ).1
  have hL_all (k : Fin 4) (s : Fin 6 → Bool) (hact : Active mode k s) :
      (L k).all (fun x => Bool.xor (wireU2 gs_S x.1 s) x.2) = A6 k s := by
    rw [Bool.eq_iff_iff, List.all_eq_true, hActive_equiv k s hact]
    constructor
    · intro h p hp
      have hmem : pairFor p ∈ L k := List.mem_map.mpr ⟨p, Finset.mem_toList.mpr hp, rfl⟩
      have hpQ : p ∈ Q_active := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      rw [← (hpairFor_spec p hpQ).2 s]
      exact h (pairFor p) hmem
    · intro h x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have hp' := Finset.mem_toList.mp hp
      have hpQ : p ∈ Q_active := (Finset.mem_filter.mp (Finset.mem_filter.mp hp').1).1
      rw [(hpairFor_spec p hpQ).2 s]
      exact h p hp'

  -- Chain foldAndList across k = 0, 1, 2, 3!
  let r0 := foldAndList gs_S (L 0)
  have hr0 := foldAndList_spec gs_S (L 0) (hL_ne 0) hgs_S_valid (hL_bound 0)
  obtain ⟨hv0, hlen0, ⟨ext0, hext0⟩, hlt0, hev0⟩ := hr0
  change r0.1.length = gs_S.length + ((L 0).length - 1) at hlen0
  change r0.2.1 < 6 + r0.1.length at hlt0

  let r1 := foldAndList r0.1 (L 1)
  have hr1 := foldAndList_spec r0.1 (L 1) (hL_ne 1) hv0 (fun x hx => by have := hL_bound 1 x hx; omega)
  obtain ⟨hv1, hlen1, ⟨ext1, hext1⟩, hlt1, hev1⟩ := hr1
  change r1.1.length = r0.1.length + ((L 1).length - 1) at hlen1
  change r1.2.1 < 6 + r1.1.length at hlt1

  let r2 := foldAndList r1.1 (L 2)
  have hr2 := foldAndList_spec r1.1 (L 2) (hL_ne 2) hv1 (fun x hx => by have := hL_bound 2 x hx; omega)
  obtain ⟨hv2, hlen2, ⟨ext2, hext2⟩, hlt2, hev2⟩ := hr2
  change r2.1.length = r1.1.length + ((L 2).length - 1) at hlen2
  change r2.2.1 < 6 + r2.1.length at hlt2

  let r3 := foldAndList r2.1 (L 3)
  have hr3 := foldAndList_spec r2.1 (L 3) (hL_ne 3) hv2 (fun x hx => by have := hL_bound 3 x hx; omega)
  obtain ⟨hv3, hlen3, ⟨ext3, hext3⟩, hlt3, hev3⟩ := hr3
  change r3.1.length = r2.1.length + ((L 3).length - 1) at hlen3
  change r3.2.1 < 6 + r3.1.length at hlt3

  -- Total length <= 7 - mode!
  have hlen_final : r3.1.length ≤ 7 - mode := by
    have h0 := Finset.card_pos.mpr (hQpk_ne 0)
    have h1 := Finset.card_pos.mpr (hQpk_ne 1)
    have h2 := Finset.card_pos.mpr (hQpk_ne 2)
    have h3 := Finset.card_pos.mpr (hQpk_ne 3)
    rw [hlen3, hlen2, hlen1, hlen0, hgs_S_len, hL_len 0, hL_len 1, hL_len 2, hL_len 3]
    omega

  let outW : Fin 4 → Nat := ![r0.2.1, r1.2.1, r2.2.1, r3.2.1]
  let outP : Fin 4 → Bool := ![r0.2.2, r1.2.2, r2.2.2, r3.2.2]

  have hout_lt : ∀ k : Fin 4, outW k < 6 + r3.1.length := by
    intro k; fin_cases k <;> dsimp [outW] <;> omega

  have hcomp : ∀ k : Fin 4, ComputesTarget r3.1 mode k (outW k) (outP k) := by
    intro k s hact
    have hL_eq (m : Fin 4) (hactm : Active mode m s) (gsB : List U2Gate) (extB : List U2Gate) (heqB : gsB = gs_S ++ extB) :
        (L m).all (fun x => Bool.xor (wireU2 gsB x.1 s) x.2) = A6 m s := by
      rw [← hL_all m s hactm]
      have hgo : ∀ l : List (Nat × Bool), (∀ x ∈ l, x.1 < 6 + gs_S.length) →
          l.all (fun x => Bool.xor (wireU2 gsB x.1 s) x.2) =
          l.all (fun x => Bool.xor (wireU2 gs_S x.1 s) x.2) := by
        intro l hl
        induction l with
        | nil => rfl
        | cons z zs ihz =>
          rw [List.all_cons, List.all_cons, ihz (fun x hx => hl x (List.mem_cons_of_mem _ hx)),
            heqB, wireU2_append_lt gs_S extB z.1 (hl z List.mem_cons_self) s]
      exact hgo (L m) (hL_bound m)
    fin_cases k
    · dsimp [outW, outP]
      have hfull : r3.1 = r0.1 ++ (ext1 ++ ext2 ++ ext3) := by
        rw [hext3, hext2, hext1]; simp [List.append_assoc]
      rw [hfull, wireU2_append_lt r0.1 _ r0.2.1 hlt0 s, hev0 s, hL_all 0 s hact]
    · dsimp [outW, outP]
      have hfull : r3.1 = r1.1 ++ (ext2 ++ ext3) := by
        rw [hext3, hext2]; simp [List.append_assoc]
      rw [hfull, wireU2_append_lt r1.1 _ r1.2.1 hlt1 s, hev1 s, hL_eq 1 hact r0.1 ext0 hext0]
    · dsimp [outW, outP]
      rw [hext3, wireU2_append_lt r2.1 ext3 r2.2.1 hlt2 s, hev2 s,
        hL_eq 2 hact r1.1 (ext0 ++ ext1) (by rw [hext1, hext0, List.append_assoc])]
    · dsimp [outW, outP]
      rw [hev3 s,
        hL_eq 3 hact r2.1 (ext0 ++ ext1 ++ ext2) (by rw [hext2, hext1, hext0]; simp [List.append_assoc])]

  exact NoSevenU2.no_u2_circuit mode hPair_le2 r3.1 hv3 hlen_final outW outP hout_lt hcomp

theorem p10_ge_sixteen_bin :
    ∀ (x1 : Circuit), FanInTwo x1 →
      List.countP (fun x3 : Gate => !x3.op.eval [Bool.false]) x1.gates ≤ 15 →
      ∃ x4 : Fin 10 → Bool, x1.eval (List.ofFn x4) ≠ p10F x4 := by
  intro C hfan hle
  by_contra hall
  push Not at hall
  obtain ⟨gs, o, least, hcost⟩ := least_with_budget C hfan hall p10_nonconstant
  have hcount_eq : nonNotCount C.gates = List.countP (fun x3 : Gate => !x3.op.eval [Bool.false]) C.gates := by
    unfold nonNotCount
    apply List.countP_congr
    intro g hg
    rcases (hfan g hg).1 with h | h | h <;> rw [h] <;> rfl
  have h15_ge : 15 ≤ nonNotCount gs := (p10_six_branches_and_structure least).2.1
  have h15_le : nonNotCount gs ≤ 15 := hcost.trans (hcount_eq ▸ hle)
  exact p10_not_fifteen_bin least (by omega)

end TreeExtract
