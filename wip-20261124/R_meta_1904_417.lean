import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.FactorSubst

-- Reduce L-meta-1904 from general Monotone2 circuits on girth-5 graphs to three clean
-- IsLeastAO + TopForm subgoals, proving directly:
--   1. The empty-graph case (zero-gate circuit).
--   2. Exact equivalence between least Monotone2 circuits and IsLeastAO circuits on nonempty graphs.
--   3. The FactorSubst obstruction: for any dirty AND gate c of a least IsAO2 circuit and any
--      per-reader operand substitution sigma, substReads C n c sigma must leak on some non-edge input.
-- The three children are:
--   (1) TopForm normalization preserving IsLeastAO without increasing junk count.
--   (2) Single dirty AND gate elimination (junk = {g}) in TopForm with the FactorSubst obstruction.
--   (3) Multi-dirty AND gate reduction (2 <= junk.card) in TopForm with the FactorSubst obstruction.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1904_417
    (topForm_norm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C →
      ∃ C' : Circuit, IsLeastAO G C' ∧ (junk G C').card ≤ (junk G C).card ∧ TopForm G C')
    (elim_one_junk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ),
      (∀ u v w : Fin n, G.Adj u v → G.Adj v w → ¬ G.Adj w u) →
      NoFourCycle G → G.edgeFinset.Nonempty →
      IsLeastAO G C → TopForm G C → junk G C = {g} →
      (∀ sigma : ℕ → ℕ, (∀ r : ℕ, sigma r = opnd C g 0 ∨ sigma r = opnd C g 1) →
        ∃ x : Fin n → Bool, (substReads C n g sigma).eval (List.ofFn x) = true ∧ graphFun G ∅ x = false) →
      ∃ C' : Circuit, IsLeastAO G C' ∧ junk G C' = ∅)
    (reduce_multi_junk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ u v w : Fin n, G.Adj u v → G.Adj v w → ¬ G.Adj w u) →
      NoFourCycle G → G.edgeFinset.Nonempty →
      IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      (∀ c ∈ junk G C, ∀ sigma : ℕ → ℕ, (∀ r : ℕ, sigma r = opnd C c 0 ∨ sigma r = opnd C c 1) →
        ∃ x : Fin n → Bool, (substReads C n c sigma).eval (List.ofFn x) = true ∧ graphFun G ∅ x = false) →
      ∃ C' : Circuit, IsLeastAO G C' ∧ (junk G C').card < (junk G C).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x1 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x6.size ≤ x7.size) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  intro n G _ htri hc4
  -- Basic GateOp.eval identities without simp [GateOp.eval]
  have eval_and0 : GateOp.and.eval [] = true := rfl
  have eval_or0 : GateOp.or.eval [] = false := rfl
  have eval_and1 : ∀ b : Bool, GateOp.and.eval [b] = b := fun b => by cases b <;> rfl
  have eval_or1 : ∀ b : Bool, GateOp.or.eval [b] = b := fun b => by cases b <;> rfl
  have eval_and2 : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) :=
    fun b1 b2 => by cases b1 <;> cases b2 <;> rfl
  have eval_or2 : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) :=
    fun b1 b2 => by cases b1 <;> cases b2 <;> rfl
  -- General foldl wire evaluation lemmas
  let wstep : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have wfold_len : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (wstep xs g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [ih (wstep xs g) r hr']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have wireVal_input : ∀ (D : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < n),
      wireVal n D r x = x ⟨r, hr⟩ := by
    intro D x r hr
    have hlt : r < (List.ofFn x).length := by rw [List.length_ofFn]; exact hr
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt D.gates (List.ofFn x) r hlt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wireVal_ge : ∀ (D : Circuit) (x : Fin n → Bool) (r : ℕ),
      n + D.gates.length ≤ r → wireVal n D r x = false := by
    intro D x r hr
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = false
    apply List.getD_eq_default
    rw [wfold_len, List.length_ofFn]; exact hr
  have wireVal_gate_gen : ∀ (D : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < D.gates.length),
      wireVal n D (n + k) x =
        D.gates[k].op.eval (D.gates[k].inputs.map fun i =>
          if i < n + k then wireVal n D i x else false) := by
    intro D x k hk
    let g := D.gates[k]
    have hsplit : D.gates = D.gates.take k ++ g :: D.gates.drop (k + 1) := by
      dsimp only [g]
      rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
    let pref := (D.gates.take k).foldl wstep (List.ofFn x)
    have hpref_len : pref.length = n + k := by
      dsimp only [pref]
      rw [wfold_len, List.length_ofFn, List.length_take]; omega
    have hwires_eq : D.wires (List.ofFn x) =
        (D.gates.drop (k + 1)).foldl wstep (wstep pref g) := by
      change D.gates.foldl wstep (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ i : ℕ, pref.getD i false = if i < n + k then wireVal n D i x else false := by
      intro i
      by_cases hi : i < n + k
      · rw [if_pos hi]
        change pref.getD i false = (D.wires (List.ofFn x)).getD i false
        rw [hwires_eq]
        have hi1 : i < (wstep pref g).length := by
          simp only [wstep, List.length_append, List.length_singleton]; omega
        rw [wfold_getD_lt _ _ i hi1]
        have hi0 : i < pref.length := by omega
        simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
      · rw [if_neg hi]
        exact List.getD_eq_default _ _ (by omega)
    change (D.wires (List.ofFn x)).getD (n + k) false = _
    rw [hwires_eq]
    have hidx : n + k < (wstep pref g).length := by
      simp only [wstep, List.length_append, List.length_singleton]; omega
    rw [wfold_getD_lt _ _ (n + k) hidx]
    have hstep_at : (wstep pref g).getD (n + k) false =
        g.op.eval (g.inputs.map fun i => pref.getD i false) := by
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]
      simp
    rw [hstep_at]
    congr 1
    exact List.map_congr_left fun i _ => hpref_get i
  -- Equivalence between graphFun G empty and the target edge predicate
  have hgraphFun_eq : ∀ x : Fin n → Bool,
      graphFun G ∅ x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    unfold graphFun
    have hempty : decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) = false := by
      simp
    rw [hempty, Bool.false_or]
  -- Case 0: G has no edges
  by_cases hne : G.edgeFinset.Nonempty
  swap
  · refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · intro x
      have hl : (⟨[], n⟩ : Circuit).eval (List.ofFn x) = false := by
        change (List.ofFn x).getD n false = false
        exact List.getD_eq_default _ _ (by rw [List.length_ofFn])
      have hr : decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) = false := by
        rw [decide_eq_false_iff_not]
        rintro ⟨u, v, huv, _, _⟩
        apply hne
        exact ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr huv⟩
      rw [hl, hr]
    · intro D _ _; exact Nat.zero_le _
    · intro j g hgj; simp at hgj
  -- Case 1: G has at least one edge. Establish NoFourCycle G.
  have hN4 : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro w1 hw1 w2 hw2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    rcases hc4 a w1 b w2 hw1.1 hw1.2.symm hw2.2 hw2.1.symm with h1 | h2
    · exact absurd h1 hab
    · exact h2
  -- Build an IsAO2 circuit computing graphFun G empty
  have hExistsAO : ∃ C : Circuit, IsAO2 n C ∧ circuitFun n C = graphFun G ∅ := by
    let edgePairs : List (Fin n × Fin n) :=
      (Finset.univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2).toList
    have hmem_ep : ∀ p : Fin n × Fin n, p ∈ edgePairs ↔ G.Adj p.1 p.2 := by
      intro p
      simp [edgePairs]
    have hep_ne : edgePairs ≠ [] := by
      intro hem
      obtain ⟨e, he⟩ := hne
      revert he
      induction e using Sym2.ind with
      | _ u v =>
        intro huv
        have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp huv
        have hmem : (u, v) ∈ edgePairs := (hmem_ep (u, v)).mpr hadj
        rw [hem] at hmem
        simp at hmem
    have hbuild : ∀ (l : List (Fin n × Fin n)), l ≠ [] →
        ∃ C : Circuit, IsAO2 n C ∧ C.output < n + C.gates.length ∧
          ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
            ∃ p ∈ l, x p.1 = true ∧ x p.2 = true := by
      intro l
      induction l with
      | nil => intro h; exact absurd rfl h
      | cons p rest ih =>
        intro _
        by_cases hr : rest = []
        · subst hr
          let C0 : Circuit := ⟨[⟨GateOp.and, [p.1.val, p.2.val]⟩], n⟩
          refine ⟨C0, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
          · intro g hg; simp only [C0, List.mem_singleton] at hg; rw [hg]; exact Or.inl rfl
          · intro j hj i hi
            have hj0 : j = 0 := by simp [C0] at hj; omega
            subst hj0
            change i ∈ [p.1.val, p.2.val] at hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · exact Nat.lt_of_lt_of_le p.1.isLt (Nat.le_add_right n 0)
            · exact Nat.lt_of_lt_of_le p.2.isLt (Nat.le_add_right n 0)
          · intro g hg; simp only [C0, List.mem_singleton] at hg; rw [hg]; rfl
          · simp [C0]
          · intro x
            change wireVal n C0 (n + 0) x = true ↔ _
            rw [wireVal_gate_gen C0 x 0 (by simp [C0])]
            simp only [C0, List.getElem_cons_zero, List.map_cons, List.map_nil]
            rw [if_pos (Nat.lt_of_lt_of_le p.1.isLt (Nat.le_add_right n 0)),
              if_pos (Nat.lt_of_lt_of_le p.2.isLt (Nat.le_add_right n 0)),
              wireVal_input C0 x p.1.val p.1.isLt, wireVal_input C0 x p.2.val p.2.isLt,
              eval_and2, Bool.and_eq_true]
            simp
        · obtain ⟨C1, ⟨hAO1, hRB1, hL1⟩, hOut1, hEv1⟩ := ih hr
          let m := C1.gates.length
          let gAnd : Gate := ⟨GateOp.and, [p.1.val, p.2.val]⟩
          let gOr : Gate := ⟨GateOp.or, [C1.output, n + m]⟩
          let C2 : Circuit := ⟨C1.gates ++ [gAnd, gOr], n + (m + 1)⟩
          have hlen2 : C2.gates.length = m + 2 := by simp [C2, m]
          have hpref2 : ∀ (x : Fin n → Bool) (r : ℕ), r < n + m →
              wireVal n C2 r x = wireVal n C1 r x := by
            intro x r hr'
            change ((C1.gates ++ [gAnd, gOr]).foldl wstep (List.ofFn x)).getD r false =
              (C1.gates.foldl wstep (List.ofFn x)).getD r false
            rw [List.foldl_append]
            apply wfold_getD_lt
            rw [wfold_len, List.length_ofFn]; exact hr'
          refine ⟨C2, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
          · intro g hg
            simp only [C2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with hg | rfl | rfl
            · exact hAO1 g hg
            · exact Or.inl rfl
            · exact Or.inr rfl
          · intro j hj i hi
            rw [hlen2] at hj
            by_cases hjm : j < m
            · have hga : gateAt C2 j = gateAt C1 j := by
                simp only [gateAt, C2, List.getD_eq_getElem?_getD, List.getElem?_append_left hjm]
              rw [hga] at hi
              exact hRB1 j hjm i hi
            · by_cases hjEq : j = m
              · subst hjEq
                have hga : gateAt C2 m = gAnd := by
                  simp only [gateAt, C2, m, List.getD_eq_getElem?_getD]
                  rw [List.getElem?_append_right (le_refl _)]
                  simp
                rw [hga] at hi
                simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · exact Nat.lt_of_lt_of_le p.1.isLt (Nat.le_add_right n m)
                · exact Nat.lt_of_lt_of_le p.2.isLt (Nat.le_add_right n m)
              · have hjEq2 : j = m + 1 := by omega
                subst hjEq2
                have hga : gateAt C2 (m + 1) = gOr := by
                  simp only [gateAt, C2, m, List.getD_eq_getElem?_getD]
                  rw [List.getElem?_append_right (by omega : C1.gates.length ≤ C1.gates.length + 1)]
                  have hsub : C1.gates.length + 1 - C1.gates.length = 1 := by omega
                  rw [hsub]; simp
                rw [hga] at hi
                simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · omega
                · omega
          · intro g hg
            simp only [C2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with hg | rfl | rfl
            · exact hL1 g hg
            · rfl
            · rfl
          · dsimp only [C2]; rw [hlen2]; omega
          · intro x
            have hm_lt : m < C2.gates.length := by rw [hlen2]; omega
            have hm1_lt : m + 1 < C2.gates.length := by rw [hlen2]; omega
            have hC2m : C2.gates[m]'hm_lt = gAnd := by
              simp only [C2, m]
              rw [List.getElem_append_right (le_refl _)]
              simp
            have hC2m1 : C2.gates[m + 1]'hm1_lt = gOr := by
              simp only [C2, m]
              rw [List.getElem_append_right (by omega : C1.gates.length ≤ C1.gates.length + 1)]
              have hsub : C1.gates.length + 1 - C1.gates.length = 1 := by omega
              simp [hsub]
            have hvm : wireVal n C2 (n + m) x = (x p.1 && x p.2) := by
              rw [wireVal_gate_gen C2 x m hm_lt, hC2m]
              simp only [gAnd, List.map_cons, List.map_nil]
              rw [if_pos (Nat.lt_of_lt_of_le p.1.isLt (Nat.le_add_right n m)),
                if_pos (Nat.lt_of_lt_of_le p.2.isLt (Nat.le_add_right n m)),
                wireVal_input C2 x p.1.val p.1.isLt, wireVal_input C2 x p.2.val p.2.isLt,
                eval_and2]
            change wireVal n C2 (n + (m + 1)) x = true ↔ _
            rw [wireVal_gate_gen C2 x (m + 1) hm1_lt, hC2m1]
            simp only [gOr, List.map_cons, List.map_nil]
            rw [if_pos (by omega : C1.output < n + (m + 1)),
              if_pos (by omega : n + m < n + (m + 1)),
              hpref2 x C1.output hOut1, hvm, eval_or2, Bool.or_eq_true, Bool.and_eq_true]
            have hev := hEv1 x
            change wireVal n C1 C1.output x = true ↔ _ at hev
            rw [hev]
            constructor
            · rintro (⟨q, hq, hq1, hq2⟩ | ⟨hp1, hp2⟩)
              · exact ⟨q, List.mem_cons_of_mem p hq, hq1, hq2⟩
              · exact ⟨p, List.mem_cons_self, hp1, hp2⟩
            · rintro ⟨q, hq, hq1, hq2⟩
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact Or.inr ⟨hq1, hq2⟩
              · exact Or.inl ⟨q, hq', hq1, hq2⟩
    obtain ⟨C, hAO, _, hEv⟩ := hbuild edgePairs hep_ne
    refine ⟨C, hAO, ?_⟩
    funext x
    rw [hgraphFun_eq x]
    change C.eval (List.ofFn x) = _
    apply Bool.eq_iff_iff.mpr
    rw [hEv x, decide_eq_true_iff]
    constructor
    · rintro ⟨⟨u, v⟩, hmem, hu, hv⟩
      exact ⟨u, v, (hmem_ep (u, v)).mp hmem, hu, hv⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      exact ⟨(u, v), (hmem_ep (u, v)).mpr huv, hu, hv⟩
  -- Helper: delete a redundant gate j (constant false, copy of wire w < n + j, or constant true)
  -- from a Monotone2 circuit whose output is not constantly true.
  have hDelWire : ∀ (C : Circuit) (j : ℕ) (rep : ℕ),
      Monotone2 C → j < C.gates.length → (rep < n + j ∨ n + C.gates.length ≤ rep) →
      (∀ x : Fin n → Bool, wireVal n C (n + j) x =
        if rep < n + j then wireVal n C rep x else false) →
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size - 1 ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro C j rep hM hj hrep hval
    let mapPre : ℕ → ℕ := fun i => if i < n + j then i else n + C.gates.length
    let mapPost : ℕ → ℕ := fun i =>
      if i = n + j then rep else if n + j < i then i - 1 else i
    let newGates : List Gate :=
      (List.range (C.gates.length - 1)).map fun k =>
        if k < j then
          let g := C.gates.getD k ⟨GateOp.or, []⟩
          ⟨g.op, g.inputs.map mapPre⟩
        else
          let g := C.gates.getD (k + 1) ⟨GateOp.or, []⟩
          ⟨g.op, g.inputs.map mapPost⟩
    let D : Circuit := ⟨newGates, mapPost C.output⟩
    have hDlen : D.gates.length = C.gates.length - 1 := by simp [D, newGates]
    have hD_lt : ∀ (k : ℕ) (hk : k < D.gates.length), k < j →
        D.gates[k]'hk = ⟨(C.gates[k]'(by omega)).op, (C.gates[k]'(by omega)).inputs.map mapPre⟩ := by
      intro k hk hkj
      simp only [D, newGates, List.getElem_map, List.getElem_range, if_pos hkj,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < C.gates.length),
        Option.getD_some]
    have hD_ge : ∀ (k : ℕ) (hk : k < D.gates.length), j ≤ k →
        D.gates[k]'hk = ⟨(C.gates[k + 1]'(by omega)).op, (C.gates[k + 1]'(by omega)).inputs.map mapPost⟩ := by
      intro k hk hjk
      have hnot : ¬ k < j := by omega
      simp only [D, newGates, List.getElem_map, List.getElem_range, if_neg hnot,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k + 1 < C.gates.length),
        Option.getD_some]
    have hDM : Monotone2 D := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      by_cases hkj : k < j
      · rw [hD_lt k hk hkj]
        have hmk := hM (C.gates[k]'(by omega)) (List.getElem_mem _)
        exact ⟨hmk.1, by simp [hmk.2]⟩
      · rw [hD_ge k hk (by omega)]
        have hmk := hM (C.gates[k + 1]'(by omega)) (List.getElem_mem _)
        exact ⟨hmk.1, by simp [hmk.2]⟩
    have hDval : ∀ (x : Fin n → Bool) (r : ℕ), r < n + C.gates.length →
        wireVal n D (mapPost r) x = wireVal n C r x := by
      intro x r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr
        by_cases hrn : r < n
        · have hmp : mapPost r = r := by simp [mapPost]; split_ifs <;> omega
          rw [hmp, wireVal_input D x r hrn, wireVal_input C x r hrn]
        · by_cases hrj : r < n + j
          · have hmp : mapPost r = r := by simp [mapPost]; split_ifs <;> omega
            rw [hmp]
            let k := r - n
            have hkC : k < C.gates.length := by omega
            have hkD : k < D.gates.length := by rw [hDlen]; omega
            have hrk : r = n + k := by omega
            rw [hrk, wireVal_gate_gen D x k hkD, wireVal_gate_gen C x k hkC, hD_lt k hkD (by omega)]
            simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro i _
            simp only [Function.comp_apply]
            by_cases hik : i < n + k
            · have hij : i < n + j := by omega
              have hpre : mapPre i = i := by simp [mapPre, hij]
              have hpost : mapPost i = i := by simp only [mapPost]; split_ifs <;> omega
              rw [hpre, if_pos hik, if_pos hik]
              conv_lhs => rw [← hpost]
              exact ih i (by omega) (by omega)
            · by_cases hij : i < n + j
              · have hpre : mapPre i = i := by simp [mapPre, hij]
                rw [hpre, if_neg hik, if_neg hik]
              · have hpre : mapPre i = n + C.gates.length := by simp [mapPre, hij]
                rw [hpre, if_neg (by omega), if_neg hik]
          · by_cases hreq : r = n + j
            · subst hreq
              have hmp : mapPost (n + j) = rep := by simp [mapPost]
              rw [hmp, hval x]
              rcases hrep with hrep_lt | hrep_ge
              · rw [if_pos hrep_lt]
                have hmp_rep : mapPost rep = rep := by simp only [mapPost]; split_ifs <;> omega
                conv_lhs => rw [← hmp_rep]
                exact ih rep hrep_lt (by omega)
              · rw [if_neg (by omega : ¬ rep < n + j)]
                exact wireVal_ge D x rep (by rw [hDlen]; omega)
            · let k := r - n - 1
              have hjk : j ≤ k := by omega
              have hkD : k < D.gates.length := by rw [hDlen]; omega
              have hk1C : k + 1 < C.gates.length := by omega
              have hrk1 : r = n + (k + 1) := by omega
              have hmp : mapPost r = n + k := by simp [mapPost]; split_ifs <;> omega
              rw [hmp, hrk1, wireVal_gate_gen D x k hkD, wireVal_gate_gen C x (k + 1) hk1C,
                hD_ge k hkD hjk]
              simp only [List.map_map]
              congr 1
              apply List.map_congr_left
              intro i _
              simp only [Function.comp_apply]
              by_cases hi : i < n + (k + 1)
              · rw [if_pos hi]
                by_cases him : mapPost i < n + k
                · rw [if_pos him]
                  exact ih i (by omega) (by omega)
                · rw [if_neg him]
                  have hieq : i = n + j := by
                    simp only [mapPost] at him
                    split_ifs at him <;> omega
                  subst hieq
                  have hrep_ge : ¬ rep < n + j := by
                    simp only [mapPost, ↓reduceIte] at him; omega
                  rw [hval x, if_neg hrep_ge]
              · rw [if_neg hi, if_neg]
                simp only [mapPost]
                split_ifs <;> omega
    refine ⟨D, hDM, by exact hDlen, fun x => ?_⟩
    by_cases ho : C.output < n + C.gates.length
    · exact hDval x C.output ho
    · have hoD : n + D.gates.length ≤ D.output := by
        simp only [D, hDlen, mapPost]
        split_ifs <;> omega
      change wireVal n D D.output x = wireVal n C C.output x
      rw [wireVal_ge D x D.output hoD, wireVal_ge C x C.output (by omega)]
  have hDelTrue : ∀ (C : Circuit) (j : ℕ),
      Monotone2 C → j < C.gates.length → C.output ≠ n + j →
      (∀ x : Fin n → Bool, wireVal n C (n + j) x = true) →
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size - 1 ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro C j hM hj hout htrue
    classical
    let mapPre : ℕ → ℕ := fun i => if i < n + j then i else n + C.gates.length
    let mapShift : ℕ → ℕ := fun i => if n + j < i then i - 1 else i
    let newGates : List Gate :=
      (List.range (C.gates.length - 1)).map fun k =>
        if k < j then
          let g := C.gates.getD k ⟨GateOp.or, []⟩
          ⟨g.op, g.inputs.map mapPre⟩
        else
          let g := C.gates.getD (k + 1) ⟨GateOp.or, []⟩
          if g.op = GateOp.and then
            ⟨GateOp.and, (g.inputs.filter (fun i => decide (i ≠ n + j))).map mapShift⟩
          else
            if n + j ∈ g.inputs then ⟨GateOp.and, []⟩
            else ⟨g.op, g.inputs.map mapShift⟩
    let D : Circuit := ⟨newGates, mapShift C.output⟩
    have hDlen : D.gates.length = C.gates.length - 1 := by simp [D, newGates]
    have hD_lt : ∀ (k : ℕ) (hk : k < D.gates.length), k < j →
        D.gates[k]'hk = ⟨(C.gates[k]'(by omega)).op, (C.gates[k]'(by omega)).inputs.map mapPre⟩ := by
      intro k hk hkj
      simp only [D, newGates, List.getElem_map, List.getElem_range, if_pos hkj,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < C.gates.length),
        Option.getD_some]
    have hD_ge : ∀ (k : ℕ) (hk : k < D.gates.length), j ≤ k →
        D.gates[k]'hk =
          let g := C.gates[k + 1]'(by omega)
          if g.op = GateOp.and then
            Gate.mk GateOp.and ((g.inputs.filter (fun i => decide (i ≠ n + j))).map mapShift)
          else
            if n + j ∈ g.inputs then Gate.mk GateOp.and []
            else Gate.mk g.op (g.inputs.map mapShift) := by
      intro k hk hjk
      have hnot : ¬ k < j := by omega
      simp only [D, newGates, List.getElem_map, List.getElem_range, if_neg hnot,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k + 1 < C.gates.length),
        Option.getD_some]
    have hDM : Monotone2 D := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      by_cases hkj : k < j
      · rw [hD_lt k hk hkj]
        have hmk := hM (C.gates[k]'(by omega)) (List.getElem_mem _)
        exact ⟨hmk.1, by simp [hmk.2]⟩
      · rw [hD_ge k hk (by omega)]
        dsimp only
        have hmk := hM (C.gates[k + 1]'(by omega)) (List.getElem_mem _)
        by_cases hand : (C.gates[k + 1]'(by omega)).op = GateOp.and
        · rw [if_pos hand]
          refine ⟨Or.inl rfl, ?_⟩
          rw [List.length_map]
          exact le_trans (List.length_filter_le _ _) hmk.2
        · rw [if_neg hand]
          by_cases hmem : n + j ∈ (C.gates[k + 1]'(by omega)).inputs
          · rw [if_pos hmem]; exact ⟨Or.inl rfl, by simp⟩
          · rw [if_neg hmem]; exact ⟨hmk.1, by simp [hmk.2]⟩
    have hDval : ∀ (x : Fin n → Bool) (r : ℕ), r < n + C.gates.length → r ≠ n + j →
        wireVal n D (mapShift r) x = wireVal n C r x := by
      intro x r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr hrne
        by_cases hrn : r < n
        · have hms : mapShift r = r := by simp only [mapShift]; split_ifs <;> omega
          rw [hms, wireVal_input D x r hrn, wireVal_input C x r hrn]
        · by_cases hrj : r < n + j
          · have hms : mapShift r = r := by simp only [mapShift]; split_ifs <;> omega
            rw [hms]
            let k := r - n
            have hkC : k < C.gates.length := by omega
            have hkD : k < D.gates.length := by rw [hDlen]; omega
            have hrk : r = n + k := by omega
            rw [hrk, wireVal_gate_gen D x k hkD, wireVal_gate_gen C x k hkC, hD_lt k hkD (by omega)]
            simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro i _
            simp only [Function.comp_apply]
            by_cases hik : i < n + k
            · have hij : i < n + j := by omega
              have hpre : mapPre i = i := by simp [mapPre, hij]
              have hsh : mapShift i = i := by simp only [mapShift]; split_ifs <;> omega
              rw [hpre, if_pos hik, if_pos hik]
              conv_lhs => rw [← hsh]
              exact ih i (by omega) (by omega) (by omega)
            · by_cases hij : i < n + j
              · have hpre : mapPre i = i := by simp [mapPre, hij]
                rw [hpre, if_neg hik, if_neg hik]
              · have hpre : mapPre i = n + C.gates.length := by simp [mapPre, hij]
                rw [hpre, if_neg (by omega), if_neg hik]
          · let k := r - n - 1
            have hjk : j ≤ k := by omega
            have hkD : k < D.gates.length := by rw [hDlen]; omega
            have hk1C : k + 1 < C.gates.length := by omega
            have hrk1 : r = n + (k + 1) := by omega
            have hms : mapShift r = n + k := by simp [mapShift]; split_ifs <;> omega
            rw [hms, hrk1, wireVal_gate_gen D x k hkD, wireVal_gate_gen C x (k + 1) hk1C,
              hD_ge k hkD hjk]
            dsimp only
            have hmk := hM (C.gates[k + 1]'hk1C) (List.getElem_mem hk1C)
            have hih_i : ∀ i : ℕ, i ≠ n + j →
                (if mapShift i < n + k then wireVal n D (mapShift i) x else false) =
                (if i < n + (k + 1) then wireVal n C i x else false) := by
              intro i hine
              by_cases hi : i < n + (k + 1)
              · have hms_lt : mapShift i < n + k := by simp only [mapShift]; split_ifs <;> omega
                rw [if_pos hms_lt, if_pos hi]
                exact ih i (by omega) (by omega) hine
              · have hms_ge : ¬ mapShift i < n + k := by simp only [mapShift]; split_ifs <;> omega
                rw [if_neg hms_ge, if_neg hi]
            have hread_j : (if n + j < n + (k + 1) then wireVal n C (n + j) x else false) = true := by
              rw [if_pos (by omega), htrue x]
            by_cases hand : (C.gates[k + 1]'hk1C).op = GateOp.and
            · rw [if_pos hand, hand]
              rcases hinp : (C.gates[k + 1]'hk1C).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
              · rw [hinp]; simp [eval_and0]
              · rw [hinp]
                by_cases ha : a = n + j
                · subst ha; simp [eval_and0, eval_and1, hread_j]
                · simp [ha, eval_and1, hih_i a ha]
              · rw [hinp]
                by_cases ha : a = n + j <;> by_cases hb : b = n + j
                · subst ha; subst hb; simp [eval_and0, eval_and2, hread_j]
                · subst ha; simp [hb, eval_and1, eval_and2, hread_j, hih_i b hb]
                · subst hb; simp [ha, eval_and1, eval_and2, hread_j, hih_i a ha]
                · simp [ha, hb, eval_and2, hih_i a ha, hih_i b hb]
              · have hlen := hmk.2; rw [hinp] at hlen; simp at hlen
            · rw [if_neg hand]
              have hor : (C.gates[k + 1]'hk1C).op = GateOp.or := by
                rcases hmk.1 with h | h
                · exact absurd h hand
                · exact h
              by_cases hmem : n + j ∈ (C.gates[k + 1]'hk1C).inputs
              · rw [if_pos hmem, hor]
                rcases hinp : (C.gates[k + 1]'hk1C).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
                · rw [hinp] at hmem; simp at hmem
                · rw [hinp] at hmem ⊢
                  have ha : a = n + j := (List.mem_singleton.mp hmem).symm
                  subst ha; simp [eval_and0, eval_or1, hread_j]
                · rw [hinp] at hmem ⊢
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                  rcases hmem with h1 | h2
                  · rw [← h1]; simp [eval_and0, eval_or2, hread_j]
                  · rw [← h2]; simp [eval_and0, eval_or2, hread_j]
                · have hlen := hmk.2; rw [hinp] at hlen; simp at hlen
              · rw [if_neg hmem]
                simp only [List.map_map]
                congr 1
                apply List.map_congr_left
                intro i hi
                exact hih_i i (fun heq => hmem (heq ▸ hi))
    refine ⟨D, hDM, by exact hDlen, fun x => ?_⟩
    by_cases ho : C.output < n + C.gates.length
    · exact hDval x C.output ho hout
    · have hoD : n + D.gates.length ≤ D.output := by
        simp only [D, hDlen, mapShift]
        split_ifs <;> omega
      change wireVal n D D.output x = wireVal n C C.output x
      rw [wireVal_ge D x D.output hoD, wireVal_ge C x C.output (by omega)]
  -- Every least Monotone2 circuit for graphFun G empty satisfies IsAO2
  have hMonoMin_AO2 : ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      (∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → C.size ≤ D.size) →
      IsAO2 n C := by
    intro C hM hfun hmin
    have hnotTrue : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
      have hf := congrFun hfun (fun _ : Fin n => false)
      change C.eval (List.ofFn (fun _ : Fin n => false)) = graphFun G ∅ (fun _ => false) at hf
      rw [hf, hgraphFun_eq]
      simp
    have hAO : AndOrOnly C := fun g hg => (hM g hg).1
    have hEach : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
        ∀ i ∈ (gateAt C j).inputs, i < n + j := by
      intro j hj
      have hgj : gateAt C j = C.gates[j]'hj := by
        simp [gateAt, List.getD_eq_getElem?_getD, hj]
      rw [hgj]
      have hmj := hM (C.gates[j]'hj) (List.getElem_mem hj)
      have hContra : ∀ (D : Circuit), Monotone2 D → D.size = C.size - 1 →
          (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → False := by
        intro D hDM hDs hDev
        have hDfun : circuitFun n D = graphFun G ∅ := by
          funext x; change D.eval (List.ofFn x) = _; rw [hDev x]; exact congrFun hfun x
        have hle := hmin D hDM hDfun
        have hpos : 0 < C.size := by change 0 < C.gates.length; omega
        omega
      rcases hinp : (C.gates[j]'hj).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
      · exfalso
        rcases hmj.1 with hand | hor
        · have htr : ∀ x : Fin n → Bool, wireVal n C (n + j) x = true := by
            intro x
            rw [wireVal_gate_gen C x j hj, hand, hinp, List.map_nil, eval_and0]
          have hout : C.output ≠ n + j := by
            intro heq
            have h1 := htr (fun _ => false)
            rw [← heq] at h1
            change C.eval (List.ofFn (fun _ => false)) = true at h1
            rw [hnotTrue] at h1; exact Bool.noConfusion h1
          obtain ⟨D, hDM, hDs, hDev⟩ := hDelTrue C j hM hj hout htr
          exact hContra D hDM hDs hDev
        · have hfa : ∀ x : Fin n → Bool, wireVal n C (n + j) x =
              if n + C.gates.length < n + j then wireVal n C (n + C.gates.length) x else false := by
            intro x
            rw [if_neg (by omega), wireVal_gate_gen C x j hj, hor, hinp, List.map_nil, eval_or0]
          obtain ⟨D, hDM, hDs, hDev⟩ :=
            hDelWire C j (n + C.gates.length) hM hj (Or.inr (le_refl _)) hfa
          exact hContra D hDM hDs hDev
      · exfalso
        by_cases ha : a < n + j
        · have hv : ∀ x : Fin n → Bool, wireVal n C (n + j) x =
              if a < n + j then wireVal n C a x else false := by
            intro x
            rw [if_pos ha, wireVal_gate_gen C x j hj, hinp, List.map_cons, List.map_nil, if_pos ha]
            rcases hmj.1 with hand | hor
            · rw [hand, eval_and1]
            · rw [hor, eval_or1]
          obtain ⟨D, hDM, hDs, hDev⟩ := hDelWire C j a hM hj (Or.inl ha) hv
          exact hContra D hDM hDs hDev
        · have hv : ∀ x : Fin n → Bool, wireVal n C (n + j) x =
              if n + C.gates.length < n + j then wireVal n C (n + C.gates.length) x else false := by
            intro x
            rw [if_neg (by omega), wireVal_gate_gen C x j hj, hinp, List.map_cons, List.map_nil,
              if_neg ha]
            rcases hmj.1 with hand | hor
            · rw [hand, eval_and1]
            · rw [hor, eval_or1]
          obtain ⟨D, hDM, hDs, hDev⟩ :=
            hDelWire C j (n + C.gates.length) hM hj (Or.inr (le_refl _)) hv
          exact hContra D hDM hDs hDev
      · refine ⟨rfl, ?_⟩
        by_cases ha : a < n + j
        · by_cases hb : b < n + j
          · intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> assumption
          · exfalso
            rcases hmj.1 with hand | hor
            · have hv : ∀ x : Fin n → Bool, wireVal n C (n + j) x =
                  if n + C.gates.length < n + j then wireVal n C (n + C.gates.length) x else false := by
                intro x
                rw [if_neg (by omega), wireVal_gate_gen C x j hj, hand, hinp,
                  List.map_cons, List.map_cons, List.map_nil, if_pos ha, if_neg hb, eval_and2]
                simp
              obtain ⟨D, hDM, hDs, hDev⟩ :=
                hDelWire C j (n + C.gates.length) hM hj (Or.inr (le_refl _)) hv
              exact hContra D hDM hDs hDev
            · have hv : ∀ x : Fin n → Bool, wireVal n C (n + j) x =
                  if a < n + j then wireVal n C a x else false := by
                intro x
                rw [if_pos ha, wireVal_gate_gen C x j hj, hor, hinp,
                  List.map_cons, List.map_cons, List.map_nil, if_pos ha, if_neg hb, eval_or2]
                simp
              obtain ⟨D, hDM, hDs, hDev⟩ := hDelWire C j a hM hj (Or.inl ha) hv
              exact hContra D hDM hDs hDev
        · exfalso
          rcases hmj.1 with hand | hor
          · have hv : ∀ x : Fin n → Bool, wireVal n C (n + j) x =
                if n + C.gates.length < n + j then wireVal n C (n + C.gates.length) x else false := by
              intro x
              rw [if_neg (by omega), wireVal_gate_gen C x j hj, hand, hinp,
                List.map_cons, List.map_cons, List.map_nil, if_neg ha, eval_and2]
              rfl
            obtain ⟨D, hDM, hDs, hDev⟩ :=
              hDelWire C j (n + C.gates.length) hM hj (Or.inr (le_refl _)) hv
            exact hContra D hDM hDs hDev
          · by_cases hb : b < n + j
            · have hv : ∀ x : Fin n → Bool, wireVal n C (n + j) x =
                  if b < n + j then wireVal n C b x else false := by
                intro x
                rw [if_pos hb, wireVal_gate_gen C x j hj, hor, hinp,
                  List.map_cons, List.map_cons, List.map_nil, if_neg ha, if_pos hb, eval_or2]
                rfl
              obtain ⟨D, hDM, hDs, hDev⟩ := hDelWire C j b hM hj (Or.inl hb) hv
              exact hContra D hDM hDs hDev
            · have hv : ∀ x : Fin n → Bool, wireVal n C (n + j) x =
                  if n + C.gates.length < n + j then wireVal n C (n + C.gates.length) x else false := by
                intro x
                rw [if_neg (by omega), wireVal_gate_gen C x j hj, hor, hinp,
                  List.map_cons, List.map_cons, List.map_nil, if_neg ha, if_neg hb, eval_or2]
                rfl
              obtain ⟨D, hDM, hDs, hDev⟩ :=
                hDelWire C j (n + C.gates.length) hM hj (Or.inr (le_refl _)) hv
              exact hContra D hDM hDs hDev
      · exfalso; have hlen := hmj.2; rw [hinp] at hlen; simp at hlen
    refine ⟨hAO, fun j hj => (hEach j hj).2, fun g hg => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hgj : gateAt C j = C.gates[j]'hj := by
      simp [gateAt, List.getD_eq_getElem?_getD, hj]
    rw [← hgj]
    exact (hEach j hj).1
  -- IsAO2 implies Monotone2
  have hAO2_Mono : ∀ C : Circuit, IsAO2 n C → Monotone2 C := by
    intro C ⟨hAO, _, hLen⟩ g hg
    exact ⟨hAO g hg, by rw [hLen g hg]⟩
  -- Existence of a least Monotone2 circuit (hence IsLeastAO)
  have hExistsMono : ∃ m : ℕ, ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ C.size = m := by
    obtain ⟨C, hAO, hfun⟩ := hExistsAO
    exact ⟨C.size, C, hAO2_Mono C hAO, hfun, rfl⟩
  classical
  let minSize := Nat.find hExistsMono
  obtain ⟨Cmin0, hCmin0M, hCmin0F, hCmin0S⟩ := Nat.find_spec hExistsMono
  have hCmin0LeastM : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → Cmin0.size ≤ D.size := by
    intro D hDM hDF
    rw [hCmin0S]
    exact Nat.find_min' hExistsMono ⟨D, hDM, hDF, rfl⟩
  have hCmin0AO2 : IsAO2 n Cmin0 := hMonoMin_AO2 Cmin0 hCmin0M hCmin0F hCmin0LeastM
  have hCmin0LeastAO : IsLeastAO G Cmin0 :=
    ⟨hCmin0AO2, hCmin0F, fun D hDAO hDF => hCmin0LeastM D (hAO2_Mono D hDAO) hDF⟩
  -- Any IsLeastAO circuit is also a least Monotone2 circuit
  have hLeastAO_LeastMono : ∀ C : Circuit, IsLeastAO G C →
      Monotone2 C ∧ (∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → C.size ≤ D.size) := by
    intro C ⟨hAO, hF, hL⟩
    refine ⟨hAO2_Mono C hAO, fun D hDM hDF => ?_⟩
    exact le_trans (hL Cmin0 hCmin0AO2 hCmin0F) (hCmin0LeastM D hDM hDF)
  -- Prove the FactorSubst obstruction for any dirty AND gate of an IsLeastAO circuit
  have hFactorSubst : ∀ (C : Circuit), IsLeastAO G C → ∀ c ∈ junk G C,
      ∀ sigma : ℕ → ℕ, (∀ r : ℕ, sigma r = opnd C c 0 ∨ sigma r = opnd C c 1) →
      ∃ x : Fin n → Bool, (substReads C n c sigma).eval (List.ofFn x) = true ∧ graphFun G ∅ x = false := by
    intro C hLeast c hc sigma hsig
    by_contra hno
    have hbelow : ∀ x : Fin n → Bool,
        (substReads C n c sigma).eval (List.ofFn x) = true → graphFun G ∅ x = true := by
      intro x hx
      cases hgx : graphFun G ∅ x
      · exfalso; exact hno ⟨x, hx, hgx⟩
      · rfl
    obtain ⟨⟨hAO, hRB, hLen⟩, hfun, hmin⟩ := hLeast
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hc
    obtain ⟨hc_lt, hc_and, _, x0, hx0_c, hx0_f⟩ := hc
    have hgc : gateAt C c = C.gates[c]'hc_lt := by
      simp [gateAt, List.getD_eq_getElem?_getD, hc_lt]
    have hgc_len : (C.gates[c]'hc_lt).inputs.length = 2 := hLen _ (List.getElem_mem hc_lt)
    obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, (C.gates[c]'hc_lt).inputs = [a, b] := by
      rcases hinp : (C.gates[c]'hc_lt).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
      · rw [hinp] at hgc_len; simp at hgc_len
      · rw [hinp] at hgc_len; simp at hgc_len
      · exact ⟨a, b, rfl⟩
      · rw [hinp] at hgc_len; simp at hgc_len
    have hop0 : opnd C c 0 = a := by simp [opnd, hgc, hab]
    have hop1 : opnd C c 1 = b := by simp [opnd, hgc, hab]
    have ha_lt : a < n + c := by
      apply hRB c hc_lt a; rw [hgc, hab]; simp
    have hb_lt : b < n + c := by
      apply hRB c hc_lt b; rw [hgc, hab]; simp
    let C' := substReads C n c sigma
    have hC'len : C'.gates.length = C.gates.length := by simp [C', substReads]
    have hC'get : ∀ (k : ℕ) (hk : k < C'.gates.length),
        C'.gates[k]'hk = ⟨(C.gates[k]'(by omega)).op,
          (C.gates[k]'(by omega)).inputs.map fun i => if i = n + c then sigma k else i⟩ := by
      intro k hk
      simp [C', substReads]
    -- Monotonicity: C' >= C on every wire
    have hMonoWire : ∀ (x : Fin n → Bool) (r : ℕ), r < n + C.gates.length →
        wireVal n C r x = true → wireVal n C' r x = true := by
      intro x r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr hval
        by_cases hrn : r < n
        · rw [wireVal_input C' x r hrn]
          rw [wireVal_input C x r hrn] at hval
          exact hval
        · let k := r - n
          have hkC : k < C.gates.length := by omega
          have hkC' : k < C'.gates.length := by rw [hC'len]; omega
          have hrk : r = n + k := by omega
          rw [hrk] at hval ⊢
          rw [wireVal_gate_gen C x k hkC] at hval
          rw [wireVal_gate_gen C' x k hkC', hC'get k hkC']
          have hgk : gateAt C k = C.gates[k]'hkC := by
            simp [gateAt, List.getD_eq_getElem?_getD, hkC]
          have hgk_len : (C.gates[k]'hkC).inputs.length = 2 := hLen _ (List.getElem_mem hkC)
          obtain ⟨u, v, huv⟩ : ∃ u v : ℕ, (C.gates[k]'hkC).inputs = [u, v] := by
            rcases hinp : (C.gates[k]'hkC).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨d, t⟩⟩⟩
            · rw [hinp] at hgk_len; simp at hgk_len
            · rw [hinp] at hgk_len; simp at hgk_len
            · exact ⟨u, v, rfl⟩
            · rw [hinp] at hgk_len; simp at hgk_len
          have hu_lt : u < n + k := by apply hRB k hkC u; rw [hgk, huv]; simp
          have hv_lt : v < n + k := by apply hRB k hkC v; rw [hgk, huv]; simp
          have hStep : ∀ w : ℕ, w < n + k → wireVal n C w x = true →
              (if (if w = n + c then sigma k else w) < n + k then
                wireVal n C' (if w = n + c then sigma k else w) x else false) = true := by
            intro w hw hwt
            by_cases hwc : w = n + c
            · subst hwc
              rw [if_pos rfl]
              have hc_ev : wireVal n C (n + c) x = (wireVal n C a x && wireVal n C b x) := by
                rw [wireVal_gate_gen C x c hc_lt]
                have hc_and' : (C.gates[c]'hc_lt).op = GateOp.and := by rw [← hgc]; exact hc_and
                rw [hc_and', hab, List.map_cons, List.map_cons, List.map_nil,
                  if_pos ha_lt, if_pos hb_lt, eval_and2]
              rw [hc_ev, Bool.and_eq_true] at hwt
              rcases hsig k with hsk | hsk
              · rw [hsk, hop0, if_pos (by omega : a < n + k)]
                exact ih a (by omega) (by omega) hwt.1
              · rw [hsk, hop1, if_pos (by omega : b < n + k)]
                exact ih b (by omega) (by omega) hwt.2
            · rw [if_neg hwc, if_pos hw]
              exact ih w (by omega) (by omega) hwt
          rw [huv] at hval ⊢
          simp only [List.map_cons, List.map_nil] at hval ⊢
          rw [if_pos hu_lt, if_pos hv_lt] at hval
          rcases hAO (C.gates[k]'hkC) (List.getElem_mem hkC) with hand | hor
          · rw [hand, eval_and2, Bool.and_eq_true] at hval ⊢
            exact ⟨hStep u hu_lt hval.1, hStep v hv_lt hval.2⟩
          · rw [hor, eval_or2, Bool.or_eq_true] at hval ⊢
            rcases hval with hu1 | hv1
            · exact Or.inl (hStep u hu_lt hu1)
            · exact Or.inr (hStep v hv_lt hv1)
    -- Therefore C' computes graphFun G empty
    have hC'fun : circuitFun n C' = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · exact hbelow x
      · intro hgx
        have hCx : wireVal n C C.output x = true := by
          change C.eval (List.ofFn x) = true
          have hf := congrFun hfun x
          change C.eval (List.ofFn x) = graphFun G ∅ x at hf
          rw [hf, hgx]
        have ho_lt : C.output < n + C.gates.length := by
          by_contra hge
          rw [wireVal_ge C x C.output (by omega)] at hCx
          exact Bool.noConfusion hCx
        exact hMonoWire x C.output ho_lt hCx
    -- C'.output != n + c because c is true at x0 where graphFun is false
    have hOut_ne : C.output ≠ n + c := by
      intro heq
      have hCx0 : C.eval (List.ofFn x0) = true := by
        change wireVal n C C.output x0 = true
        rw [heq]; exact hx0_c
      have hf := congrFun hfun x0
      change C.eval (List.ofFn x0) = graphFun G ∅ x0 at hf
      rw [hCx0, hx0_f] at hf
      exact Bool.noConfusion hf
    -- C' is IsAO2 and no gate of C' mentions wire n + c
    have hC'AO2 : IsAO2 n C' := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
        rw [hC'get k hk]
        exact hAO (C.gates[k]'(by omega)) (List.getElem_mem _)
      · intro k hk i hi
        have hgk' : gateAt C' k = C'.gates[k]'hk := by
          simp [gateAt, List.getD_eq_getElem?_getD, hk]
        rw [hgk', hC'get k hk] at hi
        obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
        have hkC : k < C.gates.length := by omega
        have hgk : gateAt C k = C.gates[k]'hkC := by
          simp [gateAt, List.getD_eq_getElem?_getD, hkC]
        have hi0_lt : i0 < n + k := hRB k hkC i0 (by rw [hgk]; exact hi0)
        by_cases hEq : i0 = n + c
        · rw [if_pos hEq]
          rcases hsig k with hsk | hsk
          · rw [hsk, hop0]; omega
          · rw [hsk, hop1]; omega
        · rw [if_neg hEq]; exact hi0_lt
      · intro g hg
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
        rw [hC'get k hk]
        simp [hLen _ (List.getElem_mem _)]
    have hNoReadC : ∀ (k : ℕ) (hk : k < C'.gates.length), n + c ∉ (C'.gates[k]'hk).inputs := by
      intro k hk hmem
      rw [hC'get k hk] at hmem
      obtain ⟨i0, _, heq⟩ := List.mem_map.mp hmem
      by_cases hEq : i0 = n + c
      · rw [if_pos hEq] at heq
        rcases hsig k with hsk | hsk
        · rw [hsk, hop0] at heq; omega
        · rw [hsk, hop1] at heq; omega
      · rw [if_neg hEq] at heq; exact hEq heq
    -- Delete gate c from C' (shifting wires > n + c down by 1) to get smaller IsAO2 circuit D
    let sh : ℕ → ℕ := fun i => if n + c < i then i - 1 else i
    let dGates : List Gate :=
      (List.range (C'.gates.length - 1)).map fun k =>
        if k < c then C'.gates.getD k ⟨GateOp.or, []⟩
        else
          let g := C'.gates.getD (k + 1) ⟨GateOp.or, []⟩
          ⟨g.op, g.inputs.map sh⟩
    let D : Circuit := ⟨dGates, sh C'.output⟩
    have hDlen : D.gates.length = C.gates.length - 1 := by simp [D, dGates, hC'len]
    have hD_lt : ∀ (k : ℕ) (hk : k < D.gates.length), k < c →
        D.gates[k]'hk = C'.gates[k]'(by omega) := by
      intro k hk hkc
      simp only [D, dGates, List.getElem_map, List.getElem_range, if_pos hkc,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < C'.gates.length),
        Option.getD_some]
    have hD_ge : ∀ (k : ℕ) (hk : k < D.gates.length), c ≤ k →
        D.gates[k]'hk = ⟨(C'.gates[k + 1]'(by omega)).op, (C'.gates[k + 1]'(by omega)).inputs.map sh⟩ := by
      intro k hk hck
      have hnot : ¬ k < c := by omega
      simp only [D, dGates, List.getElem_map, List.getElem_range, if_neg hnot,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k + 1 < C'.gates.length),
        Option.getD_some]
    have hDAO2 : IsAO2 n D := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
        by_cases hkc : k < c
        · rw [hD_lt k hk hkc]; exact hC'AO2.1 (C'.gates[k]'(by omega)) (List.getElem_mem _)
        · rw [hD_ge k hk (by omega)]; exact hC'AO2.1 (C'.gates[k + 1]'(by omega)) (List.getElem_mem _)
      · intro k hk i hi
        have hgkD : gateAt D k = D.gates[k]'hk := by
          simp [gateAt, List.getD_eq_getElem?_getD, hk]
        rw [hgkD] at hi
        by_cases hkc : k < c
        · rw [hD_lt k hk hkc] at hi
          have hk' : k < C'.gates.length := by omega
          have hgk' : gateAt C' k = C'.gates[k]'hk' := by
            simp [gateAt, List.getD_eq_getElem?_getD, hk']
          exact hC'AO2.2.1 k hk' i (by rw [hgk']; exact hi)
        · rw [hD_ge k hk (by omega)] at hi
          obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
          have hk1' : k + 1 < C'.gates.length := by omega
          have hgk1' : gateAt C' (k + 1) = C'.gates[k + 1]'hk1' := by
            simp [gateAt, List.getD_eq_getElem?_getD, hk1']
          have hi0_lt : i0 < n + (k + 1) := hC'AO2.2.1 (k + 1) hk1' i0 (by rw [hgk1']; exact hi0)
          have hi0_ne : i0 ≠ n + c := fun heq => hNoReadC (k + 1) hk1' (heq ▸ hi0)
          simp only [sh]; split_ifs <;> omega
      · intro g hg
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
        by_cases hkc : k < c
        · rw [hD_lt k hk hkc]; exact hC'AO2.2.2 _ (List.getElem_mem _)
        · rw [hD_ge k hk (by omega)]; simp [hC'AO2.2.2 _ (List.getElem_mem _)]
    have hDval : ∀ (x : Fin n → Bool) (r : ℕ), r < n + C'.gates.length → r ≠ n + c →
        wireVal n D (sh r) x = wireVal n C' r x := by
      intro x r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr hrne
        by_cases hrn : r < n
        · have hsh : sh r = r := by simp only [sh]; split_ifs <;> omega
          rw [hsh, wireVal_input D x r hrn, wireVal_input C' x r hrn]
        · by_cases hrc : r < n + c
          · have hsh : sh r = r := by simp only [sh]; split_ifs <;> omega
            rw [hsh]
            let k := r - n
            have hk' : k < C'.gates.length := by omega
            have hkD : k < D.gates.length := by rw [hDlen]; omega
            have hrk : r = n + k := by omega
            rw [hrk, wireVal_gate_gen D x k hkD, wireVal_gate_gen C' x k hk', hD_lt k hkD (by omega)]
            congr 1
            apply List.map_congr_left
            intro i hi
            have hgk' : gateAt C' k = C'.gates[k]'hk' := by
              simp [gateAt, List.getD_eq_getElem?_getD, hk']
            have hi_lt : i < n + k := hC'AO2.2.1 k hk' i (by rw [hgk']; exact hi)
            have hsh_i : sh i = i := by simp only [sh]; split_ifs <;> omega
            rw [if_pos hi_lt, if_pos hi_lt]
            conv_lhs => rw [← hsh_i]
            exact ih i (by omega) (by omega) (by omega)
          · let k := r - n - 1
            have hck : c ≤ k := by omega
            have hkD : k < D.gates.length := by rw [hDlen]; omega
            have hk1' : k + 1 < C'.gates.length := by omega
            have hrk1 : r = n + (k + 1) := by omega
            have hsh : sh r = n + k := by simp [sh]; split_ifs <;> omega
            rw [hsh, hrk1, wireVal_gate_gen D x k hkD, wireVal_gate_gen C' x (k + 1) hk1',
              hD_ge k hkD hck]
            simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro i hi
            simp only [Function.comp_apply]
            have hgk1' : gateAt C' (k + 1) = C'.gates[k + 1]'hk1' := by
              simp [gateAt, List.getD_eq_getElem?_getD, hk1']
            have hi_lt : i < n + (k + 1) := hC'AO2.2.1 (k + 1) hk1' i (by rw [hgk1']; exact hi)
            have hi_ne : i ≠ n + c := fun heq => hNoReadC (k + 1) hk1' (heq ▸ hi)
            have hsh_lt : sh i < n + k := by simp only [sh]; split_ifs <;> omega
            rw [if_pos hsh_lt, if_pos hi_lt]
            exact ih i (by omega) (by omega) hi_ne
    have hDfun : circuitFun n D = graphFun G ∅ := by
      rw [← hC'fun]
      funext x
      change wireVal n D (sh C'.output) x = wireVal n C' C'.output x
      by_cases ho : C'.output < n + C'.gates.length
      · exact hDval x C'.output ho hOut_ne
      · have hoD : n + D.gates.length ≤ sh C'.output := by
          simp only [hDlen, hC'len, sh] at ho ⊢; split_ifs <;> omega
        rw [wireVal_ge D x (sh C'.output) hoD, wireVal_ge C' x C'.output (by omega)]
    have hle := hmin D hDAO2 hDfun
    change C.gates.length ≤ D.gates.length at hle
    omega
  -- Minimize (junk G C).card over all IsLeastAO G C circuits
  have hExistsJunk : ∃ m : ℕ, ∃ C : Circuit, IsLeastAO G C ∧ (junk G C).card = m :=
    ⟨(junk G Cmin0).card, Cmin0, hCmin0LeastAO, rfl⟩
  obtain ⟨Cbest, hCbestLeast, hCbestCard⟩ := Nat.find_spec hExistsJunk
  rcases hmj : Nat.find hExistsJunk with _ | _ | k
  · -- minJunk = 0: every AND gate of Cbest is below f_G
    rw [hmj] at hCbestCard
    have hjEmpty : junk G Cbest = ∅ := Finset.card_eq_zero.mp hCbestCard
    obtain ⟨hCbestM, hCbestMinM⟩ := hLeastAO_LeastMono Cbest hCbestLeast
    refine ⟨Cbest, hCbestM, ?_, ?_, ?_⟩
    · intro x
      have hf := congrFun hCbestLeast.2.1 x
      change Cbest.eval (List.ofFn x) = graphFun G ∅ x at hf
      rw [hf, hgraphFun_eq x]
    · intro D hDM hDev
      apply hCbestMinM D hDM
      funext x
      change D.eval (List.ofFn x) = graphFun G ∅ x
      rw [hDev x, hgraphFun_eq x]
    · intro j g hgj hgop x hwx
      have hj_lt : j < Cbest.gates.length := by
        by_contra h
        rw [List.getElem?_eq_none (by omega)] at hgj
        cases hgj
      have hga : gateAt Cbest j = g := by
        simp only [gateAt, List.getD_eq_getElem?_getD, hgj, Option.getD_some]
      by_contra hnoE
      have hgf : graphFun G ∅ x = false := by
        rw [hgraphFun_eq x, decide_eq_false_iff_not]; exact hnoE
      have hmem : j ∈ junk G Cbest := by
        simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
        exact ⟨hj_lt, by rw [hga]; exact hgop, hj_lt, x, hwx, hgf⟩
      rw [hjEmpty] at hmem
      simp at hmem
  · -- minJunk = 1: normalize to TopForm and apply elim_one_junk
    exfalso
    rw [hmj] at hCbestCard
    obtain ⟨C1, hC1Least, hC1CardLe, hC1Top⟩ := topForm_norm n G Cbest hne hCbestLeast
    have hC1CardGe : 1 ≤ (junk G C1).card := by
      have hle := Nat.find_min' hExistsJunk ⟨C1, hC1Least, rfl⟩
      omega
    have hC1CardEq : (junk G C1).card = 1 := by omega
    obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hC1CardEq
    have hg_mem : g ∈ junk G C1 := by rw [hg]; simp
    obtain ⟨C2, hC2Least, hC2Empty⟩ :=
      elim_one_junk n G C1 g htri hN4 hne hC1Least hC1Top hg
        (fun sigma hsig => hFactorSubst C1 hC1Least g hg_mem sigma hsig)
    have h0 : Nat.find hExistsJunk ≤ 0 :=
      Nat.find_min' hExistsJunk ⟨C2, hC2Least, by rw [hC2Empty, Finset.card_empty]⟩
    omega
  · -- minJunk = k + 2: normalize to TopForm and apply reduce_multi_junk
    exfalso
    rw [hmj] at hCbestCard
    obtain ⟨C1, hC1Least, hC1CardLe, hC1Top⟩ := topForm_norm n G Cbest hne hCbestLeast
    have hC1CardGe : k + 2 ≤ (junk G C1).card := by
      have hle := Nat.find_min' hExistsJunk ⟨C1, hC1Least, rfl⟩
      omega
    have hC1CardEq : (junk G C1).card = k + 2 := by omega
    obtain ⟨C2, hC2Least, hC2Lt⟩ :=
      reduce_multi_junk n G C1 htri hN4 hne hC1Least hC1Top (by omega)
        (fun c hc sigma hsig => hFactorSubst C1 hC1Least c hc sigma hsig)
    have hlt := Nat.find_min' hExistsJunk ⟨C2, hC2Least, rfl⟩
    omega
