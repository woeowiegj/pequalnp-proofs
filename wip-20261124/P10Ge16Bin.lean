import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sublists
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.P10Ge16Bin


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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


end BranchGraph

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
    exact PEqualNP.Outside.P10Ge16Bin.least_gate_inputs_nodup least nonnull _
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


lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega



namespace PetersenTen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup Relation

abbrev V10 := Fin 10

def p10Edges : List (V10 × V10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),
   (0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def p10F (x : V10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def p10Adj (u v : V10) : Bool :=
  p10Edges.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

lemma p10Adj_symm : ∀ u v : V10, p10Adj u v = true → p10Adj v u = true := by
  decide +kernel

lemma p10Adj_irrefl : ∀ u : V10, ¬ (p10Adj u u = true) := by
  decide +kernel

def p10Graph : SimpleGraph V10 where
  Adj u v := p10Adj u v = true
  symm := ⟨p10Adj_symm⟩
  loopless := ⟨p10Adj_irrefl⟩

instance p10AdjDec : DecidableRel p10Graph.Adj := fun u v =>
  inferInstanceAs (Decidable (p10Adj u v = true))

lemma p10F_eq_edgeValue (x : V10 → Bool) :
    p10F x = PetersenScratch.edgeValue p10Graph x := by
  rw [Bool.eq_iff_iff]
  simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  constructor
  · intro hx
    have haux : ∀ a b : V10, (x a && x b) = true → p10Adj a b = true →
        ∃ u v : V10, p10Graph.Adj u v ∧ x u = true ∧ x v = true := by
      intro a b hab hadj
      simp only [Bool.and_eq_true] at hab
      exact ⟨a, b, hadj, hab.1, hab.2⟩
    simp only [p10F, Bool.or_eq_true] at hx
    rcases hx with (((((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11) | h12) | h13) | h14
    · exact haux 0 1 h0 (by decide)
    · exact haux 1 2 h1 (by decide)
    · exact haux 2 3 h2 (by decide)
    · exact haux 3 4 h3 (by decide)
    · exact haux 4 0 h4 (by decide)
    · exact haux 0 5 h5 (by decide)
    · exact haux 1 6 h6 (by decide)
    · exact haux 2 7 h7 (by decide)
    · exact haux 3 8 h8 (by decide)
    · exact haux 4 9 h9 (by decide)
    · exact haux 5 7 h10 (by decide)
    · exact haux 7 9 h11 (by decide)
    · exact haux 9 6 h12 (by decide)
    · exact haux 6 8 h13 (by decide)
    · exact haux 8 5 h14 (by decide)
  · rintro ⟨u, v, huv, hxu, hxv⟩
    have hmem : ∀ a b : V10, p10Adj a b = true → (a, b) ∈ p10Edges ∨ (b, a) ∈ p10Edges := by
      decide +kernel
    have hm := hmem u v huv
    rcases hm with hm | hm <;>
      simp only [p10Edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm <;>
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [p10F, hxu, hxv]

lemma p10_marked_edges (S : Finset V10) :
    p10F (setInput S) = true ↔ BranchGraph.containsEdge p10Graph S := by
  rw [p10F_eq_edgeValue]
  simp only [PetersenScratch.edgeValue, decide_eq_true_eq, BranchGraph.containsEdge, setInput]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨u, hu, v, hv, huv⟩
  · rintro ⟨u, hu, v, hv, huv⟩
    exact ⟨u, v, huv, hu, hv⟩

lemma p10_alternate_neighbors :
    ∀ i j : V10, p10Graph.Adj i j → ∃ u v : V10,
      p10Graph.Adj i u ∧ p10Graph.Adj j v ∧ u ≠ j ∧ v ≠ i ∧ ¬ p10Graph.Adj u v := by
  decide +kernel

lemma p10_triangle_free : ∀ a u z : V10, p10Graph.Adj a u → p10Graph.Adj u z → ¬ p10Graph.Adj a z := by
  decide +kernel

lemma p10_distinct_nbrs : ∀ u v : V10, u ≠ v →
    ∃ a : V10, (p10Graph.Adj a u ∧ ¬ p10Graph.Adj a v) ∨ (p10Graph.Adj a v ∧ ¬ p10Graph.Adj a u) := by
  decide +kernel

lemma p10_isolated_witness : ∀ u v z : V10, u ≠ v → v ≠ z → p10Graph.Adj u z → ¬ p10Graph.Adj v z →
    ∃ b : V10, p10Graph.Adj b v ∧ ¬ p10Graph.Adj b u ∧ ¬ p10Graph.Adj b z := by
  decide +kernel

lemma p10_no_indep_five : ∀ a b c d e : V10, a < b → b < c → c < d → d < e →
    p10Graph.Adj a b ∨ p10Graph.Adj a c ∨ p10Graph.Adj a d ∨ p10Graph.Adj a e ∨
    p10Graph.Adj b c ∨ p10Graph.Adj b d ∨ p10Graph.Adj b e ∨
    p10Graph.Adj c d ∨ p10Graph.Adj c e ∨ p10Graph.Adj d e := by
  decide +kernel

lemma p10_indep_card_le_four (I : Finset V10) (hI : BranchGraph.Independent p10Graph I) : I.card ≤ 4 := by
  by_contra hgt
  have h5 : 5 ≤ I.card := by omega
  let L := I.sort (· ≤ ·)
  have hlen : 5 ≤ L.length := by simpa [L, Finset.length_sort] using h5
  have hpair : L.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort I)
  have hlt (i j : Nat) (hi : i < L.length) (hj : j < L.length) (hij : i < j) : L[i] < L[j] :=
    List.pairwise_iff_getElem.mp hpair i j hi hj hij
  have hmem (i : Nat) (hi : i < L.length) : L[i] ∈ I :=
    (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hi)
  have h0 : 0 < L.length := by omega
  have h1 : 1 < L.length := by omega
  have h2 : 2 < L.length := by omega
  have h3 : 3 < L.length := by omega
  have h4 : 4 < L.length := by omega
  have hedge := p10_no_indep_five L[0] L[1] L[2] L[3] L[4]
    (hlt 0 1 h0 h1 (by omega)) (hlt 1 2 h1 h2 (by omega))
    (hlt 2 3 h2 h3 (by omega)) (hlt 3 4 h3 h4 (by omega))
  rcases hedge with h | h | h | h | h | h | h | h | h | h
  · exact hI _ (hmem 0 h0) _ (hmem 1 h1) h
  · exact hI _ (hmem 0 h0) _ (hmem 2 h2) h
  · exact hI _ (hmem 0 h0) _ (hmem 3 h3) h
  · exact hI _ (hmem 0 h0) _ (hmem 4 h4) h
  · exact hI _ (hmem 1 h1) _ (hmem 2 h2) h
  · exact hI _ (hmem 1 h1) _ (hmem 3 h3) h
  · exact hI _ (hmem 1 h1) _ (hmem 4 h4) h
  · exact hI _ (hmem 2 h2) _ (hmem 3 h3) h
  · exact hI _ (hmem 2 h2) _ (hmem 4 h4) h
  · exact hI _ (hmem 3 h3) _ (hmem 4 h4) h

lemma p10_dep_sample : ∀ v : V10, ∃ w : V10,
    p10F (Function.update (fun i => decide (i = w)) v (!(decide (v = w)))) ≠
      p10F (fun i => decide (i = w)) := by
  decide +kernel

lemma p10_depends (v : V10) : Dep p10F v := by
  obtain ⟨w, hw⟩ := p10_dep_sample v
  exact ⟨fun i => decide (i = w), hw⟩

lemma p10_nonconstant : ∃ x y : V10 → Bool, p10F x ≠ p10F y :=
  ⟨fun _ => false, fun _ => true, by decide⟩

lemma p10_restrict_nonconstant_sample : ∀ (v : V10) (b : Bool),
    ∃ (a c : V10), p10F (Function.update (fun i => decide (i = a ∨ i = c)) v b) ≠
      p10F (Function.update (fun _ => false) v b) := by
  decide +kernel

lemma p10_restrict_nonconstant (v : V10) (b : Bool) :
    ∃ x y : V10 → Bool, p10F (Function.update x v b) ≠ p10F (Function.update y v b) := by
  obtain ⟨a, c, h⟩ := p10_restrict_nonconstant_sample v b
  exact ⟨fun i => decide (i = a ∨ i = c), fun _ => false, h⟩

lemma least_p10_output_valid {gs : List Gate} {out : Nat} (least : Least 10 p10F gs out) :
    out < 10 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv p10_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

theorem finite_branch_bit_factor_with_prefix {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (A : Finset (Fin n)) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool, ∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I, label i = cut) → (∀ i ∈ O, cut < label i) →
        (vl gs (setInput (A ∪ I ∪ O)) out.val = true ↔ decode (code I) O) := by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)) := vl gs (setInput (A ∪ I)) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n), (∀ j ∈ J, label j = cut) ∧ code J = b ∧
      vl gs (setInput (A ∪ J ∪ O)) out.val = true
  refine ⟨code, decode, ?_⟩
  intro I O groupI afterO
  constructor
  · exact fun yes => ⟨I, groupI, rfl, yes⟩
  · rintro ⟨J, groupJ, sameCode, yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (A ∪ K ∪ O)) cut.val = code K := by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O := fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput, absent]
    have sameCut : vl gs (setInput (A ∪ I ∪ O)) cut.val = vl gs (setInput (A ∪ J ∪ O)) cut.val :=
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

lemma three_functions_impossible {α : Type} (code : α → Bool) (decode : Bool → Bool → Prop)
    (a b c : α)
    (ha0 : ¬ decode (code a) false) (ha1 : ¬ decode (code a) true)
    (hb0 : ¬ decode (code b) false) (hb1 : decode (code b) true)
    (hc0 : decode (code c) false) (hc1 : decode (code c) true) : False := by
  cases hca : code a <;> cases hcb : code b <;> cases hcc : code c
  · rw [hca] at ha1; rw [hcb] at hb1; exact ha1 hb1
  · rw [hca] at ha1; rw [hcb] at hb1; exact ha1 hb1
  · rw [hca] at ha0; rw [hcc] at hc0; exact ha0 hc0
  · rw [hcb] at hb0; rw [hcc] at hc0; exact hb0 hc0
  · rw [hcb] at hb0; rw [hcc] at hc0; exact hb0 hc0
  · rw [hca] at ha0; rw [hcc] at hc0; exact ha0 hc0
  · rw [hca] at ha1; rw [hcb] at hb1; exact ha1 hb1
  · rw [hca] at ha1; rw [hcb] at hb1; exact ha1 hb1

lemma p10_bucket_unique_of_later_neighbor {gs : List Gate} {out : Nat} (least : Least 10 p10F gs out)
    (outValid : out < 10 + gs.length)
    (live : ∀ w : Fin (10 + gs.length), w ≠ ⟨out, outValid⟩ → ∃ v, readEdge gs w v)
    (cut : Fin (10 + gs.length)) (prior : cut ≤ ⟨out, outValid⟩)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) ⟨out, outValid⟩ cut)
    (u v z : V10)
    (hu : firstInputBoundary least.hcl ⟨out, outValid⟩ live u = cut)
    (hv : firstInputBoundary least.hcl ⟨out, outValid⟩ live v = cut)
    (hz : cut < firstInputBoundary least.hcl ⟨out, outValid⟩ live z)
    (huz : p10Graph.Adj u z) : u = v := by
  classical
  let outWire : Fin (10 + gs.length) := ⟨out, outValid⟩
  let label := firstInputBoundary least.hcl outWire live
  have computes (x : V10 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue p10Graph x := by
    change vl gs x out = _
    rw [least.hev, p10F_eq_edgeValue]
  have marked (S : Finset V10) : vl gs (setInput S) outWire.val = true ↔
      BranchGraph.containsEdge p10Graph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev]
    exact p10_marked_edges S
  have helper (a : V10) (x y : V10)
      (hx : label x = cut) (hy : label y = cut)
      (hax : p10Graph.Adj a x) (hnay : ¬ p10Graph.Adj a y) (hnaz : ¬ p10Graph.Adj a z)
      (hyz : p10Graph.Adj y z) : False := by
    obtain ⟨code, decode, fac⟩ := finite_branch_bit_factor_with_prefix least.hcl outWire live cut prior terminal {a}
    have f0 (K : Finset V10) (hK : ∀ i ∈ K, label i = cut) :
        decode (code K) ∅ ↔ BranchGraph.containsEdge p10Graph ({a} ∪ K) := by
      have h := fac K ∅ hK (by simp)
      simp only [Finset.union_empty] at h
      exact h.symm.trans (marked ({a} ∪ K))
    have f1 (K : Finset V10) (hK : ∀ i ∈ K, label i = cut) :
        decode (code K) {z} ↔ BranchGraph.containsEdge p10Graph ({a} ∪ K ∪ {z}) := by
      have h := fac K {z} hK (by intro i hi; simp at hi; subst hi; exact hz)
      exact h.symm.trans (marked ({a} ∪ K ∪ {z}))
    let decB (b : Bool) (bit : Bool) : Prop := if bit then decode b {z} else decode b ∅
    have ha0 : ¬ decB (code ∅) false := by
      change ¬ decode (code ∅) ∅
      rw [f0 ∅ (by simp)]
      simp only [Finset.union_empty]
      exact BranchGraph.singleton_no_edge p10Graph a
    have ha1 : ¬ decB (code ∅) true := by
      change ¬ decode (code ∅) {z}
      rw [f1 ∅ (by simp)]
      simp only [Finset.union_empty, Finset.singleton_union]
      rw [BranchGraph.pair_contains_edge]
      exact hnaz
    have hb0 : ¬ decB (code {y}) false := by
      change ¬ decode (code {y}) ∅
      rw [f0 {y} (by intro i hi; simp at hi; subst hi; exact hy)]
      simp only [Finset.singleton_union]
      rw [BranchGraph.pair_contains_edge]
      exact hnay
    have hb1 : decB (code {y}) true := by
      change decode (code {y}) {z}
      rw [f1 {y} (by intro i hi; simp at hi; subst hi; exact hy)]
      exact ⟨y, by simp, z, by simp, hyz⟩
    have hc0 : decB (code {x}) false := by
      change decode (code {x}) ∅
      rw [f0 {x} (by intro i hi; simp at hi; subst hi; exact hx)]
      exact ⟨a, by simp, x, by simp, hax⟩
    have hc1 : decB (code {x}) true := by
      change decode (code {x}) {z}
      rw [f1 {x} (by intro i hi; simp at hi; subst hi; exact hx)]
      exact ⟨a, by simp, x, by simp, hax⟩
    exact three_functions_impossible code decB ∅ {y} {x} ha0 ha1 hb0 hb1 hc0 hc1
  by_contra huv
  have hvz_ne : v ≠ z := by
    intro heq
    subst heq
    exact ne_of_lt hz hv.symm
  by_cases hvz : p10Graph.Adj v z
  · obtain ⟨a, (⟨hau, hnav⟩ | ⟨hav, hnau⟩)⟩ := p10_distinct_nbrs u v huv
    · exact helper a u v hu hv hau hnav (p10_triangle_free a u z hau huz) hvz
    · exact helper a v u hv hu hav hnau (p10_triangle_free a v z hav hvz) huz
  · obtain ⟨b, hbv, hnbu, hnbz⟩ := p10_isolated_witness u v z huv hvz_ne huz hvz
    exact helper b v u hv hu hbv hnbu hnbz huz

theorem p10_six_branches_and_structure {gs : List Gate} {out : Nat} (least : Least 10 p10F gs out) :
    let outValid := least_p10_output_valid least
    let outWire : Fin (10 + gs.length) := ⟨out, outValid⟩
    let live := least_read_edge_live least p10_nonconstant p10_depends p10_restrict_nonconstant outValid
    let label := firstInputBoundary least.hcl outWire live
    let branches := circuitBranchWires (n := 10) gs
    6 ≤ branches.card ∧
    15 ≤ nonNotCount gs ∧
    (nonNotCount gs = 15 →
      ∃ I : Finset V10, I.card = 4 ∧ BranchGraph.Independent p10Graph I ∧
        ∀ w ∈ I, label w = outWire) := by
  classical
  have outValid := least_p10_output_valid least
  let outWire : Fin (10 + gs.length) := ⟨out, outValid⟩
  have live := least_read_edge_live least p10_nonconstant p10_depends p10_restrict_nonconstant outValid
  let label := firstInputBoundary least.hcl outWire live
  let branches := circuitBranchWires (n := 10) gs
  have computes (x : V10 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue p10Graph x := by
    change vl gs x out = _
    rw [least.hev, p10F_eq_edgeValue]
  have indep (r) : BranchGraph.Independent p10Graph (firstInputGroup least.hcl outWire live r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least p10_nonconstant)
      p10Graph computes p10_alternate_neighbors r
  have labels (v : V10) : label v = outWire ∨ label v ∈ branches := by
    have stopped := FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (in_circuit_branches.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have le_out (v : V10) : label v ≤ outWire := by
    rcases labels v with h | h
    · exact le_of_eq h
    · exact le_of_lt (before _ h)
  let S : Finset V10 := Finset.univ.filter fun u => ∃ z : V10, p10Graph.Adj u z ∧ label u < label z
  have hS_branch : ∀ u ∈ S, label u ∈ branches := by
    intro u hu
    obtain ⟨z, _, hlt⟩ := (Finset.mem_filter.mp hu).2
    have hne : label u ≠ outWire := ne_of_lt (lt_of_lt_of_le hlt (le_out z))
    exact (labels u).resolve_left hne
  have hS_inj : Set.InjOn label (S : Set V10) := by
    intro u hu v hv heq
    obtain ⟨z, huz, hlt⟩ := (Finset.mem_filter.mp hu).2
    have hterm : FirstBranchRoute.Terminal (readEdge gs) outWire (label u) :=
      Or.inr (in_circuit_branches.mp (hS_branch u hu))
    exact p10_bucket_unique_of_later_neighbor least outValid live (label u) (le_out u) hterm u v z
      rfl heq.symm hlt huz
  have hS_le_branches : S.card ≤ branches.card := by
    have himg : S.image label ⊆ branches := by
      intro r hr
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
      exact hS_branch u hu
    calc S.card = (S.image label).card := (Finset.card_image_of_injOn hS_inj).symm
      _ ≤ branches.card := Finset.card_le_card himg
  let I : Finset V10 := Finset.univ \ S
  have hI_indep : BranchGraph.Independent p10Graph I := by
    intro u hu v hv huv
    have huS : u ∉ S := (Finset.mem_sdiff.mp hu).2
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    have hne : label u ≠ label v := by
      intro heq
      exact indep (label u) u ((mem_firstInputGroup least.hcl outWire live (label u) u).mpr rfl)
        v ((mem_firstInputGroup least.hcl outWire live (label u) v).mpr heq.symm) huv
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact huS (Finset.mem_filter.mpr ⟨Finset.mem_univ u, ⟨v, huv, hlt⟩⟩)
    · exact hvS (Finset.mem_filter.mpr ⟨Finset.mem_univ v, ⟨u, huv.symm, hgt⟩⟩)
  have hI_le4 : I.card ≤ 4 := p10_indep_card_le_four I hI_indep
  have hS_add_I : I.card + S.card = 10 := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simpa [I] using h
  have h6_S : 6 ≤ S.card := by omega
  have h6_br : 6 ≤ branches.card := le_trans h6_S hS_le_branches
  have branchBudget := branching_budget least.hcl outValid (fun w hw hne => by
      let wire : Fin (10 + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
  have countTotal := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at countTotal
  have h15 : 15 ≤ nonNotCount gs := by omega
  refine ⟨h6_br, h15, ?_⟩
  intro hEq15
  have hbr6 : branches.card = 6 := by omega
  have hS6 : S.card = 6 := by omega
  have hI4 : I.card = 4 := by omega
  have himg_eq : S.image label = branches := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
      exact hS_branch u hu
    · rw [Finset.card_image_of_injOn hS_inj, hS6, hbr6]
  refine ⟨I, hI4, hI_indep, ?_⟩
  intro w hw
  rcases labels w with hOut | hBr
  · exact hOut
  · rw [← himg_eq] at hBr
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hBr
    obtain ⟨z, huz, hlt⟩ := (Finset.mem_filter.mp hu).2
    have hterm : FirstBranchRoute.Terminal (readEdge gs) outWire (label u) :=
      Or.inr (in_circuit_branches.mp (hS_branch u hu))
    have huw := p10_bucket_unique_of_later_neighbor least outValid live (label u) (le_out u) hterm u w z
      rfl heq.symm hlt huz
    subst huw
    exact False.elim ((Finset.mem_sdiff.mp hw).2 hu)

end PetersenTen


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

namespace TreeExtract

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  have hnd := PEqualNP.Outside.P10Ge16Bin.least_gate_inputs_nodup least p10_nonconstant
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

end PEqualNP.Outside.P10Ge16Bin

theorem PEqualNP.Outside.P10Ge16Bin :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.FanInTwo C →
    C.gates.countP (fun g => !(g.op.eval [false])) ≤ 15 →
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠
      (fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x :=
  PEqualNP.Outside.P10Ge16Bin.TreeExtract.p10_ge_sixteen_bin
