/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux130

/-!
# Proposition GB6, final assertion: reverse first visits from first contacts

Packet PROVE-JORDANCPL. Supplement §8.6, Proposition GB6 (`source/spec/p481-528.md` L929–L975, pp. 518–520), last
paragraph of the proof:

> "For the final assertion, apply the result on the event of an interior tip at each rational own time and intersect
> these countably many probability-one events. Interior own times are dense […]. Properness of the counterflow and
> continuity of both paths extend containment to the remaining times. If two flow points are in strict order, use
> interior times strictly between them and the assertion that the first contact with each earlier prefix is its tip.
> This gives reverse first-visit order; limiting endpoint cases follow by continuity and properness."

This file proves that deterministic step for one realization. The input is the first-contact assertion of GB6 at a
set `S` of own times that is dense in the order sense: for `s ∈ S` the counterflow `η` first meets the prefix
`α([0, s])` at a finite time `T`, and there `η(T) = α(s)` (`IsFirstContactAtTip`).

## Main results

* `firstVisit_le_of_lt`: for `s < s'` (any own times), `T(α(s')) ≤ T(α(s))`, where `T` is the first counterflow
  visit time (`Aux130.firstVisit`);
* **`antitone_firstVisit`**: `t ↦ T(α(t))` is antitone (reverse first-visit order; the hypothesis `antitone_β` of
  `Sec7.Aux130`'s selection configuration);
* `firstVisit_lt_of_lt`: strict order between two points of `S` (simple `α`);
* **`mem_closure_range`**: containment `α(t) ∈ closure (η [0, ∞))` for every own time `t`, and
  `mem_range_of_mem` (`α(s)` is visited for `s ∈ S`).

The mathematics added beyond the source's sentence: the first-contact times `T(s)`, `s ∈ S`, decrease in `s`; for
`s < s'` their limit as `s'' ↑ s'` through `S` is a visit time of `α(s')` (continuity of `η` and `α`), and it is at
most `T(α(s))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB6

open Sec7.Aux130 (firstVisit firstVisit_le le_firstVisit_iff)

variable {X : Type*}

/-- **GB6's first-contact assertion at the own time `s`**: the counterflow `η` meets the flow prefix `α([0, s])` for
the first time at a finite time `T`, and its contact point is the current tip `α(s)` ("The original first-contact
time is finite and its contact point is exactly `p`"). -/
def IsFirstContactAtTip (η α : ℝ≥0 → X) (s : ℝ≥0) : Prop :=
  ∃ T : ℝ≥0, η T = α s ∧ ∀ t < T, η t ∉ α '' Icc 0 s

/-- The first-contact time (any witness). -/
theorem IsFirstContactAtTip.le_of_mem {η α : ℝ≥0 → X} {s : ℝ≥0} {T : ℝ≥0}
    (hT : ∀ t < T, η t ∉ α '' Icc 0 s) {u : ℝ≥0} {v : ℝ≥0} (hv : v ≤ s) (hu : η u = α v) : T ≤ u :=
  not_lt.1 fun hlt => hT u hlt ⟨v, ⟨zero_le, hv⟩, hu.symm⟩

/-- The first-contact time at `s` is at most the first visit time of `α(v)`, `v ≤ s`. -/
theorem le_firstVisit_of_firstContact {η α : ℝ≥0 → X} {s : ℝ≥0} {T : ℝ≥0}
    (hT : ∀ t < T, η t ∉ α '' Icc 0 s) {v : ℝ≥0} (hv : v ≤ s) : (T : ℝ≥0∞) ≤ firstVisit η (α v) :=
  le_firstVisit_iff.2 fun _ hu => ENNReal.coe_le_coe.2 (IsFirstContactAtTip.le_of_mem hT hv hu)

variable {η α : ℝ≥0 → X} {S : Set ℝ≥0}

/-- Points of `S` are visited. -/
theorem mem_range_of_mem (hS : ∀ s ∈ S, IsFirstContactAtTip η α s) {s : ℝ≥0} (hs : s ∈ S) :
    α s ∈ range η := by
  obtain ⟨T, hT, -⟩ := hS s hs
  exact ⟨T, hT⟩

/-- **Reverse first-visit order for all own times.** If the first-contact assertion holds on a set `S` dense in the
order sense, `η` and `α` are continuous and `X` is Hausdorff, then `T(α(s')) ≤ T(α(s))` whenever `s ≤ s'`. -/
theorem firstVisit_le_of_le [TopologicalSpace X] [T2Space X] (hη : Continuous η) (hα : Continuous α)
    (hS : ∀ s ∈ S, IsFirstContactAtTip η α s)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ s ∈ S, a < s ∧ s < b) {s s' : ℝ≥0} (hss' : s ≤ s') :
    firstVisit η (α s') ≤ firstVisit η (α s) := by
  rcases hss'.eq_or_lt with rfl | hlt
  · exact le_rfl
  choose T hTη hTfirst using hS
  -- the first-contact times on `S ∩ (s, s')`
  set A : Set ℝ≥0 := S ∩ Ioo s s' with hA
  have hAne : A.Nonempty := by
    obtain ⟨u, hu, h1, h2⟩ := hdense s s' hlt
    exact ⟨u, hu, h1, h2⟩
  -- `T` decreases along `S`
  have hmono : ∀ u (hu : u ∈ S) v (hv : v ∈ S), u ≤ v → T v hv ≤ T u hu := fun u hu v hv huv =>
    IsFirstContactAtTip.le_of_mem (hTfirst v hv) huv (hTη u hu)
  -- the infimum of the first-contact times over `S ∩ (s, s')` is a visit time of `α(s')`
  set Tinf : ℝ≥0 := ⨅ u : A, T u.1 u.2.1 with hTinf
  have hbdd : BddBelow (range fun u : A => T u.1 u.2.1) := ⟨0, fun _ _ => zero_le⟩
  have : Nonempty A := hAne.to_subtype
  -- a sequence in `A` increasing to `s'`
  have hseq : ∀ n : ℕ, ∃ v ∈ A, s' - 1 / ((n : ℝ≥0) + 1) < v := by
    intro n
    have hs'0 : 0 < s' := lt_of_le_of_lt zero_le hlt
    have ha : max s (s' - 1 / ((n : ℝ≥0) + 1)) < s' :=
      max_lt hlt (tsub_lt_self hs'0 (by positivity))
    obtain ⟨v, hv, h1, h2⟩ := hdense _ s' ha
    exact ⟨v, ⟨hv, lt_of_le_of_lt (le_max_left _ _) h1, h2⟩, lt_of_le_of_lt (le_max_right _ _) h1⟩
  choose u hu hu_gt using hseq
  have hu_tend : Tendsto u atTop (𝓝 s') := by
    have hlow : Tendsto (fun n : ℕ => s' - 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 s') := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
        _root_.tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := s')).sub h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hu_gt n).le) (fun n => (hu n).2.2.le)
  -- the first-contact times along the sequence converge to their infimum along a subsequence; use the infimum
  -- `Tinf` and approximate it by first-contact times at points of `A` close to `s'`
  have hTle : ∀ n, Tinf ≤ T (u n) (hu n).1 := fun n => ciInf_le hbdd ⟨u n, hu n⟩
  -- for every point `v ∈ A` the first-contact time at `u n` is at most the one at `v` once `u n ≥ v`
  have hTinf_tend : Tendsto (fun n => T (u n) (hu n).1) atTop (𝓝 Tinf) := by
    rw [tendsto_order]
    refine ⟨fun x hx => Eventually.of_forall fun n => lt_of_lt_of_le hx (hTle n), fun x hx => ?_⟩
    obtain ⟨⟨v, hvA⟩, hvx⟩ := exists_lt_of_ciInf_lt (show Tinf < x from hx)
    have hv_lt : v < s' := hvA.2.2
    have hev : ∀ᶠ n in atTop, v ≤ u n := (hu_tend.eventually (Ioi_mem_nhds hv_lt)).mono fun n hn => hn.le
    exact hev.mono fun n hn => lt_of_le_of_lt (hmono v hvA.1 (u n) (hu n).1 hn) hvx
  -- `η(Tinf) = α(s')`
  have hvisit : η Tinf = α s' := by
    have h1 : Tendsto (fun n => η (T (u n) (hu n).1)) atTop (𝓝 (η Tinf)) :=
      (hη.tendsto Tinf).comp hTinf_tend
    have h2 : Tendsto (fun n => η (T (u n) (hu n).1)) atTop (𝓝 (α s')) := by
      have : (fun n => η (T (u n) (hu n).1)) = fun n => α (u n) := funext fun n => hTη (u n) (hu n).1
      rw [this]
      exact (hα.tendsto s').comp hu_tend
    exact tendsto_nhds_unique h1 h2
  -- `Tinf ≤ T(α(s))`
  have hTinf_le : (Tinf : ℝ≥0∞) ≤ firstVisit η (α s) := by
    obtain ⟨v, hvA⟩ := hAne
    exact le_trans (ENNReal.coe_le_coe.2 (ciInf_le hbdd ⟨v, hvA⟩))
      (le_firstVisit_of_firstContact (hTfirst v hvA.1) hvA.2.1.le)
  exact le_trans (firstVisit_le hvisit) hTinf_le

/-- **Reverse first-visit order** (GB6, final assertion): `t ↦ T(α(t))` is antitone. -/
theorem antitone_firstVisit [TopologicalSpace X] [T2Space X] (hη : Continuous η) (hα : Continuous α)
    (hS : ∀ s ∈ S, IsFirstContactAtTip η α s)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ s ∈ S, a < s ∧ s < b) :
    Antitone fun t => firstVisit η (α t) := fun _ _ hst =>
  firstVisit_le_of_le hη hα hS hdense hst

/-- **Strict reverse order** between two points of `S` of a simple flow path. -/
theorem firstVisit_lt_of_lt (hαi : Function.Injective α) (hS : ∀ s ∈ S, IsFirstContactAtTip η α s)
    {s s' : ℝ≥0} (hs : s ∈ S) (hs' : s' ∈ S) (hlt : s < s') :
    firstVisit η (α s') < firstVisit η (α s) := by
  obtain ⟨T, hTη, hTfirst⟩ := hS s' hs'
  obtain ⟨T₁, hT₁η, hT₁first⟩ := hS s hs
  -- the first contact with `α([0, s'])` happens at `α(s')`, strictly before the first visit `T₁` of `α(s)`
  have hT1 : T < T₁ := by
    refine lt_of_le_of_ne (IsFirstContactAtTip.le_of_mem hTfirst hlt.le hT₁η) fun h => hlt.ne' (hαi ?_)
    rw [← hTη, h, hT₁η]
  calc firstVisit η (α s') ≤ T := firstVisit_le hTη
    _ < T₁ := ENNReal.coe_lt_coe.2 hT1
    _ ≤ firstVisit η (α s) := le_firstVisit_of_firstContact hT₁first le_rfl

/-- **Containment** (GB6, final assertion: "Properness of the counterflow and continuity of both paths extend
containment to the remaining times"): every point of the flow path lies in the closure of the counterflow range. -/
theorem mem_closure_range [TopologicalSpace X] (hα : Continuous α) (hS : ∀ s ∈ S, IsFirstContactAtTip η α s)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ s ∈ S, a < s ∧ s < b) (t : ℝ≥0) : α t ∈ closure (range η) := by
  -- `α(t)` is the limit of `α(s)`, `s ∈ S`, `s ↓ t`
  have hseq : ∀ n : ℕ, ∃ s ∈ S, t < s ∧ s < t + 1 / ((n : ℝ≥0) + 1) := fun n =>
    hdense t (t + 1 / ((n : ℝ≥0) + 1)) (lt_add_of_pos_right t (by positivity))
  choose s hs hts hst using hseq
  have hs_tend : Tendsto s atTop (𝓝 t) := by
    have hup : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
        _root_.tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := t)).add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (hts n).le)
      fun n => (hst n).le
  exact mem_closure_of_tendsto ((hα.tendsto t).comp hs_tend)
    (Eventually.of_forall fun n => mem_range_of_mem hS (hs n))

end GB6

end Supp8

end InteractingSLE
