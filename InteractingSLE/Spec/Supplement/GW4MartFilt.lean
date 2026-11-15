/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4MartLaw
import InteractingSLE.Spec.Supplement.BW1LinesSafe

/-!
# GW4's protected martingales, part 2: the line filtration

Packet PROVE-GW4-MART. Astra's follow-up 3 §3.6 (`ig1_followup3_audited.txt` L970–L985): "The capacity clock and its
inverse are adapted. For a relative stop `T(u) = inf{t : ℓ(t) > u}` is the corresponding ambient stop […] the
time-changed raw filtration is exactly the raw filtration in (Q3.2)".

The line σ-algebras `𝒢L t` (the germ of the line's local set and its marks) need not increase in `t`. The
**line filtration** at capacity time `q` consists of the events `D` that are `𝒢L t`-events on every live line event
`{q ≤ a t < V}`. It is a filtration because the live line events decrease in `q` (`lineFilt`). Events inside
`{V ≤ q}` belong to it at time `q`, so `V` is a stopping time (`isStoppingTime_lineFilt`).

## Main definitions and results

* `liveLine`, `lineSigma`, `lineFilt`, `measurableSet_lineFilt_iff`;
* `measurableSet_lineFilt_of_subset_stop`, **`isStoppingTime_lineFilt`**;
* `measurableSet_lineFilt_of_inter`: an event cut into line events by `{q ≤ a t}` is in the line filtration;
* `measurableSet_capPiece_lineFilt`: the capped pieces of `hasPhaseSafeLaw_of_lineLaw`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW4Fix.Mart

open Coupling Restart.DomainMarkov Restart.DomainMarkov.Aux79

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The live event of the physical line `t` at capacity time `q`: the clock has reached `q` and the line is before the
lifetime. -/
def liveLine (a : ℝ≥0 → Ω → ℝ≥0∞) (V : Ω → ℝ≥0∞) (q t : ℝ≥0) : Set Ω :=
  {ω | (q : ℝ≥0∞) ≤ a t ω ∧ a t ω < V ω}

omit mΩ in
theorem liveLine_anti {a : ℝ≥0 → Ω → ℝ≥0∞} {V : Ω → ℝ≥0∞} {q q' : ℝ≥0} (hqq' : q ≤ q') (t : ℝ≥0) :
    liveLine a V q' t ⊆ liveLine a V q t :=
  fun _ hω => ⟨(ENNReal.coe_le_coe.2 hqq').trans hω.1, hω.2⟩

/-- **The line σ-algebra at capacity time `q`.** -/
@[instance_reducible]
def lineSigma (𝒢L : ℝ≥0 → MeasurableSpace Ω) (a : ℝ≥0 → Ω → ℝ≥0∞) (V : Ω → ℝ≥0∞)
    (hA : ∀ q t, MeasurableSet[𝒢L t] (liveLine a V q t)) (q : ℝ≥0) : MeasurableSpace Ω where
  MeasurableSet' D := MeasurableSet D ∧ ∀ t, MeasurableSet[𝒢L t] (D ∩ liveLine a V q t)
  measurableSet_empty := ⟨MeasurableSet.empty, fun t => by
    rw [empty_inter]; exact @MeasurableSet.empty _ (𝒢L t)⟩
  measurableSet_compl D hD := ⟨hD.1.compl, fun t => by
    have e : Dᶜ ∩ liveLine a V q t = liveLine a V q t \ (D ∩ liveLine a V q t) := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [e]
    exact (hA q t).diff (hD.2 t)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun t => by
    rw [iUnion_inter]
    exact MeasurableSet.iUnion fun i => (hf i).2 t⟩

/-- **The line filtration** in capacity time. -/
def lineFilt (𝒢L : ℝ≥0 → MeasurableSpace Ω) (a : ℝ≥0 → Ω → ℝ≥0∞) (V : Ω → ℝ≥0∞)
    (hA : ∀ q t, MeasurableSet[𝒢L t] (liveLine a V q t)) : Filtration ℝ≥0 mΩ where
  seq := lineSigma 𝒢L a V hA
  mono' q q' hqq' D hD := ⟨hD.1, fun t => by
    have e : D ∩ liveLine a V q' t = (D ∩ liveLine a V q t) ∩ liveLine a V q' t := by
      rw [inter_assoc, inter_eq_right.2 (liveLine_anti hqq' t)]
    rw [e]
    exact (hD.2 t).inter (hA q' t)⟩
  le' _ _ hD := hD.1

variable {𝒢L : ℝ≥0 → MeasurableSpace Ω} {a : ℝ≥0 → Ω → ℝ≥0∞} {V : Ω → ℝ≥0∞}
  {hA : ∀ q t, MeasurableSet[𝒢L t] (liveLine a V q t)}

theorem measurableSet_lineFilt_iff {q : ℝ≥0} {D : Set Ω} :
    MeasurableSet[lineFilt 𝒢L a V hA q] D ↔
      MeasurableSet D ∧ ∀ t, MeasurableSet[𝒢L t] (D ∩ liveLine a V q t) := Iff.rfl

/-- Events inside `{V ≤ q}` are events of the line filtration at `q`. -/
theorem measurableSet_lineFilt_of_subset_stop {q : ℝ≥0} {D : Set Ω} (hD : MeasurableSet D)
    (hDV : D ⊆ {ω | V ω ≤ q}) : MeasurableSet[lineFilt 𝒢L a V hA q] D := by
  refine ⟨hD, fun t => ?_⟩
  have e : D ∩ liveLine a V q t = ∅ := by
    ext ω
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hωD hl
    exact absurd ((hl.1.trans_lt hl.2).trans_le (hDV hωD)) (lt_irrefl _)
  rw [e]
  exact @MeasurableSet.empty _ (𝒢L t)

/-- **The lifetime is a stopping time of the line filtration.** -/
theorem isStoppingTime_lineFilt (hV : Measurable V) : IsStoppingTime (lineFilt 𝒢L a V hA) V := fun q => by
  show MeasurableSet[lineFilt 𝒢L a V hA q] {ω | V ω ≤ (q : ℝ≥0∞)}
  exact measurableSet_lineFilt_of_subset_stop (measurableSet_le hV measurable_const) fun _ h => h

/-- An event whose cuts by `{q ≤ a t}` are line events intersected with a `𝒢L t`-event is in the line filtration. -/
theorem measurableSet_lineFilt_of_inter {q : ℝ≥0} {D : Set Ω} (hD : MeasurableSet D)
    (h : ∀ t, MeasurableSet[𝒢L t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}))
    (hV : ∀ t, MeasurableSet[𝒢L t] {ω | a t ω < V ω}) : MeasurableSet[lineFilt 𝒢L a V hA q] D := by
  refine ⟨hD, fun t => ?_⟩
  have e : D ∩ liveLine a V q t = (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}) ∩ {ω | a t ω < V ω} := by
    ext ω
    simp only [liveLine, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [e]
  exact (h t).inter (hV t)

/-- **The capped pieces**: for `0 < q`, an event of the line filtration at `q`, cut by `{q ≤ capClock a N t}` and the
line safe event of the capped clock with the capped lifetime, is a `𝒢L t`-event when that safe event is one. -/
theorem measurableSet_capPiece_lineFilt {W : ℝ≥0 → Ω → ℝ} {q : ℝ≥0} {D : Set Ω}
    (hD : MeasurableSet[lineFilt 𝒢L a V hA q] D) (N : ℝ≥0) (C : Set ℂ) (t : ℝ≥0)
    (hS : MeasurableSet[𝒢L t] (lineSafe (BW1Chain.capClock a N) W (fun ω => min (V ω) N) C t)) :
    MeasurableSet[𝒢L t] (D ∩ {ω | q ≤ BW1Chain.capClock a N t ω} ∩
      lineSafe (BW1Chain.capClock a N) W (fun ω => min (V ω) N) C t) := by
  rcases le_or_gt q N with hqN | hNq
  · rw [BW1Chain.setOf_le_capClock_of_le hqN]
    have e : D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω} ∩
        lineSafe (BW1Chain.capClock a N) W (fun ω => min (V ω) N) C t =
        (D ∩ liveLine a V q t) ∩ lineSafe (BW1Chain.capClock a N) W (fun ω => min (V ω) N) C t := by
      ext ω
      simp only [liveLine, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hωD, hq⟩, hS'⟩
        refine ⟨⟨hωD, hq, ?_⟩, hS'⟩
        exact (BW1Lines.coe_capClock_lt_min_iff.1 hS'.1).2
      · rintro ⟨⟨hωD, hq, -⟩, hS'⟩
        exact ⟨⟨hωD, hq⟩, hS'⟩
    rw [e]
    exact (hD.2 t).inter hS
  · have e : {ω | q ≤ BW1Chain.capClock a N t ω} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      refine lt_of_le_of_lt ?_ hNq
      rw [← ENNReal.coe_le_coe, BW1Chain.coe_capClock]
      exact min_le_right _ _
    rw [e, inter_empty, empty_inter]
    exact @MeasurableSet.empty _ (𝒢L t)

end InteractingSLE.Theorem14.GW4Fix.Mart
