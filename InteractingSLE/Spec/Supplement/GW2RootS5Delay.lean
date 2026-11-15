/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootS5Window
import InteractingSLE.Spec.Supplement.GW2RootK3Model

/-!
# Slow root stages delay every successful candidate by one capacity unit

Continuation of PROVE-T14-GW2ROOT2. Dense observations below the target band
exclude a successful continuous crossing before relative time one. A concrete
capacity-clock comparison then gives the root's required unit increment.
The actual relative clock and its identification with `capR` remain inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u v

namespace InteractingSLE.Theorem14.GW2TipSystem.RootS5

/-- Dense-time bounds, together with continuity only at a successful
candidate, prevent reaching the opposite band before relative time one.
The observation lifetime may be any buffer stop before the actual lifetime. -/
theorem one_le_of_dense_samples {D : Set ℝ≥0} (hD : Dense D)
    {f : ℝ≥0 → ℝ} {t : ℝ≥0} {L : ℝ≥0∞} {b : ℝ}
    (hf : ContinuousAt f t) (htL : (t : ℝ≥0∞) < L) (hband : b < f t)
    (hsamples : ∀ q ∈ D, q < 1 → (q : ℝ≥0∞) < L → f q ≤ b) :
    1 ≤ t := by
  by_contra hnot
  have ht1 : t < 1 := lt_of_not_ge hnot
  have hL : {q : ℝ≥0 | (q : ℝ≥0∞) < L} ∈ 𝓝 t :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds htL
  have hev := ((hf.eventually (lt_mem_nhds hband)).and (gt_mem_nhds ht1)).and hL
  obtain ⟨q, hqD, hq⟩ :=
    ((mem_closure_iff_frequently.1 (hD t)).and_eventually hev).exists
  exact (not_lt_of_ge (hsamples q hqD hq.1.2 hq.2)) hq.1.1

/-- The slow event of a restart window bounds the absolute driver before
time one. The additional hypotheses say that the restart is at zero and
the driver has not passed zero beforehand; outside `A` it never does so.
These pathwise identifications are not inferred from a coordinate-law equality. -/
theorem RestartWindow.driver_lt_of_mem_slowEvent {κ C : ℝ} {J : Set ℝ}
    (w : RestartWindow.{u} κ C J) (a : ℝ) {ω : w.e.Ω}
    (hslow : ω ∈ w.slowEvent)
    (hbefore : ∀ t : ℝ≥0, (t : ℝ≥0∞) < w.e.lifetime ω →
      t < (w.τ ω).untopA → a + w.e.W t ω ≤ 0)
    (hzero : ω ∈ w.A → a + w.e.W (w.τ ω).untopA ω = 0)
    (houtside : ω ∉ w.A → ∀ t : ℝ≥0, (t : ℝ≥0∞) < w.e.lifetime ω →
      a + w.e.W t ω ≤ 0)
    {t : ℝ≥0} (ht : t < 1) (htL : (t : ℝ≥0∞) < w.e.lifetime ω) :
    a + w.e.W t ω < 7 / 4 := by
  by_cases hA : ω ∈ w.A
  · have hsmall := hslow.resolve_left fun hnA => hnA hA
    by_cases htt : t < (w.τ ω).untopA
    · linarith only [hbefore t htL htt]
    · have hle : (w.τ ω).untopA ≤ t := le_of_not_gt htt
      have hu : t - (w.τ ω).untopA < 1 := (tsub_le_self).trans_lt ht
      have h := hsmall _ hu
      rw [add_tsub_cancel_of_le hle, abs_lt] at h
      linarith only [h.2, hzero hA]
  · linarith only [houtside hA t htL]

open Exist Staged StagedLaw Restart LQGMetric RootK3

variable {κ : ℝ} {hκ : 0 < κ} {h12p : Theorem12ParamStatement.{u}}
  {βA : BoundaryWord × ℝ × RecData → BoundaryWord}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {c₀ : BoundaryWord}
  {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Θ : Set ℝ} {Q : Set ℝ≥0} {s : ℝ≥0}
  {P : Measure Ω} {r : ScaledRootIdx Θ Q} {G : Set Ω}
  {Ξ : Type v} [MeasurableSpace Ξ]
  {d : StageModelData Ω Θ Q Ξ (rootSigma hκ h12p βA c₀ h W' ζ' s r)}

/-- The root unit clause follows from observed slow paths and an actual
capacity clock. Its hypotheses concern raw paths and clocks under `P`;
neither path regularity nor this geometric identification is supplied by
the model's driving marginal. Every passed candidate is handled at once. -/
theorem ae_unit_of_observed_clock
    {D : Set ℝ≥0} (hD : Dense D)
    (Y : List (EntryIdx Θ Q) → ℕ → Ω → ℝ≥0 → ℝ)
    (L : List (EntryIdx Θ Q) → ℕ → Ω → ℝ≥0∞)
    (clock : List (EntryIdx Θ Q) → ℕ → Q → Ω → ℝ≥0)
    (hSlowObs : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
      d.sample l a ω ∈ d.slow l a → ∀ t ∈ D, t < 1 →
        (t : ℝ≥0∞) < L l a ω → Y l a ω t ≤ 7 / 4)
    (hClock : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l → ∀ q : Q,
      ω ∈ d.tests l a q →
        ContinuousAt (Y l a ω) (clock l a q ω) ∧
        (clock l a q ω : ℝ≥0∞) < L l a ω ∧
        7 / 4 < Y l a ω (clock l a q ω) ∧
        capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + clock l a q ω ≤
          capR hκ h12p βA b jumps c₀ h W' ζ' s r ((d.ang a, q) :: l) ω) :
    ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
      d.sample l a ω ∈ d.slow l a → ∀ q : Q, ω ∈ d.tests l a q →
        capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + 1 ≤
          capR hκ h12p βA b jumps c₀ h W' ζ' s r ((d.ang a, q) :: l) ω := by
  intro l a
  filter_upwards [hSlowObs l a, hClock l a] with ω hωslow hωclock hωA hωS q hωT
  obtain ⟨hc, htL, hband, hcap⟩ := hωclock hωA q hωT
  have ht := one_le_of_dense_samples hD hc htL hband (hωslow hωA hωS)
  have htR : (1 : ℝ) ≤ clock l a q ω := by exact_mod_cast ht
  exact (add_le_add le_rfl htR).trans hcap

end InteractingSLE.Theorem14.GW2TipSystem.RootS5
