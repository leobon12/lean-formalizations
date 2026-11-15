/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2FbConfig
import InteractingSLE.Spec.Supplement.SB2KdInputs

/-!
# SB2(1)'s chain record: the physical Loewner driver of the shifted flow

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The chain record `Tc.IsSB2LineChainAt`
contains a GLOBAL Loewner trace `IsLoewnerTrace w ηw` of a continuous driver whose trace is the shifted flow before
the horizon. Ingredients:

* `ae_flowDriver`: almost surely the upper flow `η − u` is a generating trace up to its lifetime `ζ` of a driver
  continuous before `ζ` and starting at `0` (`IsFlowLine`);
* **`exists_physDriver`** (deterministic): freezing such a driver after a horizon `T₁ < ζ`
  (`GW2Fb.exists_frozen_generatingTrace`) gives a continuous driver from `0` with a global Loewner trace equal to the
  flow on `[0, T₁]` (`isLoewnerTrace_of_isGeneratingTrace`).

Deterministic in the data apart from `ae_flowDriver`; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ve

open Lv Exist.Staged Exist.StagedLaw

/-- **The flow's driver**: almost surely `η − u` is a generating trace up to `ζ` of a driver continuous before `ζ`,
from `0`. -/
theorem ae_flowDriver {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ∃ w : ℝ≥0 → ℝ, ContinuousOn w {t | (t : ℝ≥0∞) < ζ ω} ∧ w 0 = 0 ∧
      IsGeneratingTrace w (ζ ω) (fun t => η ω t - u) := by
  rcases HP.flow with ⟨h', 𝓕, W, VL, VR, B, -, hopt, hgen⟩
  filter_upwards [hgen, hopt.1.2.2.2.2] with ω hg hp
  exact ⟨fun t => W t ω, hp.2.2.2.1, hp.1, hg⟩

/-- **A global physical Loewner trace agreeing with the flow up to a horizon before its lifetime.** -/
theorem exists_physDriver {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w ζ α)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {T₁ : ℝ≥0} (hT₁ : (T₁ : ℝ≥0∞) < ζ) :
    ∃ (W : ℝ → ℝ) (ηw : ℝ → ℂ), Continuous W ∧ W 0 = 0 ∧ IsLoewnerTrace W ηw ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ T₁ → ηw r = α r.toNNReal := by
  obtain ⟨w', α', t₂, h12, -, hw'c, hw'0, hgen', -, hαe⟩ := GW2Fb.exists_frozen_generatingTrace hα hw hw0 hT₁
  refine ⟨fun s => w' s.toNNReal, fun s => α' s.toNNReal, hw'c.comp continuous_real_toNNReal, by simp [hw'0],
    isLoewnerTrace_of_isGeneratingTrace hgen', fun r hr hrT => hαe _ ?_⟩
  exact (Real.toNNReal_le_toNNReal hrT).trans (by simp [h12.le])

end InteractingSLE.Theorem14.SB.Ve
