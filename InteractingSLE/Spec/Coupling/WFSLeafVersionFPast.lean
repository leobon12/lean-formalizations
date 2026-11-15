/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafSurvEAssembly
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingaleGeneral
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Raw dyadic pasts and scalar versions

The past records only state samples through the given time. In particular it
does not read the history's lifetime coordinate. Null augmentation can be
removed before applying the existing Doob–Dynkin factorization theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique

/-- Dyadic state samples through `t`, with later samples masked by zero. -/
def samplePast {nL nR : ℕ} (t : ℝ≥0) (γ : HistorySpace nL nR) :
    (ℕ × ℕ) → DrivingValue nL nR :=
  fun p => if dyadicTime p ≤ t then γ.2 p else 0

/-- The raw dyadic past is Borel as a function of the full history. -/
theorem measurable_samplePast {nL nR : ℕ} (t : ℝ≥0) :
    Measurable (samplePast (nL := nL) (nR := nR) t) := by
  apply measurable_pi_iff.2
  intro p
  by_cases h : dyadicTime p ≤ t
  · simp only [samplePast, h, ↓reduceIte]
    exact (measurable_pi_apply p).comp measurable_snd
  · simpa only [samplePast, h, ↓reduceIte] using
      (measurable_const : Measurable fun _ : HistorySpace nL nR => (0 : DrivingValue nL nR))

/-- Equal samples through a given time give identical raw pasts. -/
theorem samplePast_congr {nL nR : ℕ} {γ δ : HistorySpace nL nR} {t : ℝ≥0}
    (h : ∀ p, dyadicTime p ≤ t → γ.2 p = δ.2 p) : samplePast t γ = samplePast t δ := by
  funext p
  dsimp only [samplePast]
  split_ifs with hp
  · exact h p hp
  · rfl

/-- The sigma algebra of the raw dyadic state past, excluding the lifetime mark. -/
@[instance_reducible]
def samplePastSigma {Ω : Type*} {nL nR : ℕ} (Y : Ω → HistorySpace nL nR)
    (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => samplePast t (Y ω)) inferInstance

/-- A measurable history map makes its raw past sigma algebra a sub-sigma algebra. -/
theorem samplePastSigma_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
    {Y : Ω → HistorySpace nL nR} (hY : Measurable Y) (t : ℝ≥0) : samplePastSigma Y t ≤ mΩ :=
  ((measurable_samplePast t).comp hY).comap_le

/-- Remove the null augmentation, then factor a real variable through the
observation. This reuses null-invariance of conditional expectation and Doob–Dynkin. -/
theorem exists_borel_factor_of_nullAugmented_comap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {β : Type*} [MeasurableSpace β] {Y : Ω → β} (hY : Measurable Y)
    {X : Ω → ℝ} (hX : Measurable[MeasurableSpace.comap Y inferInstance ⊔ nullSigma P] X)
    (hint : Integrable X P) :
    ∃ f : β → ℝ, Measurable f ∧ X =ᵐ[P] fun ω => f (Y ω) := by
  have hfix : P[X | MeasurableSpace.comap Y inferInstance ⊔ nullSigma P] = X :=
    condExp_of_stronglyMeasurable (sup_le hY.comap_le (MeasurableSpace.generateFrom_le fun _ hs => hs.1))
      hX.stronglyMeasurable hint
  have he : X =ᵐ[P] P[X | MeasurableSpace.comap Y inferInstance] := by
    have h := MathFin.ItoLocalMartingale.condExp_sup_nulls hY.comap_le hint
    change P[X | MeasurableSpace.comap Y inferInstance ⊔ nullSigma P] =ᵐ[P]
      P[X | MeasurableSpace.comap Y inferInstance] at h
    rwa [hfix] at h
  obtain ⟨f, hfm, hfe⟩ :=
    (stronglyMeasurable_condExp (μ := P) (m := MeasurableSpace.comap Y inferInstance)
      (f := X)).exists_eq_measurable_comp
  refine ⟨f, hfm.measurable, he.trans ?_⟩
  rw [hfe]
  rfl

end InteractingSLE.WFS
