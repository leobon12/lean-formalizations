/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockMeasClock

/-!
# The deterministic clock hypotheses hold almost surely for flow lines

Packet PROVE-RESTART-CPL5. A flow line is almost surely a simple generating trace of a driver continuous before its
lifetime and vanishing at `0`, seeded at its real start (`IsPathGood`, `ae_isPathGood_of_isFlowLine`; injectivity is
the proved Aux. lemma 25, `Theorem15.aux25Statement`). At a first contact of two such paths with Lemma 7.7's
confinement, the standing hypotheses of the clock theorem (`IsContinuationGood`) follow
(`isContinuationGood_of_isPathGood`), and they only read the paths on their available intervals
(`IsContinuationGood.congr`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

/-- A simple generating trace seeded at `x`, with a driver continuous before the lifetime and vanishing at `0`. -/
def IsPathGood (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (x : ℝ) : Prop :=
  InjOn η {t | (t : ℝ≥0∞) ≤ ζ} ∧ ∃ w : ℝ≥0 → ℝ, ContinuousOn w {s | (s : ℝ≥0∞) < ζ} ∧ w 0 = 0 ∧
    IsGeneratingTrace w ζ fun t => η t - x

/-- **Flow lines are almost surely good paths** (Aux. lemma 25 for injectivity). -/
theorem ae_isPathGood_of_isFlowLine (hA : Theorem15.Aux25Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ}
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) : ∀ᵐ ω ∂P, IsPathGood (η ω) (ζ ω) x := by
  have hinj := Theorem15.ae_injOn_of_isFlowLine hA hκ hκ4 hη
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hcoup, htr⟩ := hη
  filter_upwards [hinj, htr, hcoup.1.2.2.2.2] with ω hi hωt hωp
  exact ⟨hi, fun t => W t ω, hωp.2.2.2.1, hωp.1, hωt⟩

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0} {x₁ x₂ : ℝ}

theorem IsPathGood.continuousOn {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x) :
    ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ} := by
  obtain ⟨-, w, -, -, hg⟩ := hp
  refine (hg.2.1.add (continuousOn_const (c := (x : ℂ)))).congr fun t _ => ?_
  simp

theorem IsPathGood.seed {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x) : (η 0).im = 0 := by
  obtain ⟨-, w, -, -, hg⟩ := hp
  have h0 : η 0 - x = 0 := hg.1
  rw [sub_eq_zero.1 h0]; simp

theorem IsPathGood.hcapSet {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ) : ConformalImage.hcapSet (fillH (η '' Icc 0 s)) = 2 * s := by
  obtain ⟨-, w, hw, hw0, hg⟩ := hp
  exact IsGeneratingTrace.hcapSet_fillH_add hg hw hw0 hs

/-- **The clock hypotheses at a first contact of two good paths with confinement.** -/
theorem isContinuationGood_of_isPathGood (hp₁ : IsPathGood η₁ ζ₁ x₁) (hp₂ : IsPathGood η₂ ζ₂ x₂)
    (hfc : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀)
    (hconf : ∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ closure (activeDomain η₁ s₀ η₂ t₀)) :
    IsContinuationGood η₁ ζ₁ s₀ η₂ ζ₂ t₀ := by
  obtain ⟨hi₁, w, hw, hw0, hg⟩ := id hp₁
  exact ⟨hfc, hi₁, hp₂.1, hp₁.continuousOn, hp₂.continuousOn, hp₁.seed, hconf,
    fun u s hus hsζ => IsGeneratingTrace.mem_closure_of_lt_add hg hw hw0 hus hsζ,
    fun a b hab hbζ => IsGeneratingTrace.exists_mem_H_add hg hw hw0 hab hbζ⟩

/-- The clock hypotheses only read the paths on their available intervals. -/
theorem IsContinuationGood.congr {η₁' η₂' : ℝ≥0 → ℂ} (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁' s = η₁ s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂' t = η₂ t) (hg : IsContinuationGood η₁ ζ₁ s₀ η₂ ζ₂ t₀) :
    IsContinuationGood η₁' ζ₁ s₀ η₂' ζ₂ t₀ := by
  have hfc := hg.firstContact
  have hD := activeDomain_congr ha₁ ha₂ hfc.1 hfc.2.1
  refine ⟨(isFirstContact_congr ha₁ ha₂).2 hfc, hg.injOn₁.congr fun s hs => (ha₁ s hs).symm,
    hg.injOn₂.congr fun t ht => (ha₂ t ht).symm, hg.continuousOn₁.congr fun s hs => ha₁ s hs,
    hg.continuousOn₂.congr fun t ht => ha₂ t ht, by rw [ha₁ 0 (by simp)]; exact hg.seed₁,
    fun s hs hsζ => by rw [ha₁ s hsζ, hD]; exact hg.conf s hs hsζ, fun u s hus hsζ => ?_,
    fun a b hab hbζ => ?_⟩
  · have huζ : (u : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hus.le).trans hsζ
    rw [ha₁ s hsζ, image_Icc_congr ha₁ huζ]
    exact hg.tip u s hus hsζ
  · obtain ⟨s, hs, hsH⟩ := hg.dense a b hab hbζ
    exact ⟨s, hs, by rw [ha₁ s ((ENNReal.coe_le_coe.2 hs.2.le).trans hbζ)]; exact hsH⟩

end Restart

end InteractingSLE
