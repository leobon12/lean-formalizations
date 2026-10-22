import HigherDimLQGMetric.Bilip.Main
import HigherDimLQGMetric.Sharp.TightShell
import HigherDimLQGMetric.Sharp.TightWeak

/-!
# Uniform sphere and crossing bounds from tight metric laws

This is the tightness argument of MA5 A20(b), at the origin.  Translation of
the joint field/metric law transports the same constant to other centres.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

theorem bilip_tightOver_congr_on {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}
    (hXY : ∀ r ∈ S, X r = Y r) (hT : TightOver P X S) :
    TightOver P Y S := by
  have hset : {μ | ∃ r ∈ S, μ = P.map (X r)} =
      {μ | ∃ r ∈ S, μ = P.map (Y r)} := by
    ext μ
    constructor
    · rintro ⟨r, hr, hμ⟩
      exact ⟨r, hr, by simpa only [hXY r hr] using hμ⟩
    · rintro ⟨r, hr, hμ⟩
      exact ⟨r, hr, by simpa only [← hXY r hr] using hμ⟩
  have hprob : {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X r)} =
      {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (Y r)} := by
    ext ν
    constructor
    · rintro ⟨r, hr, hν⟩
      exact ⟨r, hr, by simpa only [hXY r hr] using hν⟩
    · rintro ⟨r, hr, hν⟩
      exact ⟨r, hr, by simpa only [← hXY r hr] using hν⟩
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rw [← hXY r hr]
    exact hT.1 r hr
  · rw [← hset]
    exact hT.2.1
  · intro μ hμ
    exact hT.2.2 μ (by simpa only [hprob] using hμ)

/-- A single deterministic constant controls the two shell functionals,
uniformly over every index in a tight family of length metrics. -/
theorem bilip_uniformShellBounds {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℝ → Ω → ContMetric d) (S : Set ℝ)
    (hT : TightOver P (fun r ω => (G r ω).1) S)
    (hLen : ∀ r ∈ S, ∀ᵐ ω ∂P, (G r ω).IsLength)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ A : ℝ, 1 < A ∧ ∀ r ∈ S,
      P {ω | acrossDist (G r ω) 0 (1 / 2) 1 < ENNReal.ofReal A⁻¹} < η ∧
      P {ω | ENNReal.ofReal A < sphereDiam (G r ω) 0 1} < η := by
  obtain ⟨a, ha, hlo⟩ := TightOver.across_lower hT hη
  obtain ⟨b, hb, hup⟩ := TightOver.sphereDiam_upper hd hT hLen hη
  let A : ℝ := max 2 (max a⁻¹ b)
  have hA : 1 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hAi : A⁻¹ ≤ a := by
    have haA : a⁻¹ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
    simpa only [one_div] using
      ((one_div_le (by linarith : 0 < A) ha).mpr (by simpa only [one_div] using haA))
  have hbA : b ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A, hA, ?_⟩
  intro r hr
  constructor
  · refine lt_of_le_of_lt (measure_mono ?_) (hlo r hr)
    intro ω hω
    exact lt_of_lt_of_le hω (ENNReal.ofReal_le_ofReal hAi)
  · refine lt_of_le_of_lt (measure_mono ?_) (hup r hr)
    intro ω hω
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hbA) hω

/-- A20(b) at the origin, in the normalization used by `L6f_tightScales`.
The same constant works at every scale. -/
theorem bilip_uniformShellBounds_limit {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : ℝ) (h : Ω → DistRd d)
    (D : Ω → ContMetric d) (c : ℝ → ℝ)
    (hc : ∀ r : ℝ, 0 < r → 0 < c r)
    (hT : TightFamily P
      (fun r ω => normalizedAtScale ξ (fun _ => D ω) c (h ω) r) (Ioi 0))
    (hLen : ∀ᵐ ω ∂P, (D ω).IsLength)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℝ, 0 < r →
      P {ω | ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r 0)) *
          acrossDist (D ω) 0 (r / 2) r < ENNReal.ofReal A⁻¹} < η ∧
      P {ω | ENNReal.ofReal A <
          ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r 0)) *
            sphereDiam (D ω) 0 r} < η := by
  let G : ℝ → Ω → ContMetric d := fun r ω =>
    if hr : 0 < r then
      weakScaledMetric ξ (fun _ => D ω) c (h ω) hr 0 (hc r hr)
    else D ω
  have hGfun (r : ℝ) (hr : 0 < r) :
      (fun ω => (G r ω).1) =
        (fun ω => normalizedAtScale ξ (fun _ => D ω) c (h ω) r) := by
    funext ω
    dsimp [G]
    rw [dite_eq_left hr]
    ext p
    simp only [weakScaledMetric_apply, scaledField_apply, normalizedAtScale,
      ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul,
      add_zero]
    rfl
  have hTnorm : TightOver P
      (fun r ω => normalizedAtScale ξ (fun _ => D ω) c (h ω) r) (Ioi 0) :=
    ⟨hT.1, hT.2.1, fun μ hμ => (hT.2.2 μ hμ).mono fun _ hD => hD.1⟩
  have hTG : TightOver P (fun r ω => (G r ω).1) (Ioi 0) :=
    bilip_tightOver_congr_on (fun r hr => (hGfun r hr).symm) hTnorm
  have hGLen : ∀ r ∈ Ioi (0 : ℝ), ∀ᵐ ω ∂P, (G r ω).IsLength := by
    intro r hr
    have hr0 : 0 < r := hr
    filter_upwards [hLen] with ω hω
    dsimp [G]
    rw [dite_eq_left hr0]
    exact weakScaledMetric_isLength ξ (fun _ => D ω) c (h ω) hr0 0 (hc r hr0) hω
  obtain ⟨A, hA, hB⟩ := bilip_uniformShellBounds hd P G (Ioi 0) hTG hGLen hη
  refine ⟨A, hA, ?_⟩
  intro r hr
  obtain ⟨hlo, hup⟩ := hB r hr
  constructor
  · convert hlo using 1
    congr 1
    ext ω
    dsimp [G]
    rw [dite_eq_left hr, weakScaledMetric_acrossDist]
  · convert hup using 1
    congr 1
    ext ω
    dsimp [G]
    rw [dite_eq_left hr, weakScaledMetric_sphereDiam]

end HigherDimLQGMetric
