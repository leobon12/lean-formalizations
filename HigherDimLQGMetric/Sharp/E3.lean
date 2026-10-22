import HigherDimLQGMetric.Sharp.ComparisonCriterion
import HigherDimLQGMetric.Sharp.TightWeak
import HigherDimLQGMetric.Metric.WeylAxioms

/-!
# Uniqueness comparison in the sharp weak class

Uniform shell bounds give a comparison event above the probability threshold
of the shell criterion. The common sharp normalizer cancels exactly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem sharp_shell_probability (hd : 3 ≤ d) {ξ Q : ℝ}
    {D₁ D₂ : DistRd d → ContMetric d}
    (hD₁ : IsSharpWeakExpMetric d ξ Q D₁)
    (hD₂ : IsSharpWeakExpMetric d ξ Q D₂)
    {p₀ : ℝ} (hp₀ : p₀ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d),
        IsWholeSpaceLGF h P → ∀ z : Rd d, ∀ r : ℝ, 0 < r →
        ∃ E : Set Ω,
          AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r))) E ∧
          E =ᵐ[P] {ω | sphereDiam (D₂ (h ω)) z r ≤
            ENNReal.ofReal C * acrossDist (D₁ (h ω)) z (r / 2) r} ∧
          p₀ ≤ (P E).toReal := by
  let δ : ℝ := (1 - p₀) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨a, ha, hLower⟩ := hD₁.scaledAcrossLower (by omega : 2 ≤ d)
    (ε := ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨B, hB, hUpper⟩ := hD₂.scaledSphereDiamUpper (by omega : 2 ≤ d)
    (ε := ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  let C := max 1 (B / a)
  have hC : 1 ≤ C := le_max_left _ _
  have hBa : B ≤ C * a := by
    have hq : B / a ≤ C := le_max_right _ _
    exact (div_le_iff₀ ha).1 (by simpa only [mul_comm] using hq)
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh z r hr
  let A : Set Ω := {ω | acrossDist
    (weakScaledMetric ξ D₁ (fun s => s ^ (ξ * Q)) (h ω) hr z (hD₁.c_pos r hr))
      0 (1 / 2) 1 < ENNReal.ofReal a}
  let Bbad : Set Ω := {ω | ENNReal.ofReal B < sphereDiam
    (weakScaledMetric ξ D₂ (fun s => s ^ (ξ * Q)) (h ω) hr z (hD₂.c_pos r hr))
      0 1}
  have hA : P A < ENNReal.ofReal δ := hLower P h hh r hr z
  have hBb : P Bbad < ENNReal.ofReal δ := hUpper P h hh r hr z
  let G : Set Ω := {ω | sphereDiam (D₂ (h ω)) z r ≤
    ENNReal.ofReal C * acrossDist (D₁ (h ω)) z (r / 2) r}
  obtain ⟨E, hEm, hEeq⟩ :=
    shellCompare_aeEventIn hD₁ hD₂ (by omega : 2 ≤ d) hh z hr C
  have hpoint (ω : Ω) (hωA : ω ∉ A) (hωB : ω ∉ Bbad) : ω ∈ G := by
    have hl : ENNReal.ofReal a ≤ acrossDist
        (weakScaledMetric ξ D₁ (fun s => s ^ (ξ * Q)) (h ω) hr z
          (hD₁.c_pos r hr)) 0 (1 / 2) 1 := le_of_not_gt hωA
    have hu : sphereDiam
        (weakScaledMetric ξ D₂ (fun s => s ^ (ξ * Q)) (h ω) hr z
          (hD₂.c_pos r hr)) 0 1 ≤ ENNReal.ofReal B := le_of_not_gt hωB
    have hs : sphereDiam
        (weakScaledMetric ξ D₂ (fun s => s ^ (ξ * Q)) (h ω) hr z
          (hD₂.c_pos r hr)) 0 1 ≤
        ENNReal.ofReal C * acrossDist
          (weakScaledMetric ξ D₁ (fun s => s ^ (ξ * Q)) (h ω) hr z
            (hD₁.c_pos r hr)) 0 (1 / 2) 1 := by
      calc
        _ ≤ ENNReal.ofReal B := hu
        _ ≤ ENNReal.ofReal (C * a) := ENNReal.ofReal_le_ofReal hBa
        _ = ENNReal.ofReal C * ENNReal.ofReal a := by
          rw [ENNReal.ofReal_mul (by linarith : 0 ≤ C)]
        _ ≤ _ := by gcongr
    rw [weakScaledMetric_sphereDiam, weakScaledMetric_acrossDist] at hs
    let q : ℝ≥0∞ := ENNReal.ofReal
      (((r ^ (ξ * Q))⁻¹) * Real.exp (-ξ * sphereAvg (h ω) r z))
    have hq0 : q ≠ 0 := by
      apply (ENNReal.ofReal_pos.2 ?_).ne'
      exact mul_pos (inv_pos.2 (hD₁.c_pos r hr)) (Real.exp_pos _)
    have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
    change q * sphereDiam (D₂ (h ω)) z r ≤
      ENNReal.ofReal C * (q * acrossDist (D₁ (h ω)) z (r / 2) r) at hs
    change sphereDiam (D₂ (h ω)) z r ≤
      ENNReal.ofReal C * acrossDist (D₁ (h ω)) z (r / 2) r
    rw [mul_left_comm (ENNReal.ofReal C) q] at hs
    exact (ENNReal.mul_le_mul_iff_right hq0 hqtop).1 hs
  have hEambient : MeasurableSet E :=
    fieldSigma0_le_ambient hh.measurable _ E hEm
  have hEc : P Eᶜ < ENNReal.ofReal (2 * δ) := by
    have hmono : P Eᶜ ≤ P (A ∪ Bbad) := by
      apply measure_mono_ae
      filter_upwards [hEeq] with ω heq hω
      by_contra hnot
      simp only [mem_union, not_or] at hnot
      exact hω (heq.mp (hpoint ω hnot.1 hnot.2))
    calc
      P Eᶜ ≤ P (A ∪ Bbad) := hmono
      _ ≤ P A + P Bbad := measure_union_le _ _
      _ < ENNReal.ofReal δ + ENNReal.ofReal δ := ENNReal.add_lt_add hA hBb
      _ = ENNReal.ofReal (2 * δ) := by
        rw [show 2 * δ = δ + δ by ring, ENNReal.ofReal_add hδ.le hδ.le]
  have hEcr : (P Eᶜ).toReal < 2 * δ := ENNReal.toReal_lt_of_lt_ofReal hEc
  have hsum := probReal_add_probReal_compl hEambient (μ := P)
  change (P E).toReal + (P Eᶜ).toReal = 1 at hsum
  have hp : p₀ ≤ (P E).toReal := by dsimp [δ] at hEcr; linarith
  exact ⟨E, ⟨E, hEm, Filter.EventuallyEqSet.refl (ae P) E⟩, hEeq.symm, hp⟩

/-- (E3): two sharp weak assignments at the same exponent are comparable by
a deterministic constant on every whole-space LGF plus a continuous field. -/
theorem e3_sharp (hA1 : ShellInputA1 d) (hd : 3 ≤ d) {ξ Q : ℝ} (_hξ : 0 < ξ)
    {D D' : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hD' : IsSharpWeakExpMetric d ξ Q D') :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsLGFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ u v : Rd d,
        (D' (h ω)).1 (u, v) ≤ C * (D (h ω)).1 (u, v) ∧
          (D (h ω)).1 (u, v) ≤ C * (D' (h ω)).1 (u, v) := by
  obtain ⟨p₀, hp₀, Hcriterion⟩ := comparison_criterion_aeLength hA1 hd
  obtain ⟨C₁, hC₁, H₁⟩ := sharp_shell_probability hd hD hD' hp₀
  obtain ⟨C₂, hC₂, H₂⟩ := sharp_shell_probability hd hD' hD hp₀
  let C := max C₁ C₂
  have hC : 1 ≤ C := hC₁.trans (le_max_left _ _)
  have hCpos : 0 < C := by linarith
  have hWhole : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ᵐ ω ∂P, ∀ u v : Rd d,
        (D' (h ω)).1 (u, v) ≤ C * (D (h ω)).1 (u, v) ∧
          (D (h ω)).1 (u, v) ≤ C * (D' (h ω)).1 (u, v) := by
    intro Ω _ P _ h hh
    have hLenD := hD.length P h hh.isLGFPlusCont
    have hLenD' := hD'.length P h hh.isLGFPlusCont
    have hcmp₁ := Hcriterion P h hh (fun ω => D (h ω)) (fun ω => D' (h ω))
      C₁ (by linarith) hLenD hLenD' (H₁ P h hh)
    have hcmp₂ := Hcriterion P h hh (fun ω => D' (h ω)) (fun ω => D (h ω))
      C₂ (by linarith) hLenD' hLenD (H₂ P h hh)
    filter_upwards [hcmp₁, hcmp₂] with ω hw₁ hw₂
    intro u v
    constructor
    · exact (hw₁ u v).trans (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂)
        ((D (h ω)).nonneg u v))
    · exact (hw₂ u v).trans (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂)
        ((D' (h ω)).nonneg u v))
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh
  obtain ⟨_, f, _, h0lgf⟩ := hh
  let h0 : Ω → DistRd d := fun ω => h ω - ofCont (f ω)
  have hcmp := hWhole P h0 h0lgf
  have htrans₁ := hD.ae_apply_compare hD' h0lgf.isLGFPlusCont
    (c := 0) (C := C) le_rfl hCpos (by
      filter_upwards [hcmp] with ω hw
      intro u v
      exact ⟨by simpa using (D' (h0 ω)).nonneg u v, (hw u v).1⟩)
  have htrans₂ := hD'.ae_apply_compare hD h0lgf.isLGFPlusCont
    (c := 0) (C := C) le_rfl hCpos (by
      filter_upwards [hcmp] with ω hw
      intro u v
      exact ⟨by simpa using (D (h0 ω)).nonneg u v, (hw u v).2⟩)
  filter_upwards [htrans₁, htrans₂] with ω hw₁ hw₂
  intro u v
  have h₁ := (hw₁ (f ω) u v).2
  have h₂ := (hw₂ (f ω) u v).2
  simpa only [addFun, sub_add_cancel] using And.intro h₁ h₂

end HigherDimLQGMetric
