import HigherDimLQGMetric.Sharp.W2GoodScales
import HigherDimLQGMetric.Sharp.TightWeak
import HigherDimLQGMetric.Sharp.ShellMeas

/-!
# Field-measurable upper shell events

A normalized sphere-diameter event has a version measurable with respect to the
mean-zero field on the surrounding annulus. This permits the shell decoupling
bound to be applied to upper diameter events.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The upper sphere-diameter event is measurable modulo constants. -/
theorem w2_weakSphere_event_aeEventIn
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (z : Rd d) {r : ℝ} (hr : 0 < r) (C : ℝ) :
    AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r)))
      {ω | sphereDiam (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)) 0 1 ≤
        ENNReal.ofReal C} := by
  obtain ⟨Fdiam, _, hFm, _, hFae⟩ := hD.exists_shellVersions hd hh z hr
  let q : ℝ≥0∞ := ENNReal.ofReal ((c r)⁻¹)
  let F : Set Ω := {ω | q * Fdiam ω ≤ ENNReal.ofReal C}
  have hF : MeasurableSet[fieldSigma0 h (ann z (r / 4) (4 * r))] F :=
    measurableSet_le (measurable_const.mul hFm) measurable_const
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFae] with ω hω
  apply propext
  change sphereDiam (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)) 0 1 ≤
      ENNReal.ofReal C ↔ q * Fdiam ω ≤ ENNReal.ofReal C
  rw [weakScaledMetric_sphereDiam, hω.1]
  have hc : 0 ≤ (c r)⁻¹ := (inv_pos.mpr (hD.c_pos r hr)).le
  rw [ENNReal.ofReal_mul hc]
  simp only [q, mul_assoc]

/-- The source's normalized good sphere event. -/
def w2GoodSphere (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) (C : ℝ) (z : Rd d) (r : ℝ) : Prop :=
  sphereDiam (D g) z r ≤ ENNReal.ofReal (C * sNorm ξ Q g r z)

/-- Physical and scaled forms of the good sphere event agree. -/
theorem w2GoodSphere_iff_scaled {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (g : DistRd d) (C : ℝ)
    (hC : 0 ≤ C) (z : Rd d) {r : ℝ} (hr : 0 < r) :
    w2GoodSphere ξ Q D g C z r ↔
      sphereDiam (weakScaledMetric ξ D (fun s => s ^ (ξ * Q)) g hr z
        (hD.c_pos r hr)) 0 1 ≤ ENNReal.ofReal C := by
  let a : ℝ := sNorm ξ Q g r z
  have ha : 0 < a := mul_pos (hD.c_pos r hr) (Real.exp_pos _)
  let q : ℝ≥0∞ := ENNReal.ofReal a
  let qi : ℝ≥0∞ := ENNReal.ofReal a⁻¹
  have hqi : q * qi = 1 := by
    dsimp [q, qi]
    rw [← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one]
  have hfac : (r ^ (ξ * Q))⁻¹ * Real.exp (-ξ * sphereAvg g r z) = a⁻¹ := by
    dsimp [a, sNorm]
    rw [show -ξ * sphereAvg g r z = -(ξ * sphereAvg g r z) by ring,
      Real.exp_neg, mul_inv_rev]
    ring
  have hprod : ENNReal.ofReal (C * a) = ENNReal.ofReal C * q := by
    dsimp [q]
    rw [ENNReal.ofReal_mul hC]
  change sphereDiam (D g) z r ≤ ENNReal.ofReal (C * a) ↔ _
  rw [weakScaledMetric_sphereDiam, hfac]
  change sphereDiam (D g) z r ≤ ENNReal.ofReal (C * a) ↔
    qi * sphereDiam (D g) z r ≤ ENNReal.ofReal C
  rw [hprod]
  have hq0 : q ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hqt : q ≠ ∞ := ENNReal.ofReal_ne_top
  have hcancel : q * (qi * sphereDiam (D g) z r) = sphereDiam (D g) z r := by
    rw [← mul_assoc, hqi, one_mul]
  constructor
  · intro h
    apply (ENNReal.mul_le_mul_iff_right hq0 hqt).1
    rw [hcancel, mul_comm q]
    exact h
  · intro h
    have hm := (ENNReal.mul_le_mul_iff_right hq0 hqt).2 h
    rwa [hcancel, mul_comm q] at hm

/-- The physical good sphere event is measurable modulo constants. -/
theorem w2GoodSphere_aeEventIn
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (z : Rd d) {r : ℝ} (hr : 0 < r) {C : ℝ} (hC : 0 ≤ C) :
    AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r)))
      {ω | w2GoodSphere ξ Q D (h ω) C z r} := by
  obtain ⟨F, hFm, hEq⟩ := w2_weakSphere_event_aeEventIn hD hd hh z hr C
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hEq] with ω hω
  apply propext
  exact (w2GoodSphere_iff_scaled hD (h ω) C hC z hr).trans (Iff.of_eq hω)

/-- Uniform positive probability of a good upper sphere, for any threshold `p < 1`. -/
theorem w2_goodSphere_prob_ge {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d)
    {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ z : Rd d, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal p ≤ P {ω | w2GoodSphere ξ Q D (h ω) C z r} := by
  let δ : ℝ := (1 - p) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hp]
  obtain ⟨C, hC, hUpper⟩ := hD.scaledSphereDiamUpper hd
    (ε := ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh z r hr
  let G : Set Ω := {ω | w2GoodSphere ξ Q D (h ω) C z r}
  let B : Set Ω := {ω | ENNReal.ofReal C < sphereDiam
    (weakScaledMetric ξ D (fun s => s ^ (ξ * Q)) (h ω) hr z (hD.c_pos r hr)) 0 1}
  obtain ⟨F, hFm, hEq⟩ := w2GoodSphere_aeEventIn hD hd hh z hr hC.le
  have hFambient : MeasurableSet F := fieldSigma0_le_ambient hh.measurable _ F hFm
  have hEc : P Fᶜ < ENNReal.ofReal δ := by
    have hmono : P Fᶜ ≤ P B := by
      apply measure_mono_ae
      filter_upwards [hEq] with ω heq hω
      by_contra hnot
      have hscaled : sphereDiam
        (weakScaledMetric ξ D (fun s => s ^ (ξ * Q)) (h ω) hr z (hD.c_pos r hr)) 0 1 ≤
          ENNReal.ofReal C := le_of_not_gt hnot
      have hgood : ω ∈ G := (w2GoodSphere_iff_scaled hD (h ω) C hC.le z hr).2 hscaled
      exact hω (heq.mp hgood)
    exact lt_of_le_of_lt hmono (hUpper P h hh r hr z)
  have hEcr : (P Fᶜ).toReal < δ := ENNReal.toReal_lt_of_lt_ofReal hEc
  have hsum := probReal_add_probReal_compl hFambient (μ := P)
  change (P F).toReal + (P Fᶜ).toReal = 1 at hsum
  have hpF : p ≤ (P F).toReal := by dsimp [δ] at hEcr; linarith only [hEcr, hsum, hp]
  have hF : ENNReal.ofReal p ≤ P F := by
    rw [← ofReal_measureReal (measure_ne_top P F)]
    exact ENNReal.ofReal_le_ofReal hpF
  change ENNReal.ofReal p ≤ P G
  rw [measure_congr hEq]
  exact hF

/-- Uniform upper-diameter good scales on a translated grid. -/
theorem w2_goodSphere_everywhere (hA1 : ShellInputA1 d) (hd : 3 ≤ d)
    {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {M : ℝ} (hM : 0 < M) :
    ∃ C K : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ z : Rd d, ∀ ε ∈ Ioo (0 : ℝ) 1,
        P {ω | ∃ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
          Metric.ball (0 : Rd d) (𝕣 / ε),
          ∀ k : ℕ, ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k → 𝕣 / 2 ^ k ≤ ε * 𝕣 →
            ¬ w2GoodSphere ξ Q D (h ω) C (z + w) (𝕣 / 2 ^ k)} ≤
          ENNReal.ofReal (K * ε ^ M) := by
  obtain ⟨p, hp, K, hGrid⟩ := w2_goodScales_shifted hA1 hd hM
  obtain ⟨C, hC, hPoint⟩ := w2_goodSphere_prob_ge hD (by omega : 2 ≤ d) hp
  refine ⟨C, K, hC, ?_⟩
  intro Ω _ P _ h hh 𝕣 h𝕣 z ε hε
  let E : Rd d → ℝ → Set Ω := fun w r =>
    {ω | w2GoodSphere ξ Q D (h ω) C w r}
  have hE : ∀ w r, 0 < r → AEEventIn P
      (fieldSigma0 h (ann w (r / 4) (4 * r))) (E w r) := by
    intro w r hr
    exact w2GoodSphere_aeEventIn hD (by omega : 2 ≤ d) hh w hr hC.le
  have hpE : ∀ w r, 0 < r → ENNReal.ofReal p ≤ P (E w r) := by
    intro w r hr
    exact hPoint P h hh w r hr
  have hbound := hGrid P h hh E hE hpE 𝕣 h𝕣 z ε hε
  simpa only [E, Set.mem_ofPred_eq] using hbound

end HigherDimLQGMetric
