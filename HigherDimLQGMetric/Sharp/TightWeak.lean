import HigherDimLQGMetric.Sharp.ShellScaling
import HigherDimLQGMetric.Sharp.TightSphereDet
import HigherDimLQGMetric.Sharp.TightShell
import HigherDimLQGMetric.Events.TightLaw

/-!
# Shell tightness for any weak exponential metric

The centered normalized observable is a positive scalar multiple of an affine
coordinate change of the original metric. The uniform lower and modulus
estimates for this observable yield uniform shell bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The normalized metric at center `z` and scale `r`. -/
def weakScaledMetric (ξ : ℝ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ)
    (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d) (hc : 0 < c r) : ContMetric d :=
  ((D g).affine r hr.ne' z).smul
    ((c r)⁻¹ * Real.exp (-ξ * sphereAvg g r z))
    (mul_pos (inv_pos.2 hc) (Real.exp_pos _))

theorem weakScaledMetric_apply (ξ : ℝ) (D : DistRd d → ContMetric d)
    (c : ℝ → ℝ) (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hc : 0 < c r) (p : Rd d × Rd d) :
    (weakScaledMetric ξ D c g hr z hc).1 p = scaledField ξ D c r z g p := rfl

theorem weakScaledMetric_isLength (ξ : ℝ) (D : DistRd d → ContMetric d)
    (c : ℝ → ℝ) (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hc : 0 < c r) (hLen : (D g).IsLength) :
    (weakScaledMetric ξ D c g hr z hc).IsLength :=
  ContMetric.isLength_smul _ (ContMetric.isLength_affine hr.ne' z hLen)

theorem weakScaledMetric_sphereDiam (ξ : ℝ) (D : DistRd d → ContMetric d)
    (c : ℝ → ℝ) (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hc : 0 < c r) :
    sphereDiam (weakScaledMetric ξ D c g hr z hc) 0 1 =
      ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg g r z)) *
        sphereDiam (D g) z r := by
  unfold weakScaledMetric
  rw [sphereDiam_smul, sphereDiam_affine hr]

theorem weakScaledMetric_acrossDist (ξ : ℝ) (D : DistRd d → ContMetric d)
    (c : ℝ → ℝ) (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hc : 0 < c r) :
    acrossDist (weakScaledMetric ξ D c g hr z hc) 0 (1 / 2) 1 =
      ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg g r z)) *
        acrossDist (D g) z (r / 2) r := by
  unfold weakScaledMetric
  rw [acrossDist_smul, acrossDist_affine hr]
  congr 1
  ring

theorem IsWeakExpMetric.scaledAcrossLower {ξ : ℝ}
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (r : ℝ) (hr : 0 < r) (z : Rd d),
          P {ω | acrossDist (weakScaledMetric ξ D c (h ω) hr z
            (hD.c_pos r hr)) 0 (1 / 2) 1 < ENNReal.ofReal a} < ε := by
  have hOff : ∀ p : Rd d × Rd d,
      p ∈ sphere (0 : Rd d) (1 / 2) ×ˢ sphere (0 : Rd d) 1 → p.1 ≠ p.2 := by
    intro p hp heq
    have h1 : dist p.1 (0 : Rd d) = 1 / 2 := by
      simpa only [Metric.mem_sphere] using hp.1
    have h2 : dist p.2 (0 : Rd d) = 1 := by
      simpa only [Metric.mem_sphere] using hp.2
    rw [heq] at h1
    linarith
  obtain ⟨a, ha, H⟩ := hD.scaledLowerOffDiag hd
    ((isCompact_sphere (0 : Rd d) (1 / 2)).prod (isCompact_sphere 0 1)) hOff hε
  refine ⟨a, ha, ?_⟩
  intro Ω _ P _ h hh r hr z
  refine lt_of_le_of_lt (measure_mono ?_) (H P h hh r hr z)
  intro ω hbad hgood
  have hle : ENNReal.ofReal a ≤
      acrossDist (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)) 0 (1 / 2) 1 := by
    unfold acrossDist
    refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
    rw [weakScaledMetric_apply]
    exact ENNReal.ofReal_le_ofReal (hgood (u, v) ⟨hu, hv⟩).le
  exact (not_lt_of_ge hle) hbad

theorem IsWeakExpMetric.scaledSphereDiamUpper {ξ : ℝ}
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (r : ℝ) (hr : 0 < r) (z : Rd d),
          P {ω | ENNReal.ofReal C < sphereDiam
            (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)) 0 1} < ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  let K : Set (Rd d) := sphere 0 1
  let V : Set (Rd d) := ann 0 (1 / 2) 2
  obtain ⟨a, ha, Hsep⟩ := hD.scaledLowerOffDiag hd
    ((isCompact_sphere (0 : Rd d) 1).prod compact_frontier_unit_ann)
    sphere_frontier_offDiag hε2
  obtain ⟨b, hb, Hmod⟩ := hD.scaledModulus hd
    (isCompact_sphere (0 : Rd d) 1) ha hε2
  obtain ⟨N, hN⟩ := compact_connected_chain_bound
    (isCompact_sphere (0 : Rd d) 1) (isConnected_unit_sphere hd) hb
  let C : ℝ := (N + 1) * a
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh r hr z
  let G : Ω → ContMetric d := fun ω =>
    weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)
  have hLen : ∀ᵐ ω ∂P, (G ω).IsLength := by
    filter_upwards [hD.length P h hh.isLGFPlusCont] with ω hw
    exact weakScaledMetric_isLength ξ D c (h ω) hr z (hD.c_pos r hr) hw
  have hgood (ω : Ω) (hl : (G ω).IsLength)
      (hs : ∀ p ∈ K ×ˢ frontier V, a < scaledField ξ D c r z (h ω) p)
      (hm : ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
        scaledField ξ D c r z (h ω) (u, v) < a) :
      sphereDiam (G ω) 0 1 ≤ ENNReal.ofReal C := by
    have hsep' : ∀ u ∈ K, ∀ v ∈ frontier V, a < (G ω).1 (u, v) := by
      intro u hu v hv
      rw [weakScaledMetric_apply]
      exact hs (u, v) ⟨hu, hv⟩
    have hmod' : ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → (G ω).1 (u, v) < a := by
      intro u hu v hv huv
      rw [weakScaledMetric_apply]
      exact hm u hu v hv huv
    have hdiam := sphereDiam_le_of_modulus N hN (G ω) hl ha hsep' hmod'
    have hle : (N : ℝ≥0∞) * ENNReal.ofReal a ≤ ENNReal.ofReal C := by
      have hNa : (N : ℝ) * a ≤ C := by dsimp [C]; nlinarith
      calc
        (N : ℝ≥0∞) * ENNReal.ofReal a = ENNReal.ofReal ((N : ℝ) * a) := by
          rw [ENNReal.ofReal_mul (p := (N : ℝ)) (by positivity), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hNa
    exact hdiam.trans hle
  have hbad : P {ω | ENNReal.ofReal C < sphereDiam (G ω) 0 1} ≤
      P ({ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < scaledField ξ D c r z (h ω) p} ∪
        {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
          scaledField ξ D c r z (h ω) (u, v) < a}) := by
    refine measure_mono_ae ?_
    filter_upwards [hLen] with ω hl hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
    exact (not_lt_of_ge (hgood ω hl hnot.1 hnot.2)) hω
  calc
    P {ω | ENNReal.ofReal C < sphereDiam (G ω) 0 1} ≤ P _ := hbad
    _ ≤ P {ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < scaledField ξ D c r z (h ω) p} +
        P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
          scaledField ξ D c r z (h ω) (u, v) < a} := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (Hsep P h hh r hr z) (Hmod P h hh r hr z)
    _ = ε := ENNReal.add_halves ε

end HigherDimLQGMetric
