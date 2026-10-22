import HigherDimLQGMetric.Sec4.Lemma41
import HigherDimLQGMetric.ConvField.Shifts
import HigherDimLQGMetric.LGF.Normalized
import HigherDimLQGMetric.LGF.Invariance
import HigherDimLQGMetric.Sphere.Conv
import HigherDimLQGMetric.Field.LGFPlusCont

/-!
# [1] Lemma 4.1, uniform in the centre (packet L9b, MA6 P9 "uniform transfer")

`ref1_lemma41_uniform`: for all `η, θ > 0` there is `ε₀ > 0` such that for every normalized LGF (on any probability
space), every `ε ∈ (0, ε₀)` and every centre `u`, `P[sup_{B̄_4(u)} |h*_ε - ĥ*_ε| > η] ≤ θ`.

MA6 P9: `h*_ε - ĥ*_ε` does not see the additive constant and is stationary. Here: the recentred translate
`h_u = h(· + u) - (h(· + u))_1(0)` is a normalized LGF, `h*_ε - ĥ*_ε` at `x + u` for `h` equals the same
difference at `x` for `h_u` (almost surely; `l2b_convMollify_translate`, `l2b_ae_convMollify_addConst`,
`locField_affineComp_one`, `locField_addConst`), and the outer measure of a preimage is at most the measure of
the law, `P (h_u ⁻¹' A) ≤ (P.map h_u) A = normLGFLaw A` (no measurability of `A` needed). `ref1_lemma41` on the
canonical space `(DistRd d, normLGFLaw d, id)` concludes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## Normalized laws -/

/-- the law of every normalized LGF is `normLGFLaw d` -/
theorem l9b_map_eq_normLGFLaw (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) :
    P.map h = normLGFLaw d :=
  (normLGFLaw_spec_holds d hd).2.2 _ ((Measure.isProbabilityMeasure_map_iff
    hh.1.measurable.aemeasurable).2 inferInstance) hh.map_id

/-- **Outer-measure law transfer**: for a normalized LGF `h` and any set `A` of distributions,
`P (h⁻¹ A) ≤ normLGFLaw A` -/
theorem l9b_preimage_le_normLGFLaw (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) (A : Set (DistRd d)) :
    P (h ⁻¹' A) ≤ normLGFLaw d A := by
  rw [← l9b_map_eq_normLGFLaw hd hh]
  exact Measure.le_map_apply hh.1.measurable.aemeasurable A

/-- the recentred affine image of an LGF -/
def recentAff (r : ℝ) (u : Rd d) (g : DistRd d) : DistRd d :=
  addConst (affineComp r u g) (-sphereAvg (affineComp r u g) 1 0)

theorem isNormalizedLGF_recentAff (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P) {r : ℝ} (hr : 0 < r) (u : Rd d) :
    IsNormalizedLGF (fun ω => recentAff r u (h ω)) P := by
  have hz := hh.affineComp hr u
  exact hz.isNormalizedLGF_normalize (by omega) (hz.ae_exists_tendsto_sphereAvgSeq hd one_pos 0)

theorem addConst_recentAff (r : ℝ) (u : Rd d) (g : DistRd d) :
    addConst (recentAff r u g) (sphereAvg (affineComp r u g) 1 0) = affineComp r u g := by
  rw [recentAff, addConst_addConst, neg_add_cancel, addConst_zero]

/-- the canonical space: `normLGFLaw d` is a probability measure carrying a normalized LGF -/
theorem l9b_normLGFLaw_prob (hd : 2 ≤ d) : IsProbabilityMeasure (normLGFLaw d) :=
  (normLGFLaw_spec_holds d hd).1

theorem l9b_normLGFLaw_normalized (hd : 2 ≤ d) : IsNormalizedLGF (id : DistRd d → DistRd d)
    (normLGFLaw d) :=
  (normLGFLaw_spec_holds d hd).2.1

/-! ## Translation of the localization error -/

/-- a.s. for the recentred translate: `h*_ε - ĥ*_ε` at `x + u` equals the same quantity for `h_u` at `x` -/
theorem l9b_ae_locDiff_translate (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) (u : Rd d) {ε : ℝ} (hε : 0 < ε) (hrad : 0 < locRad ε)
    (hZ : locMass κ ε (locRad ε) ≠ 0) :
    ∀ᵐ ω ∂P, ∀ x : Rd d,
      convMollify κ ε (h ω) (x + u) - locField κ ε (h ω) (x + u) =
        convMollify κ ε (recentAff 1 u (h ω)) x - locField κ ε (recentAff 1 u (h ω)) x := by
  have hK := convKernel_contDiff (d := d) (by omega) hκ
  have hN := isNormalizedLGF_recentAff hd hh.1 one_pos u
  filter_upwards [l2b_ae_convMollify_addConst d hd κ hκ P _ hN] with ω hω
  intro x
  set c := sphereAvg (affineComp 1 u (h ω)) 1 0
  have h1 : convMollify κ ε (h ω) (x + u) = convMollify κ ε (recentAff 1 u (h ω)) x + c := by
    rw [← l2b_convMollify_translate d hd κ hκ ε (h ω) u x, ← addConst_recentAff 1 u (h ω)]
    exact hω ε hε x c
  have h2 : locField κ ε (h ω) (x + u) = locField κ ε (recentAff 1 u (h ω)) x + c := by
    rw [← locField_affineComp_one hK hrad (h ω) u x, ← addConst_recentAff 1 u (h ω)]
    exact locField_addConst hK hrad hZ _ c x
  rw [h1, h2]
  ring

/-- **[1] Lemma 4.1, uniform in the centre** (MA6 P9): for `η, θ > 0` there is `ε₀ > 0` such that for every
normalized LGF on any probability space, every `ε ∈ (0, ε₀)` and every `u`,
`P[∃ x ∈ B̄_4(u), |h*_ε(x) - ĥ*_ε(x)| > η] ≤ θ`. -/
theorem ref1_lemma41_uniform (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {η : ℝ} (hη : 0 < η) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ u : Rd d,
        P {ω | ∃ x ∈ closedBall u 4,
          η < |convMollify κ ε (h ω) x - locField κ ε (h ω) x|} ≤ θ := by
  have := l9b_normLGFLaw_prob hd
  have hcan := ref1_lemma41 hd hκ (normLGFLaw d) id (l9b_normLGFLaw_normalized hd)
    (R := 4) (by norm_num) hη
  have hev := (ENNReal.tendsto_nhds_zero.1 hcan) θ hθ
  have hev' := hev.and (l9b_eventually_locHyp hd hκ)
  obtain ⟨ε₀, hε₀, hball⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev'
  refine ⟨ε₀, hε₀, ?_⟩
  intro Ω _ P _ h hh ε hε u
  obtain ⟨hcanε, hε0, -, hrad, -, hZ⟩ := hball hε
  have hZ0 : locMass κ ε (locRad ε) ≠ 0 := by linarith
  let A : Set (DistRd d) := {g | ∃ x ∈ closedBall (0 : Rd d) 4,
    η < |convMollify κ ε g x - locField κ ε g x|}
  have hN := isNormalizedLGF_recentAff hd hh.1 one_pos u
  calc P {ω | ∃ x ∈ closedBall u 4, η < |convMollify κ ε (h ω) x - locField κ ε (h ω) x|}
      ≤ P ((fun ω => recentAff 1 u (h ω)) ⁻¹' A) := by
        refine measure_mono_ae ?_
        filter_upwards [l9b_ae_locDiff_translate hd hκ hh u hε0 hrad hZ0] with ω hω hbad
        obtain ⟨x, hx, hlt⟩ := hbad
        refine ⟨x - u, ?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right]
          rw [mem_closedBall, dist_eq_norm] at hx
          exact hx
        · have := hω (x - u)
          rw [sub_add_cancel] at this
          rw [← this]
          exact hlt
    _ ≤ normLGFLaw d A := l9b_preimage_le_normLGFLaw hd hN A
    _ ≤ θ := by simpa [A] using hcanε

end HigherDimLQGMetric
