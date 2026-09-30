import QuantumZipper.Proofs.Section5.Prop1617Proved
import QuantumZipper.Proofs.Section5.Prop16LitPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the canonical pairings through the chart, one sample

`Prop16Lit.core_pointwise` (deterministic, one sample): for a chart `ψ` (`IsLitChart`), test
functions `f j` vanishing off `B(0, R_f)`, a bump `φ` equal to `1` on `B(0, 4R_f)` and `ε₀ > 0`,
there is `δ > 0` such that for every straight field `Y` (locally good, with finite local area on
`B(0,t) ∩ ℍ`) and every field `Z` read through the chart whose area measures satisfy conformal
covariance (DS11 Prop. 2.1: `ψ_* μ_Z = μ_Y|_{ψ(U)}` and the rescaling rule for `Z`), if the
straight canonical scale lies in `(0, δ)` then the canonical pairings differ by at most
`ε₀ · ∫ φ dμ_{canonical Y}`. This combines `LitChart.pointwise_close` with the rescaling rule for
locally good fields (`Prop16Asm.integral_canonicalOn_of_locallyGood`). Own elementary argument.
-/

noncomputable section

open Filter Set Metric MeasureTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open LitChart Prop16Asm Prop16Area.G

/-- The chart of `IsLitChart` has the strict derivative `κ = Re ψ'(0) > 0` at `0`. -/
theorem _root_.QuantumZipper.IsLitChart.strict {U : Set ℂ} {r : ℝ} {ψ : ℂ → ℂ} (h : IsLitChart U r ψ) :
    HasStrictDerivAt ψ (((deriv ψ 0).re : ℝ) : ℂ) 0 := by
  obtain ⟨-, -, -, hr, hd, -, -, -, him, -⟩ := h
  have ha : AnalyticAt ℂ ψ 0 := hd.analyticAt (ball_mem_nhds 0 hr)
  have e : (((deriv ψ 0).re : ℝ) : ℂ) = deriv ψ 0 := by
    apply Complex.ext <;> simp [him]
  rw [e]; exact ha.hasStrictDerivAt

/-- The canonical local area pairing. -/
abbrev canPair (γ : ℝ) (Y : FieldSample) (U : Set ℂ) (f : ℂ → ℝ) : ℝ :=
  ∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ Y U) (canonicalDomainOn γ Y U)

/-- **One-sample comparison of the canonical pairings.** -/
theorem core_pointwise {γ : ℝ} (hγ : 0 < γ) {ψ : ℂ → ℂ} {r₀ : ℝ} {U0 : Set ℂ}
    (hch : IsLitChart U0 r₀ ψ) (hψm : Measurable ψ) (hU0H : U0 ⊆ H) {m : ℕ}
    {f : Fin m → ℂ → ℝ} (hfc : ∀ j, Continuous (f j)) (hfs : ∀ j, HasCompactSupport (f j))
    {Rf : ℝ} (hRf1 : 1 ≤ Rf) (hfR : ∀ j (u : ℂ), Rf ≤ ‖u‖ → f j u = 0)
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1)
    (hφin : ∀ z : ℂ, ‖z‖ < 4 * Rf → φ z = 1) (hφout : ∀ z : ℂ, 4 * Rf + 1 ≤ ‖z‖ → φ z = 0)
    {t : ℝ} (ht : 0 < t) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ δ > 0, ∀ (Y Z : FieldSample) (V U : Set ℂ), IsOpen U → U ⊆ H → U ⊆ V →
      IsLocallyGoodOn γ V Y → qAreaMeasureOn γ Y U (ball 0 t ∩ H) < ⊤ →
      (qAreaMeasureOn γ Z (ball 0 r₀ ∩ H)).map ψ =
        (qAreaMeasureOn γ Y U).restrict (ψ '' (ball 0 r₀ ∩ H)) →
      (0 < scaleParamOn γ Z (ball 0 r₀ ∩ H) →
        qAreaMeasureOn γ (canonicalOn γ Z (ball 0 r₀ ∩ H))
            (canonicalDomainOn γ Z (ball 0 r₀ ∩ H)) =
          (qAreaMeasureOn γ Z (ball 0 r₀ ∩ H)).map
            fun z => z / (scaleParamOn γ Z (ball 0 r₀ ∩ H) : ℂ)) →
      0 < scaleParamOn γ Y U → scaleParamOn γ Y U < δ →
      ‖(fun j => canPair γ Z (ball 0 r₀ ∩ H) (f j)) - (fun j => canPair γ Y U (f j))‖ ≤
        ε₀ * canPair γ Y U φ := by
  have hstrict := hch.strict
  obtain ⟨-, hinjH, himH, hr₀, -, -, hreal, hψ0, -, hκ⟩ := hch
  set κ := (deriv ψ 0).re with hκdef
  have hψH : ∀ z ∈ H, ψ z ∈ H := fun z hz => hU0H (himH ▸ mem_image_of_mem ψ hz)
  have hj : ∀ j, ∃ δ > 0, ∀ μ ν : Measure ℂ,
      ν.map ψ = μ.restrict (ψ '' (ball 0 r₀ ∩ H)) → (∀ᵐ z ∂ν, z ∈ ball 0 r₀ ∩ H) →
      (∀ᵐ w ∂μ, w ∈ H) → 0 < scaleOf μ → scaleOf μ < δ →
      μ (ball 0 (4 * Rf * scaleOf μ) ∩ H) < ⊤ →
      0 < scaleOf ν ∧ |∫ z, f j (z / scaleOf ν) ∂ν - ∫ w, f j (w / scaleOf μ) ∂μ| ≤
        ε₀ * (μ (ball 0 (4 * Rf * scaleOf μ) ∩ H)).toReal := fun j =>
    pointwise_close hκ hstrict hψ0 hr₀ hreal hψm hinjH hψH hr₀ (hfc j) (hfs j) hRf1 (hfR j) hε₀
  choose δj hδj0 hδj using hj
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ t / (4 * Rf + 2) ∧ ∀ j, δ ≤ δj j := by
    have hRf0 : 0 < Rf := by linarith
    refine (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and
      ((?_ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ t / (4 * Rf + 2)).and (eventually_all.2 fun j => ?_))
    · exact nhdsWithin_le_nhds (Iic_mem_nhds (by positivity))
    · exact nhdsWithin_le_nhds (Iic_mem_nhds (hδj0 j))
  obtain ⟨δ, hδ0, hδt, hδle⟩ := hev.exists
  refine ⟨δ, hδ0, ?_⟩
  intro Y Z V U hUo hUH hUV hloc hfin hmap hcanZ ha0 haδ
  have hRf0 : 0 < Rf := by linarith
  set μ := qAreaMeasureOn γ Y U with hμ
  set ν := qAreaMeasureOn γ Z (ball 0 r₀ ∩ H) with hν
  set a := scaleParamOn γ Y U with ha
  have haμ : a = scaleOf μ := rfl
  have hμH : ∀ᵐ w ∂μ, w ∈ H := by
    have := qAreaMeasureOn_compl γ Y U
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with w hw
    exact hUH (not_not.1 hw)
  have hνU : ∀ᵐ z ∂ν, z ∈ ball 0 r₀ ∩ H := by
    have := qAreaMeasureOn_compl γ Z (ball 0 r₀ ∩ H)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with w hw
    exact not_not.1 hw
  have hat : (4 * Rf + 2) * a < t := by
    have := haδ.trans_le hδt
    rwa [lt_div_iff₀ (by positivity), mul_comm] at this
  have hfinR : ∀ s, s ≤ (4 * Rf + 2) * a → μ (ball 0 s ∩ H) < ⊤ := fun s hs =>
    (measure_mono (inter_subset_inter_left _ (ball_subset_ball (hs.trans hat.le)))).trans_lt hfin
  have hfin4 : μ (ball 0 (4 * Rf * scaleOf μ) ∩ H) < ⊤ := hfinR _ (by
    rw [← haμ]; nlinarith)
  -- per-coordinate estimates
  have hcoord : ∀ j, |canPair γ Z (ball 0 r₀ ∩ H) (f j) - canPair γ Y U (f j)| ≤
      ε₀ * (μ (ball 0 (4 * Rf * a) ∩ H)).toReal := by
    intro j
    obtain ⟨hb0, hbd⟩ := hδj j μ ν hmap hνU hμH ha0 (haδ.trans_le (hδle j)) hfin4
    have hZ : canPair γ Z (ball 0 r₀ ∩ H) (f j) = ∫ z, f j (z / scaleOf ν) ∂ν := by
      simp only [canPair]
      rw [hcanZ hb0, integral_map (by fun_prop) (hfc j).aestronglyMeasurable]
      rfl
    have hY : canPair γ Y U (f j) = ∫ w, f j (w / scaleOf μ) ∂μ :=
      integral_canonicalOn_of_locallyGood hγ hloc hUo hUH hUV ha0 (hfc j)
    rw [hZ, hY]; exact hbd
  -- the bump dominates the canonical mass of `B(0, 4R_f)`
  have hφY : canPair γ Y U φ = ∫ w, φ (w / a) ∂μ :=
    integral_canonicalOn_of_locallyGood hγ hloc hUo hUH hUV ha0 hφc
  have hmeasB : ∀ s : ℝ, MeasurableSet (ball (0 : ℂ) s ∩ H) := fun s =>
    measurableSet_ball.inter (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hmass : (μ (ball 0 (4 * Rf * a) ∩ H)).toReal ≤ ∫ w, φ (w / a) ∂μ := by
    set B := ball (0 : ℂ) ((4 * Rf + 2) * a) ∩ H with hB
    have hBfin : μ B < ⊤ := hfinR _ le_rfl
    have hint : Integrable (fun w => φ (w / a)) μ := by
      refine Integrable.mono' ((integrable_indicator_iff (hmeasB _)).2
        (integrableOn_const (hs := hBfin.ne) (C := (1 : ℝ))))
        (hφc.comp (continuous_id.div_const _)).aestronglyMeasurable ?_
      filter_upwards [hμH] with w hw
      rw [Real.norm_of_nonneg (hφ0 _)]
      by_cases hwB : w ∈ B
      · rw [indicator_of_mem hwB]; exact hφ1 _
      · rw [indicator_of_notMem hwB]
        have : (4 * Rf + 2) * a ≤ ‖w‖ := by
          by_contra hlt
          exact hwB ⟨by rw [mem_ball, dist_zero_right]; linarith, hw⟩
        have hle : 4 * Rf + 1 ≤ ‖w / (a : ℂ)‖ := by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha0.le, le_div_iff₀ ha0]
          nlinarith
        rw [hφout _ hle]
    have h1 : ∫ w, (ball (0 : ℂ) (4 * Rf * a) ∩ H).indicator (fun _ => (1 : ℝ)) w ∂μ =
        (μ (ball 0 (4 * Rf * a) ∩ H)).toReal := by
      rw [integral_indicator (hmeasB _), setIntegral_const, smul_eq_mul, mul_one,
        measureReal_def]
    rw [← h1]
    refine integral_mono ((integrable_indicator_iff (hmeasB _)).2
      (integrableOn_const (hs := (hfinR _ (by nlinarith)).ne))) hint fun w => ?_
    by_cases hw : w ∈ ball (0 : ℂ) (4 * Rf * a) ∩ H
    · rw [indicator_of_mem hw]
      refine le_of_eq (hφin _ ?_).symm
      have := hw.1
      rw [mem_ball, dist_zero_right] at this
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha0.le, div_lt_iff₀ ha0]
      exact this
    · rw [indicator_of_notMem hw]; exact hφ0 _
  rw [pi_norm_le_iff_of_nonneg (by
    have := ENNReal.toReal_nonneg (a := μ (ball 0 (4 * Rf * a) ∩ H))
    have : 0 ≤ ∫ w, φ (w / a) ∂μ := integral_nonneg fun w => hφ0 _
    rw [hφY]; positivity)]
  intro j
  rw [Pi.sub_apply, Real.norm_eq_abs]
  refine (hcoord j).trans ?_
  rw [hφY]
  exact mul_le_mul_of_nonneg_left hmass hε₀.le

end Prop16Lit

end QuantumZipper
