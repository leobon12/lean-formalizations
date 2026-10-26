import SupercriticalConformalCovariance.TV.HarmonicVar

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set LQGMetric LQGMetric.GM QuantumZipper

namespace SupercriticalConformalCovariance.TV

/-- The variance of a disk Markov harmonic increment, read through radial tests. -/
theorem disk_markov_radDiff_variance
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hH hZ : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {L r δ : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    (hδ : 0 < δ) {y : ℂ} (hy : ‖y‖ + δ < r) (h0 : δ < r)
    (X : BddOn (ball (0 : ℂ) L) → Ω → ℝ)
    (hX : IsZBGFFProcessExt ⟨ball (0 : ℂ) L, isOpen_ball⟩ X P)
    (hEq : ∀ φ : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩,
      X φ.toBddOn =ᵐ[P] fun ω =>
        restrictTo ⟨ball (0 : ℂ) L, isOpen_ball⟩ (hZ ω) φ)
    (hind : IndepFun hH hZ P)
    {s : ℝ} (z : ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω) :
    Var[fun ω => hH ω (radDiff hδ.le y 0).1; P] =
      -Real.log (1 - ‖y‖ ^ 2 / L ^ 2) * (∫ x, radProf δ x) ^ 2 := by
  let U : TopologicalSpace.Opens ℂ := ⟨ball (0 : ℂ) L, isOpen_ball⟩
  let a := radBumpOnDisk hδ hL y (hy.trans hrL)
  let b := radBumpOnDisk hδ hL 0 (by simpa using h0.trans hrL)
  let φ : TestOn U := a - b
  let ψ : TestC0 := radDiff hδ.le y 0
  have hφψ : (φ : ℂ → ℝ) = ψ.1 := by
    funext x
    rfl
  have hψ : tsupport (ψ.1 : ℂ → ℝ) ⊆ U := by
    rw [← hφψ]
    exact φ.tsupport_subset
  have hφ : φ = localTestOn U ψ hψ := by
    ext x
    exact congrFun hφψ x
  have hv := harmonic_variance_eq_logCov_sub_zeroGFFTestCov hh X hX hEq
    hind z hsum ψ hψ
  rw [← hφψ, ← hφ] at hv
  have hker := logCov_sub_zeroGFFTestCov_disk_eq_harmonicKernel hL φ φ
  change logCov φ φ - zeroGFFTestCov U φ φ = _ at hker
  have hrad := integral_diskHarmonicKernel_radDiff hL hr hrL hδ hy h0
  change (∫ p : ℂ × ℂ, (φ p.1) * (φ p.2) *
      diskHarmonicKernel L p.1 p.2
      ∂((volume : Measure ℂ).prod volume)) = _ at hrad
  exact (hv.trans hker).trans hrad

/-- The deterministic disk covariance gap for a radial mean-zero difference. -/
theorem disk_radDiff_covariance_gap
    {L r δ : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    (hδ : 0 < δ) {y : ℂ} (hy : ‖y‖ + δ < r) (h0 : δ < r) :
    let φ : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩ :=
      radBumpOnDisk hδ hL y (hy.trans hrL) -
        radBumpOnDisk hδ hL 0 (by simpa using h0.trans hrL)
    logCov (radDiff hδ.le y 0).1 (radDiff hδ.le y 0).1 -
      zeroGFFTestCov (ball (0 : ℂ) L) φ φ =
      -Real.log (1 - ‖y‖ ^ 2 / L ^ 2) * (∫ x, radProf δ x) ^ 2 := by
  dsimp
  let φ : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩ :=
    radBumpOnDisk hδ hL y (hy.trans hrL) -
      radBumpOnDisk hδ hL 0 (by simpa using h0.trans hrL)
  have hφ : (φ : ℂ → ℝ) = (radDiff hδ.le y 0).1 := by
    funext x
    rfl
  change logCov (radDiff hδ.le y 0).1 (radDiff hδ.le y 0).1 -
    zeroGFFTestCov (ball (0 : ℂ) L) φ φ = _
  rw [← hφ]
  have hker := logCov_sub_zeroGFFTestCov_disk_eq_harmonicKernel hL φ φ
  rw [hker]
  have hrad := integral_diskHarmonicKernel_radDiff hL hr hrL hδ hy h0
  change (∫ p : ℂ × ℂ, φ p.1 * φ p.2 *
      diskHarmonicKernel L p.1 p.2
      ∂((volume : Measure ℂ).prod volume)) = _ at hrad
  exact hrad

/-- Uniform in-domain harmonic variance bound at radial increments, from
zero-boundary covariance monotonicity and the disk Green identity. -/
theorem markov_radDiff_variance_le_disk
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hH hZ : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (D : TopologicalSpace.Opens ℂ) (hDb : Bornology.IsBounded (D : Set ℂ))
    {L r δ : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    (hδ : 0 < δ) {y : ℂ} (hy : ‖y‖ + δ < r) (h0 : δ < r)
    (hBD : ball (0 : ℂ) L ⊆ D)
    (X : BddOn (D : Set ℂ) → Ω → ℝ)
    (hX : IsZBGFFProcessExt D X P)
    (hEq : ∀ φ : TestOn D, X φ.toBddOn =ᵐ[P]
      fun ω => restrictTo D (hZ ω) φ)
    (hind : IndepFun hH hZ P)
    {s : ℝ} (z : ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω) :
    Var[fun ω => hH ω (radDiff hδ.le y 0).1; P] ≤
      -Real.log (1 - ‖y‖ ^ 2 / L ^ 2) * (∫ x, radProf δ x) ^ 2 := by
  let B : TopologicalSpace.Opens ℂ := ⟨ball (0 : ℂ) L, isOpen_ball⟩
  let ψ : TestC0 := radDiff hδ.le y 0
  let φB : TestOn B :=
    radBumpOnDisk hδ hL y (hy.trans hrL) -
      radBumpOnDisk hδ hL 0 (by simpa using h0.trans hrL)
  have hφψ : (φB : ℂ → ℝ) = ψ.1 := by funext x; rfl
  have hψB : tsupport (ψ.1 : ℂ → ℝ) ⊆ B := by
    rw [← hφψ]
    exact φB.tsupport_subset
  have hψD : tsupport (ψ.1 : ℂ → ℝ) ⊆ D := hψB.trans hBD
  let φD : TestOn D := localTestOn D ψ hψD
  have hφD : (φB : ℂ → ℝ) = (φD : ℂ → ℝ) := by
    rw [hφψ]
    rfl
  have hmono : zeroGFFTestCov B φB φB ≤ zeroGFFTestCov D φD φD :=
    zeroGFFTestCov_self_mono hBD (zbAdmissible_of_isBounded Metric.isBounded_ball)
      (zbAdmissible_of_isBounded hDb) φB φD hφD
  have hv := harmonic_variance_eq_logCov_sub_zeroGFFTestCov hh X hX hEq
    hind z hsum ψ hψD
  change Var[fun ω => hH ω ψ.1; P] =
    logCov ψ.1 ψ.1 - zeroGFFTestCov D φD φD at hv
  have hgap := disk_radDiff_covariance_gap hL hr hrL hδ hy h0
  change logCov ψ.1 ψ.1 - zeroGFFTestCov B φB φB = _ at hgap
  calc
    Var[fun ω => hH ω ψ.1; P] =
        logCov ψ.1 ψ.1 - zeroGFFTestCov D φD φD := hv
    _ ≤ logCov ψ.1 ψ.1 - zeroGFFTestCov B φB φB := sub_le_sub_left hmono _
    _ = _ := hgap

/-- Division by the positive radial mass removes the mollifier normalization
from an increment variance estimate. -/
theorem variance_div_radial_mass_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {δ : ℝ} (hδ : 0 < δ) (X : Ω → ℝ) (q : ℝ)
    (hX : Var[X; P] ≤ q * (∫ x : ℂ, radProf δ x) ^ 2) :
    Var[fun ω => X ω / ∫ x : ℂ, radProf δ x; P] ≤ q := by
  let I := ∫ x : ℂ, radProf δ x
  have hI : 0 < I := integral_radProf_pos hδ
  have hI2 : 0 < I ^ 2 := sq_pos_of_pos hI
  have he : Var[fun ω => X ω / I; P] = Var[X; P] / I ^ 2 := by
    have hf : (fun ω => X ω / I) = fun ω => I⁻¹ * X ω := by
      funext ω
      field_simp
    rw [hf, variance_const_mul]
    field_simp
  change Var[fun ω => X ω / I; P] ≤ q
  rw [he]
  exact (div_le_iff₀ hI2).mpr hX

/-- The measurable version of a Markov harmonic increment has the disk
second-moment bound. On the harmonic event this is `H(y)-H(0)`. -/
theorem integral_sq_markov_radDiff_div_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hH hZ G : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hGm : Measurable G) (hGeq : hH =ᵐ[P] G)
    (D : TopologicalSpace.Opens ℂ) (hDb : Bornology.IsBounded (D : Set ℂ))
    {L r δ : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    (hδ : 0 < δ) {y : ℂ} (hy : ‖y‖ + δ < r) (h0 : δ < r)
    (hBD : ball (0 : ℂ) L ⊆ D)
    (X : BddOn (D : Set ℂ) → Ω → ℝ)
    (hX : IsZBGFFProcessExt D X P)
    (hEq : ∀ φ : TestOn D, X φ.toBddOn =ᵐ[P]
      fun ω => restrictTo D (hZ ω) φ)
    (hind : IndepFun hH hZ P)
    {s : ℝ} (z : ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω) :
    ∫ ω, (G ω (radDiff hδ.le y 0).1 / ∫ x, radProf δ x) ^ 2 ∂P ≤
      -Real.log (1 - ‖y‖ ^ 2 / L ^ 2) := by
  let ψ : TestC0 := radDiff hδ.le y 0
  let B : TopologicalSpace.Opens ℂ := ⟨ball (0 : ℂ) L, isOpen_ball⟩
  let φB : TestOn B :=
    radBumpOnDisk hδ hL y (hy.trans hrL) -
      radBumpOnDisk hδ hL 0 (by simpa using h0.trans hrL)
  have hφψ : (φB : ℂ → ℝ) = ψ.1 := by funext x; rfl
  have hψB : tsupport (ψ.1 : ℂ → ℝ) ⊆ B := by
    rw [← hφψ]
    exact φB.tsupport_subset
  have hψD : tsupport (ψ.1 : ℂ → ℝ) ⊆ D := hψB.trans hBD
  have hHmean := harmonic_pair_centered hh X hX hEq z hsum ψ hψD
  let I := ∫ x : ℂ, radProf δ x
  have hmean : ∫ ω, G ω ψ.1 / I ∂P = 0 := by
    have he : (fun ω => G ω ψ.1 / I) =ᵐ[P] fun ω => hH ω ψ.1 / I := by
      filter_upwards [hGeq] with ω hω
      rw [← hω]
    rw [integral_congr_ae he, integral_div, hHmean, zero_div]
  have hm : Measurable (fun ω => G ω ψ.1 / I) :=
    ((GFFInv.measurable_pair ψ.1).comp hGm).div_const I
  have hvar : Var[fun ω => G ω ψ.1 / I; P] ≤
      -Real.log (1 - ‖y‖ ^ 2 / L ^ 2) := by
    have he : (fun ω => G ω ψ.1 / I) =ᵐ[P] fun ω => hH ω ψ.1 / I := by
      filter_upwards [hGeq] with ω hω
      rw [← hω]
    rw [variance_congr he]
    exact variance_div_radial_mass_le P hδ _ _
      (markov_radDiff_variance_le_disk hh D hDb hL hr hrL hδ hy h0 hBD
        X hX hEq hind z hsum)
  rw [← variance_of_integral_eq_zero hm.aemeasurable hmean]
  exact hvar

end SupercriticalConformalCovariance.TV
