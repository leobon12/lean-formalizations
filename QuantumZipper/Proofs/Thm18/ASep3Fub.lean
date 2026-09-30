import QuantumZipper.Proofs.GFF.CircleFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 10): stochastic Fubini for folded-circle averages at an arbitrary radius

`integral_circleAvg_ae_eq_bind_rho`: verbatim copy of `integral_circleAvg_ae_eq_bind`
(CircleFubini.lean) with the dyadic radius `2^{-k}` replaced by an arbitrary `ρ > 0` (the proof
only uses `0 < 2^{-k}`). The regularization of `rescale X Q s` reads `X` at the non-dyadic radii
`s 2^{-k}`, so the identity inputs of the scale run of the engine need this form.
Source as for the original (stochastic Fubini for the GFF; Duplantier–Sheffield, Invent. Math.
185 (2011), §3). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace ASep

open CircleFubini

theorem integral_circleAvg_ae_eq_bind_rho
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {ρ : ℝ} (hρ : 0 < ρ) {z₀ : ℂ} (hz₀ : z₀ ∈ Hbar)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar)
    (hY : ∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P]
      fun ω => X ω (foldedCircle z ρ) - X ω (foldedCircle z₀ ρ))
    (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hνK : ν Kᶜ = 0) :
    (fun ω => ∫ z, Y z ω ∂ν) =ᵐ[P] fun ω =>
      X ω (ν.bind fun w => foldedCircle w ρ)
        - X ω (ν Set.univ • foldedCircle z₀ ρ) := by
  set r := ρ with hr_def
  have hr : 0 < r := hρ
  set νk := ν.bind fun w => foldedCircle w r with hνk_def
  set μ₀ := ν Set.univ • foldedCircle z₀ r with hμ₀_def
  have : IsFiniteMeasure νk := isFiniteMeasure_bind_circle ν
  have : IsFiniteMeasure μ₀ := isFiniteMeasure_smul' _ (measure_ne_top _ _) _
  obtain ⟨R₁, hR₁⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R₀ := max R₁ ‖z₀‖ with hR₀_def
  set R := R₀ + r with hR_def
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R₀ := fun z hz => by
    have := hR₁ hz
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hz₀R : ‖z₀‖ ≤ R₀ := le_max_right _ _
  set Cc : ℝ≥0∞ := 2 * ENNReal.ofReal (potConst r) with hCc_def
  have hCct : Cc ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hcP : ∀ z y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂foldedCircle z r ≤ Cc :=
    fun z y => foldedCircle_pot_le hr z y
  have hcS : ∀ z, ‖z‖ ≤ R₀ → foldedCircle z r (ballH R)ᶜ = 0 := fun z hz =>
    foldedCircle_support hr.le (by linarith)
  have hcA : ∀ z, ‖z‖ ≤ R₀ → IsAdmissibleH (foldedCircle z r) := fun z hz =>
    admissible_of_bounds (hcS z hz) hCct (hcP z)
  have hmCt : ν Set.univ * Cc ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) hCct
  have hkS : νk (ballH R)ᶜ = 0 := bind_circle_support ν hr.le hνK hKR (le_refl _)
  have hkP : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂νk ≤ ν Set.univ * Cc :=
    bind_circle_pot ν hcP
  have hkA : IsAdmissibleH νk := admissible_of_bounds hkS hmCt hkP
  have hkU : νk Set.univ = ν Set.univ := bind_circle_univ ν
  have h0S : μ₀ (ballH R)ᶜ = 0 := by
    rw [hμ₀_def, Measure.smul_apply, hcS z₀ hz₀R, smul_zero]
  have h0P : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ₀ ≤ ν Set.univ * Cc :=
    smul_pot (hcP z₀)
  have h0A : IsAdmissibleH μ₀ := admissible_of_bounds h0S hmCt h0P
  have h0U : μ₀ Set.univ = ν Set.univ := by
    rw [hμ₀_def, Measure.smul_apply, measure_univ (μ := foldedCircle z₀ r), smul_eq_mul, mul_one]
  -- the random variables
  set W : ℂ → Ω → ℝ := fun z ω => X ω (foldedCircle z r) - X ω (foldedCircle z₀ r) with hW_def
  set D : Ω → ℝ := fun ω => X ω νk - X ω μ₀ with hD_def
  have hWm : ∀ z, Measurable (W z) := fun z =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hDm : Measurable D := (hX.measurable_coord _).sub (hX.measurable_coord _)
  have h11 : ∀ z : ℂ, (foldedCircle z r) Set.univ = (foldedCircle z₀ r) Set.univ := by
    intro z; simp
  have hqU : νk Set.univ = μ₀ Set.univ := by rw [hkU, h0U]
  have hWL2 : ∀ z ∈ K, MemLp (W z) 2 P := fun z hz =>
    gff_memLp (p := (foldedCircle z r, foldedCircle z₀ r)) hX (hcA z (hKR z hz))
      (hcA z₀ hz₀R) (h11 z)
  have hDL2 : MemLp D 2 P := gff_memLp (p := (νk, μ₀)) hX hkA h0A hqU
  have hEWW : ∀ z ∈ K, ∀ z' ∈ K, ∫ ω, W z ω * W z' ω ∂P
      = kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r)
          (foldedCircle z' r, foldedCircle z₀ r) :=
    fun z hz z' hz' => gff_integral_mul (p := (foldedCircle z r, foldedCircle z₀ r))
      (q := (foldedCircle z' r, foldedCircle z₀ r)) hX (hcA z (hKR z hz)) (hcA z₀ hz₀R) (h11 z)
      (hcA z' (hKR z' hz')) (hcA z₀ hz₀R) (h11 z')
  have hEWD : ∀ z ∈ K, ∫ ω, W z ω * D ω ∂P
      = kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r) (νk, μ₀) :=
    fun z hz => gff_integral_mul (p := (foldedCircle z r, foldedCircle z₀ r)) (q := (νk, μ₀)) hX (hcA z (hKR z hz))
      (hcA z₀ hz₀R) (h11 z) hkA h0A hqU
  have hEDW : ∀ z ∈ K, ∫ ω, D ω * W z ω ∂P
      = kernelCov2 neumannH (νk, μ₀) (foldedCircle z r, foldedCircle z₀ r) :=
    fun z hz => gff_integral_mul (p := (νk, μ₀)) (q := (foldedCircle z r, foldedCircle z₀ r)) hX hkA h0A hqU (hcA z (hKR z hz)) (hcA z₀ hz₀R) (h11 z)
  have hEDD : ∫ ω, D ω * D ω ∂P = kernelCov2 neumannH (νk, μ₀) (νk, μ₀) :=
    gff_integral_mul (p := (νk, μ₀)) (q := (νk, μ₀)) hX hkA h0A hqU hkA h0A hqU
  -- a jointly measurable version of `Y`
  obtain ⟨Z, hZm, hZc, hZY, hZW⟩ := exists_measurable_version hYc hWm hY
  have hZL2 : ∀ z ∈ K, MemLp (Z z) 2 P := fun z hz =>
    (hWL2 z hz).ae_eq (hZW z (hKH hz)).symm
  -- the uniform variance bound
  set b := (nBound (foldedCircle z₀ r) (foldedCircle z₀ r) R Cc).toReal with hb_def
  have hkc : ∀ z z', ‖z‖ ≤ R₀ → ‖z'‖ ≤ R₀ →
      |kernelCov neumannH (foldedCircle z r) (foldedCircle z' r)| ≤ b := by
    intro z z' hz hz'
    have := abs_kernelCov_le (hcS z hz) (hcS z' hz') hCct (hcP z')
    have he : nBound (foldedCircle z r) (foldedCircle z' r) R Cc
        = nBound (foldedCircle z₀ r) (foldedCircle z₀ r) R Cc := by
      simp only [nBound, measure_univ]
    rwa [he] at this
  have hB : ∀ z ∈ K, ∫ ω, Z z ω ^ 2 ∂P ≤ 4 * b := by
    intro z hz
    have e1 : ∫ ω, Z z ω ^ 2 ∂P = ∫ ω, W z ω * W z ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hZW z (hKH hz)] with ω hω
      rw [hω, sq]
    rw [e1, hEWW z hz z hz]
    simp only [kernelCov2]
    have a1 := abs_le.1 (hkc z z (hKR z hz) (hKR z hz))
    have a2 := abs_le.1 (hkc z z₀ (hKR z hz) hz₀R)
    have a3 := abs_le.1 (hkc z₀ z hz₀R (hKR z hz))
    have a4 := abs_le.1 (hkc z₀ z₀ hz₀R hz₀R)
    linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  have hmom : ∀ z ∈ K, Integrable (fun ω => Z z ω ^ 2) P := fun z hz =>
    (hZL2 z hz).integrable_sq
  -- linearity of the covariance under `bind`
  have hae : ∀ᵐ z ∂ν, z ∈ K := mem_ae_iff.mpr hνK
  have hsmul : ∀ μ' : Measure ℂ, kernelCov neumannH μ₀ μ'
      = (ν Set.univ).toReal * kernelCov neumannH (foldedCircle z₀ r) μ' := by
    intro μ'; simp only [kernelCov, hμ₀_def, integral_smul_measure, smul_eq_mul]
  have hlin2 : ∀ (a b' : Measure ℂ) [IsFiniteMeasure a] [IsFiniteMeasure b'],
      a (ballH R)ᶜ = 0 → b' (ballH R)ᶜ = 0 → ∀ {C C' : ℝ≥0∞}, C ≠ ⊤ → C' ≠ ⊤ →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂a ≤ C) →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂b' ≤ C') →
      ∫ w, kernelCov2 neumannH (foldedCircle w r, foldedCircle z₀ r) (a, b') ∂ν
        = kernelCov2 neumannH (νk, μ₀) (a, b') := by
    intro a b' _ _ ha hb' C C' hC hC' hCa hCb
    obtain ⟨ia, ea⟩ := kernelCov_bind ν hkS ha hC hCa
    obtain ⟨ib, eb⟩ := kernelCov_bind ν hkS hb' hC' hCb
    simp only [kernelCov2]
    rw [integral_add (f := fun w => kernelCov neumannH (foldedCircle w r) a
          - kernelCov neumannH (foldedCircle w r) b' - kernelCov neumannH (foldedCircle z₀ r) a)
        (g := fun _ => kernelCov neumannH (foldedCircle z₀ r) b')
        ((ia.sub ib).sub (integrable_const _)) (integrable_const _),
      integral_sub (f := fun w => kernelCov neumannH (foldedCircle w r) a
          - kernelCov neumannH (foldedCircle w r) b')
        (g := fun _ => kernelCov neumannH (foldedCircle z₀ r) a) (ia.sub ib) (integrable_const _),
      integral_sub ia ib, ea, eb,
      integral_const, integral_const, smul_eq_mul, smul_eq_mul, measureReal_def, hsmul, hsmul]
  -- the second moments of `L = ∫ Z z dν`
  obtain ⟨hLm, hLL2⟩ := memLp_integral (B := 4 * b) hZm hνK hK hZc hmom hB
  set L : Ω → ℝ := fun ω => ∫ z, Z z ω ∂ν with hL_def
  have hZmz : ∀ z, Measurable (Z z) := fun z => hZm.of_uncurry_left
  have hZD : ∀ z ∈ K, ∫ ω, Z z ω * D ω ∂P
      = kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r) (νk, μ₀) := by
    intro z hz
    rw [← hEWD z hz]
    refine integral_congr_ae ?_
    filter_upwards [hZW z (hKH hz)] with ω hω
    rw [hω]
  have E1 : ∫ ω, L ω * D ω ∂P = kernelCov2 neumannH (νk, μ₀) (νk, μ₀) := by
    rw [fubini_mul hZm hνK hmom hB hDm hDL2]
    calc ∫ z, ∫ ω, Z z ω * D ω ∂P ∂ν
        = ∫ z, kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r) (νk, μ₀) ∂ν :=
          integral_congr_ae (hae.mono fun z hz => hZD z hz)
      _ = _ := hlin2 νk μ₀ hkS h0S hmCt hmCt hkP h0P
  have E2 : ∫ ω, L ω * L ω ∂P = ∫ ω, L ω * D ω ∂P := by
    rw [fubini_mul hZm hνK hmom hB hLm hLL2, fubini_mul hZm hνK hmom hB hDm hDL2]
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    show ∫ ω, Z z ω * L ω ∂P = ∫ ω, Z z ω * D ω ∂P
    have i1 : ∫ ω, Z z ω * L ω ∂P = ∫ ω, L ω * Z z ω ∂P := by simp_rw [mul_comm]
    rw [i1, fubini_mul hZm hνK hmom hB (hZmz z) (hZL2 z hz)]
    calc ∫ z', ∫ ω, Z z' ω * Z z ω ∂P ∂ν
        = ∫ z', kernelCov2 neumannH (foldedCircle z' r, foldedCircle z₀ r)
            (foldedCircle z r, foldedCircle z₀ r) ∂ν := by
          refine integral_congr_ae (hae.mono fun z' hz' => ?_)
          show ∫ ω, Z z' ω * Z z ω ∂P = _
          beta_reduce
          rw [← hEWW z' hz' z hz]
          refine integral_congr_ae ?_
          filter_upwards [hZW z (hKH hz), hZW z' (hKH hz')] with ω hω hω'
          rw [hω, hω']
      _ = kernelCov2 neumannH (νk, μ₀) (foldedCircle z r, foldedCircle z₀ r) :=
          hlin2 _ _ (hcS z (hKR z hz)) (hcS z₀ hz₀R) hCct hCct (hcP z) (hcP z₀)
      _ = ∫ ω, Z z ω * D ω ∂P := by
          rw [← hEDW z hz]
          refine integral_congr_ae ?_
          filter_upwards [hZW z (hKH hz)] with ω hω
          rw [hω, mul_comm]
  -- conclusion: `E[(L - D)²] = 0`
  have hsq : ∫ ω, (L ω - D ω) ^ 2 ∂P = 0 := by
    have : ∀ ω, (L ω - D ω) ^ 2 = (L ω * L ω - 2 * (L ω * D ω)) + D ω * D ω := fun ω => by
      ring
    simp_rw [this]
    have iLL := integrable_mul_of_memLp_two hLL2 hLL2
    have iLD := integrable_mul_of_memLp_two hLL2 hDL2
    have iDD := integrable_mul_of_memLp_two hDL2 hDL2
    rw [integral_add (f := fun ω => L ω * L ω - 2 * (L ω * D ω)) (g := fun ω => D ω * D ω)
        (iLL.sub (iLD.const_mul 2)) iDD,
      integral_sub (f := fun ω => L ω * L ω) (g := fun ω => 2 * (L ω * D ω)) iLL
        (iLD.const_mul 2),
      integral_const_mul, E2, E1, hEDD]
    ring
  have hint : Integrable (fun ω => (L ω - D ω) ^ 2) P := (hLL2.sub hDL2).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (L ω - D ω)) hint).1 hsq
  filter_upwards [h0, hZY] with ω hω hωY
  have hLD : L ω = D ω := by
    have h2 : (L ω - D ω) ^ 2 = 0 := hω
    have := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h2
    linarith
  show ∫ z, Y z ω ∂ν = D ω
  rw [← hLD]
  exact integral_congr_ae (hae.mono fun z hz => (hωY z (hKH hz)).symm)

end ASep
end QuantumZipper
