import QuantumZipper.Proofs.LQG.PalmFree
import QuantumZipper.Proofs.LQG.AreaExistenceAS

/-!
# Blueprint S5-D1 (area): the Palm formula for the quantum area measure

Part 1 (abstract). For `Y = ofFun m + Z`, `Z` a centered Gaussian field, `m` continuous, and a
random measure `μ_Y` on `ℂ` which is the `L¹` limit of `areaApprox γ Y k` (tested against
continuous functions supported in a compact `K ⊆ ℍ`): for a continuous nonnegative weight `w`
vanishing off `K` and bounded measurable `φ`,
`E ∫ w(z) φ(Y,z) μ_Y(dz) = ∫ w(z) ρ(z) E φ(Y + ofFun(γ c(z,·)), z) dz`,
`ρ(z) = exp(γ m(z) + γ² c̃(z)/2)`, where `c̃(z) = lim (Var Z(fc(z,2^{-k})) + log 2^{-k})` and
`Cov(Z μ, Z(fc(z,2^{-k}))) → ∫ c(z,·) dμ`. The normalization: the level-`k` density is
`r^{γ²/2} e^{γ Y(fc(z,r))} = exp(γ m_k(z) + γ²(Var_k + log r)/2) · (Cameron–Martin tilt by γ)`.
(`palm_formula_area_weight`.)

Part 2 (free field, `Y = ofFun m + aZ X R`, `aZ = zField`): `c = freeKernelC R` with
`freeKernelC R z w = neumannH z w − fcPot R 0 w` and `c̃(z) = 2 log R − log ‖z − z̄‖`
(`palm_formula_area_free`).

Part 3: `γ c(z,·) = γ(−log ‖· − z‖) + h_z` with `h_z = −γ log ‖· − z̄‖ − γ fcPot R 0`
continuous on `Hbar` for `z ∈ ℍ` (`mul_freeKernelC_eq`, `continuousOn_freeKernelC_rem`): at
interior points the singularity is `γ(−log|· − z|)`, not doubled as at boundary points.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

set_option linter.unusedSectionVars false

namespace QuantumZipper
namespace PalmArea

open Palm (IsCenteredGaussianField coords measurable_field measurable_coords comb_single
  covShift_single covNorm_single isSFiniteKernel_of_ne_top)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The level-`k` folded circle at `z`. -/
abbrev fcZ (z : ℂ) (k : ℕ) : Measure ℂ := foldedCircle z (radius k)

lemma ae_fcZ_ballH (z : ℂ) (k : ℕ) : ∀ᵐ w ∂fcZ z k, w ∈ CircleFubini.ballH (‖z‖ + 1) :=
  ae_iff.2 (CircleFubini.foldedCircle_support (radius_pos k).le
    (by linarith [BdryExist.radius_le_one k]))

lemma exists_bound_fcZ {m : ℂ → ℝ} (hm : ContinuousOn m Hbar) {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) :
    ∃ M, 0 ≤ M ∧ ∀ k, ∀ z ∈ K, (∀ᵐ w ∂fcZ z k, ‖m w‖ ≤ M) ∧ ‖m z‖ ≤ M := by
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := (CircleFubini.isCompact_ballH (ρ + 1)).exists_bound_of_continuousOn
    (hm.mono inter_subset_right)
  refine ⟨max C 0, le_max_right _ _, fun k z hz => ⟨?_, ?_⟩⟩
  · filter_upwards [ae_fcZ_ballH z k] with w hw
    refine (hC w ⟨?_, hw.2⟩).trans (le_max_left _ _)
    have h1 := hw.1
    rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
    linarith [hρ z hz]
  · refine (hC z ⟨?_, hKH hz⟩).trans (le_max_left _ _)
    rw [Metric.mem_closedBall, dist_zero_right]; linarith [hρ z hz]

/-- The level-`k` mean `∫ m d(fcZ z k)`. -/
def meanA (m : ℂ → ℝ) (z : ℂ) (k : ℕ) : ℝ := ∫ w, m w ∂(fcZ z k)

lemma tendsto_meanA {m : ℂ → ℝ} (hm : ContinuousOn m Hbar) {z : ℂ} (hz : z ∈ Hbar) :
    Tendsto (fun k => meanA m z k) atTop (𝓝 (m z)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := GoodSample.smooth_unif hm isCompact_singleton (singleton_subset_iff.2 hz) ε hε
  filter_upwards [RegClosure.tendsto_radius_nhdsGT.eventually h] with k hk
  rw [Real.dist_eq]; exact hk z rfl

/-! ## 1. The abstract setting -/

variable {Z : Ω → FieldSample} {m : ℂ → ℝ} {μ : ℕ → Measure ℂ} {γ : ℝ}

/-- Level-`k` variance. -/
def varA (Z : Ω → FieldSample) (P : Measure Ω) (z : ℂ) (k : ℕ) : ℝ :=
  Var[fun ω => Z ω (fcZ z k); P]

/-- Level-`k` first-moment density `exp(γ m_k(z) + γ²(Var_k(z) + log 2^{-k})/2)`. -/
def rhoKA (γ : ℝ) (m : ℂ → ℝ) (Z : Ω → FieldSample) (P : Measure Ω) (z : ℂ) (k : ℕ) : ℝ :=
  Real.exp (γ * meanA m z k + γ ^ 2 / 2 * (varA Z P z k + Real.log (radius k)))

/-- Level-`k` shift `γ Cov(Z(μ j), Z(fcZ z k))`. -/
def shiftKA (γ : ℝ) (Z : Ω → FieldSample) (P : Measure Ω) (μ : ℕ → Measure ℂ) (z : ℂ) (k : ℕ) :
    ℕ → ℝ :=
  fun j => γ * cov[fun ω => Z ω (μ j), fun ω => Z ω (fcZ z k); P]

/-- The density of `areaApprox γ (ofFun m + Z ω) k` at `z` (on `ℍ`). -/
def densA (γ : ℝ) (m : ℂ → ℝ) (Z : Ω → FieldSample) (k : ℕ) (ω : Ω) (z : ℂ) : ℝ :=
  radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg (ofFun m + Z ω) k z)

/-- The limiting shift `γ ∫ c(z,·) dμ_j`. -/
def shiftLimA (γ : ℝ) (c : ℂ → ℂ → ℝ) (μ : ℕ → Measure ℂ) (z : ℂ) : ℕ → ℝ :=
  fun j => γ * ∫ w, c z w ∂(μ j)

/-- The first-moment density `ρ(z) = exp(γ m(z) + γ² c̃(z)/2)`. -/
def rhoLimA (γ : ℝ) (m : ℂ → ℝ) (ctil : ℂ → ℝ) (z : ℂ) : ℝ :=
  Real.exp (γ * m z + γ ^ 2 * ctil z / 2)

lemma measurable_densA (hZ : IsCenteredGaussianField P Z) (k : ℕ) :
    Measurable fun p : Ω × ℂ => densA γ m Z k p.1 p.2 := by
  unfold densA
  have h1 : Measurable fun p : Ω × ℂ => avgReg (ofFun m + Z p.1) k p.2 :=
    (measurable_avgReg k).comp (((measurable_field hZ).comp measurable_fst).prodMk measurable_snd)
  exact measurable_const.mul ((h1.const_mul _).exp)

lemma densA_nonneg (k : ℕ) (ω : Ω) (z : ℂ) : 0 ≤ densA γ m Z k ω z :=
  mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le

/-- The Cameron–Martin index used at level `k`. -/
abbrev sigA (γ : ℝ) (z : ℂ) (k : ℕ) : Measure ℂ →₀ ℝ := Finsupp.single (fcZ z k) γ

lemma densA_ae_eq (hZ : IsCenteredGaussianField P Z) {z : ℂ} {k : ℕ}
    (hreg : ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k)) :
    ∀ᵐ ω ∂P, densA γ m Z k ω z = rhoKA γ m Z P z k *
      CameronMartin.tiltDensity (fun ν ω => Z ω ν) P (sigA γ z k) ω := by
  filter_upwards [hreg] with ω hω
  unfold densA rhoKA CameronMartin.tiltDensity varA
  rw [hω, comb_single, covNorm_single]
  simp only [CameronMartin.covK]
  rw [covariance_self (hZ.meas _).aemeasurable, Real.rpow_def_of_pos (radius_pos k),
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Pi.add_apply, ofFun, meanA]
  ring

lemma integral_mul_densA (hZ : IsCenteredGaussianField P Z) {z : ℂ} {k : ℕ}
    (hreg : ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k))
    (G : (ℕ → ℝ) → ℝ) (hG : Measurable G) :
    ∫ ω, G (coords m Z μ ω) * densA γ m Z k ω z ∂P =
      rhoKA γ m Z P z k * ∫ ω, G (coords m Z μ ω + shiftKA γ Z P μ z k) ∂P := by
  rw [integral_congr_ae ((densA_ae_eq hZ hreg).mono fun ω h => by rw [h, mul_left_comm])]
  rw [integral_const_mul]
  congr 1
  have hΦ : Measurable fun y : Measure ℂ → ℝ => G (fun j => ofFun m (μ j) + y (μ j)) :=
    hG.comp (measurable_pi_iff.mpr fun j => (measurable_pi_apply (μ j)).const_add _)
  have key := CameronMartin.integral_mul_tiltDensity (X := fun ν ω => Z ω ν) hZ.gauss hZ.meas
    hZ.cent (sigA γ z k) _ hΦ
  have e1 : ∀ ω, coords m Z μ ω = fun j => ofFun m (μ j) + Z ω (μ j) := fun ω => rfl
  have e2 : ∀ ω, coords m Z μ ω + shiftKA γ Z P μ z k = fun j => ofFun m (μ j) +
      (Z ω (μ j) + CameronMartin.covShift (fun ν ω => Z ω ν) P (sigA γ z k) (μ j)) := by
    intro ω; funext j
    simp only [coords, shiftKA, covShift_single, CameronMartin.covK, Pi.add_apply]
    ring
  simp_rw [e2, e1]
  exact key

lemma integrable_densA (hZ : IsCenteredGaussianField P Z) {z : ℂ} {k : ℕ}
    (hreg : ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k)) :
    Integrable (fun ω => densA γ m Z k ω z) P ∧
      ∫ ω, densA γ m Z k ω z ∂P = rhoKA γ m Z P z k := by
  have := hZ.gauss.isProbabilityMeasure
  refine ⟨?_, ?_⟩
  · exact ((CameronMartin.tiltDensity_integral hZ.gauss hZ.meas hZ.cent (sigA γ z k)).1.const_mul
      (rhoKA γ m Z P z k)).congr ((densA_ae_eq hZ hreg).mono fun ω h => h.symm)
  · have := integral_mul_densA (γ := γ) (μ := fun _ => 0) hZ hreg (fun _ => 1) measurable_const
    simpa using this

lemma exists_bound_rhoA (hm : ContinuousOn m Hbar) {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) {Cv : ℝ} {ctil : ℂ → ℝ}
    (hvarbd : ∀ k, ∀ z ∈ K, varA Z P z k + Real.log (radius k) ≤ Cv)
    (hvar : ∀ z ∈ K, Tendsto (fun k => varA Z P z k + Real.log (radius k)) atTop
      (𝓝 (ctil z))) :
    ∃ B, 0 < B ∧ ∀ z ∈ K, (∀ k, rhoKA γ m Z P z k ≤ B) ∧ rhoLimA γ m ctil z ≤ B := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fcZ hm hK hKH
  refine ⟨Real.exp (|γ| * M + γ ^ 2 / 2 * Cv), Real.exp_pos _, fun z hz => ⟨fun k => ?_, ?_⟩⟩
  · have hmk : |meanA m z k| ≤ M := by
      have := norm_integral_le_of_norm_le_const (hM k z hz).1
      rwa [probReal_univ, mul_one] at this
    unfold rhoKA
    refine Real.exp_le_exp.mpr (add_le_add ?_ ?_)
    · exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hmk (abs_nonneg _))
    · exact mul_le_mul_of_nonneg_left (hvarbd k z hz) (by positivity)
  · have hc : ctil z ≤ Cv := le_of_tendsto' (hvar z hz) fun k => hvarbd k z hz
    have hmx : |m z| ≤ M := by have := (hM 0 z hz).2; rwa [Real.norm_eq_abs] at this
    unfold rhoLimA
    refine Real.exp_le_exp.mpr ?_
    have : γ * m z ≤ |γ| * M :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hmx (abs_nonneg _))
    have : γ ^ 2 * ctil z ≤ γ ^ 2 * Cv := mul_le_mul_of_nonneg_left hc (by positivity)
    linarith

lemma setIntegral_areaApprox (y : FieldSample) (k : ℕ) {K : Set ℂ} (hK : MeasurableSet K)
    (hKH : K ⊆ H) (f : ℂ → ℝ) :
    ∫ z in K, f z ∂(areaApprox γ y k) =
      ∫ z in K, f z * (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z)) := by
  have hm : Measurable (fun z : ℂ => avgReg y k z) :=
    (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
  have hg : Measurable (fun z : ℂ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((hm.const_mul _).exp))
  unfold areaApprox
  rw [restrict_withDensity hK, Measure.restrict_restrict hK, inter_eq_left.2 hKH,
    integral_withDensity_eq_integral_toReal_smul hg (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (radius_pos k).le _)
    (Real.exp_pos _).le)]
  ring

section LevelK

variable {K : Set ℂ} {F : (ℕ → ℝ) → ℂ → ℝ} {CF : ℝ}

lemma integrable_prod_F_densA (hZ : IsCenteredGaussianField P Z) (hm : ContinuousOn m Hbar)
    (hK : IsCompact K) (hKH : K ⊆ Hbar) {Cv : ℝ} {ctil : ℂ → ℝ}
    (hreg : ∀ k, ∀ z ∈ K, ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k))
    (hvarbd : ∀ k, ∀ z ∈ K, varA Z P z k + Real.log (radius k) ≤ Cv)
    (hvar : ∀ z ∈ K, Tendsto (fun k => varA Z P z k + Real.log (radius k)) atTop
      (𝓝 (ctil z)))
    (hF : Measurable (Function.uncurry F)) (hFb : ∀ y z, |F y z| ≤ CF) (k : ℕ) :
    Integrable (Function.uncurry fun ω z => F (coords m Z μ ω) z * densA γ m Z k ω z)
      (P.prod (volume.restrict K)) := by
  have := hZ.gauss.isProbabilityMeasure
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨B, -, hB⟩ := exists_bound_rhoA (γ := γ) hm hK hKH hvarbd hvar
  have hmeas : Measurable (Function.uncurry fun ω z => F (coords m Z μ ω) z * densA γ m Z k ω z) :=
    (hF.comp (((measurable_coords hZ).comp measurable_fst).prodMk measurable_snd)).mul
      (measurable_densA hZ k)
  refine (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact (integrable_densA (γ := γ) hZ (hreg k z hz)).1.bdd_mul
      ((hF.comp ((measurable_coords hZ).prodMk measurable_const)).aestronglyMeasurable)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hFb _ _)
  · refine Integrable.of_bound ?_ (CF * B) ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left (μ := P)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      obtain ⟨hi, hv⟩ := integrable_densA (γ := γ) hZ (hreg k z hz)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ ω, ‖F (coords m Z μ ω) z * densA γ m Z k ω z‖ ∂P
          ≤ ∫ ω, CF * densA γ m Z k ω z ∂P := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (hi.const_mul CF) (ae_of_all _ fun ω => ?_)
            simp only
            rw [norm_mul, Real.norm_of_nonneg (densA_nonneg k ω z), Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hFb _ _) (densA_nonneg k ω z)
        _ = CF * rhoKA γ m Z P z k := by rw [integral_const_mul, hv]
        _ ≤ CF * B := mul_le_mul_of_nonneg_left ((hB z hz).1 k)
            ((abs_nonneg _).trans (hFb 0 0))

/-- **Level-`k` Palm identity** for the area. -/
lemma palm_levelKA (hZ : IsCenteredGaussianField P Z) (hm : ContinuousOn m Hbar)
    (hK : IsCompact K) (hKH : K ⊆ H) {Cv : ℝ} {ctil : ℂ → ℝ}
    (hreg : ∀ k, ∀ z ∈ K, ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k))
    (hvarbd : ∀ k, ∀ z ∈ K, varA Z P z k + Real.log (radius k) ≤ Cv)
    (hvar : ∀ z ∈ K, Tendsto (fun k => varA Z P z k + Real.log (radius k)) atTop
      (𝓝 (ctil z)))
    (hF : Measurable (Function.uncurry F)) (hFb : ∀ y z, |F y z| ≤ CF) (k : ℕ) :
    ∫ ω, ∫ z in K, F (coords m Z μ ω) z ∂(areaApprox γ (ofFun m + Z ω) k) ∂P =
      ∫ z in K, rhoKA γ m Z P z k * ∫ ω, F (coords m Z μ ω + shiftKA γ Z P μ z k) z ∂P := by
  have := hZ.gauss.isProbabilityMeasure
  simp_rw [setIntegral_areaApprox _ k hK.measurableSet hKH]
  change ∫ ω, (∫ z in K, F (coords m Z μ ω) z * densA γ m Z k ω z) ∂P = _
  rw [integral_integral_swap (integrable_prod_F_densA hZ hm hK (hKH.trans H_subset_Hbar) hreg
    hvarbd hvar hF hFb k)]
  refine setIntegral_congr_fun hK.measurableSet fun z hz => ?_
  exact integral_mul_densA hZ (hreg k z hz) (fun y => F y z)
    (hF.comp (measurable_id.prodMk measurable_const))

lemma measurable_F_densA (hZ : IsCenteredGaussianField P Z) (hF : Measurable (Function.uncurry F))
    (k : ℕ) :
    Measurable (Function.uncurry fun ω z => F (coords m Z μ ω) z * densA γ m Z k ω z) :=
  (hF.comp (((measurable_coords hZ).comp measurable_fst).prodMk measurable_snd)).mul
    (measurable_densA hZ k)

lemma tendsto_rhsA (hZ : IsCenteredGaussianField P Z) (hm : ContinuousOn m Hbar)
    (hK : IsCompact K) (hKH : K ⊆ Hbar) {Cv : ℝ} {ctil : ℂ → ℝ} {c : ℂ → ℂ → ℝ}
    (hreg : ∀ k, ∀ z ∈ K, ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k))
    (hvarbd : ∀ k, ∀ z ∈ K, varA Z P z k + Real.log (radius k) ≤ Cv)
    (hvar : ∀ z ∈ K, Tendsto (fun k => varA Z P z k + Real.log (radius k)) atTop
      (𝓝 (ctil z)))
    (hcov : ∀ z ∈ K, ∀ j, Tendsto
      (fun k => cov[fun ω => Z ω (μ j), fun ω => Z ω (fcZ z k); P]) atTop
      (𝓝 (∫ w, c z w ∂(μ j))))
    (hF : Measurable (Function.uncurry F)) (hFb : ∀ y z, |F y z| ≤ CF)
    (hFc : ∀ z, Continuous fun y => F y z) :
    Tendsto (fun k => ∫ z in K, rhoKA γ m Z P z k *
        ∫ ω, F (coords m Z μ ω + shiftKA γ Z P μ z k) z ∂P) atTop
      (𝓝 (∫ z in K, rhoLimA γ m ctil z *
        ∫ ω, F (coords m Z μ ω + shiftLimA γ c μ z) z ∂P)) := by
  have := hZ.gauss.isProbabilityMeasure
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨B, hB0, hB⟩ := exists_bound_rhoA (γ := γ) hm hK hKH hvarbd hvar
  replace hB0 := hB0.le
  have hIa : ∀ᵐ z ∂(volume.restrict K), z ∈ K := ae_restrict_mem hK.measurableSet
  have hnorm : ∀ (z : ℂ) (v : ℕ → ℝ), ‖∫ ω, F (coords m Z μ ω + v) z ∂P‖ ≤ CF := by
    intro z v
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => F (coords m Z μ ω + v) z)
      (C := CF) (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hFb _ _)
    rwa [probReal_univ, mul_one] at this
  refine tendsto_integral_of_dominated_convergence (fun _ => B * CF) (fun k => ?_)
    (integrable_const _) (fun k => ?_) ?_
  · have hsm := (measurable_F_densA (m := m) (μ := μ) (γ := γ) hZ hF k).stronglyMeasurable.integral_prod_left
      (μ := P)
    refine hsm.aestronglyMeasurable.congr ?_
    filter_upwards [hIa] with z hz
    exact integral_mul_densA hZ (hreg k z hz) (fun y => F y z)
      (hF.comp (measurable_id.prodMk measurable_const))
  · filter_upwards [hIa] with z hz
    rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ rhoKA γ m Z P z k from (Real.exp_pos _).le)]
    exact mul_le_mul ((hB z hz).1 k) (hnorm z _) (norm_nonneg _) hB0
  · filter_upwards [hIa] with z hz
    refine Tendsto.mul ?_ ?_
    · unfold rhoKA rhoLimA
      refine (Real.continuous_exp.tendsto _).comp ?_
      have h1 := (tendsto_meanA hm (hKH hz)).const_mul γ
      have h2 := (hvar z hz).const_mul (γ ^ 2 / 2)
      convert h1.add h2 using 2
      ring
    · refine tendsto_integral_of_dominated_convergence (fun _ => CF) (fun k => ?_)
        (integrable_const _) (fun k => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
      · exact ((hF.comp (measurable_id.prodMk measurable_const)).comp
          ((measurable_coords hZ).add_const _)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]; exact hFb _ _
      · have hs : Tendsto (fun k => shiftKA γ Z P μ z k) atTop (𝓝 (shiftLimA γ c μ z)) :=
          tendsto_pi_nhds.mpr fun j => by
            simpa only [shiftKA, shiftLimA] using (hcov z hz j).const_mul γ
        exact ((hFc z).tendsto _).comp (tendsto_const_nhds.add hs)

end LevelK

/-! ## 2. Random measures on `ℂ` -/

section RandomMeasure

variable {ν : Ω → Measure ℂ} {I : Set ℂ}

open Classical in
/-- A measurable version of `ν`, finite on `I` everywhere. -/
def nuModC (hν : AEMeasurable ν P) (I : Set ℂ) (ω : Ω) : Measure ℂ :=
  if hν.mk ν ω I < ∞ then hν.mk ν ω else 0

lemma measurable_nuModC (hν : AEMeasurable ν P) (hI : MeasurableSet I) :
    Measurable (nuModC hν I) := by
  classical
  unfold nuModC
  exact Measurable.ite (measurableSet_lt ((Measure.measurable_coe hI).comp hν.measurable_mk)
    measurable_const) hν.measurable_mk measurable_const

lemma nuModC_ae_eq (hν : AEMeasurable ν P) (hI : MeasurableSet I)
    (hfin : ∫⁻ ω, ν ω I ∂P < ∞) : ∀ᵐ ω ∂P, nuModC hν I ω = ν ω := by
  have h2 : ∀ᵐ ω ∂P, ν ω I < ∞ :=
    ae_lt_top' ((Measure.measurable_coe hI).comp_aemeasurable hν) hfin.ne
  filter_upwards [hν.ae_eq_mk, h2] with ω h1 h2
  unfold nuModC
  rw [← h1, ite_eq_left h2]

lemma nuModC_lt_top (hν : AEMeasurable ν P) (ω : Ω) : nuModC hν I ω I < ∞ := by
  unfold nuModC
  split_ifs with h
  · exact h
  · simp

/-- The kernel `ω ↦ (nuModC ω)|_I`. -/
def kerIC (hν : AEMeasurable ν P) (hI : MeasurableSet I) : Kernel Ω ℂ where
  toFun ω := (nuModC hν I ω).restrict I
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp_rw [Measure.restrict_apply hs]
    exact (Measure.measurable_coe (hs.inter hI)).comp (measurable_nuModC hν hI)

lemma kerIC_apply (hν : AEMeasurable ν P) (hI : MeasurableSet I) (ω : Ω) :
    kerIC hν hI ω = (nuModC hν I ω).restrict I := rfl

instance (hν : AEMeasurable ν P) (hI : MeasurableSet I) : IsSFiniteKernel (kerIC hν hI) :=
  isSFiniteKernel_of_ne_top _ fun ω => by
    rw [kerIC_apply, Measure.restrict_apply_univ]; exact (nuModC_lt_top hν ω).ne

lemma isFiniteMeasure_kerIC (hν : AEMeasurable ν P) (hI : MeasurableSet I) (ω : Ω) :
    IsFiniteMeasure (kerIC hν hI ω) := by
  rw [kerIC_apply]; exact isFiniteMeasure_restrict.mpr (nuModC_lt_top hν ω).ne

lemma lintegral_kerIC (hν : AEMeasurable ν P) (hI : MeasurableSet I)
    (hfin : ∫⁻ ω, ν ω I ∂P < ∞) : ∫⁻ ω, kerIC hν hI ω univ ∂P < ∞ := by
  simp_rw [kerIC_apply, Measure.restrict_apply_univ]
  rwa [lintegral_congr_ae ((nuModC_ae_eq hν hI hfin).mono fun ω h => by rw [h])]

lemma integrable_setIntegral_nuC (hν : AEMeasurable ν P) (hI : MeasurableSet I)
    (hfin : ∫⁻ ω, ν ω I ∂P < ∞) (h : ℂ →ᵇ ℝ) :
    Integrable (fun ω => ∫ x in I, h x ∂(ν ω)) P := by
  set κ := kerIC hν hI
  have hsm : StronglyMeasurable fun ω => ∫ x, h x ∂(κ ω) :=
    h.continuous.stronglyMeasurable.integral_kernel
  have hbd : Integrable (fun ω => ‖h‖ * (κ ω univ).toReal) P :=
    (integrable_toReal_of_lintegral_ne_top ((κ.measurable_coe MeasurableSet.univ).aemeasurable)
      (lintegral_kerIC hν hI hfin).ne).const_mul _
  have hA' : Integrable (fun ω => ∫ x, h x ∂(κ ω)) P := by
    refine hbd.mono' hsm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := isFiniteMeasure_kerIC hν hI ω
    have := norm_integral_le_of_norm_le_const (μ := κ ω) (f := fun x => h x)
      (ae_of_all _ fun x => h.norm_coe_le_norm x)
    rwa [measureReal_def] at this
  refine hA'.congr ((nuModC_ae_eq hν hI hfin).mono fun ω hω => ?_)
  simp only [κ, kerIC_apply, hω]

end RandomMeasure

/-! ## 3. Limits and the weighted Palm formula -/

/-- `L¹` convergence of the approximating area measures of `ofFun m + Z` to `ν`, tested against
continuous compactly supported functions vanishing off `K`. -/
def AreaL1ConvCc (γ : ℝ) (m : ℂ → ℝ) (Z : Ω → FieldSample) (P : Measure Ω)
    (ν : Ω → Measure ℂ) (K : Set ℂ) : Prop :=
  ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∀ z ∉ K, f z = 0) →
    Tendsto (fun k => ∫ ω, |∫ z, f z ∂(areaApprox γ (ofFun m + Z ω) k) -
      ∫ z, f z ∂(ν ω)| ∂P) atTop (𝓝 0)

section Weighted

variable {K : Set ℂ} {ν : Ω → Measure ℂ}

lemma tendsto_lhs_singleA (hZ : IsCenteredGaussianField P Z) (hm : ContinuousOn m Hbar)
    (hK : IsCompact K) (hKH : K ⊆ H) {Cv : ℝ} {ctil : ℂ → ℝ}
    (hreg : ∀ k, ∀ z ∈ K, ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k))
    (hvarbd : ∀ k, ∀ z ∈ K, varA Z P z k + Real.log (radius k) ≤ Cv)
    (hvar : ∀ z ∈ K, Tendsto (fun k => varA Z P z k + Real.log (radius k)) atTop
      (𝓝 (ctil z)))
    (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω K ∂P < ∞)
    {g : (ℕ → ℝ) → ℝ} {Cg : ℝ} (hg : Measurable g) (hgb : ∀ y, |g y| ≤ Cg) (h : ℂ →ᵇ ℝ)
    (hL1 : Tendsto (fun k => ∫ ω, |∫ z in K, h z ∂(areaApprox γ (ofFun m + Z ω) k) -
      ∫ z in K, h z ∂(ν ω)| ∂P) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, g (coords m Z μ ω) *
        ∫ z in K, h z ∂(areaApprox γ (ofFun m + Z ω) k) ∂P) atTop
      (𝓝 (∫ ω, g (coords m Z μ ω) * ∫ z in K, h z ∂(ν ω) ∂P)) := by
  have hA := integrable_setIntegral_nuC hν hK.measurableSet hfin h
  have hAk : ∀ k, Integrable
      (fun ω => ∫ z in K, h z ∂(areaApprox γ (ofFun m + Z ω) k)) P := by
    intro k
    have hint := (integrable_prod_F_densA (μ := μ) (γ := γ) (F := fun _ z => h z) (CF := ‖h‖) hZ
      hm hK (hKH.trans H_subset_Hbar) hreg hvarbd hvar (h.continuous.measurable.comp measurable_snd)
      (fun _ z => by rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm z) k).integral_prod_left
    refine hint.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [setIntegral_areaApprox _ k hK.measurableSet hKH]
    rfl
  have hgm : AEStronglyMeasurable (fun ω => g (coords m Z μ ω)) P :=
    (hg.comp (measurable_coords hZ)).aestronglyMeasurable
  have hgb' : ∀ᵐ ω ∂P, ‖g (coords m Z μ ω)‖ ≤ Cg :=
    ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
    (by simpa using hL1.const_mul Cg)
  rw [← integral_sub ((hAk k).bdd_mul hgm hgb') (hA.bdd_mul hgm hgb'), ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((hAk k).sub hA).abs.const_mul Cg)
    (ae_of_all _ fun ω => ?_)
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)

lemma palm_core_weightA (hZ : IsCenteredGaussianField P Z) (hm : ContinuousOn m Hbar)
    (hK : IsCompact K) (hKH : K ⊆ H) {Cv : ℝ} {ctil : ℂ → ℝ} {c : ℂ → ℂ → ℝ}
    (hreg : ∀ k, ∀ z ∈ K, ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k))
    (hvarbd : ∀ k, ∀ z ∈ K, varA Z P z k + Real.log (radius k) ≤ Cv)
    (hvar : ∀ z ∈ K, Tendsto (fun k => varA Z P z k + Real.log (radius k)) atTop
      (𝓝 (ctil z)))
    (hcov : ∀ z ∈ K, ∀ j, Tendsto
      (fun k => cov[fun ω => Z ω (μ j), fun ω => Z ω (fcZ z k); P]) atTop
      (𝓝 (∫ w, c z w ∂(μ j))))
    (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω K ∂P < ∞)
    (hL1 : AreaL1ConvCc γ m Z P ν K) (w : ℂ →ᵇ ℝ) (hwc : HasCompactSupport w)
    (hwK : ∀ z ∉ K, w z = 0) (g : (ℕ → ℝ) →ᵇ ℝ) (h : ℂ →ᵇ ℝ) :
    ∫ ω, ∫ z in K, w z * (g (coords m Z μ ω) * h z) ∂(ν ω) ∂P =
      ∫ z in K, rhoLimA γ m ctil z *
        ∫ ω, w z * (g (coords m Z μ ω + shiftLimA γ c μ z) * h z) ∂P := by
  set wh : ℂ →ᵇ ℝ := w * h with hwh
  have hwh_apply : ∀ z, wh z = w z * h z := fun z => rfl
  have hgb : ∀ y, |g y| ≤ ‖g‖ := fun y => by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm y
  have hhb : ∀ z, |wh z| ≤ ‖wh‖ := fun z => by
    rw [← Real.norm_eq_abs]; exact wh.norm_coe_le_norm z
  have hFm : Measurable (Function.uncurry fun (y : ℕ → ℝ) (z : ℂ) => g y * wh z) :=
    (g.continuous.measurable.comp measurable_fst).mul
      (wh.continuous.measurable.comp measurable_snd)
  have hFb : ∀ y z, |g y * wh z| ≤ ‖g‖ * ‖wh‖ := fun y z => by
    rw [abs_mul]; exact mul_le_mul (hgb y) (hhb z) (abs_nonneg _) (norm_nonneg _)
  have hvan : ∀ z ∉ K, wh z = 0 := fun z hz => by rw [hwh_apply, hwK z hz, zero_mul]
  have hL1' : Tendsto (fun k => ∫ ω, |∫ z in K, wh z ∂(areaApprox γ (ofFun m + Z ω) k) -
      ∫ z in K, wh z ∂(ν ω)| ∂P) atTop (𝓝 0) := by
    have hc : HasCompactSupport (fun z => wh z) := by
      have : (fun z => wh z) = (⇑w) * (⇑h) := by funext z; rfl
      rw [this]; exact hwc.mul_right
    have := hL1 (fun z => wh z) wh.continuous hc hvan
    refine this.congr fun k => ?_
    congr 1; funext ω
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvan,
      setIntegral_eq_integral_of_forall_compl_eq_zero hvan]
  have hl := tendsto_lhs_singleA (μ := μ) hZ hm hK hKH hreg hvarbd hvar hν hfin
    g.continuous.measurable hgb wh hL1'
  have hr := tendsto_rhsA (γ := γ) (μ := μ) (F := fun y z => g y * wh z) hZ hm hK
    (hKH.trans H_subset_Hbar) hreg hvarbd hvar hcov hFm hFb (fun z => g.continuous.mul continuous_const)
  have heq : ∀ k, ∫ z in K, rhoKA γ m Z P z k *
      ∫ ω, g (coords m Z μ ω + shiftKA γ Z P μ z k) * wh z ∂P =
      ∫ ω, g (coords m Z μ ω) * ∫ z in K, wh z ∂(areaApprox γ (ofFun m + Z ω) k) ∂P := by
    intro k
    have := palm_levelKA (γ := γ) (μ := μ) (F := fun y z => g y * wh z) hZ hm hK hKH hreg hvarbd
      hvar hFm hFb k
    simp_rw [integral_const_mul] at this
    exact this.symm
  have key := tendsto_nhds_unique hl (hr.congr heq)
  have e1 : ∀ ω, ∫ z in K, w z * (g (coords m Z μ ω) * h z) ∂(ν ω) =
      g (coords m Z μ ω) * ∫ z in K, wh z ∂(ν ω) := by
    intro ω
    rw [← integral_const_mul]
    congr 1; funext z; rw [hwh_apply]; ring
  have e2 : ∀ z, ∫ ω, w z * (g (coords m Z μ ω + shiftLimA γ c μ z) * h z) ∂P =
      ∫ ω, g (coords m Z μ ω + shiftLimA γ c μ z) * wh z ∂P := by
    intro z
    congr 1; funext ω; rw [hwh_apply]; ring
  simp_rw [e1, e2]
  exact key

/-- **Weighted area Palm formula (abstract, coordinates form).** -/
theorem palm_formula_area_weight_coords (hZ : IsCenteredGaussianField P Z)
    (hm : ContinuousOn m Hbar) (hmc : Continuous m) (hK : IsCompact K) (hKH : K ⊆ H)
    {Cv : ℝ} {ctil : ℂ → ℝ} (hctil : Measurable ctil) {c : ℂ → ℂ → ℝ}
    (hc : Measurable (Function.uncurry c)) [∀ j, IsFiniteMeasure (μ j)]
    (hreg : ∀ k, ∀ z ∈ K, ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k))
    (hvarbd : ∀ k, ∀ z ∈ K, varA Z P z k + Real.log (radius k) ≤ Cv)
    (hvar : ∀ z ∈ K, Tendsto (fun k => varA Z P z k + Real.log (radius k)) atTop
      (𝓝 (ctil z)))
    (hcov : ∀ z ∈ K, ∀ j, Tendsto
      (fun k => cov[fun ω => Z ω (μ j), fun ω => Z ω (fcZ z k); P]) atTop
      (𝓝 (∫ w, c z w ∂(μ j))))
    (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω K ∂P < ∞)
    (hL1 : AreaL1ConvCc γ m Z P ν K)
    {w : ℂ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ z, 0 ≤ w z)
    (hwK : ∀ z ∉ K, w z = 0)
    {φ : (ℕ → ℝ) → ℂ → ℝ} (hφ : Measurable (Function.uncurry φ)) {Cφ : ℝ}
    (hφb : ∀ y z, |φ y z| ≤ Cφ) :
    ∫ ω, ∫ z, w z * φ (coords m Z μ ω) z ∂(ν ω) ∂P =
      ∫ z, w z * rhoLimA γ m ctil z *
        ∫ ω, φ (coords m Z μ ω + shiftLimA γ c μ z) z ∂P := by
  have := hZ.gauss.isProbabilityMeasure
  have hI : MeasurableSet K := hK.measurableSet
  obtain ⟨Cw, hCw⟩ := hw.bounded_above_of_compact_support hwc
  set wB : ℂ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup w hw Cw hCw with hwB
  have hwB_apply : ∀ z, wB z = w z := fun z => rfl
  have hCw' : ∀ z, |w z| ≤ Cw := fun z => by rw [← Real.norm_eq_abs]; exact hCw z
  set κ := kerIC hν hI with hκ
  obtain ⟨B, hB0, hB⟩ := exists_bound_rhoA (γ := γ) hm hK (hKH.trans H_subset_Hbar) hvarbd hvar
  have hρ : Measurable (rhoLimA γ m ctil) := by
    unfold rhoLimA
    exact Real.measurable_exp.comp ((hmc.measurable.const_mul γ).add
      ((hctil.const_mul (γ ^ 2)).div_const 2))
  have hs : Measurable (shiftLimA γ c μ) := measurable_pi_iff.mpr fun j =>
    (hc.stronglyMeasurable.integral_prod_right (ν := μ j)).measurable.const_mul _
  have hmapL : Measurable fun p : Ω × ℂ => (coords m Z μ p.1, p.2) :=
    ((measurable_coords hZ).comp measurable_fst).prodMk measurable_snd
  have hmapR : Measurable fun p : ℂ × Ω => (coords m Z μ p.2 + shiftLimA γ c μ p.1, p.1) :=
    (((measurable_coords hZ).comp measurable_snd).add (hs.comp measurable_fst)).prodMk
      measurable_fst
  have hfinL : IsFiniteMeasure (P ⊗ₘ κ) := by
    constructor
    rw [Measure.compProd_apply MeasurableSet.univ]
    simpa only [preimage_univ] using lintegral_kerIC hν hI hfin
  set ρN : ℂ → ℝ≥0 := fun z => (rhoLimA γ m ctil z).toNNReal with hρN
  have hρNm : Measurable ρN := hρ.real_toNNReal
  set D := (volume.restrict K).withDensity fun z => (ρN z : ℝ≥0∞) with hD
  have hfinD : IsFiniteMeasure D := by
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ z in K, (ρN z : ℝ≥0∞) ≤ ∫⁻ _ in K, ENNReal.ofReal B := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hI] with z hz
          exact ENNReal.ofReal_le_ofReal (hB z hz).2
      _ < ∞ := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  set wN : ℂ → ℝ≥0 := fun z => (w z).toNNReal with hwN
  have hwNm : Measurable wN := hw.measurable.real_toNNReal
  set ML0 := (P ⊗ₘ κ).map fun p : Ω × ℂ => (coords m Z μ p.1, p.2) with hML0
  set MR0 := (D.prod P).map fun p : ℂ × Ω => (coords m Z μ p.2 + shiftLimA γ c μ p.1, p.1)
    with hMR0
  have hfinML0 : IsFiniteMeasure ML0 := by rw [hML0]; infer_instance
  have hfinMR0 : IsFiniteMeasure MR0 := by rw [hMR0]; infer_instance
  set ML := ML0.withDensity fun p => (wN p.2 : ℝ≥0∞) with hML
  set MR := MR0.withDensity fun p => (wN p.2 : ℝ≥0∞) with hMR
  have hwNle : ∀ p : (ℕ → ℝ) × ℂ, (wN p.2 : ℝ≥0∞) ≤ ENNReal.ofReal Cw := fun p => by
    show ENNReal.ofReal (w p.2) ≤ _
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hCw' _))
  have hfinW : ∀ M : Measure ((ℕ → ℝ) × ℂ), IsFiniteMeasure M →
      IsFiniteMeasure (M.withDensity fun p => (wN p.2 : ℝ≥0∞)) := by
    intro M hM
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ p, (wN p.2 : ℝ≥0∞) ∂M ≤ ∫⁻ _, ENNReal.ofReal Cw ∂M := lintegral_mono hwNle
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hfinML : IsFiniteMeasure ML := hfinW _ hfinML0
  have hfinMR : IsFiniteMeasure MR := hfinW _ hfinMR0
  have hwint : ∀ (M : Measure ((ℕ → ℝ) × ℂ)) (G : (ℕ → ℝ) × ℂ → ℝ),
      ∫ p, G p ∂(M.withDensity fun p => (wN p.2 : ℝ≥0∞)) = ∫ p, w p.2 * G p ∂M := by
    intro M G
    rw [integral_withDensity_eq_integral_smul (f := fun p : (ℕ → ℝ) × ℂ => wN p.2)
      (hwNm.comp measurable_snd)]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hwN, NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (hw0 _)]
  have hLint : ∀ G : (ℕ → ℝ) × ℂ → ℝ, Measurable G → ∀ C, (∀ p, |G p| ≤ C) →
      ∫ p, G p ∂ML = ∫ ω, ∫ z in K, w z * G (coords m Z μ ω, z) ∂(ν ω) ∂P := by
    intro G hG C hC
    have hG' : Measurable fun p : (ℕ → ℝ) × ℂ => w p.2 * G p :=
      (hw.measurable.comp measurable_snd).mul hG
    rw [hML, hwint, hML0, integral_map hmapL.aemeasurable hG'.aestronglyMeasurable,
      Measure.integral_compProd (Integrable.of_bound
        (f := fun p : Ω × ℂ => w p.2 * G (coords m Z μ p.1, p.2))
        (hG'.comp hmapL).aestronglyMeasurable (Cw * C)
        (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hCw' _) (hC _) (abs_nonneg _) ((abs_nonneg _).trans (hCw' 0))))]
    refine integral_congr_ae ((nuModC_ae_eq hν hI hfin).mono fun ω hω => ?_)
    simp only [hκ, kerIC_apply, hω]
  have hRint : ∀ G : (ℕ → ℝ) × ℂ → ℝ, Measurable G → ∀ C, (∀ p, |G p| ≤ C) →
      ∫ p, G p ∂MR = ∫ z in K, rhoLimA γ m ctil z *
        ∫ ω, w z * G (coords m Z μ ω + shiftLimA γ c μ z, z) ∂P := by
    intro G hG C hC
    have hG' : Measurable fun p : (ℕ → ℝ) × ℂ => w p.2 * G p :=
      (hw.measurable.comp measurable_snd).mul hG
    rw [hMR, hwint, hMR0, integral_map hmapR.aemeasurable hG'.aestronglyMeasurable,
      integral_prod _ (Integrable.of_bound
        (f := fun p : ℂ × Ω => w p.1 * G (coords m Z μ p.2 + shiftLimA γ c μ p.1, p.1))
        (hG'.comp hmapR).aestronglyMeasurable (Cw * C)
        (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hCw' _) (hC _) (abs_nonneg _) ((abs_nonneg _).trans (hCw' 0)))),
      hD, integral_withDensity_eq_integral_smul hρNm]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hρN, NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (show 0 ≤ rhoLimA γ m ctil z from (Real.exp_pos _).le)]
  have hM : ML = MR := by
    refine _root_.Measure.ext_of_integral_mul_boundedContinuousFunction fun g h => ?_
    have hGm : Measurable fun p : (ℕ → ℝ) × ℂ => g p.1 * h p.2 :=
      (g.continuous.measurable.comp measurable_fst).mul
        (h.continuous.measurable.comp measurable_snd)
    have hGb : ∀ p : (ℕ → ℝ) × ℂ, |g p.1 * h p.2| ≤ ‖g‖ * ‖h‖ := fun p => by
      rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul (g.norm_coe_le_norm _) (h.norm_coe_le_norm _) (norm_nonneg _)
        (norm_nonneg _)
    rw [hLint _ hGm _ hGb, hRint _ hGm _ hGb]
    have := palm_core_weightA hZ hm hK hKH hreg hvarbd hvar hcov hν hfin hL1 wB hwc hwK g h
    simpa only [hwB_apply] using this
  have hφb' : ∀ p : (ℕ → ℝ) × ℂ, |Function.uncurry φ p| ≤ Cφ := fun p => hφb _ _
  have h1 := hLint _ hφ _ hφb'
  rw [hM, hRint _ hφ _ hφb'] at h1
  simp only [Function.uncurry_apply_pair] at h1
  have hL : ∀ ω, ∫ z, w z * φ (coords m Z μ ω) z ∂(ν ω) =
      ∫ z in K, w z * φ (coords m Z μ ω) z ∂(ν ω) := fun ω =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by rw [hwK z hz, zero_mul]).symm
  have hR : ∫ z, w z * rhoLimA γ m ctil z * ∫ ω, φ (coords m Z μ ω + shiftLimA γ c μ z) z ∂P =
      ∫ z in K, rhoLimA γ m ctil z *
        ∫ ω, w z * φ (coords m Z μ ω + shiftLimA γ c μ z) z ∂P := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [hwK z hz, zero_mul, zero_mul]]
    refine setIntegral_congr_fun hI fun z _ => ?_
    rw [integral_const_mul]; ring
  simp_rw [hL]
  rw [hR]
  exact h1.symm

lemma coords_add_shiftLimA (c : ℂ → ℂ → ℝ) (ω : Ω) (z : ℂ) :
    coords m Z μ ω + shiftLimA γ c μ z =
      fun j => (ofFun m + Z ω + ofFun (fun u => γ * c z u)) (μ j) := by
  funext j
  simp only [coords, shiftLimA, Pi.add_apply, ofFun, integral_const_mul]

/-- **Weighted area Palm formula (abstract).** -/
theorem palm_formula_area_weight (hZ : IsCenteredGaussianField P Z)
    (hmc : Continuous m) (hK : IsCompact K) (hKH : K ⊆ H)
    {Cv : ℝ} {ctil : ℂ → ℝ} (hctil : Measurable ctil) {c : ℂ → ℂ → ℝ}
    (hc : Measurable (Function.uncurry c)) [∀ j, IsFiniteMeasure (μ j)]
    (hreg : ∀ k, ∀ z ∈ K, ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k z = (ofFun m + Z ω) (fcZ z k))
    (hvarbd : ∀ k, ∀ z ∈ K,
      Var[fun ω => Z ω (fcZ z k); P] + Real.log (radius k) ≤ Cv)
    (hvar : ∀ z ∈ K, Tendsto
      (fun k => Var[fun ω => Z ω (fcZ z k); P] + Real.log (radius k)) atTop (𝓝 (ctil z)))
    (hcov : ∀ z ∈ K, ∀ j, Tendsto
      (fun k => cov[fun ω => Z ω (μ j), fun ω => Z ω (fcZ z k); P]) atTop
      (𝓝 (∫ w, c z w ∂(μ j))))
    (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω K ∂P < ∞)
    (hL1 : AreaL1ConvCc γ m Z P ν K)
    {w : ℂ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ z, 0 ≤ w z)
    (hwK : ∀ z ∉ K, w z = 0)
    {φ : (ℕ → ℝ) → ℂ → ℝ} (hφ : Measurable (Function.uncurry φ)) {Cφ : ℝ}
    (hφb : ∀ y z, |φ y z| ≤ Cφ) :
    ∫ ω, ∫ z, w z * φ (fun j => (ofFun m + Z ω) (μ j)) z ∂(ν ω) ∂P =
      ∫ z, w z * Real.exp (γ * m z + γ ^ 2 * ctil z / 2) *
        ∫ ω, φ (fun j => (ofFun m + Z ω + ofFun (fun u => γ * c z u)) (μ j)) z ∂P := by
  have H := palm_formula_area_weight_coords (γ := γ) hZ hmc.continuousOn hmc hK hKH hctil hc
    hreg hvarbd hvar hcov hν hfin hL1 hw hwc hw0 hwK hφ hφb
  simp only [coords_add_shiftLimA] at H
  exact H

end Weighted

/-! ## 4. The free field: covariances and the kernel -/

section FreeCov

variable {X : Ω → FieldSample}

open BdryExist PalmFree

/-- `hreg` for the free field at any point of `Hbar`. -/
theorem ae_avgReg_zG_C [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (R : ℝ)
    (hm : ContinuousOn m Hbar) (k : ℕ) {z : ℂ} (hz : z ∈ Hbar) :
    ∀ᵐ ω ∂P, avgReg (ofFun m + zG X R ω) k z = (ofFun m + zG X R ω) (fcZ z k) := by
  filter_upwards [ae_isRegularSample_zField hX R, avgReg_zField_ae_eq hX R k hz] with ω hreg h2
  obtain ⟨F, hF⟩ := hreg
  have e1 := (GoodSample.gs_add_ofFun hF hm).avgReg_eq k hz
  have e2 := hF.avgReg_eq k hz
  rw [avgReg_congr_Hbar k (fun w hw => zG_add_fc R m ω w hw _ (radius_pos k)) hz, e1]
  simp only [Pi.add_apply]
  rw [← e2, h2, zG_fc hz (radius_pos k), ← GaussTK.addConst_fc_eq_fcPairVal]
  simp only [ofFun, fcZ, zField]
  ring

lemma variance_zG_fc_eq (hX : IsFreeGFFModConstH X P) {R : ℝ} {z : ℂ} (hz : z ∈ Hbar) {r : ℝ}
    (hr : 0 < r) (hzr : ‖z‖ + r ≤ R) :
    Var[fun ω => zG X R ω (foldedCircle z r); P] =
      kernelCov neumannH (foldedCircle z r) (foldedCircle z r) + 2 * Real.log R := by
  rw [← covariance_self (measurable_zG hX R _).aemeasurable]
  simp_rw [zG_fc hz hr]
  rw [show (fun ω => zField X R ω (foldedCircle z r)) = fun ω =>
    addConst (X ω) (-X ω (foldedCircle 0 R)) (foldedCircle z r) from rfl]
  exact GaussTK.covariance_Z_fc hX hz hz hr hr hzr hzr

/-- Variance at an interior point, small radius. -/
lemma variance_zG_fc_int (hX : IsFreeGFFModConstH X P) {R : ℝ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hrz : r ≤ z.im) (hzr : ‖z‖ + r ≤ R) :
    Var[fun ω => zG X R ω (foldedCircle z r); P] + Real.log r =
      2 * Real.log R - Real.log ‖z - (starRingEnd ℂ) z‖ := by
  rw [variance_zG_fc_eq hX (AreaExist.mem_Hbar_of_le_im hr hrz) hr hzr,
    kernelCov_fc_interior_sameCenter hr hr hrz hrz, max_self]
  ring

/-- A uniform upper bound for all radii. -/
lemma variance_zG_fc_le (hX : IsFreeGFFModConstH X P) {R : ℝ} {z : ℂ} (hz : z ∈ Hbar) {r : ℝ}
    (hr : 0 < r) (hzr : ‖z‖ + r ≤ R) :
    Var[fun ω => zG X R ω (foldedCircle z r); P] + Real.log r ≤ 2 * Real.log R - Real.log r := by
  rw [variance_zG_fc_eq hX hz hr hzr, kernelCov_fc_right' _ _ hr]
  have hle : ∫ y, KernelId.fcPot r z y ∂foldedCircle z r ≤ -2 * Real.log r := by
    have h1 : ∀ y, KernelId.fcPot r z y ≤ -2 * Real.log r := fun y => by
      unfold KernelId.fcPot
      have a1 := Real.log_le_log hr (le_max_left r ‖z - y‖)
      have a2 := Real.log_le_log hr (le_max_left r ‖z - (starRingEnd ℂ) y‖)
      linarith
    calc ∫ y, KernelId.fcPot r z y ∂foldedCircle z r ≤ ∫ _, -2 * Real.log r ∂foldedCircle z r :=
          integral_mono (RegClosure.integrable_fc (KernelId.continuous_fcPot hr z).continuousOn
            z hr.le) (integrable_const _) h1
      _ = -2 * Real.log r := by simp
  linarith

/-- The covariance kernel of the normalized free field at a point `z` of `Hbar` (inside
`B(0,R)`). -/
def freeKernelC (R : ℝ) (z w : ℂ) : ℝ := neumannH z w - KernelId.fcPot R 0 w

lemma measurable_freeKernelC {R : ℝ} (hR : 0 < R) :
    Measurable (Function.uncurry (freeKernelC R)) :=
  measurable_neumannH.sub ((KernelId.continuous_fcPot hR 0).measurable.comp measurable_snd)

lemma integrable_log_norm_sub' {ν : Measure ℂ} (hν : IsAdmissibleH ν) (z : ℂ) :
    Integrable (fun y => Real.log ‖z - y‖) ν :=
  (integrable_log_norm_sub hν z).congr (ae_of_all _ fun y => by simp only [norm_sub_rev])

lemma integrable_log_norm_sub_conj {ν : Measure ℂ} (hν : IsAdmissibleH ν) (z : ℂ) :
    Integrable (fun y => Real.log ‖z - (starRingEnd ℂ) y‖) ν :=
  (integrable_log_norm_sub hν ((starRingEnd ℂ) z)).congr (ae_of_all _ fun y => by
    simp only; rw [KernelId.norm_sub_conj_swap])

lemma integrable_neumannH_left {ν : Measure ℂ} (hν : IsAdmissibleH ν) (z : ℂ) :
    Integrable (fun y => neumannH z y) ν :=
  (integrable_log_norm_sub' hν z).neg.sub (integrable_log_norm_sub_conj hν z)

lemma tendsto_integral_fcPot_C {ν : Measure ℂ} (hν : IsAdmissibleH ν) (z : ℂ) :
    Tendsto (fun k => ∫ y, KernelId.fcPot (radius k) z y ∂ν) atTop
      (𝓝 (∫ y, neumannH z y ∂ν)) := by
  have hint := (integrable_log_norm_sub' hν z).abs.add (integrable_log_norm_sub_conj hν z).abs
  have hna : ∀ᵐ y ∂ν, y ≠ z ∧ y ≠ (starRingEnd ℂ) z := by
    have h1 : ∀ᵐ y ∂ν, y ≠ z := by rw [ae_iff]; simpa using noAtoms_of_isAdmissibleH hν z
    have h2 : ∀ᵐ y ∂ν, y ≠ (starRingEnd ℂ) z := by
      rw [ae_iff]; simpa using noAtoms_of_isAdmissibleH hν ((starRingEnd ℂ) z)
    filter_upwards [h1, h2] with y a b using ⟨a, b⟩
  have hpos : ∀ y, y ≠ z ∧ y ≠ (starRingEnd ℂ) z →
      0 < ‖z - y‖ ∧ 0 < ‖z - (starRingEnd ℂ) y‖ := fun y hy => by
    refine ⟨norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hy.1)), norm_pos_iff.2 (sub_ne_zero.2 ?_)⟩
    intro h; apply hy.2; rw [h, Complex.conj_conj]
  refine tendsto_integral_of_dominated_convergence
    (fun y => |Real.log ‖z - y‖| + |Real.log ‖z - (starRingEnd ℂ) y‖|)
    (fun k => (KernelId.continuous_fcPot (radius_pos k) _).aestronglyMeasurable) hint
    (fun k => ?_) ?_
  · filter_upwards [hna] with y hy
    obtain ⟨d1, d2⟩ := hpos y hy
    unfold KernelId.fcPot
    rw [Real.norm_eq_abs]
    calc |-Real.log (max (radius k) ‖z - y‖) - Real.log (max (radius k) ‖z - (starRingEnd ℂ) y‖)|
        ≤ |Real.log (max (radius k) ‖z - y‖)| +
            |Real.log (max (radius k) ‖z - (starRingEnd ℂ) y‖)| := by
          rw [sub_eq_add_neg, ← neg_add]; rw [abs_neg]; exact abs_add_le _ _
      _ ≤ _ := add_le_add (abs_log_max_le (radius_pos k) (radius_le_one k) d1)
          (abs_log_max_le (radius_pos k) (radius_le_one k) d2)
  · filter_upwards [hna] with y hy
    obtain ⟨d1, d2⟩ := hpos y hy
    have hr : Tendsto radius atTop (𝓝 0) := RegClosure.tendsto_radius_nhdsGT.mono_right
      nhdsWithin_le_nhds
    have hev : ∀ᶠ k in atTop, KernelId.fcPot (radius k) z y = neumannH z y := by
      filter_upwards [hr.eventually (gt_mem_nhds d1), hr.eventually (gt_mem_nhds d2)] with k h1 h2
      unfold KernelId.fcPot neumannH
      rw [max_eq_right h1.le, max_eq_right h2.le]
    exact tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm)

lemma covariance_zG_fcC (hX : IsFreeGFFModConstH X P) {R : ℝ} {ν : Measure ℂ}
    (hν : IsAdmissibleH ν) {z : ℂ} (hz : z ∈ Hbar) {r : ℝ} (hr : 0 < r) (hzr : ‖z‖ + r ≤ R) :
    cov[fun ω => zG X R ω ν, fun ω => zG X R ω (foldedCircle z r); P] =
      ∫ y, KernelId.fcPot r z y ∂ν - ∫ y, KernelId.fcPot R 0 y ∂ν := by
  have hR : 0 < R := by linarith [norm_nonneg z]
  have hfc := isAdmissibleH_foldedCircle hz hr
  rw [covariance_zG hX hR hν hfc]
  have hm1 : massN (foldedCircle z r) = 1 := by simp [massN]
  simp only [kernelCov2, hm1, one_smul, kernelCov_smul_left]
  rw [kernelCov_fc_bigCircle_left hr hzr, kernelCov_fc_bigCircle_left hR (by simp),
    kernelCov_fc_right' _ _ hr, kernelCov_fc_right' _ _ hR]
  ring

/-- **`hcov` for the free field, interior points.** -/
theorem tendsto_covariance_zG_C (hX : IsFreeGFFModConstH X P) {R : ℝ} {ν : Measure ℂ}
    (hν : IsAdmissibleH ν) {z : ℂ} (hz : z ∈ Hbar) (hzR : ‖z‖ + 1 ≤ R) :
    Tendsto (fun k => cov[fun ω => zG X R ω ν, fun ω => zG X R ω (fcZ z k); P]) atTop
      (𝓝 (∫ w, freeKernelC R z w ∂ν)) := by
  have hR : 0 < R := by linarith [norm_nonneg z]
  have e : ∀ k, cov[fun ω => zG X R ω ν, fun ω => zG X R ω (fcZ z k); P] =
      ∫ y, KernelId.fcPot (radius k) z y ∂ν - ∫ y, KernelId.fcPot R 0 y ∂ν := fun k =>
    covariance_zG_fcC hX hν hz (radius_pos k) (by linarith [radius_le_one k])
  simp_rw [e]
  have hlim : ∫ w, freeKernelC R z w ∂ν =
      ∫ y, neumannH z y ∂ν - ∫ y, KernelId.fcPot R 0 y ∂ν :=
    integral_sub (integrable_neumannH_left hν z)
      (integrable_continuous_adm hν (KernelId.continuous_fcPot hR 0))
  rw [hlim]
  exact (tendsto_integral_fcPot_C hν z).sub_const _

/-! ### Part 3: the log-singular decomposition at interior points -/

/-- `γ c(z,w) = γ(−log ‖w − z‖) + (−γ log ‖w − z̄‖ − γ fcPot R 0 w)`. -/
theorem mul_freeKernelC_eq (γ R : ℝ) (z w : ℂ) :
    γ * freeKernelC R z w = γ * (-Real.log ‖w - z‖) +
      (γ * (-Real.log ‖w - (starRingEnd ℂ) z‖) - γ * KernelId.fcPot R 0 w) := by
  unfold freeKernelC neumannH
  rw [norm_sub_rev z w, KernelId.norm_sub_conj_swap z w]
  ring

/-- The remainder is continuous on `Hbar` (indeed off `z̄`) for `z ∈ ℍ`. -/
theorem continuousOn_freeKernelC_rem (γ : ℝ) {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : 0 < z.im) :
    ContinuousOn (fun w => γ * (-Real.log ‖w - (starRingEnd ℂ) z‖) - γ * KernelId.fcPot R 0 w)
      Hbar := by
  refine ContinuousOn.sub (continuousOn_const.mul (ContinuousOn.neg ?_))
    (continuous_const.mul (KernelId.continuous_fcPot hR 0)).continuousOn
  refine ContinuousOn.log (continuous_id.sub continuous_const).norm.continuousOn fun w hw => ?_
  rw [norm_ne_zero_iff, sub_ne_zero]
  intro h
  have : w.im = -z.im := by rw [h, Complex.conj_im]
  have hw' : (0 : ℝ) ≤ w.im := hw
  linarith

end FreeCov

/-! ## 5. Discharging the remaining hypotheses for the free field -/

section FreeHypA

variable {X : Ω → FieldSample}

open BdryExist PalmFree GoodSample VagueH

lemma areaApprox_congr_Hbar {y y' : FieldSample}
    (h : ∀ w ∈ Hbar, ∀ r > 0, y (foldedCircle w r) = y' (foldedCircle w r)) :
    areaApprox γ y = areaApprox γ y' := by
  funext k
  unfold areaApprox
  refine withDensity_congr_ae ((ae_restrict_mem isOpen_H.measurableSet).mono fun z hz => ?_)
  simp only
  rw [avgReg_congr_Hbar k (fun w hw => h w hw _ (radius_pos k)) (H_subset_Hbar hz)]

lemma qAreaMeasure_congr_Hbar {y y' : FieldSample}
    (h : ∀ w ∈ Hbar, ∀ r > 0, y (foldedCircle w r) = y' (foldedCircle w r)) :
    qAreaMeasure γ y = qAreaMeasure γ y' := by
  unfold qAreaMeasure
  rw [areaApprox_congr_Hbar h]

lemma areaR_radius' {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (k : ℕ) :
    areaR γ x (radius k) = areaApprox γ x k := by
  have := areaR_radius γ hF k; rwa [one_mul] at this

lemma areaApprox_lt_top {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (k : ℕ)
    {K : Set ℂ} (hK : IsCompact K) : areaApprox γ x k K < ⊤ := by
  rw [← areaR_radius' hF k]; exact areaR_lt_top γ hF (radius_pos k) hK

/-- The weights `e^{γ m}` and `e^{γ m_k}`. -/
def eA (γ : ℝ) (m : ℂ → ℝ) (z : ℂ) : ℝ := Real.exp (γ * m z)

def eAk (γ : ℝ) (m : ℂ → ℝ) (k : ℕ) (z : ℂ) : ℝ := Real.exp (γ * smoothFun m z (radius k))

lemma continuous_eA (γ : ℝ) (hm : Continuous m) : Continuous (eA γ m) :=
  Real.continuous_exp.comp (continuous_const.mul hm)

lemma continuous_eAk (γ : ℝ) (hm : Continuous m) (k : ℕ) : Continuous (eAk γ m k) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_smoothFun hm.continuousOn _))

lemma integral_areaApprox_add_ofFun {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (hm : Continuous m) (k : ℕ) (f : ℂ → ℝ) :
    ∫ z, f z ∂areaApprox γ (x + ofFun m) k = ∫ z, eAk γ m k z * f z ∂areaApprox γ x k := by
  have := integral_areaR_add_ofFun γ hF hm.continuousOn (radius_pos k) f
  rw [areaR_radius' hF k, areaR_radius' (gs_add_ofFun hF hm.continuousOn) k] at this
  exact this

lemma eventually_smooth_closeC (hm : Continuous m) (c : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ z ∈ K, |c * smoothFun m z (radius k) - c * m z| < δ := by
  have hc := smooth_unif hm.continuousOn hK hKH (δ / (|c| + 1)) (by positivity)
  filter_upwards [RegClosure.tendsto_radius_nhdsGT.eventually hc] with k hk z hz
  have h2 := hk z hz
  rw [← mul_sub, abs_mul]
  calc |c| * |smoothFun m z (radius k) - m z| ≤ |c| * (δ / (|c| + 1)) :=
        mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

/-- Rule (5.1) for the area, along `2^{-k}`, for a regular sample. -/
lemma isVagueLimitOn_add_ofFun {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (hm : Continuous m) {μ : Measure ℂ} (hv : IsVagueLimitOn H (areaApprox γ x) μ) :
    IsVagueLimitOn H (areaApprox γ (x + ofFun m))
      (μ.withDensity fun z => ENNReal.ofReal (eA γ m z)) := by
  have hdc := continuous_eA γ hm
  refine ⟨withDensity_absolutelyContinuous _ _ hv.1,
    fun K hK hKH => withDensity_lt_top hK (hv.2.1 K hK hKH) hdc.continuousOn,
    fun f hf hfc hfH => ?_⟩
  rw [integral_withDensity_ofReal hdc.measurable fun _ => (Real.exp_pos _).le]
  have key := tendsto_integral_exp_mul (X := ℂ) (L := atTop) (U := H) isOpen_H
    (νs := fun k => areaApprox γ x k) (ν := μ)
    (Eventually.of_forall fun k K hK _ => areaApprox_lt_top hF k hK)
    hv.2.2 (v := fun k z => γ * smoothFun m z (radius k)) (v0 := fun z => γ * m z)
    (continuous_const.mul hm).continuousOn
    (Eventually.of_forall fun k =>
      (continuous_const.mul (continuous_smoothFun hm.continuousOn _)).continuousOn)
    (fun K hK hKH ε hε => eventually_smooth_closeC hm γ hK (hKH.trans H_subset_Hbar) ε hε)
    hf hfc hfH
  exact key.congr fun k => (integral_areaApprox_add_ofFun hF hm k f).symm

lemma ae_qAreaMeasure_add_ofFun [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) (hm : Continuous m) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (zField X R ω + ofFun m) =
      (qAreaMeasure γ (zField X R ω)).withDensity fun z => ENNReal.ofReal (eA γ m z) := by
  filter_upwards [ae_isRegularSample_zField hX R,
    AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω hreg hv
  obtain ⟨F, hF⟩ := hreg
  exact qAreaMeasure_eq (isVagueLimitOn_add_ofFun hF hm hv)

/-- `L¹` convergence to the limit, with integrability, for the normalized field. -/
lemma areaL1_full [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ)
    (hγ2 : γ < 2) {R : ℝ} {f : ℂ → ℝ} (hf : IsTestH f) (hfR : ∀ z ∈ tsupport f, ‖z‖ + 1 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      Integrable (fun ω => ∫ z, f z ∂areaApprox γ (zField X R ω) k) P ∧
      Integrable (fun ω => ∫ z, f z ∂areaApprox γ (zField X R ω) k -
        ∫ z, f z ∂qAreaMeasure γ (zField X R ω)) P ∧
      ∫ ω, |∫ z, f z ∂areaApprox γ (zField X R ω) k -
        ∫ z, f z ∂qAreaMeasure γ (zField X R ω)| ∂P ≤
          C * Real.exp (-AreaExist.areaRate γ * (k * Real.log 2)) := by
  obtain ⟨C, hC0, k₀, hint, hC⟩ := AreaExist.areaApprox_L1_rate hX hγ hγ2 hf.1 hf.2.1 hf.2.2 hfR
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, f z ∂areaApprox γ (zField X R ω) k) atTop
      (𝓝 (∫ z, f z ∂qAreaMeasure γ (zField X R ω))) := by
    filter_upwards [AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω hω
    exact hω.2.2 f hf.1 hf.2.1 hf.2.2
  exact ⟨C, hC0, k₀, fun k hk => ⟨hint k hk, AreaExist.integral_abs_sub_lim_le hint hlim hC hk⟩⟩

lemma tendsto_rate_zero (hγ : 0 < γ) (hγ2 : γ < 2) (C : ℝ) :
    Tendsto (fun k : ℕ => C * Real.exp (-AreaExist.areaRate γ * (k * Real.log 2))) atTop
      (𝓝 0) := by
  have hq1 : Real.exp (-AreaExist.areaRate γ * Real.log 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := AreaExist.areaRate_pos hγ hγ2
    have := Real.log_pos one_lt_two
    nlinarith
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hq1).const_mul C
  rw [mul_zero] at this
  refine this.congr fun k => ?_
  rw [← Real.exp_nat_mul]; congr 2; ring

/-- First moments of a test function converge, and the limit is integrable. -/
lemma integrable_and_tendsto_areaTest [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} {f : ℂ → ℝ} (hf : IsTestH f)
    (hfR : ∀ z ∈ tsupport f, ‖z‖ + 1 ≤ R) :
    Integrable (fun ω => ∫ z, f z ∂qAreaMeasure γ (zField X R ω)) P ∧
      ∃ k₀ : ℕ, (∀ k, k₀ ≤ k → Integrable (fun ω => ∫ z, f z ∂areaApprox γ (zField X R ω) k) P) ∧
      Tendsto (fun k => ∫ ω, ∫ z, f z ∂areaApprox γ (zField X R ω) k ∂P) atTop
        (𝓝 (∫ ω, ∫ z, f z ∂qAreaMeasure γ (zField X R ω) ∂P)) := by
  obtain ⟨C, -, k₀, hk⟩ := areaL1_full hX hγ hγ2 hf hfR
  have hL : Integrable (fun ω => ∫ z, f z ∂qAreaMeasure γ (zField X R ω)) P :=
    ((hk k₀ le_rfl).1.sub (hk k₀ le_rfl).2.1).congr (ae_of_all _ fun ω => by simp)
  refine ⟨hL, k₀, fun k h => (hk k h).1, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_
    (tendsto_rate_zero hγ hγ2 C)
  filter_upwards [eventually_ge_atTop k₀] with k hk'
  rw [← integral_sub (hk k hk').1 hL]
  exact (norm_integral_le_integral_norm _).trans (by simpa [Real.norm_eq_abs] using (hk k hk').2.2)

lemma exists_testBump {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {R : ℝ}
    (hKR : ∀ z ∈ K, ‖z‖ + 2 ≤ R) :
    ∃ g : ℂ → ℝ, IsTestH g ∧ (∀ z ∈ tsupport g, ‖z‖ + 1 ≤ R) ∧ EqOn g 1 K ∧ ∀ z, 0 ≤ g z := by
  obtain ⟨g, hgc, hgcs, hgU, hg1, hg0⟩ := exists_bump hK
    (isOpen_H.inter (isOpen_lt continuous_norm continuous_const))
    (fun z hz => ⟨hKH hz, show ‖z‖ < R - 1 by linarith [hKR z hz]⟩)
  refine ⟨g, ⟨hgc, hgcs, hgU.trans inter_subset_left⟩, fun z hz => ?_, hg1, hg0⟩
  have : ‖z‖ < R - 1 := (hgU hz).2
  linarith

lemma qAreaMeasure_zG (R : ℝ) (m : ℂ → ℝ) (ω : Ω) :
    qAreaMeasure γ (ofFun m + zG X R ω) = qAreaMeasure γ (zField X R ω + ofFun m) :=
  qAreaMeasure_congr_Hbar (zG_add_fc R m ω)

/-- **`hfin` for the free field (area).** -/
theorem lintegral_qAreaMeasure_zG_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (hKR : ∀ z ∈ K, ‖z‖ + 2 ≤ R) (hm : Continuous m) :
    ∫⁻ ω, qAreaMeasure γ (ofFun m + zG X R ω) K ∂P < ∞ := by
  obtain ⟨g, hg, hgR, hg1, hg0⟩ := exists_testBump hK hKH hKR
  obtain ⟨hGi, -⟩ := integrable_and_tendsto_areaTest hX hγ hγ2 hg hgR
  obtain ⟨E, hE⟩ := hK.exists_bound_of_continuousOn (continuous_eA γ hm).continuousOn
  have hbd : ∀ᵐ ω ∂P, qAreaMeasure γ (ofFun m + zG X R ω) K ≤
      ENNReal.ofReal E * ENNReal.ofReal (∫ z, g z ∂qAreaMeasure γ (zField X R ω)) := by
    filter_upwards [ae_qAreaMeasure_add_ofFun hX hγ hγ2 R hm,
      AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω hω hv
    rw [qAreaMeasure_zG, hω, withDensity_apply _ hK.measurableSet]
    calc ∫⁻ z in K, ENNReal.ofReal (eA γ m z) ∂qAreaMeasure γ (zField X R ω)
        ≤ ∫⁻ _ in K, ENNReal.ofReal E ∂qAreaMeasure γ (zField X R ω) :=
          setLIntegral_mono measurable_const fun z hz => ENNReal.ofReal_le_ofReal
            ((le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hE z hz))
      _ = ENNReal.ofReal E * qAreaMeasure γ (zField X R ω) K := setLIntegral_const _ _
      _ ≤ _ := by
          gcongr
          have hgi : Integrable g (qAreaMeasure γ (zField X R ω)) :=
            hg.integrable (hv.2.1 _ hg.2.1 hg.2.2)
          rw [ofReal_integral_eq_lintegral_ofReal hgi
            (ae_of_all _ hg0), ← lintegral_indicator_one hK.measurableSet]
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ K
          · rw [indicator_of_mem hz, Pi.one_apply, hg1 hz, Pi.one_apply, ENNReal.ofReal_one]
          · rw [indicator_of_notMem hz]; exact bot_le
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal E * ENNReal.ofReal
        (∫ z, g z ∂qAreaMeasure γ (zField X R ω)) ∂P := lintegral_mono_ae hbd
    _ = ENNReal.ofReal E * ∫⁻ ω, ENNReal.ofReal
        (∫ z, g z ∂qAreaMeasure γ (zField X R ω)) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGi.lintegral_lt_top

/-- **`L¹` convergence (`C_c` form) for the free field (area).** -/
theorem areaL1ConvCc_zG [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ)
    (hγ2 : γ < 2) {R : ℝ} {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (hKR : ∀ z ∈ K, ‖z‖ + 2 ≤ R) (hm : Continuous m) :
    AreaL1ConvCc γ m (zG X R) P (fun ω => qAreaMeasure γ (ofFun m + zG X R ω)) K := by
  intro f hf hfc hfK
  have htsK : tsupport f ⊆ K :=
    closure_minimal (fun z hz => by_contra fun h => hz (hfK z h)) hK.isClosed
  have hKR1 : ∀ z ∈ K, ‖z‖ + 1 ≤ R := fun z hz => by linarith [hKR z hz]
  obtain ⟨d, hd, hd1, hKd⟩ := AreaExist.exists_im_lower_bound hK hKH
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one hd (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have hrad : ∀ k, k₁ ≤ k → radius k ≤ d := fun k hk =>
    (AreaExist.aradius_anti hk).trans hk₁.le
  have hec := continuous_eA γ hm
  have hekc := continuous_eAk γ hm
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfc
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
  -- the `B` part
  have hef : IsTestH (fun z => eA γ m z * f z) :=
    ⟨hec.mul hf, hfc.mul_left, tsupport_mul_subset_right.trans (htsK.trans hKH)⟩
  have hefR : ∀ z ∈ tsupport (fun z => eA γ m z * f z), ‖z‖ + 1 ≤ R := fun z hz =>
    hKR1 z (htsK (tsupport_mul_subset_right hz))
  obtain ⟨CB, -, kB, hB⟩ := areaL1_full hX hγ hγ2 hef hefR
  have hB0 : Tendsto (fun k => ∫ ω, |∫ z, eA γ m z * f z ∂areaApprox γ (zField X R ω) k -
      ∫ z, eA γ m z * f z ∂qAreaMeasure γ (zField X R ω)| ∂P) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun k => integral_nonneg fun ω => abs_nonneg _)
      ((eventually_ge_atTop kB).mono fun k hk => (hB k hk).2.2) (tendsto_rate_zero hγ hγ2 CB)
  -- the `A` part
  obtain ⟨g, hg, hgR, hg1, hg0⟩ := exists_testBump hK hKH hKR
  obtain ⟨-, kg, hGint, hGt⟩ := integrable_and_tendsto_areaTest hX hγ hγ2 hg hgR
  have hAint : ∀ k, k₁ ≤ k → Integrable (fun ω => ∫ z, (eAk γ m k z - eA γ m z) * f z
      ∂areaApprox γ (zField X R ω) k) P := fun k hk => by
    have hc : Continuous fun z => (eAk γ m k z - eA γ m z) * f z := ((hekc k).sub hec).mul hf
    obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hfc.mul_left
    exact AreaExist.integrable_integral_areaApprox hX hK.measurableSet hK.measure_lt_top hKH hd1
      hKR1 hKd γ hc.measurable (M := M) (fun z => by simpa [Real.norm_eq_abs] using hM z)
      (fun z hz => by rw [hfK z hz, mul_zero]) (hrad k hk)
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn
    (continuous_const.mul hm : Continuous fun z : ℂ => γ * m z).continuousOn
  have hclose : ∀ η > 0, ∀ᶠ k in atTop, ∀ z ∈ K, |eAk γ m k z - eA γ m z| ≤ η := by
    intro η hη
    have hδ : 0 < min 1 (η / Real.exp (M0 + 1)) := lt_min one_pos (by positivity)
    filter_upwards [eventually_smooth_closeC hm γ hK (hKH.trans H_subset_Hbar) _ hδ] with k hk z hz
    have h1 := hk z hz
    have hv : γ * m z ≤ M0 := (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hM0 z hz)
    have hu : γ * smoothFun m z (radius k) ≤ M0 + 1 := by
      have := (abs_lt.1 h1).2
      linarith [min_le_left 1 (η / Real.exp (M0 + 1))]
    unfold eAk eA
    calc |Real.exp (γ * smoothFun m z (radius k)) - Real.exp (γ * m z)|
        ≤ Real.exp (M0 + 1) * |γ * smoothFun m z (radius k) - γ * m z| :=
          RegSample.abs_exp_sub_exp_le hu (by linarith)
      _ ≤ Real.exp (M0 + 1) * (η / Real.exp (M0 + 1)) :=
          mul_le_mul_of_nonneg_left (h1.le.trans (min_le_right _ _)) (Real.exp_pos _).le
      _ = η := by field_simp
  have hA0 : Tendsto (fun k => ∫ ω, |∫ z, (eAk γ m k z - eA γ m z) * f z
      ∂areaApprox γ (zField X R ω) k| ∂P) atTop (𝓝 0) := by
    refine tendsto_zero_of_eventually_le (fun k => integral_nonneg fun ω => abs_nonneg _) hCf0 hGt
      fun η hη => ?_
    filter_upwards [hclose η hη, eventually_ge_atTop (max k₁ kg)] with k hk hk'
    have hpt : ∀ z, ‖(eAk γ m k z - eA γ m z) * f z‖ ≤ η * Cf * g z := by
      intro z
      by_cases hz : z ∈ K
      · rw [hg1 hz, Pi.one_apply, mul_one, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hk z hz) (hCf z) (norm_nonneg _) hη.le
      · rw [hfK z hz, mul_zero, norm_zero]
        exact mul_nonneg (mul_nonneg hη.le hCf0) (hg0 z)
    have hbd : ∀ᵐ ω ∂P, |∫ z, (eAk γ m k z - eA γ m z) * f z ∂areaApprox γ (zField X R ω) k| ≤
        η * Cf * ∫ z, g z ∂areaApprox γ (zField X R ω) k := by
      filter_upwards [ae_isRegularSample_zField hX R] with ω hreg
      obtain ⟨F, hF⟩ := hreg
      rw [← integral_const_mul, ← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le ((hg.integrable (areaApprox_lt_top hF k hg.2.1)).const_mul _)
        (ae_of_all _ hpt)
    calc ∫ ω, |∫ z, (eAk γ m k z - eA γ m z) * f z ∂areaApprox γ (zField X R ω) k| ∂P
        ≤ ∫ ω, η * Cf * ∫ z, g z ∂areaApprox γ (zField X R ω) k ∂P :=
          integral_mono_ae (hAint k (le_of_max_le_left hk')).abs
            ((hGint k (le_of_max_le_right hk')).const_mul _) hbd
      _ = η * Cf * ∫ ω, ∫ z, g z ∂areaApprox γ (zField X R ω) k ∂P := integral_const_mul _ _
  -- pathwise decomposition
  have hdec : ∀ k, ∀ᵐ ω ∂P, ∫ z, f z ∂areaApprox γ (ofFun m + zG X R ω) k -
      ∫ z, f z ∂qAreaMeasure γ (ofFun m + zG X R ω) =
      (∫ z, (eAk γ m k z - eA γ m z) * f z ∂areaApprox γ (zField X R ω) k) +
      (∫ z, eA γ m z * f z ∂areaApprox γ (zField X R ω) k -
        ∫ z, eA γ m z * f z ∂qAreaMeasure γ (zField X R ω)) := by
    intro k
    filter_upwards [ae_isRegularSample_zField hX R, ae_qAreaMeasure_add_ofFun hX hγ hγ2 R hm]
      with ω hreg hq
    obtain ⟨F, hF⟩ := hreg
    rw [areaApprox_congr_Hbar (zG_add_fc R m ω), qAreaMeasure_zG, hq,
      integral_areaApprox_add_ofFun hF hm k f,
      integral_withDensity_ofReal hec.measurable (fun _ => (Real.exp_pos _).le)]
    have hek : IsTestH (fun z => eAk γ m k z * f z) :=
      ⟨(hekc k).mul hf, hfc.mul_left, tsupport_mul_subset_right.trans (htsK.trans hKH)⟩
    have hi1 : Integrable (fun z => eAk γ m k z * f z) (areaApprox γ (zField X R ω) k) :=
      hek.integrable (areaApprox_lt_top hF k hek.2.1)
    have hi2 : Integrable (fun z => eA γ m z * f z) (areaApprox γ (zField X R ω) k) :=
      hef.integrable (areaApprox_lt_top hF k hef.2.1)
    have e3 : ∫ z, (eAk γ m k z - eA γ m z) * f z ∂areaApprox γ (zField X R ω) k =
        ∫ z, eAk γ m k z * f z ∂areaApprox γ (zField X R ω) k -
          ∫ z, eA γ m z * f z ∂areaApprox γ (zField X R ω) k := by
      simp_rw [sub_mul]; exact integral_sub hi1 hi2
    rw [e3]; ring
  refine squeeze_zero' (Eventually.of_forall fun k => integral_nonneg fun ω => abs_nonneg _) ?_
    (by simpa using hA0.add hB0)
  filter_upwards [eventually_ge_atTop (max k₁ kB)] with k hk
  have hA := (hAint k (le_of_max_le_left hk)).abs
  have hBi := (hB k (le_of_max_le_right hk)).2.1.abs
  rw [← integral_add hA hBi]
  refine integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _) (hA.add hBi) ?_
  filter_upwards [hdec k] with ω hω
  rw [hω]; exact abs_add_le _ _

/-- **`hν` for the free field (area).** -/
theorem aemeasurable_qAreaMeasure_free [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) (hm : Continuous m) :
    AEMeasurable (fun ω => qAreaMeasure γ (ofFun m + zField X R ω)) P := by
  have hae : ∀ᵐ ω ∂P, IsVagueLimitOn H (areaApprox γ (zField X R ω + ofFun m))
      (qAreaMeasure γ (zField X R ω + ofFun m)) := by
    filter_upwards [ae_isRegularSample_zField hX R,
      AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω hreg hv
    obtain ⟨F, hF⟩ := hreg
    have hv' := isVagueLimitOn_add_ofFun hF hm hv
    rwa [qAreaMeasure_eq hv']
  have h := LQGMeasAE.aemeasurable_qAreaMeasure_of_ae
    (X := fun ω => zField X R ω + ofFun m)
    (fun μ => ((measurable_pi_apply μ).comp (measurable_zField hX R)).add_const _) hae
  refine h.congr (ae_of_all _ fun ω => ?_)
  show qAreaMeasure γ (zField X R ω + ofFun m) = qAreaMeasure γ (ofFun m + zField X R ω)
  rw [add_comm]

end FreeHypA

/-! ## 6. The free-field area Palm formula -/

/-- **S5-D1 (area) for the free field.** `Y = ofFun m + aZ X R` (`aZ = zField`, the free field
normalized at `fc(0,R)`), `m` continuous, `0 < γ < 2`, `w ≥ 0` continuous with compact support
in `ℍ ∩ {‖z‖ + 2 ≤ R}`, admissible `μ_j`, bounded measurable `φ`:
`E ∫ w(z) φ(Y,z) μ_Y(dz) =
  ∫ w(z) exp(γ m(z) + γ²(2 log R − log ‖z − z̄‖)/2) E φ(Y + ofFun(γ c(z,·)), z) dz`,
with `c = freeKernelC R`. -/
theorem palm_formula_area_free {X : Ω → FieldSample} [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} (hR : 0 < R)
    (hm : Continuous m) (hμ : ∀ j, IsAdmissibleH (μ j))
    {w : ℂ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ z, 0 ≤ w z)
    (hwH : tsupport w ⊆ H) (hwR : ∀ z ∈ tsupport w, ‖z‖ + 2 ≤ R)
    {φ : (ℕ → ℝ) → ℂ → ℝ} (hφ : Measurable (Function.uncurry φ)) {Cφ : ℝ}
    (hφb : ∀ y z, |φ y z| ≤ Cφ) :
    ∫ ω, ∫ z, w z * φ (fun j => (ofFun m + AreaExist.aZ X R ω) (μ j)) z
        ∂(qAreaMeasure γ (ofFun m + AreaExist.aZ X R ω)) ∂P =
      ∫ z, w z * Real.exp (γ * m z + γ ^ 2 * (2 * Real.log R -
          Real.log ‖z - (starRingEnd ℂ) z‖) / 2) *
        ∫ ω, φ (fun j => (ofFun m + AreaExist.aZ X R ω +
          ofFun (fun u => γ * freeKernelC R z u)) (μ j)) z ∂P := by
  have : ∀ j, IsFiniteMeasure (μ j) := fun j => (hμ j).1
  set K := tsupport w with hKdef
  have hK : IsCompact K := hwc
  have hwK : ∀ z ∉ K, w z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hKR1 : ∀ z ∈ K, ‖z‖ + 1 ≤ R := fun z hz => by linarith [hwR z hz]
  obtain ⟨d, hd, -, hKd⟩ := AreaExist.exists_im_lower_bound hK hwH
  have hqa : ∀ ω, qAreaMeasure γ (ofFun m + PalmFree.zG X R ω) =
      qAreaMeasure γ (ofFun m + BdryExist.zField X R ω) := fun ω =>
    qAreaMeasure_congr_Hbar (PalmFree.zG_add_fc' R m ω)
  have hν' : AEMeasurable (fun ω => qAreaMeasure γ (ofFun m + PalmFree.zG X R ω)) P := by
    rw [show (fun ω => qAreaMeasure γ (ofFun m + PalmFree.zG X R ω)) = fun ω =>
      qAreaMeasure γ (ofFun m + BdryExist.zField X R ω) from funext hqa]
    exact aemeasurable_qAreaMeasure_free hX hγ hγ2 R hm
  have hvarbd : ∀ k, ∀ z ∈ K, Var[fun ω => PalmFree.zG X R ω (fcZ z k); P] +
      Real.log (radius k) ≤ 2 * Real.log R - Real.log d := by
    intro k z hz
    have hzr : ‖z‖ + radius k ≤ R := by linarith [hKR1 z hz, BdryExist.radius_le_one k]
    by_cases hrz : radius k ≤ z.im
    · rw [variance_zG_fc_int hX (radius_pos k) hrz hzr]
      have h2 := AreaExist.two_im_le_norm_sub_conj z
      have : Real.log d ≤ Real.log ‖z - (starRingEnd ℂ) z‖ :=
        Real.log_le_log hd (by linarith [hKd z hz])
      linarith
    · have := variance_zG_fc_le hX (H_subset_Hbar (hwH hz)) (radius_pos k) hzr
      have : Real.log d ≤ Real.log (radius k) :=
        Real.log_le_log hd (by linarith [hKd z hz, not_le.1 hrz])
      linarith
  have hvar : ∀ z ∈ K, Tendsto (fun k => Var[fun ω => PalmFree.zG X R ω (fcZ z k); P] +
      Real.log (radius k)) atTop (𝓝 (2 * Real.log R - Real.log ‖z - (starRingEnd ℂ) z‖)) := by
    intro z hz
    have hr : Tendsto radius atTop (𝓝 0) := RegClosure.tendsto_radius_nhdsGT.mono_right
      nhdsWithin_le_nhds
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hr.eventually (gt_mem_nhds (hwH hz : 0 < z.im))] with k hk
    exact (variance_zG_fc_int hX (radius_pos k) hk.le
      (by linarith [hKR1 z hz, BdryExist.radius_le_one k])).symm
  have hctil : Measurable fun z : ℂ => 2 * Real.log R - Real.log ‖z - (starRingEnd ℂ) z‖ :=
    measurable_const.sub (Real.measurable_log.comp
      (continuous_id.sub Complex.continuous_conj).norm.measurable)
  have H := palm_formula_area_weight (Z := PalmFree.zG X R) (μ := μ) (γ := γ)
    (ν := fun ω => qAreaMeasure γ (ofFun m + PalmFree.zG X R ω))
    (PalmFree.isCenteredGaussianField_zG hX hR) hm hK hwH hctil (measurable_freeKernelC hR)
    (fun k z hz => ae_avgReg_zG_C hX R hm.continuousOn k (H_subset_Hbar (hwH hz)))
    hvarbd hvar
    (fun z hz j => tendsto_covariance_zG_C hX (hμ j) (H_subset_Hbar (hwH hz)) (hKR1 z hz))
    hν' (lintegral_qAreaMeasure_zG_lt_top hX hγ hγ2 hK hwH hwR hm)
    (areaL1ConvCc_zG hX hγ hγ2 hK hwH hwR hm) hw hwc hw0 hwK hφ hφb
  have hc1 : ∀ ω, (fun j => (ofFun m + PalmFree.zG X R ω) (μ j)) =
      fun j => (ofFun m + BdryExist.zField X R ω) (μ j) := fun ω => by
    funext j; simp only [Pi.add_apply]; rw [PalmFree.zG_of_adm (hμ j)]
  have hc2 : ∀ ω z, (fun j => (ofFun m + PalmFree.zG X R ω + ofFun (fun u => γ * freeKernelC R z u))
      (μ j)) = fun j => (ofFun m + BdryExist.zField X R ω +
        ofFun (fun u => γ * freeKernelC R z u)) (μ j) := fun ω z => by
    funext j; simp only [Pi.add_apply]; rw [PalmFree.zG_of_adm (hμ j)]
  simp only [hc1, hc2, hqa] at H
  exact H

end PalmArea
end QuantumZipper
