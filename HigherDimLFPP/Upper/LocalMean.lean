import HigherDimLFPP.Upper.LocalMeanEndpoints
import HigherDimLFPP.Upper.ChainSimultaneity

/-!
# Lemma 4.3: the local Gaussian optimization (packet P-U4)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.2, Lemma 4.3 (text lines 692–803), as
completed by the planning audit HA3 (`planning/audits/HA3-section-4.md`), Details D5 (Steps 0,
1a–1d, 2a–2c and the energy expansion; fixes F2, F3, F6, F11, F15, F16) and D6 (iv); ruling H7.

* **T1** (`localPenalizedMean`, HA3's `LocalPenalizedMean` in block (c)): there is `C = C(d)` such
  that for all `n ≥ 3`, `τ, u ∈ (0,1)` and `η > 0` there is `δ₀ > 0` with: for `0 < δ < δ₀`,
  every `L > 0`, centers `c_A, c_B` with `L/4 ≤ |c_B - c_A| ≤ 4L`, and every finite family `F` of
  configurations `([x, y], Q)` with `|x - c_A|, |y - c_B| ≤ √d δ L` and `Q ∈ G_K(x, y)`
  (`K = 2ⁿ`, threshold `a₀ = 1/(500 K)`),
  `E max_F (Y - (1-τ) E_δ) ≤ (1+u)^{2/3} (1-τ)^{-1/3} A_{n,d} + C u^{-1/2} + η`,
  where `Y` is the centered Gaussian family with the all-scale covariance
  `δ⁻¹ Λ(ν_{[x,y]} - ν_Q, ν_{[x',y']} - ν_{Q'})` (`logCov`) and `E_δ = δ⁻² log(len Q/|y - x|)`.
  Proof: normalization by a similarity (Step 2a; `scaleCov_map_simAffine_Ioi`,
  `goodFamily_map_simAffine`), then `step2`.
* **T2** (`localPenalizedMean_band`, Step 0): the same bound, with the same `C` and `δ₀`, for the
  covariance `δ⁻¹ Cov(⟨H_S, ·⟩)` of the band field of every admissible kernel and every measurable
  scale set `S ⊆ (0, ∞)` — in particular every band `(a, b)`, `0 ≤ a < b ≤ ∞`, and the cutoff
  field `H_{ε,1}`.  Sudakov–Fernique (`gEM_le_of_dist`) with the cutoff domination (3.3)
  (`scaleCov_self_le_of_subset`): the increments are mass-zero combinations.
* **T3** (`goodRecordMeanBound_holds`, HA3 D6 (iv)): P-U3's `GoodRecordMeanBound d κ` for every
  admissible `κ` and `d ≥ 2`: for good records in bin `k` and finite `F ⊆ Φ(ρ)`,
  `E max_F Y ≤ b*_n + (1-τ)(k+1)`.  The record variables are the white-noise Gaussian family of
  `HigherDimLFPP.Upper.integral_iSup_cfgVal`, `Φ(ρ)` lies in the family of T2 with `L = 2^{-j}` and
  the cube corners as centers, and `Y ≤ (Y - (1-τ)E_δ) + (1-τ)(k+1)` on bin `k`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

variable {d : ℕ}

attribute [local instance] isFiniteMeasure_polyMeasure

/-! ## Helpers -/

section Helpers

/-- **Sudakov–Fernique with drift**, covariance form: if the canonical distances of `C` are
dominated by those of `C'` on `F`, then `E max_F (X + b) ≤ E max_F (X' + b)`. -/
theorem gEM_le_of_dist {ι : Type} (F : Finset ι) {C C' : ι → ι → ℝ} (hC : PSDOn F C)
    (hC' : PSDOn F C') (b : ι → ℝ)
    (h : ∀ i ∈ F, ∀ j ∈ F, C i i + C j j - 2 * C i j ≤ C' i i + C' j j - 2 * C' i j) :
    gaussianExpectedMax F C b ≤ gaussianExpectedMax F C' b := by
  obtain ⟨v, hv, hvE⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F C hC
  obtain ⟨v', hv', hv'E⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F C' hC'
  rw [hvE, hv'E]
  refine LQGDimension.sudakovFernique ι (EuclideanSpace ℝ F) (EuclideanSpace ℝ F) F v v' b
    fun i hi j hj => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_eq_of_gram hv hi hj,
    norm_sub_sq_eq_of_gram hv' hi hj]
  exact h i hi j hj

/-- Good polygons of a chord `[x, y]` (threshold `≤ 1/2`) are carried by the ball of radius
`|x| + 2|y - x|`. -/
theorem goodFamily_ae_norm_le {K : ℕ} {a : ℝ} (ha : a ≤ 1 / 2) {x y : Rd d} {Q : List (Rd d)}
    (hQ : Q ∈ goodFamily K a x y) : ∀ᵐ z ∂(polyMeasure Q), ‖z‖ ≤ ‖x‖ + 2 * ‖y - x‖ := by
  obtain ⟨V, hQV, hV0, -, -, -, hpoly⟩ := goodFamily_vertex hQ
  have hexp : Real.exp a ≤ 2 := by
    rcases le_total a 0 with h0 | h0
    · exact (Real.exp_le_one_iff.2 h0).trans (by norm_num)
    · have := exp_le_one_add_add_sq h0 (by linarith)
      nlinarith
  have hS : plen V K ≤ 2 * ‖y - x‖ :=
    hpoly.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  rw [hQV, polyMeasure_range_map]
  refine ae_norm_le_segSum fun i hi => ?_
  have h1 := norm_sub_le_plen V i
  rw [hV0] at h1
  have h2 := plen_mono V hi
  calc ‖V i‖ = ‖x + (V i - x)‖ := by rw [add_sub_cancel]
    _ ≤ ‖x‖ + ‖V i - x‖ := norm_add_le _ _
    _ ≤ ‖x‖ + 2 * ‖y - x‖ := by linarith

theorem segMeasure_ae_norm_le (x y : Rd d) :
    ∀ᵐ z ∂(segMeasure x y), ‖z‖ ≤ ‖x‖ + 2 * ‖y - x‖ := by
  rw [segMeasure_eq, ae_map_iff (measurable_lin _ _).aemeasurable
    (measurableSet_le continuous_norm.measurable measurable_const)]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  calc ‖lin x y s‖ ≤ ‖x‖ + ‖s • (y - x)‖ := norm_add_le _ _
    _ = ‖x‖ + s * ‖y - x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    _ ≤ ‖x‖ + 2 * ‖y - x‖ := by nlinarith [hs.2, norm_nonneg (y - x)]

/-- The configurations of Lemma 4.3: a chord `[x, y]` and a good polygon `Q ∈ G_K(x, y)`. -/
def GoodPair (n : ℕ) (c : Config d) : Prop :=
  ∃ x y : Rd d, c.1 = [x, y] ∧ x ≠ y ∧ c.2 ∈ goodFamily (2 ^ n) (a0 n) x y

/-- On good configurations the all-scale covariance of an admissible kernel is the log covariance
(3.2), and both pairs are pairable. -/
theorem scaleCov_eq_logCov_cfg {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {n : ℕ} {c c' : Config d}
    (hc : GoodPair n c) (hc' : GoodPair n c') :
    IsPairable κ (Ioi 0) (polyMeasure c.1) (polyMeasure c.2) ∧
      IsPairable κ (Ioi 0) (polyMeasure c'.1) (polyMeasure c'.2) ∧
      scaleCov κ (Ioi 0) (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1)
        (polyMeasure c'.2) =
      logCov (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1) (polyMeasure c'.2) := by
  obtain ⟨x, y, h1, hxy, hQ⟩ := hc
  obtain ⟨x', y', h1', hxy', hQ'⟩ := hc'
  have ha : a0 n ≤ 1 / 2 := a0_le_half n
  rw [h1, h1', polyMeasure_pair hxy, polyMeasure_pair hxy']
  have := goodFamily_isProbabilityMeasure hQ hxy
  have := goodFamily_isProbabilityMeasure hQ' hxy'
  have hr : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  have hr' : 0 < ‖y' - x'‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy'))
  set D := max (‖x‖ + 2 * ‖y - x‖) (‖x'‖ + 2 * ‖y' - x'‖) with hD
  have s1 : ∀ᵐ z ∂(segMeasure x y), ‖z‖ ≤ D :=
    (segMeasure_ae_norm_le x y).mono fun z hz => hz.trans (le_max_left _ _)
  have s2 : ∀ᵐ z ∂(polyMeasure c.2), ‖z‖ ≤ D :=
    (goodFamily_ae_norm_le ha hQ).mono fun z hz => hz.trans (le_max_left _ _)
  have s3 : ∀ᵐ z ∂(segMeasure x' y'), ‖z‖ ≤ D :=
    (segMeasure_ae_norm_le x' y').mono fun z hz => hz.trans (le_max_right _ _)
  have s4 : ∀ᵐ z ∂(polyMeasure c'.2), ‖z‖ ≤ D :=
    (goodFamily_ae_norm_le ha hQ').mono fun z hz => hz.trans (le_max_right _ _)
  exact scaleCov_eq_logCov_of_growthBound hκ hr hr'
    (HigherDimLFPP.GrowthBound.mono_const (μ := segMeasure x y) (segMeasure_growthBound hxy) hr
      (by norm_num))
    (goodFamily_growthBound hQ hxy)
    (HigherDimLFPP.GrowthBound.mono_const (μ := segMeasure x' y') (segMeasure_growthBound hxy')
      hr' (by norm_num))
    (goodFamily_growthBound hQ' hxy') s1 s2 s3 s4

end Helpers

/-! ## T1: Lemma 4.3 in the all-scale form -/

section T1

/-- **Lemma 4.3, all-scale form** (HA3 block (c), `LocalPenalizedMean`, with the frozen `A`): there
is `C` such that for all `n ≥ 3`, `τ, u ∈ (0,1)` and `η > 0` there is `δ₀ > 0` with the following
property.  For `0 < δ < δ₀`, `L > 0`, centers `c_A, c_B` with `L/4 ≤ |c_B - c_A| ≤ 4L`, and every
finite family `F` of configurations `([x, y], Q)` with `|x - c_A|, |y - c_B| ≤ √d δ L` and
`Q ∈ G_K(x, y)` (`K = 2ⁿ`, threshold `a0 n = 1/(500 · 2ⁿ)`), the penalized expected maximum of the
centered Gaussian family with covariance `δ⁻¹ Λ(ν_{[x,y]} - ν_Q, ν_{[x',y']} - ν_{Q'})` and drift
`-(1-τ) δ⁻² log(len Q/|y - x|)` is at most
`(1+u)^{2/3} (1-τ)^{-1/3} A_{n,d} + C u^{-1/2} + η`. -/
def LocalPenalizedMean (d : ℕ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → ∀ τ ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, ∀ η > 0,
    ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ L > 0, ∀ cA cB : Rd d,
      L / 4 ≤ ‖cB - cA‖ → ‖cB - cA‖ ≤ 4 * L →
      ∀ F : Finset (Config d),
        (∀ c ∈ F, ∃ x y : Rd d, c.1 = [x, y] ∧ ‖x - cA‖ ≤ Real.sqrt d * δ * L ∧
          ‖y - cB‖ ≤ Real.sqrt d * δ * L ∧ c.2 ∈ goodFamily (2 ^ n) (a0 n) x y) →
        gaussianExpectedMax F
            (fun c c' => δ⁻¹ * logCov (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1)
              (polyMeasure c'.2))
            (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) ≤
          (1 + u) ^ (2 / 3 : ℝ) * (1 - τ) ^ (-(1 / 3 : ℝ)) * (A n d).toReal +
            C * u ^ (-(1 / 2 : ℝ)) + η

theorem a0_eq (n : ℕ) : a0 n = 1 / 500 / (2 : ℝ) ^ n := by
  rw [a0]; push_cast; ring

/-- The normalizing similarity of Step 2a and its properties: for `c_A ≠ c_B` there is a similarity
`S` of ratio `|c_B - c_A|⁻¹` with `S c_A = 0`, `S c_B = e₁`. -/
theorem exists_normalizer (hd : 0 < d) {cA cB : Rd d} (hAB : cA ≠ cB) :
    ∃ (b : Rd d) (O : Rd d ≃ₗᵢ[ℝ] Rd d), simAffine b ‖cB - cA‖⁻¹ O cA = 0 ∧
      simAffine b ‖cB - cA‖⁻¹ O cB = e₁ d := by
  have hv : cB - cA ≠ 0 := sub_ne_zero.2 (Ne.symm hAB)
  have hr : 0 < ‖cB - cA‖ := norm_pos_iff.2 hv
  obtain ⟨O, hO⟩ := Lower.exists_frame hd (norm_inv_norm_smul hv)
  refine ⟨-(‖cB - cA‖⁻¹ • O.symm cA), O.symm, ?_, ?_⟩
  · simp only [simAffine]
    rw [neg_add_cancel]
  · simp only [simAffine]
    have h1 : O.symm cB = O.symm cA + ‖cB - cA‖ • e₁ d := by
      have h2 : O.symm (cB - cA) = ‖cB - cA‖ • e₁ d := by
        have hu : ‖cB - cA‖ • O (e₁ d) = cB - cA := by
          rw [hO, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
        calc O.symm (cB - cA) = O.symm (‖cB - cA‖ • O (e₁ d)) := by rw [hu]
          _ = ‖cB - cA‖ • e₁ d := by rw [map_smul, LinearIsometryEquiv.symm_apply_apply]
      rw [map_sub] at h2
      rw [← h2]
      abel
    rw [h1, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    abel

/-- **T1: Lemma 4.3 in the all-scale form** (HA3 D5), for every dimension `d ≥ 2`. -/
theorem localPenalizedMean (hd2 : 2 ≤ d) : LocalPenalizedMean d := by
  classical
  have hd : 0 < d := by omega
  obtain ⟨κ₀, hκ₀⟩ := exists_isLFPPKernel d
  obtain ⟨Cs, -, hstep2⟩ := step2 hd2 hκ₀
  refine ⟨Cs, fun n _ τ hτ u hu η hη => ?_⟩
  obtain ⟨δ₀, hδ₀, h⟩ := hstep2 n τ hτ u hu η hη
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  refine ⟨min δ₀ (1 / (16 * Real.sqrt d)), lt_min hδ₀ (by positivity),
    fun δ hδ L hL cA cB hAB1 hAB2 F hF => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ₀' : δ < δ₀ := hδ.2.trans_le (min_le_left _ _)
  have hδs : Real.sqrt d * δ ≤ 1 / 16 := by
    have h1 := hδ.2.le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hr : 0 < ‖cB - cA‖ := lt_of_lt_of_le (by positivity) hAB1
  have hAB : cA ≠ cB := fun h => by rw [h, sub_self, norm_zero] at hr; exact lt_irrefl _ hr
  obtain ⟨b, O, hSA, hSB⟩ := exists_normalizer hd hAB
  have hri : 0 < ‖cB - cA‖⁻¹ := inv_pos.2 hr
  have hrL : ‖cB - cA‖⁻¹ * L ≤ 4 := by
    rw [inv_mul_le_iff₀ hr]; linarith
  -- the normalized configurations
  set S := simAffine b ‖cB - cA‖⁻¹ O with hSdef
  set φ : Config d → Config d := fun c => (c.1.map S, c.2.map S) with hφ
  -- every configuration of `F` is nondegenerate and normalizes to a `NormCfg`
  have hgood : ∀ c ∈ F, GoodPair n c := by
    intro c hc
    obtain ⟨x, y, h1, hx, hy, hQ⟩ := hF c hc
    refine ⟨x, y, h1, fun hxy => ?_, hQ⟩
    have h2 : ‖cB - cA‖ ≤ ‖x - cA‖ + ‖y - cB‖ := by
      calc ‖cB - cA‖ = ‖(x - cA) - (y - cB)‖ := by rw [hxy]; congr 1; abel
        _ ≤ ‖x - cA‖ + ‖y - cB‖ := norm_sub_le _ _
    have h3 : Real.sqrt d * δ * L ≤ L / 16 := by nlinarith
    linarith
  have hnorm : ∀ c ∈ F, NormCfg n (4 * Real.sqrt d * δ) (φ c) := by
    intro c hc
    obtain ⟨x, y, h1, hx, hy, hQ⟩ := hF c hc
    refine ⟨S x, S y, by simp [hφ, h1], ?_, ?_, ?_⟩
    · have e : ‖S x‖ = ‖cB - cA‖⁻¹ * ‖x - cA‖ := by
        rw [← sub_zero (S x), ← hSA, hSdef, norm_simAffine_sub b hri O]
      rw [e]
      calc ‖cB - cA‖⁻¹ * ‖x - cA‖ ≤ ‖cB - cA‖⁻¹ * (Real.sqrt d * δ * L) :=
            mul_le_mul_of_nonneg_left hx hri.le
        _ = Real.sqrt d * δ * (‖cB - cA‖⁻¹ * L) := by ring
        _ ≤ Real.sqrt d * δ * 4 := mul_le_mul_of_nonneg_left hrL (by positivity)
        _ = 4 * Real.sqrt d * δ := by ring
    · have e : ‖S y - e₁ d‖ = ‖cB - cA‖⁻¹ * ‖y - cB‖ := by
        rw [← hSB, hSdef, norm_simAffine_sub b hri O]
      rw [e]
      calc ‖cB - cA‖⁻¹ * ‖y - cB‖ ≤ ‖cB - cA‖⁻¹ * (Real.sqrt d * δ * L) :=
            mul_le_mul_of_nonneg_left hy hri.le
        _ = Real.sqrt d * δ * (‖cB - cA‖⁻¹ * L) := by ring
        _ ≤ Real.sqrt d * δ * 4 := mul_le_mul_of_nonneg_left hrL (by positivity)
        _ = 4 * Real.sqrt d * δ := by ring
    · exact goodFamily_map_simAffine b hri O hQ
  -- the kernel and the drift are invariant
  have hK : ∀ c ∈ F, ∀ c' ∈ F, δ⁻¹ * scaleCov κ₀ (Ioi 0) (polyMeasure (φ c).1)
      (polyMeasure (φ c).2) (polyMeasure (φ c').1) (polyMeasure (φ c').2) =
      δ⁻¹ * logCov (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1) (polyMeasure c'.2) := by
    intro c hc c' hc'
    simp only [hφ, hSdef, polyMeasure_map_simAffine b hri O]
    rw [scaleCov_map_simAffine_Ioi hκ₀ b hri O,
      (scaleCov_eq_logCov_cfg hκ₀ (hgood c hc) (hgood c' hc')).2.2]
  have hb : ∀ c ∈ F, -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen (φ c).2 / polyLen (φ c).1)) =
      -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1)) := by
    intro c _
    simp only [hφ, hSdef, polyLen_map_simAffine b hri O, mul_div_mul_left _ _ hri.ne']
  have hPSD : PSDOn (F.image φ) (fun c c' => δ⁻¹ * scaleCov κ₀ (Ioi 0) (polyMeasure c.1)
      (polyMeasure c.2) (polyMeasure c'.1) (polyMeasure c'.2)) :=
    HigherDimLFPP.Var.psdOn_const_mul (show PSDOn (F.image φ)
      (fun c c' => ⟪cfgV κ₀ c, cfgV κ₀ c'⟫) from LQGDimension.posSemidef_gramOn _ (cfgV κ₀))
      (inv_nonneg.2 hδ0.le)
  have e1 := HigherDimLFPP.Var.gEM_image F φ (fun c c' => δ⁻¹ * scaleCov κ₀ (Ioi 0)
    (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1) (polyMeasure c'.2))
    (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) hPSD
  have e2 : gaussianExpectedMax F
      (fun c c' => δ⁻¹ * logCov (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1)
        (polyMeasure c'.2))
      (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) =
      gaussianExpectedMax (F.image φ) (fun c c' => δ⁻¹ * scaleCov κ₀ (Ioi 0) (polyMeasure c.1)
        (polyMeasure c.2) (polyMeasure c'.1) (polyMeasure c'.2))
      (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) := by
    rw [e1]
    exact LQGDimension.Subadd.gEM_congr F (fun c hc c' hc' => (hK c hc c' hc').symm)
      (fun c hc => (hb c hc).symm)
  rw [e2]
  refine h δ ⟨hδ0, hδ₀'⟩ (F.image φ) fun c hc => ?_
  obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.1 hc
  exact hnorm c₀ hc₀

end T1

/-! ## T2: the cutoff version (Step 0) -/

section T2

/-- **T2: Lemma 4.3 for the band fields** (HA3 D5, Step 0).  With the constant `C` of T1 and the
same `δ₀`, the bound of `LocalPenalizedMean` holds for the covariance
`δ⁻¹ Cov(⟨H_S, ν_{[x,y]} - ν_Q⟩, ⟨H_S, ν_{[x',y']} - ν_{Q'}⟩)` of the band field `H_S` of every
admissible kernel `κ` and every measurable scale set `S ⊆ (0, ∞)` (every band `(a, b)`,
`0 ≤ a < b ≤ ∞`; for `S = (ε, 1)` this is the cutoff field `H_{ε,1}`), uniformly in `κ` and `S`. -/
theorem localPenalizedMean_band (hd2 : 2 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → ∀ τ ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, ∀ η > 0,
      ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
      ∀ S : Set ℝ, MeasurableSet S → S ⊆ Ioi 0 → ∀ L > 0, ∀ cA cB : Rd d,
        L / 4 ≤ ‖cB - cA‖ → ‖cB - cA‖ ≤ 4 * L →
        ∀ F : Finset (Config d),
          (∀ c ∈ F, ∃ x y : Rd d, c.1 = [x, y] ∧ ‖x - cA‖ ≤ Real.sqrt d * δ * L ∧
            ‖y - cB‖ ≤ Real.sqrt d * δ * L ∧ c.2 ∈ goodFamily (2 ^ n) (a0 n) x y) →
          gaussianExpectedMax F
              (fun c c' => δ⁻¹ * scaleCov κ S (polyMeasure c.1) (polyMeasure c.2)
                (polyMeasure c'.1) (polyMeasure c'.2))
              (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) ≤
            (1 + u) ^ (2 / 3 : ℝ) * (1 - τ) ^ (-(1 / 3 : ℝ)) * (A n d).toReal +
              C * u ^ (-(1 / 2 : ℝ)) + η := by
  have hd : 0 < d := by omega
  obtain ⟨C, hT1⟩ := localPenalizedMean hd2
  refine ⟨C, fun n hn τ hτ u hu η hη => ?_⟩
  obtain ⟨δ₀, hδ₀, h⟩ := hT1 n hn τ hτ u hu η hη
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  refine ⟨min δ₀ (1 / (16 * Real.sqrt d)), lt_min hδ₀ (by positivity),
    fun δ hδ κ hκ S hS hS0 L hL cA cB hAB1 hAB2 F hF => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδs : Real.sqrt d * δ ≤ 1 / 16 := by
    have h1 := hδ.2.le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  -- the configurations are nondegenerate
  have hgood : ∀ c ∈ F, GoodPair n c := by
    intro c hc
    obtain ⟨x, y, h1, hx, hy, hQ⟩ := hF c hc
    refine ⟨x, y, h1, fun hxy => ?_, hQ⟩
    have h2 : ‖cB - cA‖ ≤ ‖x - cA‖ + ‖y - cB‖ := by
      calc ‖cB - cA‖ = ‖(x - cA) - (y - cB)‖ := by rw [hxy]; congr 1; abel
        _ ≤ ‖x - cA‖ + ‖y - cB‖ := norm_sub_le _ _
    have h3 : Real.sqrt d * δ * L ≤ L / 16 := by nlinarith
    linarith
  -- Sudakov–Fernique against the all-scale covariance
  have hPS : PSDOn F (fun c c' => δ⁻¹ * scaleCov κ S (polyMeasure c.1) (polyMeasure c.2)
      (polyMeasure c'.1) (polyMeasure c'.2)) :=
    HigherDimLFPP.Var.psdOn_const_mul (psdOn_scaleCov (κ := κ) S F (fun c => polyMeasure c.1)
      (fun c => polyMeasure c.2)) (inv_nonneg.2 hδ0.le)
  have hPL : PSDOn F (fun c c' => δ⁻¹ * logCov (polyMeasure c.1) (polyMeasure c.2)
      (polyMeasure c'.1) (polyMeasure c'.2)) := by
    refine psdOn_congr (fun c hc c' hc' => ?_) (HigherDimLFPP.Var.psdOn_const_mul
      (psdOn_scaleCov (κ := κ) (Ioi 0) F (fun c => polyMeasure c.1) (fun c => polyMeasure c.2))
      (inv_nonneg.2 hδ0.le))
    rw [(scaleCov_eq_logCov_cfg hκ (hgood c hc) (hgood c' hc')).2.2]
  have hdist : ∀ c ∈ F, ∀ c' ∈ F,
      δ⁻¹ * scaleCov κ S (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c.1) (polyMeasure c.2) +
        δ⁻¹ * scaleCov κ S (polyMeasure c'.1) (polyMeasure c'.2) (polyMeasure c'.1)
          (polyMeasure c'.2) -
        2 * (δ⁻¹ * scaleCov κ S (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1)
          (polyMeasure c'.2)) ≤
      δ⁻¹ * logCov (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c.1) (polyMeasure c.2) +
        δ⁻¹ * logCov (polyMeasure c'.1) (polyMeasure c'.2) (polyMeasure c'.1) (polyMeasure c'.2) -
        2 * (δ⁻¹ * logCov (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1)
          (polyMeasure c'.2)) := by
    intro c hc c' hc'
    obtain ⟨p1, p2, e12⟩ := scaleCov_eq_logCov_cfg hκ (hgood c hc) (hgood c' hc')
    have e11 := (scaleCov_eq_logCov_cfg hκ (hgood c hc) (hgood c hc)).2.2
    have e22 := (scaleCov_eq_logCov_cfg hκ (hgood c' hc') (hgood c' hc')).2.2
    rw [← e11, ← e22, ← e12]
    -- both sides are `δ⁻¹ ‖V(c) - V(c')‖²` for the bands `S` and `(0, ∞)`
    have hgram : ∀ T : Set ℝ, scaleCov κ T (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c.1)
        (polyMeasure c.2) + scaleCov κ T (polyMeasure c'.1) (polyMeasure c'.2) (polyMeasure c'.1)
        (polyMeasure c'.2) - 2 * scaleCov κ T (polyMeasure c.1) (polyMeasure c.2)
        (polyMeasure c'.1) (polyMeasure c'.2) =
        ‖bandVecM κ T (polyMeasure c.1) (polyMeasure c.2) -
          bandVecM κ T (polyMeasure c'.1) (polyMeasure c'.2)‖ ^ 2 := by
      intro T
      rw [norm_sub_sq_real, ← scaleCov_self, ← scaleCov_self]
      simp only [scaleCov]
      ring
    have hS1 := p1.mono_set hS hS0
    have hS2 := p2.mono_set hS hS0
    have hsub := bandVecM_sub_bandVecM hκ hS1 hS2
    have hsub' := bandVecM_sub_bandVecM hκ p1 p2
    have hdom := scaleCov_self_le_of_subset hS hS0 (IsPairable.sub hκ p1 p2)
    have key : ‖bandVecM κ S (polyMeasure c.1) (polyMeasure c.2) -
        bandVecM κ S (polyMeasure c'.1) (polyMeasure c'.2)‖ ^ 2 ≤
        ‖bandVecM κ (Ioi 0) (polyMeasure c.1) (polyMeasure c.2) -
          bandVecM κ (Ioi 0) (polyMeasure c'.1) (polyMeasure c'.2)‖ ^ 2 := by
      rw [hsub, hsub', ← scaleCov_self, ← scaleCov_self]
      exact hdom
    have h1 := hgram S
    have h2 := hgram (Ioi 0)
    have hδi : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ0.le
    have h3 := mul_le_mul_of_nonneg_left key hδi
    nlinarith
  refine (gEM_le_of_dist F hPS hPL _ hdist).trans ?_
  exact h δ ⟨hδ0, hδ.2.trans_le (min_le_left _ _)⟩ L hL cA cB hAB1 hAB2 F hF

/-- **T2 for the band fields themselves** (HA3 D5 in its field form): for every white-noise model,
every band `0 < a ≤ b` and every continuous version `H` of `H_{a,b}`,
`E max_{c ∈ F} (δ^{-1/2} ⟨H_{a,b}, ν_{[x,y]} - ν_Q⟩ - (1-τ) E_δ(c)) ≤
  (1+u)^{2/3}(1-τ)^{-1/3} A_{n,d} + C u^{-1/2} + η`, with the constant and `δ₀` of T2 (uniform in
the kernel, the model, the band and the version). -/
theorem localPenalizedMean_bandField (hd2 : 2 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → ∀ τ ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, ∀ η > 0,
      ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}, IsWhiteNoise P W →
      ∀ a b : ℝ, 0 < a → a ≤ b → ∀ H : Rd d → Ω → ℝ, IsBandVersion P W κ a b H →
      ∀ L > 0, ∀ cA cB : Rd d, L / 4 ≤ ‖cB - cA‖ → ‖cB - cA‖ ≤ 4 * L →
        ∀ F : Finset (Config d),
          (∀ c ∈ F, ∃ x y : Rd d, c.1 = [x, y] ∧ ‖x - cA‖ ≤ Real.sqrt d * δ * L ∧
            ‖y - cB‖ ≤ Real.sqrt d * δ * L ∧ c.2 ∈ goodFamily (2 ^ n) (a0 n) x y) →
          ∫ ω, (⨆ c : F, (cfgVal δ (fun z => H z ω) c - (1 - τ) * (δ ^ 2)⁻¹ *
              Real.log (polyLen (c : Config d).2 / polyLen (c : Config d).1))) ∂P ≤
            (1 + u) ^ (2 / 3 : ℝ) * (1 - τ) ^ (-(1 / 3 : ℝ)) * (A n d).toReal +
              C * u ^ (-(1 / 2 : ℝ)) + η := by
  obtain ⟨C, hT2⟩ := localPenalizedMean_band hd2
  refine ⟨C, fun n hn τ hτ u hu η hη => ?_⟩
  obtain ⟨δ₀, hδ₀, h⟩ := hT2 n hn τ hτ u hu η hη
  refine ⟨δ₀, hδ₀, fun δ hδ κ hκ Ω _ P W hW a b ha hab H hH L hL cA cB hAB1 hAB2 F hF => ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ c : F, cfgVal δ (fun z => H z ω) c = W (cfgVec κ a b δ c) ω :=
    ae_all_iff.2 fun c => cfgVal_ae_eq hκ hW ha hab hH δ c
  have e1 : ∀ ω, (∀ c : F, cfgVal δ (fun z => H z ω) c = W (cfgVec κ a b δ c) ω) →
      (⨆ c : F, (cfgVal δ (fun z => H z ω) c - (1 - τ) * (δ ^ 2)⁻¹ *
        Real.log (polyLen (c : Config d).2 / polyLen (c : Config d).1))) =
      ⨆ c : F, W (cfgVec κ a b δ c) ω +
        (fun c : Config d => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) c := by
    intro ω hω
    congr 1
    funext c
    rw [hω c, sub_eq_add_neg]
  refine (le_of_eq (integral_congr_ae (hall.mono fun ω hω => e1 ω hω))).trans ?_
  rw [hW.integral_iSup_eq_gaussianExpectedMax F (cfgVec κ a b δ)
    (fun c : Config d => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1)))]
  have hcongr : gaussianExpectedMax F (fun c c' => ⟪cfgVec κ a b δ c, cfgVec κ a b δ c'⟫)
      (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) =
      gaussianExpectedMax F (fun c c' => δ⁻¹ * scaleCov κ (Ioo a b) (polyMeasure c.1)
        (polyMeasure c.2) (polyMeasure c'.1) (polyMeasure c'.2))
      (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) :=
    LQGDimension.gaussianExpectedMax_congr F _ fun c _ c' _ => inner_cfgVec hκ ha hab hδ.1 c c'
  rw [hcongr]
  exact h δ hδ κ hκ (Ioo a b) measurableSet_Ioo (fun t ht => lt_trans ha ht.1) L hL cA cB hAB1
    hAB2 F hF

end T2

/-! ## T3: the good-record mean bound (HA3 D6 (iv)) -/

section T3

/-- **T3: the good-record mean bound** (HA3 D6 (iv); P-U3's `GoodRecordMeanBound`), for every
admissible kernel in every dimension `d ≥ 2`. -/
theorem goodRecordMeanBound_holds (hd2 : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    GoodRecordMeanBound d κ := by
  classical
  have hd : 0 < d := by omega
  obtain ⟨C, hT2⟩ := localPenalizedMean_band hd2
  refine ⟨C, fun Ω _ P W hW H hH n hn τ hτ u hu => ?_⟩
  obtain ⟨δ₀, hδ₀, hb⟩ := hT2 n hn τ hτ u hu 1 one_pos
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  refine ⟨min δ₀ (1 / (8 * Real.sqrt d)), lt_min hδ₀ (by positivity),
    fun δ hδ ε hε g hg F hF hne => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδs : Real.sqrt d * δ ≤ 1 / 8 := by
    have h1 := hδ.2.le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  -- the record variables form the Gaussian family of the cutoff field (interface (I1))
  rw [integral_iSup_cfgVal hκ hW hε.1 hε.2.le (hH ε hε) δ F]
  have hC0 : ∀ c c' : Config d, ⟪cfgVec κ ε 1 δ c, cfgVec κ ε 1 δ c'⟫ =
      δ⁻¹ * scaleCov κ (Ioo ε 1) (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1)
        (polyMeasure c'.2) := fun c c' => inner_cfgVec hκ hε.1 hε.2.le hδ0 c c'
  have hPSD : PSDOn F (fun c c' => ⟪cfgVec κ ε 1 δ c, cfgVec κ ε 1 δ c'⟫) :=
    LQGDimension.posSemidef_gramOn F (cfgVec κ ε 1 δ)
  -- on bin `k`, `Y ≤ (Y - (1-τ)E_δ) + (1-τ)(k+1)`
  have hbin : ∀ c ∈ F, (fun _ : Config d => (0 : ℝ)) c ≤
      (fun c : Config d => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) c +
        (1 - τ) * ((g.bin : ℝ) + 1) := by
    intro c hc
    obtain ⟨x, y, h1, -, -, -, hk2, -, -⟩ := hF hc
    simp only
    rw [h1, polyLen_pair]
    have h3 : (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / ‖y - x‖) ≤ (g.bin : ℝ) + 1 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      linarith
    have hτ1 : 0 ≤ 1 - τ := by linarith [hτ.2]
    have := mul_le_mul_of_nonneg_left h3 hτ1
    nlinarith
  refine (gEM_le_of_drift_le F hne hPSD hbin).trans ?_
  -- the record family lies in the family of Lemma 4.3 (HA3 D6 (iv))
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (2 : ℝ) ^ (-g.loc.1) := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; positivity
  obtain ⟨cA, hcA⟩ : ∃ cA : Rd d, cA = corner (side δ g.loc.1) g.loc.2.1 := ⟨_, rfl⟩
  obtain ⟨cB, hcB⟩ : ∃ cB : Rd d, cB = corner (side δ g.loc.1) g.loc.2.2 := ⟨_, rfl⟩
  have hside : side δ g.loc.1 = δ * L := by rw [hL]; rfl
  have hcfg : ∀ c ∈ F, ∃ x y : Rd d, c.1 = [x, y] ∧ ‖x - cA‖ ≤ Real.sqrt d * δ * L ∧
      ‖y - cB‖ ≤ Real.sqrt d * δ * L ∧ c.2 ∈ goodFamily (2 ^ n) (a0 n) x y ∧
      (2 : ℝ) ^ (-g.loc.1 - 1) < ‖y - x‖ ∧ ‖y - x‖ ≤ L := by
    intro c hc
    obtain ⟨x, y, h1, ⟨hl1, hl2, hxQ, hyQ⟩, hQ, -⟩ := hF hc
    refine ⟨x, y, h1, ?_, ?_, hQ, hl1, by rw [hL]; exact hl2⟩
    · have := norm_sub_corner_le (side_pos hδ0 g.loc.1) hxQ
      rw [← hcA, hside] at this
      linarith
    · have := norm_sub_corner_le (side_pos hδ0 g.loc.1) hyQ
      rw [← hcB, hside] at this
      linarith
  -- the centers are at distance in `[L/4, 4L]`
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨x, y, -, hx, hy, -, hl1, hl2⟩ := hcfg c₀ hc₀
  have hhalf : (2 : ℝ) ^ (-g.loc.1 - 1) = L / 2 := by
    rw [hL, zpow_sub₀ two_ne_zero, zpow_one]
  have hsmall : Real.sqrt d * δ * L ≤ L / 8 := by nlinarith
  have hAB1 : L / 4 ≤ ‖cB - cA‖ := by
    have h2 : ‖y - x‖ ≤ ‖cB - cA‖ + ‖x - cA‖ + ‖y - cB‖ := by
      calc ‖y - x‖ = ‖(cB - cA) - (x - cA) + (y - cB)‖ := by congr 1; abel
        _ ≤ ‖(cB - cA) - (x - cA)‖ + ‖y - cB‖ := norm_add_le _ _
        _ ≤ ‖cB - cA‖ + ‖x - cA‖ + ‖y - cB‖ := by linarith [norm_sub_le (cB - cA) (x - cA)]
    rw [hhalf] at hl1
    linarith
  have hAB2 : ‖cB - cA‖ ≤ 4 * L := by
    have h2 : ‖cB - cA‖ ≤ ‖y - x‖ + ‖x - cA‖ + ‖y - cB‖ := by
      calc ‖cB - cA‖ = ‖(y - x) + (x - cA) - (y - cB)‖ := by congr 1; abel
        _ ≤ ‖(y - x) + (x - cA)‖ + ‖y - cB‖ := norm_sub_le _ _
        _ ≤ ‖y - x‖ + ‖x - cA‖ + ‖y - cB‖ := by linarith [norm_add_le (y - x) (x - cA)]
    linarith
  have hbound := hb δ ⟨hδ0, hδ.2.trans_le (min_le_left _ _)⟩ κ hκ (Ioo ε 1) measurableSet_Ioo
    (fun t ht => lt_trans hε.1 ht.1) L hL0 cA cB hAB1 hAB2 F fun c hc => by
      obtain ⟨x, y, h1, hx, hy, hQ, -⟩ := hcfg c hc
      exact ⟨x, y, h1, hx, hy, hQ⟩
  have hcongr : gaussianExpectedMax F (fun c c' => ⟪cfgVec κ ε 1 δ c, cfgVec κ ε 1 δ c'⟫)
      (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) =
      gaussianExpectedMax F (fun c c' => δ⁻¹ * scaleCov κ (Ioo ε 1) (polyMeasure c.1)
        (polyMeasure c.2) (polyMeasure c'.1) (polyMeasure c'.2))
      (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) :=
    LQGDimension.gaussianExpectedMax_congr F _ fun c _ c' _ => hC0 c c'
  rw [hcongr]
  have hbs : bStar d n τ u C = (1 + u) ^ (2 / 3 : ℝ) * (1 - τ) ^ (-(1 / 3 : ℝ)) *
      (A n d).toReal + C * u ^ (-(1 / 2 : ℝ)) + 1 := rfl
  rw [hbs]
  linarith

/-- **The good-record mean bound in every dimension `d ≥ 2`** (the input of
`HigherDimLFPP.Upper.upperComparison_of_goodRecordMeanBound`). -/
theorem goodRecordMeanBound_all : ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    GoodRecordMeanBound d κ :=
  fun _ hd _ hκ => goodRecordMeanBound_holds hd hκ

end T3

end HigherDimLFPP.Upper
