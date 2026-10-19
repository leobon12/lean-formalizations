import GaussianLQG.Core.Setup
import GaussianLQG.LQG.Scaling.Measurability
import GaussianLQG.LQG.Exponents
import GaussianLQG.Metric.HopfRinow
import GaussianLQG.Metric.Geodesic
import LQGMetric.Meas.CR
import LQGMetric.Meas.Geod
import LQGMetric.Papers.GM.S2.TightE

/-!
# Bounded compactness and existence of geodesics (blueprint Lemma `lem:geodesics-exist`)

Blueprint Lemma `lem:geodesics-exist`: there is `γ_g > 0` such that for each `γ ∈ (0, γ_g]`, almost
surely, the annulus crossing distances `L_{2^k}` tend to `∞`, the closed `D^γ`-balls are compact,
and any two points of `ℂ` are joined by a constant-speed `D^γ`-geodesic
(`Setup.exists_ae_geodesics`; the event form `Setup.exists_geoEvent` gives a measurable event
`Ω^geo_γ ⊂ Ω_γ` of probability one). The proof takes Lemma `lem:scaling`(d)
(`Setup.AnnulusScaling`) as a hypothesis; that interface lemma is proved separately.

Proof (blueprint): choose `γ_g` so small that `ξQ ≥ 3/4` and `64 ξ² ≤ 2` (consequences of (S1),
`Setup.exists_exponent_bounds`). Then `E[L_R^{-8}] ≤ C R^{-4}`, so by Markov's inequality
`P[L_{2^k} ≤ 2^{k/4}] ≤ C 4^{-k}`, and Borel–Cantelli gives `L_{2^k} > 2^{k/4}` for all large `k`
a.s. If `D` is a length metric, every point of `B̄_R(0)` is at `D`-distance at least `L_R` from
every point outside `B_{2R}(0)` (`annulusCross_le_of_isLength`), so `D`-balls are
Euclidean-bounded, hence compact (`isCompact_setOf_le_of_tendsto_annulusCross`), and Lemma
`lem:hopf-rinow` (`exists_isGeod01_of_isCompact_closedBall`) gives geodesics.

Also here: two Markov inequalities for `ℝ≥0∞`-valued random variables, used again in the
localization lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

/-! ## Exponents -/

/-- A consequence of (S1) (blueprint (1.3), `lem:exponents`): for every `ε > 0` there is
`γε ∈ (0, 1]` such that `0 < ξ_γ ≤ ε` and `|ξ_γ Q_γ - 1| ≤ ε` for all `γ ∈ (0, γε]`. It follows from
`Setup.exists_exponents`: `γ/3 ≤ ξ_γ ≤ γ` and `|ξ_γ Q_γ - 1| ≤ C₁ ξ_γ`. -/
theorem Setup.exists_exponent_bounds (S : Setup) {ε : ℝ} (hε : 0 < ε) :
    ∃ γε : ℝ, 0 < γε ∧ γε ≤ 1 ∧ ∀ γ ∈ Ioc (0 : ℝ) γε,
      0 < S.ξ γ ∧ S.ξ γ ≤ ε ∧ |S.ξ γ * Q γ - 1| ≤ ε := by
  obtain ⟨γe, C₁, hγe, -, h⟩ := S.exists_exponents
  have hC : 0 < max C₁ 1 := one_pos.trans_le (le_max_right _ _)
  refine ⟨min (min γe 1) (ε / max C₁ 1), lt_min (lt_min hγe one_pos) (div_pos hε hC),
    (min_le_left _ _).trans (min_le_right _ _), fun γ hγ => ?_⟩
  obtain ⟨hξ3, hξγ, -, hQ⟩ :=
    h γ ⟨hγ.1, hγ.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hCγ : max C₁ 1 * γ ≤ ε := by
    rw [mul_comm]
    exact (le_div_iff₀ hC).1 (hγ.2.trans (min_le_right _ _))
  have hξ : 0 < S.ξ γ := by linarith [hγ.1]
  refine ⟨hξ, hξγ.trans ((le_mul_of_one_le_left hγ.1.le (le_max_right _ _)).trans hCγ), ?_⟩
  calc |S.ξ γ * Q γ - 1| ≤ C₁ * S.ξ γ := hQ
    _ ≤ max C₁ 1 * S.ξ γ := mul_le_mul_of_nonneg_right (le_max_left _ _) hξ.le
    _ ≤ max C₁ 1 * γ := mul_le_mul_of_nonneg_left hξγ hC.le
    _ ≤ ε := hCγ

/-! ## Markov inequalities in `ℝ≥0∞` -/

section markov

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Lower-tail Markov bound through negative moments: `μ{g ≤ t} ≤ t^p ∫ g^{-p}`. -/
theorem measure_le_le_rpow_mul_lintegral_inv_rpow {g : Ω → ℝ≥0∞} (hg : AEMeasurable g μ)
    {p : ℝ} (hp : 0 < p) {t : ℝ≥0∞} (ht0 : t ≠ 0) (htop : t ≠ ⊤) :
    μ {ω | g ω ≤ t} ≤ t ^ p * ∫⁻ ω, (g ω)⁻¹ ^ p ∂μ := by
  have hf : AEMeasurable (fun ω => (g ω)⁻¹ ^ p) μ := hg.inv.pow_const p
  have hε0 : t⁻¹ ^ p ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, ENNReal.inv_eq_zero, htop, false_and,
      ENNReal.inv_eq_top, ht0, false_or, not_false_eq_true]
  have hεtop : t⁻¹ ^ p ≠ ⊤ := by
    simp only [ne_eq, ENNReal.rpow_eq_top_iff, ENNReal.inv_eq_zero, htop, false_and,
      ENNReal.inv_eq_top, ht0, or_self, not_false_eq_true]
  calc μ {ω | g ω ≤ t} ≤ μ {ω | t⁻¹ ^ p ≤ (g ω)⁻¹ ^ p} :=
        measure_mono fun ω (hω : g ω ≤ t) => ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.2 hω) hp.le
    _ ≤ (∫⁻ ω, (g ω)⁻¹ ^ p ∂μ) / t⁻¹ ^ p := meas_ge_le_lintegral_div hf hε0 hεtop
    _ = t ^ p * ∫⁻ ω, (g ω)⁻¹ ^ p ∂μ := by
        rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_rpow, inv_inv]

/-- Upper-tail Markov bound through moments: `μ{t ≤ g} ≤ t^{-p} ∫ g^p`. -/
theorem measure_ge_le_inv_rpow_mul_lintegral_rpow {g : Ω → ℝ≥0∞} (hg : AEMeasurable g μ)
    {p : ℝ} (hp : 0 < p) {t : ℝ≥0∞} (ht0 : t ≠ 0) (htop : t ≠ ⊤) :
    μ {ω | t ≤ g ω} ≤ (t ^ p)⁻¹ * ∫⁻ ω, g ω ^ p ∂μ := by
  have hf : AEMeasurable (fun ω => g ω ^ p) μ := hg.pow_const p
  have hε0 : t ^ p ≠ 0 := by
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, ht0, false_and, htop, false_or,
      not_false_eq_true]
  have hεtop : t ^ p ≠ ⊤ := by
    simp only [ne_eq, ENNReal.rpow_eq_top_iff, ht0, false_and, htop, or_self,
      not_false_eq_true]
  calc μ {ω | t ≤ g ω} ≤ μ {ω | t ^ p ≤ g ω ^ p} :=
        measure_mono fun ω (hω : t ≤ g ω) => ENNReal.rpow_le_rpow hω hp.le
    _ ≤ (∫⁻ ω, g ω ^ p ∂μ) / t ^ p := meas_ge_le_lintegral_div hf hε0 hεtop
    _ = (t ^ p)⁻¹ * ∫⁻ ω, g ω ^ p ∂μ := by rw [ENNReal.div_eq_inv_mul]

end markov

/-! ## Deterministic part: annulus crossings and bounded compactness -/

/-- In a length metric, every point of `B̄_R(0)` is at distance at least
`L_R = inf {D(x, y) : |x| = R, |y| = 2R}` from every point outside `B_{2R}(0)`: a near-geodesic
crosses both circles (blueprint, proof of Lemma `lem:geodesics-exist`). -/
theorem annulusCross_le_of_isLength {D : ContMetric} (hlen : D.IsLength) {R : ℝ} {z x : ℂ}
    (hz : ‖z‖ ≤ R) (hx : 2 * R ≤ ‖x‖) : annulusCross D.1 R ≤ ENNReal.ofReal (D.1 (z, x)) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, -, hDr, hrL⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlt
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hcross : ∀ u ∈ Metric.sphere (0 : ℂ) R, ∀ v ∈ Metric.sphere (0 : ℂ) (2 * R),
      r ≤ D.1 (u, v) := by
    intro u hu v hv
    have h1 : annulusCross D.1 R ≤ ENNReal.ofReal (D.1 (u, v)) := by
      unfold annulusCross
      exact (iInf₂_le u hu).trans (iInf₂_le v hv)
    exact (ENNReal.ofReal_le_ofReal_iff (ContMetric.nonneg D u v)).1 (hrL.le.trans h1)
  have hrD : r ≤ D.1 (z, x) := GM.Tight.le_of_forall_crossing hlen (z := 0)
    (by linarith : R ≤ 2 * R) (by simpa using hz) (by simpa using hx) hcross
  exact absurd hDr (not_lt.2 (ENNReal.ofReal_le_ofReal hrD))

/-- If `D` is a length metric and `L_{2^k} → ∞`, then the closed `D`-balls are compact (blueprint,
proof of Lemma `lem:geodesics-exist`). -/
theorem isCompact_setOf_le_of_tendsto_annulusCross {D : ContMetric} (hlen : D.IsLength)
    (hL : Tendsto (fun k : ℕ => annulusCross D.1 (2 ^ k)) atTop (𝓝 ⊤)) (z : ℂ) (ρ : ℝ) :
    IsCompact {x : ℂ | D.1 (z, x) ≤ ρ} := by
  have h1 : ∀ᶠ k : ℕ in atTop, ENNReal.ofReal ρ < annulusCross D.1 (2 ^ k) :=
    hL.eventually (lt_mem_nhds ENNReal.ofReal_lt_top)
  have h2 : ∀ᶠ k : ℕ in atTop, ‖z‖ ≤ (2 : ℝ) ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually (eventually_ge_atTop _)
  obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
  refine (isCompact_closedBall (0 : ℂ) (2 * 2 ^ k)).of_isClosed_subset
    (isClosed_le (D.1.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const)
    fun x (hx : D.1 (z, x) ≤ ρ) => ?_
  rw [mem_closedBall_zero_iff]
  by_contra hlt
  push Not at hlt
  have h3 := annulusCross_le_of_isLength hlen hk2 hlt.le
  exact absurd (hk1.trans_le (h3.trans (ENNReal.ofReal_le_ofReal hx))) (lt_irrefl _)

/-! ## The probabilistic part -/

/-- `((2^k)^{1/4})^8 (2^k)^{-4} = 4^{-k}`. -/
theorem two_pow_rpow_quarter_aux (k : ℕ) :
    (((2 : ℝ) ^ k) ^ (1 / 4 : ℝ)) ^ (8 : ℝ) * ((2 : ℝ) ^ k) ^ (-4 : ℝ) = (1 / 4 : ℝ) ^ k := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [← Real.rpow_mul h2.le, ← Real.rpow_add h2]
  norm_num
  rw [← pow_mul, mul_comm, pow_mul, one_div, inv_pow]
  norm_num

/-- Borel–Cantelli step of Lemma `lem:geodesics-exist`: if `E[L_{2^k}^{-8}] ≤ C (2^k)^{-4}` for all
`k`, then a.s. `L_{2^k} → ∞`. -/
theorem ae_tendsto_annulusCross_of_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {L : ℕ → Ω → ℝ≥0∞} (hLm : ∀ k, AEMeasurable (L k) μ) {C : ℝ}
    (hmom : ∀ k : ℕ, ∫⁻ ω, (L k ω)⁻¹ ^ (8 : ℝ) ∂μ ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ k) ^ (-4 : ℝ))) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => L k ω) atTop (𝓝 ⊤) := by
  set t : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (((2 : ℝ) ^ k) ^ (1 / 4 : ℝ)) with ht
  have htpos : ∀ k, 0 < ((2 : ℝ) ^ k) ^ (1 / 4 : ℝ) := fun k => by positivity
  have hprob : ∀ k, μ {ω | L k ω ≤ t k} ≤
      ENNReal.ofReal (max C 0) * ENNReal.ofReal (1 / 4) ^ k := by
    intro k
    have ht0 : t k ≠ 0 := by simp only [ht, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact htpos k
    have hmark := measure_le_le_rpow_mul_lintegral_inv_rpow (hLm k) (by norm_num : (0 : ℝ) < 8)
      ht0 ENNReal.ofReal_ne_top
    refine hmark.trans ?_
    have hC : ENNReal.ofReal (C * ((2 : ℝ) ^ k) ^ (-4 : ℝ)) ≤
        ENNReal.ofReal (max C 0 * ((2 : ℝ) ^ k) ^ (-4 : ℝ)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))
    calc t k ^ (8 : ℝ) * ∫⁻ ω, (L k ω)⁻¹ ^ (8 : ℝ) ∂μ
        ≤ t k ^ (8 : ℝ) * ENNReal.ofReal (max C 0 * ((2 : ℝ) ^ k) ^ (-4 : ℝ)) :=
          by gcongr; exact (hmom k).trans hC
      _ = ENNReal.ofReal (max C 0) * ENNReal.ofReal (1 / 4) ^ k := by
          rw [ht, ENNReal.ofReal_rpow_of_nonneg (htpos k).le (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by norm_num),
            ← ENNReal.ofReal_mul (le_max_right C 0)]
          congr 1
          rw [← two_pow_rpow_quarter_aux k]
          ring
  have hsum : ∑' k, μ {ω | L k ω ≤ t k} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hprob)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
    exact (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 (by norm_num))).ne'
  have htend : Tendsto t atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  refine tendsto_nhds_top_mono htend ?_
  filter_upwards [hω] with k hk
  simp only [not_le] at hk
  exact hk.le

/-- **Blueprint Lemma `lem:geodesics-exist`.** Assume Lemma `lem:scaling`(d)
(`Setup.AnnulusScaling`). There is `γ_g ∈ (0, 2)` such that for each `γ ∈ (0, γ_g]`, almost surely:
`D^γ` is a length metric, the annulus crossing distances `L_{2^k}` tend to `∞`, the closed
`D^γ`-balls are compact, and any two points are joined by a constant-speed `D^γ`-geodesic. -/
theorem Setup.exists_ae_geodesics (S : Setup) (hL : S.AnnulusScaling) :
    ∃ γg : ℝ, 0 < γg ∧ γg < 2 ∧ ∀ γ ∈ Ioc (0 : ℝ) γg, ∀ᵐ ω ∂stdP,
      (S.D γ ω).IsLength ∧
      Tendsto (fun k : ℕ => annulusCross (S.D γ ω).1 (2 ^ k)) atTop (𝓝 ⊤) ∧
      (∀ (z : ℂ) (ρ : ℝ), IsCompact {x : ℂ | (S.D γ ω).1 (z, x) ≤ ρ}) ∧
      ∀ z w : ℂ, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η := by
  obtain ⟨γε, hγε, hγε1, hexp⟩ := S.exists_exponent_bounds (ε := 1 / 8) (by norm_num)
  obtain ⟨γs, C, hγs, hLs⟩ := hL 8 (by norm_num)
  refine ⟨min γε γs, lt_min hγε hγs, (min_le_left _ _).trans_lt (by linarith), ?_⟩
  rintro γ ⟨hγ0, hγ⟩
  have hγ2 : γ < 2 := by linarith [min_le_left γε γs]
  obtain ⟨hξ, hξε, hξQ⟩ := hexp γ ⟨hγ0, hγ.trans (min_le_left _ _)⟩
  -- almost surely `D^γ` is a length metric
  obtain ⟨Ωγ, -, hΩγ, hgood⟩ := S.good γ hγ0 hγ2
  have hlen : ∀ᵐ ω ∂stdP, (S.D γ ω).IsLength := by
    filter_upwards [(mem_ae_iff.2 hΩγ : Ωγ ∈ ae stdP)] with ω hω using (hgood ω hω).1
  -- `E[L_{2^k}^{-8}] ≤ C (2^k)^{-4}`
  have hmom : ∀ k : ℕ, ∫⁻ ω, (annulusCross (S.D γ ω).1 (2 ^ k))⁻¹ ^ (8 : ℝ) ∂stdP ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ k) ^ (-4 : ℝ)) := by
    intro k
    have hR : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
    refine (hLs γ ⟨hγ0, hγ.trans (min_le_right _ _)⟩ (2 ^ k) hR).trans ?_
    have hexp' : -((8 : ℝ) * (S.ξ γ * Q γ)) + 8 ^ 2 * S.ξ γ ^ 2 ≤ -4 := by
      have h1 : 7 / 8 ≤ S.ξ γ * Q γ := by
        have := neg_abs_le (S.ξ γ * Q γ - 1)
        linarith
      have h2 : S.ξ γ ^ 2 ≤ 1 / 64 := by nlinarith
      nlinarith
    by_cases hC : 0 ≤ C
    · exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hexp') hC)
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (not_le.1 hC).le
        (by positivity))]
      exact zero_le
  have hcross := ae_tendsto_annulusCross_of_moment
    (fun k => (S.measurable_annulusCross γ (2 ^ k)).aemeasurable) hmom
  filter_upwards [hlen, hcross] with ω h1 h2
  have hc := isCompact_setOf_le_of_tendsto_annulusCross h1 h2
  exact ⟨h1, h2, hc, exists_isGeod01_of_isCompact_closedBall _ h1 hc⟩

/-- **Blueprint Lemma `lem:geodesics-exist`, event form.** Assume `Setup.AnnulusScaling`. There is
`γ_g ∈ (0, 2)` such that for each `γ ∈ (0, γ_g]` there is a measurable event `Ω^geo_γ` of
probability one contained in the event `Ω_γ` of (S2)–(S3) (on it `D^γ` is a length metric with Weyl
scaling), on which `L_{2^k} → ∞`, the closed `D^γ`-balls are compact, and any two points are joined
by a constant-speed `D^γ`-geodesic. -/
theorem Setup.exists_geoEvent (S : Setup) (hL : S.AnnulusScaling) :
    ∃ γg : ℝ, 0 < γg ∧ γg < 2 ∧ ∀ γ ∈ Ioc (0 : ℝ) γg, ∃ Ωgeo : Set Coord,
      MeasurableSet Ωgeo ∧ stdP Ωgeoᶜ = 0 ∧ ∀ ω ∈ Ωgeo,
        (S.D γ ω).IsLength ∧
        (∀ (v : ℕ →₀ ℝ) (z w : ℂ), ENNReal.ofReal ((S.D γ (shiftBy ω v)).1 (z, w)) =
          weylScale (S.ξ γ) (frameFunC S.e S.frame.1 v) (S.D γ ω) z w) ∧
        Tendsto (fun k : ℕ => annulusCross (S.D γ ω).1 (2 ^ k)) atTop (𝓝 ⊤) ∧
        (∀ (z : ℂ) (ρ : ℝ), IsCompact {x : ℂ | (S.D γ ω).1 (z, x) ≤ ρ}) ∧
        ∀ z w : ℂ, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η := by
  obtain ⟨γg, hγg, hγg2, hae⟩ := S.exists_ae_geodesics hL
  refine ⟨γg, hγg, hγg2, fun γ hγ => ?_⟩
  obtain ⟨Ωγ, hΩm, hΩγ, hgood⟩ := S.good γ hγ.1 (hγ.2.trans_lt hγg2)
  obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hae γ hγ))
  refine ⟨Ωγ ∩ tᶜ, hΩm.inter htm.compl, ?_, fun ω hω => ?_⟩
  · rw [compl_inter, compl_compl]
    exact measure_union_null hΩγ ht0
  · have hQ := not_not.1 fun hn => hω.2 (hst hn)
    exact ⟨hQ.1, (hgood ω hω.1).2, hQ.2⟩

/-! ## Compatibility names (cleanup W15) -/

theorem measurable_annulusCross_contMetric (R : ℝ) :
    Measurable fun d : ContMetric => annulusCross d.1 R :=
  (measurable_annulusCross_cont R).comp measurable_subtype_coe

end GaussianLQG
