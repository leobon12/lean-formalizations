import SmallGammaGeodesics.Upper.Competitor
import SmallGammaGeodesics.Upper.ProbeInvEnergy
import SmallGammaGeodesics.Upper.ExponentsGain
import SmallGammaGeodesics.Upper.ResidualField
import SmallGammaGeodesics.Upper.Good

/-!
# The single-probe bound (5.10) (packet P-U3)

Blueprint `s5-upper.tex`, Proposition `prop:single-probe` (BP2 detail D9), with the interface
hypotheses `hCC` (one-sided conformal covariance, `CC.ConfCovLE`) and `h42` (Lemma 4.2′, `Lemma42`)
of ruling G10.

For `γ` small, every measurable a.s. geodesic `η` of the coordinate setup `G`,
`δ ≤ R ≤ 2ξ^{99/200}`, `j ≤ J_γ`, `a ∈ [0,1]` and `r = c_β R ℓ_j^{1/8}`:
`P[𝒢 ∩ {|B_{j,a}(y_η)| > r}] ≤ C (ξ² ℓ²/r³ + ξ² (m + ξ^{99/100} L) ℓ²/r⁴ + ξ² L²/r²)`.

Proof (blueprint Steps 1–6), for each sign `σ = ±1` separately (`singleProbe_sign`):
* Step 1: `θ = σ c_* r`, with `|θ| = c_* r ≤ min(ε₀, ε_c, ε_G) ℓ_j` (`probe_gain`);
* Step 2: the coupling space `(Ω, P, h, h̄, K)` of `Lemma42` for `(j, a, θ)`, and a measurable a.s.
  geodesic `η_σ` of `D_h` (`exists_measurable_geod01`), which is a.s. also a geodesic of `D_{nrm h}`
  (`ae_isGeod01_nrmF`);
* Step 3: the event `𝒢 ∩ {σ B > r}` of the coordinate space has the probability of the Borel event
  `A_σ` of the pair `(η_σ, nrm h)` on the coupling space (`measure_pair_eq_of_geod`);
* Step 4: on that event, `approxGeod_of_euclidErrF_le`, `probe_gain` and `competitor_probe` give
  `(c_*/4) r²/ℓ ≤ ξ|G_θ(h)| + |Z(h̄)| + |Z(h)| + 2ξ sup_{V_j}|K|`, so one of the four terms is
  `≥ κ r²/ℓ`, `κ = c_*/16` (`meas_le_of_four_sq`);
* Step 5: Markov's inequality for the squares, with `E G_θ² ≤ C_G |θ|`
  (`lintegral_sq_measPairing_sub`, `energy_pushforward_probe`),
  `E Z² ≤ C_Z ξ² (m + ξ^{99/100} L)` on every realization (`residualVariance_field`) and
  `E sup K² ≤ (C_K (|θ|/ℓ)(1 + log(1/ℓ)))²` (clause of `Lemma42`), with `1 + log(1/ℓ) ≤ 2L`
  (`log_inv_ell_le`);
* Step 6: `{|B| > r} = {B > r} ∪ {−B > r}` (`singleProbe`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## Markov's inequality for squares -/

/-- **Markov's inequality for a scaled square.** If `∫⁻ X² ≤ B` and `t > 0`, then
`P{t ≤ c |X|} ≤ c² B / t²`. -/
theorem meas_le_mul_abs_of_lintegral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) {c t B : ℝ} (ht : 0 < t)
    (hB : ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P ≤ ENNReal.ofReal B) :
    P {ω | t ≤ c * |X ω|} ≤ ENNReal.ofReal (c ^ 2 * B / t ^ 2) := by
  have ht2 : 0 < t ^ 2 := by positivity
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (X ω ^ 2) with hf_def
  have hf : AEMeasurable f P := ((hX.pow_const 2).ennreal_ofReal).const_mul _
  have hsub : {ω | t ≤ c * |X ω|} ⊆ {ω | ENNReal.ofReal (t ^ 2) ≤ f ω} := by
    intro ω (hω : t ≤ c * |X ω|)
    show ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (X ω ^ 2)
    rw [← ENNReal.ofReal_mul (sq_nonneg c)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc t ^ 2 ≤ (c * |X ω|) ^ 2 := pow_le_pow_left₀ ht.le hω 2
      _ = c ^ 2 * X ω ^ 2 := by rw [mul_pow, sq_abs]
  have hmk := mul_meas_ge_le_lintegral₀ hf (ENNReal.ofReal (t ^ 2))
  have hint : ∫⁻ ω, f ω ∂P ≤ ENNReal.ofReal (c ^ 2 * B) := by
    rw [hf_def, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (sq_nonneg c)]
    gcongr
  rw [ENNReal.ofReal_div_of_pos ht2, ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.2 ht2).ne') (Or.inl ENNReal.ofReal_ne_top)]
  calc P {ω | t ≤ c * |X ω|} * ENNReal.ofReal (t ^ 2)
      = ENNReal.ofReal (t ^ 2) * P {ω | t ≤ c * |X ω|} := mul_comm _ _
    _ ≤ ENNReal.ofReal (t ^ 2) * P {ω | ENNReal.ofReal (t ^ 2) ≤ f ω} := by
        gcongr
    _ ≤ ∫⁻ ω, f ω ∂P := hmk
    _ ≤ ENNReal.ofReal (c ^ 2 * B) := hint

/-- **One of four terms is large** (blueprint `prop:single-probe`, Steps 4–5): if, almost surely on
`E`, `4t ≤ Σᵢ cᵢ |Xᵢ|`, then `P(E) ≤ Σᵢ P{t ≤ cᵢ |Xᵢ|} ≤ Σᵢ cᵢ² Bᵢ / t²`, where `∫⁻ Xᵢ² ≤ Bᵢ`. -/
theorem meas_le_of_four_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Set Ω}
    {X₁ X₂ X₃ X₄ : Ω → ℝ} {c₁ c₂ c₃ c₄ t B₁ B₂ B₃ B₄ : ℝ}
    (hX₁ : AEMeasurable X₁ P) (hX₂ : AEMeasurable X₂ P) (hX₃ : AEMeasurable X₃ P)
    (hX₄ : AEMeasurable X₄ P) (ht : 0 < t)
    (hB₁ : ∫⁻ ω, ENNReal.ofReal (X₁ ω ^ 2) ∂P ≤ ENNReal.ofReal B₁)
    (hB₂ : ∫⁻ ω, ENNReal.ofReal (X₂ ω ^ 2) ∂P ≤ ENNReal.ofReal B₂)
    (hB₃ : ∫⁻ ω, ENNReal.ofReal (X₃ ω ^ 2) ∂P ≤ ENNReal.ofReal B₃)
    (hB₄ : ∫⁻ ω, ENNReal.ofReal (X₄ ω ^ 2) ∂P ≤ ENNReal.ofReal B₄)
    (hE : ∀ᵐ ω ∂P, ω ∈ E →
      4 * t ≤ c₁ * |X₁ ω| + c₂ * |X₂ ω| + c₃ * |X₃ ω| + c₄ * |X₄ ω|) :
    P E ≤ ENNReal.ofReal (c₁ ^ 2 * B₁ / t ^ 2) + ENNReal.ofReal (c₂ ^ 2 * B₂ / t ^ 2) +
      ENNReal.ofReal (c₃ ^ 2 * B₃ / t ^ 2) + ENNReal.ofReal (c₄ ^ 2 * B₄ / t ^ 2) := by
  set S₁ : Set Ω := {ω | t ≤ c₁ * |X₁ ω|}
  set S₂ : Set Ω := {ω | t ≤ c₂ * |X₂ ω|}
  set S₃ : Set Ω := {ω | t ≤ c₃ * |X₃ ω|}
  set S₄ : Set Ω := {ω | t ≤ c₄ * |X₄ ω|}
  have hsub : E ≤ᵐ[P] (S₁ ∪ S₂ ∪ S₃ ∪ S₄ : Set Ω) := by
    filter_upwards [hE] with ω hω hωE
    have h4 := hω hωE
    by_contra hcon
    simp only [S₁, S₂, S₃, S₄, mem_union, mem_ofPred_eq, not_or, not_le] at hcon
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4'⟩ := hcon
    linarith
  calc P E ≤ P (S₁ ∪ S₂ ∪ S₃ ∪ S₄) := measure_mono_ae hsub
    _ ≤ P S₁ + P S₂ + P S₃ + P S₄ := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ _ := by
        gcongr
        · exact meas_le_mul_abs_of_lintegral_sq hX₁ ht hB₁
        · exact meas_le_mul_abs_of_lintegral_sq hX₂ ht hB₂
        · exact meas_le_mul_abs_of_lintegral_sq hX₃ ht hB₃
        · exact meas_le_mul_abs_of_lintegral_sq hX₄ ht hB₄

/-! ## The single-probe bound for one sign -/

/-- **Proposition `prop:single-probe`, one sign** (blueprint Steps 1–5): for `σ = ±1`,
`P[𝒢 ∩ {σ B_{j,a}(y_η) > r}] ≤ C₁ ξ²ℓ²/r³ + C₂ ξ²(m + ξ^{99/100} L)ℓ²/r⁴ + C₃ ξ²L²/r²`, with
`C₁ = C_G c_*/κ²`, `C₂ = 2 C_Z⁺/κ²`, `C₃ = 16 C_K² c_*²/κ²` and `κ = c_*/16`. -/
theorem singleProbe_sign (G : GSetup) (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ))
    (h42 : Lemma42) : ∃ C₁ C₂ C₃ γ₁ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 < γ₁ ∧
    ∀ γ ∈ Ioc (0:ℝ) γ₁, ∀ η : Coord → C(unitInterval, ℂ), Measurable η →
    (∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) →
    ∀ R, dlt γ ≤ R → R ≤ 2 * xiGamma γ ^ (99/200 : ℝ) → ∀ j ≤ Jg γ, ∀ a ∈ Icc (0:ℝ) 1,
    ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      stdP {ω | goodEv G γ ω ∧ cBeta * R * ell j ^ (1/8 : ℝ) < σ * band (yPath (η ω)) j a} ≤
        ENNReal.ofReal (C₁ * (xiGamma γ ^ 2 * ell j ^ 2 / (cBeta * R * ell j ^ (1/8:ℝ)) ^ 3) +
          C₂ * (xiGamma γ ^ 2 * ((∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99/100:ℝ) * Lg γ) *
            ell j ^ 2 / (cBeta * R * ell j ^ (1/8:ℝ)) ^ 4) +
          C₃ * (xiGamma γ ^ 2 * Lg γ ^ 2 / (cBeta * R * ell j ^ (1/8:ℝ)) ^ 2)) := by
  -- Step 1: constants
  obtain ⟨cs, hcs, hgain⟩ := probe_gain
  obtain ⟨ε₀, CK, hε₀, -, h42f⟩ := h42
  obtain ⟨εc, hεc, hcomp⟩ := competitor_probe
  obtain ⟨εG, CG, hεG, hCG, hen⟩ := energy_pushforward_probe
  obtain ⟨γZ, CZ, hγZ, hres⟩ := residualVariance_field G
  obtain ⟨γg, hγg, -, hgood⟩ := approxGeod_of_good G
  obtain ⟨γ₀, hγ₀, -, hξ⟩ := exists_xiGamma_pos_le
  obtain ⟨γs, hγs, -, hgs⟩ := hgain (min ε₀ (min εc εG)) (lt_min hε₀ (lt_min hεc hεG))
  set κ : ℝ := cs / 16 with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨CG * cs / κ ^ 2, 2 * max CZ 0 / κ ^ 2, 16 * CK ^ 2 * cs ^ 2 / κ ^ 2,
    min (min γs γZ) (min (min γg γ₀) (1 / 10)), by positivity,
    div_nonneg (mul_nonneg zero_le_two (le_max_right _ _)) (sq_nonneg _), by positivity,
    lt_min (lt_min hγs hγZ) (lt_min (lt_min hγg hγ₀) (by norm_num)), ?_⟩
  intro γ hγ η hηm hη R hR1 hR2 j hj a ha σ hσ
  have hγ0 : 0 < γ := hγ.1
  have hγs' : γ ≤ γs := hγ.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγZ' : γ ≤ γZ := hγ.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγg' : γ ≤ γg :=
    hγ.2.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hγ₀' : γ ≤ γ₀ :=
    hγ.2.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hγ10 : γ ≤ 1 / 10 := hγ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγ2 : γ < 2 := by linarith
  obtain ⟨hξ0, hξγ⟩ := hξ γ ⟨hγ0, hγ₀'⟩
  have hxa : xiGamma γ ^ (99 / 100 : ℝ) ≤ 1 / 100 := (hgood γ ⟨hγ0, hγg'⟩).1
  obtain ⟨-, hlogℓ⟩ := log_inv_ell_le hξ0 (hξγ.trans hγ10) hj
  have hDs : IsStrongLQGMetric γ (G.Dfam γ) := (G.hD γ hγ0 hγ2).1
  obtain ⟨-, -, hgj⟩ := hgs γ ⟨hγ0, hγs'⟩
  obtain ⟨hcsr, hdet⟩ := hgj j hj a ha R hR1 hR2 σ hσ
  -- the probe amplitude `r` and the probe parameter `θ = σ c_* r`
  set r : ℝ := cBeta * R * ell j ^ (1 / 8 : ℝ) with hr_def
  have hℓ : 0 < ell j := ell_pos j
  have hδ : 0 < dlt γ := Real.rpow_pos_of_pos hξ0 _
  have hr : 0 < r :=
    mul_pos (mul_pos cBeta_pos (hδ.trans_le hR1)) (Real.rpow_pos_of_pos hℓ _)
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hθabs : |σ * cs * r| = cs * r := by
    rw [abs_mul, abs_mul, hσabs, abs_of_pos hcs, abs_of_pos hr, one_mul]
  have hθne : σ * cs * r ≠ 0 := by
    intro h0
    have h1 := congrArg abs h0
    rw [hθabs, abs_zero] at h1
    exact (mul_pos hcs hr).ne' h1
  have hθε : |σ * cs * r| ≤ min ε₀ (min εc εG) * ell j := by rw [hθabs]; exact hcsr
  have hθ0 : |σ * cs * r| ≤ ε₀ * ell j :=
    hθε.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hℓ.le)
  have hθc : |σ * cs * r| ≤ εc * ell j :=
    hθε.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hℓ.le)
  have hθG : |σ * cs * r| ≤ εG * ell j :=
    hθε.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hℓ.le)
  -- Step 2: the coupling space of Lemma 4.2′ and a measurable geodesic on it
  obtain ⟨Ω, mΩ, P, hP, h, hbar, K, hh, hhb, hKm, hKh, -, hcoup, hSm, hS2, hb5⟩ :=
    h42f j a (σ * cs * r) ha hθ0
  obtain ⟨hμ1, hμreg, hEn⟩ := hen j a (σ * cs * r) hθne hθG
  obtain ⟨ησ, -, hησ⟩ := exists_measurable_geod01 hγ0 hγ2 hDs P h hh 0 1
  have hησn := ae_isGeod01_nrmF hDs hh hησ
  have hcω := hcomp hγ0 hγ2 hDs (hCC γ hγ0 hγ2) j a (σ * cs * r) ha hθc P h hbar K hh hhb hKm hKh
    hcoup hb5 ησ hησ (G.S.b γ)
  -- Step 3: transfer to the coupling space
  have hA : MeasurableSet {p : C(unitInterval, ℂ) × DistC |
      euclidErrF (G.S.b γ) 8 (G.Dfam γ p.2) ≤ ENNReal.ofReal (xiGamma γ ^ (99/100:ℝ)) ∧
        p.1 ∈ {η' : C(unitInterval, ℂ) | r < σ * band (yPath η') j a}} :=
    measurableSet_good_pair hDs.measurable _ _ _
      (measurableSet_lt measurable_const ((measurable_band_yPath j a).const_mul σ))
  have hset : {ω | goodEv G γ ω ∧ r < σ * band (yPath (η ω)) j a} =
      {ω | (η ω, G.h₀ ω) ∈ {p : C(unitInterval, ℂ) × DistC |
        euclidErrF (G.S.b γ) 8 (G.Dfam γ p.2) ≤ ENNReal.ofReal (xiGamma γ ^ (99/100:ℝ)) ∧
          p.1 ∈ {η' : C(unitInterval, ℂ) | r < σ * band (yPath η') j a}}} := by
    ext ω
    simp only [mem_ofPred_eq, goodEv, euclidErr_eq_euclidErrF, (G.compat γ ⟨hγ0, hγ2⟩).2 ω]
  rw [hset, measure_pair_eq_of_geod hγ0 hγ2 hDs G.normalized (isNormalizedWPGFF_nrmF hh) hη hησn hA]
  -- Steps 4–5: one of four terms is at least `t = κ r²/ℓ`, and Markov's inequality for each
  set t : ℝ := κ * r ^ 2 / ell j with ht_def
  have ht : 0 < t := by positivity
  have hseg : IsRegular (segMeasure (0:ℂ) 1) := isRegular_segMeasure (zero_ne_one (α := ℂ))
  have hmG : AEMeasurable (fun ω => probePair j a (σ * cs * r) (h ω)) P :=
    (((measurable_measPairing _).comp hh.measurable).sub
      ((measurable_measPairing _).comp hh.measurable)).aemeasurable
  have hmZb : AEMeasurable (fun ω => Zf γ (G.S.b γ) (G.Dfam γ) (hbar ω)) P :=
    ((measurable_Zf (G.hD γ hγ0 hγ2)).comp hhb.measurable).aemeasurable
  have hmZ : AEMeasurable (fun ω => Zf γ (G.S.b γ) (G.Dfam γ) (h ω)) P :=
    ((measurable_Zf (G.hD γ hγ0 hγ2)).comp hh.measurable).aemeasurable
  have hBG : ∫⁻ ω, ENNReal.ofReal (probePair j a (σ * cs * r) (h ω) ^ 2) ∂P ≤
      ENNReal.ofReal (CG * |σ * cs * r|) := by
    have e := lintegral_sq_measPairing_sub hh hμreg hseg
    simp only [probePair]
    rw [e]
    exact ENNReal.ofReal_le_ofReal hEn
  obtain ⟨-, hZ⟩ := hres γ ⟨hγ0, hγZ'⟩ η hηm hη
  refine (meas_le_of_four_sq (c₁ := xiGamma γ) (c₂ := 1) (c₃ := 1) (c₄ := 2 * xiGamma γ)
    hmG hmZb hmZ hSm.aemeasurable ht hBG (hZ P hbar hhb) (hZ P h hh) hS2 ?_).trans ?_
  · -- Step 4: the gain on the coupling space
    filter_upwards [hησn, hcω] with ω hgeo hcmp hωE
    obtain ⟨hgE, hgB⟩ := hωE
    obtain ⟨hAp, hΔ, -⟩ :=
      approxGeod_of_euclidErrF_le hgE (Real.rpow_nonneg hξ0.le _) hxa hgeo
    obtain ⟨hloc, hlog⟩ := hdet _ _ _ hAp hΔ hgB
    have key := hcmp hloc
    have e4 : 4 * t = cs / 4 * r ^ 2 / ell j := by rw [ht_def, hκ]; ring
    have elog : -(cs / 4) * r ^ 2 / ell j = -(cs / 4 * r ^ 2 / ell j) := by ring
    have h1 : -(xiGamma γ * probePair j a (σ * cs * r) (h ω)) ≤
        xiGamma γ * |probePair j a (σ * cs * r) (h ω)| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) hξ0.le
    have h2 := neg_le_abs (Zf γ (G.S.b γ) (G.Dfam γ) (hbar ω))
    have h3 := le_abs_self (Zf γ (G.S.b γ) (G.Dfam γ) (h ω))
    have h4 : 2 * xiGamma γ * ⨆ w ∈ probeRectV j, |K ω w| ≤
        2 * xiGamma γ * |(⨆ w ∈ probeRectV j, |K ω w|)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    linarith
  · -- the constants
    have hm0 : 0 ≤ ∫ ω, maxDev (η ω) ∂stdP := integral_nonneg fun ω => maxDev_nonneg _
    have hL0 : 0 ≤ Lg γ := Real.log_nonneg ((one_le_inv₀ hξ0).2 (by linarith))
    set X : ℝ := (∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99/100:ℝ) * Lg γ with hX
    have hX0 : 0 ≤ X := add_nonneg hm0 (mul_nonneg (Real.rpow_nonneg hξ0.le _) hL0)
    have hlog0 : 0 ≤ 1 + Real.log (ell j)⁻¹ := by
      have := Real.log_nonneg ((one_le_inv₀ hℓ).2 (ell_le_one j))
      linarith
    have e1 : xiGamma γ ^ 2 * (CG * |σ * cs * r|) / t ^ 2 =
        CG * cs / κ ^ 2 * (xiGamma γ ^ 2 * ell j ^ 2 / r ^ 3) := by
      rw [hθabs, ht_def]
      field_simp
    have e2 : 1 ^ 2 * (CZ * xiGamma γ ^ 2 * X) / t ^ 2 ≤
        max CZ 0 / κ ^ 2 * (xiGamma γ ^ 2 * X * ell j ^ 2 / r ^ 4) := by
      have e : 1 ^ 2 * (CZ * xiGamma γ ^ 2 * X) / t ^ 2 =
          CZ / κ ^ 2 * (xiGamma γ ^ 2 * X * ell j ^ 2 / r ^ 4) := by
        rw [ht_def]
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) (by positivity)
    have e3 : (2 * xiGamma γ) ^ 2 *
        (CK * (|σ * cs * r| / ell j) * (1 + Real.log (1 / ell j))) ^ 2 / t ^ 2 ≤
        16 * CK ^ 2 * cs ^ 2 / κ ^ 2 * (xiGamma γ ^ 2 * Lg γ ^ 2 / r ^ 2) := by
      have hlog2 : (1 + Real.log (ell j)⁻¹) ^ 2 ≤ (2 * Lg γ) ^ 2 :=
        pow_le_pow_left₀ hlog0 hlogℓ 2
      have eL : (2 * xiGamma γ) ^ 2 *
          (CK * (|σ * cs * r| / ell j) * (1 + Real.log (1 / ell j))) ^ 2 / t ^ 2 =
          4 * CK ^ 2 * cs ^ 2 / κ ^ 2 * (xiGamma γ ^ 2 / r ^ 2) *
            (1 + Real.log (ell j)⁻¹) ^ 2 := by
        rw [hθabs, ht_def, one_div (ell j)]
        field_simp
        ring
      have eR : 16 * CK ^ 2 * cs ^ 2 / κ ^ 2 * (xiGamma γ ^ 2 * Lg γ ^ 2 / r ^ 2) =
          4 * CK ^ 2 * cs ^ 2 / κ ^ 2 * (xiGamma γ ^ 2 / r ^ 2) * (2 * Lg γ) ^ 2 := by
        ring
      rw [eL, eR]
      exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
    have hT1 : 0 ≤ CG * cs / κ ^ 2 * (xiGamma γ ^ 2 * ell j ^ 2 / r ^ 3) := by positivity
    have hT2 : 0 ≤ max CZ 0 / κ ^ 2 * (xiGamma γ ^ 2 * X * ell j ^ 2 / r ^ 4) :=
      mul_nonneg (div_nonneg (le_max_right _ _) (sq_nonneg _)) (by positivity)
    have hT3 : 0 ≤ 16 * CK ^ 2 * cs ^ 2 / κ ^ 2 * (xiGamma γ ^ 2 * Lg γ ^ 2 / r ^ 2) := by
      positivity
    calc _ ≤ ENNReal.ofReal (CG * cs / κ ^ 2 * (xiGamma γ ^ 2 * ell j ^ 2 / r ^ 3)) +
          ENNReal.ofReal (max CZ 0 / κ ^ 2 * (xiGamma γ ^ 2 * X * ell j ^ 2 / r ^ 4)) +
          ENNReal.ofReal (max CZ 0 / κ ^ 2 * (xiGamma γ ^ 2 * X * ell j ^ 2 / r ^ 4)) +
          ENNReal.ofReal (16 * CK ^ 2 * cs ^ 2 / κ ^ 2 * (xiGamma γ ^ 2 * Lg γ ^ 2 / r ^ 2)) := by
          rw [e1]
          refine add_le_add (add_le_add (add_le_add le_rfl ?_) ?_) ?_
          · exact ENNReal.ofReal_le_ofReal e2
          · exact ENNReal.ofReal_le_ofReal e2
          · exact ENNReal.ofReal_le_ofReal e3
      _ = ENNReal.ofReal (CG * cs / κ ^ 2 * (xiGamma γ ^ 2 * ell j ^ 2 / r ^ 3) +
          max CZ 0 / κ ^ 2 * (xiGamma γ ^ 2 * X * ell j ^ 2 / r ^ 4) +
          max CZ 0 / κ ^ 2 * (xiGamma γ ^ 2 * X * ell j ^ 2 / r ^ 4) +
          16 * CK ^ 2 * cs ^ 2 / κ ^ 2 * (xiGamma γ ^ 2 * Lg γ ^ 2 / r ^ 2)) := by
          rw [ENNReal.ofReal_add (by positivity) hT3, ENNReal.ofReal_add (by positivity) hT2,
            ENNReal.ofReal_add hT1 hT2]
      _ = _ := by
          congr 1
          ring

/-! ## The single-probe bound -/

/-- **Proposition `prop:single-probe`** (source (5.10); BP2 detail D9): for `γ` small, every
measurable a.s. geodesic `η`, `δ ≤ R ≤ 2ξ^{99/200}`, `j ≤ J_γ`, `a ∈ [0,1]` and
`r = c_β R ℓ_j^{1/8}`,
`P[𝒢 ∩ {|B_{j,a}(y_η)| > r}] ≤ C (ξ² ℓ²/r³ + ξ² (m + ξ^{99/100} L) ℓ²/r⁴ + ξ² L²/r²)`.
The two signs live on different coupling spaces and are combined only here (Step 6). -/
theorem singleProbe (G : GSetup) (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ))
    (h42 : Lemma42) : ∃ C γ₁, 0 < γ₁ ∧ ∀ γ ∈ Ioc (0:ℝ) γ₁,
    ∀ η : Coord → C(unitInterval, ℂ), Measurable η →
    (∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) →
    ∀ R, dlt γ ≤ R → R ≤ 2 * xiGamma γ ^ (99/200 : ℝ) → ∀ j ≤ Jg γ, ∀ a ∈ Icc (0:ℝ) 1,
      stdP {ω | goodEv G γ ω ∧ cBeta * R * ell j ^ (1/8 : ℝ) < |band (yPath (η ω)) j a|} ≤
        ENNReal.ofReal (C * (xiGamma γ ^ 2 * ell j ^ 2 / (cBeta * R * ell j ^ (1/8:ℝ)) ^ 3 +
          xiGamma γ ^ 2 * ((∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99/100:ℝ) * Lg γ) *
            ell j ^ 2 / (cBeta * R * ell j ^ (1/8:ℝ)) ^ 4 +
          xiGamma γ ^ 2 * Lg γ ^ 2 / (cBeta * R * ell j ^ (1/8:ℝ)) ^ 2)) := by
  obtain ⟨C₁, C₂, C₃, γ₁, hC₁, hC₂, hC₃, hγ₁, hsign⟩ := singleProbe_sign G hCC h42
  obtain ⟨γ₀, hγ₀, hγ₀1, hξ⟩ := exists_xiGamma_pos_le
  refine ⟨2 * (C₁ + C₂ + C₃), min γ₁ γ₀, lt_min hγ₁ hγ₀,
    fun γ hγ η hηm hη R hR1 hR2 j hj a ha => ?_⟩
  have hγ1 : γ ∈ Ioc (0:ℝ) γ₁ := ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩
  obtain ⟨hξ0, hξγ⟩ := hξ γ ⟨hγ.1, hγ.2.trans (min_le_right _ _)⟩
  have hp := hsign γ hγ1 η hηm hη R hR1 hR2 j hj a ha 1 (Or.inl rfl)
  have hn := hsign γ hγ1 η hηm hη R hR1 hR2 j hj a ha (-1) (Or.inr rfl)
  set r : ℝ := cBeta * R * ell j ^ (1 / 8 : ℝ) with hr_def
  have hℓ : 0 < ell j := ell_pos j
  have hr : 0 < r := mul_pos (mul_pos cBeta_pos ((Real.rpow_pos_of_pos hξ0 _).trans_le hR1))
    (Real.rpow_pos_of_pos hℓ _)
  have hm0 : 0 ≤ ∫ ω, maxDev (η ω) ∂stdP := integral_nonneg fun ω => maxDev_nonneg _
  have hL0 : 0 ≤ Lg γ := Real.log_nonneg ((one_le_inv₀ hξ0).2
    (hξγ.trans ((hγ.2.trans (min_le_right _ _)).trans hγ₀1.le)))
  set T₁ : ℝ := xiGamma γ ^ 2 * ell j ^ 2 / r ^ 3 with hT₁
  set T₂ : ℝ := xiGamma γ ^ 2 * ((∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99/100:ℝ) * Lg γ) *
    ell j ^ 2 / r ^ 4 with hT₂
  set T₃ : ℝ := xiGamma γ ^ 2 * Lg γ ^ 2 / r ^ 2 with hT₃
  have hT₁0 : 0 ≤ T₁ := by positivity
  have hT₂0 : 0 ≤ T₂ := by
    have : 0 ≤ (∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99/100:ℝ) * Lg γ :=
      add_nonneg hm0 (mul_nonneg (Real.rpow_nonneg hξ0.le _) hL0)
    positivity
  have hT₃0 : 0 ≤ T₃ := by positivity
  have hS0 : 0 ≤ C₁ * T₁ + C₂ * T₂ + C₃ * T₃ := by positivity
  have hsub : {ω | goodEv G γ ω ∧ r < |band (yPath (η ω)) j a|} ⊆
      {ω | goodEv G γ ω ∧ r < 1 * band (yPath (η ω)) j a} ∪
        {ω | goodEv G γ ω ∧ r < -1 * band (yPath (η ω)) j a} := by
    rintro ω ⟨hg, hb⟩
    rcases lt_abs.1 hb with h | h
    · exact Or.inl ⟨hg, by rwa [one_mul]⟩
    · exact Or.inr ⟨hg, by rwa [neg_one_mul]⟩
  calc stdP {ω | goodEv G γ ω ∧ r < |band (yPath (η ω)) j a|}
      ≤ stdP ({ω | goodEv G γ ω ∧ r < 1 * band (yPath (η ω)) j a} ∪
          {ω | goodEv G γ ω ∧ r < -1 * band (yPath (η ω)) j a}) := measure_mono hsub
    _ ≤ stdP {ω | goodEv G γ ω ∧ r < 1 * band (yPath (η ω)) j a} +
          stdP {ω | goodEv G γ ω ∧ r < -1 * band (yPath (η ω)) j a} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * T₁ + C₂ * T₂ + C₃ * T₃) +
          ENNReal.ofReal (C₁ * T₁ + C₂ * T₂ + C₃ * T₃) := add_le_add hp hn
    _ = ENNReal.ofReal ((C₁ * T₁ + C₂ * T₂ + C₃ * T₃) + (C₁ * T₁ + C₂ * T₂ + C₃ * T₃)) :=
        (ENNReal.ofReal_add hS0 hS0).symm
    _ ≤ ENNReal.ofReal (2 * (C₁ + C₂ + C₃) * (T₁ + T₂ + T₃)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : 2 * (C₁ + C₂ + C₃) * (T₁ + T₂ + T₃) =
            ((C₁ * T₁ + C₂ * T₂ + C₃ * T₃) + (C₁ * T₁ + C₂ * T₂ + C₃ * T₃)) +
              2 * (C₁ * (T₂ + T₃) + C₂ * (T₁ + T₃) + C₃ * (T₁ + T₂)) := by ring
        rw [e]
        have : 0 ≤ C₁ * (T₂ + T₃) + C₂ * (T₁ + T₃) + C₃ * (T₁ + T₂) := by positivity
        linarith
    _ = _ := by rw [mul_assoc]

end SmallGammaGeodesics
