import SmallGammaGeodesics.Upper.Lemma51
import SmallGammaGeodesics.Tight.Band

/-!
# The mean height (5.13)–(5.14) (packet P-U3)

Blueprint `s5-upper.tex`, Proposition `prop:mean` (BP2 detail D11), with the interface hypotheses
`hCC`, `h42` (ruling G10).

`mean_maxDev_le`: `E M(η) ≤ C₆ ξ^{2/3}` for small `γ` and every measurable a.s. geodesic `η`.

Proof. `m = E M(η)` is finite (`residualVariance_field`), and `m = E[M 1_𝒢] + E[M 1_{𝒢ᶜ}]`; the
second term is at most `C_c ξ^{10}` (`lintegral_maxDev_compl_good_le`). By the layer-cake formula
(`setLIntegral_ofReal_le_of_tail`) and the tail on the good event (`tail_good_le`: the right side of
Lemma 5.1 for `δ ≤ t ≤ 2ξ^{99/200}`, and `0` above), with `c = A₀ δ`, `A₀ = C₅⁺ + 1`,
`E[M 1_𝒢] ≤ c + C₅⁺ (ξ²/(2c²) + ξ²(m + ξ^{99/100} L)/(3c³) + ξ^{49/32} L²/c)`
`      ≤ A₀ δ + δ/2 + (m + ξ^{99/100} L)/3 + ξ^{49/32} L²/δ`  (`ξ² = δ³`, `C₅⁺ ≤ A₀ ≤ A₀² ≤ A₀³`).
For small `γ`: `ξ^{99/100} L = ξ^{97/300} L δ ≤ δ`, `ξ^{49/32} L²/δ = ξ^{19/96} L² δ ≤ δ/2` and
`C_c ξ^{10} = C_c ξ^{28/3} δ ≤ δ/2` (`Tight.rpow_mul_log_inv_le`). Absorbing `m/3` (`m < ∞`) gives
`m ≤ (3/2 A₀ + 11/4) δ ≤ (2 A₀ + 3) δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## Layer cake with a power tail -/

/-- `∫⁻_{(c,∞)} ofReal (a t^{-3} + b t^{-4} + e t^{-2}) dt = ofReal (a/(2c²) + b/(3c³) + e/c)` for
`c > 0` and `a, b, e ≥ 0`. -/
theorem lintegral_Ioi_ofReal_three_rpow {c a b e : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 0 ≤ e) :
    ∫⁻ t in Ioi c, ENNReal.ofReal (a * t ^ (-3 : ℝ) + b * t ^ (-4 : ℝ) + e * t ^ (-2 : ℝ)) =
      ENNReal.ofReal (a / (2 * c ^ 2) + b / (3 * c ^ 3) + e / c) := by
  have h3 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hc
  have h4 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hc
  have h2 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc
  have i3 : Integrable (fun t : ℝ => a * t ^ (-3 : ℝ)) (volume.restrict (Ioi c)) := h3.const_mul a
  have i4 : Integrable (fun t : ℝ => b * t ^ (-4 : ℝ)) (volume.restrict (Ioi c)) := h4.const_mul b
  have i2 : Integrable (fun t : ℝ => e * t ^ (-2 : ℝ)) (volume.restrict (Ioi c)) := h2.const_mul e
  have i34 : Integrable (fun t : ℝ => a * t ^ (-3 : ℝ) + b * t ^ (-4 : ℝ))
      (volume.restrict (Ioi c)) := i3.add i4
  have hint : IntegrableOn
      (fun t : ℝ => a * t ^ (-3 : ℝ) + b * t ^ (-4 : ℝ) + e * t ^ (-2 : ℝ)) (Ioi c) :=
    i34.add i2
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi c)]
      fun t : ℝ => a * t ^ (-3 : ℝ) + b * t ^ (-4 : ℝ) + e * t ^ (-2 : ℝ) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      have ht0 : 0 ≤ t := hc.le.trans (le_of_lt ht)
      have := Real.rpow_nonneg ht0 (-3 : ℝ)
      have := Real.rpow_nonneg ht0 (-4 : ℝ)
      have := Real.rpow_nonneg ht0 (-2 : ℝ)
      show 0 ≤ a * t ^ (-3 : ℝ) + b * t ^ (-4 : ℝ) + e * t ^ (-2 : ℝ)
      positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_add i34 i2, integral_add i3 i4,
    integral_const_mul, integral_const_mul,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hc,
    integral_Ioi_rpow_of_lt (by norm_num) hc, integral_Ioi_rpow_of_lt (by norm_num) hc]
  congr 1
  have e2 : c ^ ((-3 : ℝ) + 1) = (c ^ 2)⁻¹ := by
    rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hc.le, Real.rpow_ofNat]
  have e3 : c ^ ((-4 : ℝ) + 1) = (c ^ 3)⁻¹ := by
    rw [show (-4 : ℝ) + 1 = -3 by norm_num, Real.rpow_neg hc.le, Real.rpow_ofNat]
  have e1 : c ^ ((-2 : ℝ) + 1) = c⁻¹ := by
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  rw [e1, e2, e3]
  field_simp
  ring

/-- **Layer cake on an event with a power tail.** Let `M ≥ 0` be measurable and `S` an event with
`P(S ∩ {M > t}) ≤ a t^{-3} + b t^{-4} + e t^{-2}` for every `t > c`, where `c > 0` and
`a, b, e ≥ 0`. Then
`∫⁻_S M ≤ c + a/(2c²) + b/(3c³) + e/c`. -/
theorem setLIntegral_ofReal_le_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {M : Ω → ℝ} (hM : Measurable M) (hM0 : ∀ ω, 0 ≤ M ω) {S : Set Ω}
    {c a b e : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (htail : ∀ t, c < t →
      P (S ∩ {ω | t < M ω}) ≤
        ENNReal.ofReal (a * t ^ (-3 : ℝ) + b * t ^ (-4 : ℝ) + e * t ^ (-2 : ℝ))) :
    ∫⁻ ω in S, ENNReal.ofReal (M ω) ∂P ≤
      ENNReal.ofReal c + ENNReal.ofReal (a / (2 * c ^ 2) + b / (3 * c ^ 3) + e / c) := by
  rw [lintegral_eq_lintegral_meas_lt (P.restrict S) (ae_of_all _ hM0) hM.aemeasurable,
    ← Ioc_union_Ioi_eq_Ioi hc.le]
  refine (lintegral_union_le _ _ _).trans (add_le_add ?_ ?_)
  · calc ∫⁻ t in Ioc 0 c, (P.restrict S) {ω | t < M ω} ≤ ∫⁻ _ in Ioc (0 : ℝ) c, 1 :=
          lintegral_mono fun t => (Measure.restrict_apply_le _ _).trans prob_le_one
      _ = ENNReal.ofReal c := by rw [setLIntegral_one, Real.volume_Ioc, sub_zero]
  · rw [← lintegral_Ioi_ofReal_three_rpow hc ha hb he]
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hM), inter_comm]
    exact htail t ht

/-! ## The good event is Borel -/

/-- The good event `𝒢_γ` is measurable for `γ ∈ (0,2)`. -/
theorem measurableSet_goodEv (G : GSetup) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    MeasurableSet {ω | goodEv G γ ω} := by
  have e : {ω | goodEv G γ ω} = (fun ω => euclidErrF (G.S.b γ) 8 (G.Dfam γ (G.h₀ ω))) ⁻¹'
      Iic (ENNReal.ofReal (xiGamma γ ^ (99 / 100 : ℝ))) := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_Iic, goodEv, euclidErr_eq_euclidErrF,
      (G.compat γ ⟨hγ, hγ2⟩).2 ω]
  rw [e]
  exact ((measurable_euclidErrF _ _).comp ((G.hD γ hγ hγ2).1.measurable.comp G.measurable_h₀))
    measurableSet_Iic

/-! ## The mean height -/

/-- **Proposition `prop:mean`** (source (5.13)–(5.14); BP2 detail D11): `E M(η) ≤ C₆ ξ^{2/3}` for
small `γ` and every measurable a.s. geodesic `η`. -/
theorem mean_maxDev_le (G : GSetup) (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ))
    (h42 : Lemma42) : ∃ C γ₁, 0 < γ₁ ∧ ∀ γ ∈ Ioc (0:ℝ) γ₁,
    ∀ η : Coord → C(unitInterval, ℂ), Measurable η →
    (∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) →
    ∫⁻ ω, ENNReal.ofReal (maxDev (η ω)) ∂stdP ≤ ENNReal.ofReal (C * dlt γ) := by
  obtain ⟨C₅, γ₅, hγ₅, htail⟩ := tail_good_le G hCC h42
  obtain ⟨γc, Cc, hγc, hcompl⟩ := lintegral_maxDev_compl_good_le G
  obtain ⟨γZ, CZ, hγZ, hres⟩ := residualVariance_field G
  obtain ⟨γ₀, hγ₀, hγ₀1, hξ⟩ := exists_xiGamma_pos_le
  set B : ℝ := max C₅ 0 with hB
  have hB0 : 0 ≤ B := le_max_right _ _
  set A₀ : ℝ := B + 1 with hA₀
  have hA₀1 : 1 ≤ A₀ := by linarith
  set Cc' : ℝ := max Cc 0 with hCc'
  have hCc'0 : 0 ≤ Cc' := le_max_right _ _
  have hmin : 0 < min (min γ₅ γc) (min γZ γ₀) := lt_min (lt_min hγ₅ hγc) (lt_min hγZ hγ₀)
  -- the thresholds, as `γ → 0⁺`
  have hev : ∀ᶠ γ in 𝓝[>] (0:ℝ), γ ∈ Ioo 0 (min (min γ₅ γc) (min γZ γ₀)) ∧
      600 / 97 * γ ^ (97 / 600 : ℝ) < 1 ∧ 2 * (384 / 19) ^ 2 * γ ^ (19 / 192 : ℝ) < 1 ∧
      2 * Cc' * γ ^ (28 / 3 : ℝ) < 1 := by
    filter_upwards [Tight.eventually_mem_Ioo_zero hmin,
      Tight.eventually_mul_rpow_lt (600 / 97) (q := 97 / 600) (by norm_num) one_pos,
      Tight.eventually_mul_rpow_lt (2 * (384 / 19) ^ 2) (q := 19 / 192) (by norm_num) one_pos,
      Tight.eventually_mul_rpow_lt (2 * Cc') (q := 28 / 3) (by norm_num) one_pos]
      with γ h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : 0 < u := hu
  refine ⟨2 * A₀ + 3, u / 2, by positivity, fun γ hγ η hηm hη => ?_⟩
  obtain ⟨hγI, hE2, hE3, hE4⟩ := hsub ⟨hγ.1, by linarith [hγ.2]⟩
  have hγ0 : 0 < γ := hγ.1
  have hγmin : γ < min (min γ₅ γc) (min γZ γ₀) := hγI.2
  have hγ5 : γ ∈ Ioc (0:ℝ) γ₅ :=
    ⟨hγ0, (hγmin.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le⟩
  have hγc' : γ ∈ Ioc (0:ℝ) γc :=
    ⟨hγ0, (hγmin.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le⟩
  have hγZ' : γ ∈ Ioc (0:ℝ) γZ :=
    ⟨hγ0, (hγmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le⟩
  have hγ₀' : γ ∈ Ioc (0:ℝ) γ₀ :=
    ⟨hγ0, (hγmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le⟩
  have hγ1 : γ ≤ 1 := hγ₀'.2.trans hγ₀1.le
  have hγ2 : γ < 2 := by linarith
  obtain ⟨hξ0, hξγ⟩ := hξ γ hγ₀'
  have hξ1 : xiGamma γ ≤ 1 := hξγ.trans hγ1
  obtain ⟨hint, -⟩ := hres γ hγZ' η hηm hη
  obtain ⟨hT1, hT2⟩ := htail γ hγ5 η hηm hη
  have hbad := hcompl γ hγc' η hηm hη
  have hGm := measurableSet_goodEv G hγ0 hγ2
  -- notation
  set ξ : ℝ := xiGamma γ with hξdef
  set δ : ℝ := dlt γ with hδdef
  have hδeq : δ = ξ ^ (2 / 3 : ℝ) := rfl
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hξ0 _
  have hξ2 : ξ ^ 2 = δ ^ 3 := by rw [hδeq, Tight.rpow_two_thirds_pow_three hξ0.le]
  set L : ℝ := Lg γ with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ hξ0).2 hξ1)
  set m : ℝ := ∫ ω, maxDev (η ω) ∂stdP with hmdef
  have hm0 : 0 ≤ m := integral_nonneg fun ω => maxDev_nonneg _
  have hmeq : ∫⁻ ω, ENNReal.ofReal (maxDev (η ω)) ∂stdP = ENNReal.ofReal m :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => maxDev_nonneg _)).symm
  set X : ℝ := m + ξ ^ (99 / 100 : ℝ) * L with hX
  have hX0 : 0 ≤ X := add_nonneg hm0 (mul_nonneg (Real.rpow_nonneg hξ0.le _) hL0)
  set E : ℝ := ξ ^ (49 / 32 : ℝ) * L ^ 2 with hE
  have hE0 : 0 ≤ E := mul_nonneg (Real.rpow_nonneg hξ0.le _) (sq_nonneg _)
  set c : ℝ := A₀ * δ with hc
  have hc0 : 0 < c := by positivity
  have hδc : δ ≤ c := le_mul_of_one_le_left hδ0.le hA₀1
  -- the layer cake on `𝒢`
  have hgood : ∫⁻ ω in {ω | goodEv G γ ω}, ENNReal.ofReal (maxDev (η ω)) ∂stdP ≤
      ENNReal.ofReal c + ENNReal.ofReal (B * ξ ^ 2 / (2 * c ^ 2) + B * (ξ ^ 2 * X) / (3 * c ^ 3) +
        B * E / c) := by
    refine setLIntegral_ofReal_le_of_tail (measurable_maxDev_comp hηm) (fun ω => maxDev_nonneg _)
      hc0 (by positivity) (by positivity) (by positivity) fun t ht => ?_
    have ht0 : 0 < t := hc0.trans ht
    have hδt : δ ≤ t := hδc.trans ht.le
    show stdP {ω | goodEv G γ ω ∧ t < maxDev (η ω)} ≤ _
    rcases le_or_gt t (2 * ξ ^ (99 / 200 : ℝ)) with hts | hts
    · refine (hT1 t hδt hts).trans (ENNReal.ofReal_le_ofReal ?_)
      have e3 : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by rw [Real.rpow_neg ht0.le, Real.rpow_ofNat]
      have e4 : t ^ (-4 : ℝ) = (t ^ 4)⁻¹ := by rw [Real.rpow_neg ht0.le, Real.rpow_ofNat]
      have e2 : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by rw [Real.rpow_neg ht0.le, Real.rpow_ofNat]
      rw [e3, e4, e2]
      have hnn : 0 ≤ ξ ^ 2 / t ^ 3 + ξ ^ 2 * X / t ^ 4 + E / t ^ 2 := by positivity
      calc C₅ * (ξ ^ 2 / t ^ 3 + ξ ^ 2 * X / t ^ 4 + E / t ^ 2)
          ≤ B * (ξ ^ 2 / t ^ 3 + ξ ^ 2 * X / t ^ 4 + E / t ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
        _ = B * ξ ^ 2 * (t ^ 3)⁻¹ + B * (ξ ^ 2 * X) * (t ^ 4)⁻¹ + B * E * (t ^ 2)⁻¹ := by ring
    · rw [hT2 t hts.le]
      exact zero_le
  -- the total mean
  set Y : ℝ := B * ξ ^ 2 / (2 * c ^ 2) + B * (ξ ^ 2 * X) / (3 * c ^ 3) + B * E / c with hY
  have hY0 : 0 ≤ Y := by positivity
  have hξ10 : 0 ≤ Cc' * ξ ^ 10 := by positivity
  have htot : ENNReal.ofReal m ≤
      ENNReal.ofReal c + ENNReal.ofReal Y + ENNReal.ofReal (Cc' * ξ ^ 10) := by
    rw [← hmeq, ← lintegral_add_compl _ hGm]
    refine add_le_add hgood ((hbad : _).trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  rw [← ENNReal.ofReal_add hc0.le hY0, ← ENNReal.ofReal_add (by positivity) hξ10,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at htot
  -- the small terms
  obtain ⟨hr1, hr2⟩ := Tight.rpow_mul_log_inv_le hξ0 hξ1
  have k5 : ξ ^ (99 / 100 : ℝ) * L ≤ δ := by
    have e : ξ ^ (99 / 100 : ℝ) * L = ξ ^ (97 / 300 : ℝ) * L * δ := by
      rw [hδeq, mul_right_comm, ← Real.rpow_add hξ0]
      norm_num
    have g1 : ξ ^ (97 / 600 : ℝ) ≤ γ ^ (97 / 600 : ℝ) :=
      Real.rpow_le_rpow hξ0.le hξγ (by norm_num)
    have h1 : ξ ^ (97 / 300 : ℝ) * L ≤ 1 := by
      calc ξ ^ (97 / 300 : ℝ) * L ≤ 600 / 97 * ξ ^ (97 / 600 : ℝ) := hr1
        _ ≤ 600 / 97 * γ ^ (97 / 600 : ℝ) := by gcongr
        _ ≤ 1 := hE2.le
    rw [e]
    calc ξ ^ (97 / 300 : ℝ) * L * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right h1 hδ0.le
      _ = δ := one_mul δ
  have k3 : E / δ ≤ δ / 2 := by
    have e : E / δ = ξ ^ (19 / 96 : ℝ) * L ^ 2 * δ := by
      rw [hE, hδeq]
      have hd : (0 : ℝ) < ξ ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hξ0 _
      rw [div_eq_iff hd.ne']
      have e' : ξ ^ (49 / 32 : ℝ) = ξ ^ (19 / 96 : ℝ) * ξ ^ (2 / 3 : ℝ) * ξ ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add hξ0, ← Real.rpow_add hξ0]
        norm_num
      rw [e']
      ring
    have g2 : ξ ^ (19 / 192 : ℝ) ≤ γ ^ (19 / 192 : ℝ) :=
      Real.rpow_le_rpow hξ0.le hξγ (by norm_num)
    have hr2' : ξ ^ (19 / 96 : ℝ) * L ^ 2 ≤ (384 / 19) ^ 2 * ξ ^ (19 / 192 : ℝ) := hr2
    have g2' : (384 / 19 : ℝ) ^ 2 * ξ ^ (19 / 192 : ℝ) ≤ (384 / 19) ^ 2 * γ ^ (19 / 192 : ℝ) :=
      mul_le_mul_of_nonneg_left g2 (by positivity)
    have h2' : ξ ^ (19 / 96 : ℝ) * L ^ 2 ≤ 1 / 2 := by linarith
    rw [e]
    calc ξ ^ (19 / 96 : ℝ) * L ^ 2 * δ ≤ 1 / 2 * δ := mul_le_mul_of_nonneg_right h2' hδ0.le
      _ = δ / 2 := by ring
  have k4 : Cc' * ξ ^ 10 ≤ δ / 2 := by
    have e : ξ ^ 10 = ξ ^ (28 / 3 : ℝ) * δ := by
      rw [hδeq, ← Real.rpow_add hξ0, ← Real.rpow_natCast]
      norm_num
    have g3 : ξ ^ (28 / 3 : ℝ) ≤ γ ^ (28 / 3 : ℝ) :=
      Real.rpow_le_rpow hξ0.le hξγ (by norm_num)
    have h3 : 2 * Cc' * ξ ^ (28 / 3 : ℝ) ≤ 1 :=
      (mul_le_mul_of_nonneg_left g3 (by positivity)).trans hE4.le
    have h3' : Cc' * ξ ^ (28 / 3 : ℝ) ≤ 1 / 2 := by linarith
    rw [e]
    calc Cc' * (ξ ^ (28 / 3 : ℝ) * δ) = Cc' * ξ ^ (28 / 3 : ℝ) * δ := by ring
      _ ≤ 1 / 2 * δ := mul_le_mul_of_nonneg_right h3' hδ0.le
      _ = δ / 2 := by ring
  -- the three terms of `Y`
  have hA₀0 : 0 < A₀ := by linarith
  have hA₀B : B ≤ A₀ := by linarith
  have hA₀2 : B ≤ A₀ ^ 2 := hA₀B.trans (le_self_pow₀ hA₀1 two_ne_zero)
  have hA₀3 : B ≤ A₀ ^ 3 := hA₀B.trans (le_self_pow₀ hA₀1 (by norm_num))
  have k1 : B * ξ ^ 2 / (2 * c ^ 2) ≤ δ / 2 := by
    have e : B * ξ ^ 2 / (2 * c ^ 2) = B / A₀ ^ 2 * (δ / 2) := by
      rw [hξ2, hc]
      field_simp
    rw [e]
    calc B / A₀ ^ 2 * (δ / 2) ≤ 1 * (δ / 2) :=
          mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).2 hA₀2) (by positivity)
      _ = δ / 2 := one_mul _
  have k2 : B * (ξ ^ 2 * X) / (3 * c ^ 3) ≤ X / 3 := by
    have e : B * (ξ ^ 2 * X) / (3 * c ^ 3) = B / A₀ ^ 3 * (X / 3) := by
      rw [hξ2, hc]
      field_simp
    rw [e]
    calc B / A₀ ^ 3 * (X / 3) ≤ 1 * (X / 3) :=
          mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).2 hA₀3) (by positivity)
      _ = X / 3 := one_mul _
  have k3' : B * E / c ≤ E / δ := by
    have e : B * E / c = B / A₀ * (E / δ) := by
      rw [hc]
      field_simp
    rw [e]
    calc B / A₀ * (E / δ) ≤ 1 * (E / δ) :=
          mul_le_mul_of_nonneg_right ((div_le_one hA₀0).2 hA₀B) (by positivity)
      _ = E / δ := one_mul _
  -- absorption
  have hfinal : m ≤ (2 * A₀ + 3) * δ := by
    have hXle : X ≤ m + δ := by
      rw [hX]
      linarith
    have hAδ : 0 ≤ A₀ * δ := by positivity
    rw [hY] at htot
    linarith
  rw [hmeq]
  exact ENNReal.ofReal_le_ofReal hfinal

end SmallGammaGeodesics
