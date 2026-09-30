import QuantumZipper.Proofs.GFF.K3.MixedProj

/-!
# Uniform local energy bounds (GFF-K3 node M5, preparation)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M4 step (i), M5 "Lipschitz"/"representation").

* `lintegral_kInvPot_sq_le`: the kernel-composition bound of `lintegral_kInvPot_sq_lt_top` with
  its explicit constant `(A₀ μ(ℂ) + A₁ C) μ(ℂ)`.
* `mixed_local_pairing_bound`: the M4 estimate `|∫ f dμ| ≤ B(μ) E(f)^{1/2}` with the constant
  `B(μ)` explicit in `μ(ℂ)` and the kernel potential of `μ`, and the Poincaré constant chosen
  once for all `μ` carried by `K`.
* `exists_norm_rieszVec_foldedCircle_le`: `sup_{z ∈ K} ‖v_{fold z s}‖ < ∞`.

The proofs are those of `MixedLocal.lean` (Adams–Hedberg, *Function Spaces and Potential
Theory*, eq. (1.2.4) p. 8, §2.3 eq. (2.3.3) p. 24; Gilbarg–Trudinger Lemma 7.16) with the
constants kept explicit.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- The kernel-composition bound with its explicit constant. -/
theorem lintegral_kInvPot_sq_le {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {ρ : ℝ}
    (hρ : 0 < ρ) {C : ℝ≥0∞}
    (hbd : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ ≤ C) :
    ∫⁻ y, (∫⁻ z, kInv ρ (y - z) ∂μ) ^ (2 : ℝ) ≤
      (2 * ENNReal.ofReal (2 * π) * (1 + ENNReal.ofReal (max (Real.log (2 * ρ)) 0)) * μ univ +
        2 * ENNReal.ofReal (2 * π) * C) * μ univ := by
  have hμf := hμ.1
  have := hμf
  have hatom := noAtoms_of_isAdmissibleH hμ
  set A0 := 2 * ENNReal.ofReal (2 * π) * (1 + ENNReal.ofReal (max (Real.log (2 * ρ)) 0)) with hA0
  set A1 := 2 * ENNReal.ofReal (2 * π) with hA1
  have hk2 : Measurable fun p : ℂ × ℂ => kInv ρ (p.1 - p.2) :=
    (measurable_kInv ρ).comp (measurable_fst.sub measurable_snd)
  have hF : Measurable fun p : (ℂ × ℂ) × ℂ => kInv ρ (p.1.1 - p.1.2) * kInv ρ (p.1.1 - p.2) :=
    (hk2.comp measurable_fst).mul (hk2.comp (measurable_fst.fst.prodMk measurable_snd))
  have step1 : ∀ y, (∫⁻ z, kInv ρ (y - z) ∂μ) ^ (2 : ℝ) =
      ∫⁻ z, (∫⁻ z', kInv ρ (y - z) * kInv ρ (y - z') ∂μ) ∂μ := by
    intro y
    have hm : Measurable fun z => kInv ρ (y - z) :=
      (measurable_kInv ρ).comp (measurable_const.sub measurable_id)
    rw [ENNReal.rpow_two, sq, lintegral_lintegral_mul hm.aemeasurable hm.aemeasurable]
  simp_rw [step1]
  have hm1 : Measurable fun q : ℂ × ℂ => ∫⁻ z', kInv ρ (q.1 - q.2) * kInv ρ (q.1 - z') ∂μ :=
    Measurable.lintegral_prod_right' (ν := μ) hF
  rw [lintegral_lintegral_swap (μ := volume) (ν := μ) hm1.aemeasurable]
  have step2 : ∀ z, ∫⁻ y, (∫⁻ z', kInv ρ (y - z) * kInv ρ (y - z') ∂μ) =
      ∫⁻ z', (∫⁻ y, kInv ρ (y - z) * kInv ρ (y - z')) ∂μ := by
    intro z
    refine lintegral_lintegral_swap ?_
    exact ((hk2.comp (measurable_fst.prodMk measurable_const)).mul hk2).aemeasurable
  simp_rw [step2]
  have hK : ∀ z, ∫⁻ z', (∫⁻ y, kInv ρ (y - z) * kInv ρ (y - z')) ∂μ ≤
      A0 * μ univ + A1 * C := by
    intro z
    calc ∫⁻ z', (∫⁻ y, kInv ρ (y - z) * kInv ρ (y - z')) ∂μ
        ≤ ∫⁻ z', (A0 + A1 * ENNReal.ofReal (-Real.log ‖z' - z‖)) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hatom z)] with z' hz'
          have hne : z ≠ z' := fun h => hz' (by rw [h]; rfl)
          have h := lintegral_kInv_mul_kInv_le hne hρ
          rwa [norm_sub_rev z z'] at h
      _ = A0 * μ univ + A1 * ∫⁻ z', ENNReal.ofReal (-Real.log ‖z' - z‖) ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const,
            lintegral_const_mul _ (admissible_measurable_logNeg_sub z)]
      _ ≤ A0 * μ univ + A1 * C := add_le_add_right (mul_le_mul_right (hbd z) _) _
  calc ∫⁻ z, (∫⁻ z', (∫⁻ y, kInv ρ (y - z) * kInv ρ (y - z')) ∂μ) ∂μ
      ≤ ∫⁻ _z, (A0 * μ univ + A1 * C) ∂μ := lintegral_mono hK
    _ = (A0 * μ univ + A1 * C) * μ univ := lintegral_const _

/-- The M4 estimate with explicit constant. -/
theorem mixed_local_pairing_bound {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {K : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hKloc : ∀ z ∈ K, LocalBall D S z (2 * R)) :
    ∃ CP : ℝ, ∀ μ : Measure ℂ, IsAdmissibleH μ → μ Kᶜ = 0 → ∀ f ∈ mixedSpace D S,
      ENNReal.ofReal (3 * R ^ 2 / 2) * ENNReal.ofReal |∫ x, f x ∂μ| ≤
        ENNReal.ofReal (∫ z in D, ‖fderiv ℝ f z‖ ^ 2) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (2 * π)⁻¹ * 2 * μ univ *
            (volume D ^ (1 / 2 : ℝ) * ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal (3 * R ^ 2 / 2) * (ENNReal.ofReal (2 * π)⁻¹ * 2 *
            (∫⁻ y, (∫⁻ z, kInv (2 * R) (y - z) ∂μ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))) := by
  obtain ⟨CP, hCP⟩ := mixed_poincare hD hDH hb hS
  refine ⟨CP, fun μ hμ hμK f hf => ?_⟩
  have hμf := hμ.1
  have hKae : ∀ᵐ z ∂μ, z ∈ K := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμK] with z hz
    exact Set.notMem_compl_iff.mp hz
  set a : ℝ≥0∞ := ENNReal.ofReal (3 * R ^ 2 / 2) with ha
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * π)⁻¹ with hc
  set P : ℂ → ℝ≥0∞ := fun y => ∫⁻ z, kInv (2 * R) (y - z) ∂μ with hPdef
  have hPm : Measurable P :=
    Measurable.lintegral_prod_right' (ν := μ)
      ((measurable_kInv (2 * R)).comp (measurable_fst.sub measurable_snd))
  set PP : ℝ≥0∞ := ∫⁻ y, P y ^ (2 : ℝ) with hPP
  set VD : ℝ≥0∞ := volume D with hVD
  have hVD_lt : VD < ⊤ := hb.measure_lt_top
  set B : ℝ≥0∞ := c * 2 * μ univ * (VD ^ (1 / 2 : ℝ) * ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ)) +
    a * (c * 2 * PP ^ (1 / 2 : ℝ)) with hB
  have ha0 : 0 < 3 * R ^ 2 / 2 := by positivity
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le one_le_smooth
  have hfc : Continuous f := hf1.continuous
  have hdc : Continuous (fderiv ℝ f) := hf1.continuous_fderiv one_ne_zero
  set G : ℝ := ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg hD.measurableSet fun _ _ => sq_nonneg _
  have hGint : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D := hf.2.1
  set Y : ℝ≥0∞ := ENNReal.ofReal G ^ (1 / 2 : ℝ) with hY
  -- (a) the energy as a lintegral
  have hEn : ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal G := by
    rw [hG, ofReal_integral_eq_lintegral_ofReal hGint
      (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  -- (b) Poincaré
  have hfsq : IntegrableOn (fun z => f z ^ 2) D :=
    ((hfc.pow 2).continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have hL2 : ∫⁻ y in D, ‖f y‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (max CP 0) * ENNReal.ofReal G := by
    have e : ∫⁻ y in D, ‖f y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∫ z in D, f z ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hfsq (Eventually.of_forall fun _ => sq_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
        Real.rpow_two, sq_abs]
    rw [e, ← ENNReal.ofReal_mul (le_max_right _ _)]
    exact ENNReal.ofReal_le_ofReal
      ((hCP f hf).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hG0))
  -- (c) the `L¹` term
  set L1 := ∫⁻ y in D, ‖f y‖ₑ with hL1def
  have hL1 : L1 ≤ VD ^ (1 / 2 : ℝ) * (ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) * Y) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict D) Real.HolderConjugate.two_two
      (f := fun _ => (1 : ℝ≥0∞)) (g := fun y => ‖f y‖ₑ) aemeasurable_const
      hfc.enorm.measurable.aemeasurable
    simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const,
      Measure.restrict_apply_univ] at h
    refine h.trans (mul_le_mul_right ?_ _)
    calc (∫⁻ y in D, ‖f y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (max CP 0) * ENNReal.ofReal G) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hL2 (by norm_num)
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  -- (d) the pointwise bound, integrated
  have hint1 : a * ∫⁻ z, ENNReal.ofReal |f z| ∂μ ≤ c * (2 * L1) * μ univ +
      a * (c * ∫⁻ z, (∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) ∂μ) := by
    rw [← lintegral_const_mul' a (fun z => ENNReal.ofReal |f z|) ENNReal.ofReal_ne_top]
    calc ∫⁻ z, a * ENNReal.ofReal |f z| ∂μ
        ≤ ∫⁻ z, (c * (2 * L1) +
          a * (c * ∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z)))) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hKae] with z hz
          exact local_pointwise_bound hD.measurableSet hf1 (hKloc z hz).1 hR
            (fun y hy hyz => (hKloc z hz).mem_of_mem_H hD hS hy hyz.le)
      _ = _ := by
          rw [lintegral_add_left measurable_const, lintegral_const,
            lintegral_const_mul' a _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
  -- (e) Tonelli, and restriction to `D`
  have hswap : ∫⁻ z, (∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) ∂μ ≤
      2 * ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ * P y := by
    have hm : Measurable fun p : ℂ × ℂ => ‖fderiv ℝ f p.2‖ₑ * (2 * kInv (2 * R) (p.2 - p.1)) :=
      (hdc.enorm.measurable.comp measurable_snd).mul
        (measurable_const.mul ((measurable_kInv _).comp (measurable_snd.sub measurable_fst)))
    have e : ∀ y, ∫⁻ z, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z)) ∂μ =
        2 * (‖fderiv ℝ f y‖ₑ * P y) := by
      intro y
      calc ∫⁻ z, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z)) ∂μ
          = ∫⁻ z, (‖fderiv ℝ f y‖ₑ * 2) * kInv (2 * R) (y - z) ∂μ := by simp_rw [mul_assoc]
        _ = (‖fderiv ℝ f y‖ₑ * 2) * P y :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top (by norm_num))
        _ = 2 * (‖fderiv ℝ f y‖ₑ * P y) := by ring
    rw [lintegral_lintegral_swap hm.aemeasurable, setLIntegral_congr_fun measurableSet_H_mx (fun y _ => e y),
      lintegral_const_mul' _ _ (by norm_num)]
    refine mul_le_mul_right ?_ 2
    rw [← lintegral_indicator measurableSet_H_mx, ← lintegral_indicator hD.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hyD : y ∈ D
    · rw [indicator_of_mem (hDH hyD), indicator_of_mem hyD]
    · rw [indicator_of_notMem hyD]
      by_cases hyH : y ∈ H
      · rw [indicator_of_mem hyH]
        have hP0 : P y = 0 := by
          rw [hPdef]
          refine (lintegral_congr_ae ?_).trans lintegral_zero
          filter_upwards [hKae] with z hz
          have hk : ¬ ‖y - z‖ < 2 * R := fun h =>
            hyD ((hKloc z hz).mem_of_mem_H hD hS hyH h.le)
          simp [kInv, hk]
        rw [hP0, mul_zero]
      · rw [indicator_of_notMem hyH]
  -- (f) Cauchy–Schwarz for the gradient term
  have hW : ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ * P y ≤ Y * PP ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict D) Real.HolderConjugate.two_two
      (f := fun y => ‖fderiv ℝ f y‖ₑ) (g := P) hdc.enorm.measurable.aemeasurable hPm.aemeasurable
    simp only [Pi.mul_apply] at h
    refine h.trans (mul_le_mul' (le_of_eq ?_)
      (ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by norm_num)))
    rw [hEn]
  -- (g) combination
  have hmain : a * ENNReal.ofReal |∫ x, f x ∂μ| ≤ Y * B := by
    have h0 : ENNReal.ofReal |∫ x, f x ∂μ| ≤ ∫⁻ z, ENNReal.ofReal |f z| ∂μ := by
      rw [← Real.enorm_eq_ofReal_abs]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp only [Real.enorm_eq_ofReal_abs]
    calc a * ENNReal.ofReal |∫ x, f x ∂μ| ≤ a * ∫⁻ z, ENNReal.ofReal |f z| ∂μ :=
          mul_le_mul_right h0 _
      _ ≤ c * (2 * L1) * μ univ +
          a * (c * ∫⁻ z, (∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) ∂μ) := hint1
      _ ≤ c * (2 * (VD ^ (1 / 2 : ℝ) * (ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) * Y))) * μ univ +
          a * (c * (2 * (Y * PP ^ (1 / 2 : ℝ)))) := by
          refine add_le_add (mul_le_mul_left (mul_le_mul_right (mul_le_mul_right hL1 2) c) _)
            (mul_le_mul_right (mul_le_mul_right (hswap.trans (mul_le_mul_right hW 2)) c) a)
      _ = Y * B := by rw [hB]; ring
  exact hmain

/-- Conversion of the `ℝ≥0∞` form of the M4 estimate to a real inequality. -/
theorem sq_le_of_ennreal_bound {I G a : ℝ} {B : ℝ≥0∞} (ha : 0 < a) (hG : 0 ≤ G) (hB : B ≠ ⊤)
    (h : ENNReal.ofReal a * ENNReal.ofReal |I| ≤ ENNReal.ofReal G ^ (1 / 2 : ℝ) * B) :
    I ^ 2 ≤ (B.toReal / a) ^ 2 * G := by
  have hYeq : ENNReal.ofReal G ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt G) := by
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hG (by norm_num)]
  rw [hYeq, ← ENNReal.ofReal_toReal hB, ← ENNReal.ofReal_mul ha.le,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg)).mp h
  have hI : |I| ≤ Real.sqrt G * (B.toReal / a) := by
    rw [← mul_div_assoc, le_div_iff₀ ha]
    linarith
  calc I ^ 2 = |I| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt G * (B.toReal / a)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hI 2
    _ = (B.toReal / a) ^ 2 * G := by rw [mul_pow, Real.sq_sqrt hG]; ring

/-- **Uniform bound.** The Riesz vectors of the folded circles of a fixed radius `s < R`
centred in `K` are uniformly bounded. -/
theorem exists_norm_rieszVec_foldedCircle_le {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {K : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hKloc : ∀ z ∈ K, LocalBall D S z (2 * R)) {s : ℝ} (hs : 0 < s) (hsR : s < R) :
    ∃ B : ℝ, ∀ z ∈ K, ‖rieszVec D (mixedSpace D S) (foldedCircle z s)‖ ≤ B := by
  set R' : ℝ := (2 * R - s) / 2 with hR'
  have hR'0 : 0 < R' := by rw [hR']; linarith
  set K' : Set ℂ := {w | w ∈ Hbar ∧ ∃ z ∈ K, dist w z ≤ s} with hK'
  have hK'loc : ∀ w ∈ K', LocalBall D S w (2 * R') := by
    rintro w ⟨hw, z, hz, hwz⟩
    exact (hKloc z hz).mono hw (by linarith) (by rw [hR']; linarith)
  obtain ⟨CP, hCP⟩ := mixed_local_pairing_bound hD hDH hb hS hR'0 hK'loc
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * π)⁻¹ with hc
  set a : ℝ≥0∞ := ENNReal.ofReal (3 * R' ^ 2 / 2) with ha
  set Cs : ℝ≥0∞ := 2 * ENNReal.ofReal (Real.log 2 + |Real.log s|) with hCs
  set Q : ℝ≥0∞ := (2 * ENNReal.ofReal (2 * π) *
      (1 + ENNReal.ofReal (max (Real.log (2 * (2 * R'))) 0)) * 1 +
      2 * ENNReal.ofReal (2 * π) * Cs) * 1 with hQ
  set B0 : ℝ≥0∞ := c * 2 * 1 * (volume D ^ (1 / 2 : ℝ) * ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ)) +
    a * (c * 2 * Q ^ (1 / 2 : ℝ)) with hB0
  have hVD : volume D ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hb.measure_lt_top.ne
  have hQt : Q ≠ ⊤ := by rw [hQ, hCs]; finiteness
  have hB0t : B0 ≠ ⊤ := by
    have h1 : Q ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hQt
    have h2 : ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    rw [hB0]; finiteness
  have ha0 : 0 < 3 * R' ^ 2 / 2 := by positivity
  set M : ℝ := (B0.toReal / (3 * R' ^ 2 / 2)) ^ 2 with hM
  refine ⟨Real.sqrt (M * (2 * π)), fun z hz => ?_⟩
  have hzH : z ∈ Hbar := (hKloc z hz).1
  have hμ := isAdmissibleH_foldedCircle hzH hs
  have hsub : closedBall z s ∩ Hbar ⊆ K' := fun w hw => ⟨hw.2, z, hz, hw.1⟩
  have hμK' : foldedCircle z s K'ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hsub) (foldedCircle_compl_eq_zero hzH hs.le)
  have huniv : foldedCircle z s univ = 1 := by
    have := hμ.1
    rw [foldedCircle, Measure.map_apply measurable_foldH MeasurableSet.univ, preimage_univ]
    exact measure_univ
  have hPP : ∫⁻ y, (∫⁻ w, kInv (2 * R') (y - w) ∂(foldedCircle z s)) ^ (2 : ℝ) ≤ Q := by
    have h := lintegral_kInvPot_sq_le hμ (ρ := 2 * R') (by linarith) (C := Cs)
      (lintegral_negLog_foldedCircle_le z hs)
    rwa [huniv] at h
  have hpair : ∀ f ∈ mixedSpace D S,
      (∫ x, f x ∂(foldedCircle z s)) ^ 2 ≤ M * ∫ w in D, ‖fderiv ℝ f w‖ ^ 2 := by
    intro f hf
    have h := hCP _ hμ hμK' f hf
    rw [huniv] at h
    have h' : a * ENNReal.ofReal |∫ x, f x ∂(foldedCircle z s)| ≤
        ENNReal.ofReal (∫ w in D, ‖fderiv ℝ f w‖ ^ 2) ^ (1 / 2 : ℝ) * B0 := by
      refine h.trans ?_
      rw [hB0]
      gcongr
    exact sq_le_of_ennreal_bound ha0 (setIntegral_nonneg hD.measurableSet fun _ _ => sq_nonneg _)
      hB0t h'
  have hadm : IsAdmissibleDual D (mixedSpace D S) (foldedCircle z s) :=
    isAdmissibleDual_foldedCircle_of_local hD hDH hb hS (hKloc z hz) hs (by linarith)
  have hsupp : ∃ K, IsCompact K ∧ foldedCircle z s Kᶜ = 0 :=
    ⟨closedBall z s ∩ Hbar, (isCompact_closedBall z s).inter_right isClosed_Hbar,
      foldedCircle_compl_eq_zero hzH hs.le⟩
  have hdn := dualNormSq_eq_norm_rieszVec (isDNSpace_mixedSpace D S) hsupp hadm.2.2
  have hle : dualNormSq D (mixedSpace D S) (foldedCircle z s) ≤ ENNReal.ofReal (M * (2 * π)) := by
    unfold dualNormSq
    refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hf.2]
    have hE : dirichletEnergyOn D f = (2 * π)⁻¹ * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 := rfl
    have hπ : (2 * π) ≠ 0 := by positivity
    calc (∫ x, f x ∂(foldedCircle z s)) ^ 2 ≤ M * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 := hpair f hf.1
      _ = M * (2 * π) * dirichletEnergyOn D f := by
          rw [hE, ← mul_assoc, mul_assoc M (2 * π) (2 * π)⁻¹, mul_inv_cancel₀ hπ, mul_one]
  rw [hdn] at hle
  have hM0 : 0 ≤ M * (2 * π) := by positivity
  have h2 := (ENNReal.ofReal_le_ofReal_iff hM0).mp hle
  exact Real.le_sqrt_of_sq_le h2

end QuantumZipper.K3
