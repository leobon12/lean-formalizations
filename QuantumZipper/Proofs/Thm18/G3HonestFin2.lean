import QuantumZipper.Proofs.Thm18.G3HonestFin1
import QuantumZipper.Proofs.LQG.AllOffsetsBasic
import QuantumZipper.Proofs.LQG.TwoRadiusTilt

/-!
# G3 fidelity F3: finiteness of `E ν_h[−δ, 0]` (`R = 1` first moment of the free field)

Sheffield, arXiv:1012.4797, Theorem 1.8; Duplantier–Sheffield arXiv:0808.1560 §6. This file
proves the `R = 1` first-moment finiteness (`G3HonestFin1.G3HonestFinOneStmt`) for the
unit-normalized free field, and hence the residual F3 input `Thm18Asm.G3HonestFinStmt`
(`E ν_h[−δ, 0] < ∞` for `h = normField γ X₀`, `0 < γ < 2`).

The library's free-field first-moment formula (`FirstMoment.integral_qBoundaryMeasure_free`,
`PalmFree.palm_formula_free`) needs a window `[−N, N]` with `N + 2 ≤ R` and a *continuous* mean,
so it does not apply at the normalization radius `R = 1` of Theorem 1.2's field (nor to the mean
`(2/γ) log |·|`, singular at `0`). The route here is the level-`k` computation plus Fatou:

* `ae_avgReg_zField_one_eq_zV`: a.s. `avgReg (zField X 1) k t = zV X 1 (2^{-k}) t` (both are the
  balanced difference `fcPairVal X ((t:ℂ), 2^{-k}, 0, 1)`; `BdryExist.avgReg_zField_ae_eq` and
  `AllOffsets.ae_zV_eq`).
* `integral_exp_avgReg_zField_one`, `lintegral_exp_avgReg_zField_one`: for `|t| + 2^{-k} ≤ 1`,
  `E e^{(γ/2) avgReg (zField X 1) k t} = (2^{-k})^{−γ²/4}` — the `R = 1` case of the level-`k`
  density `PalmFormula.rhoK` (`AllOffsets.integral_exp_zV`, variance `2 log 1 − 2 log 2^{-k}`).
* `lintegral_bdryApprox_zField_one`: the level-`k` first-moment **identity**
  `E ∫ f d(bdryApprox γ (zField X 1) k) = ∫ f` whenever `|t| + 2^{-k} ≤ 1` on `tsupport f`: the
  density `2^{-kγ²/4} e^{(γ/2) avgReg}` times the Gaussian moment `(2^{-k})^{−γ²/4}` is `1`.
* `lintegral_le_liminf_of_isVagueLimitR`: Fatou for a vague limit (own elementary proof).
* `lintegral_qBoundaryMeasure_zField_one_Icc_lt_top`: **the `R = 1` finiteness** for
  `Icc u v ⊆ (−1, 1)`: a bump (`GoodSample.exists_bump`) dominating `1_{[u,v]}`, Fatou in `ω`
  (`lintegral_liminf_le`) and the level-`k` identity bound the expected mass by `∫ f < ∞`.
* `g3HonestFinStmt_main`: `G3HonestFinStmt γ i`, combining this with
  `G3HonestFin1.g3HonestFinStmt_of_zFieldOne` (`ν_h = |t| · ν_{zField X₀ 1}`).

Source: Duplantier–Sheffield, arXiv:0808.1560 §6 (first moment of the quantum boundary measure
at a fixed normalization), in the normalization `h₁(0) = 0` (unit semicircle) of Theorem 1.2;
the level-`k` density `rhoK` is `PalmFormula.rhoK` and the Fatou step is an own elementary
argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

set_option maxHeartbeats 2000000

namespace QuantumZipper
namespace Thm18Asm

open K3

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample} {γ : ℝ}

/-! ## The a.s. identification of the regularized average -/

/-- A.s. the regularized folded-circle average of the unit-normalized free field at `(t, 2^{-k})`
is the coordinate `zV X 1 (2^{-k}) t`: both are the balanced difference
`fcPairVal X ((t:ℂ), 2^{-k}, 0, 1)`. -/
theorem ae_avgReg_zField_one_eq_zV (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    (t : ℝ) (k : ℕ) :
    (fun ω => avgReg (BdryExist.zField X 1 ω) k (t : ℂ)) =ᵐ[P]
      AllOffsets.zV X 1 (radius k) t :=
  (BdryExist.avgReg_zField_ae_eq (P := P) hX 1 k (GaussTK.ofReal_mem_Hbar t)).trans
    (AllOffsets.ae_zV_eq (P := P) hX 1 t (radius_pos k)).symm

/-! ## The exponential moment of the unit-normalized free field -/

/-- **Level-`k` exponential moment.** For `|t| + 2^{-k} ≤ 1`,
`E exp((γ/2) avgReg (zField X 1) k t) = (2^{-k})^{−γ²/4}`: the variance of the coordinate is
`2 log 1 − 2 log 2^{-k}` (`AllOffsets.integral_exp_zV` with `R = 1`). -/
theorem integral_exp_avgReg_zField_one (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    {t : ℝ} {k : ℕ} (ht : |t| + radius k ≤ 1) :
    ∫ ω, Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ)) ∂P =
      radius k ^ (-(γ ^ 2 / 4)) := by
  have hr := radius_pos k
  have h1 : (fun ω => Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ))) =ᵐ[P]
      fun ω => Real.exp (γ / 2 * AllOffsets.zV X 1 (radius k) t ω) :=
    (ae_avgReg_zField_one_eq_zV (P := P) hX t k).mono fun ω hω =>
      congrArg (fun x => Real.exp (γ / 2 * x)) hω
  rw [integral_congr_ae h1, AllOffsets.integral_exp_zV (P := P) hX hr ht (γ / 2),
    Real.rpow_def_of_pos hr]
  congr 1
  have hlog : ((2 * Real.log (1 : ℝ) - 2 * Real.log (radius k)).toNNReal : ℝ) =
      -(2 * Real.log (radius k)) := by
    rw [Real.log_one, mul_zero, zero_sub]
    exact Real.coe_toNNReal _ (by
      have := Real.log_nonpos hr.le (BdryExist.radius_le_one k)
      linarith)
  rw [hlog]
  ring

/-- The same in `lintegral` form. -/
theorem lintegral_exp_avgReg_zField_one (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    {t : ℝ} {k : ℕ} (ht : |t| + radius k ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ))) ∂P =
      ENNReal.ofReal (radius k ^ (-(γ ^ 2 / 4))) := by
  have hr := radius_pos k
  have h2 : Integrable (fun ω => Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ)))
      P := by
    have hL := AllOffsets.hasLaw_zV (P := P) hX (R := 1) (t := t) (r := radius k) hr ht
    have hZ : Integrable (fun ω => Real.exp (γ / 2 * AllOffsets.zV X 1 (radius k) t ω)) P := by
      simpa only [zero_add] using hL.integrable_fun_comp
        (TwoRadius.integrable_exp_mul_add_gaussianReal _ (γ / 2) 0)
    refine hZ.congr ?_
    exact (ae_avgReg_zField_one_eq_zV (P := P) hX t k).mono fun ω hω =>
      congrArg (fun x => Real.exp (γ / 2 * x)) hω.symm
  rw [← ofReal_integral_eq_lintegral_ofReal h2 (ae_of_all _ fun ω => (Real.exp_pos _).le),
    integral_exp_avgReg_zField_one (P := P) hX ht]

/-! ## The level-`k` first-moment identity -/

/-- Joint measurability of the coordinate `(ω, t) ↦ avgReg (zField X 1 ω) k t`. -/
theorem measurable_avgReg_zField_one_pair (hX : IsFreeGFFModConstH X P) (k : ℕ) :
    Measurable (fun p : Ω × ℝ => avgReg (BdryExist.zField X 1 p.1) k (p.2 : ℂ)) := by
  have h1 : Measurable (fun p : Ω × ℝ => BdryExist.zField X 1 p.1) :=
    (BdryExist.measurable_zField hX 1).comp measurable_fst
  exact Measurable.comp (g := fun q : FieldSample × ℂ => avgReg q.1 k q.2)
    (f := fun p : Ω × ℝ => (BdryExist.zField X 1 p.1, (p.2 : ℂ))) (measurable_avgReg k)
    (h1.prodMk (Complex.measurable_ofReal.comp measurable_snd))

/-- Measurability of the level-`k` density `t ↦ 2^{-kγ²/4} e^{(γ/2) avgReg (zField X 1) k t}`. -/
theorem measurable_bdryDens_zField_one (_hX : IsFreeGFFModConstH X P) (k : ℕ) (ω : Ω) :
    Measurable (fun t : ℝ => ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
      Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ)))) := by
  have havg : Measurable (fun t : ℝ => avgReg (BdryExist.zField X 1 ω) k (t : ℂ)) :=
    Measurable.comp (g := fun q : FieldSample × ℂ => avgReg q.1 k q.2)
      (f := fun t : ℝ => (BdryExist.zField X 1 ω, (t : ℂ))) (measurable_avgReg k)
      (measurable_const.prodMk (Complex.measurable_ofReal.comp measurable_id))
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Real.measurable_exp.comp (havg.const_mul _)))

/-- Joint measurability of the level-`k` density in `(ω, t)`. -/
theorem measurable_bdryDens_zField_one_pair (hX : IsFreeGFFModConstH X P) (k : ℕ) :
    Measurable (fun p : Ω × ℝ => ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
      Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 p.1) k (p.2 : ℂ)))) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
    ((measurable_avgReg_zField_one_pair (X := X) hX k).const_mul _)))

/-- **Level-`k` first moment of `bdryApprox γ (zField X 1)`, exactly `∫ f`.** For `f ≥ 0`
continuous with compact support and `|t| + 2^{-k} ≤ 1` on `tsupport f`, the level-`k` expectation
is `∫ f`: the density `2^{-kγ²/4} exp((γ/2) avgReg)` integrates to
`2^{-kγ²/4} · (2^{-k})^{−γ²/4} = 1`. -/
theorem lintegral_bdryApprox_zField_one (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) (hfc : HasCompactSupport f)
    {k : ℕ} (hk : ∀ t ∈ tsupport f, |t| + radius k ≤ 1) :
    ∫⁻ ω, ∫⁻ t, ENNReal.ofReal (f t) ∂(bdryApprox γ (BdryExist.zField X 1 ω) k) ∂P =
      ENNReal.ofReal (∫ t, f t) := by
  have hr := radius_pos k
  have havg := measurable_avgReg_zField_one_pair (X := X) hX k
  -- step 1: unfold `withDensity`
  have hstep : ∀ ω, ∫⁻ t, ENNReal.ofReal (f t) ∂(bdryApprox γ (BdryExist.zField X 1 ω) k) =
      ∫⁻ (t : ℝ), ENNReal.ofReal ((radius k ^ (γ ^ 2 / 4) *
        Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ))) * f t) ∂volume := by
    intro ω
    rw [bdryApprox,
      lintegral_withDensity_eq_lintegral_mul₀
        (measurable_bdryDens_zField_one (X := X) hX k ω).aemeasurable
        (hf.measurable.ennreal_ofReal.aemeasurable)]
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply]
    exact (ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.le _)
      (Real.exp_pos _).le)).symm
  -- joint measurability for Tonelli
  have hGm : AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal ((radius k ^ (γ ^ 2 / 4) *
      Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 p.1) k (p.2 : ℂ))) * f p.2))
      (P.prod volume) := by
    refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
    exact (measurable_const.mul (Real.measurable_exp.comp (havg.const_mul _))).mul
      (hf.measurable.comp measurable_snd)
  rw [lintegral_congr hstep, lintegral_lintegral_swap hGm]
  -- step 2: the inner integral over `ω`, pointwise in `t`
  have hinner : ∀ t : ℝ, ∫⁻ (ω : Ω), ENNReal.ofReal ((radius k ^ (γ ^ 2 / 4) *
      Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ))) * f t) ∂P =
      ENNReal.ofReal (f t) := by
    intro t
    by_cases ht : t ∈ tsupport f
    · have htk : |t| + radius k ≤ 1 := hk t ht
      have hsplit : ∀ ω : Ω, ENNReal.ofReal ((radius k ^ (γ ^ 2 / 4) *
          Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ))) * f t) =
          ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * f t) *
            ENNReal.ofReal (Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ))) := by
        intro ω
        rw [show (radius k ^ (γ ^ 2 / 4) *
            Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ))) * f t =
            (radius k ^ (γ ^ 2 / 4) * f t) *
              Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ)) by ring,
          ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.le _) (hf0 t))]
      simp_rw [hsplit, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_exp_avgReg_zField_one (P := P) hX htk]
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.le _) (hf0 t))]
      congr 1
      have hrc : radius k ^ (γ ^ 2 / 4) * radius k ^ (-(γ ^ 2 / 4)) = 1 := by
        rw [← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero (radius k)]
      calc radius k ^ (γ ^ 2 / 4) * f t * radius k ^ (-(γ ^ 2 / 4))
          = f t * (radius k ^ (γ ^ 2 / 4) * radius k ^ (-(γ ^ 2 / 4))) := by ring
        _ = f t := by rw [hrc, mul_one]
    · have hft : f t = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [hft]
  simp_rw [hinner]
  exact (ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hfc)
    (ae_of_all _ hf0)).symm

/-! ## Fatou for a vague limit -/

/-- **Fatou for a vague limit.** For `g ≥ 0` continuous with compact support, `ν`-integrable,
`∫⁻ g dν ≤ liminf_k ∫⁻ g dν_k`: the real integrals converge to `∫ g dν` while each level's
`lintegral` dominates `ofReal` of the real integral. (Own elementary proof.) -/
theorem lintegral_le_liminf_of_isVagueLimitR {νs : ℕ → Measure ℝ} {ν : Measure ℝ}
    (h : IsVagueLimitR νs ν) {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hg0 : ∀ t, 0 ≤ g t) (hint : Integrable g ν) :
    ∫⁻ t, ENNReal.ofReal (g t) ∂ν ≤
      liminf (fun k => ∫⁻ t, ENNReal.ofReal (g t) ∂(νs k)) atTop := by
  have key : ∀ k, ENNReal.ofReal (∫ t, g t ∂(νs k)) ≤ ∫⁻ t, ENNReal.ofReal (g t) ∂(νs k) := by
    intro k
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  have hliminf : liminf (fun k => ENNReal.ofReal (∫ t, g t ∂(νs k))) atTop =
      ENNReal.ofReal (∫ t, g t ∂ν) :=
    Filter.Tendsto.liminf_eq ((ENNReal.continuous_ofReal.tendsto _).comp (h.2 g hg hgc))
  calc ∫⁻ t, ENNReal.ofReal (g t) ∂ν
      = ENNReal.ofReal (∫ t, g t ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hg0)).symm
    _ = liminf (fun k => ENNReal.ofReal (∫ t, g t ∂(νs k))) atTop := hliminf.symm
    _ ≤ liminf (fun k => ∫⁻ t, ENNReal.ofReal (g t) ∂(νs k)) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall key)

/-! ## The `R = 1` first-moment finiteness -/

/-- **F3 finiteness, unit-normalized free field.** For a window `Icc u v ⊆ (−1, 1)` the expected
mass of `ν_{zField X 1}` is finite: the level-`k` identity `lintegral_bdryApprox_zField_one`
and Fatou (`lintegral_liminf_le`) bound `E ν(Icc u v)` by `∫ f < ∞` for a bump `f ≥ 1_{[u,v]}`. -/
theorem lintegral_qBoundaryMeasure_zField_one_Icc_lt_top (hX : IsFreeGFFModConstH X P)
    [IsProbabilityMeasure P] {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {u v : ℝ}
    (hu : -1 < u) (hv : v < 1) :
    ∫⁻ ω, qBoundaryMeasure γ (BdryExist.zField X 1 ω) (Icc u v) ∂P < ⊤ := by
  by_cases huv : u ≤ v
  · -- a fixed window `(−d, d) ⊆ (−1, 1)` containing `[u, v]`
    have hu1 : |u| < 1 := by
      rw [abs_lt]
      exact ⟨hu, huv.trans_lt hv⟩
    have hv1 : |v| < 1 := by
      rw [abs_lt]
      exact ⟨hu.trans_le huv, hv⟩
    obtain ⟨d, hd1, hdmax, hd2⟩ : ∃ d : ℝ, d < 1 ∧ max |u| |v| < d ∧ 0 < d :=
      ⟨(max |u| |v| + 1) / 2, by linarith [max_lt hu1 hv1], by linarith [max_lt hu1 hv1],
        by have h : (0 : ℝ) ≤ max |u| |v| := (abs_nonneg u).trans (le_max_left _ _); linarith⟩
    have huw : -d < u := by
      have h1 : |u| ≤ max |u| |v| := le_max_left _ _
      have h2 : -|u| ≤ u := neg_abs_le u
      linarith
    have hvw : v < d := by
      have h1 : |v| ≤ max |u| |v| := le_max_right _ _
      have h2 : v ≤ |v| := le_abs_self v
      linarith
    obtain ⟨f, hfc, hfcs, hfsupp, hfone, hf0⟩ :=
      GoodSample.exists_bump isCompact_Icc isOpen_Ioo
        (fun t ht => ⟨huw.trans_le ht.1, ht.2.trans_lt hvw⟩)
    -- the level-`k` window condition holds eventually
    have hr : Tendsto radius atTop (𝓝 (0 : ℝ)) :=
      RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds
    have hev : ∀ᶠ k in atTop, ∀ t ∈ tsupport f, |t| + radius k ≤ 1 := by
      filter_upwards [hr.eventually
        (eventually_lt_nhds (show (0 : ℝ) < 1 - d by linarith))] with k hk t ht
      have htd : |t| < d := by
        have := hfsupp ht
        rw [Set.mem_Ioo] at this
        exact abs_lt.2 this
      linarith
    -- the level-`k` masses
    set Z : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ∫⁻ t, ENNReal.ofReal (f t) ∂(bdryApprox γ (BdryExist.zField X 1 ω) k) with hZdef
    have hZeq : ∀ k, Z k = fun ω => ∫⁻ (t : ℝ), ENNReal.ofReal (f t) *
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
          Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ))) ∂volume := by
      intro k
      funext ω
      rw [hZdef]
      simp only
      rw [bdryApprox, lintegral_withDensity_eq_lintegral_mul₀
        (measurable_bdryDens_zField_one (X := X) hX k ω).aemeasurable
        (hfc.measurable.ennreal_ofReal.aemeasurable)]
      refine lintegral_congr fun t => ?_
      simp only [Pi.mul_apply]
      exact mul_comm _ _
    have hZmeas : ∀ k, Measurable (Z k) := by
      intro k
      rw [hZeq k]
      have hjoint : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
          ENNReal.ofReal (f t) * ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
            Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ)))) :=
        (hfc.measurable.ennreal_ofReal.comp measurable_snd).mul
          (measurable_bdryDens_zField_one_pair (X := X) hX k)
      exact Measurable.lintegral_prod_right (ν := volume)
        (f := fun (ω : Ω) (t : ℝ) => ENNReal.ofReal (f t) * ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
          Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ)))) hjoint
    -- a.s. the limit dominates the mass on `Icc u v`
    have hae : ∀ᵐ ω ∂P, qBoundaryMeasure γ (BdryExist.zField X 1 ω) (Icc u v) ≤
        liminf (fun k => Z k ω) atTop := by
      filter_upwards [BdryExist.ae_isVagueLimitR_qBoundaryMeasure_zField (P := P) hX hγ hγ2 1,
        FirstMoment.ae_qBoundaryMeasure_Icc_lt_top_zField (P := P) hX hγ hγ2 1] with ω hv hfin
      have hint : Integrable f (qBoundaryMeasure γ (BdryExist.zField X 1 ω)) :=
        GoodSample.integrable_of_tsupport (U := Icc (-1) 1)
          (fun K hK hKU => (measure_mono hKU).trans_lt (by simpa using hfin (-1) 1))
          hfc hfcs (fun t ht => by
            have htd : |t| < d := by
              have := hfsupp ht
              rw [Set.mem_Ioo] at this
              exact abs_lt.2 this
            exact ⟨by have h := neg_abs_le t; linarith, by have h := le_abs_self t; linarith⟩)
      refine (le_trans ?_ (lintegral_le_liminf_of_isVagueLimitR hv hfc hfcs hf0 hint))
      rw [← lintegral_indicator_one measurableSet_Icc]
      refine lintegral_mono fun t => ?_
      by_cases ht : t ∈ Icc u v
      · rw [indicator_of_mem ht, Pi.one_apply, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (le_of_eq (hfone ht).symm)
      · rw [indicator_of_notMem ht]
        exact zero_le
    have hevconst : ∀ᶠ k in atTop, ∫⁻ ω, Z k ω ∂P = ENNReal.ofReal (∫ t, f t) := by
      filter_upwards [hev] with k hk
      exact lintegral_bdryApprox_zField_one (P := P) hX hfc hf0 hfcs hk
    have hliminfconst : liminf (fun k => ∫⁻ ω, Z k ω ∂P) atTop = ENNReal.ofReal (∫ t, f t) :=
      Filter.Tendsto.liminf_eq
        (Filter.Tendsto.congr' (hevconst.mono fun k hk => hk.symm) tendsto_const_nhds)
    calc ∫⁻ ω, qBoundaryMeasure γ (BdryExist.zField X 1 ω) (Icc u v) ∂P
        ≤ ∫⁻ ω, liminf (fun k => Z k ω) atTop ∂P := lintegral_mono_ae hae
      _ ≤ liminf (fun k => ∫⁻ ω, Z k ω ∂P) atTop := lintegral_liminf_le hZmeas
      _ = ENNReal.ofReal (∫ t, f t) := hliminfconst
      _ < ⊤ := ENNReal.ofReal_lt_top
  · rw [Set.Icc_eq_empty huv]
    simp

/-! ## F3 finiteness for Theorem 1.8 -/

/-- **Theorem 1.8, F3 finiteness** (`G3HonestFin1.G3HonestFinStmt`): for `0 < γ < 2` the expected
boundary length `E ν_h[−δ, 0]` of the Theorem 1.2 field `h = normField γ X₀` is finite, for the
scheme window `[−δ, 0]`, `δ ≤ 1/4` (`G3Idx.hδ`). -/
theorem g3HonestFinOneStmt {γ : ℝ} (i : G3Idx) (hγ : 0 < γ) (hγ2 : γ < 2) :
    G3HonestFinOneStmt γ i :=
  lintegral_qBoundaryMeasure_zField_one_Icc_lt_top (X := X₀) (P := gffBase.P)
    gffBase.gff hγ hγ2 (by have := i.hδ; linarith) (by norm_num)

/-- **Theorem 1.8, F3 finiteness** (`G3HonestFin1.G3HonestFinStmt`): for `0 < γ < 2` the expected
boundary length `E ν_h[−δ, 0]` of the Theorem 1.2 field `h = normField γ X₀` is finite, for the
scheme window `[−δ, 0]` with `δ ≤ 1/4` (`G3Idx.hδ`). -/
theorem g3HonestFinStmt_main {γ : ℝ} (i : G3Idx) (hγ : 0 < γ) (hγ2 : γ < 2) :
    G3HonestFinStmt γ i :=
  g3HonestFinStmt_of_zFieldOne (i := i) hγ hγ2 (g3HonestFinOneStmt i hγ hγ2)

end Thm18Asm
end QuantumZipper
