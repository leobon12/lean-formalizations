import QuantumZipper.Proofs.LQG.WedgeBdryInfB1
import QuantumZipper.Proofs.LQG.WedgeInfGrowth

/-!
# WEDGE-BDRY 4 (b), 2/3: infinite boundary mass of the reference wedge field

In the coupling of `WedgeBdry.wedge_ae_of_logSing` the reference wedge field is
`W = V + α(−log‖·‖) + m` with `V` of the law of the free field plus a log singularity and `m` a
continuous correction built from the two Brownian paths. For `t ≥ 1` (Sheffield §1.6, the wedge
as a free field with a log singularity times an independent radial part; the coupling is this
repository's own argument, see `WedgeGood.lean`)

* `corrM_apply'`: `m(t) = √2 b'(log t + s₀) + (Q − α)s₀ − √2 N(log t)`,
* the a.s. growth bounds (`WedgeInf.ae_wedgeProcess_neg_ge` for `b'`, sublinear growth of `N`)
  give `m(t) ≥ −C − (α''−α)log t` for `α'' > α`,

so by the (5.1) density rule `ν_W = e^{γm/2}·ν_{V+α(−log)}` and `ae_infWeight_logSing`,
`ν_W[1,∞) ≥ e^{−γC/2} ∫_{[1,∞)} t^{−(α''−α)γ/2} dν_{V+α(−log)} = ⊤`, hence `ν_W[1,∞) = ⊤` and
`ν_W[0,∞) = ⊤` (`ae_qBoundaryMeasure_Ici_top_wedgeField`, clause 3 of
`S5.WedgeBoundaryRegularStmt` for the reference field, given `WedgeBdryFreeInfStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper

namespace WedgeBdry

open WedgeTK WedgeRes CircleFubini WedgeGood
open GaussTK (norm_ofReal')

/-! ## 1. The coupling correction and its value -/

theorem infGood_reconstruct (γ β : ℝ) (x : FieldSample) :
    InfGood γ β (Factorization.reconstruct (Factorization.coords x)) ↔ InfGood γ β x := by
  simp only [InfGood, infWeight_reconstruct, GoodSample.isLQGGood_iff_reconstruct]

theorem infGood_add_const {γ β : ℝ} {x : FieldSample} (h : InfGood γ β x) (c : ℝ) :
    InfGood γ β (x + ofFun (fun _ => c)) := by
  rw [← GoodSample.addConst_eq_add_ofFun]
  exact ⟨(infWeight_addConst h.2 c).2 h.1, h.2.addConst c⟩

theorem qBoundaryMeasure_congr_coords {γ : ℝ} {x y : FieldSample}
    (h : Factorization.coords x = Factorization.coords y) :
    qBoundaryMeasure γ x = qBoundaryMeasure γ y := by
  rw [← qBoundaryMeasure_reconstruct γ x, ← qBoundaryMeasure_reconstruct γ y, h]

/-- The reflected radial path `s ↦ √2 b'(s) − (α−Q)s`. -/
def reflPath (α Q : ℝ) (b' : ℝ≥0 → ℝ) : ℝ → ℝ :=
  fun s => √2 * b' s.toNNReal - (α - Q) * s

theorem continuous_reflPath {α Q : ℝ} {b' : ℝ≥0 → ℝ} (hb' : Continuous b') :
    Continuous (reflPath α Q b') :=
  ((hb'.comp continuous_real_toNNReal).const_mul _).sub (continuous_const.mul continuous_id)

theorem reflPath_zero {α Q : ℝ} {b' : ℝ≥0 → ℝ} (h : b' 0 = 0) : reflPath α Q b' 0 = 0 := by
  simp [reflPath, h]

/-- `lastZero` of a reflected path is nonnegative. -/
theorem lastZero_reflPath_nonneg (α Q : ℝ) (b' : ℝ≥0 → ℝ) :
    0 ≤ lastZero (reflPath α Q b') :=
  Real.sSup_nonneg fun _ hx => hx.1

/-- The correction `φ` of the coupling, as a function of the two paths. -/
def corrPhi (α Q : ℝ) (b' bN : ℝ≥0 → ℝ) : ℝ → ℝ :=
  fun t => Q * t + reflPath α Q b' (-t + lastZero (reflPath α Q b')) - √2 * bN (-t).toNNReal - α * t

/-- The continuous correction `m` of the coupling, as a function of the two paths. -/
def corrM (α Q : ℝ) (b' bN : ℝ≥0 → ℝ) : ℂ → ℝ :=
  fun z => corrPhi α Q b' bN (-Real.log (max ‖z‖ 1))

theorem corrM_continuous {α Q : ℝ} {b' bN : ℝ≥0 → ℝ} (hb' : Continuous b')
    (hbN : Continuous bN) : Continuous (corrM α Q b' bN) := by
  have hφ : Continuous (corrPhi α Q b' bN) :=
    (((continuous_const.mul continuous_id).add
      ((continuous_reflPath hb').comp (continuous_neg.add continuous_const))).sub
      (continuous_const.mul (hbN.comp (continuous_real_toNNReal.comp continuous_neg)))).sub
      (continuous_const.mul continuous_id)
  exact hφ.comp ((continuous_norm.max continuous_const).log
    (fun z => (one_pos.trans_le (le_max_right _ _)).ne')).neg

/-- `wedgePath` at a negative time, in terms of the reflected path. -/
theorem wedgePath_neg_eq {α Q : ℝ} {b b' : ℝ≥0 → ℝ} {u : ℝ} (hu : 0 < u) :
    wedgePath α Q b b' (-u) = reflPath α Q b' (u + lastZero (reflPath α Q b')) := by
  have hnot : ¬ (0 ≤ -u) := by linarith
  simp only [wedgePath, reflPath, hnot, if_false, neg_neg]
  rfl

/-- The value of the coupling correction `m` at a real point `t ≥ 1`. -/
theorem corrM_apply' {α Q : ℝ} {b' bN : ℝ≥0 → ℝ} {t : ℝ} (ht : 1 ≤ t) :
    corrM α Q b' bN (t : ℂ) =
      √2 * b' (Real.toNNReal (Real.log t + lastZero (reflPath α Q b')))
        + (Q - α) * lastZero (reflPath α Q b') - √2 * bN (Real.toNNReal (Real.log t)) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have h1 : Real.log (max ‖((t : ℝ) : ℂ)‖ 1) = Real.log t := by
    rw [norm_ofReal', abs_of_pos ht0, max_eq_left ht]
  have h2 : reflPath α Q b' (Real.log t + lastZero (reflPath α Q b')) =
      √2 * b' (Real.toNNReal (Real.log t + lastZero (reflPath α Q b')))
        - (α - Q) * (Real.log t + lastZero (reflPath α Q b')) := rfl
  simp only [corrM, corrPhi, h1, neg_neg, h2]
  ring

/-- The value of the coupling correction `m` at `1` is `0`. -/
theorem corrM_apply_one {α Q : ℝ} {b' bN : ℝ≥0 → ℝ} (hb' : Continuous b') (hb0 : b' 0 = 0)
    (hN0 : bN 0 = 0) : corrM α Q b' bN ((1 : ℝ) : ℂ) = 0 := by
  have hz : reflPath α Q b' (lastZero (reflPath α Q b')) = 0 :=
    apply_lastZero (continuous_reflPath hb') (reflPath_zero hb0)
  have hz' : √2 * b' (Real.toNNReal (lastZero (reflPath α Q b'))) =
      (α - Q) * lastZero (reflPath α Q b') := by
    have h2 : reflPath α Q b' (lastZero (reflPath α Q b')) =
        √2 * b' (Real.toNNReal (lastZero (reflPath α Q b')))
          - (α - Q) * lastZero (reflPath α Q b') := rfl
    linarith [hz, h2]
  rw [corrM_apply' (α := α) (Q := Q) (b' := b') (bN := bN) (t := (1 : ℝ)) le_rfl]
  simp only [Real.log_one, zero_add, Real.toNNReal_zero, hN0, sub_zero]
  rw [hz']
  ring

/-! ## 2. The coupling: infinite mass of the reference wedge field -/

/-- **WEDGE-BDRY 4 (b), step 2.** Given the free-field statement (item 4 (a)), almost surely the
reference wedge field of a quantum wedge has infinite boundary mass on `[0,∞)`. -/
theorem ae_qBoundaryMeasure_Ici_top_wedgeField (hInf : WedgeBdryFreeInfStmt) {γ α α'' : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < α'') (hα'' : α'' < Qc γ) (Ω' : Type)
    [MeasurableSpace Ω'] (P' : Measure Ω') (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ)
    (hP : IsProbabilityMeasure P') (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hind : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P',
      qBoundaryMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) (Ici (0 : ℝ))
        = ⊤ := by
  haveI := hP
  obtain ⟨B, B', hB, hB', hBind, hAB⟩ := hA
  have hAw : IsWedgeProcess α (Qc γ) A P' := ⟨B, B', hB, hB', hBind, hAB⟩
  obtain ⟨Bt, hBtm, hBtc, hBtB⟩ := exists_good_version hB
  obtain ⟨Bt', hBt'm, hBt'c, hBt'B⟩ := exists_good_version hB'
  have hBtpre : IsPreBrownianReal Bt P' :=
    hB.toIsPreBrownianReal.congr fun s => hBtB.mono fun ω h => (h s).symm
  have hBt'0 : ∀ᵐ ω ∂P', Bt' 0 ω = 0 := by
    filter_upwards [hBt'B, hB'.eval_zero_ae_eq_zero] with ω h1 h2
    rw [h1, h2]
  obtain ⟨Pt, hPtm, hPtc, hPtW⟩ := exists_good_version (isBrownianReal_radialBMpos hX)
  obtain ⟨Nt, hNtm, hNtc, hNtW⟩ := exists_good_version (isBrownianReal_radialBMneg hX)
  have hPtpre : IsPreBrownianReal Pt P' :=
    (isBrownianReal_radialBMpos hX).toIsPreBrownianReal.congr fun s =>
      hPtW.mono fun ω h => (h s).symm
  have hNtpre : IsPreBrownianReal Nt P' :=
    (isBrownianReal_radialBMneg hX).toIsPreBrownianReal.congr fun s =>
      hNtW.mono fun ω h => (h s).symm
  have hNt0 : ∀ᵐ ω ∂P', Nt 0 ω = 0 := by
    filter_upwards [hNtW] with ω hω
    rw [hω 0]
    simp [radialBMneg, radialProc]
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  -- the fields
  set Lf : ℂ → ℝ := fun z => α * -Real.log ‖z‖ with hLf
  set ρ : Ω' → ℂ → ℝ := fun ω z =>
    if ‖z‖ ≤ 1 then √2 * Bt (tau z) ω else √2 * Nt (tauM z) ω with hρ
  set V : Ω' → FieldSample := fun ω => lateralPart (X ω) + ofFun (ρ ω) with hV
  set Z : Ω' → FieldSample := fun ω => addConst (X ω) (-radAvgReg (X ω) 1) with hZ
  set Lat : Ω' → ℕ → ℝ := fun ω i => lateralPart (X ω) (fcC i) with hLat
  set Ψ : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × (ℝ≥0 → ℝ) → ℕ → ℝ := fun p i =>
    p.1.1 i + √2 * (Jmod (((fcC i).restrict Dsc).map tau) p.2 +
      Jmod (((fcC i).restrict Dscᶜ).map tauM) p.1.2) + ∫ z, Lf z ∂fcC i with hΨ
  have hLfint : ∀ i, Integrable Lf (fcC i) := fun i =>
    ((integrable_log_norm_adm (fcC_admissible i)).neg.const_mul α :
      Integrable (fun z => α * -Real.log ‖z‖) (fcC i))
  -- splitting the integral of a two-sided Brownian profile
  have hsplit : ∀ (W1 W2 : ℝ≥0 → Ω' → ℝ), Measurable (Function.uncurry W1) →
      IsPreBrownianReal W1 P' → Measurable (Function.uncurry W2) → IsPreBrownianReal W2 P' →
      ∀ i, ∀ᵐ ω ∂P',
        Integrable (fun z => if ‖z‖ ≤ 1 then √2 * W1 (tau z) ω else √2 * W2 (tauM z) ω)
          (fcC i) ∧
        ∫ z, (if ‖z‖ ≤ 1 then √2 * W1 (tau z) ω else √2 * W2 (tauM z) ω) ∂fcC i =
          √2 * (Jmod (((fcC i).restrict Dsc).map tau) (fun s => W1 s ω) +
            Jmod (((fcC i).restrict Dscᶜ).map tauM) (fun s => W2 s ω)) := by
    intro W1 W2 h1m h1 h2m h2 i
    filter_upwards [ae_Jmod_eq h1m h1 measurable_tau (integrable_tau_restrict (fcC_admissible i) Dsc),
      ae_Jmod_eq h2m h2 measurable_tauM (integrable_tauM_restrict (fcC_admissible i) Dscᶜ)]
      with ω hA1 hA2
    set f : ℂ → ℝ := fun z => if ‖z‖ ≤ 1 then √2 * W1 (tau z) ω else √2 * W2 (tauM z) ω
      with hf
    have hf1 : EqOn (fun z => √2 * W1 (tau z) ω) f Dsc := fun z hz => by
      have : ‖z‖ ≤ 1 := by simpa using hz
      simp only [hf, if_pos this]
    have hf2 : EqOn (fun z => √2 * W2 (tauM z) ω) f Dscᶜ := fun z hz => by
      have : ¬ ‖z‖ ≤ 1 := by simpa using hz
      simp only [hf, if_neg this]
    have i1 : IntegrableOn f Dsc (fcC i) :=
      IntegrableOn.congr_fun (hA1.1.const_mul (√2) : IntegrableOn _ Dsc (fcC i)) hf1 measurableSet_Dsc
    have i2 : IntegrableOn f Dscᶜ (fcC i) :=
      IntegrableOn.congr_fun (hA2.1.const_mul (√2) : IntegrableOn _ Dscᶜ (fcC i)) hf2
        measurableSet_Dsc.compl
    have hint : Integrable f (fcC i) := by
      have := i1.union i2
      rwa [union_compl_self, integrableOn_univ] at this
    refine ⟨hint, ?_⟩
    rw [← integral_add_compl measurableSet_Dsc hint,
      ← setIntegral_congr_fun measurableSet_Dsc hf1,
      ← setIntegral_congr_fun measurableSet_Dsc.compl hf2, integral_const_mul,
      integral_const_mul, hA1.2, hA2.2]
    ring
  -- the coordinates of `V + Lf` and of `Z + Lf`
  have hVc : ∀ i, (fun ω => Factorization.coords (V ω + ofFun Lf) i) =ᵐ[P']
      fun ω => Ψ ((Lat ω, fun s => Nt s ω), fun s => Bt s ω) i := by
    intro i
    filter_upwards [hsplit Bt Nt hBtm hBtpre hNtm hNtpre i] with ω hω
    show lateralPart (X ω) (fcC i) + ∫ z, ρ ω z ∂fcC i + ∫ z, Lf z ∂fcC i = _
    simp only [hρ]
    rw [hω.2]
  have hZc : ∀ i, (fun ω => Factorization.coords (Z ω + ofFun Lf) i) =ᵐ[P']
      fun ω => Ψ ((Lat ω, fun s => Nt s ω), fun s => Pt s ω) i := by
    intro i
    have hμ := fcC_admissible i
    have h0 := noAtoms_of_isAdmissibleH hμ 0
    filter_upwards [hG.ae_good, ae_evalReg_fc hG (Factorization.dyadicIndex i).1
        (radius_pos (Factorization.dyadicIndex i).2), ae_integral_radial hX hG hμ, hPtW, hNtW,
      hsplit Pt Nt hPtm hPtpre hNtm hNtpre i] with ω hg h1 h2 h3 h4 h5
    have h1' : evalReg (X ω) (fcC i) = X ω (fcC i) := h1
    have hlat : lateralPart (X ω) (fcC i) = X ω (fcC i) - ∫ z, G ω (0, ‖z‖) ∂fcC i := by
      rw [hg.lateralPart_eq h0, h1']
    have hpt : (fun z => G ω (0, ‖z‖) - G ω (0, 1)) =ᵐ[fcC i]
        fun z => if ‖z‖ ≤ 1 then √2 * Pt (tau z) ω else √2 * Nt (tauM z) ω := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with z hz0
      have hz : z ≠ 0 := hz0
      by_cases hz1 : ‖z‖ ≤ 1
      · rw [if_pos hz1, h3, ← radialProc_eq_pos, radialProc, hg.radAvgReg_eq (Real.exp_pos _),
          hg.radAvgReg_eq one_pos, exp_neg_tau hz hz1]
      · have hz1' : 1 < ‖z‖ := lt_of_not_ge hz1
        have e : Real.exp (-(-((tauM z : ℝ)))) = ‖z‖ := by
          rw [neg_neg, tauM, Real.coe_toNNReal _ (Real.log_nonneg hz1'.le),
            Real.exp_log (by linarith)]
        rw [if_neg hz1, h4, ← radialProc_eq_neg, radialProc, hg.radAvgReg_eq (Real.exp_pos _),
          hg.radAvgReg_eq one_pos, e]
    have e1 : ∫ z, (if ‖z‖ ≤ 1 then √2 * Pt (tau z) ω else √2 * Nt (tauM z) ω) ∂fcC i =
        ∫ z, G ω (0, ‖z‖) ∂fcC i - G ω (0, 1) := by
      rw [← integral_congr_ae hpt, integral_sub h2.1 (integrable_const _), integral_const,
        probReal_univ, one_smul]
    rw [h5.2] at e1
    show X ω (fcC i) + -radAvgReg (X ω) 1 * ((fcC i) Set.univ).toReal + ∫ z, Lf z ∂fcC i = _
    simp only [hΨ, hLat, measure_univ, ENNReal.toReal_one, mul_one, hg.radAvgReg_eq one_pos]
    rw [e1, hlat]
    ring
  -- measurability
  have hLatm : Measurable Lat :=
    measurable_pi_iff.2 fun i => measurable_lateral_of (hY_X hX) (fcC i)
  have hNpm : Measurable fun ω (s : ℝ≥0) => Nt s ω :=
    measurable_pi_iff.2 fun s => hNtm.of_uncurry_left
  have hBpm : Measurable fun ω (s : ℝ≥0) => Bt s ω :=
    measurable_pi_iff.2 fun s => hBtm.of_uncurry_left
  have hPpm : Measurable fun ω (s : ℝ≥0) => Pt s ω :=
    measurable_pi_iff.2 fun s => hPtm.of_uncurry_left
  have hΨm : Measurable Ψ := by
    refine measurable_pi_iff.2 fun i => ?_
    exact (((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).add
      ((((measurable_Jmod _).comp measurable_snd).add
        ((measurable_Jmod _).comp (measurable_snd.comp measurable_fst))).const_mul _)).add_const _
  -- independence of the lateral data (with `β⁻`) from `b` and from `β⁺`
  have hI1 : IndepFun (fun ω => (Lat ω, fun s => Nt s ω)) (fun ω s => Bt s ω) P' := by
    have hΦ : Measurable (fun x : FieldSample => ((fun i => lateralPart x (fcC i)),
        fun s : ℝ≥0 => (√2)⁻¹ * (radAvgReg x (Real.exp (-(-(s : ℝ)))) - radAvgReg x 1))) :=
      (measurable_pi_iff.2 fun i => measurable_lateralPart_apply (fcC i)).prodMk
        (measurable_pi_iff.2 fun s =>
          ((measurable_radAvgReg₂.comp (measurable_id.prodMk measurable_const)).sub
            (measurable_radAvgReg₂.comp (measurable_id.prodMk measurable_const))).const_mul _)
    have hψ : Measurable (fun (a : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * (a s - (α - Qc γ) * s)) :=
      measurable_pi_iff.2 fun s => ((measurable_pi_apply _).sub_const _).const_mul _
    refine (hind.comp hΦ hψ).congr ?_ ?_
    · filter_upwards [hNtW] with ω hω
      refine Prod.ext rfl (funext fun s => ?_)
      show _ = Nt s ω
      rw [hω s]; rfl
    · filter_upwards [hBtB] with ω hω
      funext s
      simp only [Function.comp_apply, hω s, hAB ω, wedgePath]
      rw [if_pos (NNReal.coe_nonneg s), Real.toNNReal_coe]
      have h2 : (√2 : ℝ) ≠ 0 := by positivity
      field_simp
      ring
  have hI2 : IndepFun (fun ω => (Lat ω, fun s => Nt s ω)) (fun ω s => Pt s ω) P' := by
    have hrad := indepFun_radialProc_lateralPart hX
    have hbm := indepFun_radialBM hX
    set R : Ω' → ℝ → ℝ := fun ω t => radialProc X t ω with hR
    set C : Ω' → (ℕ → ℝ) × (TestFun H → ℝ) := fun ω =>
      (CoordsFull.coordsFull (lateralPart (X ω)), fun ρ : TestFun H =>
        pairRaw (lateralPart (X ω)) ρ.1) with hC
    choose j hj using exists_fullIndex
    have hLatC : Lat = (fun p : (ℕ → ℝ) × (TestFun H → ℝ) => fun i => p.1 (j i)) ∘ C := by
      funext ω i
      simp only [Function.comp_apply, hC, hLat, CoordsFull.coordsFull, hj i]
      rfl
    have hιm : Measurable (fun p : (ℕ → ℝ) × (TestFun H → ℝ) => fun i => p.1 (j i)) :=
      measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp measurable_fst
    have hRm : Measurable R := measurable_pi_iff.2 fun t => measurable_radialProc hX t
    have hnegR : pathOf (radialBMneg X) = (fun (a : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * a (-(s : ℝ))) ∘ R :=
      rfl
    have hposR : pathOf (radialBMpos X) = (fun (a : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * a s) ∘ R := rfl
    have hnm : Measurable (fun (a : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * a (-(s : ℝ))) :=
      measurable_pi_iff.2 fun s => (measurable_pi_apply _).const_mul _
    have hpm : Measurable (fun (a : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * a s) :=
      measurable_pi_iff.2 fun s => (measurable_pi_apply _).const_mul _
    have h12 : Indep (MeasurableSpace.comap (pathOf (radialBMneg X)) MeasurableSpace.pi)
        (MeasurableSpace.comap (pathOf (radialBMpos X)) MeasurableSpace.pi) P' :=
      ((IndepFun_iff_Indep _ _ _).1 hbm).symm
    have hXB : Indep (MeasurableSpace.comap Lat MeasurableSpace.pi)
        (MeasurableSpace.comap R MeasurableSpace.pi) P' := by
      refine indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).1 hrad).symm ?_
      rw [hLatC, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hιm.comap_le
    have h₁ : MeasurableSpace.comap (pathOf (radialBMneg X)) MeasurableSpace.pi ≤
        MeasurableSpace.comap R MeasurableSpace.pi := by
      rw [hnegR, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hnm.comap_le
    have h₂ : MeasurableSpace.comap (pathOf (radialBMpos X)) MeasurableSpace.pi ≤
        MeasurableSpace.comap R MeasurableSpace.pi := by
      rw [hposR, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hpm.comap_le
    have hsup := UnzipInvariance.indep_sup_of_indep h₁ h₂ hRm.comap_le hLatm.comap_le h12 hXB
    have hI : IndepFun (fun ω => (Lat ω, pathOf (radialBMneg X) ω)) (pathOf (radialBMpos X)) P' := by
      rw [IndepFun_iff_Indep]
      refine indep_of_indep_of_le_left hsup ?_
      exact le_of_eq ((MeasurableSpace.comap_prodMk _ _).trans (sup_comm _ _))
    refine hI.congr ?_ ?_
    · filter_upwards [hNtW] with ω hω
      refine Prod.ext rfl (funext fun s => ?_)
      exact (hω s).symm
    · filter_upwards [hPtW] with ω hω
      funext s
      exact (hω s).symm
  have hjoint : P'.map (fun ω => ((Lat ω, fun s => Nt s ω), fun s => Bt s ω)) =
      P'.map (fun ω => ((Lat ω, fun s => Nt s ω), fun s => Pt s ω)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hLatm.prodMk hNpm).aemeasurable
        hBpm.aemeasurable).1 hI1,
      (indepFun_iff_map_prod_eq_prod_map_map (hLatm.prodMk hNpm).aemeasurable
        hPpm.aemeasurable).1 hI2, map_path_eq hBtpre hPtpre hBpm hPpm]
  -- equal laws of the coordinates of `V + Lf` and `Z + Lf`
  have hΨV : Measurable fun ω => Ψ ((Lat ω, fun s => Nt s ω), fun s => Bt s ω) :=
    hΨm.comp ((hLatm.prodMk hNpm).prodMk hBpm)
  have hΨZ : Measurable fun ω => Ψ ((Lat ω, fun s => Nt s ω), fun s => Pt s ω) :=
    hΨm.comp ((hLatm.prodMk hNpm).prodMk hPpm)
  have hVae : AEMeasurable (fun ω => Factorization.coords (V ω + ofFun Lf)) P' :=
    AEMeasurable.of_eval fun i =>
      ((measurable_pi_apply i).comp hΨV).aemeasurable.congr (hVc i).symm
  have hZae : AEMeasurable (fun ω => Factorization.coords (Z ω + ofFun Lf)) P' :=
    AEMeasurable.of_eval fun i =>
      ((measurable_pi_apply i).comp hΨZ).aemeasurable.congr (hZc i).symm
  have hlawVZ : P'.map (fun ω => Factorization.coords (V ω + ofFun Lf)) =
      P'.map (fun ω => Factorization.coords (Z ω + ofFun Lf)) := by
    rw [map_eq_of_forall_ae_eq hVae hΨV.aemeasurable hVc,
      map_eq_of_forall_ae_eq hZae hΨZ.aemeasurable hZc]
    have h := congrArg (Measure.map Ψ) hjoint
    rw [Measure.map_map hΨm ((hLatm.prodMk hNpm).prodMk hBpm),
      Measure.map_map hΨm ((hLatm.prodMk hNpm).prodMk hPpm)] at h
    exact h
  -- the property for `V + Lf`, from the free-field statement
  have hlogGood : ∀ᵐ ω ∂P', InfGood γ ((α'' - α) * γ / 2) (X ω + ofFun fun z => α * -Real.log ‖z‖) := by
    filter_upwards [ae_infWeight_logSing hInf hγ hγ2 hα hα'' P' X hX,
      LogSingGood.logSingGoodAS_holds hγ hγ2 (hα.trans hα'') Ω' _ P' X inferInstance hX]
      with ω h1 h2
    exact ⟨h1, h2⟩
  set Sg : Set (ℕ → ℝ) := {y | InfGood γ ((α'' - α) * γ / 2) (Factorization.reconstruct y)} with hSg_def
  have hSg : MeasurableSet Sg := Factorization.measurable_reconstruct (measurableSet_infGood γ ((α'' - α) * γ / 2))
  have hZgood : ∀ᵐ ω ∂P', Factorization.coords (Z ω + ofFun Lf) ∈ Sg := by
    filter_upwards [hlogGood] with ω hω
    show InfGood γ ((α'' - α) * γ / 2) (Factorization.reconstruct (Factorization.coords (Z ω + ofFun Lf)))
    rw [infGood_reconstruct]
    have e : Z ω + ofFun Lf = addConst (X ω + ofFun Lf) (-radAvgReg (X ω) 1) := by
      funext μ
      simp only [hZ, addConst, Pi.add_apply]
      ring
    rw [e, GoodSample.addConst_eq_add_ofFun]
    exact infGood_add_const hω _
  have hVgood : ∀ᵐ ω ∂P', InfGood γ ((α'' - α) * γ / 2) (V ω + ofFun Lf) := by
    have h1 := (ae_map_iff hZae hSg).2 hZgood
    rw [← hlawVZ] at h1
    filter_upwards [(ae_map_iff hVae hSg).1 h1] with ω hω
    exact (infGood_reconstruct γ ((α'' - α) * γ / 2) _).1 hω
  -- the continuous correction `m`
  set Yt : Ω' → ℝ → ℝ := fun ω s => √2 * Bt' s.toNNReal ω - (α - Qc γ) * s with hYt
  set φ : Ω' → ℝ → ℝ := fun ω t => Qc γ * t + Yt ω (-t + lastZero (Yt ω)) -
    √2 * Nt (-t).toNNReal ω - α * t with hφ
  set m : Ω' → ℂ → ℝ := fun ω z => φ ω (-Real.log (max ‖z‖ 1)) with hm
  have hYtc : ∀ ω, Continuous (Yt ω) := fun ω =>
    (continuous_const.mul ((hBt'c ω).comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have hmCfun : ∀ ω, m ω = corrM α (Qc γ) (fun s => Bt' s ω) (fun s => Nt s ω) :=
    fun _ => rfl
  have hs0Y : ∀ ω, lastZero (reflPath α (Qc γ) (fun s => Bt' s ω)) = lastZero (Yt ω) :=
    fun _ => rfl
  have hmc : ∀ ω, Continuous (m ω) := fun ω => by
    have hmC : m ω = corrM α (Qc γ) (fun s => Bt' s ω) (fun s => Nt s ω) := hmCfun ω
    rw [hmC]
    exact corrM_continuous (hBt'c ω) (hNtc ω)
  have hρint : ∀ i, ∀ᵐ ω ∂P', Integrable (ρ ω) (fcC i) := fun i =>
    (hsplit Bt Nt hBtm hBtpre hNtm hNtpre i).mono fun ω hω => hω.1
  have hcoordW : ∀ᵐ ω ∂P', Factorization.coords
      (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) =
        Factorization.coords (V ω + ofFun Lf + ofFun (m ω)) := by
    filter_upwards [hBtB, hBt'B, hBt'0, hNt0, ae_all_iff.2 hρint] with ω h1 h2 h3 h4 h5
    have hY0 : Yt ω (lastZero (Yt ω)) = 0 := apply_lastZero (hYtc ω) (by simp [hYt, h3])
    have hpt : ∀ z, Qc γ * -Real.log ‖z‖ + A (-Real.log ‖z‖) ω = ρ ω z + Lf z + m ω z := by
      intro z
      by_cases hz1 : ‖z‖ ≤ 1
      · have ht : 0 ≤ -Real.log ‖z‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg z) hz1)
        have hm0 : m ω z = 0 := by
          simp only [hm, hφ, max_eq_right hz1, Real.log_one, neg_zero, zero_add, mul_zero,
            sub_zero, Real.toNNReal_zero, hY0, h4]
        rw [hm0, hAB ω, wedgePath]
        simp only [if_pos ht, hρ, if_pos hz1, hLf, tau, ← h1]
        ring
      · have hz1' : 1 < ‖z‖ := lt_of_not_ge hz1
        have ht : ¬ 0 ≤ -Real.log ‖z‖ := by
          have := Real.log_pos hz1'; linarith
        have hYeq : (fun s : ℝ => √2 * B' s.toNNReal ω - (α - Qc γ) * s) = Yt ω :=
          funext fun s => by simp only [hYt, ← h2 s.toNNReal]
        rw [hAB ω, wedgePath]
        simp only [if_neg ht]
        rw [hYeq]
        simp only [hρ, if_neg hz1, hLf, hm, hφ, max_eq_left hz1'.le, tauM, neg_neg]
        simp only [hYt, ← h2]
        ring
    funext i
    show lateralPart (X ω) (fcC i) +
        ∫ z, (Qc γ * -Real.log ‖z‖ + A (-Real.log ‖z‖) ω) ∂fcC i =
      lateralPart (X ω) (fcC i) + ∫ z, ρ ω z ∂fcC i + ∫ z, Lf z ∂fcC i + ∫ z, m ω z ∂fcC i
    have hmint : Integrable (m ω) (fcC i) :=
      integrable_of_continuousOn_Hbar (hmc ω).continuousOn (fcC_admissible i)
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_add (f := fun z => ρ ω z + Lf z) (g := m ω) ((h5 i).add (hLfint i)) hmint,
      integral_add (f := ρ ω) (g := Lf) (h5 i) (hLfint i)]
    ring
  -- the growth of `m` at `+∞`
  have hY0ae : ∀ᵐ ω ∂P', Yt ω (lastZero (Yt ω)) = 0 := by
    filter_upwards [hBt'0] with ω h3
    exact apply_lastZero (hYtc ω) (by simp [hYt, h3])
  have hNgrow : ∀ᵐ ω ∂P', ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ s : ℝ≥0, |Nt s ω| ≤ ε * s + K := by
    filter_upwards [WedgeInf.ae_abs_le_of_isBrownianReal (isBrownianReal_radialBMneg hX),
      hNtW] with ω h1 h2 ε hε
    obtain ⟨K, hK⟩ := h1 ε hε
    exact ⟨K, fun s => by rw [h2 s]; exact hK s⟩
  have hbound : ∀ᵐ ω ∂P', ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      -C - (α'' - α) * Real.log t ≤ m ω t := by
    filter_upwards [WedgeInf.ae_wedgeProcess_neg_ge hAw, hNgrow, hBt'B, hBt'0, hNt0]
      with ω hgrow hNg hBB hB0 hN0
    obtain ⟨C1, hC1⟩ := hgrow ((α'' - α) / 2) (by linarith)
    obtain ⟨K, hK⟩ := hNg ((α'' - α) / 4) (by linarith)
    have hs0 : 0 ≤ lastZero (reflPath α (Qc γ) (fun s => Bt' s ω)) :=
      lastZero_reflPath_nonneg α (Qc γ) (fun s => Bt' s ω)
    have hs0Y0 : 0 ≤ lastZero (Yt ω) := hs0Y ω ▸ hs0
    have hs0eq : lastZero (reflPath α (Qc γ) (fun s => Bt' s ω)) =
        lastZero (reflPath α (Qc γ) (fun s => B' s ω)) := by
      congr 1
      funext s
      simp only [reflPath]
      rw [hBB s.toNNReal]
    have hCtot : (0 : ℝ) ≤ max C1 0 + √2 * max K 0 :=
      add_nonneg (le_max_right C1 0) (mul_nonneg (Real.sqrt_nonneg 2) (le_max_right K 0))
    refine ⟨max C1 0 + √2 * max K 0, hCtot, fun t ht => ?_⟩
    rcases eq_or_lt_of_le ht with rfl | ht1
    · rw [Real.log_one, mul_zero, sub_zero]
      have hm1 : m ω ((1 : ℝ) : ℂ) = 0 := by
        rw [hmCfun ω]
        exact corrM_apply_one (hBt'c ω) hB0 hN0
      rw [hm1]
      have h2 : (0 : ℝ) ≤ √2 * max K 0 :=
        mul_nonneg (Real.sqrt_nonneg 2) (le_max_right K 0)
      linarith [le_max_right C1 0]
    · have hu : 0 < Real.log t := Real.log_pos ht1
      have hmv : m ω t = √2 * B' (Real.toNNReal (Real.log t + lastZero (Yt ω))) ω
          + (Qc γ - α) * lastZero (Yt ω) - √2 * Nt (Real.toNNReal (Real.log t)) ω := by
        rw [hmCfun ω, corrM_apply' ht1.le, hs0Y ω,
          hBB (Real.toNNReal (Real.log t + lastZero (Yt ω)))]
      have hAval : A (-(Real.log t)) ω = √2 * B'
            (Real.toNNReal (Real.log t + lastZero (reflPath α (Qc γ) (fun s => B' s ω)))) ω
          - (α - Qc γ) * (Real.log t + lastZero (reflPath α (Qc γ) (fun s => B' s ω))) := by
        rw [hAB ω, wedgePath_neg_eq hu]
        rfl
      have hC1' := hC1 (Real.log t) hu.le
      rw [hAval] at hC1'
      have hK' := hK (Real.toNNReal (Real.log t))
      rw [Real.coe_toNNReal _ hu.le] at hK'
      have hK'' : -√2 * (((α'' - α) / 4) * Real.log t) - √2 * K ≤
          -√2 * Nt (Real.toNNReal (Real.log t)) ω := by
        have h4 : Nt (Real.toNNReal (Real.log t)) ω ≤ ((α'' - α) / 4) * Real.log t + K :=
          (le_abs_self _).trans hK'
        nlinarith [h4, Real.sqrt_nonneg 2]
      have hs0Y' : lastZero (Yt ω) = lastZero (reflPath α (Qc γ) (fun s => B' s ω)) := by
        rw [← hs0Y ω, hs0eq]
      have hmu : m ω t = A (-(Real.log t)) ω - (Qc γ - α) * Real.log t
          - √2 * Nt (Real.toNNReal (Real.log t)) ω := by
        rw [hmv, hs0Y', hAval]
        ring
      have huu : 0 ≤ (α'' - α) * Real.log t := mul_nonneg (by linarith) hu.le
      have hsqrt2 : √2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have hsqrt4 : √2 * ((α'' - α) / 4) + (α'' - α) / 2 ≤ α'' - α := by
        nlinarith [huu, hsqrt2]
      have hKmax : √2 * K ≤ √2 * max K 0 :=
        mul_le_mul_of_nonneg_left (le_max_left K 0) (Real.sqrt_nonneg 2)
      nlinarith [hC1', hK'', hmu, hu.le, hsqrt4, hKmax, le_max_left C1 0]
  -- the density comparison
  have hνeq : ∀ᵐ ω ∂P', qBoundaryMeasure γ
      (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) =
      qBoundaryMeasure γ (V ω + ofFun Lf + ofFun (m ω)) :=
    hcoordW.mono fun _ hc => qBoundaryMeasure_congr_coords hc
  filter_upwards [hVgood, hbound, hνeq] with ω hV hC hνeqω
  obtain ⟨C, hC0, hCb⟩ := hC
  have hνdens : qBoundaryMeasure γ (V ω + ofFun Lf + ofFun (m ω)) =
      (qBoundaryMeasure γ (V ω + ofFun Lf)).withDensity
        (fun t => ENNReal.ofReal (Real.exp (γ / 2 * m ω t))) :=
    GoodSample.qBoundaryMeasure_add_ofFun hV.2 (hmc ω).continuousOn
  have hpt : ∀ t ∈ Ici (1 : ℝ), ENNReal.ofReal (Real.exp (-(γ * C / 2))) *
      infWeightFn ((α'' - α) * γ / 2) t ≤ ENNReal.ofReal (Real.exp (γ / 2 * m ω t)) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have hm := hCb t ht1
    have hexp : Real.exp (-(γ * C / 2)) * t ^ (-((α'' - α) * γ / 2)) ≤
        Real.exp (γ / 2 * m ω t) := by
      rw [Real.rpow_def_of_pos ht0, ← Real.exp_add]
      have heq : -(γ * C / 2) + Real.log t * (-((α'' - α) * γ / 2)) =
          γ / 2 * (-C - (α'' - α) * Real.log t) := by ring
      rw [heq]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ γ / 2))
    show ENNReal.ofReal (Real.exp (-(γ * C / 2))) *
        ENNReal.ofReal (t ^ (-((α'' - α) * γ / 2))) ≤ ENNReal.ofReal (Real.exp (γ / 2 * m ω t))
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hexp
  have hle : ∫⁻ t in Ici (1 : ℝ), (ENNReal.ofReal (Real.exp (-(γ * C / 2))) *
        infWeightFn ((α'' - α) * γ / 2) t) ∂qBoundaryMeasure γ (V ω + ofFun Lf)
      ≤ ∫⁻ t in Ici (1 : ℝ), ENNReal.ofReal (Real.exp (γ / 2 * m ω t))
        ∂qBoundaryMeasure γ (V ω + ofFun Lf) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hpt t ht
  have hval : ∫⁻ t in Ici (1 : ℝ), (ENNReal.ofReal (Real.exp (-(γ * C / 2))) *
        infWeightFn ((α'' - α) * γ / 2) t) ∂qBoundaryMeasure γ (V ω + ofFun Lf) = ⊤ := by
    rw [lintegral_const_mul _ (measurable_infWeightFn _), hV.1]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hIci1 : qBoundaryMeasure γ (V ω + ofFun Lf + ofFun (m ω)) (Ici (1 : ℝ)) = ⊤ := by
    rw [hνdens, MeasureTheory.withDensity_apply _ measurableSet_Ici]
    exact le_antisymm le_top (hval ▸ hle)
  have hfinal : qBoundaryMeasure γ (V ω + ofFun Lf + ofFun (m ω)) (Ici (0 : ℝ)) = ⊤ :=
    top_le_iff.1 (hIci1 ▸ measure_mono (Ici_subset_Ici.2 (by norm_num : (0 : ℝ) ≤ 1)))
  rw [hνeqω, hfinal]

end WedgeBdry

end QuantumZipper
