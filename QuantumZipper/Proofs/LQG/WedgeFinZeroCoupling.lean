import QuantumZipper.Proofs.LQG.WedgeGood
import QuantumZipper.Proofs.LQG.WedgeCanonical4
import QuantumZipper.Proofs.LQG.WedgeFinZeroSum

/-!
# WEDGE-FIN0, part 4: finite wedge area near `0` (`WedgeCan4.WedgeFiniteNearZero`)

* `wedgeFiniteNearZero_of_logSing`: if for every free field `X` almost surely `X + α(−log‖·‖)` is
  good with finite area on `B(0,1) ∩ ℍ`, then so is the wedge field of `IsQuantumWedge`
  (`WedgeCan4.WedgeFiniteNearZero γ α`). The proof is the coupling of
  `WedgeGood.wedgeRefGoodAS_of_logSing`, copied here with the coordinate event "good" replaced
  by the (measurable) event "good with finite area on the unit half-disc": the coordinates of
  `V + α(−log)` have the law of those of `(X − h₁(0)) + α(−log)`, and pathwise the wedge field
  is `V + α(−log) + m` on the coordinates with `m` continuous and `m = 0` on the closed unit disc,
  so the area measures agree on `B(0,1) ∩ ℍ` (rule (5.1), `GoodSample.qAreaMeasure_add_ofFun`).
* `wedgeFiniteNearZero_holds`: the input holds for `0 < γ < 2`, `α < Q`
  (`WedgeFinZero.ae_logSing_ball_lt_top`).

Source: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.6, p. 21 ("a
finite amount of µ_h mass in each bounded neighborhood of 0"). The coupling is the own argument
recorded in `WedgeGood`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace WedgeFinZero

open WedgeGood WedgeTK WedgeRes CircleFubini

open Classical in
/-- **`WedgeFiniteNearZero` from the log singularity** (coupling of `WedgeGood`). -/
theorem wedgeFiniteNearZero_of_logSing {γ α : ℝ}
    (h : ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → FieldSample),
      IsProbabilityMeasure P → IsFreeGFFModConstH X P →
        ∀ᵐ ω ∂P, IsLQGGood γ (X ω + ofFun fun z => α * -Real.log ‖z‖) ∧
          qAreaMeasure γ (X ω + ofFun fun z => α * -Real.log ‖z‖) (Metric.ball 0 1 ∩ H) < ⊤) :
    WedgeCan4.WedgeFiniteNearZero γ α := by
  intro Ω' _ P' X A hP hX hA hind
  obtain ⟨B, B', hB, hB', -, hAB⟩ := hA
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
  -- the event: good with finite area on the unit half-disc
  set Sf : Set (ℕ → ℝ) := {y | IsLQGGood γ (Factorization.reconstruct y) ∧
    (if IsLQGGood γ (Factorization.reconstruct y) then
      qAreaMeasure γ (Factorization.reconstruct y) else 0) (Metric.ball 0 1 ∩ H) < ⊤}
    with hSf_def
  have hSf : MeasurableSet Sf := by
    have hm := Factorization.measurable_reconstruct
    have h1 : MeasurableSet {y : ℕ → ℝ | IsLQGGood γ (Factorization.reconstruct y)} :=
      hm (GoodMeas.measurableSet_isLQGGood γ)
    have h2 := (Measure.measurable_coe (AreaProfile.measurableSet_ball_inter_H 1)).comp
      ((GoodMeas.measurable_qAreaMeasure_global γ).comp hm)
    exact h1.inter (h2 measurableSet_Iio)
  have hmem : ∀ x : FieldSample, Factorization.coords x ∈ Sf ↔
      IsLQGGood γ x ∧ qAreaMeasure γ x (Metric.ball 0 1 ∩ H) < ⊤ := by
    intro x
    have hg := GoodSample.isLQGGood_iff_reconstruct γ x
    have hq := Factorization.qAreaMeasure_congr (Factorization.avgReg_reconstruct_coords x) γ
    simp only [hSf_def, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [if_pos h1, hq] at h2
      exact ⟨hg.1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨hg.2 h1, ?_⟩
      rw [if_pos (hg.2 h1), hq]
      exact h2
  have hZfin : ∀ᵐ ω ∂P', Factorization.coords (Z ω + ofFun Lf) ∈ Sf := by
    filter_upwards [h Ω' _ P' X hP hX] with ω hω
    rw [hmem]
    have e : Z ω + ofFun Lf = addConst (X ω + ofFun Lf) (-radAvgReg (X ω) 1) := by
      funext μ
      simp only [hZ, addConst, Pi.add_apply]
      ring
    rw [e]
    refine ⟨hω.1.addConst _, ?_⟩
    rw [GoodSample.qAreaMeasure_addConst hω.1, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hω.2
  have hVfin : ∀ᵐ ω ∂P', IsLQGGood γ (V ω + ofFun Lf) ∧
      qAreaMeasure γ (V ω + ofFun Lf) (Metric.ball 0 1 ∩ H) < ⊤ := by
    have h1 := (ae_map_iff hZae hSf).2 hZfin
    rw [← hlawVZ] at h1
    filter_upwards [(ae_map_iff hVae hSf).1 h1] with ω hω
    exact (hmem _).1 hω
  -- the continuous correction `m`
  set Yt : Ω' → ℝ → ℝ := fun ω s => √2 * Bt' s.toNNReal ω - (α - Qc γ) * s with hYt
  set φ : Ω' → ℝ → ℝ := fun ω t => Qc γ * t + Yt ω (-t + lastZero (Yt ω)) -
    √2 * Nt (-t).toNNReal ω - α * t with hφ
  set m : Ω' → ℂ → ℝ := fun ω z => φ ω (-Real.log (max ‖z‖ 1)) with hm
  have hYtc : ∀ ω, Continuous (Yt ω) := fun ω =>
    (continuous_const.mul ((hBt'c ω).comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have hmc : ∀ ω, Continuous (m ω) := by
    intro ω
    have hφc : Continuous (φ ω) :=
      (((continuous_const.mul continuous_id).add
        ((hYtc ω).comp (continuous_neg.add continuous_const))).sub
        (continuous_const.mul ((hNtc ω).comp (continuous_real_toNNReal.comp continuous_neg)))).sub
        (continuous_const.mul continuous_id)
    exact hφc.comp ((continuous_norm.max continuous_const).log
      (fun z => (one_pos.trans_le (le_max_right _ _)).ne')).neg
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
  have hm0 : ∀ᵐ ω ∂P', ∀ z : ℂ, ‖z‖ ≤ 1 → m ω z = 0 := by
    filter_upwards [hBt'0, hNt0] with ω h3 h4 z hz1
    have hY0 : Yt ω (lastZero (Yt ω)) = 0 := apply_lastZero (hYtc ω) (by simp [hYt, h3])
    simp only [hm, hφ, max_eq_right hz1, Real.log_one, neg_zero, zero_add, mul_zero,
      sub_zero, Real.toNNReal_zero, hY0, h4]
  filter_upwards [hVfin, hcoordW, hm0] with ω hg hc h0
  have hS : MeasurableSet (Metric.ball (0 : ℂ) 1 ∩ H) := AreaProfile.measurableSet_ball_inter_H 1
  have hq : qAreaMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) =
      qAreaMeasure γ (V ω + ofFun Lf + ofFun (m ω)) := by
    refine Factorization.qAreaMeasure_congr ?_ γ
    rw [← Factorization.avgReg_reconstruct_coords, hc, Factorization.avgReg_reconstruct_coords]
  rw [hq, GoodSample.qAreaMeasure_add_ofFun hg.1 (hmc ω).continuousOn, withDensity_apply _ hS]
  have e : ∫⁻ z in Metric.ball 0 1 ∩ H, ENNReal.ofReal (Real.exp (γ * m ω z))
      ∂qAreaMeasure γ (V ω + ofFun Lf) =
      ∫⁻ z in Metric.ball 0 1 ∩ H, 1 ∂qAreaMeasure γ (V ω + ofFun Lf) :=
    setLIntegral_congr_fun hS fun z hz => by
      have hz1 : ‖z‖ ≤ 1 := by
        have := hz.1
        rw [Metric.mem_ball, dist_zero_right] at this
        exact this.le
      rw [h0 z hz1, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
  rw [e, setLIntegral_const, one_mul]
  exact hg.2

/-- **`WedgeFiniteNearZero γ α` holds** for `0 < γ < 2` and `α < Q` (WEDGE-FIN0). -/
theorem wedgeFiniteNearZero_holds {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    WedgeCan4.WedgeFiniteNearZero γ α :=
  wedgeFiniteNearZero_of_logSing fun Ω _ P X hP hX =>
    haveI := hP
    ae_logSing_ball_lt_top hX hγ hγ2 hα

end WedgeFinZero

end QuantumZipper
