import QuantumZipper.Proofs.LQG.WedgeTranslation
import QuantumZipper.Proofs.LQG.GoodMeasurable
import QuantumZipper.Proofs.NonVacuityWedge

/-!
# The reference wedge field is almost surely good (`WedgeRefGoodAS`), given the log singularity

`NonVacuity.WedgeRefGoodAS γ α`: for a free field `X` and an independent `α`-wedge radial process
`A`, almost surely `IsLQGGood γ (wedgeField (lateralPart X) A Q)`.

We reduce it to the single named hypothesis `LogSingGoodAS γ α` (M4-P4 with the offsets of
`IsLQGGood`, boundary and area): for a free field `X`, almost surely
`IsLQGGood γ (X + α(−log‖·‖))`.

Route (a coupling, no local certificates).
* `V := lateralPart X + ρ` where `ρ(z) = √2 b(−log|z|)` on the closed unit disc (`b` the forward
  Brownian motion of `A`) and `ρ(z) = √2 β⁻(log|z|)` outside (`β⁻` the backward radial Brownian
  motion of `X` itself). The coordinates of `V + α(−log)` have the law of those of
  `(X − h₁(0)) + α(−log)` (`coords_law_eq`), which is a.s. good by `LogSingGoodAS` and rule (5.1)
  for constants. Hence `V + α(−log)` is a.s. good (goodness is a measurable coordinate event).
* Pathwise, `W = V + α(−log) + m` on the coordinates, with `m` continuous on `ℂ` (`m = 0` on the
  unit disc), so `W` is good by rule (5.1) (`IsLQGGood.add_ofFun`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper

/-- **Named hypothesis (M4-P4 with offsets, boundary and area).** For a free field `X`, almost
surely `X + α(−log‖·‖)` is a good sample. Expected for `γ ∈ (0,2)` and `α < Q`. -/
def LogSingGoodAS (γ α : ℝ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → FieldSample),
    IsProbabilityMeasure P → IsFreeGFFModConstH X P →
      ∀ᵐ ω ∂P, IsLQGGood γ (X ω + ofFun fun z => α * -Real.log ‖z‖)

namespace WedgeGood

open WedgeTK WedgeRes CircleFubini

/-! ## 1. Coordinates, time maps, and a path-integral lemma -/

/-- The circles read by `Factorization.coords`. -/
def fcC (i : ℕ) : Measure ℂ :=
  foldedCircle (Factorization.dyadicIndex i).1 (radius (Factorization.dyadicIndex i).2)

instance isProbabilityMeasure_fcC (i : ℕ) : IsProbabilityMeasure (fcC i) := by
  unfold fcC; infer_instance

theorem fcC_admissible (i : ℕ) : IsAdmissibleH (fcC i) := by
  rw [fcC, ← fc_foldH_eq]
  exact isAdmissibleH_foldedCircle (foldH_mem_Hbar' _) (radius_pos _)

theorem isLQGGood_congr_coords {γ : ℝ} {x y : FieldSample}
    (h : Factorization.coords x = Factorization.coords y) : IsLQGGood γ x ↔ IsLQGGood γ y := by
  rw [← GoodSample.isLQGGood_iff_reconstruct γ x, h, GoodSample.isLQGGood_iff_reconstruct]

/-- The log-scale `(log‖z‖)⁺` (outside the unit disc). -/
def tauM (z : ℂ) : ℝ≥0 := (Real.log ‖z‖).toNNReal

theorem measurable_tauM : Measurable tauM :=
  (Real.measurable_log.comp measurable_norm).real_toNNReal

/-- The closed unit disc. -/
abbrev Dsc : Set ℂ := Metric.closedBall 0 1

theorem measurableSet_Dsc : MeasurableSet Dsc := measurableSet_closedBall

theorem integrable_tau_restrict {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (E : Set ℂ) :
    Integrable (fun s : ℝ≥0 => (s : ℝ)) ((μ.restrict E).map tau) := by
  have := hμ.1
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
    measurable_tau.aemeasurable]
  refine Integrable.mono' (integrable_log_norm_adm hμ).abs.restrict
    (measurable_coe_nnreal_real.comp measurable_tau).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  simp only [Function.comp_apply, tau, Real.coe_toNNReal', Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (neg_le_abs _) (abs_nonneg _)

theorem integrable_tauM_restrict {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (E : Set ℂ) :
    Integrable (fun s : ℝ≥0 => (s : ℝ)) ((μ.restrict E).map tauM) := by
  have := hμ.1
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
    measurable_tauM.aemeasurable]
  refine Integrable.mono' (integrable_log_norm_adm hμ).abs.restrict
    (measurable_coe_nnreal_real.comp measurable_tauM).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  simp only [Function.comp_apply, tauM, Real.coe_toNNReal', Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

section Jlemma

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Path integrals read through `Jmod` agree a.s. with the integral along the time map. -/
theorem ae_Jmod_eq {W : ℝ≥0 → Ω → ℝ} (hWm : Measurable (Function.uncurry W))
    (hW : IsPreBrownianReal W P) {ν : Measure ℂ} [IsFiniteMeasure ν] {T : ℂ → ℝ≥0}
    (hT : Measurable T) (hint : Integrable (fun s : ℝ≥0 => (s : ℝ)) (ν.map T)) :
    ∀ᵐ ω ∂P, Integrable (fun z => W (T z) ω) ν ∧
      Jmod (ν.map T) (fun s => W s ω) = ∫ z, W (T z) ω ∂ν := by
  filter_upwards [ae_tendsto_Jn hWm hW hint] with ω h
  have hWω : Measurable fun s => W s ω := hWm.comp (measurable_id.prodMk measurable_const)
  refine ⟨(integrable_map_measure hWω.aestronglyMeasurable hT.aemeasurable).1 h.1, ?_⟩
  rw [Jmod, h.2.limUnder_eq, integral_map hT.aemeasurable hWω.aestronglyMeasurable]

end Jlemma

/-- A continuous path vanishing at `0` vanishes at its last zero. -/
theorem apply_lastZero {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) : f (lastZero f) = 0 := by
  unfold lastZero
  set Z : Set ℝ := {s | 0 ≤ s ∧ f s = 0} with hZ
  by_cases hb : BddAbove Z
  · have hZc : IsClosed Z :=
      (isClosed_le continuous_const continuous_id).inter (isClosed_eq hf continuous_const)
    exact (hZc.csSup_mem ⟨0, le_rfl, h0⟩ hb).2
  · rw [Real.sSup_of_not_bddAbove hb]; exact h0

/-- Every circle of `coords` is a circle of `coordsFull`. -/
theorem exists_fullIndex (i : ℕ) : ∃ j, CoordsFull.fullIndex j =
    ((Factorization.dyadicIndex i).1, radius (Factorization.dyadicIndex i).2) := by
  set p := Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i with hp
  have hz : dyadicRoundC p.2.2.1 (Factorization.dyadicIndex i).1 =
      (Factorization.dyadicIndex i).1 := by
    have e : ∀ a : ℤ, dyadicRound p.2.2.1 ((a : ℝ) / (2 : ℝ) ^ p.2.2.1) =
        (a : ℝ) / (2 : ℝ) ^ p.2.2.1 := by
      intro a
      unfold dyadicRound
      rw [mul_div_cancel₀ _ (by positivity), Int.floor_intCast]
    apply Complex.ext
    · show dyadicRound p.2.2.1 ((p.1 : ℝ) / (2 : ℝ) ^ p.2.2.1) = _
      rw [e]; rfl
    · show dyadicRound p.2.2.1 ((p.2.1 : ℝ) / (2 : ℝ) ^ p.2.2.1) = _
      rw [e]; rfl
  obtain ⟨j, hj⟩ := CoordsFull.fullIndex_surj p.2.2.1 (Factorization.dyadicIndex i).1 1 one_pos
    (Factorization.dyadicIndex i).2
  refine ⟨j, ?_⟩
  rw [hj, hz, CoordsFull.radius_eq_div]

/-! ## 2. The reduction -/

/-- **`WedgeRefGoodAS` from the log singularity.** If a free field plus `α(−log‖·‖)` is a.s.
good (`LogSingGoodAS γ α`), then the reference wedge field of `IsQuantumWedge` is a.s. good. -/
theorem wedgeRefGoodAS_of_logSing {γ α : ℝ} (h : LogSingGoodAS γ α) :
    NonVacuity.WedgeRefGoodAS γ α := by
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
  -- goodness of `V + Lf`
  set Sg : Set (ℕ → ℝ) := {y | IsLQGGood γ (Factorization.reconstruct y)} with hSg_def
  have hSg : MeasurableSet Sg :=
    Factorization.measurable_reconstruct (GoodMeas.measurableSet_isLQGGood γ)
  have hZgood : ∀ᵐ ω ∂P', Factorization.coords (Z ω + ofFun Lf) ∈ Sg := by
    filter_upwards [h Ω' _ P' X hP hX] with ω hω
    show IsLQGGood γ (Factorization.reconstruct (Factorization.coords (Z ω + ofFun Lf)))
    rw [GoodSample.isLQGGood_iff_reconstruct]
    have e : Z ω + ofFun Lf = addConst (X ω + ofFun Lf) (-radAvgReg (X ω) 1) := by
      funext μ
      simp only [hZ, addConst, Pi.add_apply]
      ring
    rw [e]
    exact hω.addConst _
  have hVgood : ∀ᵐ ω ∂P', IsLQGGood γ (V ω + ofFun Lf) := by
    have h1 := (ae_map_iff hZae hSg).2 hZgood
    rw [← hlawVZ] at h1
    filter_upwards [(ae_map_iff hVae hSg).1 h1] with ω hω
    exact (GoodSample.isLQGGood_iff_reconstruct γ _).1 hω
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
  filter_upwards [hVgood, hcoordW] with ω hg hc
  rw [isLQGGood_congr_coords hc]
  exact hg.add_ofFun (hmc ω).continuousOn

end WedgeGood

end QuantumZipper
