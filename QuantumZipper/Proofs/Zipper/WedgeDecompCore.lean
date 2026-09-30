import QuantumZipper.Proofs.Zipper.WedgeDecompBasic
import QuantumZipper.Proofs.Zipper.F2WedgeCouple
import QuantumZipper.Proofs.Zipper.Cor15MarkovField

/-!
# W-D (wedge decomposition), part 2: `WedgeDecompStmt` holds

Decision D29 (`DECISIONS.md`), `handoff/WEDGE-UNZIP.md`. Sources: Sheffield, arXiv:1012.4797,
§1.6 (the `α`-wedge restricted to the unit disc is a free field plus `α(−log|·|)`, via its
radial part `A_t = √2 b_t + (α − Q)t`, `t ≥ 0`, and the lateral part of a free field) and
Duplantier–Miller–Sheffield, arXiv:1409.7055, §4.1 and Def. 4.4 (radial/lateral decomposition
of the free field: lateral part, forward and backward radial Brownian motions are independent).

Construction (on `Ω × Unit`; no fresh randomness is needed, the backward radial Brownian motion
`n = radialBMneg X'` of the free field itself plays the role of the resampled part, as in
`WedgeGood.wedgeRefGoodAS_of_logSing`):

  `X'' = lateral part of X' + prof b n`,   `G = corrField α Q A n`,

with `b` a continuous version of the forward wedge Brownian motion. `X''` is read through the
measurable map `PhiF` (dyadic Riemann sums `Jmod` for the path integrals, equal to the integrals
pathwise by `WDec.jmod_eq_integral_of_continuous`), so it is a measurable function of `(X', b)`,
hence independent of the driver. Freeness of `X''` is a law statement:
* with the forward radial Brownian motion `p` of `X'` in place of `b`, the field is `X'` minus
  the random constant `h₁(0)` (`isFreeGFFModConstH_of_ae_shift`);
* `(latF X', n, b)` and `(latF X', n, p)` have the same law (`latF X'`, `n`, `p` independent:
  `indepFun_latF_radialProc`, `indepFun_radialBM`; `b` independent of `X'`; `b`, `p` Brownian),
  so the two fields have the same law (`isFreeGFFModConstH_of_map_eq`);
* the lateral part `lateralPart X'` (with `evalReg`) agrees a.s. with the raw lateral part
  `latF X'` at each folded circle (`ae_evalReg_fc`); `X''` uses `lateralPart` exactly on folded
  circles (`latW`) so that the pathwise identity with the wedge field holds on *all* folded
  circles simultaneously.
The assembly is our own (bookkeeping around the published decomposition).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip
namespace WDec

open WedgeRes WedgeGood WedgeTK

/-- Folded circles `fc(d, r)`, `d ∈ ℍ̄`, `r > 0`. -/
def IsFC (μ : Measure ℂ) : Prop := ∃ d ∈ Hbar, ∃ r : ℝ, 0 < r ∧ μ = foldedCircle d r

open Classical in
/-- The lateral part used by `X''`: `lateralPart` (with `evalReg`) on folded circles, the raw
lateral part `F2.latF` elsewhere. -/
def latW (x : FieldSample) : FieldSample := fun μ =>
  if IsFC μ then lateralPart x μ else F2.latF (fun y : FieldSample => y) x μ

/-- The backward radial path `s ↦ (√2)⁻¹ (h_{e^s}(0) − h_1(0))` of a field. -/
def nPath (x : FieldSample) : ℝ≥0 → ℝ := fun s =>
  (√2)⁻¹ * (radAvgReg x (Real.exp (-(-(s : ℝ)))) - radAvgReg x 1)

open Classical in
/-- The measurable reading of `lateral + profile`: `l μ + √2 (Jmod … b + Jmod … n)` at admissible
`μ`, `0` elsewhere. -/
def PhiF (p : (FieldSample × (ℝ≥0 → ℝ)) × (ℝ≥0 → ℝ)) : FieldSample := fun μ =>
  if IsAdmissibleH μ then
    p.1.1 μ + √2 * (Jmod ((μ.restrict Dsc).map tau) p.2 + Jmod ((μ.restrict Dscᶜ).map tauM) p.1.2)
  else 0

theorem measurable_nPath : Measurable nPath :=
  measurable_pi_iff.2 fun _s =>
    ((measurable_radAvgReg₂.comp (measurable_id.prodMk measurable_const)).sub
      (measurable_radAvgReg₂.comp (measurable_id.prodMk measurable_const))).const_mul _

theorem measurable_latW : Measurable latW := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : IsFC μ
  · have e : (fun x => latW x μ) = fun x => lateralPart x μ := funext fun x => by
      simp only [latW, h, ↓reduceIte]
    rw [e]
    obtain ⟨d, -, r, -, rfl⟩ := h
    exact measurable_lateralPart_apply _
  · have e : (fun x => latW x μ) = fun x => F2.latF (fun y : FieldSample => y) x μ :=
      funext fun x => by simp only [latW, h, ↓reduceIte]
    rw [e]
    exact (measurable_pi_apply μ).comp F2.measurable_latF_id

theorem measurable_PhiF : Measurable PhiF := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : IsAdmissibleH μ
  · have := h.1
    have e : (fun p => PhiF p μ) = fun p : (FieldSample × (ℝ≥0 → ℝ)) × (ℝ≥0 → ℝ) =>
        p.1.1 μ + √2 * (Jmod ((μ.restrict Dsc).map tau) p.2 +
          Jmod ((μ.restrict Dscᶜ).map tauM) p.1.2) :=
      funext fun p => by simp only [PhiF, h, ↓reduceIte]
    rw [e]
    exact ((measurable_pi_apply μ).comp (measurable_fst.comp measurable_fst)).add
      ((((measurable_Jmod _).comp measurable_snd).add
        ((measurable_Jmod _).comp (measurable_snd.comp measurable_fst))).const_mul _)
  · have e : (fun p => PhiF p μ) = fun _ => 0 := funext fun p => by simp [PhiF, h]
    rw [e]
    exact measurable_const

theorem PhiF_apply {p : (FieldSample × (ℝ≥0 → ℝ)) × (ℝ≥0 → ℝ)} {μ : Measure ℂ}
    (h : IsAdmissibleH μ) : PhiF p μ = p.1.1 μ + √2 * (Jmod ((μ.restrict Dsc).map tau) p.2 +
      Jmod ((μ.restrict Dscᶜ).map tauM) p.1.2) := by
  simp only [PhiF, h, ↓reduceIte]

/-! ## Freeness at the forward radial motion of the field itself -/

/-- With the forward radial Brownian motion `p` of `X'` in place of `b`, `PhiF` reads `X'`
minus the random constant `h₁(0)` (times the mass) at every admissible measure, a.s.; hence it is
a free field modulo constants. -/
theorem isFree_PhiF_pos {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X' : Ω → FieldSample} (hX : IsFreeGFFModConstH X' P) :
    IsFreeGFFModConstH (fun ω => PhiF ((F2.latF X' ω, pathOf (radialBMneg X') ω),
      pathOf (radialBMpos X') ω)) P := by
  have hN : Measurable (pathOf (radialBMneg X')) :=
    measurable_pi_iff.2 fun s => (measurable_radialProc hX _).const_mul _
  have hPm : Measurable (pathOf (radialBMpos X')) :=
    measurable_pi_iff.2 fun s => (measurable_radialProc hX _).const_mul _
  have hT : Measurable fun ω =>
      ((F2.latF X' ω, pathOf (radialBMneg X') ω), pathOf (radialBMpos X') ω) :=
    ((F2.measurable_latF hX).prodMk hN).prodMk hPm
  refine E5.isFreeGFFModConstH_of_ae_shift hX (fun ω => -radAvgReg (X' ω) 1)
    (fun μ => (measurable_pi_apply μ).comp (measurable_PhiF.comp hT)) fun μ hμ => ?_
  have hpB := isBrownianReal_radialBMpos hX
  have hnB := isBrownianReal_radialBMneg hX
  have h0 := noAtoms_of_isAdmissibleH hμ 0
  have := hμ.1
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  filter_upwards [F2.ae_radInt_eq hX hμ, hpB.cont, hnB.cont, ae_exists_linear_bound hpB,
    ae_exists_linear_bound hnB] with ω hr hpc hnc hpl hnl
  obtain ⟨C1, hC1, hb1⟩ := hpl
  obtain ⟨C2, hC2, hb2⟩ := hnl
  have hb1' : ∀ t : ℝ≥0, |pathOf (radialBMpos X') ω t| ≤ max C1 C2 * (1 + (t : ℝ)) := fun t =>
    (hb1 t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hb2' : ∀ t : ℝ≥0, |pathOf (radialBMneg X') ω t| ≤ max C1 C2 * (1 + (t : ℝ)) := fun t =>
    (hb2 t).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := integrable_integral_prof (b := pathOf (radialBMpos X') ω)
    (n := pathOf (radialBMneg X') ω) hμ hpc hnc hb1' hb2'
  have hpt : (fun z => prof (pathOf (radialBMpos X') ω) (pathOf (radialBMneg X') ω) z) =ᵐ[μ]
      fun z => radAvgReg (X' ω) ‖z‖ - radAvgReg (X' ω) 1 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with z hz0
    have hz : z ≠ 0 := hz0
    by_cases hz1 : ‖z‖ ≤ 1
    · simp only [prof, hz1, ↓reduceIte, pathOf, radialBMpos, radialProc,
        mul_inv_cancel_left₀ h2, exp_neg_tau hz hz1]
    · have hz1' : 1 < ‖z‖ := lt_of_not_ge hz1
      have e : Real.exp (-(-((tauM z : ℝ)))) = ‖z‖ := by
        rw [neg_neg, tauM, Real.coe_toNNReal _ (Real.log_nonneg hz1'.le),
          Real.exp_log (by linarith)]
      simp only [prof, hz1, ↓reduceIte, pathOf, radialBMneg, radialProc,
        mul_inv_cancel_left₀ h2, e]
  have hint : ∫ z, prof (pathOf (radialBMpos X') ω) (pathOf (radialBMneg X') ω) z ∂μ =
      F2.radInt (X' ω) μ - (μ univ).toReal * radAvgReg (X' ω) 1 := by
    rw [integral_congr_ae hpt, integral_sub hr.1 (integrable_const _), integral_const,
      smul_eq_mul, measureReal_def]
    rfl
  have hlat : F2.latF X' ω μ = X' ω μ - F2.radInt (X' ω) μ :=
    Set.indicator_of_mem (s := {μ : Measure ℂ | IsAdmissibleH μ}) hμ _
  show PhiF _ μ = _
  rw [PhiF_apply hμ]
  dsimp only
  rw [hlat, ← hs.2, hint]
  ring

/-! ## Independence of the lateral part and the two radial motions -/

theorem indepFun_lat_neg_pos {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X' : Ω → FieldSample} (hX : IsFreeGFFModConstH X' P) :
    IndepFun (fun ω => (F2.latF X' ω, pathOf (radialBMneg X') ω))
      (pathOf (radialBMpos X')) P := by
  have hLm := F2.measurable_latF hX
  have hRm : Measurable (fun ω t => radialProc X' t ω) :=
    measurable_pi_iff.2 fun t => measurable_radialProc hX t
  have hnm : Measurable (fun (a : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * a (-(s : ℝ))) :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply _).const_mul _
  have hpm : Measurable (fun (a : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * a s) :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply _).const_mul _
  have hnegR : pathOf (radialBMneg X') =
      (fun (a : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * a (-(s : ℝ))) ∘ (fun ω t => radialProc X' t ω) :=
    rfl
  have hposR : pathOf (radialBMpos X') =
      (fun (a : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * a s) ∘ (fun ω t => radialProc X' t ω) := rfl
  have h12 : Indep (MeasurableSpace.comap (pathOf (radialBMneg X')) inferInstance)
      (MeasurableSpace.comap (pathOf (radialBMpos X')) inferInstance) P :=
    ((IndepFun_iff_Indep _ _ _).1 (indepFun_radialBM hX)).symm
  have hXB : Indep (MeasurableSpace.comap (F2.latF X') inferInstance)
      (MeasurableSpace.comap (fun ω t => radialProc X' t ω) inferInstance) P :=
    (IndepFun_iff_Indep _ _ _).1 (F2.indepFun_latF_radialProc hX)
  have h₁ : MeasurableSpace.comap (pathOf (radialBMneg X')) inferInstance ≤
      MeasurableSpace.comap (fun ω t => radialProc X' t ω) inferInstance := by
    rw [hnegR, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hnm.comap_le
  have h₂ : MeasurableSpace.comap (pathOf (radialBMpos X')) inferInstance ≤
      MeasurableSpace.comap (fun ω t => radialProc X' t ω) inferInstance := by
    rw [hposR, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hpm.comap_le
  have hsup := UnzipInvariance.indep_sup_of_indep h₁ h₂ hRm.comap_le hLm.comap_le h12 hXB
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_left hsup ?_
  exact le_of_eq ((MeasurableSpace.comap_prodMk _ _).trans (sup_comm _ _))

/-! ## Freeness of the decomposed field -/

/-- **The decomposed field is free.** For a continuous-path version `Bt` of a Brownian motion
independent of (raw lateral part, backward radial motion) of `X'`, the field
`PhiF ((latW X', nPath X'), Bt)` is a free field modulo constants. -/
theorem isFree_PhiF_of_indep {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X' : Ω → FieldSample} (hX : IsFreeGFFModConstH X' P)
    {Bt : ℝ≥0 → Ω → ℝ} (hBtm : Measurable (Function.uncurry Bt))
    (hBtpre : IsPreBrownianReal Bt P)
    (hI1 : IndepFun (fun ω => (F2.latF X' ω, pathOf (radialBMneg X') ω)) (pathOf Bt) P) :
    IsFreeGFFModConstH (fun ω => PhiF ((latW (X' ω), nPath (X' ω)), pathOf Bt ω)) P := by
  have hBtpm : Measurable (pathOf Bt) := measurable_pi_iff.2 fun s => hBtm.of_uncurry_left
  have hN : Measurable (pathOf (radialBMneg X')) :=
    measurable_pi_iff.2 fun s => (measurable_radialProc hX _).const_mul _
  have hPm : Measurable (pathOf (radialBMpos X')) :=
    measurable_pi_iff.2 fun s => (measurable_radialProc hX _).const_mul _
  have hLm := F2.measurable_latF hX
  have hTBm : Measurable fun ω => ((F2.latF X' ω, pathOf (radialBMneg X') ω), pathOf Bt ω) :=
    (hLm.prodMk hN).prodMk hBtpm
  have hTPm : Measurable fun ω =>
      ((F2.latF X' ω, pathOf (radialBMneg X') ω), pathOf (radialBMpos X') ω) :=
    (hLm.prodMk hN).prodMk hPm
  have hjoint : P.map (fun ω => ((F2.latF X' ω, pathOf (radialBMneg X') ω), pathOf Bt ω)) =
      P.map (fun ω => ((F2.latF X' ω, pathOf (radialBMneg X') ω), pathOf (radialBMpos X') ω)) := by
    have e1 := (indepFun_iff_map_prod_eq_prod_map_map (hLm.prodMk hN).aemeasurable
      hBtpm.aemeasurable).1 hI1
    have e2 := (indepFun_iff_map_prod_eq_prod_map_map (hLm.prodMk hN).aemeasurable
      hPm.aemeasurable).1 (indepFun_lat_neg_pos hX)
    have hpe : P.map (pathOf Bt) = P.map (pathOf (radialBMpos X')) :=
      map_path_eq hBtpre (isBrownianReal_radialBMpos hX).toIsPreBrownianReal hBtpm hPm
    rw [e1, e2, hpe]
  have hWB : IsFreeGFFModConstH
      (fun ω => PhiF ((F2.latF X' ω, pathOf (radialBMneg X') ω), pathOf Bt ω)) P := by
    refine Cor15Group.isFreeGFFModConstH_of_map_eq
      (fun μ => (measurable_pi_apply μ).comp (measurable_PhiF.comp hTBm)) ?_ (isFree_PhiF_pos hX)
    rw [← Function.comp_def PhiF, ← Function.comp_def PhiF,
      ← Measure.map_map measurable_PhiF hTBm, ← Measure.map_map measurable_PhiF hTPm, hjoint]
  have hVmeas : Measurable fun ω => PhiF ((latW (X' ω), nPath (X' ω)), pathOf Bt ω) :=
    measurable_PhiF.comp (((measurable_latW.comp (measurable_X_pi hX)).prodMk
      (measurable_nPath.comp (measurable_X_pi hX))).prodMk hBtpm)
  obtain ⟨Gv, hGv⟩ := exists_isRegVersion hX
  refine E5.isFreeGFFModConstH_of_ae_shift hWB 0
    (fun μ => (measurable_pi_apply μ).comp hVmeas) fun μ hμ => ?_
  have key : ∀ ω, latW (X' ω) μ = F2.latF X' ω μ →
      PhiF ((latW (X' ω), nPath (X' ω)), pathOf Bt ω) μ =
        PhiF ((F2.latF X' ω, pathOf (radialBMneg X') ω), pathOf Bt ω) μ +
          (μ univ).toReal * (0 : Ω → ℝ) ω := by
    intro ω hl
    rw [PhiF_apply hμ, PhiF_apply hμ, Pi.zero_apply, mul_zero, add_zero]
    dsimp only
    rw [hl]
    rfl
  by_cases hfc : IsFC μ
  · obtain ⟨d, hd, r, hr, rfl⟩ := hfc
    filter_upwards [ae_evalReg_fc hGv d hr] with ω hω
    refine key ω ?_
    simp only [latW, show IsFC (foldedCircle d r) from ⟨d, hd, r, hr, rfl⟩, ↓reduceIte,
      lateralPart, hω]
    exact (Set.indicator_of_mem (s := {μ : Measure ℂ | IsAdmissibleH μ}) hμ
      (fun μ => X' ω μ - F2.radInt (X' ω) μ)).symm
  · refine Eventually.of_forall fun ω => key ω ?_
    simp only [latW, hfc, ↓reduceIte]
    rfl

/-! ## The pathwise identity -/

/-- **Deterministic core of the pathwise identity.** On every folded circle, the wedge field is
`PhiF ((latW x, n), b) + α(−log) + corrField`, when the paths are continuous of linear growth and
the radial path is `√2 b_t + (α − Q)t` for `t ≥ 0`. -/
theorem wedgeField_eq_PhiF {α Q : ℝ} {x : FieldSample} {a : ℝ → ℝ} {b n : ℝ≥0 → ℝ}
    (hb : Continuous b) (hn : Continuous n) {C : ℝ}
    (hbC : ∀ s : ℝ≥0, |b s| ≤ C * (1 + (s : ℝ))) (hnC : ∀ s : ℝ≥0, |n s| ≤ C * (1 + (s : ℝ)))
    (ha : ∀ t : ℝ, 0 ≤ t → a t = √2 * b t.toNNReal + (α - Q) * t)
    (hGc : Continuous (corrField α Q a n)) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    wedgeField (lateralPart x) a Q (foldedCircle d r) =
      (PhiF ((latW x, n), b) + ofFun (fun z => α * -Real.log ‖z‖) + ofFun (corrField α Q a n))
        (foldedCircle d r) := by
  have hμ := isAdmissibleH_foldedCircle hd hr
  have hs := integrable_integral_prof hμ hb hn hbC hnC
  have hlog : Integrable (fun z : ℂ => α * -Real.log ‖z‖) (foldedCircle d r) :=
    (integrable_log_norm_adm hμ).neg.const_mul α
  have hG : Integrable (corrField α Q a n) (foldedCircle d r) :=
    integrable_of_continuousOn_Hbar hGc.continuousOn hμ
  have hl : latW x (foldedCircle d r) = lateralPart x (foldedCircle d r) := by
    simp only [latW, show IsFC (foldedCircle d r) from ⟨d, hd, r, hr, rfl⟩, ↓reduceIte]
  have hVv : PhiF ((latW x, n), b) (foldedCircle d r) = lateralPart x (foldedCircle d r) +
      ∫ z, prof b n z ∂foldedCircle d r := by
    rw [PhiF_apply hμ, hs.2]
    dsimp only
    rw [hl]
  have hk : ∫ z, (Q * (-Real.log ‖z‖) + a (-Real.log ‖z‖)) ∂foldedCircle d r =
      ∫ z, (prof b n z + α * (-Real.log ‖z‖) + corrField α Q a n z) ∂foldedCircle d r :=
    integral_congr_ae (ae_of_all _ fun z => kernel_eq_prof ha z)
  simp only [wedgeField, Pi.add_apply, ofFun]
  rw [hVv, hk, integral_add (f := fun z => prof b n z + α * -Real.log ‖z‖) (hs.1.add hlog) hG,
    integral_add (f := prof b n) (g := fun z => α * -Real.log ‖z‖) hs.1 hlog]
  ring

/-- **The pathwise identity, almost surely** (all folded circles at once). -/
theorem ae_pathwise {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B B' Bt : ℝ≥0 → Ω → ℝ}
    (hX : IsFreeGFFModConstH X' P)
    (hA : IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P)
    (hAe : ∀ ω t, A t ω = wedgePath (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ))
      (fun s => B s ω) (fun s => B' s ω) t)
    (hBm : IsBrownianReal B P) (hBtc : ∀ ω, Continuous fun s => Bt s ω)
    (hBtB : ∀ᵐ ω ∂P, ∀ s, Bt s ω = B s ω) :
    ∀ᵐ ω ∂P,
      Continuous (corrField (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ))
        (fun t => A t ω) (nPath (X' ω))) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → corrField (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ))
        (fun t => A t ω) (nPath (X' ω)) z = 0) ∧
      ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
        F2.zU (Real.sqrt κ) X' A ω (foldedCircle d r) =
          (PhiF ((latW (X' ω), nPath (X' ω)), pathOf Bt ω) + F2.logSingField κ +
            ofFun (corrField (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ))
              (fun t => A t ω) (nPath (X' ω)))) (foldedCircle d r) := by
  have hnB := isBrownianReal_radialBMneg hX
  filter_upwards [hBtB, ae_exists_linear_bound hBm, hnB.cont, ae_exists_linear_bound hnB,
    WedgeCan4.ae_continuous_wedgeProcess hA, hBm.eval_zero_ae_eq_zero]
    with ω hBt hBl hnc hnl hAc hB0
  obtain ⟨C1, hC1, hb1⟩ := hBl
  obtain ⟨C2, hC2, hb2⟩ := hnl
  have hb1' : ∀ t : ℝ≥0, |pathOf Bt ω t| ≤ max C1 C2 * (1 + (t : ℝ)) := fun t => by
    show |Bt t ω| ≤ _
    rw [hBt t]
    exact (hb1 t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hb2' : ∀ t : ℝ≥0, |nPath (X' ω) t| ≤ max C1 C2 * (1 + (t : ℝ)) := fun t =>
    (hb2 t).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hA0 : A 0 ω = 0 := by
    rw [hAe ω 0]
    simp [wedgePath, hB0]
  have hn0 : nPath (X' ω) 0 = 0 := by simp [nPath]
  have hAt : ∀ t : ℝ, 0 ≤ t → A t ω = √2 * pathOf Bt ω t.toNNReal +
      (Real.sqrt κ - 2 / Real.sqrt κ - Qc (Real.sqrt κ)) * t := by
    intro t ht
    rw [hAe ω t]
    simp only [wedgePath, ht, ↓reduceIte, pathOf, hBt]
  have hGc := continuous_corrField (α := Real.sqrt κ - 2 / Real.sqrt κ)
    (Q := Qc (Real.sqrt κ)) hAc hnc hA0 hn0
  refine ⟨hGc, fun z hz => corrField_eq_zero hz, fun d hd r hr => ?_⟩
  exact wedgeField_eq_PhiF (hBtc ω) hnc hb1' hb2' hAt hGc hd hr

/-! ## The decomposition -/

/-! ## Independences from the data -/

theorem pathB_eq {Ω : Type} {A : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hAB : ∀ ω (s : ℝ≥0), A (s : ℝ) ω = √2 * B s ω + c * s) (ω : Ω) :
    (fun s : ℝ≥0 => (A s ω - c * s) / √2) = pathOf B ω := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  funext s
  rw [hAB ω s, add_sub_cancel_right, mul_div_cancel_left₀ _ h2]
  rfl

theorem measurable_Φb (c : ℝ) : Measurable fun (a : ℝ → ℝ) (s : ℝ≥0) => (a s - c * s) / √2 :=
  measurable_pi_iff.2 fun s => ((measurable_pi_apply (s : ℝ)).sub_const _).div_const _

theorem indep_lat_Bt {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B Bt : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hI : IndepFun X' (fun ω t => A t ω) P)
    (hAB : ∀ ω (s : ℝ≥0), A (s : ℝ) ω = √2 * B s ω + c * s)
    (hBtB : ∀ᵐ ω ∂P, ∀ s, Bt s ω = B s ω) :
    IndepFun (fun ω => (F2.latF X' ω, pathOf (radialBMneg X') ω)) (pathOf Bt) P := by
  have hΦ : Measurable fun x : FieldSample =>
      (F2.latF (fun y : FieldSample => y) x, nPath x) :=
    F2.measurable_latF_id.prodMk measurable_nPath
  have h := hI.comp hΦ (measurable_Φb c)
  refine h.congr (Eventually.of_forall fun ω => ?_) ?_
  · rfl
  · filter_upwards [hBtB] with ω hω
    refine (pathB_eq hAB ω).trans (funext fun s => (hω s).symm)

theorem indep_X_Bt {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B Bt B'' : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hIB : IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P)
    (hAB : ∀ ω (s : ℝ≥0), A (s : ℝ) ω = √2 * B s ω + c * s)
    (hBtB : ∀ᵐ ω ∂P, ∀ s, Bt s ω = B s ω) :
    IndepFun (fun ω => (X' ω, pathOf Bt ω)) (pathOf B'') P := by
  have hΨ : Measurable fun q : FieldSample × (ℝ → ℝ) =>
      (q.1, (fun (a : ℝ → ℝ) (s : ℝ≥0) => (a s - c * s) / √2) q.2) :=
    measurable_fst.prodMk ((measurable_Φb c).comp measurable_snd)
  have h := hIB.comp hΨ measurable_id
  refine h.congr ?_ (Eventually.of_forall fun ω => rfl)
  filter_upwards [hBtB] with ω hω
  exact Prod.ext rfl ((pathB_eq hAB ω).trans (funext fun s => (hω s).symm))

theorem wedge_hAB {Ω : Type} {α Q : ℝ} {A : ℝ → Ω → ℝ} {B B' : ℝ≥0 → Ω → ℝ}
    (hAe : ∀ ω t, A t ω = wedgePath α Q (fun s => B s ω) (fun s => B' s ω) t) :
    ∀ ω (s : ℝ≥0), A (s : ℝ) ω = √2 * B s ω + (α - Q) * s := by
  intro ω s
  rw [hAe ω (s : ℝ)]
  simp only [wedgePath, NNReal.coe_nonneg, ↓reduceIte, Real.toNNReal_coe]

/-- The field on the product with a trivial factor is still free. -/
theorem isFree_fst {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → FieldSample} (hV : IsFreeGFFModConstH V P) :
    IsFreeGFFModConstH (fun ω : Ω × Unit => V ω.1) (P.prod (Measure.dirac ())) := by
  have hVm : Measurable V := measurable_pi_iff.2 hV.measurable_coord
  refine Cor15Group.isFreeGFFModConstH_of_map_eq
    (fun μ => (hV.measurable_coord μ).comp measurable_fst) ?_ hV
  have e : (fun ω : Ω × Unit => V ω.1) = V ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map hVm measurable_fst,
    (measurePreserving_fst (μ := P) (ν := Measure.dirac ())).map_eq]

/-! ## The decomposition -/

/-- **`WedgeDecompStmt` holds** (core W-D of D29). -/
theorem wedgeDecompStmt_holds : WedgeDecompStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  obtain ⟨B, B', hBm, hB'm, -, hAe⟩ := id hA
  obtain ⟨Bt, hBtm, hBtc, hBtB⟩ := WedgeRes.exists_good_version hBm
  have hAB := wedge_hAB hAe
  have hBtpm : Measurable (pathOf Bt) := measurable_pi_iff.2 fun s => hBtm.of_uncurry_left
  have hBtpre : IsPreBrownianReal Bt P :=
    hBm.toIsPreBrownianReal.congr fun s => hBtB.mono fun ω h => (h s).symm
  have hVfree := isFree_PhiF_of_indep hX hBtm hBtpre (indep_lat_Bt hI hAB hBtB)
  have hVm' : Measurable fun q : FieldSample × (ℝ≥0 → ℝ) => PhiF ((latW q.1, nPath q.1), q.2) :=
    measurable_PhiF.comp (((measurable_latW.comp measurable_fst).prodMk
      (measurable_nPath.comp measurable_fst)).prodMk measurable_snd)
  have hVind : IndepFun (pathOf B'')
      (fun ω => PhiF ((latW (X' ω), nPath (X' ω)), pathOf Bt ω)) P :=
    ((indep_X_Bt hIB hAB hBtB).comp hVm' measurable_id).symm
  have hmain := ae_pathwise hX hA hAe hBm hBtc hBtB
  exact ⟨Unit, inferInstance, Measure.dirac (), inferInstance,
    fun ω => PhiF ((latW (X' ω.1), nPath (X' ω.1)), pathOf Bt ω.1),
    fun ω => corrField (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) (fun t => A t ω.1)
      (nPath (X' ω.1)), isFree_fst hVfree,
    NonVacuity.nv_isBrownianReal measurePreserving_fst hB, NonVacuity.nv_indepFun_fst hVind,
    F2.ae_fst (P' := Measure.dirac ()) hmain⟩

end WDec
end WedgeUnzip
end QuantumZipper
