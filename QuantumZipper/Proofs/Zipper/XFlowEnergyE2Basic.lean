import QuantumZipper.Proofs.Zipper.XFlowEnergyDefs
import QuantumZipper.Proofs.Zipper.UnifUCE2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-E2 (basic): the D33 E2 lemmas with a general circle `fc(d, r)`

The D33 E2 inputs (`RegUnif.alphaUS_ae_facts`, `RegUnif.muUS_eq_map`, `RegUnif.muUS_zero_eq`,
`RegUnif.energyParZero_le`, `RegUnif.energyPar_large_le`) with the dyadic radius `radius k`
replaced by a general radius `r > 0`, and with constants depending on the circle only through a
lower bound `rc ≤ r` and an upper bound `‖d‖ + r ≤ R₀`. The measure `muUS W d k (u, s) ρ` of D33
is the measure `flowMu W (u, s, d, radius k) ρ`; the D33 proofs use `radius k` only through
`0 < radius k` (no step needs `radius k ≤ 1`), so they carry over verbatim.

Sources: as D33 (Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; Duplantier–Sheffield,
Invent. Math. 185 (2011), Prop. 3.1); the proofs are copies of the D33 ones.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace QuantumZipper
namespace F1

open RegCont TwoPoint GFFExist B2 RegUnif CircleFubini FrostmanReg SmoothConv CoordReg

variable {W : ℝ → ℝ}

/-- Pointwise facts of the second unzip map along `fc(d, r)` (general `r > 0`). -/
theorem e2_flowNu_ae_facts (hW : Continuous W) {T Mw : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw)
    (d : ℂ) {r : ℝ} (hr : 0 < r) {P : ℝ × ℝ} (hp : P ∈ tri T) :
    ∀ᵐ z ∂foldedCircle d r, z ∈ H ∧ ‖z‖ ≤ ‖d‖ + r ∧
      z.im ≤ (revMap (vrev W (P.1 + P.2)) P.2 z).im ∧ revMap (vrev W (P.1 + P.2)) P.2 z ∈ H ∧
      ‖revMap (vrev W (P.1 + P.2)) P.2 z‖ ≤ RegCont.revBound (2 * Mw) T (‖d‖ + r) := by
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr,
    TwoPoint.foldedCircle_ae_norm_le d hr.le] with z hz hzn
  have hV := continuous_vrev hW (P.1 + P.2)
  refine ⟨hz, hzn, im_le_im_revMap _ hV z hz hp.2.1, TwoPoint.im_revMap_pos hV hz hp.2.1, ?_⟩
  exact (RegCont.norm_revMap_le_revBound hV hp.2.1
    (fun r _ => abs_vrev_le hM ⟨add_nonneg hp.1 hp.2.1, hp.2.2⟩ r) _ hzn).trans
    (RegCont.revBound_mono (by linarith [hp.1, hp.2.2]))

theorem e1_isProbabilityMeasure_flowNu' (hW : Continuous W) (d : ℂ) (r : ℝ) {T : ℝ} {P : ℝ × ℝ}
    (hp : P ∈ tri T) : IsProbabilityMeasure (flowNu W (P.1, P.2, d, r)) := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (P.1 + P.2)) hp.2.1
  show IsProbabilityMeasure ((foldedCircle d r).map (revMap (vrev W (P.1 + P.2)) P.2))
  infer_instance

theorem e2_flowNu_ae_H_norm (hW : Continuous W) {T Mw : ℝ} (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw)
    (d : ℂ) {r : ℝ} (hr : 0 < r) {P : ℝ × ℝ} (hp : P ∈ tri T) :
    ∀ᵐ x ∂flowNu W (P.1, P.2, d, r), x ∈ H ∧ ‖x‖ ≤ revBound (2 * Mw) T (‖d‖ + r) := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (P.1 + P.2)) hp.2.1
  exact (ae_map_iff hRm.aemeasurable (measurableSet_H_norm_le _)).2
    ((e2_flowNu_ae_facts hW hMw d hr hp).mono fun z hz => ⟨hz.2.2.2.1, hz.2.2.2.2⟩)

theorem e1_flowMu_eq_map' (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) {r : ℝ} (hr : 0 < r) {P : ℝ × ℝ}
    (hp : P ∈ tri T) {ρ : ℝ} (hρ : 0 < ρ) :
    flowMu W (P.1, P.2, d, r) ρ =
      (bindFc (flowNu W (P.1, P.2, d, r)) ρ).map (revMap (vrev W P.1) P.1) := by
  have := e1_isProbabilityMeasure_flowNu' hW d r hp
  unfold flowMu
  refine Measure.map_congr ?_
  filter_upwards [CoordReg.bind_fc_mem_H_norm _ hρ
    ((e2_flowNu_ae_H_norm hW hMw d hr hp).mono fun x hx => hx.2)] with x hx
  exact fwdMapInv_eq_revMap_vrev hW hW0 hp.1 hx.1

/-- `μ_{(u,s,d,r),0} = (ψ_{u+s})_* fc(d, r)` (the D33 `muUS_zero_eq` with a general radius). -/
theorem e1_flowMu_zero_eq' (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) {r : ℝ} (hr : 0 < r) {P : ℝ × ℝ}
    (hp : P ∈ tri T) :
    flowMu W (P.1, P.2, d, r) 0 =
      (foldedCircle d r).map (revMap (vrev W (P.1 + P.2)) (P.1 + P.2)) := by
  have := e1_isProbabilityMeasure_flowNu' hW d r hp
  have hαH := (e2_flowNu_ae_H_norm hW hMw d hr hp).mono fun x hx => hx.1
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (P.1 + P.2)) hp.2.1
  have hψm := TwoPoint.measurable_revMap (continuous_vrev hW P.1) hp.1
  show (bindFc (flowNu W (P.1, P.2, d, r)) 0).map (fwdMapInv W P.1) = _
  rw [bindFc_zero_of_ae_H hαH]
  have e1 : (flowNu W (P.1, P.2, d, r)).map (fwdMapInv W P.1) =
      (flowNu W (P.1, P.2, d, r)).map (revMap (vrev W P.1) P.1) := by
    refine Measure.map_congr ?_
    filter_upwards [hαH] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hp.1 hx
  rw [e1]
  show ((foldedCircle d r).map (revMap (vrev W (P.1 + P.2)) P.2)).map (revMap (vrev W P.1) P.1) = _
  rw [Measure.map_map hψm hRm]
  refine Measure.map_congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with z hz
  exact (revMap_vrev_split hW hp.1 hp.1 hp.2.1 le_rfl hz).symm

/-- **E2 at `ρ = 0`, uniform over circles** (`energyParZero_le` with a general circle
`rc ≤ r`, `‖d‖ + r ≤ R`): `|E| ≤ 2 · timeK M T rc R CH · dist(P,P')^{a/12}`. -/
theorem flowE2_zero_le (hW : Continuous W) (hW0 : W 0 = 0) {T Mw a CH rc R : ℝ} (hT : 0 ≤ T)
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) (hrc : 0 < rc) {d : ℂ} {r : ℝ} (hr : rc ≤ r)
    (hdR : ‖d‖ + r ≤ R) {P P' : ℝ × ℝ} (hp : P ∈ tri T) (hp' : P' ∈ tri T) :
    |kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) 0, flowMu W (P'.1, P'.2, d, r) 0)
        (flowMu W (P.1, P.2, d, r) 0, flowMu W (P'.1, P'.2, d, r) 0)| ≤
      2 * timeK Mw T rc R CH * dist P P' ^ (a / 12) := by
  have hr0 : 0 < r := hrc.trans_le hr
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  set K := timeK Mw T rc R CH with hK
  have hK0 : 0 ≤ K := timeK_nonneg_E2 hMw0 hT hrc hCH
  have hpT : P.1 + P.2 ∈ Icc (0 : ℝ) T := ⟨add_nonneg hp.1 hp.2.1, hp.2.2⟩
  have hp'T : P'.1 + P'.2 ∈ Icc (0 : ℝ) T := ⟨add_nonneg hp'.1 hp'.2.1, hp'.2.2⟩
  rw [e1_flowMu_zero_eq' hW hW0 hMw d hr0 hp, e1_flowMu_zero_eq' hW hW0 hMw d hr0 hp',
    revMap_map_eq_nuT hW hW0 hpT.1 hr0, revMap_map_eq_nuT hW hW0 hp'T.1 hr0]
  refine (abs_kernelCov2_νT_time_unif hW hW0 hrc hMw ha ha1 hCH hH hr hdR hpT hp'T).trans ?_
  set δ := dist P P' with hδ
  have hδ0 : 0 ≤ δ := dist_nonneg
  have h1 : |P.1 + P.2 - (P'.1 + P'.2)| ≤ 2 * δ := by
    have h2 : |P.1 - P'.1| ≤ δ := by
      rw [← Real.dist_eq, hδ, Prod.dist_eq]; exact le_max_left _ _
    have h3 : |P.2 - P'.2| ≤ δ := by
      rw [← Real.dist_eq, hδ, Prod.dist_eq]; exact le_max_right _ _
    rw [show P.1 + P.2 - (P'.1 + P'.2) = (P.1 - P'.1) + (P.2 - P'.2) by ring]
    exact (abs_add_le _ _).trans (by linarith)
  have h2 := Real.rpow_le_rpow (abs_nonneg _) h1 (by positivity : (0 : ℝ) ≤ a / 12)
  have h3 : (2 * δ) ^ (a / 12 : ℝ) ≤ 2 * δ ^ (a / 12) := by
    rw [Real.mul_rpow (by norm_num) hδ0]
    have h2a : (2 : ℝ) ^ (a / 12) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show a / 12 ≤ 1 by linarith)
      rwa [Real.rpow_one] at this
    have := mul_le_mul_of_nonneg_right h2a (Real.rpow_nonneg hδ0 (a / 12))
    linarith
  refine (mul_le_mul_of_nonneg_left (h2.trans h3) hK0).trans (le_of_eq ?_)
  ring

/-- **The time modulus at radii `ρ ≥ r₀`** (strip form), general circle (`energyPar_large_le`
with `radius k ↦ r`, `rc ≤ r`, `‖d‖ + r ≤ R₀`, `revBound (2Mw) T (‖d‖ + r) ≤ Ra`). -/
theorem flowE2_large_le {T a CH : ℝ} (hWH : HolderDrv W T a CH) {Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) {d : ℂ} {r rc R₀ Ra : ℝ} (hrc : 0 < rc)
    (hr : rc ≤ r) (hdR : ‖d‖ + r ≤ R₀) (hRa : revBound (2 * Mw) T (‖d‖ + r) ≤ Ra)
    {P P' : ℝ × ℝ} (hp : P ∈ tri T)
    (hp' : P' ∈ tri T) (hpp : dist P P' ≤ 1 / 2) {r₀ ρ τ : ℝ} (hr₀ : 0 < r₀) (hρ : r₀ ≤ ρ)
    (hρ1 : ρ ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ)
        (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ) ≤
      2 * (2 * (timeK Mw T r₀ (Ra + 1) CH * dist P P' ^ (a / 12)) +
          2 * (spaceK Mw T r₀ (Ra + 1) *
            (4 * (CH + 2) * (1 + Real.sqrt (R₀ ^ 2 + 8 * T)) * dist P P' ^ a /
              τ ^ 2) ^ (1 / 12 : ℝ))) +
        2 * ((2 * (timeK Mw T r₀ (Ra + 1) CH * dist P P' ^ (a / 12)) +
            2 * (spaceK Mw T r₀ (Ra + 1) * (2 * Ra) ^ (1 / 12 : ℝ))) *
          (18 * Real.sqrt (τ / rc)) ^ 2) := by
  have hWH' := hWH
  obtain ⟨hW, hW0, ha, ha1, hCH, hH⟩ := hWH'
  have hr0 : 0 < r := hrc.trans_le hr
  have hT : 0 ≤ T := hp.1.trans (by linarith [hp.2.1, hp.2.2])
  have hM0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  have hu : P.1 ∈ Icc (0 : ℝ) T := ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩
  have hu' : P'.1 ∈ Icc (0 : ℝ) T := ⟨hp'.1, by linarith [hp'.2.1, hp'.2.2]⟩
  have hρ0 : 0 < ρ := hr₀.trans_le hρ
  have hδu : |P.1 - P'.1| ≤ dist P P' := by
    rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _
  rw [e1_flowMu_eq_map' hW hW0 hMw d hr0 hp hρ0, e1_flowMu_eq_map' hW hW0 hMw d hr0 hp' hρ0]
  have hwm := TwoPoint.measurable_revMap (continuous_vrev hW (P.1 + P.2)) hp.2.1
  have hwm' := TwoPoint.measurable_revMap (continuous_vrev hW (P'.1 + P'.2)) hp'.2.1
  have hψ := TwoPoint.measurable_revMap (continuous_vrev hW P.1) hp.1
  have hψ' := TwoPoint.measurable_revMap (continuous_vrev hW P'.1) hp'.1
  have hf := e2_flowNu_ae_facts hW hMw d hr0 hp
  have hf' := e2_flowNu_ae_facts hW hMw d hr0 hp'
  set R := Ra + 1 with hR
  have htK := timeK_nonneg_E2 (R := R) hM0 hT hr₀ hCH
  have hsK := spaceK_nonneg_E2 (R := R) hM0 hT hr₀
  have hRa0 : 0 ≤ Ra := (revBound_nonneg (by linarith) hT).trans hRa
  set Kb := 2 * (timeK Mw T r₀ R CH * dist P P' ^ (a / 12)) +
    2 * (spaceK Mw T r₀ R *
      (4 * (CH + 2) * (1 + Real.sqrt (R₀ ^ 2 + 8 * T)) * dist P P' ^ a /
        τ ^ 2) ^ (1 / 12 : ℝ)) with hKb
  set Ks := 2 * (timeK Mw T r₀ R CH * dist P P' ^ (a / 12)) +
    2 * (spaceK Mw T r₀ R * (2 * Ra) ^ (1 / 12 : ℝ)) with hKs
  have hKb0 : 0 ≤ Kb := by rw [hKb]; positivity
  have hKs0 : 0 ≤ Ks := by rw [hKs]; positivity
  have key := energy_mixFc_le_strip (A := foldedCircle d r) hwm hwm' hψ hψ'
    (ρ := ρ) (ρ' := ρ) (α := 1 / 3) (C := RegCont.frostC T r₀ R) (B := revBound (2 * Mw) T R)
    (by norm_num) (by unfold RegCont.frostC; positivity) (revBound_nonneg (by linarith) hT)
    (by
      filter_upwards [hf, hf'] with z hz hz'
      exact ⟨(goodM_pushed_circle hW hW0 hMw hu hr₀ hρ (R := R)
          (by linarith [hz.2.2.2.2])).2,
        (goodM_pushed_circle hW hW0 hMw hu' hr₀ hρ (R := R) (by linarith [hz'.2.2.2.2])).2⟩)
    (Kb := Kb) (Ks := Ks) (τ := τ) hKb0 hKs0
    (by
      filter_upwards [hf, hf'] with z hz hz' hzτ
      have hzR : ‖revMap (vrev W (P.1 + P.2)) P.2 z‖ + ρ ≤ R := by linarith [hz.2.2.2.2]
      have hzR' : ‖revMap (vrev W (P'.1 + P'.2)) P'.2 z‖ + ρ ≤ R := by
        linarith [hz'.2.2.2.2]
      rw [← (goodM_pushed_circle hW hW0 hMw hu hr₀ hρ hzR).1,
        ← (goodM_pushed_circle hW hW0 hMw hu' hr₀ hρ hzR').1]
      exact energy_nuT_pair_le hW hW0 hr₀ hMw ha ha1 hCH hH hρ hzR hzR' hu hu' hδu
        (norm_RUS_sub_le_holder hWH hT hτ hτ1 hp hp' hpp hz.1 hzτ (hz.2.1.trans hdR)))
    (by
      filter_upwards [hf, hf'] with z hz hz' _
      have hzR : ‖revMap (vrev W (P.1 + P.2)) P.2 z‖ + ρ ≤ R := by linarith [hz.2.2.2.2]
      have hzR' : ‖revMap (vrev W (P'.1 + P'.2)) P'.2 z‖ + ρ ≤ R := by
        linarith [hz'.2.2.2.2]
      rw [← (goodM_pushed_circle hW hW0 hMw hu hr₀ hρ hzR).1,
        ← (goodM_pushed_circle hW hW0 hMw hu' hr₀ hρ hzR').1]
      refine energy_nuT_pair_le hW hW0 hr₀ hMw ha ha1 hCH hH hρ hzR hzR' hu hu' hδu ?_
      refine (norm_sub_le _ _).trans ?_
      linarith [hz.2.2.2.2, hz'.2.2.2.2])
  refine key.trans ?_
  -- the strip mass
  set m := (foldedCircle d r {z : ℂ | z.im < τ}).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hm1 : m ≤ 18 * Real.sqrt (τ / r) := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine le_trans (measure_mono_ae ?_) (foldedCircle_strip_le d hr0 hτ)
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr0] with z hz
    exact fun (hzτ : z.im < τ) => show |z.im| < τ by
      rw [abs_of_pos (show 0 < z.im from hz)]; exact hzτ
  have hm1' : m ≤ 18 * Real.sqrt (τ / rc) := by
    refine hm1.trans ?_
    have : τ / r ≤ τ / rc := div_le_div_of_nonneg_left hτ.le hrc hr
    have := Real.sqrt_le_sqrt this
    linarith
  have hm2 : m ^ 2 ≤ (18 * Real.sqrt (τ / rc)) ^ 2 := pow_le_pow_left₀ hm0 hm1' 2
  have e1 := Real.sq_sqrt hKb0
  have e2 := Real.sq_sqrt hKs0
  have h3 : (Real.sqrt Kb + Real.sqrt Ks * m) ^ 2 ≤
      2 * Real.sqrt Kb ^ 2 + 2 * (Real.sqrt Ks ^ 2 * m ^ 2) := by
    nlinarith [sq_nonneg (Real.sqrt Kb - Real.sqrt Ks * m)]
  rw [e1, e2] at h3
  have h4 := mul_le_mul_of_nonneg_left hm2 hKs0
  linarith

end F1
end QuantumZipper
