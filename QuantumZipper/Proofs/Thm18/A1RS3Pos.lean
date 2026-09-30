import QuantumZipper.Proofs.Thm18.A1RS3Id

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (4): the rescaling identity at positive smoothing radius (pathwise)

**`evalReg_smear_rescale_pos`**: for `ρ > 0`,
`evalReg y ν^W_{(t,d,s),ρ} = evalReg Z ν^V_{(b²t, μ⁻¹d, μ⁻¹s), bρ} + Q log b`, where `y` has the
regularized averages of `rescale Z Q b`, `W = V(b² ·)/b` and `ψ_W = b⁻¹ ψ_V(μ⁻¹ ·)`.
Both sides are integrals of per-loop pairings against the pushed side circles
(`A1RF.integral_evalReg_fc_eq_nu`, with the per-loop uniform convergence of `y` and of `Z`,
`loopUC_Z`); the per-loop pairings rescale (`evalReg_loop_rescale`) and the pushed side circles
rescale (`a1rMu_scale`). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm F1 B3d.ZipLen

variable {κ : ℝ} {X Z : FieldSample} {FX : ℂ × ℝ → ℝ} {G : ℂ → ℝ} {V : ℝ → ℝ}

/-- **The rescaling identity at positive radius.** -/
theorem evalReg_smear_rescale_pos (hκ : 0 < κ) (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    (hGV : G1zDrvGood V)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hS1 : ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ X V ρ p) L (𝓝[>] 0) (flowBox m))
    {Q b : ℝ} (hb : 0 < b) {y : FieldSample} (hy : avgReg y = avgReg (rescale Z Q b))
    {Fy : ℂ × ℝ → ℝ} (hyF : IsRegularWith y Fy)
    (hGW : G1zDrvGood fun r => V (b ^ 2 * r) / b)
    (hUCy : ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ R : ℝ,
      TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => ∫ u, avgReg y k u
          ∂((foldedCircle z ρ).map (fwdMapInv (fun r => V (b ^ 2 * r) / b) t)))
        (fun z => evalReg y ((foldedCircle z ρ).map (fwdMapInv (fun r => V (b ^ 2 * r) / b) t)))
        atTop (Hbar ∩ closedBall 0 R))
    {left : Bool} {μ : ℝ} (hμ : 0 < μ)
    (hψ : ∀ w ∈ H, g1zSideMap left (fun r => V (b ^ 2 * r) / b) w =
      ((b⁻¹ : ℝ) : ℂ) * g1zSideMap left V (((μ : ℂ))⁻¹ * w))
    {t : ℝ} (ht : 0 < t) (d : ℂ) {s : ℝ} (hs : 0 < s) {ρ : ℝ} (hρ : 0 < ρ) :
    evalReg y (a1rfNu (fun r => V (b ^ 2 * r) / b) t left d s ρ) =
      evalReg Z (a1rfNu V (b ^ 2 * t) left (((μ⁻¹ : ℝ) : ℂ) * d) (μ⁻¹ * s) (b * ρ)) +
        Q * Real.log b := by
  have hbt : 0 < b ^ 2 * t := by positivity
  have hs' : 0 < μ⁻¹ * s := mul_pos (inv_pos.2 hμ) hs
  have hbρ : 0 < b * ρ := mul_pos hb hρ
  have hZF := isRegularWith_Z (κ := κ) hFX hGc hZfc
  have hmapEq := a1rMu_scale hGV hb hGW hμ hψ ht d hs
  set μW := a1rMu (fun r => V (b ^ 2 * r) / b) t left d s with hμW
  set μV := a1rMu V (b ^ 2 * t) left (((μ⁻¹ : ℝ) : ℂ) * d) (μ⁻¹ * s) with hμV
  have hmb : Measurable fun z : ℂ => (b : ℂ) * z := measurable_const_mul _
  -- `μW` is a probability measure carried by `ℍ̄`
  obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hGW ht left
  have hae := TwoPoint.foldedCircle_ae_mem_H d hs
  have hFa : AEMeasurable (fun w => fwdMap (fun r => V (b ^ 2 * r) / b) t
      (g1zSideMap left (fun r => V (b ^ 2 * r) / b) w)) (foldedCircle d s) :=
    hgm.aemeasurable.congr (hae.mono fun w hw => (hEq hw).symm)
  have hμWP : IsProbabilityMeasure μW := (Measure.isProbabilityMeasure_map_iff hFa).2 inferInstance
  obtain ⟨RW, hsuppW⟩ := A1R.exists_ae_bdd_a1rMu hGW ht left d hs
  -- the per-loop pairing of `Z` is continuous and `μV` has compact support
  set F : ℂ → ℝ := fun v => evalReg Z ((foldedCircle v (b * ρ)).map (fwdMapInv V (b ^ 2 * t)))
    with hF
  have hFc : ContinuousOn F Hbar :=
    (continuousOn_evalReg_loop_Z hκ hFX hGc hZfc hGV.1 hGV.2.1 hfy hS1).comp
      (f := fun v : ℂ => ((b ^ 2 * t, v, b * ρ) : ℝ × ℂ × ℝ))
      (show Continuous fun v : ℂ => ((b ^ 2 * t, v, b * ρ) : ℝ × ℂ × ℝ) by fun_prop).continuousOn
      fun v hv => ⟨hbt, hv, hbρ⟩
  obtain ⟨RV, hsuppV⟩ := A1R.exists_ae_bdd_a1rMu hGV hbt left (((μ⁻¹ : ℝ) : ℂ) * d) hs'
  set K : Set ℂ := Hbar ∩ closedBall 0 RV with hK
  have hKc : IsCompact K := (isCompact_closedBall (0 : ℂ) RV).inter_left isClosed_Hbar
  have hKm : MeasurableSet K := isClosed_Hbar.measurableSet.inter measurableSet_closedBall
  have hsuppK : ∀ᵐ v ∂μV, v ∈ K := hsuppV.mono fun v hv =>
    ⟨hv.1, by rw [mem_closedBall, dist_zero_right]; exact hv.2⟩
  have hFint : Integrable F μV := by
    have h := (hFc.mono inter_subset_left).integrableOn_compact' hKc hKm (μ := μV)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hsuppK] at h
  have hFae : AEStronglyMeasurable F (μW.map fun z => (b : ℂ) * z) := by
    rw [hmapEq]; exact hFint.aestronglyMeasurable
  have hFint' : Integrable F (μW.map fun z => (b : ℂ) * z) := by rw [hmapEq]; exact hFint
  have hint2 : Integrable (fun z => F ((b : ℂ) * z)) μW :=
    (integrable_map_measure hFae hmb.aemeasurable).1 hFint'
  have key : ∫ v, F v ∂μV = ∫ z, F ((b : ℂ) * z) ∂μW := by
    rw [← hmapEq, integral_map hmb.aemeasurable hFae]
  -- the per-loop identity
  have hcongr : ∀ᵐ z ∂μW, evalReg y ((foldedCircle z ρ).map
      (fwdMapInv (fun r => V (b ^ 2 * r) / b) t)) = F ((b : ℂ) * z) + Q * Real.log b := by
    filter_upwards [hsuppW] with z hz
    have h := evalReg_loop_rescale hκ hFX hGc hZfc hGV.1 hGV.2.1 hfy hS1 hb hy ht hρ hz.1
    rw [scaledDrv_eq hGV hb] at h
    exact h
  rw [← A1RF.integral_evalReg_fc_eq_nu hyF hGW ht left d hs hρ (hUCy t ht ρ hρ),
    ← A1RF.integral_evalReg_fc_eq_nu hZF hGV hbt left _ hs' hbρ
      (fun R => loopUC_Z hκ hFX hGc hZfc hGV.1 hGV.2.1 hfy hS1 hbt hbρ R)]
  change _ = ∫ v, F v ∂μV + _
  rw [key, integral_congr_ae hcongr, integral_add hint2 (integrable_const _), integral_const]
  simp

end A1RS
end R18
end QuantumZipper
