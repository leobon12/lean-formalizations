import QuantumZipper.Proofs.Zipper.ZipLen2ContDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2 continuum: the fixed-parameter identity at continuous radius

**Main result** `flowIdentC_holds`: at fixed parameters `p = (u, s, d, r) ∈ flowPar` and fixed
radius `ρ > 0`, almost surely `Φ^c(p, ρ) = X(μ_{p,ρ}) + det^c(p, ρ)`.

This is `F1.flowIdentStmt_holds` (XFlowMechIdent.lean) with the dyadic radius `radius j`
replaced by `ρ`; the circle average of the regular sample at `(z, ρ)` is read off the witness via
`IsRegularWith.evalReg_fc_of_mem` instead of the dyadic limit.

Sources (as in XFlowMechIdent): Duplantier–Sheffield, *Liouville quantum gravity and KPZ*,
Invent. Math. 185 (2011), Prop. 3.1 and its proof (p. 18); Revuz–Yor, 3rd ed., Ch. I, Thm (2.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

open RegCont TwoPoint B2 CoordReg CircleFubini RegSample RegUnif F1

/-- **Fixed-parameter identity at continuous radius** (Duplantier–Sheffield 2011, Prop. 3.1). -/
theorem flowIdentC_holds {κ : ℝ} (hκ : 0 < κ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ F1.flowPar) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∀ᵐ ω ∂P, flowPhiYc κ (X ω) W ρ p = X ω (F1.flowMu W p ρ) + flowDetC κ W p ρ := by
  obtain ⟨hu, hs, -, hr⟩ := hp
  set V : ℝ → ℝ := fun r => W (p.1 - r) - W p.1 with hVdef
  have hV : Continuous V := (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hE : EnergyModulus V p.1 (1 / 12) := energyModulus_holds_timeRev hW hu
  obtain ⟨Vh, hVc, hVV, hreg⟩ := exists_regular_witness_revMap (W := V) (T := p.1) hV hu hX
    (by norm_num : (0 : ℝ) < 1 / 12) hE (2 / Real.sqrt κ) (g₁ := fun _ : ℂ => (0 : ℝ))
    continuous_const (Qc (Real.sqrt κ))
  have hreg' : ∀ᵐ ω ∂P, IsRegularWith
      (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) p.1)
      (fun q => Vh (pr q.1 q.2 0) ω + Dfun V p.1 (2 / Real.sqrt κ) (fun _ : ℂ => (0 : ℝ))
        (Qc (Real.sqrt κ)) q) := by
    filter_upwards [hreg] with ω hω
    rw [ofFun_h0rev_of_zero κ] at hω
    have h := (isRegularWith_coordChange_congr (ofFun (h0rev κ) + X ω)
      (eqOn_fwdMapInv hW hW0 hu) (Qc (Real.sqrt κ))).2 hω
    simpa only [unzippedField] using h
  have havg : ∀ᵐ ω ∂P, ∀ z ∈ Hbar,
      evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) p.1) (foldedCircle z ρ) =
        Vh (pr z ρ 0) ω + ∫ v, PsiU κ W p.1 v ∂foldedCircle z ρ := by
    filter_upwards [hreg'] with ω hω z hz
    rw [hω.evalReg_fc_of_mem hz hρ]
    rw [Dfun_timeRev_eq_integral_PsiU hW hW0 hu κ (hρ)]
  obtain ⟨R₁, hR₁0, hsupp, haeH⟩ := flowNu_ae_mem hW hu hs hr
  have : IsProbabilityMeasure (flowNu W p) := isProbabilityMeasure_flowNu hW hs
  have hfub : ∀ᵐ ω ∂P, ∫ z, Vh (pr z ρ 0) ω ∂flowNu W p =
      X ω ((flowNu W p).bind (pK hV hu ρ)) :=
    ae_integral_Vhat_eq_gen (W := V) (T := p.1) hV hu hX hVc hVV hR₁0 hsupp (hρ)
  have hbind : (flowNu W p).bind (pK hV hu ρ) = flowMu W p ρ := by
    rw [bind_pK_eq (W := V) (T := p.1) hV hu (flowNu W p) ρ]
    unfold flowMu bindFc
    refine Measure.map_congr ?_
    filter_upwards [bindFc_ae_mem_H (flowNu W p) (hρ)] with z hz
    exact (eqOn_fwdMapInv hW hW0 hu hz).symm
  have hL1 : LogBounded (fun v : ℂ => Real.log ‖revMap V p.1 v‖) :=
    logBounded_log_norm_revMap (W := V) (T := p.1) hV hu
  have hL3 : LogBounded (fun v : ℂ => Real.log ‖deriv (revMap V p.1) v‖) :=
    logBounded_log_norm_deriv_revMap (W := V) (T := p.1) hV hu
  have hint2 : Integrable (fun z => ∫ v, PsiU κ W p.1 v ∂foldedCircle z ρ)
      (flowNu W p) := by
    have hc1 : Continuous fun z : ℂ => ∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z ρ :=
      hL1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
        (fun _ => hρ)
    have hc3 : Continuous fun z : ℂ =>
        ∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z ρ :=
      hL3.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
        (fun _ => hρ)
    have hsum : Integrable (fun z : ℂ =>
        (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z ρ) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z ρ))
        (flowNu W p) :=
      ((integrable_of_continuous_ballH hc1 hsupp).const_mul _).add
        ((integrable_of_continuous_ballH hc3 hsupp).const_mul _)
    refine Integrable.congr (f := fun z : ℂ =>
        (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z ρ) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z ρ))
      hsum ?_
    refine Filter.Eventually.of_forall fun z => ?_
    show (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z ρ) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z ρ) =
      ∫ v, PsiU κ W p.1 v ∂foldedCircle z ρ
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hL1.integrable z (hρ)).const_mul (2 / Real.sqrt κ))
        ((hL3.integrable z (hρ)).const_mul (Qc (Real.sqrt κ)))]
    exact integral_congr_ae ((foldedCircle_ae_mem_H z (hρ)).mono fun v hv => by
      have h1 : fwdMapInv W p.1 v = revMap V p.1 v := eqOn_fwdMapInv hW hW0 hu hv
      have h2 : deriv (fwdMapInv W p.1) v = deriv (revMap V p.1) v :=
        Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hv)
          (eqOn_fwdMapInv hW hW0 hu))
      simp only [PsiU, h0rev, h1, h2])
  filter_upwards [havg, hfub] with ω havgω hfubω
  have hint1 : Integrable (fun z => Vh (pr z ρ 0) ω) (flowNu W p) :=
    integrable_of_continuous_ballH ((hVc ω).comp (continuous_pr_fst ρ 0)) hsupp
  have hdet : flowDetC κ W p ρ = ∫ z, (∫ v, PsiU κ W p.1 v ∂foldedCircle z ρ) ∂
      flowNu W p := rfl
  rw [flowPhiYc, hdet, integral_congr_ae
      ((haeH.mono fun z hz => havgω z (show (0 : ℝ) ≤ z.im from hz.le)) : _ =ᵐ[flowNu W p] _),
    integral_add hint1 hint2, hfubω, hbind]

end ZipLen
end B3d
end QuantumZipper
