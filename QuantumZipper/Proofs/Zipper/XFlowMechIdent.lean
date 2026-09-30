import QuantumZipper.Proofs.Zipper.XFlowMechAdm
import QuantumZipper.Proofs.Zipper.UnifUCIdDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FLOW-MECH (2/3): the identity node `F1.FlowIdentStmt`

**Main result** `flowIdentStmt_holds : FlowIdentStmt`: at fixed parameters
`p = (u, s, d, r) ∈ flowPar` and fixed scale `j`, almost surely

`Φ^y_j(p) = ∫ avgReg y_u j dν_p = X(μ_{p,2^{-j}}) + det_j(p)`.

This is the D33 proof `RegUnif.identStmt` (UnifUCIdDet.lean) verbatim, with the pushed dyadic
circle `α_{u,s} = (R_{u,s})_* fc(d, 2^{-k})` replaced by `ν_p = (R_{u,s})_* fc(d, r)`: the proof
only uses that the outer measure is a probability measure, a.s. in `ℍ`, supported in a ball
(`flowNu_ae_mem`), never that its radius is dyadic.

Sources (as in D33): Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185
(2011), Prop. 3.1 and its proof (p. 18); Revuz–Yor, 3rd ed., Ch. I, Thm (2.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint B2 CoordReg CircleFubini RegSample RegUnif

/-- **FLOW-MECH: the fixed-parameter identity.** -/
theorem flowIdentStmt_holds : FlowIdentStmt := by
  intro κ _ _ Ω _ P _ X hX W hW hW0 p hp j
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
      avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) p.1) j z =
        Vh (pr z (radius j) 0) ω + ∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j) := by
    filter_upwards [hreg'] with ω hω z hz
    rw [avgReg, (hω.2.1 j z hz).limUnder_eq]
    simp only [Pi.add_apply]
    rw [Dfun_timeRev_eq_integral_PsiU hW hW0 hu κ (radius_pos j)]
  obtain ⟨R₁, hR₁0, hsupp, haeH⟩ := flowNu_ae_mem hW hu hs hr
  have : IsProbabilityMeasure (flowNu W p) := isProbabilityMeasure_flowNu hW hs
  have hfub : ∀ᵐ ω ∂P, ∫ z, Vh (pr z (radius j) 0) ω ∂flowNu W p =
      X ω ((flowNu W p).bind (pK hV hu (radius j))) :=
    ae_integral_Vhat_eq_gen (W := V) (T := p.1) hV hu hX hVc hVV hR₁0 hsupp (radius_pos j)
  have hbind : (flowNu W p).bind (pK hV hu (radius j)) = flowMu W p (radius j) := by
    rw [bind_pK_eq (W := V) (T := p.1) hV hu (flowNu W p) (radius j)]
    unfold flowMu bindFc
    refine Measure.map_congr ?_
    filter_upwards [bindFc_ae_mem_H (flowNu W p) (radius_pos j)] with z hz
    exact (eqOn_fwdMapInv hW hW0 hu hz).symm
  have hL1 : LogBounded (fun v : ℂ => Real.log ‖revMap V p.1 v‖) :=
    logBounded_log_norm_revMap (W := V) (T := p.1) hV hu
  have hL3 : LogBounded (fun v : ℂ => Real.log ‖deriv (revMap V p.1) v‖) :=
    logBounded_log_norm_deriv_revMap (W := V) (T := p.1) hV hu
  have hint2 : Integrable (fun z => ∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j))
      (flowNu W p) := by
    have hc1 : Continuous fun z : ℂ => ∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z (radius j) :=
      hL1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
        (fun z => radius_pos j)
    have hc3 : Continuous fun z : ℂ =>
        ∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z (radius j) :=
      hL3.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
        (fun z => radius_pos j)
    have hsum : Integrable (fun z : ℂ =>
        (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z (radius j)) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z (radius j)))
        (flowNu W p) :=
      ((integrable_of_continuous_ballH hc1 hsupp).const_mul _).add
        ((integrable_of_continuous_ballH hc3 hsupp).const_mul _)
    refine Integrable.congr (f := fun z : ℂ =>
        (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z (radius j)) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z (radius j)))
      hsum ?_
    refine Filter.Eventually.of_forall fun z => ?_
    show (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z (radius j)) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z (radius j)) =
      ∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j)
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hL1.integrable z (radius_pos j)).const_mul (2 / Real.sqrt κ))
        ((hL3.integrable z (radius_pos j)).const_mul (Qc (Real.sqrt κ)))]
    exact integral_congr_ae ((foldedCircle_ae_mem_H z (radius_pos j)).mono fun v hv => by
      have h1 : fwdMapInv W p.1 v = revMap V p.1 v := eqOn_fwdMapInv hW hW0 hu hv
      have h2 : deriv (fwdMapInv W p.1) v = deriv (revMap V p.1) v :=
        Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hv)
          (eqOn_fwdMapInv hW hW0 hu))
      simp only [PsiU, h0rev, h1, h2])
  filter_upwards [havg, hfub] with ω havgω hfubω
  have hint1 : Integrable (fun z => Vh (pr z (radius j) 0) ω) (flowNu W p) :=
    integrable_of_continuous_ballH ((hVc ω).comp (continuous_pr_fst (radius j) 0)) hsupp
  have hdet : flowDetJ κ W p j = ∫ z, (∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j)) ∂
      flowNu W p := rfl
  rw [flowPhiY, hdet, integral_congr_ae
      ((haeH.mono fun z hz => havgω z (show (0 : ℝ) ≤ z.im from hz.le)) : _ =ᵐ[flowNu W p] _),
    integral_add hint1 hint2, hfubω, hbind]

end F1
end QuantumZipper
