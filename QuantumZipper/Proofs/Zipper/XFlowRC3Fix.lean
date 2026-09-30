import QuantumZipper.Proofs.Zipper.XFlowRC3Reduce
import QuantumZipper.Proofs.GFF.CoordRegComp
import QuantumZipper.Proofs.GFF.CoordRegCompFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-FLOW-RC3: the fixed-parameter node `XFlowRC3FixStmt`, proved

For each fixed `p = (u, s, d, r)` (`u, s ≥ 0`, `d ∈ ℍ̄`, `r > 0`), almost surely
`evalReg x_u ν_p = x_u ν_p`, where `x = X + α₀(−log|·|)`, `x_u = F2.unzX κ X W u` and
`ν_p = (R_{u,s})_* fc(d, r)`.

Route: this is the `Γ⁰` fixed-parameter RC3 `CoordRegComp.ae_evalReg_Yf_push` (Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1, through the RC3-general
law `CoordRegComp.ae_evalReg_comp_fc`; Sheffield arXiv:1012.4797 §5.2, pp. 57–59), whose proof
never uses the particular deterministic part `𝔥₀ = (2/√κ) log|·|`: the fixed-driver law
`ae_evalReg_comp_fc` holds for any field `a·log|·| + g₁ + X` (`g₁` continuous), and the transfer to
the Brownian driver (`ae_lhsC_eq_rhsC_random`) is generic in the deterministic part. We restate
the transfer for a general deterministic part (`ae_evalReg_push_gen`, a verbatim generalization of
`ae_evalReg_Yf_push`) and apply it with `a = −α₀ = 2/√κ − √κ`, `g₁ = 0`
(`logSing_eq_logAdd`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open CoordRegComp CoordReg CharFun B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
/-- `CoordRegComp.hfix_of_law` for a general deterministic part `G`. -/
theorem hfix_of_law_gen (G : ℂ → ℝ) (hT : 0 ≤ T) (ht : 0 ≤ t) (hs : 0 ≤ T - t) (htT : t ≤ T)
    {μ : Measure ℂ}
    (hlaw : ∀ Vf V A : ℝ → ℝ, Continuous Vf → Continuous V → Continuous A →
      EqOn Vf V (Icc 0 t) → (∀ r ∈ Icc (0 : ℝ) (T - t), Vf (t + r) - Vf t = A r) →
      ∀ᵐ ω ∂P, evalReg (coordChange (ofFun G + X ω) (revMap A (T - t))
          (Qc (Real.sqrt κ))) (μ.map (revMap V t)) =
        coordChange (ofFun G + X ω) (revMap A (T - t)) (Qc (Real.sqrt κ))
          (μ.map (revMap V t)))
    (f : C(Icc (0 : ℝ) T, ℝ)) :
    ∀ᵐ ω ∂P, lhsC κ hT ht hs G (Qc (Real.sqrt κ)) μ (f, X ω) =
      rhsC κ hT ht hs G (Qc (Real.sqrt κ)) μ (f, X ω) := by
  unfold lhsC rhsC
  refine hlaw (Wof κ T hT (revPath hT T T f)) (Wof κ t ht (revPath hT T t f))
    (Wof κ (T - t) hs (revPath hT (T - t) (T - t) f)) (continuous_Wof κ T hT (revPath hT T T f))
    (continuous_Wof κ t ht (revPath hT T t f))
    (continuous_Wof κ (T - t) hs (revPath hT (T - t) (T - t) f)) (fun r hr => ?_) (fun r hr => ?_)
  · rw [Wof_revPath κ hT hT T f ⟨hr.1, hr.2.trans htT⟩, Wof_revPath κ hT ht T f hr]
  · rw [Wof_revPath κ hT hT T f ⟨by linarith [hr.1], by linarith [hr.2]⟩,
      Wof_revPath κ hT hT T f ⟨ht, htT⟩, Wof_revPath κ hT hs (T - t) f hr,
      show T - (t + r) = T - t - r by ring]
    ring

/-- **`CoordRegComp.ae_evalReg_Yf_push` for a general deterministic part `G`**: the RC3
composition law for `coordChange (ofFun G + X) f_{T−t}⁻¹ Q` at `μ.map (revMap V t)`, from the
fixed-driver law. -/
theorem ae_evalReg_push_gen (G : ℂ → ℝ) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T)
    {μ : Measure ℂ} [IsProbabilityMeasure μ] (hμH : ∀ᵐ z ∂μ, z ∈ H)
    (hlaw : ∀ Vf V A : ℝ → ℝ, Continuous Vf → Continuous V → Continuous A →
      EqOn Vf V (Icc 0 t) → (∀ r ∈ Icc (0 : ℝ) (T - t), Vf (t + r) - Vf t = A r) →
      ∀ᵐ ω ∂P, evalReg (coordChange (ofFun G + X ω) (revMap A (T - t))
          (Qc (Real.sqrt κ))) (μ.map (revMap V t)) =
        coordChange (ofFun G + X ω) (revMap A (T - t)) (Qc (Real.sqrt κ))
          (μ.map (revMap V t))) :
    ∀ᵐ ω ∂P, evalReg (coordChange (ofFun G + X ω) (fwdMapInv (drive κ B ω) (T - t))
        (Qc (Real.sqrt κ))) (μ.map (revMap (Vr κ T B ω) t)) =
      coordChange (ofFun G + X ω) (fwdMapInv (drive κ B ω) (T - t)) (Qc (Real.sqrt κ))
        (μ.map (revMap (Vr κ T B ω) t)) := by
  have hT : 0 ≤ T := ht.trans htT
  have hs : 0 ≤ T - t := sub_nonneg.2 htT
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := CharFun.exists_good_version hB
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  have hr := ae_lhsC_eq_rhsC_random κ hT ht hs G (Qc (Real.sqrt κ)) μ hX hμH
    (measurable_pathC T hB₁m hB₁c) (indepFun_pathC T hind₁ hB₁c)
    (hfix_of_law_gen G hT ht hs htT hlaw)
  filter_upwards [hr, hB₁eq, hB.eval_zero_ae_eq_zero] with ω h h1 h0
  set f := pathC T B₁ hB₁c ω with hf
  have hPj : ∀ x (hx : x ∈ Icc (0 : ℝ) T), f (projIcc 0 T hT x) = B x.toNNReal ω := by
    intro x hx
    rw [projIcc_of_mem hT hx]
    exact h1 _
  have hcB : Continuous fun s => B s ω := by
    have : (fun s => B s ω) = fun s => B₁ s ω := funext fun s => (h1 s).symm
    rw [this]; exact hB₁c ω
  have hW : Continuous (drive κ B ω) := continuous_const.mul (hcB.comp continuous_real_toNNReal)
  have hW0 : drive κ B ω 0 = 0 := by
    have : B 0 ω = 0 := h0
    simp [drive, this]
  have hFeq : revMap (Vr κ T B ω) t = revMap (Wof κ t ht (revPath hT T t f)) t :=
    funext fun z => ReverseFlow.revMap_congr_drive z fun r hr => by
      rw [Wof_revPath κ hT ht T f hr, Vr, vrev_of_mem ⟨hr.1, hr.2.trans htT⟩,
        hPj _ ⟨by linarith [hr.2], by linarith [hr.1]⟩, hPj _ ⟨hT, le_rfl⟩]
      simp only [drive]; ring
  have hEq : EqOn (fwdMapInv (drive κ B ω) (T - t))
      (revMap (Wof κ (T - t) hs (revPath hT (T - t) (T - t) f)) (T - t)) H := fun z hz => by
    rw [eqOn_fwdMapInv hW hW0 hs hz]
    exact ReverseFlow.revMap_congr_drive z fun r hr => by
      show drive κ B ω (T - t - r) - drive κ B ω (T - t) = _
      rw [Wof_revPath κ hT hs (T - t) f hr, hPj _ ⟨by linarith [hr.2], by linarith [hr.1]⟩,
        hPj _ ⟨hs, by linarith⟩]
      simp only [drive]; ring
  have hνH : ∀ᵐ z ∂(μ.map (revMap (Wof κ t ht (revPath hT T t f)) t)), z ∈ H :=
    (ae_map_iff (TwoPoint.measurable_revMap (continuous_Wof κ t ht _) ht).aemeasurable
      isOpen_H.measurableSet).2
      (hμH.mono fun z hz => TwoPoint.im_revMap_pos (continuous_Wof κ t ht _) hz ht)
  rw [hFeq, evalReg_coordChange_congr _ hEq, coordChange_congr_of_eqOn_H _ hEq _ hνH]
  exact h

/-- `X + α₀(−log|·|) = (−α₀)·log|·| + 0 + X`, in the form of `CoordRegComp.ae_evalReg_comp_fc`. -/
theorem logSing_eq_logAdd (κ : ℝ) (x : FieldSample) :
    x + F2.logSingField κ = ofFun (fun v => -(Real.sqrt κ - 2 / Real.sqrt κ) * Real.log ‖v‖ +
      (fun _ => (0 : ℝ)) v) + x := by
  funext μ
  have hfun : (fun z : ℂ => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖) =
      fun v => -(Real.sqrt κ - 2 / Real.sqrt κ) * Real.log ‖v‖ + (fun _ => (0 : ℝ)) v :=
    funext fun z => by ring
  show x μ + ∫ z, (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖ ∂μ =
    (∫ z, (-(Real.sqrt κ - 2 / Real.sqrt κ) * Real.log ‖z‖ + (fun _ => (0 : ℝ)) z) ∂μ) + x μ
  rw [hfun]
  ring

/-- **`XFlowRC3FixStmt` holds**: fixed-parameter RC3 of the unzipped `x`-field at the pushed
folded circle. -/
theorem xFlowRC3FixStmt_holds : XFlowRC3FixStmt := by
  intro κ _ _ Ω _ P _ B X hB hX hind p hp
  obtain ⟨hu, hs, -, hr⟩ := hp
  have key := ae_evalReg_push_gen (P := P) (κ := κ) (T := p.1 + p.2.1) (t := p.2.1)
    (fun v => -(Real.sqrt κ - 2 / Real.sqrt κ) * Real.log ‖v‖ + (fun _ => (0 : ℝ)) v)
    hB hX hind hs (le_add_of_nonneg_left hu) (μ := foldedCircle p.2.2.1 p.2.2.2)
    (TwoPoint.foldedCircle_ae_mem_H _ hr) fun Vf V A hVf hV hA hVV hAV =>
      ae_evalReg_comp_fc hX _ continuous_const _ hVf hV hA hs
        (sub_nonneg.2 (le_add_of_nonneg_left hu)) hVV hAV _ hr
  refine key.mono fun ω hω => ?_
  rw [add_sub_cancel_right] at hω
  simp only [flowRegSide, flowRawSide, flowNu, F2.unzX, unzippedField]
  rw [logSing_eq_logAdd]
  exact hω

end F1
end QuantumZipper
