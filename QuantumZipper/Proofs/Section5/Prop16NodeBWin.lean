import QuantumZipper.Proofs.Section5.Prop16NodeBGeom
import QuantumZipper.Proofs.LQG.LocalRule

/-!
# Proposition 1.6, Palm node B′: the local Palm formula on a window of the free arc

`palm_formula_prop16_window`: for the data of Proposition 1.6 and a window
`[a', b'] ⊆ (a, b)`, the Palm formula
`E ∫_{(a',b')} G((h0 + X)(μ_j), x) ν(dx) = ∫_{(a',b')} ρ(x) E G((h0 + X + (γ/2)G_D(x,·))(μ_j), x) dx`,
`ρ(x) = exp(γ h0(x)/2 + γ² k(x,x)/8)` (`k` the M6 kernel), for measurable `G ≥ 0` and
admissible `μ_j` carried by the window set `palmWinK a' b' g`, assuming

* `hL1`: the `L¹` convergence `PalmFree.BdryL1ConvCc γ h0 X P ν a' b'` of the boundary
  approximations of the **actual** field `h0 + X` to `ν` on `[a', b']` (item (2)); it is
  transferred to the masked field (`bdryL1ConvCc_maskK`, locality of `avgReg`);
* `hreg`: the a.s. regularity of the masked field at the folded circles centred on the window
  (the hypothesis `hreg` of the abstract Palm formula).

Own bookkeeping (locality: `LocalRule.avgReg_congr_local`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

section

variable {a' b' g : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Folded circles of radius `≤ g/4` centred within `g/4` of the window are carried by
`palmWinK`. -/
theorem foldedCircle_palmWinK_compl' {t : ℝ} (ht : t ∈ Icc a' b') {c : ℂ} (hc : c ∈ Hbar)
    (hct : dist c (t : ℂ) < g / 4) {r : ℝ} (hr : 0 < r) (hrg : r ≤ g / 4) :
    foldedCircle c r (palmWinK a' b' g)ᶜ = 0 := by
  refine measure_mono_null (compl_subset_compl.2 fun u hu => ⟨?_, hu.2⟩)
    (K3.foldedCircle_compl_eq_zero hc hr.le)
  refine mem_cthickening_of_dist_le u t _ _ ⟨t, ht, rfl⟩ ?_
  have := mem_closedBall.1 hu.1
  linarith [dist_triangle u c (t : ℂ)]

/-- Locality: at small scales, the regularized averages of the masked field `m + maskK X` and
of the actual field `h0 + X` agree on the window. -/
theorem avgReg_maskK_eq {m h0 : ℂ → ℝ} (hmK : EqOn m h0 (palmWinK a' b' g)) (hg : 0 < g)
    {t : ℝ} (ht : t ∈ Icc a' b') {n : ℕ} (hn : radius n ≤ g / 4) (ω : Ω) :
    avgReg (ofFun m + maskK (palmWinK a' b' g) X ω) n (t : ℂ) =
      avgReg (ofFun h0 + X ω) n (t : ℂ) := by
  refine LocalRule.avgReg_congr_local n (by positivity : (0 : ℝ) < g / 4) (fun c hc hct => ?_)
    (show (0 : ℝ) ≤ ((t : ℂ)).im by simp)
  have hK := foldedCircle_palmWinK_compl' ht hc hct (radius_pos n) hn
  have hA : KAdm (palmWinK a' b' g) (foldedCircle c (radius n)) :=
    ⟨isAdmissibleH_foldedCircle hc (radius_pos n), hK⟩
  simp only [Pi.add_apply, maskK_of_KAdm hA]
  rw [ofFun_eq_of_eqOn hmK hK]

/-- **`L¹` convergence transfers from the actual field to the masked field.** -/
theorem bdryL1ConvCc_maskK {γ : ℝ} {m h0 : ℂ → ℝ} (hmK : EqOn m h0 (palmWinK a' b' g))
    (hg : 0 < g) {ν : Ω → Measure ℝ} (hL1 : PalmFree.BdryL1ConvCc γ h0 X P ν a' b') :
    PalmFree.BdryL1ConvCc γ m (maskK (palmWinK a' b' g) X) P ν a' b' := by
  intro f hf hfc hfab
  refine (hL1 f hf hfc hfab).congr' ?_
  have hr : Tendsto radius atTop (𝓝 0) := tendsto_radius_zero_nodeB
  filter_upwards [hr.eventually (ge_mem_nhds (show (0 : ℝ) < g / 4 by positivity))] with n hn
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have hres : (bdryApprox γ (ofFun h0 + X ω) n).restrict (Icc a' b') =
      (bdryApprox γ (ofFun m + maskK (palmWinK a' b' g) X ω) n).restrict (Icc a' b') := by
    unfold bdryApprox
    rw [restrict_withDensity measurableSet_Icc, restrict_withDensity measurableSet_Icc]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [avgReg_maskK_eq hmK hg ht hn ω]
  have e : ∀ μ : Measure ℝ, ∫ x, f x ∂μ = ∫ x in Icc a' b', f x ∂μ := fun μ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hfab x hx).symm
  simp only
  rw [e (bdryApprox γ (ofFun h0 + X ω) n), e (bdryApprox γ (ofFun m + _) n), hres]

end

/-! ## The window Palm formula for the data of Proposition 1.6 -/

end Prop16Asm

end QuantumZipper
