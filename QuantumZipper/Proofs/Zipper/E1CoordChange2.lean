import QuantumZipper.Proofs.Zipper.E1CoordChange
import QuantumZipper.Proofs.GFF.CoordRegRandom
import QuantumZipper.Proofs.GFF.CoordRegLog
import QuantumZipper.Proofs.LQG.PalmNormLocal
import QuantumZipper.Proofs.LQG.RegularSample
import QuantumZipper.Proofs.LQG.BoundaryExistenceAS

/-!
# E1-CC (part 2): the `𝔥₀` term and the full coordinate change on a live window

`handoff/E1-PLAN.md`, sub-node **E1-CC**. Part 1 (`E1CoordChange.lean`) transported M4-T4
(Duplantier–Sheffield, *LQG and KPZ*, arXiv:0808.1560, Prop. 3.1; boundary version, node M4-T4)
to the reverse map. Here we add the `𝔥₀ = (2/√κ) log|·|` term on both sides, by the additive
rule (5.1) (`LocalRule.qBoundaryMeasureOn_add_ofFun`), and assemble E1-CC:

```
∀ᵐ ω' ∂P', ∀ g, Measurable g →
  ∫⁻ x, g (F x) ∂qBoundaryMeasureOn √κ (hFix κ v t (X' ω')) (Ioo a b)
    = ∫⁻ y, g y ∂qBoundaryMeasureOn √κ (ofFun (h0rev κ) + X' ω') (Ioo (F a) (F b))
```

(`F = realRevMap v t`). Paper: Sheffield, arXiv:1012.4797, Thm 1.2/(1.3) (the coordinate rule
`h ↦ h∘ψ + Q log|ψ'|`) together with `e^{γ𝔥₀(y)/2} = |y|`.

* **x-side** (`ae_hFix_fc_eq`, `ae_avgReg_hFix_eq`): at every folded circle, a.s.,
  `hFix(fc) = coordChange X' F Q (fc) + ∫ 𝔥₀∘ψ dfc`. This is the split
  `evalReg (ofFun 𝔥₀ + X') ν = ∫ 𝔥₀ dν + X' ν` of RC1 (`CoordReg.ae_evalReg_h0rev_eq_frostman'`,
  `FrostmanReg.ae_evalReg_eq_frostman`) for `ν = F_* fc(c,ρ)` (support and Frostman bound:
  `CoordReg.pushK_support`, `CoordReg.pushK_frostman`). The regularized averages `avgReg` only
  read folded circles with dyadic centres, a countable family, so a.s. the two fields have the
  same `avgReg`, hence the same `bdryApprox` and the same local boundary measure. Then the
  additive rule applies to the regular sample `coordChange X' F Q`
  (`CoordReg.ae_isRegularSample_coordChange_revMap'`) with `φ = 𝔥₀ ∘ ψ`, continuous near the
  window because `F[a,b] ⊂ (−∞,0)`.
* **y-side**: the free field `X'` is a.s. a regular sample (`RegSample.ae_isRegularSample`, M4-R3),
  so the additive rule applies directly with `φ = 𝔥₀`, continuous off `0`.

(The E1-CC handoff claimed `IsRegularSample X'` fails for the free field modulo constants; this is
not so: M4-R3 proves it a.s.) The bookkeeping (countable family, sign of `F`) is our own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open RevMapExtension

variable {Ω : Type*} [MeasurableSpace Ω] {P' : Measure Ω}
variable {κ t a b : ℝ} {v : ℝ → ℝ} {X' : Ω → FieldSample}

/-! ## 1. Sign of the reverse flow on negative live points -/

/-- A live negative point stays negative (the real solution never vanishes and starts at
`x − v 0 = x`; intermediate value theorem). Own elementary argument. -/
theorem realRevMap_neg (hv : Continuous v) (hv0 : v 0 = 0) (ht : 0 ≤ t) {x : ℝ} (hx : x < 0)
    (hl : IsLive v t x) : realRevMap v t x < 0 := by
  obtain ⟨u, hu⟩ := exists_isRealRevSol_of_isLive hl
  rw [RealLine.realRevMap_eq hv hu ht le_rfl]
  have hu0 : u 0 = x := by rw [RealLine.isRealRevSol_zero hu ht, hv0, sub_zero]
  by_contra hpos
  rw [not_lt] at hpos
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht hu.1
    (show (0 : ℝ) ∈ Icc (u 0) (u t) from ⟨by rw [hu0]; exact hx.le, hpos⟩)
  exact (hu.2 s hs).1 hs0

/-- `h0rev κ` is continuous off the origin. -/
theorem continuousOn_h0rev (κ : ℝ) : ContinuousOn (h0rev κ) {z : ℂ | z ≠ 0} := by
  unfold h0rev
  exact continuousOn_const.mul (Real.continuousOn_log.comp continuous_norm.continuousOn
    fun z hz => norm_ne_zero_iff.2 hz)

/-! ## 2. The x-side field identity at folded circles -/

/-- **RC1 split at one folded circle.** For `ψ = revMap v t` on `ℍ`, almost surely
`hFix(fc(c,ρ)) = coordChange X' F Q (fc(c,ρ)) + ∫ 𝔥₀∘ψ dfc(c,ρ)`. -/
theorem ae_hFix_fc_eq [IsProbabilityMeasure P'] (hX : IsFreeGFFModConstH X' P')
    (hv : Continuous v) (ht : 0 ≤ t) {ψ : ℂ → ℂ} (hH : EqOn ψ (revMap v t) H) (c : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P', hFix κ v t (X' ω) (foldedCircle c ρ) =
      (coordChange (X' ω) (revMap v t) (Qc (Real.sqrt κ)) + ofFun (fun u => h0rev κ (ψ u)))
        (foldedCircle c ρ) := by
  obtain ⟨Bf, hBf⟩ := CoordReg.norm_revMap_le' hv ht (‖c‖ + ρ)
  have hs := CoordReg.pushK_support hv ht hBf hρ (u := c) le_rfl
  have hf := CoordReg.pushK_frostman hv ht hρ (u := c) le_rfl le_rfl
  filter_upwards [CoordReg.ae_evalReg_h0rev_eq_frostman' hX hs hf (by norm_num) κ,
    FrostmanReg.ae_evalReg_eq_frostman hX hs hf (by norm_num)] with ω h1 h2
  simp only [CoordReg.pushKernel_apply] at h1 h2
  have hm := TwoPoint.measurable_revMap hv ht
  have hint : ∫ z, h0rev κ z ∂(foldedCircle c ρ).map (revMap v t) =
      ∫ u, h0rev κ (ψ u) ∂foldedCircle c ρ := by
    have hh : Measurable (h0rev κ) := by
      unfold h0rev; exact measurable_const.mul (Real.measurable_log.comp measurable_norm)
    rw [integral_map hm.aemeasurable hh.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H c hρ] with u hu
    rw [hH hu]
  simp only [hFix, coordChange, Pi.add_apply, ofFun]
  rw [h1, h2, hint]
  ring

/-- The folded circles read by `avgReg`: dyadic centres, dyadic radii (a countable family). -/
def dyC (p : ℕ × ℤ × ℤ) : ℂ := ⟨(p.2.1 : ℝ) / (2 : ℝ) ^ p.1, (p.2.2 : ℝ) / (2 : ℝ) ^ p.1⟩

theorem dyadicRoundC_eq_dyC (n : ℕ) (z : ℂ) :
    dyadicRoundC n z = dyC (n, ⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋) := rfl

/-- **x-side, `avgReg` level.** Almost surely, at every level and every point,
`avgReg (hFix X') = avgReg (coordChange X' F Q + ofFun (𝔥₀∘ψ))`. -/
theorem ae_avgReg_hFix_eq [IsProbabilityMeasure P'] (hX : IsFreeGFFModConstH X' P')
    (hv : Continuous v) (ht : 0 ≤ t) {ψ : ℂ → ℂ} (hH : EqOn ψ (revMap v t) H) :
    ∀ᵐ ω ∂P', ∀ k z, avgReg (hFix κ v t (X' ω)) k z =
      avgReg (coordChange (X' ω) (revMap v t) (Qc (Real.sqrt κ)) +
        ofFun (fun u => h0rev κ (ψ u))) k z := by
  have h : ∀ᵐ ω ∂P', ∀ q : ℕ × (ℕ × ℤ × ℤ), hFix κ v t (X' ω)
      (foldedCircle (dyC q.2) (radius q.1)) =
      (coordChange (X' ω) (revMap v t) (Qc (Real.sqrt κ)) + ofFun (fun u => h0rev κ (ψ u)))
        (foldedCircle (dyC q.2) (radius q.1)) :=
    ae_all_iff.2 fun q => ae_hFix_fc_eq hX hv ht hH _ (radius_pos q.1)
  filter_upwards [h] with ω hω k z
  unfold avgReg
  congr 1
  funext n
  rw [dyadicRoundC_eq_dyC]
  exact hω (k, _)

/-! ## 3. Assembly of E1-CC -/

/-- **E1-CC** (`handoff/E1-PLAN.md`): coordinate change of the boundary measure on a live
negative window, fixed driver. -/
theorem ae_lintegral_hFix_eq [IsProbabilityMeasure P'] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hX : IsFreeGFFModConstH X' P') (hv : Continuous v) (hv0 : v 0 = 0) (ht : 0 ≤ t)
    (hab : a < b) (hw : ∀ x ∈ Icc a b, x < 0 ∧ IsLive v t x) :
    ∀ᵐ ω' ∂P', ∀ g : ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (realRevMap v t x) ∂qBoundaryMeasureOn (Real.sqrt κ) (hFix κ v t (X' ω')) (Ioo a b)
        = ∫⁻ y, g y ∂qBoundaryMeasureOn (Real.sqrt κ) (ofFun (h0rev κ) + X' ω')
            (Ioo (realRevMap v t a) (realRevMap v t b)) := by
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  have hγ2 : γ < 2 := by
    rw [hγdef, show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  obtain ⟨U, hUo, hJU, hdiff, hH, hreal, him, hne⟩ :=
    exists_revMapExt_window hv ht (a := a) (b := b) fun x hx => (hw x hx).2
  set ψ := revMapExt v t with hψdef
  set F := realRevMap v t with hFdef
  have hmono : StrictMonoOn (fun x : ℝ => (ψ x).re) (Icc a b) := by
    intro x hx y hy hxy
    simp only [hreal x hx, hreal y hy, Complex.ofReal_re]
    exact RealLine.strictMonoOn_realRevMap hv ht (exists_isRealRevSol_of_isLive (hw x hx).2)
      (exists_isRealRevSol_of_isLive (hw y hy).2) hxy
  set Φ := CoordChange.extIso hab.le
    (CoordChange.continuousOn_re_of_differentiableOn hJU hdiff) hmono with hΦdef
  have hΦ : ∀ x ∈ Icc a b, Φ x = F x := fun x hx => by
    rw [hΦdef, CoordChange.extIso_eq, hreal x hx, Complex.ofReal_re]; exact hx
  have hFneg : ∀ x ∈ Icc a b, F x < 0 := fun x hx =>
    realRevMap_neg hv hv0 ht (hw x hx).1 (hw x hx).2
  have haI : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hbI : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  -- the a.s. inputs
  have hA := CoordChange.ae_isVagueLimitOnR_coordChange hX hγ hγ2 hab hUo hJU hdiff him hmono hne
  filter_upwards [hA, CoordReg.ae_isRegularSample_coordChange_revMap' hv ht hX 0
      (g₁ := fun _ => 0) continuous_const (Qc γ), ae_avgReg_hFix_eq (κ := κ) hX hv ht hH,
    BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2, RegSample.ae_isRegularSample hX]
    with ω hlim hregY havg hν hregX
  set ν := qBoundaryMeasure γ (X' ω) with hνdef
  set Y := coordChange (X' ω) (revMap v t) (Qc γ) with hYdef
  have hzero : ofFun (fun v : ℂ => (0 : ℝ) * Real.log ‖v‖ + (fun _ => (0 : ℝ)) v) + X' ω = X' ω := by
    funext μ; simp [ofFun]
  rw [hzero] at hregY
  have hlimY : IsVagueLimitOnR (Ioo a b) (bdryApprox γ Y) (CoordChange.targetMeasure ν Φ a b) := by
    have e : bdryApprox γ Y = bdryApprox γ (coordChange (X' ω) ψ (Qc γ)) := funext fun k =>
      (bdryApprox_coordChange_revMapExt hH γ (X' ω) (Qc γ) k).symm
    rw [e]; exact hlim
  -- x-side
  set W : Set ℂ := U ∩ ψ ⁻¹' {z | z ≠ 0} with hWdef
  have hWo : IsOpen W := hdiff.continuousOn.isOpen_inter_preimage hUo isOpen_ne
  have hUW : ∀ x ∈ Ioo a b, (x : ℂ) ∈ W := fun x hx =>
    ⟨hJU x (Ioo_subset_Icc_self hx), by
      show ψ x ≠ 0
      rw [hreal x (Ioo_subset_Icc_self hx)]
      exact_mod_cast (hFneg x (Ioo_subset_Icc_self hx)).ne⟩
  have hφc : ContinuousOn (fun u => h0rev κ (ψ u)) (W ∩ Hbar) :=
    (continuousOn_h0rev κ).comp (hdiff.continuousOn.mono fun z hz => hz.1.1) fun z hz => hz.1.2
  have hx_side : qBoundaryMeasureOn γ (hFix κ v t (X' ω)) (Ioo a b) =
      (CoordChange.targetMeasure ν Φ a b).withDensity fun x => ENNReal.ofReal |Φ x| := by
    have e1 : qBoundaryMeasureOn γ (hFix κ v t (X' ω)) (Ioo a b) =
        qBoundaryMeasureOn γ (Y + ofFun fun u => h0rev κ (ψ u)) (Ioo a b) :=
      qBoundaryMeasureOn_congr_of_eventuallyEq isOpen_Ioo (Eventually.of_forall fun k => by
        unfold bdryApprox; simp_rw [havg k])
    rw [e1, LocalRule.qBoundaryMeasureOn_add_ofFun hregY isOpen_Ioo ⟨_, hlimY⟩ hWo hUW hφc,
      LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo hlimY]
    refine withDensity_congr_ae ?_
    have h0 : CoordChange.targetMeasure ν Φ a b (Ioo a b)ᶜ = 0 := hlimY.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
    have hx' : x ∈ Icc a b := Ioo_subset_Icc_self (by simpa using hx)
    rw [hreal x hx', hΦ x hx', exp_half_mul_h0rev hκ (hFneg x hx').ne]
  -- y-side
  have hlimX := PalmNorm.isVagueLimitOnR_restrict_of_R hν (isOpen_Ioo (a := F a) (b := F b))
  have hy_side : qBoundaryMeasureOn γ (ofFun (h0rev κ) + X' ω) (Ioo (F a) (F b)) =
      (ν.withDensity fun y => ENNReal.ofReal |y|).restrict (Ioo (F a) (F b)) := by
    rw [add_comm, LocalRule.qBoundaryMeasureOn_add_ofFun hregX isOpen_Ioo ⟨_, hlimX⟩
      (W := {z : ℂ | z ≠ 0}) isOpen_ne (fun y hy => by
        show (y : ℂ) ≠ 0
        exact_mod_cast (hy.2.trans (hFneg b hbI)).ne)
      ((continuousOn_h0rev κ).mono inter_subset_left),
      LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo hlimX, restrict_withDensity measurableSet_Ioo]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [exp_half_mul_h0rev hκ (hy.2.trans (hFneg b hbI)).ne]
  intro g hg
  rw [hx_side, hy_side, ← hΦ a haI, ← hΦ b hbI,
    ← lintegral_targetMeasure_withDensity_abs ν Φ a b hg]
  refine lintegral_congr_ae ?_
  have h0 : CoordChange.targetMeasure ν Φ a b (Ioo a b)ᶜ = 0 := hlimY.1
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le
    (measure_eq_zero_iff_ae_notMem.1 h0)] with x hx
  have hx' : x ∈ Icc a b := Ioo_subset_Icc_self (by simpa using hx)
  rw [hΦ x hx']

end E1
end QuantumZipper
