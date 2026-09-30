import QuantumZipper.Proofs.Zipper.E1Fixed
import QuantumZipper.Proofs.LQG.AtomlessUncond

/-!
# B5-V window identity for a fixed driver (the independent side)

Task B5V-FIX (`handoff/B5.md`, R1 (c)). For a **fixed** continuous driver `v` with `v 0 = 0`, a
time `t ≥ 0`, a compact live window `[a,b] ⊆ liveNeg v t`, and a free field `X'`, almost surely

`ν^{loc}_{hFix}(a,b) = ν_{𝔥₀ + X'}(F a, F b)`, `F = realRevMap v t`,

where `hFix = coordChange (𝔥₀ + X') (revMap v t) Q` (`E1.hFix`) and `ν^{loc}` is its local
boundary measure on `(a,b)` (**`ae_qBoundaryMeasureOn_hFix_window`**). This is the
coordinate-change rule for the boundary measure (Sheffield, arXiv:1012.4797, proof of Thm 1.3 and
Lemma 5.6, pp. 66–68; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 2.1 / §6.2) at the
pair `(𝔥₀ + X', revMap v t)`: the free part transforms by `CoordChange.ae_isVagueLimitOnR_coordChange`,
the logarithmic part by `LocalRule.isVagueLimitOnR_add_ofFun`, and `ν_{𝔥₀ + X'} = |y| ν_{X'}` off `0`
(`AtomlessUncond.ae_gamma0_logSingularity`). The assembly follows
`E1.ae_exists_isVagueLimitOnR_hFix`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open RevMapExtension E1

variable {Ω : Type*} [MeasurableSpace Ω] {P' : Measure Ω}
variable {κ t a b : ℝ} {v : ℝ → ℝ} {X' : Ω → FieldSample}

/-- `exp (γ/2 · 𝔥₀(y)) = |y|` for real `y ≠ 0`, `γ = √κ`. -/
theorem exp_h0rev_ofReal (hκ : 0 < κ) {y : ℝ} (hy : y ≠ 0) :
    Real.exp (Real.sqrt κ / 2 * h0rev κ (y : ℂ)) = |y| := by
  have hγ : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  rw [h0rev_eq_log]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [show Real.sqrt κ / 2 * (2 / Real.sqrt κ * Real.log |y|) = Real.log |y| by field_simp,
    Real.exp_log (abs_pos.2 hy)]

/-- **Window identity for a fixed driver.** -/
theorem ae_qBoundaryMeasureOn_hFix_window [IsProbabilityMeasure P'] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hX : IsFreeGFFModConstH X' P') (hv : Continuous v) (hv0 : v 0 = 0) (ht : 0 ≤ t)
    (hab : a < b) (hw : ∀ x ∈ Icc a b, x < 0 ∧ IsLive v t x) :
    ∀ᵐ ω ∂P', qBoundaryMeasureOn (Real.sqrt κ) (hFix κ v t (X' ω)) (Ioo a b) (Ioo a b) =
      qBoundaryMeasure (Real.sqrt κ) (ofFun (h0rev κ) + X' ω)
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
  have hmono : StrictMonoOn (fun x : ℝ => (ψ x).re) (Icc a b) := by
    intro x hx y hy hxy
    simp only [hreal x hx, hreal y hy, Complex.ofReal_re]
    exact RealLine.strictMonoOn_realRevMap hv ht (exists_isRealRevSol_of_isLive (hw x hx).2)
      (exists_isRealRevSol_of_isLive (hw y hy).2) hxy
  have hFneg : ∀ x ∈ Icc a b, realRevMap v t x < 0 := fun x hx =>
    realRevMap_neg hv hv0 ht (hw x hx).1 (hw x hx).2
  set Φ := CoordChange.extIso hab.le (CoordChange.continuousOn_re_of_differentiableOn hJU hdiff)
    hmono with hΦdef
  have hΦ : ∀ x ∈ Icc a b, Φ x = realRevMap v t x := fun x hx => by
    rw [hΦdef, CoordChange.extIso_eq hab.le _ hmono hx, hreal x hx, Complex.ofReal_re]
  have hA := CoordChange.ae_isVagueLimitOnR_coordChange hX hγ hγ2 hab hUo hJU hdiff him hmono hne
  filter_upwards [hA, CoordReg.ae_isRegularSample_coordChange_revMap' hv ht hX 0
      (g₁ := fun _ => 0) continuous_const (Qc γ), ae_avgReg_hFix_eq (κ := κ) hX hv ht hH,
      AtomlessUncond.ae_gamma0_logSingularity hX hκ hκ4]
    with ω hlim hregY havg hg0
  set Y := coordChange (X' ω) (revMap v t) (Qc γ) with hYdef
  have hzero : ofFun (fun v : ℂ => (0 : ℝ) * Real.log ‖v‖ + (fun _ => (0 : ℝ)) v) + X' ω = X' ω := by
    funext μ; simp [ofFun]
  rw [hzero] at hregY
  set ν0 := CoordChange.targetMeasure (qBoundaryMeasure γ (X' ω)) Φ a b with hν0
  have hlimY : IsVagueLimitOnR (Ioo a b) (bdryApprox γ Y) ν0 := by
    have e : bdryApprox γ Y = bdryApprox γ (coordChange (X' ω) ψ (Qc γ)) := funext fun k =>
      (bdryApprox_coordChange_revMapExt hH γ (X' ω) (Qc γ) k).symm
    rw [e]; exact hlim
  set W : Set ℂ := U ∩ ψ ⁻¹' {z | z ≠ 0} with hWdef
  have hWo : IsOpen W := hdiff.continuousOn.isOpen_inter_preimage hUo isOpen_ne
  have hUW : ∀ x ∈ Ioo a b, (x : ℂ) ∈ W := fun x hx =>
    ⟨hJU x (Ioo_subset_Icc_self hx), by
      show ψ x ≠ 0
      rw [hreal x (Ioo_subset_Icc_self hx)]
      exact_mod_cast (hFneg x (Ioo_subset_Icc_self hx)).ne⟩
  have hφc : ContinuousOn (fun u => h0rev κ (ψ u)) (W ∩ Hbar) :=
    (continuousOn_h0rev κ).comp (hdiff.continuousOn.mono fun z hz => hz.1.1) fun z hz => hz.1.2
  have e1 : bdryApprox γ (hFix κ v t (X' ω)) = bdryApprox γ (Y + ofFun fun u => h0rev κ (ψ u)) :=
    funext fun k => by unfold bdryApprox; simp_rw [havg k]
  have hlimF := LocalRule.isVagueLimitOnR_add_ofFun hregY isOpen_Ioo hlimY hWo hUW hφc
  rw [← e1] at hlimF
  have hI : Ioo (Φ a) (Φ b) ∩ {0}ᶜ = Ioo (Φ a) (Φ b) := by
    refine inter_eq_left.2 fun y hy h0 => ?_
    rw [mem_singleton_iff] at h0
    have : Φ b < 0 := by rw [hΦ b ⟨hab.le, le_rfl⟩]; exact hFneg b ⟨hab.le, le_rfl⟩
    exact absurd (h0 ▸ hy.2) (not_lt.2 this.le)
  have hφ' : ∀ x ∈ Ioo a b, ENNReal.ofReal (Real.exp (γ / 2 * h0rev κ (ψ x))) =
      ENNReal.ofReal |Φ x| := by
    intro x hx
    have hxI := Ioo_subset_Icc_self hx
    rw [hreal x hxI, hΦ x hxI, exp_h0rev_ofReal hκ (hFneg x hxI).ne]
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal |Φ x| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp Φ.continuous.measurable)
  rw [LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo hlimF, withDensity_apply _ measurableSet_Ioo,
    setLIntegral_congr_fun measurableSet_Ioo hφ', ← withDensity_apply _ measurableSet_Ioo,
    hν0, targetMeasure_withDensity _ _ _ _ hmeas,
    CoordChange.targetMeasure_apply _ _ measurableSet_Ioo, OrderIso.image_Ioo, inter_self,
    ← hΦ a ⟨le_rfl, hab.le⟩, ← hΦ b ⟨hab.le, le_rfl⟩, hg0.2.1,
    withDensity_apply _ measurableSet_Ioo, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, hI]
  simp only [OrderIso.apply_symm_apply, hγdef]

end B5
end QuantumZipper
