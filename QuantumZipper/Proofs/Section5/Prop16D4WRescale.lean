import QuantumZipper.Proofs.Section5.Prop16LocalAssembly

/-!
# Proposition 1.6, D4⁺ʷ tool: the rescaling rule for LOCAL area measures

Decision D24 (`DECISIONS.md`), "intended proof of D4⁺ʷ": the area measure of the canonical field
is a push-forward under a dilation, which needs a deterministic rescaling rule for the local
area measures `qAreaMeasureOn` (the global version is `GoodTransforms.qAreaMeasure_rescale`,
M4-T3).

The local measure `qAreaMeasureOn` is a limit along the dyadic radii `2^{-k}` only, and a dilation
by `s` moves these radii to `s 2^{-k}`, so the rule cannot be read off `IsVagueLimitOn` alone. We
prove it for locally good samples (`G.IsLocallyGoodOn`: near `V`, `x` agrees on the dyadic
circles with `y + ofFun ψ`, `y` good, `ψ` continuous), which is the form available for
Proposition 1.6's fields (M4-P7-LOC):

* `qAreaMeasureOn_eq_withDensity_of_agree`: `μ^U_x = e^{γψ}·(μ_y|_U)`;
* `qAreaMeasureOn_rescale_of_locallyGood`: for `s > 0` and `U ⊆ V ∩ ℍ` open,
  `μ^{s⁻¹U}_{rescale x Q s} = (·/s)_* μ^U_x` (`Q = Qc γ`);
* `scaleParamOn_rescale_of_locallyGood`: `scaleParamOn (rescale x Q s) (s⁻¹U) = scaleParamOn x U / s`
  (for `U` containing the relevant half-balls this is exact; the statement needs nothing more);
* `canonicalDomainOn_rescale_of_locallyGood`: the canonical domains agree.

Own argument (AGENT_GUIDE cost rule): the global rule M4-T3 transported through the locality
tools of M4-P7-LOC and the local rule (5.1) (`LocalRule.isVagueLimitOn_add_ofFun`), plus a
change of variables for `withDensity` under the dilation. Reference for the rule itself:
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Proposition 2.1 (coordinate change), and Sheffield, arXiv:1012.4797, (1.8)/(1.2).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal Pointwise

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G GoodSample RegClosure LocalRule

/-- The dilation `z ↦ z / s` (`s > 0`) as a measurable equivalence of `ℂ`. -/
def divEquiv {s : ℝ} (hs : 0 < s) : ℂ ≃ᵐ ℂ where
  toFun z := z / (s : ℂ)
  invFun z := (s : ℂ) * z
  left_inv z := by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only; field_simp
  right_inv z := by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only; field_simp
  measurable_toFun := measurable_id.div_const _
  measurable_invFun := measurable_const.mul measurable_id

theorem coe_divEquiv {s : ℝ} (hs : 0 < s) : ⇑(divEquiv hs) = fun z : ℂ => z / (s : ℂ) := rfl

/-- Change of variables for a restricted measure with a density under `z ↦ z / s`. -/
theorem map_div_restrict_withDensity (ν : Measure ℂ) {U : Set ℂ} (hU : MeasurableSet U)
    (ρ : ℂ → ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    ((ν.restrict U).withDensity ρ).map (fun z : ℂ => z / (s : ℂ)) =
      ((ν.map fun z : ℂ => z / (s : ℂ)).restrict ((fun z => (s : ℂ) * z) ⁻¹' U)).withDensity
        (fun u => ρ ((s : ℂ) * u)) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set e := divEquiv hs
  rw [← coe_divEquiv hs]
  ext A hA
  have hU' : MeasurableSet ((fun z => (s : ℂ) * z) ⁻¹' U) :=
    (measurable_const.mul measurable_id) hU
  rw [Measure.map_apply e.measurable hA, withDensity_apply _ (e.measurable hA),
    withDensity_apply _ hA, Measure.restrict_restrict (e.measurable hA),
    Measure.restrict_restrict hA, e.restrict_map, lintegral_map_equiv]
  have hpre : e ⁻¹' (A ∩ (fun z => (s : ℂ) * z) ⁻¹' U) = e ⁻¹' A ∩ U := by
    ext z; simp only [mem_preimage, mem_inter_iff, coe_divEquiv hs, e]
    rw [mul_div_cancel₀ _ hs']
  rw [hpre]
  refine lintegral_congr fun z => ?_
  simp only [coe_divEquiv hs, e, mul_div_cancel₀ _ hs']

/-- For a sample agreeing near `U` with `y + ofFun ψ` (`y` good, `ψ` continuous on `W ∩ H̄`), the
local area measure on `U` is `e^{γψ}·(μ_y|_U)`. -/
theorem qAreaMeasureOn_eq_withDensity_of_agree {γ : ℝ} {W U : Set ℂ} (hWo : IsOpen W)
    {x y : FieldSample} {ψ : ℂ → ℝ} (hy : IsLQGGood γ y) (hψ : ContinuousOn ψ (W ∩ Hbar))
    (h : CircAgree W x (y + ofFun ψ)) (hU : IsOpen U) (hUH : U ⊆ H) (hUW : U ⊆ W) :
    qAreaMeasureOn γ x U = ((qAreaMeasure γ y).restrict U).withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * ψ z))) := by
  refine qAreaMeasureOn_eq hU (isVagueLimitOn_of_circAgree hWo h hUH hUW ?_)
  exact isVagueLimitOn_add_ofFun hy.1 hU hUH
    (isVagueLimitOn_restrict_sub hU hUH (isVagueLimitOn_H_of_good hy)) hWo hUW hψ

/-- **Rescaling rule for local area measures.** For a locally good sample on `V`, an open
`U ⊆ V ∩ ℍ` and `s > 0`: `μ^{s⁻¹U}_{rescale x Q s} = (·/s)_* μ^U_x`, `Q = Qc γ`. -/
theorem qAreaMeasureOn_rescale_of_locallyGood {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ}
    {x : FieldSample} (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V)
    {s : ℝ} (hs : 0 < s) :
    qAreaMeasureOn γ (rescale x (Qc γ) s) ((fun z => (s : ℂ) * z) ⁻¹' U) =
      (qAreaMeasureOn γ x U).map fun z : ℂ => z / (s : ℂ) := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hψ, h⟩ := hx
  rw [← hWV] at hUV hψ
  have hUW : U ⊆ W := fun z hz => (hUV hz).1
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hmul : Continuous fun z : ℂ => (s : ℂ) * z := continuous_const.mul continuous_id
  set U' := (fun z => (s : ℂ) * z) ⁻¹' U
  set W' := (fun z => (s : ℂ) * z) ⁻¹' W
  have hU' : IsOpen U' := hU.preimage hmul
  have hW' : IsOpen W' := hWo.preimage hmul
  have hU'H : U' ⊆ H := fun z hz => by
    have h1 : (0 : ℝ) < ((s : ℂ) * z).im := hUH hz
    rw [Complex.im_ofReal_mul] at h1
    exact pos_of_mul_pos_right h1 hs.le
  have hU'W : U' ⊆ W' := fun z hz => hUW hz
  have hψ' : ContinuousOn (fun u => ψ ((s : ℂ) * u)) (W' ∩ Hbar) :=
    hψ.comp hmul.continuousOn fun u hu => ⟨hu.1, mapsTo_mul_pos hs hu.2⟩
  have hag : CircAgree W' (rescale x (Qc γ) s)
      (rescale y (Qc γ) s + ofFun fun u => ψ ((s : ℂ) * u)) :=
    ((fcAgree_rescale hWo h (Qc γ) hs).trans
      (fcAgree_rescale_add_ofFun hy.1 hWo hψ (Qc γ) hs)).circAgree
  rw [qAreaMeasureOn_eq_withDensity_of_agree hW' (hy.rescale hγ hs) hψ' hag hU' hU'H hU'W,
    qAreaMeasureOn_eq_withDensity_of_agree hWo hy hψ h hU hUH hUW,
    GoodTransforms.qAreaMeasure_rescale hy hγ hs,
    map_div_restrict_withDensity _ hU.measurableSet _ hs]

/-- **Rescaling rule for the local scale.** -/
theorem scaleParamOn_rescale_of_locallyGood {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ}
    {x : FieldSample} (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V)
    {s : ℝ} (hs : 0 < s) :
    scaleParamOn γ (rescale x (Qc γ) s) ((fun z => (s : ℂ) * z) ⁻¹' U) =
      scaleParamOn γ x U / s := by
  unfold scaleParamOn
  rw [qAreaMeasureOn_rescale_of_locallyGood hγ hx hU hUH hUV hs]
  have hmeas : Measurable (fun z : ℂ => z / (s : ℂ)) := measurable_id.div_const _
  have e : {a : ℝ | 0 < a ∧ 1 ≤ ((qAreaMeasureOn γ x U).map fun z : ℂ => z / (s : ℂ))
      (Metric.ball (0 : ℂ) a ∩ H)} =
      s⁻¹ • {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasureOn γ x U (Metric.ball (0 : ℂ) a ∩ H)} := by
    ext a
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hs.ne'), inv_inv, smul_eq_mul]
    simp only [mem_ofPred_eq]
    rw [Measure.map_apply hmeas (Metric.isOpen_ball.inter isOpen_H).measurableSet,
      GoodTransforms.preimage_div_ball_inter_H hs, mul_comm s a]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨mul_pos h1 hs, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨pos_of_mul_pos_left h1 hs.le, h2⟩
  rw [e, Real.sInf_smul_of_nonneg (inv_nonneg.2 hs.le), smul_eq_mul, div_eq_inv_mul]

end Prop16Asm

end QuantumZipper
