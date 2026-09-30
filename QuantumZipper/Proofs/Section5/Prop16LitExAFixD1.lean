import QuantumZipper.Proofs.Section5.Prop16LitExAFixDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: `GoodA` for chart zooms of locally free fields (D98)

* `Prop16Lit.ExA.ChartGood`: a regular sample with regular pushed averages along `ψ` whose
  coordinate change has an area limit on `ℍ`; a.s. for the free field
  (`Prop16Lit.ExA.ae_chartGood`, from `CoordChangeArea.ae_pushRegular` and
  `ae_isVagueLimitOn_coordChange_free`, DS11 Prop. 2.1).
* `Prop16Lit.ExA.goodA_zoomLit_of_agree`: if the translate `h(· + t)` agrees on the dyadic
  circles in `V ⊇ ψ(B(0,r) ∩ ℍ)` with a chart-good sample plus a continuous function, the chart
  zoom `zoomFieldLit γ C h t ψ` satisfies `GoodA`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit
namespace ExA

open CoordChangeArea

/-- A chart-good sample. -/
def ChartGood (γ : ℝ) (ψ : ℂ → ℂ) (y : FieldSample) : Prop :=
  IsRegularSample y ∧ PushRegular y ψ ∧
    ∃ μ, IsVagueLimitOn H (areaApprox γ (coordChange y ψ (Qc γ))) μ

theorem ae_chartGood {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ψ : ℂ → ℂ} (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H) (hψH : MapsTo ψ H H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) : ∀ᵐ ω ∂P, ChartGood γ ψ (X ω) := by
  filter_upwards [RegSample.ae_isRegularSample hX, ae_pushRegular hX hψd hψi hψH hψ0,
    ae_isVagueLimitOn_coordChange_free hX hγ hγ2 hψd hψi hψH hψ0] with ω h1 h2 h3
  exact ⟨h1, h2, _, h3⟩

/-- **`GoodA` for the chart zoom of a locally chart-good field.** -/
theorem goodA_zoomLit_of_agree {γ C : ℝ} {x' y : FieldSample} {ψ : ℂ → ℂ}
    (hy : ChartGood γ ψ y) (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) {V : Set ℂ} (hVo : IsOpen V) (hVH : V ⊆ H) {g : ℂ → ℝ}
    (hg : ContinuousOn g V) {t : ℝ}
    (hag : Prop16Area.G.CircAgree V (translate x' (t : ℂ)) (y + ofFun g)) {r : ℝ}
    (hUV : MapsTo ψ (ball 0 r ∩ H) V) : GoodA γ (zoomFieldLit γ C x' t ψ) r := by
  obtain ⟨⟨F, hF⟩, hpush, μ, hμ⟩ := hy
  have hUo : IsOpen (ball (0 : ℂ) r ∩ H) := isOpen_ball.inter isOpen_H
  have hUH : ball (0 : ℂ) r ∩ H ⊆ H := inter_subset_right
  have hUHb : MapsTo ψ (ball 0 r ∩ H) Hbar := fun z hz => H_subset_Hbar (hVH (hUV hz))
  have hTC := circAgree_addConst hg hag (C / γ)
  have hgc : ContinuousOn (fun u => g u + C / γ) V := hg.add continuousOn_const
  have hv := isVagueLimitOn_coordChange_of_circAgree hF hψm hψd hψ0 hpush hμ hVo hgc hTC hUo hUH
    hUV hUHb
  have hlit := isVagueLimitOn_addConst_coordChange hF hψm hψd hpush hVo hg hag hUo hUH hUV hUHb
    (Qc γ) (C / γ) hv
  refine goodA_of_vague hlit fun K hK hKU => ?_
  filter_upwards [eventually_avgReg_addConst_coordChange (γ := γ) hF hψm hψd hpush hVo hg hag hUo hUH hUV
      hUHb (Qc γ) (C / γ) hK hKU,
    eventually_continuousOn_avgReg_coordChange hF hψm hψd hψ0 hpush hVo hgc hTC hUo hUH hUV hUHb
      (Qc γ) hK hKU] with k h1 h2
  exact h2.congr fun w hw => (h1 w hw).symm

end ExA
end Prop16Lit
end QuantumZipper
