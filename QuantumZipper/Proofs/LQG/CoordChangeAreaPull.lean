import QuantumZipper.Proofs.LQG.CoordChangeAreaLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the quantum area measure: the pullback form (COORD-CHANGE, D98)

**Main theorem** `CoordChangeArea.ae_map_qAreaMeasureOn_coordChange`, the local form of
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Proposition 2.1 (arXiv:0808.1560, p. 12): for the free-boundary GFF `X` on `ℍ` and a
deterministic conformal map `ψ` of `ℍ` into `ℍ` (holomorphic, injective, `ψ' ≠ 0`,
measurable), almost surely, **simultaneously** for every field sample `x` that agrees on the
dyadic circles inside an open set `W` with `X ω + φ`, `φ` continuous on `W` (a field of GFF
type near `W`: the free field itself, a mixed or zero-boundary GFF through a local coupling, plus
a continuous function, plus a log singularity at a boundary point outside `W`), for every open
`U ⊆ ℍ` and open `V ⊆ W ∩ ℍ` with `ψ(U) ⊆ V`:

  `ψ_* μ^{U}_{x ∘ ψ + Q log|ψ'|} = μ^{V}_x |_{ψ(U)}`,

where `μ^{U}_h = qAreaMeasureOn γ h U` is the local area measure (A17). Equivalently the area
measure of the coordinate change is the pullback `ψ^* μ_x` on `U`. The global case (`x = X ω`,
`W = V = ℍ`) is `CoordChangeArea.ae_qAreaMeasure_coordChange_free`.

`CoordChangeArea.map_pullMu_withDensity` is the change of variables for the pullback measure
`pullMu` (own elementary measure theory).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore GoodSample G1Side

/-- **Change of variables for the pullback measure.** -/
theorem map_pullMu_withDensity {Φ : ℂ → ℂ} (hΦm : Measurable Φ) (hc : ContinuousOn Φ H)
    (hi : InjOn Φ H) {ν : Measure ℂ} {U : Set ℂ} (hU : MeasurableSet U) (hUH : U ⊆ H)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    (((pullMu ν Φ).restrict U).withDensity fun z => f (Φ z)).map Φ =
      (ν.withDensity f).restrict (Φ '' U) := by
  have hE := measurableEmbedding_resH hc hi
  have himU : Φ '' U = resH Φ '' (Subtype.val ⁻¹' U) := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hUH hu⟩, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  have hΦU : MeasurableSet (Φ '' U) := by
    rw [himU]; exact hE.measurableSet_image.2 (measurable_subtype_coe hU)
  have key : ∀ T : Set H, MeasurableSet T →
      ∫⁻ u in T, f (resH Φ u) ∂(ν.comap (resH Φ)) = ∫⁻ w in resH Φ '' T, f w ∂ν := by
    intro T hT
    have hpre : resH Φ ⁻¹' (resH Φ '' T) = T := hE.injective.preimage_image T
    have hS : MeasurableSet (resH Φ '' T) := hE.measurableSet_image.2 hT
    have h1 : ((ν.comap (resH Φ)).restrict T).map (resH Φ) = ν.restrict (resH Φ '' T) := by
      have := hE.restrict_map (ν.comap (resH Φ)) (resH Φ '' T)
      rw [hpre, hE.map_comap, Measure.restrict_restrict hS,
        inter_eq_left.2 (image_subset_range _ _)] at this
      exact this.symm
    rw [← h1, hE.lintegral_map]
  ext A hA
  rw [Measure.map_apply hΦm hA, withDensity_apply _ (hΦm hA),
    Measure.restrict_restrict (hΦm hA), Measure.restrict_apply hA,
    withDensity_apply _ (hA.inter hΦU)]
  unfold pullMu
  rw [setLIntegral_map ((hΦm hA).inter hU) (f := fun z => f (Φ z)) (hf.comp hΦm)
    measurable_subtype_coe]
  have hT : MeasurableSet (Subtype.val ⁻¹' (Φ ⁻¹' A ∩ U) : Set H) :=
    measurable_subtype_coe ((hΦm hA).inter hU)
  have e := key _ hT
  simp only [resH] at e
  rw [e]
  congr 2
  ext w
  constructor
  · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩; exact ⟨hu1, u, hu2, rfl⟩
  · rintro ⟨hw, u, hu, rfl⟩; exact ⟨⟨u, hUH hu⟩, ⟨hw, hu⟩, rfl⟩

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Coordinate change of the quantum area measure (DS11 Prop. 2.1), local pullback form.** -/
theorem ae_map_qAreaMeasureOn_coordChange [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H)
    (hψH : MapsTo ψ H H) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ (x : FieldSample) (W : Set ℂ) (φ : ℂ → ℝ) (U V : Set ℂ), IsOpen W →
      ContinuousOn φ W → Prop16Area.G.CircAgree W x (X ω + ofFun φ) → IsOpen U → U ⊆ H →
      IsOpen V → V ⊆ H → V ⊆ W → MapsTo ψ U V →
      (qAreaMeasureOn γ (coordChange x ψ (Qc γ)) U).map ψ =
        (qAreaMeasureOn γ x V).restrict (ψ '' U) := by
  filter_upwards [ae_qAreaMeasureOn_coordChange hX hγ hγ2 hψm hψd hψi hψH hψ0,
    RegSample.ae_isRegularSample hX, AreaExist.ae_isVagueLimitOn_qAreaMeasure hX (P := P) hγ hγ2]
    with ω hcc hreg hμ x W φ U V hWo hφ hag hUo hUH hVo hVH hVW hUV
  classical
  -- a measurable version of `φ`
  set φ' : ℂ → ℝ := W.piecewise φ 0 with hφ'def
  have hφ'm : Measurable φ' :=
    hφ.measurable_piecewise continuousOn_const hWo.measurableSet
  have hφφ' : EqOn φ' φ W := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  have hφ'c : ContinuousOn φ' W := hφ.congr hφφ'
  have hag' : Prop16Area.G.CircAgree W x (X ω + ofFun φ') := by
    intro n k z hz hsub
    rw [hag n k z hz hsub]
    simp only [Pi.add_apply, ofFun]
    congr 1
    refine integral_congr_ae ?_
    have hfc : ∀ᵐ u ∂foldedCircle (dyadicRoundC n z) (radius k),
        u ∈ closedBall (dyadicRoundC n z) (radius k) ∩ Hbar := by
      filter_upwards [ae_fc_mem_closedBall (CircleCont.dyadicRoundC_mem_Hbar hz n)
        (radius_pos k).le, RegClosure.fc_ae_mem_Hbar _ _] with u h1 h2 using ⟨h1, h2⟩
    filter_upwards [hfc] with u hu
    exact (hφφ' (hsub hu)).symm
  -- the coordinate-changed field
  have h1 := hcc x W φ' U hWo hφ'c hag' hUo hUH (hUV.mono_right hVW)
  -- the field itself on `V`
  have hxV : IsVagueLimitOn V (areaApprox γ x)
      (((qAreaMeasure γ (X ω)).restrict V).withDensity
        fun z => ENNReal.ofReal (Real.exp (γ * φ' z))) :=
    Prop16Area.G.isVagueLimitOn_of_circAgree hWo hag' hVH hVW
      (LocalRule.isVagueLimitOn_add_ofFun hreg hVo hVH
        (Prop16Area.G.isVagueLimitOn_restrict_sub hVo hVH hμ) hWo hVW
        (hφ'c.mono inter_subset_left))
  rw [h1, LocalRule.qAreaMeasureOn_eq hVo hxV]
  have hf : Measurable fun w => ENNReal.ofReal (Real.exp (γ * φ' w)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hφ'm.const_mul γ))
  rw [map_pullMu_withDensity hψm hψd.continuousOn hψi hUo.measurableSet hUH hf,
    ← restrict_withDensity hVo.measurableSet, Measure.restrict_restrict_of_subset
      (image_subset_iff.2 hUV)]

end CoordChangeArea
end QuantumZipper
