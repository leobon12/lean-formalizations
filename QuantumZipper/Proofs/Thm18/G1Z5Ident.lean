import QuantumZipper.Proofs.Thm18.G1Z5SideCert
import QuantumZipper.Proofs.Thm18.G1ZBdryDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z5 (D58, S1): identification of the side limit with the pullback, on a countable family

If `ν` is the side boundary limit (along all radii) of a field `z`, `y` has the vague boundary
limit `qBoundaryMeasure γ y`, and `Φ` is an order isomorphism fixing `0`, then
`ν = ((qBoundaryMeasure γ y)|_S).map Φ.symm` as soon as, for the countable glued family
`glue left (testFam N m)`, `glue left (bump N)`, the dyadic integrals of `g ∘ Φ` against the
approximations of `z` converge to `∫ g d(qBoundaryMeasure γ y)` (`eq_pullback_of_ident`).
This is a countable (hence measurable, given a measurable `Φ`) form of the transport identity.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z5

open GoodSample GoodMeas
open BdryVague (testFam bump continuous_testFam hasCompactSupport_testFam continuous_bump
  hasCompactSupport_bump)

theorem pushR_lt_top_of_side (left : Bool) {μ : Measure ℝ}
    (hμ : ∀ K, IsCompact K → K ⊆ g1SideHalf left → μ K < ⊤) {K : Set ℝ} (hK : IsCompact K) :
    pushR left μ K < ⊤ := by
  rw [pushR, Measure.map_apply (measurable_sig left) hK.isClosed.measurableSet,
    Measure.restrict_apply (measurable_sig left hK.isClosed.measurableSet)]
  refine (measure_mono fun t ht => ?_).trans_lt (hμ _ (hK.image (continuous_tau left)) ?_)
  · exact ⟨sig left t, ht.1, tau_sig ht.2⟩
  · rintro _ ⟨u, -, rfl⟩; exact tau_mem left u

theorem map_tau_pushR (left : Bool) {μ : Measure ℝ} (hμ : μ (g1SideHalf left)ᶜ = 0) :
    (pushR left μ).map (tau left) = μ := by
  have hS := (g1z2_isOpen_sideHalf left).measurableSet
  rw [pushR, Measure.map_map (continuous_tau left).measurable (measurable_sig left)]
  have h1 : (μ.restrict (g1SideHalf left)).map (tau left ∘ sig left) =
      (μ.restrict (g1SideHalf left)).map id :=
    Measure.map_congr ((ae_restrict_mem hS).mono fun t ht => tau_sig ht)
  rw [h1, Measure.map_id, Measure.restrict_eq_self_of_ae_mem]
  exact (ae_iff.2 (by simpa [compl_def] using hμ))

/-- Two measures carried by `S`, finite on compacts of `S`, with the same integrals of the glued
countable family, are equal. -/
theorem eq_of_glue_integrals (left : Bool) {μ₁ μ₂ : Measure ℝ}
    (h1S : μ₁ (g1SideHalf left)ᶜ = 0) (h2S : μ₂ (g1SideHalf left)ᶜ = 0)
    (h1 : ∀ K, IsCompact K → K ⊆ g1SideHalf left → μ₁ K < ⊤)
    (h2 : ∀ K, IsCompact K → K ⊆ g1SideHalf left → μ₂ K < ⊤)
    (hT : ∀ N m, ∫ t, glue left (testFam N m) t ∂μ₁ = ∫ t, glue left (testFam N m) t ∂μ₂)
    (hB : ∀ N, ∫ t, glue left (bump N) t ∂μ₁ = ∫ t, glue left (bump N) t ∂μ₂) :
    μ₁ = μ₂ := by
  have f1 : IsFiniteMeasureOnCompacts (pushR left μ₁) :=
    ⟨fun K hK => pushR_lt_top_of_side left h1 hK⟩
  have f2 : IsFiniteMeasureOnCompacts (pushR left μ₂) :=
    ⟨fun K hK => pushR_lt_top_of_side left h2 hK⟩
  have hT' : ∀ N m, ∫ t, testFam N m t ∂pushR left μ₁ = ∫ t, testFam N m t ∂pushR left μ₂ :=
    fun N m => by
      rw [← integral_glue left _ (continuous_testFam N m),
        ← integral_glue left _ (continuous_testFam N m)]
      exact hT N m
  have hB' : ∀ N, ∫ t, bump N t ∂pushR left μ₁ = ∫ t, bump N t ∂pushR left μ₂ := fun N => by
    rw [← integral_glue left _ (continuous_bump N), ← integral_glue left _ (continuous_bump N)]
    exact hB N
  have hv1 : IsVagueLimitR (fun _ : ℕ => pushR left μ₁) (pushR left μ₁) :=
    ⟨inferInstance, fun f _ _ => tendsto_const_nhds⟩
  have hv2 : IsVagueLimitR (fun _ : ℕ => pushR left μ₁) (pushR left μ₂) := by
    refine ⟨inferInstance, fun f hf hfc => ?_⟩
    exact tendsto_of_testFam_filter (L := atTop) (Eventually.of_forall fun _ => f1)
      (fun N m => by rw [hT' N m]; exact tendsto_const_nhds)
      (fun N => by rw [hB' N]; exact tendsto_const_nhds) hf hfc
  have he := isVagueLimitR_unique hv1 hv2
  rw [← map_tau_pushR left h1S, ← map_tau_pushR left h2S, he]

/-- `tsupport (g ∘ Φ) ⊆ Φ.symm '' tsupport g`. -/
theorem tsupport_comp_iso_subset {g : ℝ → ℝ} (hgc : HasCompactSupport g) (Φ : ℝ ≃o ℝ) :
    tsupport (g ∘ Φ) ⊆ Φ.symm '' tsupport g := by
  have hc : IsCompact (Φ.symm '' tsupport g) := hgc.image Φ.symm.continuous
  refine closure_minimal (fun t ht => ?_) hc.isClosed
  exact ⟨Φ t, subset_closure ht, Φ.symm_apply_apply t⟩

/-- **Identification of the side limit with the pullback** from the countable family. -/
theorem eq_pullback_of_ident {γ : ℝ} {left : Bool} {z y : FieldSample} {ν : Measure ℝ}
    (hν : G1Z2SideBdryLim γ left z ν)
    (hy : IsVagueLimitR (bdryApprox γ y) (qBoundaryMeasure γ y)) {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0)
    (hid : ∀ g : ℝ → ℝ, ((∃ N m, g = glue left (testFam N m)) ∨ ∃ N, g = glue left (bump N)) →
      Tendsto (fun k => ∫ t, g (Φ t) ∂bdryR γ z (goodRad (k, 1))) atTop
        (𝓝 (∫ t, g t ∂qBoundaryMeasure γ y))) :
    ν = ((qBoundaryMeasure γ y).restrict (g1SideHalf left)).map Φ.symm := by
  set S := g1SideHalf left with hSdef
  have hSm : MeasurableSet S := (g1z2_isOpen_sideHalf left).measurableSet
  have hIm : Φ '' S = S := image_g1SideHalf h0 left
  have hpre : Φ ⁻¹' S = S := by
    ext t
    have := Φ.injective.mem_set_image (s := S) (a := t)
    rw [hIm] at this
    exact this
  have himg : ∀ s : Set ℝ, Φ.symm '' s = Φ ⁻¹' s := fun s => by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩; simpa using hu
    · intro ht; exact ⟨Φ t, ht, Φ.symm_apply_apply t⟩
  have hImS : Φ.symm '' S = S := by rw [himg, hpre]
  have := hy.1
  -- the family is tested on both sides
  have key : ∀ G : ℝ → ℝ, Continuous G → HasCompactSupport G →
      Tendsto (fun k => ∫ t, glue left G (Φ t) ∂bdryR γ z (goodRad (k, 1))) atTop
        (𝓝 (∫ t, glue left G t ∂qBoundaryMeasure γ y)) →
      ∫ t, glue left G t ∂ν.map Φ =
        ∫ t, glue left G t ∂(qBoundaryMeasure γ y).restrict S := by
    intro G hG hGc ht
    have hg := continuous_glue left hG hGc
    have hgc := hasCompactSupport_glue left hG hGc
    have hgS := tsupport_glue_side left hG hGc
    have hcomp : Continuous (glue left G ∘ Φ) := hg.comp Φ.continuous
    have hcompc : HasCompactSupport (glue left G ∘ Φ) :=
      IsCompact.of_isClosed_subset (hgc.image Φ.symm.continuous) (isClosed_tsupport _)
        (tsupport_comp_iso_subset hgc Φ)
    have hcompS : tsupport (glue left G ∘ Φ) ⊆ S := by
      refine (tsupport_comp_iso_subset hgc Φ).trans ?_
      rw [← hImS]; exact image_mono hgS
    have hl := (hν.2.2 _ hcomp hcompc hcompS).comp tendsto_one_goodFilter
    rw [integral_map Φ.continuous.aemeasurable hg.aestronglyMeasurable,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun t htS =>
        image_eq_zero_of_notMem_tsupport fun h => htS (hgS h)]
    exact tendsto_nhds_unique hl ht
  have hEq : ν.map Φ = (qBoundaryMeasure γ y).restrict S := by
    refine eq_of_glue_integrals left ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Measure.map_apply Φ.continuous.measurable hSm.compl, preimage_compl, hpre]; exact hν.1
    · rw [Measure.restrict_apply hSm.compl, compl_inter_self, measure_empty]
    · intro K hK hKS
      rw [Measure.map_apply Φ.continuous.measurable hK.isClosed.measurableSet]
      refine hν.2.1 _ ?_ ?_
      · rw [← himg]; exact hK.image Φ.symm.continuous
      · intro t ht
        have : t ∈ Φ ⁻¹' S := hKS ht
        rwa [hpre] at this
    · intro K hK _
      exact (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top
    · intro N m
      exact key _ (continuous_testFam N m) (hasCompactSupport_testFam N m)
        (hid _ (Or.inl ⟨N, m, rfl⟩))
    · intro N
      exact key _ (continuous_bump N) (hasCompactSupport_bump N) (hid _ (Or.inr ⟨N, rfl⟩))
  rw [← hEq, Measure.map_map Φ.symm.continuous.measurable Φ.continuous.measurable]
  have hid' : (Φ.symm ∘ Φ : ℝ → ℝ) = id := funext Φ.symm_apply_apply
  rw [hid', Measure.map_id]

end G1Z5
end Thm18Asm
end QuantumZipper
