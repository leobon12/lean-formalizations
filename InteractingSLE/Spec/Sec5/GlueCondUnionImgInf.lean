/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondUnionImgMean
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# G3 (ii): the union mean at the counterflow's start (physical `∞` in the chart `Q`)

Packet PROVE-GLUECOND6 (specification §4.2, proof of Lemma 4.7, p. 118: "Proposition 3.7 and Proposition 3.8 together
tell us that the boundary data … along `∂_U𝒮 ∪ η′([0, t])` agree with those of the conditional law of `h` given just
`η′|_{[0,t]}` alone"). PROVE-GLUECOND2's `ae_union_mean_cfGlue` gives this comparison at every finite boundary point;
the counterflow starts at `∞` of the chart `Q`, and if its trace returns to its start the prime ends of
`ℍ ∖ (A ∪ G)` at `∞` may be infinitely many (PROVE-GLUECOND4, "What remains" 4). They are all covered here at once:

* **`isZeroBoundaryGFF_reflectField`**: the reflection `−X ∘ R` (`R z = −1/z`) of a zero-boundary GFF on `ℍ` is a
  zero-boundary GFF (`isGFFWithBoundaryData_returnField` with zero data);
* **`reflectField_rep`**: a representative `v` of a distribution on `U` gives the representative `−v ∘ R` of the
  reflected distribution on `R(U)`;
* **`ae_tendsto_union_sub_cfMean_cobounded`** (Proposition 3.8 in the chart `R`, at the point `0 = R(∞)`): on the glued
  space, almost surely, for all harmonic representatives `w` of the union mean on `ℍ ∖ (A ∪ G)` and `w_G` of the
  counterflow hull's mean on `ℍ ∖ G`, `w(z) − w_G(z) → 0` as `|z| → ∞` in `ℍ ∖ (A ∪ G)` — no hypothesis on returns
  of the counterflow to its start. The flow hull `A = K_q` is bounded, so `R(A)` stays away from `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.GlueCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Sec7.StripSysField
open LocalSets (IsLocalSetMean)

/-! ### The reflected zero-boundary GFF -/

section Reflect

/-- **The reflection of a zero-boundary GFF on `ℍ` is a zero-boundary GFF.** -/
theorem isZeroBoundaryGFF_reflectField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P) :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => reflectField (X ω)) P := by
  have hz0 : IsBoundedHarmonicExtension (fun _ : ℝ => (0 : ℝ)) ((∅ : Finset ℝ) : Set ℝ) (fun _ => 0) :=
    ⟨fun z _ => InnerProductSpace.harmonicAt_const 0, ⟨0, fun _ _ => by simp⟩,
      fun _ _ => tendsto_const_nhds⟩
  -- `X` is a GFF with zero boundary data
  have hG : IsGFFWithBoundaryData P X (fun _ => 0) ((∅ : Finset ℝ) : Set ℝ) := by
    refine ⟨hX.1, fun u₀ hu₀ => ?_⟩
    have hu0 := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension (Set.toFinite _) hz0 hu₀
    have e : (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) = fun (φ : TestOn upperHalfPlaneOpens) ω => X ω φ := by
      funext φ ω
      have hi : (∫ z, u₀ z * φ z) = 0 := by
        rw [← integral_zero ℂ ℝ]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ H
        · simp only [hu0 hz, zero_mul]
        · simp only [image_eq_zero_of_notMem_tsupport fun h => hz (φ.tsupport_subset h), mul_zero]
      rw [hi, sub_zero]
    rw [e]
    exact hX.2
  have hR := isGFFWithBoundaryData_returnField 0 0 ⟨_, hz0⟩ hG
  have hzR : IsBoundedHarmonicExtension (returnData 0 0 fun _ => (0 : ℝ)) (returnExcept ∅ : Set ℝ) (fun _ => 0) :=
    ⟨fun z _ => InnerProductSpace.harmonicAt_const 0, ⟨0, fun _ _ => by simp⟩,
      fun x _ => by simp only [returnData, neg_zero, add_zero, zero_mul]; exact tendsto_const_nhds⟩
  refine ⟨measurable_reflectField.comp hX.1, ?_⟩
  have e : (fun φ ω => returnField 0 0 (X ω) φ - ∫ z, (fun _ => (0 : ℝ)) z * φ z) =
      fun (φ : TestOn upperHalfPlaneOpens) ω => reflectField (X ω) φ := by
    funext φ ω
    simp only [zero_mul, integral_zero, sub_zero]
    rfl
  rw [← e]
  exact hR.2 _ hzR

/-- **Representatives under the reflection**: if `v` represents `g` on `U ⊆ ℍ` (open), then `−v ∘ R` represents the
reflected distribution on `R(U)`. -/
theorem reflectField_rep {U : Set ℂ} {g : DistOn upperHalfPlaneOpens} {v : ℂ → ℝ}
    (hrep : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ U → g φ = ∫ z, v z * φ z)
    (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ negInv '' U) :
    reflectField g φ = ∫ z, -v (negInv z) * φ z := by
  have hsupp : tsupport (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ) ⊆ U := by
    refine (tsupport_pushTest_return_subset φ).trans ?_
    calc negInv '' tsupport φ ⊆ negInv '' (negInv '' U) := image_mono hφ
      _ = U := image_negInv_image_negInv U
  rw [reflectField_apply, hrep _ hsupp, Chart.integral_mul_pushTest, ← integral_neg]
  congr 1
  funext w
  simp only [neg_mul]
  rfl

end Reflect

/-! ### Proposition 3.8 at the counterflow's start -/

section Inf

/-- `R` sends `∞` within `C` to `0` within `R(C)`; a limit of `u` at `0` within `R(C)` is a limit of `u ∘ R` at `∞`
within `C`. -/
theorem tendsto_cobounded_of_negInv {C : Set ℂ} {u v : ℂ → ℝ} (huv : ∀ z ∈ C, u (negInv z) = v z)
    (hu : Tendsto u (𝓝[negInv '' C] 0) (𝓝 0)) : Tendsto v (Bornology.cobounded ℂ ⊓ 𝓟 C) (𝓝 0) := by
  have hR : Tendsto negInv (Bornology.cobounded ℂ ⊓ 𝓟 C) (𝓝[negInv '' C] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := (tendsto_inv₀_cobounded (α := ℂ)).neg
      rw [neg_zero] at h
      exact (h.mono_left inf_le_left).congr fun z => rfl
    · exact Filter.mem_of_superset (Filter.mem_inf_of_right (mem_principal_self C)) fun z hz =>
        mem_image_of_mem negInv hz
  refine (hu.comp hR).congr' ?_
  exact Filter.mem_of_superset (Filter.mem_inf_of_right (mem_principal_self C)) fun z hz => huv z hz

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

/-- **Proposition 3.8 at the counterflow's start** (the point `0` of the chart `R`, i.e. `∞` of the chart `Q`). In the
setting of `isLocalSet_union_glue`, for local-set means `g` of `A ∪ G` (`A = K_q` the flow hull, `G = R(K′_t)` the
counterflow hull) and `g_G` of `G`, for the centred field `h − 𝔥₀` on the glued space: almost surely, for all harmonic
representatives `w` of `g` on `ℍ ∖ (A ∪ G)` and `w_G` of `g_G` on `ℍ ∖ G`, `w − w_G → 0` at `∞` within
`ℍ ∖ (A ∪ G)`. With `ae_union_mean_cfGlue` this covers every prime end of `ℍ ∖ (A ∪ G)` away from `A`, also when the
counterflow returns to its start. -/
theorem ae_tendsto_union_sub_cfMean_cobounded (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0)
    {g gG : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
      (fun p => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) g)
    (hgG : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2)
      (fun p => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) gG) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)), ∀ w wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) → g p φ = ∫ z, w z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ cfHullQ t p.2) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ t p.2 → gG p φ = ∫ z, wG z * φ z) →
      Tendsto (fun z => w z - wG z)
        (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2))) (𝓝 0) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  set Aω : Ω → Set ℂ := fun ω => hullAt q (killedHistory W VL VR ζ ω) with hAωdef
  have hAm : Measurable[mΩ, hittingSigma] Aω := (measurable_hullAt q).comp (measurable_killedHistory hX)
  obtain ⟨hAg, hGg, -⟩ := isLocalSet_union_glue (k := k) hC hζ hcf hreg₂ hlaw hk hu₀ q t
  -- the glued field and its reflection are zero-boundary GFFs
  have hF0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenT κ u₀ (cfField κ (h ω))) P := by
    have e : (fun ω => cenT κ u₀ (cfField κ (h ω))) = WholeField.centredField h u₀ :=
      funext fun ω => cenT_cfField κ u₀ (h ω)
    rw [e]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 0 0 =>
      cenT κ u₀ (cfField κ (h p.1))) μ :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => cenT κ u₀ (cfField κ (h ω))) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hXm) hF0
  have hFR := isZeroBoundaryGFF_reflectField hF
  -- the reflected hulls: `R(A)` and `R(G) = K′_t`
  have hA₁ : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 => negInv '' Aω p.1 := by
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    exact measurable_image_negInv.comp (hAm.comp measurable_fst)
  have hA₂ : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 => hullAt t p.2 := by
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    exact (measurable_hullAt t).comp measurable_snd
  have hAωR : Measurable[mΩ, hittingSigma] fun ω => negInv '' Aω ω := by
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    exact measurable_image_negInv.comp hAm
  have hci := condIndepEv_glue_sets (P := P) hXm k (T := fun f => reflectField (cenT κ u₀ f))
    (measurable_reflectField.comp (measurable_cenT κ u₀)) (T' := fun f => cenT' κ u₀ (reflectField f))
    ((measurable_cenT' κ u₀).comp measurable_reflectField)
    (fun f => by
      show cenT' κ u₀ (reflectField (reflectField (cenT κ u₀ f))) = f
      rw [reflectField_reflectField, cenT'_cenT]) hAωR (measurable_hullAt t)
  have hGG : (fun p : Ω × HistorySpace 0 0 => negInv '' cfHullQ t p.2) = fun p => hullAt t p.2 :=
    funext fun p => image_negInv_image_negInv _
  have h₁ := WangWu.IsLocalSet.reflect hAg
  have h₂ := WangWu.IsLocalSet.reflect hGg
  rw [hGG] at h₂
  have hunb : ∀ᵐ p ∂μ, ∀ z ∈ LocalSets.lowerUnion (hullAt t p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion (hullAt t p.2)) z) :=
    Eventually.of_forall fun p => not_isBounded_lowerUnion_of_isHPHull (isHPHull_hullAt _ _)
  have hrel : ∀ p : Ω × HistorySpace 0 0, (Aω p.1 ∪ cfHullQ t p.2) ⊆ H ∧ IsOpen (H \ (Aω p.1 ∪ cfHullQ t p.2)) := by
    intro p
    obtain ⟨h1, h1o⟩ := hullAt_relClosed q (killedHistory W VL VR ζ p.1)
    obtain ⟨h2, h2o⟩ := cfHullQ_relClosed t p.2
    refine ⟨union_subset h1 h2, ?_⟩
    rw [← Set.sdiff_inter_sdiff]; exact h1o.inter h2o
  have hg' := WangWu.IsLocalSetMean.reflect hrel hg
  have hUU : (fun p : Ω × HistorySpace 0 0 => negInv '' (Aω p.1 ∪ cfHullQ t p.2)) =
      fun p => negInv '' Aω p.1 ∪ hullAt t p.2 := by
    funext p; rw [image_union, cfHullQ, image_negInv_image_negInv]
  have hg'' : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => negInv '' Aω p.1 ∪ hullAt t p.2)
      (fun p => reflectField (cenT κ u₀ (cfField κ (h p.1)))) μ (fun p => reflectField (g p)) := by
    rw [← hUU]; exact hg'
  have hgG' : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt t p.2)
      (fun p => reflectField (cenT κ u₀ (cfField κ (h p.1)))) μ (fun p => reflectField (gG p)) := by
    have := WangWu.IsLocalSetMean.reflect (A := fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2)
      (h := fun p => cenT κ u₀ (cfField κ (h p.1))) (g := gG) (fun p => cfHullQ_relClosed t p.2) hgG
    rw [hGG] at this
    exact this
  have h38 := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hFR hA₁ hA₂ hci h₁ h₂ hunb hg'' hgG'
  filter_upwards [h38] with p ⟨u, hu, hrep, hlim⟩
  intro w wG hw hrepw hwG hrepwG
  set C := H \ (Aω p.1 ∪ cfHullQ t p.2) with hCdef
  have hCo : IsOpen C := (hrel p).2
  have hCH : C ⊆ H := sdiff_subset
  have hCG : C ⊆ H \ cfHullQ t p.2 := fun z hz => ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩
  have hRC : H \ (negInv '' Aω p.1 ∪ hullAt t p.2) = negInv '' C := by
    rw [← image_negInv_image_negInv (hullAt t p.2), ← image_union, H_diff_image_negInv]
    rfl
  -- `u = −w ∘ R + w_G ∘ R` on `R(C)`
  have hRCo : IsOpen (negInv '' C) := isOpen_image_negInv hCo hCH
  have hRCH : negInv '' C ⊆ H := image_negInv_subset_H hCH
  have hw' := harmonicOnNhd_comp_negInv hCo hCH hw
  have hwG' := harmonicOnNhd_comp_negInv hCo hCH (fun z hz => hwG z (hCG hz))
  have hv : InnerProductSpace.HarmonicOnNhd (fun z => -w (negInv z) + wG (negInv z)) (negInv '' C) :=
    fun z hz => (hw' z hz).neg.add (hwG' z hz)
  have hcont : ∀ {v : ℂ → ℝ} {U : Set ℂ}, InnerProductSpace.HarmonicOnNhd v U → ContinuousOn v U :=
    fun hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hu' : InnerProductSpace.HarmonicOnNhd u (negInv '' C) := by rw [← hRC]; exact hu
  have heq : EqOn u (fun z => -w (negInv z) + wG (negInv z)) (negInv '' C) := by
    refine Sec6.eqOn_of_integral_mul_eq hRCo hRCH hu' hv fun φ hφ => ?_
    have hφ' : tsupport φ ⊆ H \ (negInv '' Aω p.1 ∪ hullAt t p.2) := by rw [hRC]; exact hφ
    have i1 := LocalSets.integrable_mul_test hRCo (hcont hw').neg φ hφ
    have i2 := LocalSets.integrable_mul_test hRCo (hcont hwG') φ hφ
    have e1 := reflectField_rep hrepw φ hφ
    have e2 := reflectField_rep (U := H \ cfHullQ t p.2) hrepwG φ (hφ.trans (image_mono hCG))
    rw [← hrep φ hφ', e1, e2]
    have i1' : Integrable fun z => -w (negInv z) * φ z := i1
    have i2' : Integrable fun z => -wG (negInv z) * φ z := by
      refine i2.neg.congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.neg_apply, Function.comp_apply, neg_mul]
    rw [← integral_sub i1' i2']
    congr 1; funext z; ring
  -- the limit at `0` of the chart `R`
  obtain ⟨M, hM⟩ := (isHPHull_hullAt q (killedHistory W VL VR ζ p.1)).2.1.subset_closedBall 0
  have hM0 : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hloc : ∃ r > 0, negInv '' Aω p.1 ∩ ball 0 r ⊆ hullAt t p.2 := by
    refine ⟨(max M 1)⁻¹, inv_pos.2 hM0, ?_⟩
    rintro _ ⟨⟨a, ha, rfl⟩, hb⟩
    exfalso
    have ha' : ‖a‖ ≤ max M 1 := by
      have := hM ha
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have ha0 : a ≠ 0 := ne_zero_of_mem_H ((hullAt_relClosed q _).1 ha)
    rw [mem_ball, dist_zero_right, norm_negInv] at hb
    have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
    have := (inv_lt_inv₀ hapos hM0).1 hb
    linarith
  have h0 := hlim 0 (Or.inr (by simp)) hloc
  rw [hRC] at h0
  refine tendsto_cobounded_of_negInv (u := fun z => -u z) (fun z hz => ?_) ?_
  · have := heq (mem_image_of_mem negInv hz)
    simp only [WangWu.negInv_negInv] at this
    rw [this]; ring
  · simpa using h0.neg

end Inf

end InteractingSLE.Sec5.GlueCond
