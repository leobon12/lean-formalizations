/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeightBoxSingle
import InteractingSLE.Spec.Sec7.Lemma78MeanAssembly

/-!
# The union mean against a single-prefix mean: Proposition 3.8 twice

Packet PROVE-SIDEHEIGHT2 (specification Lemma 7.8, p. 293: "The relative zero-GFF boundary comparison, with
separation from the added range, identifies its mean germ there with the known single-path germ at `r`"). For two
field-determined local sets `A`, `B` of a zero-boundary GFF whose lower unions have only unbounded components, the
union `A ∪ B` is a field-determined local set (Wang–Wu Lemma 4.5), and Proposition 3.8 applied to `(A, B)` and to
`(B, A)` compares the harmonic representatives of the two means at every point near which the two sets agree:
`v_A − v_B → 0` there (`ae_tendsto_sub_of_locals`). This avoids identifying the mean of a selected (non-stopping)
union with the mean of an enlarged one: only boundary values are compared.

The two sets of Lemma 7.8's comparison are the first-contact union of the capped flow lines (`fcUnion_facts`) and the
range of one capped flow line at a deterministic stop (`range_facts`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace SideHeightBox

open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF CondIndepEv)
open LocalSets Sec6 Restart

/-! ### Proposition 3.8 twice -/

section Generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Two field-determined local sets have the same mean boundary values where they agree** (Proposition 3.8 for
`(A, B)` and for `(B, A)`, through the mean of the union). -/
theorem ae_tendsto_sub_of_locals (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A B : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hBm : Measurable[mΩ, hittingSigma] B) (hAloc : IsLocalSet A h P)
    (hBloc : IsLocalSet B h P)
    (hAdet : MeasurableSpace.comap A hittingSigma ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hBdet : MeasurableSpace.comap B hittingSigma ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hAunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω), ¬ IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hBunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B ω), ¬ IsBounded (connectedComponentIn (lowerUnion (B ω)) z))
    {gA gB : Ω → DistOn upperHalfPlaneOpens} (hgA : IsLocalSetMean A h P gA) (hgB : IsLocalSetMean B h P gB) :
    ∀ᵐ ω ∂P, ∀ vA vB : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd vA (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → gA ω φ = ∫ z, vA z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ B ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → gB ω φ = ∫ z, vB z * φ z) →
      ∀ p : ℂ, p ∈ A ω ∪ {z : ℂ | z.im = 0} → p ∈ B ω ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, B ω ∩ ball p r ⊆ A ω) → (∃ r > 0, A ω ∩ ball p r ⊆ B ω) →
      Tendsto (fun z => vA z - vB z) (𝓝[H \ (A ω ∪ B ω)] p) (𝓝 0) := by
  have hhm := hh.measurable
  obtain ⟨hUloc, -⟩ := WangWu.isLocalSet_union_of_aeDetermined hh hAm hBm hAloc hBloc
    (fun s hs => hAdet s hs) (fun s hs => hBdet s hs)
  obtain ⟨gU, hgU⟩ := IsLocalSet.exists_isLocalSetMean hh (measurable_union_hitting hAm hBm) hUloc
  have hci₁ : CondIndepEv (MeasurableSpace.comap h inferInstance) (MeasurableSpace.comap A hittingSigma)
      (MeasurableSpace.comap B hittingSigma) P := condIndepEv_of_le_aeSigma hhm.comap_le hBm.comap_le hAdet
  have hci₂ : CondIndepEv (MeasurableSpace.comap h inferInstance) (MeasurableSpace.comap B hittingSigma)
      (MeasurableSpace.comap A hittingSigma) P := condIndepEv_of_le_aeSigma hhm.comap_le hAm.comap_le hBdet
  have hgU' : IsLocalSetMean (fun ω => B ω ∪ A ω) h P gU := by
    have e : (fun ω => B ω ∪ A ω) = fun ω => A ω ∪ B ω := funext fun ω => union_comm _ _
    rw [e]
    exact hgU
  have h1 := IsLocalSetMean.ae_tendsto_sub_of_union hh hBm hAm hci₂ hBloc hAloc hAunb hgU' hgA
  have h2 := IsLocalSetMean.ae_tendsto_sub_of_union hh hAm hBm hci₁ hAloc hBloc hBunb hgU hgB
  filter_upwards [h1, h2, hAloc.2.1, hBloc.2.1] with ω ⟨ua, hua, huar, hual⟩ ⟨ub, hub, hubr, hubl⟩ hAo hBo
    vA vB hvA hvAr hvB hvBr p hpA hpB hBA hAB
  rw [union_comm (B ω) (A ω)] at hua huar hual
  have hO : IsOpen (H \ (A ω ∪ B ω)) := by
    have e : H \ (A ω ∪ B ω) = (H \ A ω) ∩ (H \ B ω) := by
      ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
    rw [e]
    exact hAo.2.inter hBo.2
  exact tendsto_sub_of_union_means hO (sdiff_subset_sdiff_right subset_union_left)
    (sdiff_subset_sdiff_right subset_union_right) hvA hvAr hvB hvBr hua huar hub hubr (hual p hpA hBA)
    (hubl p hpB hAB)

end Generic

/-! ### The two local sets of the comparison -/

section Flow

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The range of a capped flow line at a deterministic stop** is a hitting-measurable, field-determined local set of
the centred field whose lower union has only unbounded components (PROVE-SIDEHEIGHT's construction, Lemma 6.2 through
`exists_twoHist_versions`). -/
theorem range_facts (hL75 : Theorem15.Lemma75Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {x θ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m q : ℝ≥0) {ηc : Ω → ℝ≥0 → ℂ}
    (hηcc : ∀ ω, Continuous (ηc ω)) (hηcm : ∀ t, Measurable fun ω => ηc ω t)
    (hηce : ∀ᵐ ω ∂P, ∀ t, ηc ω t = η ω (capTime m (ζ ω) t)) :
    Measurable[mΩ, hittingSigma] (fun ω => ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H) ∧
    IsLocalSet (fun ω => ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H) (WholeField.centredField h u₀) P ∧
    MeasurableSpace.comap (fun ω => ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
    ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H),
      ¬ IsBounded (connectedComponentIn (lowerUnion (ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H)) z) := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨ηs, hc, h0, hηm, hdet, hloc, hfr, him, hs₁, -⟩ :=
    exists_twoHist_versions hL75 hA56 hκ hκ4 hb hh hη hη hu₀ m
  set s₂ : Fin 2 → ℝ≥0∞ := ![(q : ℝ≥0∞), 0] with hs₂
  have hA₁'loc := isLocalSet_explored_const hh0 hc h0 hηm hdet hloc hfr s₂
  have hA₁'det := comap_explored_const_le_aeSigma hc hdet s₂
  have hA₁'eq : ∀ ω, explored ηs (fun i _ => s₂ i) ω = ηs 0 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H := fun ω =>
    explored_pair_left ηs q (by rw [h0 1 ω]; simp)
  set A₁ : Ω → Set ℂ := fun ω => ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H with hA₁_def
  have hA₁A₁' : A₁ =ᵐ[P] explored ηs fun i _ => s₂ i := by
    filter_upwards [hηce, hs₁] with ω h1 h2
    rw [hA₁'eq]
    have : ηc ω = ηs 0 ω := funext fun t => (h1 t).trans (h2 t).symm
    show ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = _
    rw [this]
  have hA₁loc := Coupling.IsLocalSet.congr_set hA₁'loc hA₁A₁'
  have hA₁det := SideHeight.comap_le_aeSigma_of_ae_eq hA₁A₁' hA₁'det
  have e : ∀ ω, (explored (fun _ : Fin 1 => ηc) fun _ _ => (q : ℝ≥0∞)) ω = A₁ ω := fun ω => by
    simp only [explored, iUnion_const, hA₁_def]
  have hA₁m : Measurable[_, hittingSigma] A₁ := by
    have h1 := measurable_explored_const (η := fun _ : Fin 1 => ηc) (fun _ => hηcc) (fun _ => hηcm)
      (fun _ => (q : ℝ≥0∞))
    rwa [show (explored (fun _ : Fin 1 => ηc) fun _ _ => (q : ℝ≥0∞)) = A₁ from funext e] at h1
  refine ⟨hA₁m, hA₁loc, hA₁det, ?_⟩
  filter_upwards [hηce, hs₁, him] with ω h1 h2 h3
  have hηs : ηc ω = ηs 0 ω := funext fun t => (h1 t).trans (h2 t).symm
  have e' : ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = (explored (fun _ : Fin 1 => ηc) fun _ _ => (q : ℝ≥0∞)) ω :=
    (e ω).symm
  rw [e']
  refine not_isBounded_lowerUnion_explored (fun _ => hηcc ω) (fun _ => ?_) (fun _ t => ?_)
  · rw [hηs, h0 0 ω]; simp
  · rw [hηs]; exact h3 0 t

/-- **The first-contact union of two capped flow lines** is a hitting-measurable, field-determined local set of the
centred field (Lemma 7.7's marked locality, PROVE-PRIMEEND2's `isLocalSet_fcUnion_of_isFlowLine`) whose lower union
has only unbounded components. -/
theorem fcUnion_facts (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω)) (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t)
    (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t) (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) :
    Measurable[mΩ, hittingSigma] (fcUnion ηc₁ ηc₂) ∧
    IsLocalSet (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) P ∧
    MeasurableSpace.comap (fcUnion ηc₁ ηc₂) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
    ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (fcUnion ηc₁ ηc₂ ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (fcUnion ηc₁ ηc₂ ω)) z) := by
  obtain ⟨ηs, hc, h0, hηm, hdet, -, -, him, hs₁, hs₂⟩ :=
    exists_twoHist_versions hL75 hA56 hκ hκ4 hb hh hη₁ hη₂ hu₀ m
  refine ⟨measurable_fcUnion hc₁ hc₂ hm₁ hm₂,
    isLocalSet_fcUnion_of_isFlowLine hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ m hag₁ hag₂, ?_, ?_⟩
  · have hηsm : ∀ i t, Measurable[aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P]
        fun ω => ηs i ω t := fun i t => by
      obtain ⟨f, hf, he⟩ := hdet i t
      exact measurable_aeSigma_of_ae_eq hf he
    have hmeas := @measurable_fcUnion Ω (aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀)
      inferInstance) P) (ηs 0) (ηs 1) (hc 0) (hc 1) (hηsm 0) (hηsm 1)
    have hae : fcUnion ηc₁ ηc₂ =ᵐ[P] fcUnion (ηs 0) (ηs 1) := by
      filter_upwards [hag₁, hag₂, hs₁, hs₂] with ω h1 h2 h3 h4
      have e1 : ηc₁ ω = ηs 0 ω := funext fun t => (h1 t).trans (h3 t).symm
      have e2 : ηc₂ ω = ηs 1 ω := funext fun t => (h2 t).trans (h4 t).symm
      exact fcUnion_congr e1 e2
    exact SideHeight.comap_le_aeSigma_of_ae_eq hae hmeas.comap_le
  · filter_upwards [hag₁, hag₂, hs₁, hs₂, him] with ω h1 h2 h3 h4 h5
    have e1 : ηc₁ ω = ηs 0 ω := funext fun t => (h1 t).trans (h3 t).symm
    have e2 : ηc₂ ω = ηs 1 ω := funext fun t => (h2 t).trans (h4 t).symm
    refine not_isBounded_lowerUnion_explored (η := pairPath ηc₁ ηc₂) (τ := fcLine ηc₁ ηc₂) (ω := ω)
      (fun i => ?_) (fun i => ?_) (fun i t => ?_)
    · fin_cases i
      exacts [hc₁ ω, hc₂ ω]
    · fin_cases i
      · show (ηc₁ ω 0).im = 0
        rw [e1, h0 0 ω]; simp
      · show (ηc₂ ω 0).im = 0
        rw [e2, h0 1 ω]; simp
    · fin_cases i
      · show 0 ≤ (ηc₁ ω t).im
        rw [e1]; exact h5 0 t
      · show 0 ≤ (ηc₂ ω t).im
        rw [e2]; exact h5 1 t

end Flow

end SideHeightBox

end Sec7

end InteractingSLE
