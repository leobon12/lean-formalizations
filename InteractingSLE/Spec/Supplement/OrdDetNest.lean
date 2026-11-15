/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetZoneMean

/-!
# Proposition 3.8 in the stop-line chart for two nested retained unions

Packet PROVE-T15-ORDDET (Theorem 1.5's leaf 3; specification Aux. lemma 79, pp. 289–290: the later-line mean is compared
with the stop-line mean, "with the earlier marked information included in the later one"). For the two flow lines of
Theorem 1.5's retained pair and cutoffs `(a, c) ≤ (a', c')`, the stopped unions `A₂ = (η₁[0, a] ∪ η₂[0, c]) ∩ ℍ ⊆
A = (η₁[0, a'] ∪ η₂[0, c']) ∩ ℍ` are nested history-marked local sets. Proposition 3.8 in a chart
(`RetZone.ae_tendsto_zero_of_history`, PROVE-T15-RET6) in the chart of the smaller filled union gives
**`ae_tendsto_sub_nested`**: almost surely on `{a' < ζ₁, c' < ζ₂}`, the difference of the two local-set means is a
harmonic function `v` off `A` that tends to `0` along every approach within `ℍ \ fill(η₁[0, a] ∪ η₂[0, c])` on which the
mapping-out function of that filled union tends to a real point whose ball contains no image of a point of the larger
union.

The marks are the killed histories of good capped versions (`Restart.exists_capped_version`, cap `m₁`); the smaller
history is the restriction of the larger one (`Restart.khistRestrict_khistOf`); locality is
`Sec7.Lemma76F.isHistoryAvoidanceLocal_cstUnion`. The given versions may be capped at different caps `m₀`, `m₁` (each
above its own cutoffs); capped paths agree below both caps (`capTime_eq_capTime`).

For Theorem 1.5; uses Lemma 7.5 (field determination) only (R43/R48: no Theorem 1.2/1.3 input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

namespace OrdDet

open Sec7 Sec7.Lemma76F Sec7.Lemma76G Restart LocalSets RetZone

/-- Capped paths agree below both caps. -/
theorem capTime_eq_capTime {m m' t : ℝ≥0} (hm : t < m) (hm' : t < m') (ζ : ℝ≥0∞) :
    capTime m ζ t = capTime m' ζ t := by
  unfold capTime
  rcases eq_or_ne ζ ⊤ with rfl | hζ
  · simp only [min_eq_right le_top, ENNReal.toNNReal_coe, min_eq_left hm.le, min_eq_left hm'.le]
  · lift ζ to ℝ≥0 using hζ
    rw [← ENNReal.coe_min, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
    rcases le_total t ζ with htz | htz
    · rw [min_eq_left (le_min htz hm.le), min_eq_left (le_min htz hm'.le)]
    · rw [← min_assoc, ← min_assoc, min_eq_right htz, min_eq_left (htz.trans hm.le),
        min_eq_left (htz.trans hm'.le)]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Proposition 3.8 in the stop-line chart for two nested retained unions** (see the module docstring). -/
theorem ae_tendsto_sub_nested (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {a c a' c' m₀ m₁ : ℝ≥0} (haa : a ≤ a') (hcc : c ≤ c') (ham : a < m₀) (hcm : c < m₀) (ham' : a' < m₁)
    (hcm' : c' < m₁) {ηa₁ ηa₂ ηb₁ ηb₂ : Ω → ℝ≥0 → ℂ}
    (hca₁ : ∀ ω, Continuous (ηa₁ ω)) (hca₂ : ∀ ω, Continuous (ηa₂ ω))
    (hcb₁ : ∀ ω, Continuous (ηb₁ ω)) (hcb₂ : ∀ ω, Continuous (ηb₂ ω))
    (hma₁ : ∀ t, Measurable fun ω => ηa₁ ω t) (hma₂ : ∀ t, Measurable fun ω => ηa₂ ω t)
    (hmb₁ : ∀ t, Measurable fun ω => ηb₁ ω t) (hmb₂ : ∀ t, Measurable fun ω => ηb₂ ω t)
    (haga₁ : ∀ᵐ ω ∂P, ∀ t, ηa₁ ω t = η₁ ω (capTime m₀ (ζ₁ ω) t))
    (haga₂ : ∀ᵐ ω ∂P, ∀ t, ηa₂ ω t = η₂ ω (capTime m₀ (ζ₂ ω) t))
    (hagb₁ : ∀ᵐ ω ∂P, ∀ t, ηb₁ ω t = η₁ ω (capTime m₁ (ζ₁ ω) t))
    (hagb₂ : ∀ᵐ ω ∂P, ∀ t, ηb₂ ω t = η₂ ω (capTime m₁ (ζ₂ ω) t))
    {g₀ g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg₀ : IsLocalSetMean (cstUnion ηa₁ ηa₂ a c) (WholeField.centredField h u₀) P g₀)
    (hg₁ : IsLocalSetMean (cstUnion ηb₁ ηb₂ a' c') (WholeField.centredField h u₀) P g₁) :
    ∀ᵐ ω ∂P, (a' : ℝ≥0∞) < ζ₁ ω → (c' : ℝ≥0∞) < ζ₂ ω →
      ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ cstUnion ηb₁ ηb₂ a' c' ω) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cstUnion ηb₁ ηb₂ a' c' ω →
          g₁ ω φ - g₀ ω φ = ∫ z, v z * φ z) ∧
        ∀ y ρ : ℝ, 0 < ρ → (∀ z ∈ H \ fillH (prefixSet (η₁ ω) a (η₂ ω) c),
            ConformalImage.mapOut (fillH (prefixSet (η₁ ω) a (η₂ ω) c)) z ∈ ball (y : ℂ) ρ →
              z ∉ prefixSet (η₁ ω) a' (η₂ ω) c') →
          ∀ F : Filter ℂ, F ≤ 𝓟 (H \ fillH (prefixSet (η₁ ω) a (η₂ ω) c)) →
            Tendsto (ConformalImage.mapOut (fillH (prefixSet (η₁ ω) a (η₂ ω) c))) F (𝓝 (y : ℂ)) →
              Tendsto v F (𝓝 0) := by
  classical
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hhm := hh0.measurable
  -- good capped versions, their killed histories and their marked locality
  obtain ⟨ηg₁, hcg₁, hmg₁, h0g₁, -, hagg₁, hdetg₁, hdetζg₁⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m₁
  obtain ⟨ηg₂, hcg₂, hmg₂, h0g₂, -, hagg₂, hdetg₂, hdetζg₂⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m₁
  have hloc₁ := WholeField.retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ u₀ hu₀ m₁ ηg₁
    hcg₁ hmg₁ hagg₁
  have hloc₂ := WholeField.retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ u₀ hu₀ m₁ ηg₂
    hcg₂ hmg₂ hagg₂
  set ζl₁ : Ω → ℝ≥0∞ := fun ω => cutLife (ζ₁ ω) m₁ with hζl₁
  set ζl₂ : Ω → ℝ≥0∞ := fun ω => cutLife (ζ₂ ω) m₁ with hζl₂
  have hζlm₁ : Measurable ζl₁ := (measurable_cutLife _).comp (measurable_lifetime_of_isFlowLine hη₁)
  have hζlm₂ : Measurable ζl₂ := (measurable_cutLife _).comp (measurable_lifetime_of_isFlowLine hη₂)
  have hlocA' := isHistoryAvoidanceLocal_cstUnion (u := a') (r := c') hhm hcg₁ hcg₂ h0g₁ h0g₂ hmg₁ hmg₂ hζlm₁
    hζlm₂ hdetg₁ hdetg₂ hdetζg₁ hdetζg₂ hloc₁ hloc₂
  have hlocA₂' := isHistoryAvoidanceLocal_cstUnion (u := a) (r := c) hhm hcg₁ hcg₂ h0g₁ h0g₂ hmg₁ hmg₂ hζlm₁
    hζlm₂ hdetg₁ hdetg₂ hdetζg₁ hdetζg₂ hloc₁ hloc₂
  -- the two sets and their almost sure agreement with the good versions
  set A : Ω → Set ℂ := cstUnion ηb₁ ηb₂ a' c' with hAdef
  set A₂ : Ω → Set ℂ := cstUnion ηa₁ ηa₂ a c with hA₂def
  have hAm : Measurable[mΩ, hittingSigma] A := measurable_cstUnion hcb₁ hcb₂ hmb₁ hmb₂ a' c'
  have hA₂m : Measurable[mΩ, hittingSigma] A₂ := measurable_cstUnion hca₁ hca₂ hma₁ hma₂ a c
  have hverb₁ : ∀ᵐ ω ∂P, ∀ t, ηb₁ ω t = ηg₁ ω t := by
    filter_upwards [hagb₁, hagg₁] with ω h1 h2 t; rw [h1, h2]
  have hverb₂ : ∀ᵐ ω ∂P, ∀ t, ηb₂ ω t = ηg₂ ω t := by
    filter_upwards [hagb₂, hagg₂] with ω h1 h2 t; rw [h1, h2]
  have hvera₁ : ∀ᵐ ω ∂P, ∀ t ≤ a, ηa₁ ω t = ηg₁ ω t := by
    filter_upwards [haga₁, hagg₁] with ω h1 h2 t ht
    rw [h1, h2, capTime_eq_capTime (ht.trans_lt ham) (ht.trans_lt (haa.trans_lt ham'))]
  have hvera₂ : ∀ᵐ ω ∂P, ∀ t ≤ c, ηa₂ ω t = ηg₂ ω t := by
    filter_upwards [haga₂, hagg₂] with ω h1 h2 t ht
    rw [h1, h2, capTime_eq_capTime (ht.trans_lt hcm) (ht.trans_lt (hcc.trans_lt hcm'))]
  have hAae : ∀ᵐ ω ∂P, cstUnion ηg₁ ηg₂ a' c' ω = A ω := by
    filter_upwards [hverb₁, hverb₂] with ω h1 h2
    have e1 : ηg₁ ω = ηb₁ ω := funext fun t => (h1 t).symm
    have e2 : ηg₂ ω = ηb₂ ω := funext fun t => (h2 t).symm
    simp only [hAdef, cstUnion_eq, e1, e2]
  have hA₂ae : ∀ᵐ ω ∂P, cstUnion ηg₁ ηg₂ a c ω = A₂ ω := by
    filter_upwards [hvera₁, hvera₂] with ω h1 h2
    have e1 : ηg₁ ω '' Icc 0 a = ηa₁ ω '' Icc 0 a := image_congr fun t ht => (h1 t ht.2).symm
    have e2 : ηg₂ ω '' Icc 0 c = ηa₂ ω '' Icc 0 c := image_congr fun t ht => (h2 t ht.2).symm
    simp only [hA₂def, cstUnion_eq, e1, e2]
  have hlocA := Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae hAae hlocA'
  have hlocA₂ := Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae hA₂ae hlocA₂'
  -- the marks
  have hℋ : sideMark ηg₁ ηg₂ ζl₁ ζl₂ a' c' ≤ mΩ := (measurable_cstHist hmg₁ hmg₂ hζlm₁ hζlm₂ a' c').comap_le
  have hℋ₁ : sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c ≤ sideMark ηg₁ ηg₂ ζl₁ ζl₂ a' c' := by
    have e : cstHist ηg₁ ηg₂ ζl₁ ζl₂ a c =
        (fun p : KHist × KHist => (khistRestrict p.1 a, khistRestrict p.2 c)) ∘ cstHist ηg₁ ηg₂ ζl₁ ζl₂ a' c' := by
      funext ω
      simp only [Function.comp, cstHist]
      rw [khistRestrict_khistOf (ENNReal.coe_le_coe.2 haa), khistRestrict_khistOf (ENNReal.coe_le_coe.2 hcc)]
    have hR : Measurable fun p : KHist × KHist => (khistRestrict p.1 a, khistRestrict p.2 c) :=
      (measurable_khistRestrict.comp (measurable_fst.prodMk measurable_const)).prodMk
        (measurable_khistRestrict.comp (measurable_snd.prodMk measurable_const))
    unfold sideMark
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hR.comap_le
  -- the smaller prefixes are recorded by the smaller history
  have hrec₁ : ∀ t ≤ a, Measurable[sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c] fun ω => ηg₁ ω t := by
    intro t ht
    have e : (fun ω => ηg₁ ω t) = fun ω => Restart.recon (cstHist ηg₁ ηg₂ ζl₁ ζl₂ a c ω).1.1 t := by
      funext ω
      exact (Restart.recon_histOf (T' := ⊤) (by simpa using hcg₁ ω) le_top (ENNReal.coe_le_coe.2 ht)).symm
    rw [e]
    exact (Restart.measurable_recon t).comp (measurable_fst.comp (measurable_fst.comp (comap_measurable _)))
  have hrec₂ : ∀ t ≤ c, Measurable[sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c] fun ω => ηg₂ ω t := by
    intro t ht
    have e : (fun ω => ηg₂ ω t) = fun ω => Restart.recon (cstHist ηg₁ ηg₂ ζl₁ ζl₂ a c ω).2.1 t := by
      funext ω
      exact (Restart.recon_histOf (T' := ⊤) (by simpa using hcg₂ ω) le_top (ENNReal.coe_le_coe.2 ht)).symm
    rw [e]
    exact (Restart.measurable_recon t).comp (measurable_fst.comp (measurable_snd.comp (comap_measurable _)))
  -- the smaller union is recorded by the marks
  have hA₂ℋ : MeasurableSpace.comap A₂ hittingSigma ≤ aeSigma (MeasurableSpace.comap A hittingSigma ⊔
      sideMark ηg₁ ηg₂ ζl₁ ζl₂ a' c') P := by
    set ηs₁ : Ω → ℝ≥0 → ℂ := fun ω t => ηg₁ ω (min t a) with hηs₁
    set ηs₂ : Ω → ℝ≥0 → ℂ := fun ω t => ηg₂ ω (min t c) with hηs₂
    have hcs₁ : ∀ ω, Continuous (ηs₁ ω) := fun ω => (hcg₁ ω).comp (continuous_id.min continuous_const)
    have hcs₂ : ∀ ω, Continuous (ηs₂ ω) := fun ω => (hcg₂ ω).comp (continuous_id.min continuous_const)
    have hms₁ : ∀ t, Measurable[sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c] fun ω => ηs₁ ω t :=
      fun t => hrec₁ (min t a) (min_le_right _ _)
    have hms₂ : ∀ t, Measurable[sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c] fun ω => ηs₂ ω t :=
      fun t => hrec₂ (min t c) (min_le_right _ _)
    have hBm := @measurable_cstUnion Ω (sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c) ηs₁ ηs₂ hcs₁ hcs₂ hms₁ hms₂ a c
    have hBeq : ∀ ω, cstUnion ηs₁ ηs₂ a c ω = cstUnion ηg₁ ηg₂ a c ω := fun ω => by
      have e1 : ηs₁ ω '' Icc 0 a = ηg₁ ω '' Icc 0 a :=
        image_congr fun t ht => by simp only [hηs₁, min_eq_left ht.2]
      have e2 : ηs₂ ω '' Icc 0 c = ηg₂ ω '' Icc 0 c :=
        image_congr fun t ht => by simp only [hηs₂, min_eq_left ht.2]
      rw [cstUnion_eq, cstUnion_eq, e1, e2]
    have hae : A₂ =ᵐ[P] cstUnion ηs₁ ηs₂ a c := by
      filter_upwards [hA₂ae] with ω hω
      rw [hBeq, hω]
    have h1 := (@WholeField.measurable_aeSigma_of_ae_eq' Ω mΩ P (Set ℂ) hittingSigma _ A₂ _ hBm hae).comap_le
    exact h1.trans (Sec7.FlatClockProof.aeSigma_mono (hℋ₁.trans le_sup_right))
  have hgsub : ∀ ω, cstUnion ηg₁ ηg₂ a c ω ⊆ cstUnion ηg₁ ηg₂ a' c' ω := fun ω => by
    rw [cstUnion_eq, cstUnion_eq]
    exact inter_subset_inter_left _ (union_subset_union (image_mono (Icc_subset_Icc_right haa))
      (image_mono (Icc_subset_Icc_right hcc)))
  have hclosed : ∀ᵐ ω ∂P, (A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧ (A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧ A₂ ω ⊆ A ω := by
    filter_upwards [hAae, hA₂ae] with ω h1 h2
    refine ⟨cstUnion_relClosed hcb₁ hcb₂ a' c' ω, cstUnion_relClosed hca₁ hca₂ a c ω, ?_⟩
    rw [← h1, ← h2]
    exact hgsub ω
  -- the chart: the mapping-out function of the filled smaller union
  set K₀ : Ω → Set ℂ := fun ω => ηg₁ ω '' Icc 0 a ∪ ηg₂ ω '' Icc 0 c with hK₀
  have hKc : ∀ ω, IsCompact (K₀ ω) := fun ω =>
    (isCompact_Icc.image (hcg₁ ω)).union (isCompact_Icc.image (hcg₂ ω))
  have hKp : ∀ ω, IsPreconnected (K₀ ω ∪ Restart.lowerHalf) := by
    intro ω
    have h1 : IsPreconnected (ηg₁ ω '' Icc 0 a ∪ Restart.lowerHalf) :=
      (isPreconnected_Icc.image _ (hcg₁ ω).continuousOn).union (ηg₁ ω 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
        (by show (ηg₁ ω 0).im ≤ 0; rw [h0g₁ ω]; simp) InteractingSLE.isPreconnected_lowerHalf
    have h2 : IsPreconnected (ηg₂ ω '' Icc 0 c ∪ Restart.lowerHalf) :=
      (isPreconnected_Icc.image _ (hcg₂ ω).continuousOn).union (ηg₂ ω 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
        (by show (ηg₂ ω 0).im ≤ 0; rw [h0g₂ ω]; simp) InteractingSLE.isPreconnected_lowerHalf
    have e : K₀ ω ∪ Restart.lowerHalf =
        (ηg₁ ω '' Icc 0 a ∪ Restart.lowerHalf) ∪ (ηg₂ ω '' Icc 0 c ∪ Restart.lowerHalf) := by
      rw [hK₀]; ext z; simp only [mem_union]; tauto
    rw [e]
    exact IsPreconnected.union (x₁ : ℂ) (Or.inr (show ((x₁ : ℂ)).im ≤ 0 by simp))
      (Or.inr (show ((x₁ : ℂ)).im ≤ 0 by simp)) h1 h2
  have hHull : ∀ ω, IsHPHull (fillH (K₀ ω)) := fun ω =>
    isHPHull_fillH_of_isPreconnected (hKc ω).isBounded (hKp ω)
  have hKdy : @Restart.IsDyadicHitMeasurable Ω (sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c) K₀ := by
    have h1 := @Restart.RetAux79.isDyadicHitMeasurable_prefix Ω (sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c) ηg₁ a hcg₁ hrec₁
    have h2 := @Restart.RetAux79.isDyadicHitMeasurable_prefix Ω (sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c) ηg₂ c hcg₂ hrec₂
    intro n k
    have e : {ω | (Restart.dyadicSquare n k ∩ K₀ ω).Nonempty} =
        {ω | (Restart.dyadicSquare n k ∩ ηg₁ ω '' Icc 0 a).Nonempty} ∪
          {ω | (Restart.dyadicSquare n k ∩ ηg₂ ω '' Icc 0 c).Nonempty} := by
      ext ω
      simp only [hK₀, mem_ofPred_eq, mem_union, inter_union_distrib_left, union_nonempty]
    rw [e]
    exact (h1 n k).union (h2 n k)
  have hchart : ∀ᵐ ω ∂P, IsChartSetting (H \ fillH (K₀ ω)) (H \ A₂ ω)
      (ConformalImage.mapOut (fillH (K₀ ω))) ∧ ∃ M : ℝ, ∀ z ∈ H \ fillH (K₀ ω),
        ‖ConformalImage.mapOut (fillH (K₀ ω)) z - z‖ ≤ M := by
    filter_upwards [hA₂ae] with ω hω
    have hO : H \ A₂ ω = H \ K₀ ω := by
      rw [← hω, cstUnion_eq]
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, not_and, hK₀]
      exact ⟨fun ⟨hz, hn⟩ => ⟨hz, fun hu => hn hu hz⟩, fun ⟨hz, hn⟩ => ⟨hz, fun hu _ => hn hu⟩⟩
    have hMO := ConformalImage.isMapOut_mapOut (hHull ω)
    rw [hO]
    exact ⟨{ isOpen_D := isOpen_H_diff_fillH (hKc ω).isBounded
             isOpen_O := QuantumZipper.isOpen_H.sdiff (hKc ω).isClosed
             subset_O := HalfPlaneSep.H_diff_fillH_subset_H_diff (hKc ω).isClosed
             O_subset := sdiff_subset
             comp := fun z hz => HalfPlaneSep.connectedComponentIn_subset_H_diff_fillH (hKc ω).isClosed hz
             conf := hMO.1 }, IsMapOut.exists_norm_sub_le (hHull ω) hMO⟩
  have key := ae_tendsto_zero_of_history
    (ℋ := sideMark ηg₁ ηg₂ ζl₁ ζl₂ a' c') (ℋ₁ := sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c)
    (D := fun ω => H \ fillH (K₀ ω)) (G := fun ω => ConformalImage.mapOut (fillH (K₀ ω)))
    hh0 hAm hA₂m hℋ hℋ₁ hlocA hlocA₂ hA₂ℋ hclosed hg₁ hg₀ hchart
    (fun q => @Restart.measurableSet_mem_H_diff_fillH Ω (sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c) _ hKdy hKc q)
    (fun q => @Restart.measurable_indicator_mapOut Ω (sideMark ηg₁ ηg₂ ζl₁ ζl₂ a c) _ hKdy hKc hKp q)
  filter_upwards [key, hagg₁, hagg₂, hAae] with ω ⟨v, hv, hvr, hdec⟩ hgω₁ hgω₂ hAω
  intro h₁ h₂
  have e₁ : ∀ t ≤ a', ηg₁ ω t = η₁ ω t := RetZone.eqOn_of_capped hgω₁ h₁ ham'
  have e₂ : ∀ t ≤ c', ηg₂ ω t = η₂ ω t := RetZone.eqOn_of_capped hgω₂ h₂ hcm'
  have hK₀ω : K₀ ω = prefixSet (η₁ ω) a (η₂ ω) c := by
    simp only [hK₀, prefixSet]
    rw [image_congr fun t ht => e₁ t (ht.2.trans haa), image_congr fun t ht => e₂ t (ht.2.trans hcc)]
  have hAω' : A ω = prefixSet (η₁ ω) a' (η₂ ω) c' ∩ H := by
    rw [← hAω, cstUnion_eq, prefixSet, image_congr fun t ht => e₁ t ht.2, image_congr fun t ht => e₂ t ht.2]
  refine ⟨v, hv, hvr, fun y ρ hρ hclr F hF hT => ?_⟩
  refine hdec y ρ hρ (fun z hzD hzb hzA => ?_) F (by rw [hK₀ω]; exact hF) (by rw [hK₀ω]; exact hT)
  rw [hK₀ω] at hzD hzb
  rw [hAω'] at hzA
  exact hclr z hzD hzb hzA.1

end OrdDet

end RLC

end InteractingSLE
