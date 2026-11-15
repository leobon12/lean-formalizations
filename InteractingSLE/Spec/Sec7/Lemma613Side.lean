/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeight
import InteractingSLE.Spec.Coupling.WholeField9Entr

/-!
# Lemma 6.13: retained histories and side heights of one flow line from its own determination map

Packet PROVE-LEMMA71J (specification §6.3, proof of Lemma 6.13, pp. 216–217, `source/spec/p193-240.md#lem-6.13-proof`:
"In the `ψᵢ` coordinate, the single-curve conditional field has height `λ − θᵢχ` along its negative real boundary";
the retained information "is the two labeled curves and their canonical revealed germs, as in the marked-union law").

Lemma 6.13 is used inside Lemma 7.1's chain (ruling R43), so the all-words Lemma 7.5 (`Theorem15.Lemma75Statement`)
may not be used there. The landed constructions `Restart.exists_capped_version`, `Sec7.exists_twoHist_versions` and
`SideHeight.singlePathSideHeightStatement_of_inputs` use Lemma 7.5 only to read **one** flow line off the field. This
file restates them with that reading as a hypothesis on the given flow line (a Borel map `Φ` of the field with
`Φ(h) = (ζ, η)` almost surely: for the flow lines of Figure 7.1 it is `Lemma75Bridge.exists_flowLineMap_of_admissible`
fed by the §4.2 reference), and with Aux. lemma 56 at first entrances discharged by the landed
`WholeField.retainedRangeEntranceStatement`:

* `exists_capped_version_of_map`: capped versions with Lemma 6.2's measurability and determination;
* `exists_twoHist_versions_of_maps`: the two retained histories of Lemma 6.2 for two flow lines;
* **`sideHeight_of_map`**: the single-path side heights (`Sec7.SinglePathSideHeightStatement`) for this flow line.

The proofs are those of the landed statements with the one substitution.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec7.Lemma613

open QuantumZipper (H fwdMap fwdHull)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6 Restart SideHeight

section Flow

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

omit [IsProbabilityMeasure P] in
/-- **A capped version of a flow line from a reading of the flow line off the field** (`Restart.exists_capped_version`
with Lemma 7.5 replaced by the map `Φ` of this flow line; same proof). -/
theorem exists_capped_version_of_map (hη : IsFlowLine κ b jumps x θ P h η ζ)
    (hΦ : ∃ Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (Φ (h ω)).2 t = η ω t)
    (u₀ : ℂ → ℝ) (m : ℝ≥0) :
    ∃ ηc : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (ηc ω)) ∧ (∀ t, Measurable fun ω => ηc ω t) ∧
      (∀ ω, ηc ω 0 = x) ∧ (∀ ω t, m ≤ t → ηc ω t = ηc ω m) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc ω t = η ω (capTime m (ζ ω) t)) ∧
      (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => ηc ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) := by
  classical
  obtain ⟨Φ, hΦm, hΦh⟩ := hΦ
  have hζm := measurable_lifetime_of_isFlowLine hη
  obtain ⟨η', hη'm, hη'⟩ := exists_measurable_version_of_isFlowLine hη
  obtain ⟨_, _, _, _, _, _, -, -, htr⟩ := hη
  -- the good event
  set good : Ω → Prop := fun ω => ContinuousOn (η ω) {s | (s : ℝ≥0∞) ≤ ζ ω} ∧ η ω 0 = x ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ ω → η' ω s = η ω s) ∧ (Φ (h ω)).1 = ζ ω ∧
    ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ ω → (Φ (h ω)).2 s = η ω s with hgooddef
  have hgood : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [htr, hη', hΦh] with ω h1 h2 h3
    refine ⟨?_, ?_, h2, h3.1, h3.2⟩
    · have hc := h1.2.1.add (continuousOn_const (c := (x : ℂ)))
      refine hc.congr fun s _ => ?_
      simp
    · have := h1.1
      simp only at this
      exact sub_eq_zero.1 this
  set G : Set Ω := (toMeasurable P {ω | ¬ good ω})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGg : ∀ ω ∈ G, good ω := fun ω hω => by
    by_contra hng
    exact hω (subset_toMeasurable _ _ hng)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have e : {ω | ¬ ω ∈ G} = toMeasurable P {ω | ¬ good ω} := by ext ω; simp [hGdef]
    rw [e, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hcont' : ∀ ω ∈ G, ContinuousOn (η' ω) {s | (s : ℝ≥0∞) ≤ ζ ω} := fun ω hω =>
    (hGg ω hω).1.congr fun s hs => (hGg ω hω).2.2.1 s hs
  have hcap : ∀ ω ∈ G, ∀ t, capPath m (ζ ω, η' ω) t = η ω (capTime m (ζ ω) t) := fun ω hω t => by
    rw [capPath_eq m (hcont' ω hω) t, (hGg ω hω).2.2.1 _ (capTime_le m (ζ ω) t)]
  refine ⟨fun ω t => if ω ∈ G then capPath m (ζ ω, η' ω) t else (x : ℂ), fun ω => ?_, fun t => ?_,
    fun ω => ?_, fun ω t ht => ?_, ?_, fun t => ?_⟩
  · by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte]
      have e : (fun t => capPath m (ζ ω, η' ω) t) = fun t => η' ω (capTime m (ζ ω) t) :=
        funext (capPath_eq m (hcont' ω hω))
      rw [e]
      exact continuous_capTime_comp m (hcont' ω hω)
    · simp only [hω, ↓reduceIte]
      exact continuous_const
  · exact Measurable.ite hGm ((measurable_capPath m t).comp (hζm.prodMk (measurable_pi_iff.2 hη'm)))
      measurable_const
  · by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte]
      rw [hcap ω hω, show capTime m (ζ ω) 0 = 0 from min_eq_left zero_le]
      exact (hGg ω hω).2.1
    · simp only [hω, ↓reduceIte]
  · by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte]
      rw [hcap ω hω, hcap ω hω]
      congr 1
      unfold capTime
      rw [min_eq_right ((ENNReal.coe_le_coe.1 ?_).trans ht), min_eq_right (ENNReal.coe_le_coe.1 ?_)]
      · rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
        exact min_le_right _ _
      · rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
        exact min_le_right _ _
    · simp only [hω, ↓reduceIte]
  · filter_upwards [hGae] with ω hω t
    simp only [hω, ↓reduceIte]
    exact hcap ω hω t
  · refine ⟨fun g => capPath m (Φ (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)) t,
      (measurable_capPath m t).comp (hΦm.comp (WholeField.measurable_add_dist _)), ?_⟩
    filter_upwards [hGae] with ω hω
    simp only [hω, ↓reduceIte, WholeField.centredField, sub_add_cancel]
    have hg := hGg ω hω
    rw [← Prod.mk.eta (p := Φ (h ω)), hg.2.2.2.1]
    exact capPath_congr m (fun s hs => (hg.2.2.1 s hs).trans (hg.2.2.2.2 s hs).symm) t

end Flow

section Two

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Two retained flow-line histories with Lemma 6.2's hypotheses, from the maps of the two flow lines**
(`Sec7.exists_twoHist_versions` with Lemma 7.5 replaced by the two maps and Aux. lemma 56 at first entrances
discharged by `WholeField.retainedRangeEntranceStatement`; same proof). -/
theorem exists_twoHist_versions_of_maps (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hΦ₁ : ∃ Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ₁ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₁ ω → (Φ (h ω)).2 t = η₁ ω t)
    (hΦ₂ : ∃ Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ₂ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → (Φ (h ω)).2 t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℝ≥0) :
    ∃ ηs : Fin 2 → Ω → ℝ≥0 → ℂ, (∀ i ω, Continuous (ηs i ω)) ∧
      (∀ i ω, ηs i ω 0 = (![(x₁ : ℂ), (x₂ : ℂ)] : Fin 2 → ℂ) i) ∧ (∀ i t, Measurable fun ω => ηs i ω t) ∧
      (∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => ηs i ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
      (∀ i, IsEntranceHistoryLocal (ηs i) (WholeField.centredField h u₀) P) ∧
      (∀ i ω t, m ≤ t → ηs i ω t = ηs i ω m) ∧ (∀ᵐ ω ∂P, ∀ i t, 0 ≤ (ηs i ω t).im) ∧
      (∀ᵐ ω ∂P, ∀ t, ηs 0 ω t = η₁ ω (capTime m (ζ₁ ω) t)) ∧
      (∀ᵐ ω ∂P, ∀ t, ηs 1 ω t = η₂ ω (capTime m (ζ₂ ω) t)) := by
  obtain ⟨ηs₁, hc₁, hm₁, h0₁, hfr₁, hs₁, hdet₁⟩ := exists_capped_version_of_map hη₁ hΦ₁ u₀ m
  obtain ⟨ηs₂, hc₂, hm₂, h0₂, hfr₂, hs₂, hdet₂⟩ := exists_capped_version_of_map hη₂ hΦ₂ u₀ m
  have hA56 := WholeField.retainedRangeEntranceStatement.{u}
  have hloc₁ := (hA56 κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ u₀ hu₀ m ηs₁ hc₁ hm₁ hs₁).isEntranceHistoryLocal
  have hloc₂ := (hA56 κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ u₀ hu₀ m ηs₂ hc₂ hm₂ hs₂).isEntranceHistoryLocal
  refine ⟨![ηs₁, ηs₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs₁, hs₂⟩
  · intro i; fin_cases i
    exacts [hc₁, hc₂]
  · intro i; fin_cases i
    exacts [h0₁, h0₂]
  · intro i; fin_cases i
    exacts [hm₁, hm₂]
  · intro i; fin_cases i
    exacts [hdet₁, hdet₂]
  · intro i; fin_cases i
    exacts [hloc₁, hloc₂]
  · intro i; fin_cases i
    exacts [hfr₁, hfr₂]
  · filter_upwards [hs₁, hs₂, ae_im_nonneg_of_isFlowLine' hη₁, ae_im_nonneg_of_isFlowLine' hη₂]
      with ω ha₁ ha₂ hi₁ hi₂ i t
    fin_cases i
    · show 0 ≤ (ηs₁ ω t).im
      rw [ha₁]
      exact hi₁ _ (capTime_le m (ζ₁ ω) t)
    · show 0 ≤ (ηs₂ ω t).im
      rw [ha₂]
      exact hi₂ _ (capTime_le m (ζ₂ ω) t)

end Two

section Side

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The single-path side heights of one flow line from its own determination map** (the conclusion of
`Sec7.SinglePathSideHeightStatement` for this flow line; proof of `SideHeight.singlePathSideHeightStatement_of_inputs`
with `exists_twoHist_versions_of_maps` in place of the Lemma 7.5 construction). -/
theorem sideHeight_of_map (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη : IsFlowLine κ b jumps x θ P h η ζ)
    (hΦ : ∃ Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (Φ (h ω)).2 t = η ω t)
    (W : ℝ≥0 → Ω → ℝ) (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m q : ℝ≥0) (hqm : q ≤ m)
    (ηc : Ω → ℝ≥0 → ℂ) (hηcc : ∀ ω, Continuous (ηc ω)) (hηcm : ∀ t, Measurable fun ω => ηc ω t)
    (hηce : ∀ᵐ ω ∂P, ∀ t, ηc ω t = η ω (Restart.capTime m (ζ ω) t)) (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean (fun ω => ηc ω '' {t | (t : ℝ≥0∞) ≤ q} ∩ H) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (ηc ω '' {t | (t : ℝ≥0∞) ≤ q} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηc ω '' {t | (t : ℝ≥0∞) ≤ q} ∩ H) →
        g ω φ = ∫ z, v z * φ z) →
      ∀ t₀ : ℝ≥0, t₀ < q → η ω t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
        F ≤ 𝓝[H \ fillH (η ω '' Icc 0 q)] (η ω t₀) → ∀ y : ℝ,
        Tendsto (fun z => QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) q (z - x)) F (𝓝 (y : ℂ)) →
          (0 < y → Tendsto (fun z => v z + u₀ z + QuantumZipper.chiC κ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im) F
            (𝓝 (sleLambda κ - θ * QuantumZipper.chiC κ))) ∧
          (y < 0 → Tendsto (fun z => v z + u₀ z + QuantumZipper.chiC κ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im) F
            (𝓝 (-sleLambda κ - θ * QuantumZipper.chiC κ))) := by
  classical
  obtain ⟨h', 𝓕, W', VL, VR, B, htrans, hC, htr'⟩ := id hη
  obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps x θ)
    (flowLineRhoR κ b jumps x θ) (flowLineXL b jumps x) (flowLineXR b jumps x)
  have hrel := Exist.eqOn_flowLine_harmonicExtension hκ hb x θ hu₀ hu₀'
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hX, -⟩ := hC.2.2.2
  -- good versions of the capped flow line (Lemma 6.2 inputs), from the pair construction with the line twice
  obtain ⟨ηs, hc, h0, hηm, hdet, hloc, hfr, -, hs₁, -⟩ :=
    exists_twoHist_versions_of_maps hκ hκ4 hb hh hη hη hΦ hΦ hu₀ m
  set s₂ : Fin 2 → ℝ≥0∞ := ![(q : ℝ≥0∞), 0] with hs₂
  have hA₁'loc := isLocalSet_explored_const hh0 hc h0 hηm hdet hloc hfr s₂
  have hA₁'det := comap_explored_const_le_aeSigma hc hdet s₂
  have hA₁'eq : ∀ ω, explored ηs (fun i _ => s₂ i) ω = ηs 0 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H := fun ω =>
    explored_pair_left ηs q (by rw [h0 1 ω]; simp)
  -- the range of the given version
  set A₁ : Ω → Set ℂ := fun ω => ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H with hA₁_def
  have hA₁A₁' : A₁ =ᵐ[P] explored ηs fun i _ => s₂ i := by
    filter_upwards [hηce, hs₁] with ω h1 h2
    rw [hA₁'eq]
    have : ηc ω = ηs 0 ω := funext fun t => (h1 t).trans (h2 t).symm
    show ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = _
    rw [this]
  have hA₁loc := Coupling.IsLocalSet.congr_set hA₁'loc hA₁A₁'
  have hA₁det := comap_le_aeSigma_of_ae_eq hA₁A₁' hA₁'det
  have hA₁m : Measurable[_, hittingSigma] A₁ := by
    have h1 := measurable_explored_const (η := fun _ : Fin 1 => ηc) (fun _ => hηcc) (fun _ => hηcm)
      (fun _ => (q : ℝ≥0∞))
    have e : (explored (fun _ : Fin 1 => ηc) fun _ _ => (q : ℝ≥0∞)) = A₁ := by
      funext ω
      simp only [explored, iUnion_const, hA₁_def]
    rwa [e] at h1
  have hA₁b : ∀ ω, Bornology.IsBounded (A₁ ω) := fun ω =>
    (((isCompact_Icc (a := (0 : ℝ≥0)) (b := q)).image (hηcc ω)).isBounded).subset (inter_subset_left.trans (by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨t, ⟨zero_le, show t ≤ q from by exact_mod_cast ht⟩, rfl⟩))
  -- the range is the stopped range of the flow line on `{q < ζ}`
  have hA₁q : ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → A₁ ω = η ω '' Icc 0 q ∩ H := by
    filter_upwards [hηce] with ω hce hq
    show ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = η ω '' Icc 0 q ∩ H
    congr 1
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      have htq : t ≤ q := by exact_mod_cast ht
      refine ⟨t, ⟨zero_le, htq⟩, ?_⟩
      rw [hce t, Restart.capTime_of_le m (ζ ω) (le_min (ht.trans hq.le) (ENNReal.coe_le_coe.2 (htq.trans hqm)))]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, by exact_mod_cast ht.2, ?_⟩
      rw [hce t, Restart.capTime_of_le m (ζ ω)
        (le_min ((ENNReal.coe_le_coe.2 ht.2).trans hq.le) (ENNReal.coe_le_coe.2 (ht.2.trans hqm)))]
  -- every earlier hull lies in the filling of the range
  have hA₁fill : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ q → (t : ℝ≥0∞) < ζ ω →
      (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t ⊆ fillH (A₁ ω) := by
    filter_upwards [htr', hηce] with ω htrω hce t htq htζ
    rw [fwdHull_eq_fillH_of_isGeneratingTrace htrω htζ, ← Restart.fillH_image_add_real,
      Restart.image_add_real_eq, hA₁_def, fillH_inter_H]
    refine fillH_mono ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s, show (s : ℝ≥0∞) ≤ q from ENNReal.coe_le_coe.2 (hs.2.trans htq), ?_⟩
    rw [hce s, Restart.capTime_of_le m (ζ ω)
      (le_min ((ENNReal.coe_le_coe.2 hs.2).trans htζ.le) (ENNReal.coe_le_coe.2 ((hs.2.trans htq).trans hqm)))]
  -- the force data at `q`
  choose u hu using fun ω => Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps x θ)
    (flowLineRhoR κ b jumps x θ) (fun i => VL i q ω - W' q ω) (fun i => VR i q ω - W' q ω)
  have hmain := ae_apply_eq_flowMean_of_range hC hκ htrans hh0 hu₀.1 hu₀' hrel hX htr' hA₁m
    (fun ω => inter_subset_right) hA₁b hA₁loc hA₁det hA₁q hA₁fill hg hu
  filter_upwards [hmain, htr, htr', hC.1.2.2.2.2, hA₁q, hA₁fill] with ω hmω htrω htr'ω hp h1 hfill hq v hv hrep
    t₀ ht₀ hη₀ F hFne hFle y hy
  have := hFne
  set χ := QuantumZipper.chiC κ with hχ
  -- the unbounded part and the identification of `v`
  set U := H \ fillH (A₁ ω) with hU
  have hUo : IsOpen U := isOpen_H_diff_fillH (hA₁b ω)
  have hUA : U ⊆ H \ A₁ ω := fun z hz => ⟨hz.1, fun h => hz.2 (subset_fillH inter_subset_right h)⟩
  set M : ℂ → ℝ := fun z => couplingMean κ (fun s : ℝ => W' s.toNNReal ω) q (u ω) (z - x) - θ * χ - u₀ z with hM
  have hKU : U ⊆ H \ (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) q := fun z hz =>
    ⟨hz.1, fun h => hz.2 (hfill q le_rfl hq h)⟩
  have hMh : InnerProductSpace.HarmonicOnNhd M U :=
    (harmonicOnNhd_flowMean hp.2.2.2.1 hq (hu ω).1 x (θ * χ) hu₀.1).mono hKU
  have hvM : EqOn v M U := eqOn_of_integral_mul_eq hUo (hUA.trans sdiff_subset) (hv.mono hUA) hMh
    fun φ hφ => by rw [← hrep φ (hφ.trans hUA), hmω hq φ hφ]
  have hfillη : fillH (η ω '' Icc 0 q) = fillH (A₁ ω) := by rw [h1 hq, fillH_inter_H]
  have hev : ∀ᶠ z in F, z ∈ U := by
    have := hFle self_mem_nhdsWithin
    rwa [hfillη] at this
  -- the coupling's driver generates the same trace
  have hf := fwdMap_eq_of_isGeneratingTrace htrω htr'ω hq
  have hL := logDerivFwd_eq_of_isGeneratingTrace htrω htr'ω hq
  -- the approach in the centred chart
  set F' : Filter ℂ := Filter.map (fun z => z - x) F with hF'
  have hp0 : η ω t₀ - x ∈ H := show 0 < (η ω t₀ - x).im by simpa using (show 0 < (η ω t₀).im from hη₀)
  have hF'le : F' ≤ 𝓝[H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) q] (η ω t₀ - x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((continuous_sub_right (x : ℂ)).tendsto _).comp
      (hFle.trans nhdsWithin_le_nhds), hev.mono fun z hz => ?_⟩
    have hz' := hKU hz
    refine ⟨show 0 < (z - x).im by simpa using (show 0 < z.im from hz'.1), fun hK => hz'.2 ⟨z - x, hK, by ring⟩⟩
  have hy' : Tendsto (fwdMap (fun s : ℝ => W' s.toNNReal ω) q) F' (𝓝 (y : ℂ)) := by
    rw [← hf]
    exact tendsto_map'_iff.2 hy
  -- the function along `F`
  have hcongr : (fun z => v z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im)
      =ᶠ[F] fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x)) - θ * χ := by
    filter_upwards [hev] with z hz
    rw [hvM hz, hM, hL]
    simp only [couplingMean]
    ring
  refine ⟨fun hy0 => ?_, fun hy0 => ?_⟩
  · have hlim := tendsto_comp_fwdMap_of_pos hp htr'ω hq (hu ω) hp0 hF'le hy' hy0
    have hlim' : Tendsto (fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x))) F (𝓝 (sleLambda κ)) :=
      tendsto_map'_iff.1 hlim
    exact (hlim'.sub_const (θ * χ)).congr' hcongr.symm
  · have hlim := tendsto_comp_fwdMap_of_neg hp htr'ω hq (hu ω) hp0 hF'le hy' hy0
    have hlim' : Tendsto (fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x))) F
        (𝓝 (-sleLambda κ)) :=
      tendsto_map'_iff.1 hlim
    exact (hlim'.sub_const (θ * χ)).congr' hcongr.symm

end Side

end InteractingSLE.Sec7.Lemma613
