/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1Flow

/-!
# Aux. lemma 77 (RU1) at the later first-contact lines: marked locality of `η₁[0, σ₁ + t₁] ∪ η₂[0, σ₂ + t₂]`

Packet PROVE-DOMAINMARKOV8 (specification Aux. lemma 77, pp. 287–289, and its use for the first-contact restart,
p. 295: "Aux. lemma 77 supplies the nested marked Gaussian kernels at every continuation stopping time; its identity
(RU2) includes clipping at the original terminal time"). PROVE-RESTART-CPL6 proved Lemma 7.7's marked locality at the
first-contact stopping line `(σ₁, σ₂)` (`R1StopLineLocal.lean`, `R1Flow.lean`). The first-contact continuation of
`η₁` is read on the **later lines** `(σ₁ + t, σ₂)` (and that of `η₂` on `(σ₁, σ₂ + t)`), at deterministic physical
times `t` after the contact; these are the lines on which `Aux79.hasSafeLaw_of_lineKernel` and
`Aux79.hasSafeMembers_of_lineLocal` need the kernels and the locality. Here the line is shifted by deterministic
`(t₁, t₂)`:

* `shLine`, `shUnion = η₁([0, σ₁ + t₁]) ∪ η₂([0, σ₂ + t₂])` (its `ℍ`-part), `shHist` (the two killed histories);
* **`le_aeSigma_shUnion`**: the avoidance event of the shifted union and the retained histories on it are almost
  surely determined by `h_{U^c}`. The proof is CPL6's (with (GR1)): the shifted union avoids `U` iff
  `σᵢ + tᵢ ≤ Tᵢ` (first entrance times); then `σᵢ ≤ Tᵢ`, so the histories through `T` recover `σ` (`rec_eq`), and
  conversely the recovered values decide it (`rec_le_iff`). Only this step changes;
* `isLocalSet_shUnion`, `isHistoryAvoidanceLocal_shUnion`, **`ae_condExp_exp_eq_shUnion`**: locality, history
  marking and the marked Gaussian kernel on every complementary component;
* **`exists_shUnion_marked_of_isFlowLine`**: the kernel for two capped flow lines (CPL6's
  `exists_fcUnion_marked_of_isFlowLine` with the shifted line).

The proofs are copies of CPL6's with these changes (provenance: `R1StopLineLocal.lean`, `R1Flow.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open LocalSets Sec6

/-! ### The shifted first-contact line -/

section Defs

variable {Ω : Type*}

/-- **The first-contact stopping line shifted by `(t₁, t₂)`**: `(σ₁ + t₁, σ₂ + t₂)` with `(σ₁, σ₂)` the first-contact
line `fcLine` (`⊤` if the paths never meet). -/
def shLine (η₁ η₂ : Ω → ℝ≥0 → ℂ) (t₁ t₂ : ℝ≥0) : Fin 2 → Ω → ℝ≥0∞ :=
  ![fun ω => recFst (fullHist η₁ η₂ ω) + t₁, fun ω => recSnd (fullHist η₁ η₂ ω) + t₂]

/-- **The shifted first-contact union** `η₁([0, σ₁ + t₁]) ∪ η₂([0, σ₂ + t₂])` (its `ℍ`-part). -/
def shUnion (η₁ η₂ : Ω → ℝ≥0 → ℂ) (t₁ t₂ : ℝ≥0) : Ω → Set ℂ := explored (pairPath η₁ η₂) (shLine η₁ η₂ t₁ t₂)

/-- **The retained histories at the shifted line**: the two killed stopped histories. -/
def shHist (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (t₁ t₂ : ℝ≥0) (ω : Ω) : KHist × KHist :=
  (khistOf (pathCoord (η₁ ω)) (ζ₁ ω) (recFst (fullHist η₁ η₂ ω) + t₁),
    khistOf (pathCoord (η₂ ω)) (ζ₂ ω) (recSnd (fullHist η₁ η₂ ω) + t₂))

theorem shUnion_eq (η₁ η₂ : Ω → ℝ≥0 → ℂ) (t₁ t₂ : ℝ≥0) (ω : Ω) :
    shUnion η₁ η₂ t₁ t₂ ω = (η₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recFst (fullHist η₁ η₂ ω) + t₁} ∪
      η₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recSnd (fullHist η₁ η₂ ω) + t₂}) ∩ H := by
  ext z
  simp only [shUnion, explored, pairPath, shLine, mem_inter_iff, mem_iUnion, Fin.exists_fin_two, mem_union,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The unshifted line is the first-contact line. -/
theorem shUnion_zero (η₁ η₂ : Ω → ℝ≥0 → ℂ) : shUnion η₁ η₂ 0 0 = fcUnion η₁ η₂ := by
  funext ω
  rw [shUnion_eq, fcUnion_eq]
  simp only [ENNReal.coe_zero, add_zero]

variable [MeasurableSpace Ω]

theorem measurable_shLine {η₁ η₂ : Ω → ℝ≥0 → ℂ} (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t)
    (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t) (t₁ t₂ : ℝ≥0) (i : Fin 2) : Measurable (shLine η₁ η₂ t₁ t₂ i) := by
  fin_cases i
  · exact (measurable_recFst.comp (measurable_fullHist hηm₁ hηm₂)).add measurable_const
  · exact (measurable_recSnd.comp (measurable_fullHist hηm₁ hηm₂)).add measurable_const

theorem measurable_shHist {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t)
    (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t) (hζm₁ : Measurable ζ₁) (hζm₂ : Measurable ζ₂) (t₁ t₂ : ℝ≥0) :
    Measurable (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂) := by
  have h₁ : Measurable fun ω => pathCoord (η₁ ω) := Measurable.of_eval fun q => hηm₁ q
  have h₂ : Measurable fun ω => pathCoord (η₂ ω) := Measurable.of_eval fun q => hηm₂ q
  have hF := measurable_fullHist hηm₁ hηm₂
  have hk : Measurable fun p : (ℚ≥0 → ℂ) × ℝ≥0∞ × ℝ≥0∞ => khistOf p.1 p.2.1 p.2.2 :=
    (measurable_histOf.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).prodMk
      (measurable_lifeRec.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
  have e₁ := hk.comp (h₁.prodMk (hζm₁.prodMk ((measurable_recFst.comp hF).add (measurable_const (a := (t₁ : ℝ≥0∞))))))
  have e₂ := hk.comp (h₂.prodMk (hζm₂.prodMk ((measurable_recSnd.comp hF).add (measurable_const (a := (t₂ : ℝ≥0∞))))))
  dsimp only [Function.comp_def] at e₁ e₂
  exact e₁.prodMk e₂

theorem measurable_shUnion {η₁ η₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (η₁ ω))
    (hc₂ : ∀ ω, Continuous (η₂ ω)) (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t)
    (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t) (t₁ t₂ : ℝ≥0) :
    Measurable[_, hittingSigma] (shUnion η₁ η₂ t₁ t₂) := by
  refine measurable_explored (fun i ω => ?_) (fun i t => ?_) (measurable_shLine hηm₁ hηm₂ t₁ t₂)
  · fin_cases i
    · exact hc₁ ω
    · exact hc₂ ω
  · fin_cases i
    · exact hηm₁ t
    · exact hηm₂ t

end Defs

section Avoid

variable {Ω : Type*} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {t₁ t₂ : ℝ≥0}

/-- **The union avoids `U` iff both stopped paths do.** -/
theorem disjoint_shUnion_iff {U : Set ℂ} (hUH : U ⊆ H) (ω : Ω) :
    Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U ↔ AvoidsUpTo (η₁ ω) (recFst (fullHist η₁ η₂ ω) + t₁) U ∧
      AvoidsUpTo (η₂ ω) (recSnd (fullHist η₁ η₂ ω) + t₂) U := by
  rw [shUnion, disjoint_explored_iff hUH ω, Fin.forall_fin_two]
  simp only [pairPath, shLine, Matrix.cons_val_zero, Matrix.cons_val_one]

variable {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The recorded union is read from the retained histories**: the σ-algebra of Lemma 3.6 (ii) of the union (the
avoidance event and the union recorded on it) is contained in the σ-algebra of the avoidance event and the retained
histories recorded on it. -/
theorem markedSigma_shUnion_le (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω)) (U : Set ℂ) :
    markedSigma (shUnion η₁ η₂ t₁ t₂) U ≤
      markedHistSigma {ω | Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U} (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂) := by
  refine sup_le ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ rfl
    exact MeasurableSpace.measurableSet_generateFrom ⟨univ, MeasurableSet.univ, by rw [preimage_univ, inter_univ]⟩
  · unfold hittingSigma
    rw [MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨_, ⟨V, hVo, hVH, rfl⟩, rfl⟩
    set Ψ : Set (KHist × KHist) :=
      {y | ∃ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞)) ≤ y.1.1.1 ∧ y.1.1.2 q ∈ V} ∪
        {y | ∃ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞)) ≤ y.2.1.1 ∧ y.2.1.2 q ∈ V} with hΨdef
    have hΨ : MeasurableSet Ψ := by
      refine MeasurableSet.union ?_ ?_
      · simp only [ofPred_exists, ofPred_and]
        exact MeasurableSet.iUnion fun q => (measurableSet_le measurable_const
          (measurable_fst.comp (measurable_fst.comp measurable_fst))).inter
          (((measurable_pi_apply q).comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))
            hVo.measurableSet)
      · simp only [ofPred_exists, ofPred_and]
        exact MeasurableSet.iUnion fun q => (measurableSet_le measurable_const
          (measurable_fst.comp (measurable_fst.comp measurable_snd))).inter
          (((measurable_pi_apply q).comp (measurable_snd.comp (measurable_fst.comp measurable_snd)))
            hVo.measurableSet)
    have e : (fun ω => markedSet U (shUnion η₁ η₂ t₁ t₂ ω)) ⁻¹' {A | (A ∩ V).Nonempty} =
        {ω | Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U} ∩ shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂ ⁻¹' Ψ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, markedSet_inter_nonempty_iff, mem_inter_iff]
      refine and_congr_right fun _ => ?_
      rw [shUnion, explored_inter_nonempty_iff (continuous_pairPath hc₁ hc₂) hVo hVH ω, Fin.exists_fin_two]
      simp only [pairPath, shLine, Matrix.cons_val_zero, Matrix.cons_val_one, hΨdef, mem_union, mem_ofPred_eq,
        shHist, khistOf, histOf]
      refine or_congr (exists_congr fun q => and_congr_right fun hq => ?_)
        (exists_congr fun q => and_congr_right fun hq => ?_)
      · rw [stopCoord_of_le hq]; rfl
      · rw [stopCoord_of_le hq]; rfl
    rw [e]
    exact MeasurableSpace.measurableSet_generateFrom ⟨Ψ, hΨ, rfl⟩

end Avoid

/-! ### Lemma 7.7's marked locality -/

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℂ} {t₁ t₂ : ℝ≥0}

/-- **The core of Lemma 7.7's marked locality**: for every open `U ⊆ ℍ` and Borel version `G` of the projection onto
`H(U)`, the avoidance event of the first-contact union and, on it, the two retained killed histories are almost
surely determined by `h_{U^c}`. -/
theorem le_aeSigma_shUnion (hhm : Measurable h) (hc₁ : ∀ ω, Continuous (η₁ ω))
    (hc₂ : ∀ ω, Continuous (η₂ ω)) (h0₁ : ∀ ω, η₁ ω 0 = x₁) (h0₂ : ∀ ω, η₂ ω 0 = x₂)
    (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t) (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t)
    (hζm₁ : Measurable ζ₁) (hζm₂ : Measurable ζ₂)
    (hdet₁ : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η₁ ω t) =ᵐ[P] fun ω => f (h ω))
    (hdet₂ : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η₂ ω t) =ᵐ[P] fun ω => f (h ω))
    (hdetζ₁ : ∃ f : DistOn upperHalfPlaneOpens → ℝ≥0∞, Measurable f ∧ ζ₁ =ᵐ[P] fun ω => f (h ω))
    (hdetζ₂ : ∃ f : DistOn upperHalfPlaneOpens → ℝ≥0∞, Measurable f ∧ ζ₂ =ᵐ[P] fun ω => f (h ω))
    (hloc₁ : IsEntranceKilledHistoryLocal η₁ ζ₁ h P) (hloc₂ : IsEntranceKilledHistoryLocal η₂ ζ₂ h P)
    (hfc : ∀ᵐ ω ∂P, (∃ s t : ℝ≥0, η₁ ω s = η₂ ω t) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) ⊤ (η₂ ω) ⊤ s₀ t₀)
    (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) :
    markedHistSigma {ω | Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U} (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂) ≤
      aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P := by
  classical
  set N := aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P with hNdef
  let _ : MeasurableSpace Ω := mΩ
  by_cases hx : x₁ ∈ (U : Set ℂ) ∨ x₂ ∈ (U : Set ℂ)
  · -- a starting point lies in `U`: the union always meets `U`
    have hE : {ω | Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U} = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
      have hω' : Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U := hω
      rw [disjoint_shUnion_iff hUH ω] at hω'
      rcases hx with hx | hx
      · exact hω'.1 0 (by simp) (by rw [h0₁]; exact hx)
      · exact hω'.2 0 (by simp) (by rw [h0₂]; exact hx)
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨B, -, rfl⟩
    rw [hE, empty_inter]
    exact @MeasurableSet.empty _ N
  push Not at hx
  have h0₁' : ∀ ω, η₁ ω 0 ∉ (U : Set ℂ) := fun ω => by rw [h0₁]; exact hx.1
  have h0₂' : ∀ ω, η₂ ω 0 ∉ (U : Set ℂ) := fun ω => by rw [h0₂]; exact hx.2
  -- the killed histories through the first entrance times are determined by `h_{U^c}`
  have hHtm := (measurable_entranceKHist hhm hc₁ hηm₁ hζm₁ hdet₁ hdetζ₁ hloc₁ U G hUH hG hd h0₁').prodMk
    (measurable_entranceKHist hhm hc₂ hηm₂ hζm₂ hdet₂ hdetζ₂ hloc₂ U G hUH hG hd h0₂')
  -- the reconstruction
  have hpr : Measurable fun y : KHist × KHist => (y.1.1, y.2.1) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  set ΨE : Set (KHist × KHist) :=
    {y | recFst (y.1.1, y.2.1) + t₁ ≤ y.1.1.1 ∧ recSnd (y.1.1, y.2.1) + t₂ ≤ y.2.1.1} with hΨEdef
  have hr₁ : Measurable fun y : KHist × KHist => recFst (y.1.1, y.2.1) + (t₁ : ℝ≥0∞) :=
    (measurable_recFst.comp hpr).add measurable_const
  have hr₂ : Measurable fun y : KHist × KHist => recSnd (y.1.1, y.2.1) + (t₂ : ℝ≥0∞) :=
    (measurable_recSnd.comp hpr).add measurable_const
  have hΨE : MeasurableSet ΨE :=
    (measurableSet_le hr₁ (measurable_fst.comp (measurable_fst.comp measurable_fst))).inter
      (measurableSet_le hr₂ (measurable_fst.comp (measurable_fst.comp measurable_snd)))
  have hΦm := (measurable_khistRestrict.comp (measurable_fst.prodMk hr₁)).prodMk
    (measurable_khistRestrict.comp (measurable_snd.prodMk hr₂))
  dsimp only [Function.comp_def] at hΦm
  -- pointwise identification on the event of Lemma 7.7
  have hgood : ∀ᵐ ω ∂P, ∃ σ₁ σ₂ : ℝ≥0∞, IsFCPair (η₁ ω) (η₂ ω) σ₁ σ₂ := by
    filter_upwards [hfc] with ω hω using exists_isFCPair hω
  have hpt : ∀ ω, (∃ σ₁ σ₂ : ℝ≥0∞, IsFCPair (η₁ ω) (η₂ ω) σ₁ σ₂) →
      (Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U ↔
        (khistOf (pathCoord (η₁ ω)) (ζ₁ ω) (firstEntrance U (pathCoord (η₁ ω))),
          khistOf (pathCoord (η₂ ω)) (ζ₂ ω) (firstEntrance U (pathCoord (η₂ ω)))) ∈ ΨE) ∧
      (Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U →
        (khistRestrict (khistOf (pathCoord (η₁ ω)) (ζ₁ ω) (firstEntrance U (pathCoord (η₁ ω))))
            (recFst (histOf (pathCoord (η₁ ω)) (firstEntrance U (pathCoord (η₁ ω))),
              histOf (pathCoord (η₂ ω)) (firstEntrance U (pathCoord (η₂ ω)))) + t₁),
          khistRestrict (khistOf (pathCoord (η₂ ω)) (ζ₂ ω) (firstEntrance U (pathCoord (η₂ ω))))
            (recSnd (histOf (pathCoord (η₁ ω)) (firstEntrance U (pathCoord (η₁ ω))),
              histOf (pathCoord (η₂ ω)) (firstEntrance U (pathCoord (η₂ ω)))) + t₂)) =
          shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂ ω) := by
    rintro ω ⟨σ₁, σ₂, hσ⟩
    obtain ⟨e₁, e₂⟩ := fcLine_eq (hc₁ ω) (hc₂ ω) hσ
    have hav : Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U ↔
        σ₁ + t₁ ≤ firstEntrance U (pathCoord (η₁ ω)) ∧ σ₂ + t₂ ≤ firstEntrance U (pathCoord (η₂ ω)) := by
      rw [disjoint_shUnion_iff hUH ω, e₁, e₂]
      exact and_congr (disjoint_range_iff_le_firstEntrance U.isOpen (hc₁ ω) (h0₁' ω) _)
        (disjoint_range_iff_le_firstEntrance U.isOpen (hc₂ ω) (h0₂' ω) _)
    have hrec : (σ₁ + t₁ ≤ firstEntrance U (pathCoord (η₁ ω)) ∧ σ₂ + t₂ ≤ firstEntrance U (pathCoord (η₂ ω))) ↔
        (recFst (histOf (pathCoord (η₁ ω)) (firstEntrance U (pathCoord (η₁ ω))),
            histOf (pathCoord (η₂ ω)) (firstEntrance U (pathCoord (η₂ ω)))) + t₁ ≤
            firstEntrance U (pathCoord (η₁ ω)) ∧
          recSnd (histOf (pathCoord (η₁ ω)) (firstEntrance U (pathCoord (η₁ ω))),
            histOf (pathCoord (η₂ ω)) (firstEntrance U (pathCoord (η₂ ω)))) + t₂ ≤
            firstEntrance U (pathCoord (η₂ ω))) := by
      constructor
      · rintro ⟨a₁, a₂⟩
        obtain ⟨r₁, r₂⟩ := rec_eq (hc₁ ω) (hc₂ ω) hσ (le_self_add.trans a₁) (le_self_add.trans a₂)
        rw [r₁, r₂]
        exact ⟨a₁, a₂⟩
      · rintro ⟨a₁, a₂⟩
        obtain ⟨b₁, b₂⟩ := (rec_le_iff (hc₁ ω) (hc₂ ω) hσ).2 ⟨le_self_add.trans a₁, le_self_add.trans a₂⟩
        obtain ⟨r₁, r₂⟩ := rec_eq (hc₁ ω) (hc₂ ω) hσ b₁ b₂
        rw [r₁] at a₁
        rw [r₂] at a₂
        exact ⟨a₁, a₂⟩
    refine ⟨hav.trans hrec, fun hω => ?_⟩
    obtain ⟨h₁, h₂⟩ := hav.1 hω
    obtain ⟨r₁, r₂⟩ := rec_eq (hc₁ ω) (hc₂ ω) hσ (le_self_add.trans h₁) (le_self_add.trans h₂)
    rw [r₁, r₂, khistRestrict_khistOf h₁, khistRestrict_khistOf h₂, shHist, e₁, e₂]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨B, hB, rfl⟩
  refine measurableSet_aeSigma_of_ae_eq ?_ (hHtm (hΨE.inter (hΦm hB)))
  filter_upwards [hgood] with ω hω
  have hp := hpt ω hω
  refine propext ⟨fun hωEB => ⟨hp.1.1 hωEB.1, ?_⟩, fun hωΨB => ⟨hp.1.2 hωΨB.1, ?_⟩⟩
  · have key : shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂ ω ∈ B := hωEB.2
    rw [← hp.2 hωEB.1] at key
    exact key
  · show shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂ ω ∈ B
    rw [← hp.2 (hp.1.2 hωΨB.1)]
    exact hωΨB.2

end Main

/-! ### Consequences: locality, history marking, the conditional law off the union -/

section Consequences

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℂ} {t₁ t₂ : ℝ≥0}
  (hhm : Measurable h) (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω))
  (h0₁ : ∀ ω, η₁ ω 0 = x₁) (h0₂ : ∀ ω, η₂ ω 0 = x₂)
  (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t) (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t)
  (hζm₁ : Measurable ζ₁) (hζm₂ : Measurable ζ₂)
  (hdet₁ : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
    (fun ω => η₁ ω t) =ᵐ[P] fun ω => f (h ω))
  (hdet₂ : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
    (fun ω => η₂ ω t) =ᵐ[P] fun ω => f (h ω))
  (hdetζ₁ : ∃ f : DistOn upperHalfPlaneOpens → ℝ≥0∞, Measurable f ∧ ζ₁ =ᵐ[P] fun ω => f (h ω))
  (hdetζ₂ : ∃ f : DistOn upperHalfPlaneOpens → ℝ≥0∞, Measurable f ∧ ζ₂ =ᵐ[P] fun ω => f (h ω))
  (hloc₁ : IsEntranceKilledHistoryLocal η₁ ζ₁ h P) (hloc₂ : IsEntranceKilledHistoryLocal η₂ ζ₂ h P)
  (hfc : ∀ᵐ ω ∂P, (∃ s t : ℝ≥0, η₁ ω s = η₂ ω t) →
    ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) ⊤ (η₂ ω) ⊤ s₀ t₀)
include hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂ hfc

/-- **Lemma 7.7, marked locality (history-sensitive form)**: for every open `U ⊆ ℍ`, given `h_{U^c}`, the pair
consisting of the avoidance event of the first-contact union and the two retained killed histories on it is
conditionally independent of `h_U`. -/
theorem condIndepEv_shHist (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) :
    CondIndepEv (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance)
      (markedHistSigma {ω | Disjoint (shUnion η₁ η₂ t₁ t₂ ω) U} (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂))
      (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance) P :=
  condIndepEv_of_le_aeSigma ((measurable_markovCompl hG).comp hhm).comap_le (hG.comp hhm).comap_le
    (le_aeSigma_shUnion (t₁ := t₁) (t₂ := t₂) hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁
        hdetζ₂ hloc₁ hloc₂ hfc
      U G hUH hG hd)

/-- **The first-contact union satisfies Lemma 3.6 (ii).** -/
theorem isMarkedAvoidanceLocal_shUnion : IsMarkedAvoidanceLocal (shUnion η₁ η₂ t₁ t₂) h P := fun U G hUH hG hd =>
  condIndepEv_of_le_aeSigma ((measurable_markovCompl hG).comp hhm).comap_le (hG.comp hhm).comap_le
    ((markedSigma_shUnion_le (ζ₁ := ζ₁) (ζ₂ := ζ₂) hc₁ hc₂ U).trans
      (le_aeSigma_shUnion (t₁ := t₁) (t₂ := t₂) hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁
        hdetζ₂ hloc₁ hloc₂ hfc
        U G hUH hG hd))

/-- **Lemma 7.7, locality**: for a zero-boundary GFF, if the first-contact union is almost surely relatively closed
in `ℍ`, it is a local set (Lemma 3.6, (ii) ⇒ (iv)). -/
theorem isLocalSet_shUnion (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hcl : ∀ᵐ ω ∂P, IsOpen (H \ shUnion η₁ η₂ t₁ t₂ ω)) : IsLocalSet (shUnion η₁ η₂ t₁ t₂) h P := by
  have hA := measurable_shUnion hc₁ hc₂ hηm₁ hηm₂ t₁ t₂
  have hAc : ∀ᵐ ω ∂P, shUnion η₁ η₂ t₁ t₂ ω ⊆ H ∧ IsOpen (H \ shUnion η₁ η₂ t₁ t₂ ω) := by
    filter_upwards [hcl] with ω hω using ⟨inter_subset_right, hω⟩
  exact ((isLocalSet_tfae hh hA hAc).out 2 4).1
    (isMarkedAvoidanceLocal_shUnion hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁
      hloc₂ hfc)

/-- **Lemma 7.7, history marking** (Aux. lemma 18's criterion for the union with the retained histories as marks):
for every open `U ⊆ ℍ`, every Borel version `G` of the projection onto `H(U)` and every event `F` of the retained
histories, `P[{fcUnion ∩ U = ∅} ∩ F | h]` is a measurable function of `h − G h`. -/
theorem isHistoryAvoidanceLocal_shUnion :
    WholeField.IsHistoryAvoidanceLocal (MeasurableSpace.comap (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂) inferInstance)
      (shUnion η₁ η₂ t₁ t₂) h P := by
  intro U G hUH hG hd F hF
  obtain ⟨B, hB, rfl⟩ := hF
  have hmem := le_aeSigma_shUnion (t₁ := t₁) (t₂ := t₂) hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂
    hdetζ₁ hdetζ₂ hloc₁ hloc₂
    hfc U G hUH hG hd _ (MeasurableSpace.measurableSet_generateFrom ⟨B, hB, rfl⟩)
  obtain ⟨G', hG', he⟩ := hmem
  obtain ⟨B', hB', rfl⟩ := hG'
  refine ⟨B'.indicator fun _ => (1 : ℝ), measurable_const.indicator hB', ?_⟩
  have hsub : MeasurableSet[MeasurableSpace.comap h inferInstance]
      ((fun ω => markovCompl G (h ω)) ⁻¹' B') :=
    ⟨(markovCompl G) ⁻¹' B', measurable_markovCompl hG hB', rfl⟩
  have hle : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set he)).trans ?_
  rw [condExp_of_stronglyMeasurable hle (stronglyMeasurable_const.indicator hsub)
    ((integrable_const (1 : ℝ)).indicator (hle _ hsub))]
  refine Eventually.of_forall fun ω => ?_
  rfl

/-- **Marked locality off the first-contact union** (Lemma 7.7, with Aux. lemma 18 and Lemma 3.6; the input
"(b)" of (R1)). For a zero-boundary GFF `h` and the first-contact union `A` (almost surely relatively closed), there
is a version `g` of the local-set mean of `A`, and given the germs of `A` together with the two retained killed
histories, the field paired with a test function supported in a complementary component `C` of `A` (e.g. the
unbounded one) is Gaussian with mean `g(φ)` and the zero-boundary variance of `C`. -/
theorem ae_condExp_exp_eq_shUnion (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hcl : ∀ᵐ ω ∂P, IsOpen (H \ shUnion η₁ η₂ t₁ t₂ ω)) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (shUnion η₁ η₂ t₁ t₂) h P g ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ shUnion η₁ η₂ t₁ t₂ ω,
        tsupport φ ⊆ connectedComponentIn (H \ shUnion η₁ η₂ t₁ t₂ ω) z₀ →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
            germSigma (shUnion η₁ η₂ t₁ t₂) h ⊔ MeasurableSpace.comap (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂) inferInstance] ω =
          Complex.exp (Complex.I * (g ω φ : ℂ)) *
            ((Real.exp (-(1 / 2) *
              QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ shUnion η₁ η₂ t₁ t₂ ω) z₀) φ φ) : ℝ) : ℂ) := by
  have hA := measurable_shUnion hc₁ hc₂ hηm₁ hηm₂ t₁ t₂
  have hloc := isLocalSet_shUnion hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂
    hfc hh hcl
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh hA hloc
  refine ⟨g, hg, fun φ => ?_⟩
  exact ae_condExp_exp_eq_of_component_marked hh hA hloc
    (measurable_shHist hηm₁ hηm₂ hζm₁ hζm₂ t₁ t₂).comap_le
    (isHistoryAvoidanceLocal_shUnion hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁
      hloc₂ hfc) hg φ

end Consequences

theorem exists_shUnion_marked_of_isFlowLine (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m t₁ t₂ : ℝ≥0) :
    ∃ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (ηc₁ ω)) ∧ (∀ ω, Continuous (ηc₂ ω)) ∧
      (∀ t, Measurable fun ω => ηc₁ ω t) ∧ (∀ t, Measurable fun ω => ηc₂ ω t) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t)) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) ∧
      ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (shUnion ηc₁ ηc₂ t₁ t₂) (WholeField.centredField h u₀) P g ∧
        ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ shUnion ηc₁ ηc₂ t₁ t₂ ω,
          tsupport φ ⊆ connectedComponentIn (H \ shUnion ηc₁ ηc₂ t₁ t₂ ω) z₀ →
          P[fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) |
              germSigma (shUnion ηc₁ ηc₂ t₁ t₂) (WholeField.centredField h u₀) ⊔
                MeasurableSpace.comap
                  (shHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) m) (fun ω => cutLife (ζ₂ ω) m) t₁ t₂) inferInstance] ω =
            Complex.exp (Complex.I * (g ω φ : ℂ)) *
              ((Real.exp (-(1 / 2) *
                QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ shUnion ηc₁ ηc₂ t₁ t₂ ω) z₀) φ φ) :
                  ℝ) : ℂ) := by
  obtain ⟨ηc₁, hc₁, hm₁, h0₁, hfr₁, hag₁, hdet₁, hdetζ₁⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨ηc₂, hc₂, hm₂, h0₂, hfr₂, hag₂, hdet₂, hdetζ₂⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hloc₁ := hA56 κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ u₀ hu₀ m ηc₁ hc₁ hm₁ hag₁
  have hloc₂ := hA56 κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ u₀ hu₀ m ηc₂ hc₂ hm₂ hag₂
  have hζm₁ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₁)
  have hζm₂ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₂)
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- Lemma 7.7's common first point for the capped paths
  have hfc : ∀ᵐ ω ∂P, (∃ s t : ℝ≥0, ηc₁ ω s = ηc₂ ω t) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (ηc₁ ω) ⊤ (ηc₂ ω) ⊤ s₀ t₀ := by
    filter_upwards [hL77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂, hag₁, hag₂]
      with ω h77 ha₁ ha₂
    rintro ⟨s, t, hst⟩
    rw [ha₁, ha₂] at hst
    obtain ⟨s₀, t₀, hfc, -, -⟩ := h77 ⟨_, _, capTime_le m (ζ₁ ω) s, capTime_le m (ζ₂ ω) t, hst⟩
    obtain ⟨hs₀, ht₀⟩ := hfc.2.2.2 _ _ (capTime_le m (ζ₁ ω) s) (capTime_le m (ζ₂ ω) t) hst
    have hcs₀ : capTime m (ζ₁ ω) s₀ = s₀ := capTime_of_le m (ζ₁ ω)
      (le_min hfc.1 (ENNReal.coe_le_coe.2 (hs₀.trans (capTime_le_cap m (ζ₁ ω) s))))
    have hct₀ : capTime m (ζ₂ ω) t₀ = t₀ := capTime_of_le m (ζ₂ ω)
      (le_min hfc.2.1 (ENNReal.coe_le_coe.2 (ht₀.trans (capTime_le_cap m (ζ₂ ω) t))))
    refine ⟨s₀, t₀, le_top, le_top, ?_, fun s' t' _ _ he => ?_⟩
    · rw [ha₁, ha₂, hcs₀, hct₀]
      exact hfc.2.2.1
    · rw [ha₁, ha₂] at he
      obtain ⟨a, c⟩ := hfc.2.2.2 _ _ (capTime_le m (ζ₁ ω) s') (capTime_le m (ζ₂ ω) t') he
      exact ⟨a.trans (min_le_left _ _), c.trans (min_le_left _ _)⟩
  -- the capped union is relatively closed
  have hcl : ∀ᵐ ω ∂P, IsOpen (H \ shUnion ηc₁ ηc₂ t₁ t₂ ω) := by
    refine Eventually.of_forall fun ω => ?_
    have hK : IsCompact (ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recFst (fullHist ηc₁ ηc₂ ω) + t₁} ∪
        ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recSnd (fullHist ηc₁ ηc₂ ω) + t₂}) :=
      (isCompact_image_of_const (hc₁ ω) (hfr₁ ω) _).union (isCompact_image_of_const (hc₂ ω) (hfr₂ ω) _)
    have e : H \ shUnion ηc₁ ηc₂ t₁ t₂ ω = H \ (ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recFst (fullHist ηc₁ ηc₂ ω) + t₁} ∪
        ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recSnd (fullHist ηc₁ ηc₂ ω) + t₂}) := by
      rw [shUnion_eq]
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, not_and]
      exact ⟨fun ⟨hz, hn⟩ => ⟨hz, fun hu => hn hu hz⟩, fun ⟨hz, hn⟩ => ⟨hz, fun hu _ => hn hu⟩⟩
    rw [e]
    exact QuantumZipper.isOpen_H.sdiff hK.isClosed
  refine ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hag₁, hag₂, ?_⟩
  exact ae_condExp_exp_eq_shUnion (x₁ := (x₁ : ℂ)) (x₂ := (x₂ : ℂ)) hh0.measurable hc₁ hc₂ h0₁ h0₂ hm₁ hm₂ hζm₁ hζm₂
    hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂ hfc hh0 hcl


end Restart

end InteractingSLE
