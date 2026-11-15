/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1StopLine
import InteractingSLE.Spec.Sec6.Prop61BMarked

/-!
# Lemma 7.7's marked locality at the first-contact stopping line

Packet PROVE-RESTART-CPL6, (R1) (b) of `FirstContactKernelClockStatement`: "marked locality off the union"
(specification Lemma 7.7, `source/spec/p241-288.md#lem-7.7-proof`, pp. 282–284, "Marked locality"; it is the input
"Lemma 7.7 has established the common first point, marked locality, confinement, and old-union avoidance" of
Lemma 7.8, p. 292).

Setting: two continuous paths `η₁, η₂` on `[0, ∞)` (an available path frozen after its lifetime) with deterministic
starting points and lifetimes `ζ₁, ζ₂`, a field `h`. Hypotheses (those of Lemma 6.2, `Sec6.le_aeSigma_explored`, with
the killing record retained, and Lemma 7.7's common first point):
* every coordinate `ηᵢ(t)` and the lifetime `ζᵢ` are almost surely Borel functions of `h` (field determination,
  Lemma 7.5);
* each path is history-sensitively local at first entrance times, with its killing record
  (`IsEntranceKilledHistoryLocal`; for a flow line, Aux. lemma 56's retained-range law);
* almost surely, if the paths meet they have a first contact (`IsFirstContact` with infinite lifetimes; Lemma 7.7's
  common-first-point clause, landed for flow lines as `Supp10.Lemma77Statement`).

The selected pair `(σ₁, σ₂)` is the first contact, `(⊤, ⊤)` if the paths never meet (Lemma 7.7: "If there is no
finite contact, both contact parameters are infinite by convention"); here it is the measurable reconstruction
`recFst`, `recSnd` of the full histories (`fcLine`), which is the first contact on the almost sure event above.
The union is `fcUnion = η₁([0, σ₁]) ∪ η₂([0, σ₂])` (its `ℍ`-part, as Lemma 6.2's `explored`), and the retained
history is `fcHist`, the two killed stopped histories.

## Main results

* **`le_aeSigma_fcUnion`**: for every open `U ⊆ ℍ`, the avoidance event `{fcUnion ∩ U = ∅}` and, on it, both killed
  stopped histories are almost surely determined by `h_{U^c}`.
  Proof (the route of Lemma 6.2's proof, with (GR1) in place of the sequential induction): with `Tᵢ` the first
  entrance times into `U`, the killed histories through `Tᵢ` are `h_{U^c}`-determined (`measurable_entranceKHist`);
  the union avoids `U` iff `σᵢ ≤ Tᵢ` for both `i`, and this event and the histories through `σ` are measurable
  functions of the histories through `T` (`rec_le_iff`, `rec_eq`, `khistRestrict_khistOf`).
* `markedSigma_fcUnion_le`: the recorded union is read from the retained histories;
* **`isMarkedAvoidanceLocal_fcUnion`**, `isLocalSet_fcUnion`: the union is a local set (Lemma 3.6);
* **`isHistoryAvoidanceLocal_fcUnion`**: the history-marked avoidance criterion of Aux. lemma 18 for the union with
  the retained histories as marks;
* **`ae_condExp_exp_eq_fcUnion`** (marked locality off the union): given the germs of the union and the two
  retained histories, on every complementary component `C` (in particular the unbounded one, `activeDomain`) the
  field is its local-set mean plus a zero-boundary GFF of `C`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open LocalSets Sec6

/-! ### The first-contact union and its retained histories -/

section Defs

variable {Ω : Type*}

/-- The full recorded histories of two paths. -/
def fullHist (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ω : Ω) : Hist × Hist :=
  (histOf (pathCoord (η₁ ω)) ⊤, histOf (pathCoord (η₂ ω)) ⊤)

/-- The two paths as a family indexed by `Fin 2`. -/
def pairPath (η₁ η₂ : Ω → ℝ≥0 → ℂ) : Fin 2 → Ω → ℝ≥0 → ℂ := ![η₁, η₂]

/-- **The first-contact stopping line** `(σ₁, σ₂)`, read measurably from the full histories (`recFst`, `recSnd`):
on the almost sure event of Lemma 7.7 it is the first contact, `(⊤, ⊤)` if the paths never meet (`fcLine_eq`). -/
def fcLine (η₁ η₂ : Ω → ℝ≥0 → ℂ) : Fin 2 → Ω → ℝ≥0∞ :=
  ![fun ω => recFst (fullHist η₁ η₂ ω), fun ω => recSnd (fullHist η₁ η₂ ω)]

/-- **The first-contact union** `η₁([0, σ₁]) ∪ η₂([0, σ₂])` (its `ℍ`-part). -/
def fcUnion (η₁ η₂ : Ω → ℝ≥0 → ℂ) : Ω → Set ℂ := explored (pairPath η₁ η₂) (fcLine η₁ η₂)

/-- **The retained histories**: the two killed stopped histories at the first-contact stopping line. -/
def fcHist (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (ω : Ω) : KHist × KHist :=
  (khistOf (pathCoord (η₁ ω)) (ζ₁ ω) (recFst (fullHist η₁ η₂ ω)),
    khistOf (pathCoord (η₂ ω)) (ζ₂ ω) (recSnd (fullHist η₁ η₂ ω)))

theorem fcUnion_eq (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ω : Ω) :
    fcUnion η₁ η₂ ω = (η₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recFst (fullHist η₁ η₂ ω)} ∪
      η₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recSnd (fullHist η₁ η₂ ω)}) ∩ H := by
  ext z
  simp only [fcUnion, explored, pairPath, fcLine, mem_inter_iff, mem_iUnion, Fin.exists_fin_two, mem_union,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- On the event of Lemma 7.7, the stopping line is the first contact (`⊤` if there is none). -/
theorem fcLine_eq {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ω : Ω} (hc₁ : Continuous (η₁ ω)) (hc₂ : Continuous (η₂ ω))
    {σ₁ σ₂ : ℝ≥0∞} (hσ : IsFCPair (η₁ ω) (η₂ ω) σ₁ σ₂) :
    recFst (fullHist η₁ η₂ ω) = σ₁ ∧ recSnd (fullHist η₁ η₂ ω) = σ₂ :=
  rec_eq hc₁ hc₂ hσ le_top le_top

/-- Under Lemma 7.7's common-first-point clause, the first-contact pair exists. -/
theorem exists_isFCPair {γ₁ γ₂ : ℝ≥0 → ℂ}
    (hfc : (∃ s t : ℝ≥0, γ₁ s = γ₂ t) → ∃ s₀ t₀ : ℝ≥0, IsFirstContact γ₁ ⊤ γ₂ ⊤ s₀ t₀) :
    ∃ σ₁ σ₂ : ℝ≥0∞, IsFCPair γ₁ γ₂ σ₁ σ₂ := by
  by_cases hm : ∃ s t : ℝ≥0, γ₁ s = γ₂ t
  · obtain ⟨s₀, t₀, h⟩ := hfc hm
    exact ⟨s₀, t₀, Or.inl ⟨s₀, t₀, h, rfl, rfl⟩⟩
  · push Not at hm
    exact ⟨⊤, ⊤, Or.inr ⟨hm, rfl, rfl⟩⟩

variable [MeasurableSpace Ω]

theorem measurable_fullHist {η₁ η₂ : Ω → ℝ≥0 → ℂ} (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t)
    (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t) : Measurable (fullHist η₁ η₂) := by
  have h₁ : Measurable fun ω => pathCoord (η₁ ω) := Measurable.of_eval fun q => hηm₁ q
  have h₂ : Measurable fun ω => pathCoord (η₂ ω) := Measurable.of_eval fun q => hηm₂ q
  exact (measurable_histOf.comp (measurable_const.prodMk h₁)).prodMk
    (measurable_histOf.comp (measurable_const.prodMk h₂))

theorem measurable_fcLine {η₁ η₂ : Ω → ℝ≥0 → ℂ} (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t)
    (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t) (i : Fin 2) : Measurable (fcLine η₁ η₂ i) := by
  fin_cases i
  · exact measurable_recFst.comp (measurable_fullHist hηm₁ hηm₂)
  · exact measurable_recSnd.comp (measurable_fullHist hηm₁ hηm₂)

theorem measurable_fcHist {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t)
    (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t) (hζm₁ : Measurable ζ₁) (hζm₂ : Measurable ζ₂) :
    Measurable (fcHist η₁ η₂ ζ₁ ζ₂) := by
  have h₁ : Measurable fun ω => pathCoord (η₁ ω) := Measurable.of_eval fun q => hηm₁ q
  have h₂ : Measurable fun ω => pathCoord (η₂ ω) := Measurable.of_eval fun q => hηm₂ q
  have hF := measurable_fullHist hηm₁ hηm₂
  have hk : Measurable fun p : (ℚ≥0 → ℂ) × ℝ≥0∞ × ℝ≥0∞ => khistOf p.1 p.2.1 p.2.2 :=
    (measurable_histOf.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).prodMk
      (measurable_lifeRec.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
  have e₁ := hk.comp (h₁.prodMk (hζm₁.prodMk (measurable_recFst.comp hF)))
  have e₂ := hk.comp (h₂.prodMk (hζm₂.prodMk (measurable_recSnd.comp hF)))
  dsimp only [Function.comp_def] at e₁ e₂
  exact e₁.prodMk e₂

theorem measurable_fcUnion {η₁ η₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (η₁ ω))
    (hc₂ : ∀ ω, Continuous (η₂ ω)) (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t)
    (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t) : Measurable[_, hittingSigma] (fcUnion η₁ η₂) := by
  refine measurable_explored (fun i ω => ?_) (fun i t => ?_) (measurable_fcLine hηm₁ hηm₂)
  · fin_cases i
    · exact hc₁ ω
    · exact hc₂ ω
  · fin_cases i
    · exact hηm₁ t
    · exact hηm₂ t

end Defs

/-! ### The aeSigma closure -/

theorem measurableSet_aeSigma_of_ae_eq {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {S S' : Set Ω} (h : S =ᵐ[P] S') (hS' : MeasurableSet[aeSigma m P] S') :
    MeasurableSet[aeSigma m P] S := by
  obtain ⟨G', hG', he⟩ := hS'
  exact ⟨G', hG', h.trans he⟩

/-! ### The avoidance event and the recorded union -/

section Avoid

variable {Ω : Type*} {η₁ η₂ : Ω → ℝ≥0 → ℂ}

/-- **The union avoids `U` iff both stopped paths do.** -/
theorem disjoint_fcUnion_iff {U : Set ℂ} (hUH : U ⊆ H) (ω : Ω) :
    Disjoint (fcUnion η₁ η₂ ω) U ↔ AvoidsUpTo (η₁ ω) (recFst (fullHist η₁ η₂ ω)) U ∧
      AvoidsUpTo (η₂ ω) (recSnd (fullHist η₁ η₂ ω)) U := by
  rw [fcUnion, disjoint_explored_iff hUH ω, Fin.forall_fin_two]
  simp only [pairPath, fcLine, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem continuous_pairPath (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω)) :
    ∀ i ω, Continuous (pairPath η₁ η₂ i ω) := by
  intro i ω
  fin_cases i
  · exact hc₁ ω
  · exact hc₂ ω

variable {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The recorded union is read from the retained histories**: the σ-algebra of Lemma 3.6 (ii) of the union (the
avoidance event and the union recorded on it) is contained in the σ-algebra of the avoidance event and the retained
histories recorded on it. -/
theorem markedSigma_fcUnion_le (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω)) (U : Set ℂ) :
    markedSigma (fcUnion η₁ η₂) U ≤
      markedHistSigma {ω | Disjoint (fcUnion η₁ η₂ ω) U} (fcHist η₁ η₂ ζ₁ ζ₂) := by
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
    have e : (fun ω => markedSet U (fcUnion η₁ η₂ ω)) ⁻¹' {A | (A ∩ V).Nonempty} =
        {ω | Disjoint (fcUnion η₁ η₂ ω) U} ∩ fcHist η₁ η₂ ζ₁ ζ₂ ⁻¹' Ψ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, markedSet_inter_nonempty_iff, mem_inter_iff]
      refine and_congr_right fun _ => ?_
      rw [fcUnion, explored_inter_nonempty_iff (continuous_pairPath hc₁ hc₂) hVo hVH ω, Fin.exists_fin_two]
      simp only [pairPath, fcLine, Matrix.cons_val_zero, Matrix.cons_val_one, hΨdef, mem_union, mem_ofPred_eq,
        fcHist, khistOf, histOf]
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
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℂ}

/-- **The core of Lemma 7.7's marked locality**: for every open `U ⊆ ℍ` and Borel version `G` of the projection onto
`H(U)`, the avoidance event of the first-contact union and, on it, the two retained killed histories are almost
surely determined by `h_{U^c}`. -/
theorem le_aeSigma_fcUnion (hhm : Measurable h) (hc₁ : ∀ ω, Continuous (η₁ ω))
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
    markedHistSigma {ω | Disjoint (fcUnion η₁ η₂ ω) U} (fcHist η₁ η₂ ζ₁ ζ₂) ≤
      aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P := by
  classical
  set N := aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P with hNdef
  let _ : MeasurableSpace Ω := mΩ
  by_cases hx : x₁ ∈ (U : Set ℂ) ∨ x₂ ∈ (U : Set ℂ)
  · -- a starting point lies in `U`: the union always meets `U`
    have hE : {ω | Disjoint (fcUnion η₁ η₂ ω) U} = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
      have hω' : Disjoint (fcUnion η₁ η₂ ω) U := hω
      rw [disjoint_fcUnion_iff hUH ω] at hω'
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
    {y | recFst (y.1.1, y.2.1) ≤ y.1.1.1 ∧ recSnd (y.1.1, y.2.1) ≤ y.2.1.1} with hΨEdef
  have hΨE : MeasurableSet ΨE :=
    (measurableSet_le (measurable_recFst.comp hpr) (measurable_fst.comp (measurable_fst.comp measurable_fst))).inter
      (measurableSet_le (measurable_recSnd.comp hpr) (measurable_fst.comp (measurable_fst.comp measurable_snd)))
  have hΦm := (measurable_khistRestrict.comp (measurable_fst.prodMk (measurable_recFst.comp hpr))).prodMk
    (measurable_khistRestrict.comp (measurable_snd.prodMk (measurable_recSnd.comp hpr)))
  dsimp only [Function.comp_def] at hΦm
  -- pointwise identification on the event of Lemma 7.7
  have hgood : ∀ᵐ ω ∂P, ∃ σ₁ σ₂ : ℝ≥0∞, IsFCPair (η₁ ω) (η₂ ω) σ₁ σ₂ := by
    filter_upwards [hfc] with ω hω using exists_isFCPair hω
  have hpt : ∀ ω, (∃ σ₁ σ₂ : ℝ≥0∞, IsFCPair (η₁ ω) (η₂ ω) σ₁ σ₂) →
      (Disjoint (fcUnion η₁ η₂ ω) U ↔
        (khistOf (pathCoord (η₁ ω)) (ζ₁ ω) (firstEntrance U (pathCoord (η₁ ω))),
          khistOf (pathCoord (η₂ ω)) (ζ₂ ω) (firstEntrance U (pathCoord (η₂ ω)))) ∈ ΨE) ∧
      (Disjoint (fcUnion η₁ η₂ ω) U →
        (khistRestrict (khistOf (pathCoord (η₁ ω)) (ζ₁ ω) (firstEntrance U (pathCoord (η₁ ω))))
            (recFst (histOf (pathCoord (η₁ ω)) (firstEntrance U (pathCoord (η₁ ω))),
              histOf (pathCoord (η₂ ω)) (firstEntrance U (pathCoord (η₂ ω))))),
          khistRestrict (khistOf (pathCoord (η₂ ω)) (ζ₂ ω) (firstEntrance U (pathCoord (η₂ ω))))
            (recSnd (histOf (pathCoord (η₁ ω)) (firstEntrance U (pathCoord (η₁ ω))),
              histOf (pathCoord (η₂ ω)) (firstEntrance U (pathCoord (η₂ ω)))))) =
          fcHist η₁ η₂ ζ₁ ζ₂ ω) := by
    rintro ω ⟨σ₁, σ₂, hσ⟩
    obtain ⟨e₁, e₂⟩ := fcLine_eq (hc₁ ω) (hc₂ ω) hσ
    have hav : Disjoint (fcUnion η₁ η₂ ω) U ↔
        σ₁ ≤ firstEntrance U (pathCoord (η₁ ω)) ∧ σ₂ ≤ firstEntrance U (pathCoord (η₂ ω)) := by
      rw [disjoint_fcUnion_iff hUH ω, e₁, e₂]
      exact and_congr (disjoint_range_iff_le_firstEntrance U.isOpen (hc₁ ω) (h0₁' ω) σ₁)
        (disjoint_range_iff_le_firstEntrance U.isOpen (hc₂ ω) (h0₂' ω) σ₂)
    refine ⟨hav.trans (rec_le_iff (hc₁ ω) (hc₂ ω) hσ), fun hω => ?_⟩
    obtain ⟨h₁, h₂⟩ := hav.1 hω
    obtain ⟨r₁, r₂⟩ := rec_eq (hc₁ ω) (hc₂ ω) hσ h₁ h₂
    rw [r₁, r₂, khistRestrict_khistOf h₁, khistRestrict_khistOf h₂, fcHist, e₁, e₂]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨B, hB, rfl⟩
  refine measurableSet_aeSigma_of_ae_eq ?_ (hHtm (hΨE.inter (hΦm hB)))
  filter_upwards [hgood] with ω hω
  have hp := hpt ω hω
  refine propext ⟨fun hωEB => ⟨hp.1.1 hωEB.1, ?_⟩, fun hωΨB => ⟨hp.1.2 hωΨB.1, ?_⟩⟩
  · have key : fcHist η₁ η₂ ζ₁ ζ₂ ω ∈ B := hωEB.2
    rw [← hp.2 hωEB.1] at key
    exact key
  · show fcHist η₁ η₂ ζ₁ ζ₂ ω ∈ B
    rw [← hp.2 (hp.1.2 hωΨB.1)]
    exact hωΨB.2

end Main

/-! ### Consequences: locality, history marking, the conditional law off the union -/

section Consequences

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℂ}
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
theorem condIndepEv_fcHist (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) :
    CondIndepEv (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance)
      (markedHistSigma {ω | Disjoint (fcUnion η₁ η₂ ω) U} (fcHist η₁ η₂ ζ₁ ζ₂))
      (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance) P :=
  condIndepEv_of_le_aeSigma ((measurable_markovCompl hG).comp hhm).comap_le (hG.comp hhm).comap_le
    (le_aeSigma_fcUnion hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂ hfc
      U G hUH hG hd)

/-- **The first-contact union satisfies Lemma 3.6 (ii).** -/
theorem isMarkedAvoidanceLocal_fcUnion : IsMarkedAvoidanceLocal (fcUnion η₁ η₂) h P := fun U G hUH hG hd =>
  condIndepEv_of_le_aeSigma ((measurable_markovCompl hG).comp hhm).comap_le (hG.comp hhm).comap_le
    ((markedSigma_fcUnion_le (ζ₁ := ζ₁) (ζ₂ := ζ₂) hc₁ hc₂ U).trans
      (le_aeSigma_fcUnion hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂ hfc
        U G hUH hG hd))

/-- **Lemma 7.7, locality**: for a zero-boundary GFF, if the first-contact union is almost surely relatively closed
in `ℍ`, it is a local set (Lemma 3.6, (ii) ⇒ (iv)). -/
theorem isLocalSet_fcUnion (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hcl : ∀ᵐ ω ∂P, IsOpen (H \ fcUnion η₁ η₂ ω)) : IsLocalSet (fcUnion η₁ η₂) h P := by
  have hA := measurable_fcUnion hc₁ hc₂ hηm₁ hηm₂
  have hAc : ∀ᵐ ω ∂P, fcUnion η₁ η₂ ω ⊆ H ∧ IsOpen (H \ fcUnion η₁ η₂ ω) := by
    filter_upwards [hcl] with ω hω using ⟨inter_subset_right, hω⟩
  exact ((isLocalSet_tfae hh hA hAc).out 2 4).1
    (isMarkedAvoidanceLocal_fcUnion hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁
      hloc₂ hfc)

/-- **Lemma 7.7, history marking** (Aux. lemma 18's criterion for the union with the retained histories as marks):
for every open `U ⊆ ℍ`, every Borel version `G` of the projection onto `H(U)` and every event `F` of the retained
histories, `P[{fcUnion ∩ U = ∅} ∩ F | h]` is a measurable function of `h − G h`. -/
theorem isHistoryAvoidanceLocal_fcUnion :
    WholeField.IsHistoryAvoidanceLocal (MeasurableSpace.comap (fcHist η₁ η₂ ζ₁ ζ₂) inferInstance)
      (fcUnion η₁ η₂) h P := by
  intro U G hUH hG hd F hF
  obtain ⟨B, hB, rfl⟩ := hF
  have hmem := le_aeSigma_fcUnion hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂
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
theorem ae_condExp_exp_eq_fcUnion (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hcl : ∀ᵐ ω ∂P, IsOpen (H \ fcUnion η₁ η₂ ω)) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (fcUnion η₁ η₂) h P g ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ fcUnion η₁ η₂ ω,
        tsupport φ ⊆ connectedComponentIn (H \ fcUnion η₁ η₂ ω) z₀ →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
            germSigma (fcUnion η₁ η₂) h ⊔ MeasurableSpace.comap (fcHist η₁ η₂ ζ₁ ζ₂) inferInstance] ω =
          Complex.exp (Complex.I * (g ω φ : ℂ)) *
            ((Real.exp (-(1 / 2) *
              QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ fcUnion η₁ η₂ ω) z₀) φ φ) : ℝ) : ℂ) := by
  have hA := measurable_fcUnion hc₁ hc₂ hηm₁ hηm₂
  have hloc := isLocalSet_fcUnion hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂
    hfc hh hcl
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh hA hloc
  refine ⟨g, hg, fun φ => ?_⟩
  exact ae_condExp_exp_eq_of_component_marked hh hA hloc
    (measurable_fcHist hηm₁ hηm₂ hζm₁ hζm₂).comap_le
    (isHistoryAvoidanceLocal_fcUnion hhm hc₁ hc₂ h0₁ h0₂ hηm₁ hηm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁
      hloc₂ hfc) hg φ

end Consequences

end Restart

end InteractingSLE
