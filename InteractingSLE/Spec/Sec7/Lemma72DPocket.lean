/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72DClause
import InteractingSLE.Spec.Sec7.Lemma72DHull
import InteractingSLE.Spec.Sec7.Lemma72CLocal
import InteractingSLE.Spec.Sec7.Lemma71EDisc
import InteractingSLE.Spec.Coupling.MartMeans2Sub

/-!
# Lemma 7.1's conditional clause: the inputs of `isChartCouplingCharFunConst_cond` for random charts

Packet PROVE-LEMMA72D. Three of the hypotheses of `Lemma72D.isChartCouplingCharFunConst_cond` in the pocket setting:

* `usualAugmentation_le_cond`: the augmented filtration under `P` is below the augmentation of `𝓐 ∨ 𝒬` under
  `P[· | G]` (the pocket filtration `𝓖 ≤ 𝓖_G` of `Lemma72C.PocketCondStatement`);
* `norm_condExp_cexp_of_isHistoryAvoidanceLocal` (**the modulus `hmod`**): for a history-marked local set `B` of the
  centred field, the conditional characteristic function of `h(φ)` given germs ∨ marks has modulus
  `exp(−½ G_{ℍ ∖ B}(φ, φ))` (`Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal`);
* `exists_cover_clauseEvent` (**the cover `hcov`**): for conformal charts whose closed-ball domain events and masked
  forward maps are measurable for `𝓐₀ ≤ 𝓐_t`, and a driver adapted before `ζ` to `𝓐`, the clause event
  `{t < ζ, supp φ ⊆ inv(ℍ ∖ K_t)}` is a countable union of `𝓐_t`-events inside it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.Lemma72D

open Coupling LocalSets

/-! ### The filtrations -/

/-- `usualAugmentation 𝓐 P ≤ usualAugmentation (𝓐 ∨ 𝒬) P[· | G]`. -/
theorem usualAugmentation_le_cond {Ω : Type*} (𝒬 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (𝓐 : Filtration ℝ≥0 mΩ) (h𝒬 : 𝒬 ≤ mΩ) (G : Set Ω) :
    usualAugmentation 𝓐 P ≤ usualAugmentation (supConst 𝓐 𝒬 h𝒬) (P[|G]) := by
  intro t
  rw [Ito.usualAugmentation_apply, Ito.usualAugmentation_apply]
  refine iInf₂_mono fun u _ => ?_
  rw [Ito.nullAugmented_apply, Ito.nullAugmented_apply]
  refine sup_le_sup (le_supConst 𝓐 𝒬 h𝒬 u) (MeasurableSpace.generateFrom_le fun s hs => ?_)
  exact MeasurableSpace.measurableSet_generateFrom ⟨hs.1, cond_absolutelyContinuous hs.2⟩

/-! ### The modulus from history-marked locality -/

section Modulus

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The modulus of the conditional characteristic function given germs ∨ marks.** For a history-marked local set
`B` of the centred field `h − u₀` (a zero-boundary GFF), given `germSigma B (h − u₀) ⊔ ℋ` the pairing `h(φ)` has a
conditional characteristic function of modulus `exp(−½ G_{ℍ ∖ B}(φ, φ))`. -/
theorem norm_condExp_cexp_of_isHistoryAvoidanceLocal {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (hhm : Measurable h)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    {B : Ω → Set ℂ} (hB : Measurable[mΩ, hittingSigma] B) (hℋ : ℋ ≤ mΩ)
    (hloc : WholeField.IsHistoryAvoidanceLocal ℋ B (WholeField.centredField h u₀) P)
    (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω)) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ‖P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
        germSigma B (WholeField.centredField h u₀) ⊔ ℋ] ω‖ =
      Real.exp (-(1 / 2) * zeroGFFTestCov (H \ B ω) φ φ) := by
  obtain ⟨h₁, hh₁m, -, hcond⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh0 hB hℋ hloc hBc
  have hcm := WholeField.measurable_centredField hhm u₀
  have hgle : germSigma B (WholeField.centredField h u₀) ≤ mΩ := germSigma_le hB hcm
  have h𝒢 : germSigma B (WholeField.centredField h u₀) ⊔ ℋ ≤ mΩ := sup_le hgle hℋ
  have hh₁m' : Measurable[germSigma B (WholeField.centredField h u₀) ⊔ ℋ] h₁ := hh₁m.mono le_sup_left le_rfl
  have hZm : Measurable fun ω => WholeField.centredField h u₀ ω - h₁ ω :=
    LQGMetric.measurable_distOn_iff.2 fun ψ => by
      rw [show (fun ω => (WholeField.centredField h u₀ ω - h₁ ω) ψ) =
        fun ω => WholeField.centredField h u₀ ω ψ - h₁ ω ψ from rfl]
      exact ((LQGMetric.measurable_distOn_apply ψ).comp hcm).sub
        ((LQGMetric.measurable_distOn_apply ψ).comp (hh₁m.mono hgle le_rfl))
  refine norm_condExp_cexp_of_isCondZeroBoundaryGFF h𝒢 hZm hcond φ
    (R := fun ω => h₁ ω φ + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ φ)
    (((LQGMetric.measurable_distOn_apply φ).comp hh₁m').add_const _) fun ω => ?_
  show h ω φ = (h ω - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ - h₁ ω) φ +
    (h₁ ω φ + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ φ)
  simp only [sub_apply]
  ring

end Modulus

/-! ### The countable cover of the clause event -/

section Cover

variable {nL nR : ℕ} {Ω : Type*} {𝓐₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {𝓐 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : Ω → Chart}

omit mΩ in
/-- Points of a dense sequence of a compact set approximate every point of it. -/
theorem exists_dist_lt_of_denseSeq {K : Set ℂ} {d : ℕ → ℂ} (hd : K ⊆ closure (range d)) {z : ℂ} (hz : z ∈ K)
    {ε : ℝ} (hε : 0 < ε) : ∃ i, dist z (d i) < ε := by
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := Metric.mem_closure_iff.1 (hd hz) ε hε
  exact ⟨i, hi⟩

/-- **The clause event is a countable union of `𝓐_t`-events inside it.** Charts conformal with closed-ball domain
events and masked forward maps measurable for `𝓐₀ ≤ 𝓐_t`; the driver adapted before `ζ` to `𝓐` and continuous before
`ζ`; `{t < ζ} ∈ 𝓐_t`. -/
theorem exists_cover_clauseEvent (hcc : ∀ ω, (c ω).IsConformal)
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet[𝓐₀] {ω | closedBall z r ⊆ (c ω).dom})
    (hfm : ∀ z, Measurable[𝓐₀] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hWa : AdaptedBefore 𝓐 ζ W) (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (t : ℝ≥0)
    (h₀ : 𝓐₀ ≤ 𝓐 t) (hζ : MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < ζ ω}) (φ : TestOn upperHalfPlaneOpens) :
    ∃ E : ℕ → Set Ω, (∀ j, MeasurableSet[𝓐 t] (E j)) ∧ (∀ j, E j ⊆ clauseEvent W ζ c t φ) ∧
      clauseEvent W ζ c t φ ⊆ ⋃ j, E j := by
  classical
  set K : Set ℂ := tsupport φ with hKdef
  have hKc : IsCompact K := φ.hasCompactSupport.isCompact
  set Kt : Ω → Set ℂ := fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) with hKt
  have hdom : ∀ ω, IsOpen ((c ω).dom : Set ℂ) := fun ω => (c ω).dom.isOpen
  have hmem : ∀ z, MeasurableSet[𝓐₀] {ω | z ∈ (c ω).dom} := fun z =>
    @Lemma71E.measurableSet_mem_of_closedBall Ω 𝓐₀ (fun ω => ((c ω).dom : Set ℂ)) hdom hCm z
  -- the empty support
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨fun _ => {ω | (t : ℝ≥0∞) < ζ ω}, fun _ => hζ, fun _ ω hω => ⟨hω, ?_⟩, fun ω hω =>
      mem_iUnion.2 ⟨0, hω.1⟩⟩
    show tsupport φ ⊆ _
    rw [← hKdef, hK0]; exact empty_subset _
  -- a dense sequence of the support
  obtain ⟨S, hSK, hSc, hKS⟩ := (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hSne : S.Nonempty := by
    obtain ⟨z, hz⟩ := hKne
    by_contra hS
    rw [not_nonempty_iff_eq_empty] at hS
    have := hKS hz
    rw [hS, closure_empty] at this
    exact this
  obtain ⟨d, rfl⟩ := hSc.exists_eq_range hSne
  -- the pieces
  set E' : Finset (ℚ × ℚ × ℚ) × ℕ → Set Ω := fun p =>
    if ballsK p.1 ⊆ H then
      {ω | (t : ℝ≥0∞) < ζ ω ∧ Disjoint (ballsK p.1) (Kt ω)} ∩
        ((⋂ i, {ω | closedBall (d i) (1 / ((p.2 : ℝ) + 1)) ⊆ (c ω).dom}) ∩
          ⋂ i, ({ω | d i ∈ (c ω).dom}ᶜ ∪
            ({ω | d i ∈ (c ω).dom} ∩ ({ω | d i ∈ (c ω).dom}.indicator fun ω => (c ω).1 (d i)) ⁻¹' ballsK p.1)))
    else ∅ with hE'def
  have hE'm : ∀ p, MeasurableSet[𝓐 t] (E' p) := fun p => by
    have hfw' : ∀ i, MeasurableSet[𝓐₀] ({ω | d i ∈ (c ω).dom}ᶜ ∪
        ({ω | d i ∈ (c ω).dom} ∩ ({ω | d i ∈ (c ω).dom}.indicator fun ω => (c ω).1 (d i)) ⁻¹' ballsK p.1)) :=
      fun i => by
        let _ : MeasurableSpace Ω := 𝓐₀
        exact (hmem (d i)).compl.union ((hmem (d i)).inter
          ((hfm (d i)) (isCompact_ballsK p.1).isClosed.measurableSet))
    let _ : MeasurableSpace Ω := 𝓐 t
    by_cases hp : ballsK p.1 ⊆ H
    · simp only [hE'def, hp, ↓reduceIte]
      exact (measurableSet_lt_disjoint_ballsK hWa hc t hζ hp).inter ((MeasurableSet.iInter fun i =>
        h₀ _ (hCm (d i) _)).inter (MeasurableSet.iInter fun i => h₀ _ (hfw' i)))
    · simp only [hE'def, hp, ↓reduceIte]; exact MeasurableSet.empty
  -- every point of `K` is in the domain, and the forward map sends `K` into `ballsK`, on a piece
  have hsub : ∀ p, E' p ⊆ clauseEvent W ζ c t φ := fun p ω hω => by
    by_cases hp : ballsK p.1 ⊆ H
    swap
    · simp only [hE'def, hp, ↓reduceIte] at hω; exact absurd hω (notMem_empty ω)
    simp only [hE'def, hp, ↓reduceIte, mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_union, mem_compl_iff,
      mem_preimage] at hω
    obtain ⟨⟨hlt, hdis⟩, hball, hfw⟩ := hω
    have hKdom : ∀ z ∈ K, z ∈ (c ω).dom := fun z hz => by
      obtain ⟨i, hi⟩ := exists_dist_lt_of_denseSeq hKS hz (ε := 1 / ((p.2 : ℝ) + 1)) (by positivity)
      exact hball i (mem_closedBall.2 hi.le)
    have hfwd : ∀ i, (c ω).1 (d i) ∈ ballsK p.1 := fun i => by
      rcases hfw i with h | ⟨hmem', h⟩
      · exact absurd (hKdom _ (hSK (mem_range_self i))) h
      · rwa [indicator_of_mem (show ω ∈ {ω | d i ∈ (c ω).dom} from hmem')] at h
    refine ⟨hlt, fun z hz => ?_⟩
    rw [(hcc ω).image_eq_inter_preimage sdiff_subset]
    have hzd := hKdom z hz
    refine ⟨hzd, ?_⟩
    have hcont : ContinuousAt (c ω).1 z :=
      ((hcc ω).differentiableOn_fwd.continuousOn).continuousAt ((hdom ω).mem_nhds hzd)
    have hcl : (c ω).1 z ∈ closure ((c ω).1 '' range d) := mem_closure_image hcont (hKS hz)
    have hK : (c ω).1 z ∈ ballsK p.1 := by
      refine closure_minimal ?_ (isCompact_ballsK p.1).isClosed hcl
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hfwd i
    exact ⟨hp hK, fun hzK => Set.disjoint_left.1 hdis hK hzK⟩
  -- the pieces cover the clause event
  have hcov : clauseEvent W ζ c t φ ⊆ ⋃ p, E' p := fun ω hω => by
    obtain ⟨hlt, hsupp⟩ := hω
    rw [(hcc ω).image_eq_inter_preimage sdiff_subset] at hsupp
    have hKdom : K ⊆ (c ω).dom := fun z hz => (hsupp hz).1
    obtain ⟨δ, hδ, hδK⟩ := hKc.exists_thickening_subset_open (hdom ω) hKdom
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    have hopen : IsOpen (H \ Kt ω) := MartMeans2.isOpen_H_diff_fwdHull_rpath (hc ω) hlt
    have himc : IsCompact ((c ω).1 '' K) :=
      hKc.image_of_continuousOn ((hcc ω).differentiableOn_fwd.continuousOn.mono hKdom)
    obtain ⟨F, hF1, hF2⟩ := exists_rationalBalls himc hopen fun _ ⟨z, hz, hzw⟩ => hzw ▸ (hsupp hz).2
    have hFH : ballsK F ⊆ H := fun w hw => (hF2 hw).1
    refine mem_iUnion.2 ⟨(F, m), ?_⟩
    simp only [hE'def, hFH, ↓reduceIte, mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_union, mem_compl_iff,
      mem_preimage]
    refine ⟨⟨hlt, Set.disjoint_left.2 fun w hw hwK => (hF2 hw).2 hwK⟩, fun i => ?_, fun i => ?_⟩
    · intro w hw
      refine hδK (Metric.mem_thickening_iff.2 ⟨d i, hSK (mem_range_self i), ?_⟩)
      exact lt_of_le_of_lt (mem_closedBall.1 hw) hm
    · right
      have hdi : d i ∈ (c ω).dom := hKdom (hSK (mem_range_self i))
      refine ⟨hdi, ?_⟩
      rw [indicator_of_mem (show ω ∈ {ω | d i ∈ (c ω).dom} from hdi)]
      exact ballsU_subset_ballsK F (hF1 ⟨d i, hSK (mem_range_self i), rfl⟩)
  -- reindex by `ℕ`
  obtain ⟨f, hf⟩ := exists_surjective_nat (Finset (ℚ × ℚ × ℚ) × ℕ)
  refine ⟨fun j => E' (f j), fun j => hE'm _, fun j => hsub _, fun ω hω => ?_⟩
  obtain ⟨p, hp⟩ := mem_iUnion.1 (hcov hω)
  obtain ⟨j, rfl⟩ := hf p
  exact mem_iUnion.2 ⟨j, hp⟩

end Cover

end InteractingSLE.Sec7.Lemma72D
