/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketUnionPtGeom

/-!
# The pocket union law and pointwise mean from the ambient pocket domain at `T(q)`

Packet PROVE-STRIPSYS32. Specification §7.4: Aux. lemma 124 (`source/spec/p385-432.md` L171–L196, pp. 393–394),
Aux. lemma 125's proof (L213–L232, pp. 396–397: "the relative active domain at `S` is exactly the target component of
`C ∖ R_{T(S)}` […] Aux. lemma 124 preserves the actual canonical active mean at `T(S)`. The marked local-set law gives
its active Dirichlet covariance"), and Aux. lemmas 35–36 (`source/spec/p145-192.md` L908–L940,
`source/spec/p193-240.md` L1–L78: the marked stopping-time union law of `A_T = Γ ∪ R_T` and the central pocket mean).

PROVE-STRIPSYS26 reduced the pocket coupling inputs to `PocketUnionPtChartLaw`: a chart, the marked union law
`PocketUnionLaw` (local set `K_q`, history marks `ℋ_q`, mean `g_q`, the relative prefix events in
`germ(K_q) ∨ ℋ_q ∨ 𝒩`, the active domain `inv(ℍ ∖ K^{rel}_q)` measurable from `K_q` and the marks, and a union of
components of `ℍ ∖ K_q`), and the pointwise mean `PocketMeanPt` on the relative active domain. This file discharges
everything in it that is not field-level mathematics, in terms of the **ambient** pocket domain
`C ∩ D_{T(q)} = C ∩ (ℍ ∖ F_q)` (`F_q` the counterflow hull at the ambient time `T(q)`):

* the history marks are the relative history itself, `ℋ_q = 𝓦 ∨ σ(A ∩ prefix events up to q)`, so the prefix
  clause is trivial, and the live event `A ∩ {q < ζ}` is one of its events (`measurableSet_live`);
* the mean `g_q` is any version of the local-set mean (it exists for a local set of a zero-boundary GFF,
  `IsLocalSet.exists_isLocalSetMean`);
* the active domain is `C ∩ (ℍ ∖ F_q)` (`activeDom_eq_inter`, from `ψ(C ∩ (ℍ ∖ F_q)) = ℍ ∖ K^{rel}_q`), a union of
  components of `ℍ ∖ K_q` (`PocketUnionPtGeom.connectedComponentIn_subset_inter`), and measurable from `K_q` and the
  walls (`measurable_compl_activeDom`, through the pocket's frontier in `K_q` and countably many points);
* the pointwise mean on the relative active domain is the pointwise mean on the ambient one, read through the chart.

What remains are two field-level statements at the ambient time `T(q)`, for the set `K_q` (for instance the marked
union `m(walls) ∪ F_q` of Aux. lemmas 35–36, or Aux. lemma 124's `(ℍ ∖ C) ∪ F_q`):

* `PocketStopLaw` (**the marked union law at `T(q)`**, Aux. lemma 124's hypothesis, Aux. lemma 35's hypothesis,
  Lemma 6.2 at the stop `T(q)`): `K_q` is a hitting-measurable relatively closed subset of `ℍ`, history-local for the
  relative history `ℋ_q` (Aux. lemma 18's marked avoidance criterion; then `K_q` is a local set by Lemma 3.6,
  `LocalSets.isLocalSet_tfae`), containing the pocket's frontier in `ℍ` and the counterflow hull, and meeting the
  pocket only in the hull;
* `PocketStopMeanAt` (**the central pocket mean at `T(q)`**, Aux. lemma 36 with Aux. lemma 122's phase selection):
  every version of the local-set mean of `K_q`, shifted by `𝔥`, has a continuous representative `v` on
  `C ∩ (ℍ ∖ F_q)` with `v + a + k ℓ = (canonical coupling mean at q) ∘ ψ` there.

## Main results

* `PocketStopLaw`, `PocketStopMeanAt`, `PocketStopChartLaw` (the two named field-level statements and their
  combination with a pocket chart);
* `measurableSet_live`, `activeDom_eq_inter`, `measurable_compl_activeDom`;
* **`pocketUnionPtChartLaw_of_stop`**: `PocketUnionPtChartLaw` from `PocketStopChartLaw`.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketUnionPt

open PocketTraversal PocketAdapt Lemma71C LocalSets WholeField PocketCoupling

/-! ### The two field-level statements at the ambient time -/

section Defs

variable {Ω : Type*}

/-- **The marked union law at the ambient time `T(q)`** (named field-level statement; Aux. lemma 124's hypothesis
"the marked optional union law for `A ∪ R_t`", Aux. lemma 35's "marked stopping-time local-set law", Lemma 6.2 at the
stop `T(q)`): `K` is a hitting-measurable random relatively closed subset of `ℍ`, history-local for the relative
history `𝓦 ∨ σ(A ∩ prefix events up to q)` (Aux. lemma 18's marked avoidance criterion; for a zero-boundary GFF this
makes `K` a local set, Lemma 3.6), and on `A ∩ {q < ζ}` it contains the frontier in `ℍ` of the pocket `C` and the
counterflow hull `F` (in `ℍ`) and meets `C` only inside `F`. -/
def PocketStopLaw (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (C F : Ω → Set ℂ) (h₀ : Ω → DistOn upperHalfPlaneOpens) (K : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  Measurable[mΩ, hittingSigma] K ∧ (∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω)) ∧
    IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ q) K h₀ P ∧
    ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → frontier (C ω) ∩ H ⊆ K ω ∧ F ω ∩ H ⊆ K ω ∧ K ω ∩ C ω ⊆ F ω

/-- **The central pocket mean at the ambient time `T(q)`** (named field-level statement; Aux. lemma 36's mean in the
component `S = C ∩ (ℍ ∖ F)` with Aux. lemma 122's phase `d = 0`): for every version `g` of the local-set mean of `K`,
almost surely on `A ∩ {q < ζ}` the field mean `g + 𝔥` has a continuous representative `v` on `S` with
`v + a + k ℓ = (canonical coupling mean of the word at q) ∘ c.fwd` on `S`. -/
def PocketStopMeanAt (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (c : Ω → Chart)
    (a k : ℝ) (h₀ : Ω → DistOn upperHalfPlaneOpens) (𝔥 : DistOn upperHalfPlaneOpens) (K S : Ω → Set ℂ)
    (q : ℝ≥0) : Prop :=
  ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h₀ P g →
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ v : ℂ → ℝ, ContinuousOn v (S ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ S ω → (g ω + 𝔥) φ = ∫ z, v z * φ z) ∧
      ∀ z ∈ S ω, v z + a + k * (c ω).2.2 z =
        couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (Restart.DomainMarkov.bheProc κ ρL ρR (fun t ω => segDriver (γ ω) t)
            (PocketTraversal.geomLW (fun t ω => segDriver (γ ω) t) xL)
            (PocketTraversal.geomRW (fun t ω => segDriver (γ ω) t) xR) ω q) ((c ω).1 z)

/-- **The pocket chart law at the ambient times**: a pocket chart, and at every relative time `q` a set `K_q` with the
marked union law and the central pocket mean at `T(q)` (`F q` the counterflow hull at `T(q)`). -/
def PocketStopChartLaw (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (𝓦 : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (F : ℝ≥0 → Ω → Set ℂ)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (𝔥 : DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (c : Ω → Chart) (a k : ℝ), IsPocketChartOn 𝓦 A C ψ c ∧ ∀ q : ℝ≥0, ∃ K : Ω → Set ℂ,
    PocketStopLaw 𝓦 P A γ C (F q) h₀ K q ∧
      PocketStopMeanAt κ ρL ρR P A γ xL xR c a k h₀ 𝔥 K (fun ω => C ω ∩ (H \ F q ω)) q

end Defs

/-! ### The live event and the active domain -/

section Live

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω}

/-- **The live event is a relative-history event**: `A ∩ {q < ζ}` is the union over the level-`0` squares of the
prefix events at `q` (the prefix contains the seed). -/
theorem measurableSet_live (A : Set Ω) (γ : Ω → ℝ → ℂ) (q : ℝ≥0) :
    MeasurableSet[locPrefixSigma 𝓦 A γ q] {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} := by
  have e : {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} = ⋃ k : ℤ × ℤ, A ∩ prefixEvent γ q 0 k := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, prefixEvent]
    constructor
    · rintro ⟨hA, hq⟩
      refine ⟨(⌊(γ ω 0).re⌋, ⌊(γ ω 0).im⌋), hA, hq, γ ω 0, ?_, 0, ⟨le_rfl, capInv_nonneg _ _⟩, rfl⟩
      simp only [Restart.dyadicSquare, pow_zero, one_mul, mem_ofPred_eq]
      exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le, Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    · rintro ⟨k, hA, hq, -⟩
      exact ⟨hA, hq⟩
  rw [e]
  refine MeasurableSet.iUnion fun k => ?_
  exact le_sup_right (a := 𝓦) _ (MeasurableSpace.measurableSet_generateFrom ⟨q, le_rfl, 0, k, rfl⟩)

/-- **The active domain is the ambient pocket domain** on the live event, from `ψ(C ∩ (ℍ ∖ F)) = ℍ ∖ K^{rel}_q`. -/
theorem activeDom_eq_inter {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {C F : Ω → Set ℂ}
    {ψ : Ω → ℂ → ℂ} {ω : Ω} (hω : ω ∈ A) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = C ω) (hfwd : EqOn (c ω).1 (ψ ω) (C ω)) (hinj : InjOn (ψ ω) (C ω))
    (hgeo : ψ ω '' (C ω ∩ (H \ F ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) :
    activeDom A γ c q ω = C ω ∩ (H \ F ω) := by
  rw [activeDom_eq hω hq]
  exact inv_image_eq_of_image hc hdom hfwd hinj inter_subset_left hgeo

/-- Off the live event the active domain is empty. -/
theorem activeDom_eq_empty {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {ω : Ω}
    (hl : ¬ (ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω))) : activeDom A γ c q ω = ∅ := by
  ext z
  exact ⟨fun h => absurd ⟨h.1, h.2.1⟩ hl, fun h => h.elim⟩

/-- **Points off the closure of a random open set**: if the open sets `C ω` (`ω ∈ A`) have measurable point events,
so do the events `x ∉ closure (C ω)` (a ball around `x` without points of a dense sequence in `C ω`). -/
theorem measurableSet_notMem_closure {m : MeasurableSpace Ω} {A : Set Ω} {C : Ω → Set ℂ}
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hA : MeasurableSet[m] A) (hCm : ∀ z, MeasurableSet[m] {ω | ω ∈ A ∧ z ∈ C ω})
    (x : ℂ) : MeasurableSet[m] {ω | ω ∈ A ∧ x ∉ closure (C ω)} := by
  set e := TopologicalSpace.denseSeq ℂ with he_def
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq ℂ
  have eq : {ω | ω ∈ A ∧ x ∉ closure (C ω)} = A ∩ ⋃ n : ℕ, ⋂ j : ℕ,
      ({_ω | e j ∉ Metric.ball x (1 / ((n : ℝ) + 1))} ∪ {ω | ω ∈ A ∧ e j ∈ C ω}ᶜ) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, mem_union, mem_compl_iff, not_and]
    constructor
    · rintro ⟨hA, hx⟩
      refine ⟨hA, ?_⟩
      rw [Metric.mem_closure_iff] at hx
      push Not at hx
      obtain ⟨ε, hε, hεC⟩ := hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine ⟨n, fun j => ?_⟩
      by_cases hj : e j ∈ Metric.ball x (1 / ((n : ℝ) + 1))
      · refine Or.inr fun _ hjC => ?_
        have := hεC (e j) hjC
        rw [Metric.mem_ball, dist_comm] at hj
        linarith
      · exact Or.inl hj
    · rintro ⟨hA, n, hn⟩
      refine ⟨hA, fun hx => ?_⟩
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      obtain ⟨b, hbC, hb⟩ := Metric.mem_closure_iff.1 hx _ hpos
      obtain ⟨j, hj⟩ := he.exists_mem_open ((hCo ω hA).inter Metric.isOpen_ball)
        ⟨b, hbC, by rw [Metric.mem_ball, dist_comm]; exact hb⟩
      rcases hn j with h | h
      · exact h hj.2
      · exact h hA hj.1
  rw [eq]
  refine hA.inter (MeasurableSet.iUnion fun n => MeasurableSet.iInter fun j => ?_)
  exact (MeasurableSet.const _).union (hCm (e j)).compl

/-- **The active domain is measurable from `K` and the marks**: if on the live event (an `ℋ`-event) the active domain
is the ambient pocket domain `C ∩ (ℍ ∖ F)` and `K` contains the frontier of `C` in `ℍ` and the hull `F ∩ ℍ` and meets
`C` only in `F`, then `ℍ ∖ activeDom` is measurable for `σ(K) ∨ ℋ` as soon as the pocket's point events are
`ℋ`-events. -/
theorem measurable_compl_activeDom {ℋ : MeasurableSpace Ω} {K : Ω → Set ℂ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {c : Ω → Chart} {q : ℝ≥0} {C F : Ω → Set ℂ} (hA : MeasurableSet[ℋ] A)
    (hlive : MeasurableSet[ℋ] {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)}) (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCm : ∀ z, MeasurableSet[ℋ] {ω | ω ∈ A ∧ z ∈ C ω})
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ F ω))
    (hK : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      frontier (C ω) ∩ H ⊆ K ω ∧ F ω ∩ H ⊆ K ω ∧ K ω ∩ C ω ⊆ F ω) :
    Measurable[MeasurableSpace.comap K hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ activeDom A γ c q ω := by
  refine @measurable_generateFrom Ω (Set ℂ) (MeasurableSpace.comap K hittingSigma ⊔ ℋ) _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  set e := TopologicalSpace.denseSeq ℂ with he_def
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq ℂ
  set live := {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} with hlive_def
  have key : (fun ω => H \ activeDom A γ c q ω) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      (live ∩ ((⋃ n : ℕ, {_ω | e n ∈ U} ∩ {ω | ω ∈ A ∧ e n ∉ closure (C ω)}) ∪
        K ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty})) ∪ (liveᶜ ∩ {_ω | U.Nonempty}) := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_inter_iff, mem_iUnion, mem_compl_iff]
    by_cases hl : ω ∈ live
    · have hl' : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) := hl
      rw [hact ω hl'.1 hl'.2]
      obtain ⟨hfr, hF, hKC⟩ := hK ω hl'.1 hl'.2
      have hCω := hCo ω hl'.1
      constructor
      · rintro ⟨z, ⟨hzH, hzn⟩, hzU⟩
        refine Or.inl ⟨hl, ?_⟩
        by_cases hzC : z ∈ C ω
        · have hzF : z ∈ F ω := by
            by_contra hzF
            exact hzn ⟨hzC, hzH, hzF⟩
          exact Or.inr ⟨z, hF ⟨hzF, hzH⟩, hzU⟩
        · by_cases hzcl : z ∈ closure (C ω)
          · have hzfr : z ∈ frontier (C ω) := by
              rw [hCω.frontier_eq]
              exact ⟨hzcl, hzC⟩
            exact Or.inr ⟨z, hfr ⟨hzfr, hzH⟩, hzU⟩
          · obtain ⟨n, hn⟩ := he.exists_mem_open (hU.sdiff isClosed_closure) ⟨z, hzU, hzcl⟩
            exact Or.inl ⟨n, hn.1, hl'.1, hn.2⟩
      · rintro (⟨-, ⟨n, hnU, -, hncl⟩ | ⟨z, hzK, hzU⟩⟩ | ⟨hnl, -⟩)
        · exact ⟨e n, ⟨hUH hnU, fun h => hncl (subset_closure h.1)⟩, hnU⟩
        · refine ⟨z, ⟨hUH hzU, fun h => h.2.2 (hKC ⟨hzK, h.1⟩)⟩, hzU⟩
        · exact absurd hl hnl
    · rw [activeDom_eq_empty hl, sdiff_empty]
      constructor
      · rintro ⟨z, -, hzU⟩
        exact Or.inr ⟨hl, z, hzU⟩
      · rintro (⟨hl', -⟩ | ⟨-, z, hzU⟩)
        · exact absurd hl' hl
        · exact ⟨z, hUH hzU, hzU⟩
  rw [key]
  have hℋ : ∀ s, MeasurableSet[ℋ] s → MeasurableSet[MeasurableSpace.comap K hittingSigma ⊔ ℋ] s :=
    fun s hs => le_sup_right (a := MeasurableSpace.comap K hittingSigma) _ hs
  refine ((hℋ _ hlive).inter ((MeasurableSet.iUnion fun n => (MeasurableSet.const _).inter
    (hℋ _ (measurableSet_notMem_closure hCo hA hCm (e n)))).union ?_)).union
    ((hℋ _ hlive).compl.inter (MeasurableSet.const _))
  exact le_sup_left (b := ℋ) _ ⟨_, measurableSet_hitting hU hUH, rfl⟩

end Live

/-! ### The assembly -/

section Assembly

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The pocket chart law in local-set and pointwise form from the ambient-time statements**: if the relative active
domain is the ambient pocket domain read through `ψ` (`ψ(C ∩ (ℍ ∖ F_q)) = ℍ ∖ K^{rel}_q`), the marked union law and the
central pocket mean at the ambient times (`PocketStopChartLaw`) give `PocketUnionPtChartLaw`, with the relative history
`𝓦 ∨ σ(A ∩ prefix events)` as the history marks and any versions of the local-set means. -/
theorem pocketUnionPtChartLaw_of_stop {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet[𝓦] A) {γ : Ω → ℝ → ℂ}
    (hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A γ q ≤ mΩ) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    {ψ : Ω → ℂ → ℂ} (hinj : ∀ ω ∈ A, InjOn (ψ ω) (C ω)) {F : ℝ≥0 → Ω → Set ℂ}
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {𝔥 : DistOn upperHalfPlaneOpens} (hin : PocketStopChartLaw κ ρL ρR 𝓦 P A γ xL xR C ψ F h₀ 𝔥) :
    PocketUnionPtChartLaw κ ρL ρR 𝓦 P A γ xL xR C ψ h₀ 𝔥 := by
  obtain ⟨c, a, k, hc, hK⟩ := hin
  choose K hKlaw hKmean using hK
  have hloc : ∀ q, IsLocalSet (K q) h₀ P := fun q =>
    ((isLocalSet_tfae hh₀ (hKlaw q).1 (hKlaw q).2.1).out 1 4).1
      (IsHistoryAvoidanceLocal.isAvoidanceLocal (hKlaw q).2.2.1)
  have hg : ∀ q, ∃ g, IsLocalSetMean (K q) h₀ P g := fun q =>
    IsLocalSet.exists_isLocalSetMean hh₀ (hKlaw q).1 (hloc q)
  choose g hg using hg
  have hact : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ F q ω) :=
    fun q ω hω hq => activeDom_eq_inter hω hq (hc.1 ω hω).1 (hc.1 ω hω).2.1 (hc.1 ω hω).2.2.1 (hinj ω hω)
      (hgeo q ω hω hq)
  have h𝓦ℋ : ∀ q : ℝ≥0, ∀ s, MeasurableSet[𝓦] s → MeasurableSet[locPrefixSigma 𝓦 A γ q] s :=
    fun q s hs => le_sup_left (b := MeasurableSpace.generateFrom _) _ hs
  refine ⟨c, a, k, K, fun q => locPrefixSigma 𝓦 A γ q, g, hc, fun q => ?_, fun q => ?_⟩
  · obtain ⟨hKm, -, hhist, hgeoK⟩ := hKlaw q
    refine ⟨hKm, hpre q, hloc q, hhist, hg q, le_sup_right.trans le_sup_left, ?_, ?_⟩
    · exact measurable_compl_activeDom (h𝓦ℋ q _ hA) (measurableSet_live A γ q) hCo
        (fun z => h𝓦ℋ q _ (hCm z)) (hact q) hgeoK
    · refine Eventually.of_forall fun ω => ?_
      by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
      · rw [hact q ω hl.1 hl.2]
        obtain ⟨hfr, hF, hKC⟩ := hgeoK ω hl.1 hl.2
        refine ⟨fun z hz => ⟨hz.2.1, fun hzK => hz.2.2 (hKC ⟨hzK, hz.1⟩)⟩, fun z hz =>
          connectedComponentIn_subset_inter (hCo ω hl.1) hfr (fun x hx => ?_) hz⟩
        refine hF ⟨?_, hx.1⟩
        by_contra hxF
        exact hx.2 ⟨hx.1, hxF⟩
      · rw [activeDom_eq_empty hl]
        exact ⟨empty_subset _, fun z hz => hz.elim⟩
  · filter_upwards [hKmean q (g q) (hg q)] with ω hω hωA hq
    obtain ⟨v, hvc, hvrep, hvid⟩ := hω hωA hq
    have hE : (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) = C ω ∩ (H \ F q ω) := by
      rw [← activeDom_eq hωA hq]
      exact hact q ω hωA hq
    refine ⟨v, by rw [hE]; exact hvc, fun φ hφ => hvrep φ (by rw [← hE]; exact hφ), fun w hw => ?_⟩
    have hz : (c ω).2.1 w ∈ C ω ∩ (H \ F q ω) := by
      rw [← hE]
      exact mem_image_of_mem _ hw
    have h := hvid _ hz
    rwa [(hc.1 ω hωA).1.2.2 w hw.1] at h

end Assembly

end InteractingSLE.Sec7.PocketUnionPt
