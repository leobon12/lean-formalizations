/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TaFill
import InteractingSLE.GFF.LocalSets.MarkovNesting
import InteractingSLE.Spec.Supplement.WalkUnionLaw
import InteractingSLE.Spec.Supplement.WalkPastLaw

/-!
# The filling of a marked local set is marked local

Packet PROVE-GW2-RELDET, ruling R113 (the core of `GW2SzLoc.SchedHullLocalStatement`: pieces of the joined chain may
enclose regions, so the explored HULL is the filling of the explored CURVE).

**`isHistoryAvoidanceLocal_fill`**. Let `S` be history-marked local for field-determined marks `ℋ`, with its avoidance
events marks, for a zero-boundary GFF `h`. Let `K` fill `S` at every sample (`IsFilling K S`), with `ℍ \ S` open and
a half-plane `{Im > R}` outside `K`. Then `K` is history-marked local for the same marks, and its avoidance events are
marks.

Proof. By `GW2TaFill.disjoint_fill_iff`, the avoidance event of `K` for an open `U ⊆ ℍ` is a countable combination of
avoidance events of `S` for the open sets `U ∪ T`, `T` a test region (`fillTube`). Marked by any `F ∈ ℋ`, each such
event lies in the complementary projection of `U ∪ T` (`WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal`). That
projection is, up to null sets, a function of the complementary projection of `U` (Markov nesting,
`LocalSets.exists_measurable_markovCompl_comp`). The criterion `WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma`
concludes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets WholeField Coupling

/-- The open set `U ∪ T` of a test region `T`. -/
def unionOpens (U : Opens ℂ) (F : Finset (ℚ × ℚ × ℚ)) (n : ℕ) (z : ℂ) : Opens ℂ :=
  ⟨(U : Set ℂ) ∪ fillTube F n z, U.isOpen.union (isOpen_fillTube F n z)⟩

section Loc

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
theorem aeSigma_aeSigma_le (m : MeasurableSpace Ω) : aeSigma (aeSigma m P) P ≤ aeSigma m P := by
  rintro s ⟨t, ⟨t', ht', htt'⟩, hst⟩
  exact ⟨t', ht', hst.trans htt'⟩

/-- **A marked avoidance event of a larger open set is an event of the smaller set's complementary projection.** -/
theorem mem_complSigma_of_le (hhm : Measurable h) (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {S : Ω → Set ℂ} (hloc : IsHistoryAvoidanceLocal ℋ S h P)
    (hSm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (S ω) U})
    (hℋd : ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P) {U V : Opens ℂ} (hUV : U ≤ V)
    (hVH : (V : Set ℂ) ⊆ H) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) {F : Set Ω}
    (hF : MeasurableSet[ℋ] F) :
    MeasurableSet[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P]
      ({ω | Disjoint (S ω) V} ∩ F) := by
  obtain ⟨GV, hGVm, hGV⟩ := exists_markovMap V hVH
  have hdV := hGV hh
  have h1 := WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc hVH hGVm hdV hF
    (hℋd _ ((hSm V hVH).inter hF))
  have hVle : V ≤ upperHalfPlaneOpens := fun x hx => hVH hx
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_measurable_markovCompl_comp hUV hVle hhm hd hdV
  have h2 := WalkLaw.comap_le_aeSigma_of_ae_eq_comp (P := P) hΨ hΨe
  exact aeSigma_aeSigma_le _ _ (WalkLaw.aeSigma_mono h2 _ h1)

/-- **The filling of a marked local set is marked local** (for field-determined marks). -/
theorem isHistoryAvoidanceLocal_fill (hhm : Measurable h) (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {S K : Ω → Set ℂ} (hloc : IsHistoryAvoidanceLocal ℋ S h P)
    (hSm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (S ω) U})
    (hℋd : ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P) (hfill : ∀ ω, IsFilling (K ω) (S ω))
    (hSo : ∀ ω, IsOpen (H \ S ω)) (hR : ∀ ω, ∃ R : ℝ, {w : ℂ | R < w.im} ⊆ H \ K ω) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (K ω) U}) ∧
      IsHistoryAvoidanceLocal ℋ K h P := by
  -- the avoidance events of `K` through countably many avoidance events of `S`
  have hev : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → {ω | Disjoint (K ω) U} = {ω | Disjoint (S ω) U} ∩
      ⋂ i, ⋂ (_ : denseSeq ℂ i ∈ (U : Set ℂ)), ⋃ F : Finset (ℚ × ℚ × ℚ), ⋃ n : ℕ,
        ⋃ (_ : IsFillTube F n (denseSeq ℂ i)), {ω | Disjoint (S ω) (unionOpens U F n (denseSeq ℂ i))} := by
    intro U hUH
    ext ω
    obtain ⟨R, hRω⟩ := hR ω
    have h := disjoint_fill_iff (hfill ω) (hSo ω) hRω U.isOpen hUH
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, exists_prop]
    exact h
  have hVH : ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ H → ∀ {F : Finset (ℚ × ℚ × ℚ)} {n : ℕ} {z : ℂ}, IsFillTube F n z →
      ((unionOpens U F n z : Opens ℂ) : Set ℂ) ⊆ H := fun U hUH _ n z hT =>
    union_subset hUH (fillTube_subset_H hT.1 n z)
  have hKm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (K ω) U} := by
    intro U hUH
    rw [hev U hUH]
    exact (hSm U hUH).inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun hT =>
        hSm _ (hVH U hUH hT))
  refine ⟨hKm, WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF => ?_⟩
  have e : {ω | Disjoint (K ω) U} ∩ F = ({ω | Disjoint (S ω) U} ∩ F) ∩
      ⋂ i, ⋂ (_ : denseSeq ℂ i ∈ (U : Set ℂ)), ⋃ F' : Finset (ℚ × ℚ × ℚ), ⋃ n : ℕ,
        ⋃ (_ : IsFillTube F' n (denseSeq ℂ i)),
          ({ω | Disjoint (S ω) (unionOpens U F' n (denseSeq ℂ i))} ∩ F) := by
    rw [hev U hUH]
    ext ω
    simp only [mem_inter_iff, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨⟨h1, h2⟩, hωF⟩
      refine ⟨⟨h1, hωF⟩, fun i hi => ?_⟩
      obtain ⟨F', n, hT, hω⟩ := h2 i hi
      exact ⟨F', n, hT, hω, hωF⟩
    · rintro ⟨⟨h1, hωF⟩, h2⟩
      refine ⟨⟨h1, fun i hi => ?_⟩, hωF⟩
      obtain ⟨F', n, hT, hω, -⟩ := h2 i hi
      exact ⟨F', n, hT, hω⟩
  rw [e]
  refine MeasurableSet.inter (mem_complSigma_of_le hhm hh hloc hSm hℋd le_rfl hUH hd hF)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun F' =>
      MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun hT => ?_)
  exact mem_complSigma_of_le hhm hh hloc hSm hℋd (fun x hx => Or.inl hx) (hVH U hUH hT) hd hF

end Loc

end InteractingSLE.Theorem14.GW2Rd
