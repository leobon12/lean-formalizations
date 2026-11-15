/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkUnionLaw
import InteractingSLE.Spec.Supplement.GB6LineL4
import InteractingSLE.Spec.Supplement.BW1VerRead

/-!
# Marked locality for determined sets: generic tools for terminal hulls

Packet PROVE-BW1-SAFELAW. For a field `h` and a Markov decomposition `G` along an open `U ⊆ ℍ`, the complementary
σ-algebra `complSigma P G h` is the completion of `σ(h − G h)`. For sets and marks determined by the field the
history-marked avoidance criterion says: marked avoidance events are almost surely events of `σ(h − G h)`
(`WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma`). This file adds:

* **`mem_complSigma_of_isAvoidanceLocal`**: the unmarked form (`F = Ω`);
* **`inter_mem_complSigma_of_subset`** (the *pull-out step*): if a determined event `E` lies in `complSigma` and,
  almost surely, inside the avoidance event of a set `A` that is marked local for `𝒦`, then `E ∩ F ∈ complSigma` for
  every determined mark `F ∈ 𝒦` — conditionally on `h` the indicator of `E` comes out of the conditional probability of
  `{A ∩ U = ∅} ∩ F`, which is a function of `h − G h`. This is how a TERMINAL hull (the hull at a lifetime, not the
  limit of the hulls at the stops before it) inherits the marks of the stops before it;
* `nullSets_le_aeSigma`; the record hull at the record's own time is a measurable function of the record
  (**`measurable_invHull_rec`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Theorem14.BW1Safe

open LocalSets Theorem14.WalkLaw

section Gen

variable {Ω : Type*} {𝒦 m₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- The null sets are almost surely events of every σ-algebra. -/
theorem nullSets_le_aeSigma : Ito.nullSets P ≤ aeSigma m₀ P := by
  refine MeasurableSpace.generateFrom_le fun s hs => ⟨∅, @MeasurableSet.empty _ m₀, ?_⟩
  exact ae_eq_empty.2 hs.2

/-- A set almost surely equal to an event of `aeSigma m` is an event of `aeSigma m`. -/
theorem measurableSet_aeSigma_of_ae_eq {A B : Set Ω}
    (hB : MeasurableSet[aeSigma m₀ P] B) (hAB : A =ᵐ[P] B) : MeasurableSet[aeSigma m₀ P] A := by
  obtain ⟨B', hB', he⟩ := hB
  exact ⟨B', hB', hAB.trans he⟩

/-- A function almost surely equal to an `aeSigma m`-measurable one is `aeSigma m`-measurable. -/
theorem measurable_aeSigma_of_ae_eq'' {β : Type*} [MeasurableSpace β] {f g : Ω → β}
    (hg : Measurable[aeSigma m₀ P] g) (hfg : f =ᵐ[P] g) : Measurable[aeSigma m₀ P] f := fun S hS =>
  measurableSet_aeSigma_of_ae_eq (hg hS) (hfg.mono fun ω hω => by
    change (f ω ∈ S) = (g ω ∈ S)
    rw [hω])

variable [IsFiniteMeasure P]

/-- **The unmarked criterion for a determined avoidance event**: it is almost surely an event of the complementary
projection. -/
theorem mem_complSigma_of_isAvoidanceLocal (hhm : Measurable h) {A : Ω → Set ℂ}
    (hloc : IsAvoidanceLocal A h P) {U : Opens ℂ}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (hE : MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] {ω | Disjoint (A ω) U}) :
    MeasurableSet[complSigma P G h] {ω | Disjoint (A ω) U} := by
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd
  obtain ⟨K, hK, hEK⟩ := hE
  have hle : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  have hKm : MeasurableSet K := hle K hK
  have h1 : P⟦{ω | Disjoint (A ω) U} | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P]
      K.indicator fun _ => (1 : ℝ) := by
    refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hEK)).trans ?_
    rw [condExp_of_stronglyMeasurable hle ((measurable_const.indicator hK).stronglyMeasurable)
      ((integrable_const (1 : ℝ)).indicator hKm)]
  have h2 : (K.indicator fun _ => (1 : ℝ)) =ᵐ[P] fun ω => g (markovCompl G (h ω)) := h1.symm.trans hge
  refine ⟨(fun ω => markovCompl G (h ω)) ⁻¹' (g ⁻¹' {1}), ⟨g ⁻¹' {1}, hg (measurableSet_singleton 1), rfl⟩,
    hEK.trans ?_⟩
  filter_upwards [h2] with ω hω
  simp only [mem_preimage, mem_singleton_iff, ← hω]
  by_cases hωK : ω ∈ K
  · simp [hωK]
  · simp [hωK]

/-- **The pull-out step.** Let `A` be marked local for `𝒦`, `E` a determined event of the complementary projection
contained almost surely in the avoidance event `{A ∩ U = ∅}`, and `F ∈ 𝒦` a determined mark. Then `E ∩ F` is almost
surely an event of the complementary projection: conditionally on `h`, `1_E` comes out of the conditional
probability of `{A ∩ U = ∅} ∩ F`, a function of `h − G h`, and `1_{E ∩ F}` is its own conditional expectation. -/
theorem inter_mem_complSigma_of_subset (hhm : Measurable h) {A : Ω → Set ℂ}
    (hloc : WholeField.IsHistoryAvoidanceLocal 𝒦 A h P) {U : Opens ℂ}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (hXm : MeasurableSet {ω | Disjoint (A ω) U}) {E : Set Ω}
    (hEd : MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] E)
    (hEc : MeasurableSet[complSigma P G h] E) (hEsub : ∀ᵐ ω ∂P, ω ∈ E → Disjoint (A ω) U) {F : Set Ω}
    (hF : MeasurableSet[𝒦] F) (hFm : MeasurableSet F)
    (hFd : MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] F) :
    MeasurableSet[complSigma P G h] (E ∩ F) := by
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd F hF
  set X : Set Ω := {ω | Disjoint (A ω) U} with hX
  obtain ⟨K, hK, hEK⟩ := hEd
  obtain ⟨K', ⟨B', hB', rfl⟩, hEK'⟩ := hEc
  obtain ⟨KF, hKF, hFKF⟩ := hFd
  have hle : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  have hKm : MeasurableSet K := hle K hK
  have hKFm : MeasurableSet KF := hle KF hKF
  -- `E ∩ F` is almost surely `K ∩ (X ∩ F)`
  have hEF : (E ∩ F : Set Ω) =ᵐ[P] (K ∩ (X ∩ F) : Set Ω) := by
    filter_upwards [hEK, hEsub] with ω hω hsub
    have hω' : (ω ∈ E) = (ω ∈ K) := hω
    simp only [mem_inter_iff, ← hω']
    exact propext ⟨fun h1 => ⟨h1.1, hsub h1.1, h1.2⟩, fun h1 => ⟨h1.1, h1.2.2⟩⟩
  -- the conditional probability of `E ∩ F` given `h`
  have hind : ((K ∩ (X ∩ F)).indicator fun _ => (1 : ℝ)) = K.indicator ((X ∩ F).indicator fun _ => (1 : ℝ)) := by
    rw [indicator_indicator]
  have h1 : P⟦E ∩ F | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P]
      K.indicator (fun ω => g (markovCompl G (h ω))) := by
    refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hEF)).trans ?_
    rw [hind]
    refine (condExp_indicator ((integrable_const (1 : ℝ)).indicator (hXm.inter hFm)) hK).trans ?_
    filter_upwards [hge] with ω hω
    by_cases hωK : ω ∈ K
    · simp only [indicator_of_mem hωK, hω]
    · simp only [indicator_of_notMem hωK]
  -- and it is the indicator of `E ∩ F` itself
  have h2 : P⟦E ∩ F | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P] (K ∩ KF).indicator fun _ => (1 : ℝ) := by
    refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (hEK.inter hFKF))).trans ?_
    rw [condExp_of_stronglyMeasurable hle ((measurable_const.indicator (hK.inter hKF)).stronglyMeasurable)
      ((integrable_const (1 : ℝ)).indicator (hKm.inter hKFm))]
  have h3 : ((K ∩ KF).indicator fun _ => (1 : ℝ)) =ᵐ[P]
      ((fun ω => markovCompl G (h ω)) ⁻¹' B').indicator (fun ω => g (markovCompl G (h ω))) := by
    filter_upwards [h2.symm.trans h1, hEK, hEK'] with ω hω he he'
    rw [hω]
    have e : (ω ∈ K) = (ω ∈ (fun ω => markovCompl G (h ω)) ⁻¹' B') := (he.symm.trans he' : _)
    by_cases hωK : ω ∈ K
    · rw [indicator_of_mem hωK, indicator_of_mem (e ▸ hωK)]
    · rw [indicator_of_notMem hωK, indicator_of_notMem (e ▸ hωK)]
  refine ⟨(fun ω => markovCompl G (h ω)) ⁻¹' (B' ∩ g ⁻¹' {1}),
    ⟨B' ∩ g ⁻¹' {1}, hB'.inter (hg (measurableSet_singleton 1)), rfl⟩, ?_⟩
  filter_upwards [hEK.inter hFKF, h3] with ω he hω
  rw [he]
  change (ω ∈ K ∩ KF) = (markovCompl G (h ω) ∈ B' ∩ g ⁻¹' {1})
  by_cases hωK : ω ∈ K ∩ KF
  · have h4 := hω
    rw [indicator_of_mem hωK] at h4
    by_cases hB : markovCompl G (h ω) ∈ B'
    · have h5 : g (markovCompl G (h ω)) = 1 := by
        rw [indicator_of_mem (show ω ∈ (fun ω => markovCompl G (h ω)) ⁻¹' B' from hB)] at h4
        exact h4.symm
      simp only [hωK, mem_inter_iff, hB, mem_preimage, mem_singleton_iff, h5, and_self]
    · rw [indicator_of_notMem (show ω ∉ (fun ω => markovCompl G (h ω)) ⁻¹' B' from hB)] at h4
      exact absurd h4 one_ne_zero
  · have h4 := hω
    rw [indicator_of_notMem hωK] at h4
    simp only [hωK, mem_inter_iff, mem_preimage, mem_singleton_iff]
    refine propext ⟨False.elim, ?_⟩
    rintro ⟨hB, h5⟩
    rw [indicator_of_mem (show ω ∈ (fun ω => markovCompl G (h ω)) ⁻¹' B' from hB), h5] at h4
    exact one_ne_zero h4.symm

end Gen

/-! ### The record hull at the record's own time -/

section RecHull

open Exist.StagedLaw BW1Ver

/-- **The avoidance events of the hull of the record driver at the record's own time are measurable.** -/
theorem measurableSet_disjoint_fwdHull_rec {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet {r : RecData | Disjoint (fwdHull (rdrv r) (recS r)) U} := by
  have e : {r : RecData | Disjoint (fwdHull (rdrv r) (recS r)) U} =
      ⋂ p : ℚ × ℚ × ℚ, ⋂ (_ : 0 < p.2.2),
        ⋂ (_ : closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U),
          {r : RecData | Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
            (fwdHull (rdrv r) (recS r))} := by
    ext r
    simp only [mem_ofPred_eq, mem_iInter]
    exact Supp8.GB6LineL.disjoint_iff_forall_posRatDisc hU
  rw [e]
  refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  have h := Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand (m := inferInstance)
    (B := fun t (r : RecData) => rdrv r (t : ℝ)) (fun r => (continuous_rdrv r).comp NNReal.continuous_coe)
    (fun t => measurable_rdrv_apply (t : ℝ)) (q := fun r => (recS r : ℝ))
    (measurable_coe_nnreal_real.comp measurable_recS) (fun r => (recS r).coe_nonneg)
    (isClosed_closedBall (x := (p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (ε := (p.2.2 : ℝ)))
  rw [Supp8.GB6LineL.drive_rdrv] at h
  exact h

/-- **The hull of the record driver at the record's own time is a hitting-measurable function of the record.** -/
theorem measurable_fwdHull_rec :
    Measurable[inferInstance, hittingSigma] fun r : RecData => fwdHull (rdrv r) (recS r) := by
  refine @measurable_generateFrom _ _ inferInstance _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : (fun r : RecData => fwdHull (rdrv r) (recS r)) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      {r : RecData | Disjoint (fwdHull (rdrv r) (recS r)) U}ᶜ := by
    ext r
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
  rw [e]
  exact (measurableSet_disjoint_fwdHull_rec hU).compl

/-- **The inverted hull `−1/K` of the record driver at the record's own time is a hitting-measurable function of the
record.** -/
theorem measurable_invHull_rec :
    Measurable[inferInstance, hittingSigma] fun r : RecData => Supp8.Q3Rel.invHull (rdrv r) (recS r) :=
  WangWu.measurable_image_negInv.comp measurable_fwdHull_rec

end RecHull

end InteractingSLE.Theorem14.BW1Safe
