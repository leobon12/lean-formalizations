/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideInputsGeometry
import InteractingSLE.Spec.Sec7.PocketStopWallsFinLeft

/-!
# Filled separation across the erasure fibre and the possible real corner

PROVE-STRIPSYS38. Reuse STRIPSYS41's R67 identity at T⁰(q): filling the pocket
exterior makes the left and right stops identical, so their added filled hull is
empty inside the pocket. This is separation across the erasure fibre; rational
references earlier than T⁰(q) still require the incident-boundary argument of BP1.

For both two-arc geometries every finite point of the closed pocket is in H or is
the incoming seed. Thus the real-corner problem reduces to that one seed, rather
than an arbitrary real point. Excluding its relative driving preimages still
requires the tracked-force-point boundary identification.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketUnionPt PocketStop PocketCoupling PocketTraversal Lemma71C PocketJordan PocketCoord
  PocketStopWallsFin PocketWordAssembly PocketSeedOpen

/-- Equality after filling the common exterior excludes every added hull point
inside the pocket. No separation of the extra hull outside the pocket is needed. -/
theorem pocket_increment_separated_of_filled_eq {C F G U : Set ℂ} (hFH : F ⊆ H)
    (he : extHullSet C G = extHullSet C F) : Disjoint (C ∩ (F \ G)) U := by
  rw [disjoint_left]
  rintro z ⟨hzC, hzF, hzG⟩ _
  have hz : z ∈ extHullSet C G := he.symm ▸ (show z ∈ extHullSet C F from
    ⟨hFH hzF, Or.inr hzF⟩)
  exact hz.2.elim (fun hn => hn hzC) hzG

/-- The filled increment from T⁰(q) to T(q) misses the pocket, hence every
pocket-side ball. This uses the proved GC2 transfer, not a range-to-hull inference. -/
theorem pocket_fibre_increment_separated {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψC : Ω → ℂ → ℂ} {ω : Ω}
    (hc : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (q : ℝ≥0) (U : Set ℂ) :
    Disjoint (cfPocket (R ω) (L ω) r ∩
      (stopHull R L r W η ψC q ω \ stopHull0 R L r W η ψC q ω)) U := by
  exact pocket_increment_separated_of_filled_eq (fun _ hz => hz.1)
    (extHullSet_stopHull0 hc q)

/-- R67's separation for the pocket opening at the flow seed. -/
theorem pocket_fibreInf_increment_separated {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ω : Ω}
    (hc : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (q : ℝ≥0) (U : Set ℂ) :
    Disjoint (cfPocket (R ω) (L ω) r ∩
      (stopHullInf R L r W η ψ q ω \ stopHull0Inf R L r W η ψ q ω)) U := by
  exact pocket_increment_separated_of_filled_eq (fun _ hz => hz.1)
    (extHullSet_stopHull0Inf hc q)

/-- The active complement used by the side-limit predicate is the exterior union
at the left stop. Its definition and all existing consumers remain unchanged. -/
theorem activeCompl_eq_stopHull0 {Ω : Type*} {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart}
    {R L : Ω → ℝ≥0 → ℂ} {r q : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    {ψ : Ω → ℂ → ℂ} {ω : Ω} (hω : ω ∈ A) (hq : (q : ℝ≥0∞) < capLife (γ ω))
    (hc : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c q ω = cfPocket (R ω) (L ω) r ∩ (H \ stopHull R L r W η ψ q ω)) :
    activeCompl A γ c q ω = extHullSet (cfPocket (R ω) (L ω) r) (stopHull0 R L r W η ψ q ω) := by
  rw [activeCompl_eq_liveExt hact, liveExt_of_live ⟨hω, hq⟩]
  exact (extHullSet_stopHull0 hc q).symm

/-- The active-complement identification for the pocket with junction at infinity. -/
theorem activeCompl_eq_stopHull0Inf {Ω : Type*} {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart}
    {R L : Ω → ℝ≥0 → ℂ} {r q : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    {ψ : Ω → ℂ → ℂ} {ω : Ω} (hω : ω ∈ A) (hq : (q : ℝ≥0∞) < capLife (γ ω))
    (hc : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c q ω = cfPocket (R ω) (L ω) r ∩ (H \ stopHullInf R L r W η ψ q ω)) :
    activeCompl A γ c q ω =
      extHullSet (cfPocket (R ω) (L ω) r) (stopHull0Inf R L r W η ψ q ω) := by
  rw [activeCompl_eq_liveExt hact, liveExt_of_live ⟨hω, hq⟩]
  exact (extHullSet_stopHull0Inf hc q).symm

/-- The closed bounded two-arc pocket lies in H except possibly at its seed. -/
theorem closure_cfPocket_subset_H_union_seed {C : Set ℂ} {α₁ α₂ : ℝ → ℂ}
    (hc : IsCfPocket C α₁ α₂) (hCH : C ⊆ H) : closure C ⊆ H ∪ {α₁ 1} := by
  rw [closure_eq_self_union_frontier, hc.frontier_eq]
  rintro z (hz | hz | hz)
  · exact Or.inl (hCH hz)
  · obtain ⟨v, hv, rfl⟩ := hz
    rcases hv.2.lt_or_eq with hv1 | hv1
    · exact Or.inl (hc.mem_H₁ v ⟨hv.1, hv1⟩)
    · exact Or.inr (by rw [hv1]; exact mem_singleton _)
  · obtain ⟨v, hv, rfl⟩ := hz
    rcases hv.2.lt_or_eq with hv1 | hv1
    · exact Or.inl (hc.mem_H₂ v ⟨hv.1, hv1⟩)
    · exact Or.inr (by rw [hv1, hc.seed]; exact mem_singleton _)

/-- The closed unbounded two-arc pocket has the same single possible real corner. -/
theorem closure_cfPocketInf_subset_H_union_seed {C : Set ℂ} {α₁ α₂ : ℝ → ℂ}
    (hc : IsCfPocketInf C α₁ α₂) : closure C ⊆ H ∪ {α₁ 0} := by
  rw [closure_eq_self_union_frontier, hc.frontier_eq]
  rintro z (hz | hz | hz)
  · exact Or.inl (hc.subset_H hz)
  · obtain ⟨v, hv, rfl⟩ := hz
    rcases (show (0 : ℝ) ≤ v from hv).eq_or_lt with hv0 | hv0
    · exact Or.inr (by rw [← hv0]; exact mem_singleton _)
    · exact Or.inl (hc.mem_H₁ v hv0)
  · obtain ⟨v, hv, rfl⟩ := hz
    rcases (show (0 : ℝ) ≤ v from hv).eq_or_lt with hv0 | hv0
    · exact Or.inr (by rw [← hv0, hc.seed]; exact mem_singleton _)
    · exact Or.inl (hc.mem_H₂ v hv0)

/-- Any finite relative inverse landing is in the closed incoming chart domain.
No boundary-extension hypothesis is needed once the finite limit is specified. -/
theorem finite_relative_landing_mem_closure {Ω : Type*} {c : Ω → Chart}
    {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {ω : Ω} (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hc : (c ω).IsConformal) {ξ : ℝ} {p : ℂ}
    (ht : Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) :
    p ∈ closure ((c ω).dom : Set ℂ) := by
  have hξcl : (ξ : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp)
  have : NeBot (𝓝[H] (ξ : ℂ)) := mem_closure_iff_nhdsWithin_neBot.1 hξcl
  apply isClosed_closure.mem_of_tendsto ht
  obtain ⟨W, hW, hW0, -, -, -, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  refine eventually_nhdsWithin_of_forall fun y hy => subset_closure ?_
  rw [hrel]
  exact hc.inv_mem_dom (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 q.coe_nonneg hy)

/-- Once the tracked force marks exclude the incoming seed, all other finite
relative landings are interior to H. The two preceding arc lemmas supply `hclosure`. -/
theorem relative_landing_mem_H_of_seed_exclusion {Ω : Type*} {c : Ω → Chart}
    {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {ω : Ω} (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hc : (c ω).IsConformal)
    {C : Set ℂ} (hdom : ((c ω).dom : Set ℂ) = C) {seed : ℂ}
    (hclosure : closure C ⊆ H ∪ {seed}) {ξ : ℝ} {p : ℂ}
    (ht : Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) (hseed : p ≠ seed) : p ∈ H := by
  have hp := finite_relative_landing_mem_closure hγ hq hc ht
  rw [hdom] at hp
  rcases hclosure hp with hpH | he
  · exact hpH
  · exact (hseed (mem_singleton_iff.1 he)).elim

end InteractingSLE.Sec7.PocketStopSide
