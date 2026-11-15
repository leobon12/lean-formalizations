/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetClosedInterior

/-!
# G8: the real boundary is the only possible common closure

Packet PROVE-G8-DET. Relative closedness rules out common closure points
in `H`. Compactness then makes real-boundary exclusion equivalent to a
strictly positive Euclidean gap between the two full closures.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.RLC.G8Det.Closed

/-- Disjoint HP hulls can have common closure points only on the real axis. -/
theorem im_eq_zero_of_mem_closures {A K : Set ℂ} (hA : IsHPHull A) (hK : IsHPHull K)
    (hd : Disjoint A K) {z : ℂ} (hzA : z ∈ closure A) (hzK : z ∈ closure K) : z.im = 0 := by
  have hbar : closure A ⊆ Hbar := closure_minimal
    (fun z hz => (show 0 < z.im from hA.1 hz).le) (isClosed_le continuous_const continuous_im)
  have him : 0 ≤ z.im := hbar hzA
  have hn : ¬ 0 < z.im := fun h => Set.disjoint_left.1 hd
    (hA.mem_of_mem_closure h hzA) (hK.mem_of_mem_closure h hzK)
  exact le_antisymm (not_lt.1 hn) him

/-- Real-boundary exclusion completes full closed-hull disjointness. -/
theorem disjoint_closures_of_real {A K : Set ℂ} (hA : IsHPHull A) (hK : IsHPHull K)
    (hd : Disjoint A K)
    (hr : ∀ x : ℝ, (x : ℂ) ∈ closure A → (x : ℂ) ∉ closure K) :
    Disjoint (closure A) (closure K) := by
  refine Set.disjoint_left.2 fun z hzA hzK => ?_
  have he := Restart.ofReal_re_eq (im_eq_zero_of_mem_closures hA hK hd hzA hzK)
  exact hr z.re (he ▸ hzA) (he ▸ hzK)

/-- The full closures of two disjoint HP hulls are compact and separated
by a positive distance. The empty-hull cases are included. -/
theorem exists_positive_gap {A K : Set ℂ} (hA : IsHPHull A) (hK : IsHPHull K)
    (hd : Disjoint (closure A) (closure K)) :
    ∃ δ > 0, ∀ x ∈ closure A, ∀ y ∈ closure K, δ ≤ dist x y := by
  obtain ⟨δ, hδ, hdist⟩ := Metric.exists_pos_forall_lt_edist hA.2.1.isCompact_closure
    hK.2.1.isCompact_closure.isClosed hd
  refine ⟨(δ : ℝ), NNReal.coe_pos.2 hδ, fun x hx y hy => ?_⟩
  have hle : δ ≤ nndist x y := ENNReal.coe_le_coe.1
    (by simpa only [edist_nndist] using (hdist x hx y hy).le)
  exact_mod_cast hle

/-- For disjoint HP hulls, excluding only real common closure points
already gives a positive distance between the entire closures. -/
theorem exists_positive_gap_of_real {A K : Set ℂ} (hA : IsHPHull A) (hK : IsHPHull K)
    (hd : Disjoint A K)
    (hr : ∀ x : ℝ, (x : ℂ) ∈ closure A → (x : ℂ) ∉ closure K) :
    ∃ δ > 0, ∀ x ∈ closure A, ∀ y ∈ closure K, δ ≤ dist x y :=
  exists_positive_gap hA hK (disjoint_closures_of_real hA hK hd hr)

end InteractingSLE.RLC.G8Det.Closed
