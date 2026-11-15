import InteractingSLE.Foundations.Loewner.HullBasic
import InteractingSLE.Frozen.Spec.IsFilling

/-!
# Bridge between `fillH` and the frozen `IsFilling`

Design `planning/INFRA-GEO.md` §3 ("`fillH_eq_iff_isFilling`: ARCH-1's `IsFilling K A` ⇔
`K = fillH A` for bounded `A`"), packet GEO-HCAP-A. A separate module because the frozen
`InteractingSLE.Frozen.Spec.IsFilling` has heavy imports.

**Design correction.** The bridge needs `A` closed (`IsFilling` uses `ℍ \ A`, `fillH` uses
`ℍ \ closure A`: for an open disc `A ⊆ ℍ`, `IsFilling A A` holds but `fillH A` is the closed disc)
and `K ⊆ ℍ` (`IsFilling K A` only constrains `ℍ \ K`). The general form is
`isFilling_iff_inter_H_eq_fillH`: `IsFilling K A ↔ K ∩ ℍ = fillH A` for bounded closed `A`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H)

namespace InteractingSLE

/-- **`IsFilling` versus `fillH`**: for a bounded closed `A`, `K` is the filling of `A` in the
sense of the frozen `IsFilling` iff `K ∩ ℍ = fillH A`. -/
theorem isFilling_iff_inter_H_eq_fillH {K A : Set ℂ} (hA : Bornology.IsBounded A)
    (hAc : IsClosed A) : IsFilling K A ↔ K ∩ H = fillH A := by
  obtain ⟨R, hR, hAR⟩ := exists_closure_subset_ball hA
  have hU := H_diff_fillH hR hAR
  rw [hAc.closure_eq] at hU hAR
  -- `K ∩ ℍ = fillH A ↔ ℍ \ K = ℍ \ fillH A`
  have hiff : K ∩ H = fillH A ↔ H \ K = H \ fillH A := by
    constructor
    · intro h
      rw [← h]; ext z; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    · intro h
      ext z
      constructor
      · rintro ⟨hzK, hzH⟩
        by_contra hzf
        have : z ∈ H \ fillH A := ⟨hzH, hzf⟩
        rw [← h] at this
        exact this.2 hzK
      · intro hzf
        refine ⟨?_, fillH_subset_H A hzf⟩
        by_contra hzK
        have : z ∈ H \ K := ⟨fillH_subset_H A hzf, hzK⟩
        rw [h] at this
        exact this.2 hzf
  rw [hiff, hU]
  constructor
  · rintro ⟨⟨z, hz, hcomp⟩, hunb⟩
    rw [← hcomp] at hunb ⊢
    exact connectedComponentIn_eq_of_not_isBounded hR hAR hunb
  · intro h
    have hz₀ : ((R + 1 : ℝ) : ℂ) * I ∈ H \ K := by
      rw [h]
      exact setOf_lt_im_subset_connectedComponentIn hR hAR
        (show R < (((R + 1 : ℝ) : ℂ) * I).im by simp)
    refine ⟨⟨_, hz₀, h.symm⟩, ?_⟩
    rw [h]
    exact not_isBounded_connectedComponentIn_of_lt hR hAR

/-- **Bridge to the frozen `IsFilling`** (corrected form of the design's planned
`fillH_eq_iff_isFilling`, which also needs `A` closed and `K ⊆ ℍ`): for a bounded closed `A` and
`K ⊆ ℍ`, `IsFilling K A ↔ K = fillH A`. -/
theorem fillH_eq_iff_isFilling_of_isClosed {K A : Set ℂ} (hA : Bornology.IsBounded A)
    (hAc : IsClosed A) (hK : K ⊆ H) : IsFilling K A ↔ K = fillH A := by
  rw [isFilling_iff_inter_H_eq_fillH hA hAc, inter_eq_left.2 hK]

/-- The filling of a compact set (for instance the range `γ([0, t])` of a curve) satisfies the
frozen `IsFilling`. -/
theorem isFilling_fillH {A : Set ℂ} (hA : IsCompact A) : IsFilling (fillH A) A :=
  (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed (fillH_subset_H A)).2 rfl

end InteractingSLE
