/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockTrace

/-!
# Capacity of the mapped continuation: additivity and unbounded clocks

Packet PROVE-RESTART-CPL5. With `K = η₁([0, s₀]) ∪ η₂([0, t₀])`, `P_t = η₁([0, s₀ + t]) ∪ η₂([0, t₀])` and the
chart `φ = g − x₀` (`g` the mapping-out function of `fill K`), the forward image of the newly filled part is the
filling of the chart path (`fwd_image_fillH_diff_eq`):

  `φ(fill P_t \ fill K) = fill Γ([0, t])`,

so by the composition rule `hcap(fill P_t) = hcap(fill Γ([0, t])) + hcap(fill K)` (`hcapSet_fillH_prefixSet_eq`).
Since `fill P_t ⊇ fill η₁([0, s₀ + t])`, whose capacity is `2 (s₀ + t)` for a generating trace, the relative capacity
clock is unbounded when the original lifetime is infinite (`chartClock_ge`): (W8.1)'s clock maps the infinite
continuation onto an infinite capacity interval.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} {Γ : ℝ≥0 → ℂ}

/-- A path from a point of `{Im ≤ 0}` together with the lower half-plane is preconnected. -/
theorem isPreconnected_image_union_lowerHalf {f : ℝ≥0 → ℂ} {a : ℝ≥0} (hf : ContinuousOn f (Icc 0 a))
    (h0 : (f 0).im ≤ 0) : IsPreconnected (f '' Icc 0 a ∪ {z : ℂ | z.im ≤ 0}) :=
  (isPreconnected_Icc.image _ hf).union (f 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩ h0
    (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected

theorem isHPHull_fillH_image {f : ℝ≥0 → ℂ} {a : ℝ≥0} (hf : ContinuousOn f (Icc 0 a)) (h0 : (f 0).im ≤ 0) :
    IsHPHull (fillH (f '' Icc 0 a)) :=
  isHPHull_fillH_of_isPreconnected (isCompact_Icc.image_of_continuousOn hf).isBounded
    (isPreconnected_image_union_lowerHalf hf h0)

theorem isHPHull_fillH_prefixSet {u : ℝ≥0} (hc₁ : ContinuousOn η₁ (Icc 0 u)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (h0₁ : (η₁ 0).im = 0) (h0₂ : (η₂ 0).im = 0) : IsHPHull (fillH (prefixSet η₁ u η₂ t₀)) :=
  isHPHull_fillH_of_isPreconnected (isCompact_prefixSet hc₁ hc₂).isBounded
    (isPreconnected_union_lowerHalf (isPreconnected_image_union_lowerHalf hc₁ h0₁.le)
      (isPreconnected_image_union_lowerHalf hc₂ h0₂.le))

/-- **The hull identity**: the forward image of the newly filled part `fill P_t \ fill K` is `fill Γ([0, t])`. -/
theorem fwd_image_fillH_diff_eq (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift)
    (hK : IsClosed (prefixSet η₁ s₀ η₂ t₀)) {t : ℝ≥0}
    (hc₁ : ContinuousOn η₁ (Icc 0 (s₀ + t))) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓψ : ∀ r ∈ Icc 0 t, ψ (Γ r) = η₁ (s₀ + r)) :
    φ '' (fillH (prefixSet η₁ (s₀ + t) η₂ t₀) \ fillH (prefixSet η₁ s₀ η₂ t₀)) = fillH (Γ '' Icc 0 t) := by
  set P := prefixSet η₁ (s₀ + t) η₂ t₀ with hP
  set D := activeDomain η₁ s₀ η₂ t₀ with hD
  have hDeq : D = H \ fillH (prefixSet η₁ s₀ η₂ t₀) := activeDomain_eq hK
  have hsub : H \ fillH P ⊆ D := by
    rw [hDeq]
    exact sdiff_subset_sdiff_right (fillH_mono (prefixSet_mono_left le_self_add))
  -- the forward image of the relative domain is the unbounded domain of `Γ([0, t])`
  have himg : φ '' (H \ fillH P) = H \ fillH (Γ '' Icc 0 t) := by
    refine Subset.antisymm (fwd_image_relDomain_subset hC hK hc₁ hc₂ hΓc hΓψ) fun w hw => ?_
    exact ⟨ψ w, inv_image_subset_relDomain hC hK hc₁ hc₂ hΓc hΓψ ⟨w, hw, rfl⟩, hC.2.2.1 w hw.1⟩
  have hdiff : fillH P \ fillH (prefixSet η₁ s₀ η₂ t₀) = D \ (H \ fillH P) := by
    rw [hDeq]
    ext z
    constructor
    · rintro ⟨hzP, hzK⟩
      exact ⟨⟨fillH_subset_H _ hzP, hzK⟩, fun h => h.2 hzP⟩
    · rintro ⟨⟨hzH, hzK⟩, hz⟩
      exact ⟨by_contra fun h => hz ⟨hzH, h⟩, hzK⟩
  rw [hdiff, image_sdiff_of_injOn hC.1.1.injOn hsub, hC.1.1.image_eq, himg]
  ext z
  exact ⟨fun h => by_contra fun h' => h.2 ⟨h.1, h'⟩, fun h => ⟨fillH_subset_H _ h, fun h' => h'.2 h⟩⟩

/-- **Additivity of the relative capacity** (composition rule): for the hydrodynamic chart `φ = g − x₀`,
`hcap(fill P_t) = hcap(fill Γ([0, t])) + hcap(fill K)`. -/
theorem hcapSet_fillH_prefixSet_eq (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {g : ℂ → ℂ} {x₀ : ℂ}
    (hg : IsMapOut (fillH (prefixSet η₁ s₀ η₂ t₀)) g) (hφ : ∀ z, φ z = g z - x₀) (hx₀ : x₀.im = 0)
    (hK : IsClosed (prefixSet η₁ s₀ η₂ t₀)) {t : ℝ≥0}
    (hc₁ : ContinuousOn η₁ (Icc 0 (s₀ + t))) (hc₂ : ContinuousOn η₂ (Icc 0 t₀)) (h0₁ : (η₁ 0).im = 0)
    (h0₂ : (η₂ 0).im = 0) (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓ0 : (Γ 0).im ≤ 0)
    (hΓψ : ∀ r ∈ Icc 0 t, ψ (Γ r) = η₁ (s₀ + r)) :
    ConformalImage.hcapSet (fillH (prefixSet η₁ (s₀ + t) η₂ t₀)) =
      ConformalImage.hcapSet (fillH (Γ '' Icc 0 t)) +
        ConformalImage.hcapSet (fillH (prefixSet η₁ s₀ η₂ t₀)) := by
  have hcs : ContinuousOn η₁ (Icc 0 s₀) := hc₁.mono (Icc_subset_Icc_right le_self_add)
  have hA := isHPHull_fillH_prefixSet hcs hc₂ h0₁ h0₂
  have hB := isHPHull_fillH_prefixSet hc₁ hc₂ h0₁ h0₂
  have hAB : fillH (prefixSet η₁ s₀ η₂ t₀) ⊆ fillH (prefixSet η₁ (s₀ + t) η₂ t₀) :=
    fillH_mono (prefixSet_mono_left le_self_add)
  have hΓ := isHPHull_fillH_image hΓc hΓ0
  have hadd := HPHull.hcap_eq_add (A := ⟨_, hA⟩) (B := ⟨_, hB⟩) hAB hg
  -- `g(fill P \ fill K)` is the translate by `x₀` of `fill Γ([0, t])`
  have himg : g '' (fillH (prefixSet η₁ (s₀ + t) η₂ t₀) \ fillH (prefixSet η₁ s₀ η₂ t₀)) =
      affHomeo 1 one_pos x₀.re '' fillH (Γ '' Icc 0 t) := by
    rw [← fwd_image_fillH_diff_eq hC hK hc₁ hc₂ hΓc hΓψ, image_image, coe_affHomeo]
    refine image_congr fun z _ => ?_
    have hx : (x₀.re : ℂ) = x₀ := Complex.ext (by simp) (by simp [hx₀])
    beta_reduce
    rw [hφ, ofReal_one, one_mul, hx, sub_add_cancel]
  have htr := HPHull.hcap_affHomeo (x := x₀.re) ⟨_, hΓ⟩ one_pos
  rw [ConformalImage.hcapSet_eq hB, ConformalImage.hcapSet_eq hΓ, ConformalImage.hcapSet_eq hA, hadd]
  congr 1
  exact (HPHull.hcap_congr (B := ⟨_, hΓ.image_affHomeo one_pos⟩) himg).trans (htr.trans (by ring))

/-! ### Unbounded clocks -/

section Trace

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} {x : ℝ}

/-- The filling of a prefix of a generating trace seeded at `x` has capacity `2 s`. -/
theorem IsGeneratingTrace.hcapSet_fillH_add (hη : IsGeneratingTrace w T fun t => η t - x)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T) :
    ConformalImage.hcapSet (fillH (η '' Icc 0 s)) = 2 * s := by
  obtain ⟨t₂, hst₂, ht₂T⟩ := exists_real_btwn_of_lt hs
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg s).trans hst₂.le
  have hL := hη.isLoewnerTraceLT ht₂T
  have hWc := continuous_frozenDrive_of_lt hw ht₂T
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have hI : (fun r : ℝ => (fun t => η t - (x : ℂ)) r.toNNReal) '' Icc 0 (s : ℝ) =
      (fun t => η t - (x : ℂ)) '' Icc 0 s := by
    have := image_toNNReal_Icc (fun t => η t - (x : ℂ)) (NNReal.coe_nonneg s)
    rwa [Real.toNNReal_coe] at this
  have hK : QuantumZipper.fwdHull (frozenDrive w t₂) s = fillH ((fun t => η t - (x : ℂ)) '' Icc 0 s) :=
    (hL.2.2 s (NNReal.coe_nonneg s) hst₂).trans (congrArg fillH hI)
  have hF := isHPHull_fwdHull hWc (NNReal.coe_nonneg s)
  have hcap := hcap_fwdHull hWc hW0 (NNReal.coe_nonneg s)
  have heq : fillH (η '' Icc 0 s) = affHomeo 1 one_pos x '' QuantumZipper.fwdHull (frozenDrive w t₂) s := by
    rw [hK, ← fillH_image_affHomeo, coe_affHomeo]
    congr 1
    rw [image_image]
    exact image_congr fun r _ => by simp
  have hH : IsHPHull (fillH (η '' Icc 0 s)) := heq ▸ hF.image_affHomeo one_pos
  rw [ConformalImage.hcapSet_eq hH]
  have htr := HPHull.hcap_affHomeo (x := x) ⟨_, hF⟩ one_pos
  rw [hcap, one_pow, one_mul] at htr
  exact (HPHull.hcap_congr (B := ⟨_, hF.image_affHomeo one_pos⟩) heq).trans htr

end Trace

/-- **Lower bound for the relative clock**: `2 · chartClock Γ t ≥ hcap(fill η₁([0, s₀ + t])) − hcap(fill K)`. -/
theorem chartClock_ge (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {g : ℂ → ℂ} {x₀ : ℂ}
    (hg : IsMapOut (fillH (prefixSet η₁ s₀ η₂ t₀)) g) (hφ : ∀ z, φ z = g z - x₀) (hx₀ : x₀.im = 0)
    (hK : IsClosed (prefixSet η₁ s₀ η₂ t₀)) {t : ℝ≥0}
    (hc₁ : ContinuousOn η₁ (Icc 0 (s₀ + t))) (hc₂ : ContinuousOn η₂ (Icc 0 t₀)) (h0₁ : (η₁ 0).im = 0)
    (h0₂ : (η₂ 0).im = 0) (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓ0 : (Γ 0).im ≤ 0)
    (hΓψ : ∀ r ∈ Icc 0 t, ψ (Γ r) = η₁ (s₀ + r)) :
    ConformalImage.hcapSet (fillH (η₁ '' Icc 0 (s₀ + t))) -
        ConformalImage.hcapSet (fillH (prefixSet η₁ s₀ η₂ t₀)) ≤ 2 * chartClock Γ t := by
  have hadd := hcapSet_fillH_prefixSet_eq hC hg hφ hx₀ hK hc₁ hc₂ h0₁ h0₂ hΓc hΓ0 hΓψ
  have h1 := isHPHull_fillH_image hc₁ h0₁.le
  have h2 := isHPHull_fillH_prefixSet hc₁ hc₂ h0₁ h0₂
  have hmono : ConformalImage.hcapSet (fillH (η₁ '' Icc 0 (s₀ + t))) ≤
      ConformalImage.hcapSet (fillH (prefixSet η₁ (s₀ + t) η₂ t₀)) := by
    rw [ConformalImage.hcapSet_eq h1, ConformalImage.hcapSet_eq h2]
    exact HPHull.hcap_mono (A := ⟨_, h1⟩) (B := ⟨_, h2⟩) (fillH_mono subset_union_left)
  unfold chartClock
  linarith

end Restart

end InteractingSLE
