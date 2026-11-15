/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxAe

/-!
# The relative lifetime of a stage is finite when the retained set after it is a hull

Worker PROVE-SB2-F3LAW (target 1). The step `ℓ → ℓ + 2` needs the canonical lifetime of B's piece `ℓ` (equal to the
relative lifetime `relLife` of F2b′'s versions) to be finite where the retained set after the piece fills to a hull.
**Argument (capacity).** Before every stop, the versions' hull field identifies the step hull
`fill K ∪ c⁻¹(K_s)` (`c = Mo.hullChart (fill K) x₀`, `K_s` the relative hull at relative time `s`) with
`fill K ∪ A₂(q)` for a rational B-time `q`, a subset of the hull `Z = fill S₂`. Capacity is monotone on hulls and
`hcap(fill K ∪ c⁻¹(K_s)) = hcap(fill K) + 2s` (`Qw.hcapSet_stepHull`), so `s ≤ (hcap Z − hcap(fill K))/2`. The relative
times reached before the stops are cofinal in every stop (`reach` and continuity of the clocks), so every stop, hence
their supremum `relLife`, is at most that bound.

* `stepHull_subset_of_hull`, `hcapSet_add_le_of_stepHull_subset`, **`ne_top_of_versions_at`** (one sample);
* **`ae_relLife_ne_top_of_versions`**: almost surely on F2b′'s live event, if `fill S₂` is a hull then `relLife < ⊤`
  (the inputs of `Qx.ae_fill_eq_stepHull_of_versions` without the record).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fl

open Restart Exist Exist.Staged Exist.StagedLaw Qw Supp8.Q3Stop Lv

/-- **The step hull lies in a set containing the retained hull and the piece**, when the hull field identifies their
complements. -/
theorem stepHull_subset_of_hull {K₀ Z A₂ : Set ℂ} (hK₀ : IsHPHull K₀) (x₀ : ℝ) {W : ℝ → ℝ} {s : ℝ}
    (hA₂H : A₂ ⊆ H) (hA₂Z : A₂ ⊆ Z) (hKZ : K₀ ⊆ Z)
    (hhull : H \ (K₀ ∪ A₂) = (Mo.hullChart K₀ x₀).2.1 '' (H \ fwdHull W s)) :
    stepHull K₀ x₀ W s ⊆ Z := by
  have hJH : fwdHull W s ⊆ H := fun z hz => hz.1
  have hc := Mo.isConformal_hullChart hK₀ x₀
  have hinvH : (Mo.hullChart K₀ x₀).2.1 '' fwdHull W s ⊆ H := by
    rintro _ ⟨w, hw, rfl⟩
    have hd := hc.inv_mem_dom (hJH hw)
    change (Mo.hullChart K₀ x₀).2.1 w ∈ ((Mo.hullChart K₀ x₀).dom : Set ℂ) at hd
    rw [Mo.coe_dom_hullChart hK₀ x₀] at hd
    exact hd.1
  rw [Qx.hullChart_inv_image_diff hK₀ x₀ hJH] at hhull
  have h2 := Qx.eq_of_H_diff_eq (union_subset hK₀.1 hA₂H) (union_subset hK₀.1 hinvH) hhull
  change K₀ ∪ (Mo.hullChart K₀ x₀).2.1 '' fwdHull W s ⊆ Z
  rw [← h2]
  exact union_subset hKZ hA₂Z

/-- **Capacity bound of a step hull inside a hull.** -/
theorem hcapSet_add_le_of_stepHull_subset {K₀ Z : Set ℂ} (hK₀ : IsHPHull K₀) (x₀ : ℝ) (hZ : IsHPHull Z)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) (hsub : stepHull K₀ x₀ W s ⊆ Z) :
    ConformalImage.hcapSet K₀ + 2 * s ≤ ConformalImage.hcapSet Z := by
  rw [← hcapSet_stepHull hK₀ x₀ hW hW0 hs, ConformalImage.hcapSet_eq (isHPHull_stepHull hK₀ x₀ hW hW0 hs),
    ConformalImage.hcapSet_eq hZ]
  exact HPHull.hcap_mono hsub

/-- **The supremum of the stops is finite, at one sample**, when the versions' hulls before the stops lie in a hull
`Z`. -/
theorem ne_top_of_versions_at {K₀ Z : Set ℂ} (hK₀ : IsHPHull K₀) (x₀ : ℝ) (hZ : IsHPHull Z) (hKZ : K₀ ⊆ Z)
    {A₂ : ℝ≥0 → Set ℂ} (hA₂H : ∀ q : ℚ, A₂ (Real.toNNReal q) ⊆ H) (hA₂Z : ∀ q : ℚ, A₂ (Real.toNNReal q) ⊆ Z)
    {W : ℕ → ℝ≥0 → ℝ} (hWc : ∀ m, Continuous (W m)) (hW0 : ∀ m, W m 0 = 0)
    {a : ℕ → ℝ≥0 → ℝ≥0∞} (hac : ∀ m, Continuous (a m)) (ha0 : ∀ m, a m 0 = 0) {V : ℕ → ℝ≥0∞} {T : ℝ≥0∞}
    (hVsup : ⨆ m, V m = T)
    (hhull : ∀ (q : ℚ) (m : ℕ), a m (Real.toNNReal q) < V m →
      H \ (K₀ ∪ A₂ (Real.toNNReal q)) = (Mo.hullChart K₀ x₀).2.1 ''
        (H \ fwdHull (fun r : ℝ => W m r.toNNReal) (a m (Real.toNNReal q)).toReal))
    (hreach : ∀ (r : ℚ) (m : ℕ), ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < V m →
      ∃ t, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ a m t) :
    T ≠ ⊤ := by
  set C : ℝ := (ConformalImage.hcapSet Z - ConformalImage.hcapSet K₀) / 2 with hC
  have hWr : ∀ m, Continuous fun r : ℝ => W m r.toNNReal := fun m => (hWc m).comp continuous_real_toNNReal
  have hWr0 : ∀ m, (fun r : ℝ => W m r.toNNReal) 0 = 0 := fun m => by
    simp only [Real.toNNReal_zero, hW0 m]
  have hle : ∀ m, V m ≤ ENNReal.ofReal C := by
    intro m
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    have hq : (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r := rfl
    obtain ⟨t₀, ht₀⟩ := hreach r m (by rw [hq]; exact hr2)
    have hivt := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t₀) (hac m).continuousOn
    obtain ⟨t₁, -, ht₁⟩ := hivt ⟨by rw [ha0 m]; exact zero_le, ht₀⟩
    have hU : IsOpen ((a m) ⁻¹' Ioo (ENNReal.ofReal C) (V m)) := isOpen_Ioo.preimage (hac m)
    have ht₁U : t₁ ∈ (a m) ⁻¹' Ioo (ENNReal.ofReal C) (V m) := by
      change a m t₁ ∈ Ioo _ _
      rw [ht₁, hq]
      exact ⟨hr1, hr2⟩
    obtain ⟨q, hqU⟩ := denseRange_rat_toNNReal.exists_mem_open hU ⟨t₁, ht₁U⟩
    have hqU' : a m (Real.toNNReal q) ∈ Ioo (ENNReal.ofReal C) (V m) := hqU
    have hane : a m (Real.toNNReal q) ≠ ⊤ := ne_top_of_lt hqU'.2
    have hsub := stepHull_subset_of_hull hK₀ x₀ (hA₂H q) (hA₂Z q) hKZ (hhull q m hqU'.2)
    have hcap := hcapSet_add_le_of_stepHull_subset hK₀ x₀ hZ (hWr m) (hWr0 m) ENNReal.toReal_nonneg hsub
    have hs : (a m (Real.toNNReal q)).toReal ≤ C := by rw [hC]; linarith
    have h3 : a m (Real.toNNReal q) ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_toReal hane]
      exact ENNReal.ofReal_le_ofReal hs
    exact absurd hqU'.1 (not_lt.2 h3)
  rw [← hVsup]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hle)

/-- **The relative lifetime is finite, almost surely on F2b′'s live event, where the retained set after the piece
fills to a hull.** -/
theorem ae_relLife_ne_top_of_versions {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {β : Ω → BoundaryWord}
    {types : Set WordType} (htypes : types.Countable) {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}
    (S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β types pc tL L relLife)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (β ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ β F w → ω ∈ seedCell κ ψ β F w)
    (hA₁ : ∀ q : ℚ, ∀ᵐ ω ∂P, ω ∈ F → A₁ (Real.toNNReal q) ω = fillH (K ω)) {S₂ : Ω → Set ℂ}
    (hphys : ∀ᵐ ω ∂P, ω ∈ F → IsHPHull (fillH (S₂ ω)) →
      fillH (K ω) ⊆ fillH (S₂ ω) ∧ (∀ q : ℚ, A₂ (Real.toNNReal q) ω ⊆ H) ∧
        (∀ q : ℚ, A₂ (Real.toNNReal q) ω ⊆ fillH (S₂ ω)) ∧
        S₂ ω ∩ H ⊆ fillH (K ω) ∪ ⋃ (q : ℚ) (_ : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < L ω), A₂ (Real.toNNReal q) ω) :
    ∀ᵐ ω ∂P, ω ∈ F → IsHPHull (fillH (S₂ ω)) → relLife ω ≠ ⊤ := by
  have hH : ∀ᵐ ω ∂P, ∀ (q : ℚ) (m : ℕ), ∀ w ∈ types, ω ∈ seedCell κ ψ β F w →
      (S.ver m).a (Real.toNNReal q) ω < (S.ver m).Λ w ω →
      H \ (A₁ (Real.toNNReal q) ω ∪ A₂ (Real.toNNReal q) ω) = (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.1 ''
        (H \ fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a (Real.toNNReal q) ω).toNNReal) := by
    refine ae_all_iff.2 fun q => ae_all_iff.2 fun m => (ae_ball_iff htypes).2 fun w hw => ?_
    exact (S.ver m).hull w hw _
  have hR : ∀ᵐ ω ∂P, ∀ (r : ℚ) (m : ℕ), ∀ w ∈ types, ω ∈ seedCell κ ψ β F w →
      ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < (S.ver m).Λ w ω → ∃ t, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ (S.ver m).a t ω := by
    refine ae_all_iff.2 fun r => ae_all_iff.2 fun m => (ae_ball_iff htypes).2 fun w hw => ?_
    exact (S.ver m).reach w hw _
  have hA₁' : ∀ᵐ ω ∂P, ∀ q : ℚ, ω ∈ F → A₁ (Real.toNNReal q) ω = fillH (K ω) := ae_all_iff.2 hA₁
  have hsd : ∀ᵐ ω ∂P, ∀ w ∈ types, ω ∈ wordTypeCell κ ψ β F w → ω ∈ seedCell κ ψ β F w :=
    (ae_ball_iff htypes).2 hseed
  filter_upwards [hH, hR, hA₁', hsd, S.V_sup, hcover, hphys] with ω hHω hRω hA₁ω hsdω hVsω hcovω hphysω hωF hZ
  have hwT : angleWordType κ ψ (β ω) ∈ types := hcovω hωF
  have hseedω : ω ∈ seedCell κ ψ β F (angleWordType κ ψ (β ω)) := hsdω _ hwT ⟨hωF, rfl⟩
  obtain ⟨hKZ, hA₂H, hA₂Z, -⟩ := hphysω hωF hZ
  refine ne_top_of_versions_at (Mo.isHPHull_fillH hKc hKp ω) (x₀ ω) hZ hKZ (A₂ := fun t => A₂ t ω) hA₂H hA₂Z
    (W := fun m s => (S.ver m).W s ω) (fun m => (S.ver m).W_cont ω) (fun m => (S.ver m).W_zero ω)
    (a := fun m t => (S.ver m).a t ω) (fun m => (S.ver m).clock_cont ω) (fun m => (S.ver m).clock_zero ω)
    (V := fun m => S.V m ω) (hVsω hωF) (fun q m hqm => ?_) (fun r m hr => ?_)
  · have h1 := hHω q m _ hwT hseedω (by rw [S.Λ_eq m]; exact hqm)
    rw [hA₁ω q hωF] at h1
    exact h1
  · exact hRω r m _ hwT hseedω (by rw [S.Λ_eq m]; exact hr)

end InteractingSLE.Theorem14.SB.Fl
