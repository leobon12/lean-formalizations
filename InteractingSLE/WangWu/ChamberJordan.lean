/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Topology.Jordan.Complex
import InteractingSLE.Foundations.Topology.Schoenflies.Plane

/-!
# The two sides of a Jordan curve, and local connectivity at the curve

Packet PROVE-WW-B4 (Wang–Wu, `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31, §4.4–4.5: the
proofs of Proposition 4.20 and Lemma 4.22 use "the Jordan curve theorem", "a Jordan domain in the sphere" and the
"Carathéodory homeomorphism of the Jordan closures"). This file packages the project's Jordan curve theorem
(`InteractingSLE.Foundations.Jordan.jordan_curve_components_complex`) and Schoenflies theorem
(`InteractingSLE.schoenflies_plane`) in a form indexed by the curve alone:

* `jordanIn Γ` (the points off `Γ` whose complementary component is bounded) and `jordanOut Γ` (unbounded);
* `JordanSides`: for a Jordan curve both are open, preconnected, disjoint, cover `Γᶜ`, have frontier `Γ`; the inside
  is bounded and the outside is not;
* `subset_jordanOut_of_isPreconnected`, `IsPreconnected.subset_jordanIn_or_subset_jordanOut`: where a connected set
  disjoint from `Γ` lies;
* `exists_homeomorph_jordanIn`: a homeomorphism of `ℂ` carrying the unit circle onto `Γ` and the unit disc onto the
  inside;
* `exists_mem_nhds_isPreconnected_inter_jordanIn`: **local connectivity of the inside at the curve** — every point
  of `Γ` has arbitrarily small neighbourhoods `N` with `N ∩ jordanIn Γ` preconnected (the image of a ball under the
  Schoenflies homeomorphism).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology

namespace InteractingSLE.WangWu

/-- The inside of a closed set `Γ ⊆ ℂ`: the points off `Γ` whose connected component in `Γᶜ` is bounded. -/
def jordanIn (Γ : Set ℂ) : Set ℂ := {z | z ∉ Γ ∧ IsBounded (connectedComponentIn Γᶜ z)}

/-- The outside of a closed set `Γ ⊆ ℂ`: the points off `Γ` whose connected component in `Γᶜ` is unbounded. -/
def jordanOut (Γ : Set ℂ) : Set ℂ := {z | z ∉ Γ ∧ ¬ IsBounded (connectedComponentIn Γᶜ z)}

theorem jordanIn_subset_compl (Γ : Set ℂ) : jordanIn Γ ⊆ Γᶜ := fun _ hz => hz.1

theorem jordanOut_subset_compl (Γ : Set ℂ) : jordanOut Γ ⊆ Γᶜ := fun _ hz => hz.1

theorem disjoint_jordanIn_jordanOut (Γ : Set ℂ) : Disjoint (jordanIn Γ) (jordanOut Γ) :=
  Set.disjoint_left.2 fun _ h₁ h₂ => h₂.2 h₁.2

theorem compl_eq_jordanIn_union_jordanOut (Γ : Set ℂ) : Γᶜ = jordanIn Γ ∪ jordanOut Γ := by
  ext z
  constructor
  · intro hz
    by_cases hb : IsBounded (connectedComponentIn Γᶜ z)
    · exact Or.inl ⟨hz, hb⟩
    · exact Or.inr ⟨hz, hb⟩
  · rintro (hz | hz)
    · exact hz.1
    · exact hz.1

/-- A preconnected unbounded set disjoint from `Γ` lies outside `Γ`. -/
theorem subset_jordanOut_of_isPreconnected {Γ S : Set ℂ} (hS : IsPreconnected S) (hSu : ¬ IsBounded S)
    (hSΓ : Disjoint S Γ) : S ⊆ jordanOut Γ := by
  intro z hz
  have hzΓ : z ∉ Γ := Set.disjoint_left.1 hSΓ hz
  refine ⟨hzΓ, fun hb => hSu (hb.subset ?_)⟩
  exact hS.subset_connectedComponentIn hz (fun w hw => Set.disjoint_left.1 hSΓ hw)

/-- The Jordan curve theorem, indexed by the curve: for a Jordan curve `Γ` the inside and the outside are open,
preconnected and nonempty, the inside is bounded and the outside is not, and both have frontier `Γ`. -/
theorem JordanSides {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) :
    IsOpen (jordanIn Γ) ∧ IsPreconnected (jordanIn Γ) ∧ IsBounded (jordanIn Γ) ∧ (jordanIn Γ).Nonempty ∧
      IsOpen (jordanOut Γ) ∧ IsPreconnected (jordanOut Γ) ∧ ¬ IsBounded (jordanOut Γ) ∧
      frontier (jordanIn Γ) = Γ ∧ frontier (jordanOut Γ) = Γ := by
  obtain ⟨x₁, hx₁, x₀, hx₀, hb, hu, hd, hun, hf₁, hf₀⟩ :=
    Foundations.Jordan.jordan_curve_components_complex hΓ
  have hΓc : IsClosed Γ := hf₁ ▸ isClosed_frontier
  have hIn : jordanIn Γ = connectedComponentIn Γᶜ x₁ := by
    ext z
    constructor
    · rintro ⟨hz, hzb⟩
      have hz' : z ∈ Γᶜ := hz
      rw [hun] at hz'
      rcases hz' with h | h
      · exact h
      · exact absurd ((connectedComponentIn_eq h) ▸ hzb) hu
    · intro hz
      refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
      rw [← connectedComponentIn_eq hz]
      exact hb
  have hOut : jordanOut Γ = connectedComponentIn Γᶜ x₀ := by
    ext z
    constructor
    · rintro ⟨hz, hzb⟩
      have hz' : z ∈ Γᶜ := hz
      rw [hun] at hz'
      rcases hz' with h | h
      · exact absurd ((connectedComponentIn_eq h) ▸ hb) hzb
      · exact h
    · intro hz
      refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
      rw [← connectedComponentIn_eq hz]
      exact hu
  rw [hIn, hOut]
  exact ⟨hΓc.isOpen_compl.connectedComponentIn, isPreconnected_connectedComponentIn, hb,
    ⟨x₁, mem_connectedComponentIn hx₁⟩, hΓc.isOpen_compl.connectedComponentIn,
    isPreconnected_connectedComponentIn, hu, hf₁, hf₀⟩

theorem isOpen_jordanIn {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) : IsOpen (jordanIn Γ) :=
  (JordanSides hΓ).1

theorem isPreconnected_jordanIn {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) :
    IsPreconnected (jordanIn Γ) :=
  (JordanSides hΓ).2.1

theorem isBounded_jordanIn {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) : IsBounded (jordanIn Γ) :=
  (JordanSides hΓ).2.2.1

theorem isOpen_jordanOut {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) : IsOpen (jordanOut Γ) :=
  (JordanSides hΓ).2.2.2.2.1

theorem isPreconnected_jordanOut {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) :
    IsPreconnected (jordanOut Γ) :=
  (JordanSides hΓ).2.2.2.2.2.1

theorem frontier_jordanIn {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) : frontier (jordanIn Γ) = Γ :=
  (JordanSides hΓ).2.2.2.2.2.2.2.1

theorem frontier_jordanOut {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) :
    frontier (jordanOut Γ) = Γ :=
  (JordanSides hΓ).2.2.2.2.2.2.2.2

theorem isClosed_of_isJordanCurve {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) : IsClosed Γ :=
  frontier_jordanIn hΓ ▸ isClosed_frontier

theorem isCompact_of_isJordanCurve' {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) : IsCompact Γ := by
  obtain ⟨γ, hγc, -, rfl⟩ := hΓ
  exact (isCompact_sphere 0 1).image_of_continuousOn hγc

theorem closure_jordanIn {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) :
    closure (jordanIn Γ) = jordanIn Γ ∪ Γ := by
  rw [closure_eq_self_union_frontier, frontier_jordanIn hΓ]

/-- Every point of the curve is adherent to the inside and to the outside. -/
theorem mem_closure_jordanIn {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γ) :
    p ∈ closure (jordanIn Γ) := by
  rw [← frontier_jordanIn hΓ] at hp
  exact frontier_subset_closure hp

theorem mem_closure_jordanOut {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γ) :
    p ∈ closure (jordanOut Γ) := by
  rw [← frontier_jordanOut hΓ] at hp
  exact frontier_subset_closure hp

/-- A preconnected set disjoint from a Jordan curve lies on one side of it. -/
theorem IsPreconnected.subset_jordanIn_or_subset_jordanOut {Γ S : Set ℂ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hS : IsPreconnected S) (hSΓ : Disjoint S Γ) :
    S ⊆ jordanIn Γ ∨ S ⊆ jordanOut Γ := by
  have hsub : S ⊆ jordanIn Γ ∪ jordanOut Γ := by
    rw [← compl_eq_jordanIn_union_jordanOut]
    exact fun z hz => Set.disjoint_left.1 hSΓ hz
  exact IsPreconnected.subset_or_subset (isOpen_jordanIn hΓ) (isOpen_jordanOut hΓ)
    (disjoint_jordanIn_jordanOut Γ) hsub hS

/-- A preconnected set disjoint from a Jordan curve and meeting its inside lies inside. -/
theorem IsPreconnected.subset_jordanIn {Γ S : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ)
    (hS : IsPreconnected S) (hSΓ : Disjoint S Γ) (hne : (S ∩ jordanIn Γ).Nonempty) : S ⊆ jordanIn Γ := by
  rcases IsPreconnected.subset_jordanIn_or_subset_jordanOut hΓ hS hSΓ with h | h
  · exact h
  · obtain ⟨z, hzS, hzI⟩ := hne
    exact absurd (h hzS) (Set.disjoint_left.1 (disjoint_jordanIn_jordanOut Γ) hzI)

/-- A preconnected set disjoint from a Jordan curve and meeting its outside lies outside. -/
theorem IsPreconnected.subset_jordanOut {Γ S : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ)
    (hS : IsPreconnected S) (hSΓ : Disjoint S Γ) (hne : (S ∩ jordanOut Γ).Nonempty) : S ⊆ jordanOut Γ := by
  rcases IsPreconnected.subset_jordanIn_or_subset_jordanOut hΓ hS hSΓ with h | h
  · obtain ⟨z, hzS, hzO⟩ := hne
    exact absurd (h hzS) (Set.disjoint_right.1 (disjoint_jordanIn_jordanOut Γ) hzO)
  · exact h

/-- **Schoenflies**, indexed by the curve: a homeomorphism of `ℂ` carrying the unit circle onto `Γ` and the unit disc
onto the inside of `Γ`. -/
theorem exists_homeomorph_jordanIn {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) :
    ∃ h : ℂ ≃ₜ ℂ, h '' sphere 0 1 = Γ ∧ h '' ball 0 1 = jordanIn Γ := by
  obtain ⟨p, hp⟩ := (JordanSides hΓ).2.2.2.1
  obtain ⟨h, hs, hb, -, -⟩ := schoenflies_plane hΓ hp.1 hp.2
  refine ⟨h, hs, hb.trans ?_⟩
  ext z
  constructor
  · intro hz
    refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
    rw [← connectedComponentIn_eq hz]
    exact hp.2
  · intro hz
    -- both `z` and `p` lie in the (unique) bounded component
    obtain ⟨x₁, -, x₀, -, -, hu, -, hun, -, -⟩ := Foundations.Jordan.jordan_curve_components_complex hΓ
    have hcomp : ∀ w ∈ Γᶜ, IsBounded (connectedComponentIn Γᶜ w) →
        connectedComponentIn Γᶜ w = connectedComponentIn Γᶜ x₁ := by
      intro w hw hwb
      have hw' := hw
      rw [hun] at hw'
      rcases hw' with h' | h'
      · exact (connectedComponentIn_eq h').symm
      · exact absurd ((connectedComponentIn_eq h') ▸ hwb) hu
    rw [hcomp p hp.1 hp.2, ← hcomp z hz.1 hz.2]
    exact mem_connectedComponentIn hz.1

/-- **Local connectivity of the inside at the curve.** Every point `p` (in particular every point of the curve) has
arbitrarily small neighbourhoods `N` such that `N ∩ jordanIn Γ` is preconnected. -/
theorem exists_mem_nhds_isPreconnected_inter_jordanIn {Γ : Set ℂ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (p : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N ∈ 𝓝 p, N ⊆ ball p ε ∧ IsPreconnected (N ∩ jordanIn Γ) := by
  obtain ⟨h, hs, hb⟩ := exists_homeomorph_jordanIn hΓ
  set q := h.symm p with hq
  have hhq : h q = p := h.apply_symm_apply p
  -- a ball around `q` mapped into `ball p ε`
  have hcont : Tendsto h (𝓝 q) (𝓝 p) := hhq ▸ h.continuous.tendsto q
  obtain ⟨δ, hδ, hδε⟩ := Metric.mem_nhds_iff.1 (hcont (ball_mem_nhds p hε))
  refine ⟨h '' ball q δ, ?_, ?_, ?_⟩
  · rw [← hhq]
    exact h.isOpenMap.image_mem_nhds (ball_mem_nhds q hδ)
  · rintro _ ⟨w, hw, rfl⟩
    exact hδε hw
  · have heq : h '' ball q δ ∩ jordanIn Γ = h '' (ball q δ ∩ ball 0 1) := by
      rw [← hb, image_inter h.injective]
    rw [heq]
    exact ((convex_ball q δ).inter (convex_ball 0 1)).isPreconnected.image _
      h.continuous.continuousOn

end InteractingSLE.WangWu
