/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartDataPath
import InteractingSLE.Spec.Sec7.InteractionFirstContact
import InteractingSLE.Spec.Sec6.DrivingUnconditional
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Foundations.Loewner.ConformalImageLoewner

/-!
# The relative domains after a first contact (Aux. lemma 76, the relative target component)

Packet PROVE-RESTART-CPL5. Specification Aux. lemma 76 (`source/spec/p241-288.md#aux-76`, pp. 285–287) and (W8.1)
(supplement p. 539). Let `η₁, η₂` be simple paths in `ℍ̄` from real seeds with first contact `η₁(s₀) = η₂(t₀)`,
`K = η₁([0, s₀]) ∪ η₂([0, t₀])` and `D = ℍ \ fill K` (the active domain). For `u ≥ s₀` put

  `D*_u = ℍ \ fill(η₁([0, u]) ∪ η₂([0, t₀]))`,

the unbounded component left by the continuation of `η₁` up to time `u`.

* `inter_subset_relDomain` (Janiszewski, Aux. lemma 59's key step): `D ∩ (ℍ \ fill η₁([0, u])) ⊆ D*_u`. The two
  obstacles `K` and `η₁([0, u])` meet exactly in `η₁([0, s₀])`, which is connected and attached to `ℝ`.
* **Old-union avoidance** in the form the clocks need (`mem_activeDomain_of_mem_H`): a continuation point
  `η₁(s)`, `s > s₀`, in `ℍ` lies in the open domain `D`. It is adherent to `D` (confinement, Lemma 7.7) and off `K`
  (no return, Aux. lemma 73, `IsFirstContact.no_return`), and a point of `ℍ` off `K` adherent to `ℍ \ fill K` is in it.
* **(CG1)** (`mem_relDomain`): if moreover `η₁(s)` is adherent to `ℍ \ fill η₁([0, u])` for some `u ∈ [s₀, s)` (the
  Loewner tip property of the original trace), then `η₁(s) ∈ D*_u`.
* **(CG2)** (`mem_closure_relDomain`): with interior times dense (an original Loewner trace spends no time interval on
  `ℝ`), `η₁(s) ∈ closure D*_u` for every available `s > u`, including real contacts and a finite terminal point.

This is the specification's argument (p. 286: "Whenever `α(t) ∈ ℍ`, confinement and avoidance put `α(t)` in the
open original component `D`. Apply Aux. lemma 59 …"), except that the active-tip conclusion of Aux. lemma 59 is
replaced by the original trace's own tip property, which makes the step a direct application of Janiszewski.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0}

/-! ### A point of `ℍ` adherent to an unbounded domain -/

/-- A point of `ℍ` off a closed set `F` and adherent to the unbounded domain `ℍ \ fill F` lies in it. -/
theorem mem_H_diff_fillH_of_mem_closure {F : Set ℂ} {z : ℂ} (hF : IsClosed F) (hzH : z ∈ H) (hzF : z ∉ F)
    (hz : z ∈ closure (H \ fillH F)) : z ∈ H \ fillH F := by
  rcases HalfPlaneSep.isFreeAt_or_isTrappedAt hF hzF with ⟨ε, hε, h⟩ | ⟨ε, hε, h⟩
  · exact h ⟨mem_ball_self hε, hzH⟩
  · obtain ⟨w, hw, hd⟩ := Metric.mem_closure_iff.1 hz ε hε
    exact absurd hw (Set.disjoint_left.1 h (mem_ball.2 (by rwa [dist_comm])))

/-! ### The relative domains -/

theorem prefixSet_mono_left {u : ℝ≥0} (hu : s₀ ≤ u) :
    prefixSet η₁ s₀ η₂ t₀ ⊆ prefixSet η₁ u η₂ t₀ :=
  union_subset_union_left _ (image_mono (Icc_subset_Icc_right hu))

theorem prefixSet_eq_union {u : ℝ≥0} (hu : s₀ ≤ u) :
    prefixSet η₁ u η₂ t₀ = prefixSet η₁ s₀ η₂ t₀ ∪ η₁ '' Icc 0 u := by
  apply Subset.antisymm
  · rintro z (hz | hz)
    · exact Or.inr hz
    · exact Or.inl (Or.inr hz)
  · rintro z ((hz | hz) | hz)
    · exact Or.inl (image_mono (Icc_subset_Icc_right hu) hz)
    · exact Or.inr hz
    · exact Or.inl hz

theorem isCompact_prefixSet {u : ℝ≥0} (hc₁ : ContinuousOn η₁ (Icc 0 u)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀)) :
    IsCompact (prefixSet η₁ u η₂ t₀) :=
  (isCompact_Icc.image_of_continuousOn hc₁).union (isCompact_Icc.image_of_continuousOn hc₂)

/-- At a first contact, the old union `K` and the prefix `η₁([0, u])`, `u ≥ s₀`, meet in `η₁([0, s₀])`. -/
theorem prefixSet_inter_image_subset (hfc : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) {u : ℝ≥0}
    (huζ : (u : ℝ≥0∞) ≤ ζ₁) :
    prefixSet η₁ s₀ η₂ t₀ ∩ η₁ '' Icc 0 u ⊆ η₁ '' Icc 0 s₀ := by
  rintro z ⟨hz | ⟨t, ht, rfl⟩, ⟨s, hs, hst⟩⟩
  · exact hz
  · have hsζ : (s : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hs.2).trans huζ
    have htζ : (t : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 ht.2).trans hfc.2.1
    obtain ⟨-, h2⟩ := hfc.2.2.2 s t hsζ htζ hst
    have htt : t = t₀ := le_antisymm ht.2 h2
    subst htt
    exact ⟨s₀, ⟨zero_le, le_rfl⟩, hfc.2.2.1⟩

/-- **Janiszewski for the relative domain** (Aux. lemma 59's key step): a point of `ℍ` in the active domain
`D = ℍ \ fill K` and in the unbounded domain of `η₁([0, u])`, `s₀ ≤ u`, is in the relative domain `D*_u`. -/
theorem inter_subset_relDomain (hfc : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) {u : ℝ≥0} (hu : s₀ ≤ u)
    (huζ : (u : ℝ≥0∞) ≤ ζ₁) (hc₁ : ContinuousOn η₁ (Icc 0 u)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (h0₁ : (η₁ 0).im = 0) :
    (H \ fillH (prefixSet η₁ s₀ η₂ t₀)) ∩ (H \ fillH (η₁ '' Icc 0 u)) ⊆
      H \ fillH (prefixSet η₁ u η₂ t₀) := by
  have hc₁' : ContinuousOn η₁ (Icc 0 s₀) := hc₁.mono (Icc_subset_Icc_right hu)
  rw [prefixSet_eq_union hu]
  refine HalfPlaneSep.H_diff_fillH_inter_subset (isCompact_prefixSet hc₁' hc₂)
    (isCompact_Icc.image_of_continuousOn hc₁) fun w hw => ?_
  refine ⟨η₁ '' Icc 0 s₀, fun z hz => ⟨Or.inl hz, image_mono (Icc_subset_Icc_right hu) hz⟩,
    isPreconnected_Icc.image _ hc₁', prefixSet_inter_image_subset hfc huζ hw, η₁ 0,
    ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩, h0₁⟩

/-- **Old-union avoidance, open form**: a continuation point `η₁(s)`, `s > s₀`, lying in `ℍ` is in the open active
domain `D = ℍ \ fill K` (confinement, Lemma 7.7, and no return, Aux. lemma 73). -/
theorem mem_activeDomain_of_mem_H (hfc : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀)
    (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hc₁ : ContinuousOn η₁ (Icc 0 s₀)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀)) {s : ℝ≥0} (hs : s₀ < s)
    (hsζ : (s : ℝ≥0∞) ≤ ζ₁) (hconf : η₁ s ∈ closure (activeDomain η₁ s₀ η₂ t₀)) (hsH : η₁ s ∈ H) :
    η₁ s ∈ H \ fillH (prefixSet η₁ s₀ η₂ t₀) := by
  have hK := (isCompact_prefixSet hc₁ hc₂).isClosed
  rw [activeDomain_eq hK] at hconf
  exact mem_H_diff_fillH_of_mem_closure hK hsH ((Sec7.IsFirstContact.no_return hi₁ hi₂ hfc).1 s hs hsζ) hconf

/-- **(CG1)**: a continuation point `η₁(s)` in `ℍ`, adherent to the unbounded domain of an earlier prefix
`η₁([0, u])`, `s₀ ≤ u < s` (the tip property of the original Loewner trace), is in the relative domain `D*_u`. -/
theorem mem_relDomain (hfc : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀)
    (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hc₁ : ContinuousOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ (Icc 0 t₀)) (h0₁ : (η₁ 0).im = 0)
    {u s : ℝ≥0} (hu : s₀ ≤ u) (hus : u < s) (hsζ : (s : ℝ≥0∞) ≤ ζ₁)
    (hconf : η₁ s ∈ closure (activeDomain η₁ s₀ η₂ t₀))
    (htip : η₁ s ∈ closure (H \ fillH (η₁ '' Icc 0 u))) (hsH : η₁ s ∈ H) :
    η₁ s ∈ H \ fillH (prefixSet η₁ u η₂ t₀) := by
  have huζ : (u : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hus.le).trans hsζ
  have hcu : ContinuousOn η₁ (Icc 0 u) :=
    hc₁.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans huζ
  refine inter_subset_relDomain hfc hu huζ hcu hc₂ h0₁
    ⟨mem_activeDomain_of_mem_H hfc hi₁ hi₂ (hcu.mono (Icc_subset_Icc_right hu)) hc₂ (hu.trans_lt hus) hsζ
      hconf hsH, ?_⟩
  refine mem_H_diff_fillH_of_mem_closure (isCompact_Icc.image_of_continuousOn hcu).isClosed hsH ?_ htip
  rintro ⟨r, hr, hrs⟩
  have := hi₁ ((ENNReal.coe_le_coe.2 hr.2).trans huζ) hsζ hrs
  exact absurd (this ▸ hr.2) (not_le.2 hus)

/-- **(CG2)**: with interior times dense after `u`, every available continuation point `η₁(s)`, `s > u ≥ s₀`, is
adherent to the relative domain `D*_u`. -/
theorem mem_closure_relDomain (hfc : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀)
    (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hc₁ : ContinuousOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ (Icc 0 t₀)) (h0₁ : (η₁ 0).im = 0)
    (hconf : ∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ closure (activeDomain η₁ s₀ η₂ t₀))
    (htip : ∀ u s : ℝ≥0, u < s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ closure (H \ fillH (η₁ '' Icc 0 u)))
    (hdense : ∀ a b : ℝ≥0, a < b → (b : ℝ≥0∞) ≤ ζ₁ → ∃ s ∈ Ioo a b, η₁ s ∈ H)
    {u s : ℝ≥0} (hu : s₀ ≤ u) (hus : u < s) (hsζ : (s : ℝ≥0∞) ≤ ζ₁) :
    η₁ s ∈ closure (H \ fillH (prefixSet η₁ u η₂ t₀)) := by
  -- interior times `sₙ ∈ (max u (s − 1/(n+1)), s)` converge to `s`
  have hmem : ∀ r : ℝ≥0, u < r → (r : ℝ≥0∞) ≤ ζ₁ → η₁ r ∈ H →
      η₁ r ∈ H \ fillH (prefixSet η₁ u η₂ t₀) := fun r hur hrζ hrH =>
    mem_relDomain hfc hi₁ hi₂ hc₁ hc₂ h0₁ hu hur hrζ (hconf r (hu.trans hur.le) hrζ)
      (htip u r hur hrζ) hrH
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 (hc₁ s hsζ) ε hε
  set a : ℝ≥0 := max u (((s : ℝ) - δ / 2).toNNReal) with ha
  have hs0 : 0 < s := lt_of_le_of_lt zero_le hus
  have has : a < s := by
    refine max_lt hus ?_
    have h := (Real.toNNReal_lt_toNNReal_iff (NNReal.coe_pos.2 hs0)).2
      (show (s : ℝ) - δ / 2 < s by linarith)
    rwa [Real.toNNReal_coe] at h
  obtain ⟨r, hr, hrH⟩ := hdense a s has hsζ
  have hrζ : (r : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hr.2.le).trans hsζ
  refine ⟨η₁ r, hmem r (lt_of_le_of_lt (le_max_left _ _) hr.1) hrζ hrH, ?_⟩
  rw [dist_comm]
  refine hδε hrζ ?_
  have h1 : (s : ℝ) - δ / 2 < r := by
    have h2 : (((s : ℝ) - δ / 2).toNNReal : ℝ) < r :=
      NNReal.coe_lt_coe.2 (lt_of_le_of_lt (le_max_right _ _) hr.1)
    exact lt_of_le_of_lt (Real.le_coe_toNNReal _) h2
  have h3 : (r : ℝ) < s := NNReal.coe_lt_coe.2 hr.2
  rw [NNReal.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### The chart path of the continuation -/

section ChartPath

variable {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

theorem IsFirstContactChart.mapsTo_fwd (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) :
    MapsTo φ (activeDomain η₁ s₀ η₂ t₀) H :=
  hC.1.1.mapsTo

theorem IsFirstContactChart.inv_fwd (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {z : ℂ}
    (hz : z ∈ activeDomain η₁ s₀ η₂ t₀) : ψ (φ z) = z := by
  obtain ⟨w, hw, rfl⟩ := hC.2.1.surjOn hz
  rw [hC.2.2.1 w hw]

/-- A point `w ∈ ℍ̄` whose `ψ`-image lies in the active domain is in `ℍ`. -/
theorem IsFirstContactChart.mem_H_of_inv_mem (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {w : ℂ}
    (hw : ψ w ∈ activeDomain η₁ s₀ η₂ t₀) : w ∈ H := by
  by_contra h
  exact hC.2.2.2.1 w h hw

theorem IsFirstContactChart.continuousOn_fwd (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) :
    ContinuousOn φ (activeDomain η₁ s₀ η₂ t₀) :=
  hC.1.2.1.continuousOn

/-- The forward image of an unbounded subset of the active domain is unbounded (`φ → ∞` at `∞`). -/
theorem IsFirstContactChart.not_isBounded_image (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift)
    {X : Set ℂ} (hXD : X ⊆ activeDomain η₁ s₀ η₂ t₀) (hX : ¬ Bornology.IsBounded X) :
    ¬ Bornology.IsBounded (φ '' X) := by
  intro hB
  have h0 : (φ '' X)ᶜ ∈ Bornology.cobounded ℂ := hB
  have h1 := hC.1.2.2.2 h0
  rw [mem_map, mem_inf_principal] at h1
  refine hX ((Bornology.isBounded_compl_iff.2 h1).subset fun z hz hz' => ?_)
  exact hz' (hXD hz) ⟨z, hz, rfl⟩

variable {U : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}

/-- At a continuation point in the active domain, the chart path is the chart value (and lies in `ℍ`). -/
theorem chartPath_eq_fwd (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {r : ℝ≥0}
    (hΓψ : ψ (Γ r) = η₁ (s₀ + r)) (hD : η₁ (s₀ + r) ∈ activeDomain η₁ s₀ η₂ t₀) :
    Γ r = φ (η₁ (s₀ + r)) ∧ Γ r ∈ H := by
  have hH : Γ r ∈ H := hC.mem_H_of_inv_mem (hΓψ ▸ hD)
  refine ⟨?_, hH⟩
  rw [← hΓψ, hC.2.2.1 _ hH]

/-- The chart path is injective where the continuation is. -/
theorem chartPath_injOn {T : Set ℝ≥0} (hΓψ : ∀ r ∈ T, ψ (Γ r) = η₁ (s₀ + r))
    (hi : InjOn (fun r => η₁ (s₀ + r)) T) : InjOn Γ T := fun a ha b hb hab =>
  hi ha hb (by simp only; rw [← hΓψ a ha, ← hΓψ b hb, hab])

/-- **The forward image of the relative domain** avoids the chart path up to time `t`: it lies in the unbounded
domain of `Γ([0, t])`. -/
theorem fwd_image_relDomain_subset (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift)
    (hK : IsClosed (prefixSet η₁ s₀ η₂ t₀)) {t : ℝ≥0}
    (hc₁ : ContinuousOn η₁ (Icc 0 (s₀ + t))) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓψ : ∀ r ∈ Icc 0 t, ψ (Γ r) = η₁ (s₀ + r)) :
    φ '' (H \ fillH (prefixSet η₁ (s₀ + t) η₂ t₀)) ⊆ H \ fillH (Γ '' Icc 0 t) := by
  set P := prefixSet η₁ (s₀ + t) η₂ t₀ with hP
  have hPc : IsCompact P := isCompact_prefixSet hc₁ hc₂
  have hsub : H \ fillH P ⊆ activeDomain η₁ s₀ η₂ t₀ := by
    rw [activeDomain_eq hK]
    exact sdiff_subset_sdiff_right (fillH_mono (prefixSet_mono_left le_self_add))
  have hX : IsPreconnected (φ '' (H \ fillH P)) :=
    (HalfPlaneSep.isPreconnected_H_diff_fillH hPc.isClosed hPc.isBounded).image _
      (hC.continuousOn_fwd.mono hsub)
  have hXu : ¬ Bornology.IsBounded (φ '' (H \ fillH P)) :=
    hC.not_isBounded_image hsub (HalfPlaneSep.not_isBounded_H_diff_fillH hPc.isClosed hPc.isBounded)
  refine HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded
    (isCompact_Icc.image_of_continuousOn hΓc).isClosed hX hXu ?_
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨hC.mapsTo_fwd (hsub hz), ?_⟩
  rintro ⟨r, hr, hrz⟩
  -- `z = ψ (φ z) = ψ (Γ r) = η₁ (s₀ + r)` lies on the prefix `η₁([0, s₀ + t])`
  have hzr : z = η₁ (s₀ + r) := by rw [← hC.inv_fwd (hsub hz), ← hrz, hΓψ r hr]
  have hzP : z ∈ P := Or.inl ⟨s₀ + r, ⟨zero_le, add_le_add le_rfl hr.2⟩, hzr.symm⟩
  exact hz.2 (mem_fillH_of_mem_closure hz.1 (subset_closure hzP))

/-- **The inverse image of the unbounded domain of `Γ([0, t])`** lies in the relative domain `D*_{s₀ + t}`. -/
theorem inv_image_subset_relDomain (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift)
    (hK : IsClosed (prefixSet η₁ s₀ η₂ t₀)) {t : ℝ≥0}
    (hc₁ : ContinuousOn η₁ (Icc 0 (s₀ + t))) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓψ : ∀ r ∈ Icc 0 t, ψ (Γ r) = η₁ (s₀ + r)) :
    ψ '' (H \ fillH (Γ '' Icc 0 t)) ⊆ H \ fillH (prefixSet η₁ (s₀ + t) η₂ t₀) := by
  obtain ⟨-, hbij, -, -, -, -, -, hψc, -, ⟨M, hM⟩, -⟩ := id hC
  have hA : IsCompact (Γ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn hΓc
  set P := prefixSet η₁ (s₀ + t) η₂ t₀ with hP
  have hPc : IsCompact P := isCompact_prefixSet hc₁ hc₂
  have hHA : H \ fillH (Γ '' Icc 0 t) ⊆ H := sdiff_subset
  have hX : IsPreconnected (ψ '' (H \ fillH (Γ '' Icc 0 t))) :=
    (HalfPlaneSep.isPreconnected_H_diff_fillH hA.isClosed hA.isBounded).image _
      (hψc.mono (hHA.trans fun w hw => show (0 : ℝ) ≤ w.im from le_of_lt (show (0 : ℝ) < w.im from hw)))
  have hXu : ¬ Bornology.IsBounded (ψ '' (H \ fillH (Γ '' Icc 0 t))) := by
    intro hB
    obtain ⟨R, hR⟩ := hB.subset_closedBall 0
    refine HalfPlaneSep.not_isBounded_H_diff_fillH hA.isClosed hA.isBounded
      ((isBounded_closedBall (x := (0 : ℂ)) (r := R + M)).subset fun w hw => ?_)
    have h1 := hR ⟨w, hw, rfl⟩
    have h2 := hM w (show (0 : ℝ) ≤ w.im from le_of_lt (show (0 : ℝ) < w.im from hw.1))
    rw [mem_closedBall_zero_iff] at h1 ⊢
    calc ‖w‖ ≤ ‖ψ w‖ + ‖ψ w - w‖ := by
          have := norm_sub_le (ψ w) (ψ w - w); rwa [sub_sub_cancel] at this
      _ ≤ R + M := add_le_add h1 h2
  refine HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hPc.isClosed hX hXu ?_
  rintro _ ⟨w, hw, rfl⟩
  have hwD : ψ w ∈ activeDomain η₁ s₀ η₂ t₀ := hbij.mapsTo hw.1
  have hDK : activeDomain η₁ s₀ η₂ t₀ ∩ prefixSet η₁ s₀ η₂ t₀ = ∅ := by
    rw [activeDomain_eq hK]
    ext z
    simp only [mem_inter_iff, Set.mem_sdiff, mem_empty_iff_false, iff_false, not_and]
    exact fun hz hzK => hz.2 (mem_fillH_of_mem_closure hz.1 (subset_closure hzK))
  refine ⟨(activeDomain_eq hK ▸ hwD).1, ?_⟩
  rintro (⟨s, hs, hsw⟩ | hw2)
  · -- `ψ w = η₁ s`: either `s ≤ s₀` (on `K`) or `s = s₀ + r`, and then `w = Γ r`
    by_cases hss : s ≤ s₀
    · exact (Set.eq_empty_iff_forall_notMem.1 hDK) _ ⟨hwD, Or.inl ⟨s, ⟨zero_le, hss⟩, hsw⟩⟩
    · push Not at hss
      set r := s - s₀ with hr
      have hsr : s = s₀ + r := by rw [hr, add_tsub_cancel_of_le hss.le]
      have hrt : r ∈ Icc 0 t := ⟨zero_le, by
        have := hs.2; rw [hsr] at this; exact le_of_add_le_add_left this⟩
      have hΓw : ψ (Γ r) = ψ w := by rw [hΓψ r hrt, ← hsr, hsw]
      have hΓrH : Γ r ∈ H := hC.mem_H_of_inv_mem (by rw [hΓw]; exact hwD)
      have hwr : w = Γ r := hbij.injOn hw.1 hΓrH hΓw.symm
      exact hw.2 (mem_fillH_of_mem_closure hw.1 (subset_closure ⟨r, hrt, hwr.symm⟩))
  · exact (Set.eq_empty_iff_forall_notMem.1 hDK) _ ⟨hwD, Or.inr hw2⟩

end ChartPath

/-! ### Proposition 6.12 for the mapped continuation -/

/-- A value adherent along good times from the left: if `f` is continuous at `b` within `{s ≤ ζ}` and every left
neighbourhood `(c, b)`, `c ≥ a`, contains a time `s` with `f s ∈ X`, then `f b ∈ closure X`. -/
theorem mem_closure_of_left {f : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {X : Set ℂ} {a b : ℝ≥0} (hab : a < b)
    (hbζ : (b : ℝ≥0∞) ≤ ζ) (hf : ContinuousWithinAt f {s | (s : ℝ≥0∞) ≤ ζ} b)
    (hgood : ∀ c : ℝ≥0, a ≤ c → c < b → ∃ s ∈ Ioo c b, f s ∈ X) : f b ∈ closure X := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hf ε hε
  set c : ℝ≥0 := max a (((b : ℝ) - δ / 2).toNNReal) with hc
  have hb0 : 0 < b := lt_of_le_of_lt zero_le hab
  have hcb : c < b := by
    refine max_lt hab ?_
    have h := (Real.toNNReal_lt_toNNReal_iff (NNReal.coe_pos.2 hb0)).2
      (show (b : ℝ) - δ / 2 < b by linarith)
    rwa [Real.toNNReal_coe] at h
  obtain ⟨r, hr, hrX⟩ := hgood c (le_max_left _ _) hcb
  have hrζ : (r : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hr.2.le).trans hbζ
  refine ⟨f r, hrX, ?_⟩
  rw [dist_comm]
  refine hδε hrζ ?_
  have h1 : (b : ℝ) - δ / 2 < r := by
    have h2 : (((b : ℝ) - δ / 2).toNNReal : ℝ) < r :=
      NNReal.coe_lt_coe.2 (lt_of_le_of_lt (le_max_right _ _) hr.1)
    exact lt_of_le_of_lt (Real.le_coe_toNNReal _) h2
  have h3 : (r : ℝ) < b := NNReal.coe_lt_coe.2 hr.2
  rw [NNReal.dist_eq, abs_lt]
  constructor <;> linarith

section Criteria

variable {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} {Γ : ℝ≥0 → ℂ}

/-- The standing deterministic hypotheses on the first path at a first contact: simple prefixes, real seed,
confinement (Lemma 7.7), the Loewner tip property and density of interior times of the original trace. -/
structure IsContinuationGood (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞)
    (t₀ : ℝ≥0) : Prop where
  firstContact : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀
  injOn₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}
  injOn₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂}
  continuousOn₁ : ContinuousOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}
  continuousOn₂ : ContinuousOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂}
  seed₁ : (η₁ 0).im = 0
  conf : ∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ closure (activeDomain η₁ s₀ η₂ t₀)
  tip : ∀ u s : ℝ≥0, u < s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ closure (H \ fillH (η₁ '' Icc 0 u))
  dense : ∀ a b : ℝ≥0, a < b → (b : ℝ≥0∞) ≤ ζ₁ → ∃ s ∈ Ioo a b, η₁ s ∈ H

namespace IsContinuationGood

variable (hg : IsContinuationGood η₁ ζ₁ s₀ η₂ ζ₂ t₀)
include hg

theorem continuousOn₁_Icc {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ ζ₁) : ContinuousOn η₁ (Icc 0 u) :=
  hg.continuousOn₁.mono fun _ hr => (ENNReal.coe_le_coe.2 hr.2).trans hu

theorem continuousOn₂_Icc : ContinuousOn η₂ (Icc 0 t₀) :=
  hg.continuousOn₂.mono fun _ hr => (ENNReal.coe_le_coe.2 hr.2).trans hg.firstContact.2.1

theorem isClosed_prefixSet : IsClosed (prefixSet η₁ s₀ η₂ t₀) :=
  (isCompact_prefixSet (hg.continuousOn₁_Icc hg.firstContact.1) hg.continuousOn₂_Icc).isClosed

/-- A continuation point in `ℍ` is in the active domain. -/
theorem mem_activeDomain {s : ℝ≥0} (hs : s₀ < s) (hsζ : (s : ℝ≥0∞) ≤ ζ₁) (hsH : η₁ s ∈ H) :
    η₁ s ∈ activeDomain η₁ s₀ η₂ t₀ := by
  rw [activeDomain_eq hg.isClosed_prefixSet]
  exact mem_activeDomain_of_mem_H hg.firstContact hg.injOn₁ hg.injOn₂
    (hg.continuousOn₁_Icc hg.firstContact.1) hg.continuousOn₂_Icc hs hsζ (hg.conf s hs.le hsζ) hsH

/-- The chart path is in `ℍ` at every positive time at which the continuation is. -/
theorem chartPath_mem_H (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {r : ℝ≥0} (hr : 0 < r)
    (hrζ : ((s₀ + r : ℝ≥0) : ℝ≥0∞) ≤ ζ₁) (hΓψ : ψ (Γ r) = η₁ (s₀ + r)) (hH : η₁ (s₀ + r) ∈ H) :
    Γ r ∈ H :=
  (chartPath_eq_fwd hC hΓψ (hg.mem_activeDomain (lt_add_of_pos_right _ hr) hrζ hH)).2

/-- **Criterion (a) for the chart path** at time `t`: every later point `Γ r`, `t < r ≤ S`, is adherent to the
unbounded domain of `Γ([0, t])`. -/
theorem chartPath_mem_closure (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {S : ℝ≥0}
    (hSζ : ((s₀ + S : ℝ≥0) : ℝ≥0∞) ≤ ζ₁) (hΓc : ContinuousOn Γ (Icc 0 S))
    (hΓψ : ∀ r ∈ Icc 0 S, ψ (Γ r) = η₁ (s₀ + r)) {t r : ℝ≥0} (htr : t < r) (hrS : r ≤ S) :
    Γ r ∈ closure (H \ fillH (Γ '' Icc 0 t)) := by
  have hζ : ∀ x : ℝ≥0, x ≤ S → ((s₀ + x : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ := fun x hx =>
    (ENNReal.coe_le_coe.2 (add_le_add le_rfl hx)).trans hSζ
  have hgood : ∀ x : ℝ≥0, t < x → x ≤ S → η₁ (s₀ + x) ∈ H →
      Γ x ∈ H \ fillH (Γ '' Icc 0 t) := by
    intro x htx hxS hxH
    have hxD := hg.mem_activeDomain (lt_add_of_pos_right _ (lt_of_le_of_lt zero_le htx)) (hζ x hxS) hxH
    have hrel := mem_relDomain hg.firstContact hg.injOn₁ hg.injOn₂ hg.continuousOn₁ hg.continuousOn₂_Icc
      hg.seed₁ (le_self_add : s₀ ≤ s₀ + t) ((add_lt_add_iff_left s₀).2 htx) (hζ x hxS)
      (hg.conf _ le_self_add (hζ x hxS)) (hg.tip _ _ ((add_lt_add_iff_left s₀).2 htx) (hζ x hxS)) hxH
    rw [(chartPath_eq_fwd hC (hΓψ x ⟨zero_le, hxS⟩) hxD).1]
    have htS : t ≤ S := htx.le.trans hxS
    exact fwd_image_relDomain_subset hC hg.isClosed_prefixSet (hg.continuousOn₁_Icc (hζ t htS))
      hg.continuousOn₂_Icc (hΓc.mono (Icc_subset_Icc_right htS))
      (fun y hy => hΓψ y ⟨zero_le, hy.2.trans htS⟩) ⟨_, hrel, rfl⟩
  by_cases hrH : η₁ (s₀ + r) ∈ H
  · exact subset_closure (hgood r htr hrS hrH)
  -- a real contact: approximate from the left by interior times
  refine mem_closure_of_left (ζ := (S : ℝ≥0∞)) htr (ENNReal.coe_le_coe.2 hrS)
    ((hΓc r ⟨zero_le, hrS⟩).mono fun x hx => ⟨zero_le, ENNReal.coe_le_coe.1 hx⟩) fun c htc hcr => ?_
  obtain ⟨s, hs, hsH⟩ := hg.dense (s₀ + c) (s₀ + r) ((add_lt_add_iff_left s₀).2 hcr) (hζ r hrS)
  have hcs : s₀ ≤ s := le_self_add.trans hs.1.le
  refine ⟨s - s₀, ⟨?_, ?_⟩, ?_⟩
  · exact lt_tsub_iff_left.2 hs.1
  · exact (tsub_lt_iff_left hcs).2 hs.2
  · have hx : s₀ + (s - s₀) = s := add_tsub_cancel_of_le hcs
    have hxS : s - s₀ ≤ S := ((tsub_lt_iff_left hcs).2 hs.2).le.trans hrS
    exact hgood _ (htc.trans_lt (lt_tsub_iff_left.2 hs.1)) hxS (by rw [hx]; exact hsH)

end IsContinuationGood

end Criteria

/-! ### The relative capacity clock -/

/-- A path on `ℝ≥0` read on `ℝ` (constant on `(-∞, 0]`). -/
def realPath (Γ : ℝ≥0 → ℂ) : ℝ → ℂ := fun r => Γ r.toNNReal

theorem realPath_image_Icc (Γ : ℝ≥0 → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    realPath Γ '' Icc 0 t = Γ '' Icc 0 t.toNNReal := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hr.2⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ⟨x.2, ?_⟩, by simp [realPath]⟩
    have := NNReal.coe_le_coe.2 hx.2
    rwa [Real.coe_toNNReal _ ht] at this

theorem realPath_coe (Γ : ℝ≥0 → ℂ) (x : ℝ≥0) : realPath Γ x = Γ x := by simp [realPath]

/-- **The relative capacity clock** (W8.1) of a chart path: half the half-plane capacity of the filling of
`Γ([0, r])`. -/
def chartClock (Γ : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ := ConformalImage.hcapSet (fillH (Γ '' Icc 0 r)) / 2

section Clock

variable {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} {Γ : ℝ≥0 → ℂ}

namespace IsContinuationGood

variable (hg : IsContinuationGood η₁ ζ₁ s₀ η₂ ζ₂ t₀)
include hg

/-- **Aux. lemma 76 and (W8.1) on `[0, S]`**: the chart path of the continuation `η₁(s₀ + ·)` satisfies the
hypotheses of Proposition 6.12, so it is generated by a continuous Loewner driver after the relative capacity clock
`chartClock Γ`, which is continuous and strictly increasing on `[0, S]` and vanishes at `0`. -/
theorem exists_driver_chartClock (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {S : ℝ≥0} (hS : 0 < S)
    (hSζ : ((s₀ + S : ℝ≥0) : ℝ≥0∞) ≤ ζ₁) (hΓc : ContinuousOn Γ (Icc 0 S))
    (hΓH : ∀ r ∈ Icc 0 S, Γ r ∈ Hbar) (hΓψ : ∀ r ∈ Icc 0 S, ψ (Γ r) = η₁ (s₀ + r)) (hΓ0 : Γ 0 = 0) :
    chartClock Γ 0 = 0 ∧ StrictMonoOn (chartClock Γ) (Icc 0 S) ∧ ContinuousOn (chartClock Γ) (Icc 0 S) ∧
      ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∀ t ∈ Icc 0 S, 0 ≤ chartClock Γ t ∧
        QuantumZipper.fwdHull W (chartClock Γ t) = fillH (Γ '' Icc 0 t) := by
  have hS' : (0 : ℝ) < S := NNReal.coe_pos.2 hS
  have hζ : ∀ x : ℝ≥0, x ≤ S → ((s₀ + x : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ := fun x hx =>
    (ENNReal.coe_le_coe.2 (add_le_add le_rfl hx)).trans hSζ
  have hmaps : MapsTo Real.toNNReal (Icc 0 (S : ℝ)) (Icc 0 S) := fun r hr =>
    ⟨zero_le, by simpa using Real.toNNReal_le_toNNReal hr.2⟩
  have hc : ContinuousOn (realPath Γ) (Icc 0 (S : ℝ)) :=
    hΓc.comp continuous_real_toNNReal.continuousOn hmaps
  have hΓi : InjOn Γ (Icc 0 S) := chartPath_injOn hΓψ fun a ha b hb hab =>
    add_left_cancel (hg.injOn₁ (hζ a ha.2) (hζ b hb.2) hab)
  have hinj : InjOn (realPath Γ) (Icc 0 (S : ℝ)) := fun a ha b hb hab => by
    have := hΓi (hmaps ha) (hmaps hb) hab
    rw [← Real.coe_toNNReal a ha.1, ← Real.coe_toNNReal b hb.1, this]
  have hH : MapsTo (realPath Γ) (Icc 0 (S : ℝ)) Hbar := fun r hr => hΓH _ (hmaps hr)
  have h0 : realPath Γ 0 = 0 := by simp [realPath, hΓ0]
  have ha : Sec6.DrivingCriterionA (realPath Γ) S := by
    rintro t ⟨ht0, htS⟩ _ ⟨r, hr, rfl⟩
    rw [realPath_image_Icc Γ ht0.le]
    have htr : t.toNNReal < r.toNNReal := (Real.toNNReal_lt_toNNReal_iff (ht0.trans hr.1)).2 hr.1
    exact hg.chartPath_mem_closure hC hSζ hΓc hΓψ htr (hmaps ⟨(ht0.trans hr.1).le, hr.2⟩).2
  have hR : interior {u ∈ Ioo 0 (S : ℝ) | (realPath Γ u).im = 0} = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
    have hx0 : 0 < x := (interior_subset hx : x ∈ _).1.1
    set a : ℝ := max (x / 2) (x - ε / 2) with ha
    have ha0 : 0 < a := lt_of_lt_of_le (half_pos hx0) (le_max_left _ _)
    have hax : a < x := max_lt (half_lt_self hx0) (by linarith)
    have hxS : x.toNNReal ≤ S := by
      have := (interior_subset hx : x ∈ _).1.2
      exact (Real.toNNReal_le_iff_le_coe).2 this.le
    obtain ⟨s, hs, hsH⟩ := hg.dense (s₀ + a.toNNReal) (s₀ + x.toNNReal)
      ((add_lt_add_iff_left s₀).2 ((Real.toNNReal_lt_toNNReal_iff hx0).2 hax)) (hζ _ hxS)
    have hcs : s₀ ≤ s := le_self_add.trans hs.1.le
    set r : ℝ≥0 := s - s₀ with hr
    have hsr : s₀ + r = s := add_tsub_cancel_of_le hcs
    have har : a.toNNReal < r := lt_tsub_iff_left.2 hs.1
    have hrx : r < x.toNNReal := (tsub_lt_iff_left hcs).2 hs.2
    have har' : a < r := by
      have := NNReal.coe_lt_coe.2 har; rwa [Real.coe_toNNReal _ ha0.le] at this
    have hrx' : (r : ℝ) < x := by
      have := NNReal.coe_lt_coe.2 hrx; rwa [Real.coe_toNNReal _ hx0.le] at this
    have hmem : (r : ℝ) ∈ ball x ε := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right (x / 2) (x - ε / 2)]
    have hreal := (hball hmem).2
    rw [realPath_coe] at hreal
    have hrS : r ≤ S := hrx.le.trans hxS
    have hΓrH := hg.chartPath_mem_H hC (lt_of_le_of_lt zero_le har) (hζ r hrS) (hΓψ r ⟨zero_le, hrS⟩)
      (by rw [hsr]; exact hsH)
    exact absurd hreal (ne_of_gt (show (0 : ℝ) < (Γ r).im from hΓrH))
  have hb : Sec6.DrivingCriterionB (realPath Γ) S := Sec6.drivingCriterionB_of_injOn hinj hR
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hσK⟩ := Sec6.exists_driver_of_drivingCriteria hS' hc h0
    (Sec6.hasSimpleApproxOn_of_injOn hS' hc hinj h0 hH) ha hb
  -- the clock is `σ` on `[0, S]`
  have hclock : ∀ t ∈ Icc 0 S, chartClock Γ t = σ t := by
    intro t ht
    have ht' : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.2, NNReal.coe_le_coe.2 ht.2⟩
    obtain ⟨hσt, hK, -⟩ := hσK t ht'
    rw [realPath_image_Icc Γ (NNReal.coe_nonneg t), Real.toNNReal_coe] at hK
    have := hcap_fwdHull hW hW0 hσt
    unfold chartClock
    rw [← hK, ConformalImage.hcapSet_eq (isHPHull_fwdHull hW hσt), this]
    ring
  refine ⟨by rw [hclock 0 ⟨le_rfl, zero_le⟩]; exact_mod_cast hσ0, fun a ha b hb hab => ?_, ?_,
    W, hW, hW0, fun t ht => ?_⟩
  · rw [hclock a ha, hclock b hb]
    exact hσm ⟨a.2, NNReal.coe_le_coe.2 ha.2⟩ ⟨b.2, NNReal.coe_le_coe.2 hb.2⟩ (NNReal.coe_lt_coe.2 hab)
  · refine (hσc.comp NNReal.continuous_coe.continuousOn fun t ht =>
      ⟨t.2, NNReal.coe_le_coe.2 ht.2⟩).congr fun t ht => hclock t ht
  · have ht' : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.2, NNReal.coe_le_coe.2 ht.2⟩
    obtain ⟨hσt, hK, -⟩ := hσK t ht'
    rw [realPath_image_Icc Γ (NNReal.coe_nonneg t), Real.toNNReal_coe] at hK
    rw [hclock t ht]
    exact ⟨hσt, hK⟩

end IsContinuationGood

end Clock

end Restart

end InteractingSLE
