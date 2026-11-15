/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCollar

/-!
# R.7 gap equality from local boundary geometry

Packet PROVE-R7-GAPEQ; supplement §5.4, pp. 473–474. These are conditional reductions of
`R7StopIn.PocketGapEq`, not unconditional assertions about the selected mixed pockets.
`HasExteriorCollar` is the local forbidden-side geometry; `HasOldAllowedCover` allows adjoining
the forbidden exterior before covering the old local boundary. Both remaining geometric
inputs are stated explicitly. Aux. 38 and Aux. 42 discharge their endpoint consequences.
The mixed case still takes the separately named `BarrierAttachConst` input. R48 is respected.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace InteractingSLE.Sec7.R7GapEq

open Sec6 R7StopIn

/-- A neighborhood of `p` is covered by the pocket, its forbidden exterior, and the simple
boundary set `K`. This is the local geometry required at an outer side point. -/
def HasExteriorCollar (C F K : Set ℂ) (p : ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ p ∈ U ∧ U ⊆ C ∪ F ∪ K

/-- Near `p`, the pocket boundary is covered by a set visited strictly before `t`.
This is a sufficient local geometric input for the fixed-side Aux. 38 argument. -/
def HasOldBoundaryCover (η : ℝ → ℂ) (C : Set ℂ) (p : ℂ) (t : ℝ) : Prop :=
  ∃ r : ℝ, 0 ≤ r ∧ r < t ∧ ∃ U J : Set ℂ, IsOpen U ∧ p ∈ U ∧
    J ⊆ η '' Icc 0 r ∧ frontier C ∩ U ⊆ J

/-- The pocket can be enlarged to an open `V` using only forbidden points and simple boundary
points, and the boundary of `V` near `p` is both old and simple. This allows the shared entrance
corner without requiring the unvisited outer wall itself to be old. -/
def HasOldAllowedCover (η : ℝ → ℂ) (C F K : Set ℂ) (p : ℂ) (t : ℝ) : Prop :=
  ∃ V : Set ℂ, IsOpen V ∧ C ⊆ V ∧ V ⊆ C ∪ F ∪ K ∧
    ∃ r : ℝ, 0 ≤ r ∧ r < t ∧ ∃ U J : Set ℂ, IsOpen U ∧ p ∈ U ∧
      J ⊆ η '' Icc 0 r ∧ frontier V ∩ U ⊆ J ∩ K

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C F K O : Set ℂ} {B : ℝ → ℂ} {τ σ : ℝ}

/-- An old cover of the actual pocket is an allowed cover, with `V = C`. -/
theorem HasOldBoundaryCover.toAllowed {p : ℂ} {t : ℝ}
    (h : HasOldBoundaryCover η C p t) (hCo : IsOpen C) (hfrK : frontier C ⊆ K) :
    HasOldAllowedCover η C F K p t := by
  obtain ⟨r, hr, hrt, U, J, hU, hp, hJ, hfr⟩ := h
  exact ⟨C, hCo, Subset.rfl, fun _ hpC => Or.inl (Or.inl hpC), r, hr, hrt,
    U, J, hU, hp, hJ, fun _ hq => ⟨hfr hq, hfrK hq.1⟩⟩

/-- Outside the contained barrier, every frontier point has a forbidden-side collar; hence
every boundary contact in a nontrivial no-pocket interval is on the contained barrier. -/
theorem mem_barrier_at_gap {A : Set ℂ}
    (hc : ContinuousOn η (Ici 0))
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ s, 0 ≤ s → η s ∉ F) (hfr : frontier C ⊆ A ∪ O)
    (houter : ∀ p ∈ O, HasExteriorCollar C F K p)
    {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hgap : ∀ s ∈ Icc a b, η s ∉ C) (ht : t ∈ Icc a b) (htfr : η t ∈ frontier C) :
    η t ∈ A := by
  rcases hfr htfr with hA | hO
  · exact hA
  · obtain ⟨U, hU, htU, hcollar⟩ := houter _ hO
    exact False.elim (not_mem_collar_at_gap hc h42 havoid ha hab hgap ht hU hcollar htU)

/-- Aux. 38 excludes a gap endpoint with an old local boundary cover. -/
theorem not_hasOldBoundaryCover_at_gap
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hCo : IsOpen C)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K) (hfrK : frontier C ⊆ K)
    {a b t s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hgap : ∀ u ∈ Icc a b, η u ∉ C)
    (ht : t ∈ Icc a b) (hvis : t ∈ closure {u | s < u ∧ η u ∈ C}) :
    ¬ HasOldBoundaryCover η C (η t) t := by
  rintro ⟨r, hr, hrt, U, J, hU, htU, hJ, hfrJ⟩
  exact not_old_boundary_collar_at_gap hη hW hW0 hCo h42 ha hab hgap ht hvis hr hrt
    hJ hU hfrJ (fun _ hp => hfrK hp.1) htU

/-- The old-side exclusion remains valid after adjoining forbidden points and simple arcs:
an open part of such an enlargement cannot be visited during a positive gap, by the outer
collar exclusion. Apply the already proved Aux. 38 argument to this enlargement. -/
theorem not_hasOldAllowedCover_at_gap
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    {a b t s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hgap : ∀ u ∈ Icc a b, η u ∉ C)
    (ht : t ∈ Icc a b) (hvis : t ∈ closure {u | s < u ∧ η u ∈ C}) :
    ¬ HasOldAllowedCover η C F K (η t) t := by
  rintro ⟨V, hVo, hCV, hV, r, hr, hrt, U, J, hU, htU, hJ, hfr⟩
  have hgapV : ∀ u ∈ Icc a b, η u ∉ V := fun u hu =>
    not_mem_collar_at_gap hη.2.1 h42 havoid ha hab hgap hu hVo hV
  have hvisV : t ∈ closure {u | s < u ∧ η u ∈ V} :=
    closure_mono (s := {u | s < u ∧ η u ∈ C}) (t := {u | s < u ∧ η u ∈ V})
      (fun u hu => ⟨hu.1, hCV hu.2⟩) hvis
  exact not_old_boundary_collar_at_gap hη hW hW0 hVo h42 ha hab hgapV ht hvisV
    hr hrt hJ hU (fun _ hq => (hfr hq).1) (fun _ hq => (hfr hq).2) htU

/-- **Mixed bounded pocket, conditional reduction.** All strict old contacts of the contained
barrier are assumed to have the displayed local old-boundary cover. This geometric input, the
outer collars, and Aux. 37 along the contained barrier imply the existing `PocketGapEq` exactly.
No continuity of the attachment parameter is assumed. -/
theorem pocketGapEq_of_collars
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hCo : IsOpen C)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (hfr : frontier C ⊆ B '' Icc 0 1 ∪ O)
    (houter : ∀ p ∈ O, HasExteriorCollar C F K p)
    (hBi : InjOn B (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) (hτf : η τ ∉ η '' Ico 0 τ)
    (hAC : BarrierAttachConst η C B τ σ)
    (hOld : ∀ t ∈ Ioo τ σ, ∀ v ∈ Icc (0 : ℝ) 1,
      firstVisit (fun s => η '' Icc 0 s) B t < v → η t = B v →
        HasOldAllowedCover η C F K (η t) t) :
    PocketGapEq η C τ σ := by
  have hfirst : firstVisit (fun s => η '' Icc 0 s) B τ = 1 :=
    R16.firstVisitParam_eq_of_fresh hBi hrev hτ0 ⟨zero_le_one, le_rfl⟩ hτ hτf
  intro a b hτa hab hbσ hgap hb ha
  have ha0 : 0 ≤ a := hτ0.trans hτa
  have endpoint : ∀ t ∈ Icc a b,
      (t = τ ∨ t ∈ closure {u | τ < u ∧ η u ∈ C}) →
        η t = B (firstVisit (fun s => η '' Icc 0 s) B t) := by
    intro t ht hvis
    rcases hvis with htτ | hvis
    · rw [htτ, hfirst, hτ]
    have htfr : η t ∈ frontier C := by
      refine ⟨mem_closure_of_visits hη.2.1 hτ0 hvis, ?_⟩
      rw [hCo.interior_eq]
      exact hgap t ht
    obtain ⟨v, hv, hvt⟩ := mem_barrier_at_gap hη.2.1 h42 havoid hfr houter
      ha0 hab hgap ht htfr
    have huv : firstVisit (fun s => η '' Icc 0 s) B t ≤ v :=
      firstVisit_le hv ⟨t, ⟨ha0.trans ht.1, le_rfl⟩, hvt.symm⟩
    rcases huv.eq_or_lt with he | he
    · rw [he, hvt]
    have htτ : τ < t := by
      refine lt_of_le_of_ne (hτa.trans ht.1) ?_
      intro heq
      have hv1 := hBi hv ⟨zero_le_one, le_rfl⟩ (hvt.trans (heq ▸ hτ))
      rw [heq.symm, hfirst, hv1] at he
      exact lt_irrefl _ he
    exact False.elim (not_hasOldAllowedCover_at_gap hη hW hW0 h42 havoid
      ha0 hab hgap ht hvis (hOld t ⟨htτ, ht.2.trans_lt hbσ⟩ v hv he hvt.symm))
  have haeq := endpoint a ⟨le_rfl, hab.le⟩ ha
  have hbvis : b ∈ closure {u | τ < u ∧ η u ∈ C} :=
    closure_mono (s := {u | a < u ∧ η u ∈ C}) (t := {u | τ < u ∧ η u ∈ C})
      (fun u hu => ⟨hτa.trans_lt hu.1, hu.2⟩) hb
  have hbeq := endpoint b ⟨hab.le, le_rfl⟩ (Or.inr hbvis)
  rw [haeq, hbeq, hAC a b hτa hab.le hbσ hgap]

/-- **Two outer sides, bounded pocket, conditional reduction.** If every frontier point other
than the two pocket corners has an exterior collar, a no-pocket interval has both endpoints at
the entrance corner. Freshness excludes the target corner before `σ`. No attachment input is
needed in this case. -/
theorem pocketGapEq_of_outerCollars
    (hc : ContinuousOn η (Ici 0)) (hCo : IsOpen C)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F) {x y : ℂ}
    (hfr : frontier C ⊆ ({x, y} : Set ℂ) ∪ O)
    (houter : ∀ p ∈ O, HasExteriorCollar C F K p)
    (hτ0 : 0 ≤ τ) (hτ : η τ = y) (hxf : x ∉ η '' Ico 0 σ) :
    PocketGapEq η C τ σ := by
  intro a b hτa hab hbσ hgap hb ha
  have ha0 := hτ0.trans hτa
  have endpoint : ∀ t ∈ Icc a b, η t ∈ frontier C → η t = y := by
    intro t ht htfr
    have hp := mem_barrier_at_gap hc h42 havoid hfr houter ha0 hab hgap ht htfr
    rcases hp with hx | hy
    · exact False.elim (hxf ⟨t, ⟨ha0.trans ht.1, ht.2.trans_lt hbσ⟩, hx⟩)
    · exact hy
  have haeq : η a = y := by
    rcases ha with ha | ha
    · rw [ha, hτ]
    · apply endpoint a ⟨le_rfl, hab.le⟩
      refine ⟨mem_closure_of_visits hc hτ0 ha, ?_⟩
      rw [hCo.interior_eq]
      exact hgap a ⟨le_rfl, hab.le⟩
  have hbeq : η b = y := by
    apply endpoint b ⟨hab.le, le_rfl⟩
    refine ⟨mem_closure_of_visits hc ha0 hb, ?_⟩
    rw [hCo.interior_eq]
    exact hgap b ⟨hab.le, le_rfl⟩
  exact haeq.trans hbeq.symm

/-- **Two outer sides, target at infinity, conditional reduction.** The finite-plane frontier
has only the entrance corner and the collared open sides. -/
theorem pocketGapEqInf_of_outerCollars
    (hc : ContinuousOn η (Ici 0)) (hCo : IsOpen C)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F) {y : ℂ}
    (hfr : frontier C ⊆ ({y} : Set ℂ) ∪ O)
    (houter : ∀ p ∈ O, HasExteriorCollar C F K p)
    (hτ0 : 0 ≤ τ) (hτ : η τ = y) : PocketGapEqInf η C τ := by
  intro a b hτa hab hgap hb ha
  have ha0 := hτ0.trans hτa
  have endpoint : ∀ t ∈ Icc a b, η t ∈ frontier C → η t = y :=
    fun t ht htfr => mem_barrier_at_gap hc h42 havoid hfr houter ha0 hab hgap ht htfr
  have haeq : η a = y := by
    rcases ha with ha | ha
    · rw [ha, hτ]
    · apply endpoint a ⟨le_rfl, hab.le⟩
      refine ⟨mem_closure_of_visits hc hτ0 ha, ?_⟩
      rw [hCo.interior_eq]
      exact hgap a ⟨le_rfl, hab.le⟩
  have hbeq : η b = y := by
    apply endpoint b ⟨hab.le, le_rfl⟩
    refine ⟨mem_closure_of_visits hc ha0 hb, ?_⟩
    rw [hCo.interior_eq]
    exact hgap b ⟨hab.le, le_rfl⟩
  exact haeq.trans hbeq.symm

end InteractingSLE.Sec7.R7GapEq
