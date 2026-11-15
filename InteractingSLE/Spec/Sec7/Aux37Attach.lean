/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40Full
import InteractingSLE.Spec.Sec6.Aux40Inf

/-!
# Aux. lemma 37: the reduction of attachment constancy to countably many rational witnesses

Packet PROVE-STRIPSYS10. Specification §6.2, **Aux.** lemma 37 and its proof (`source/spec/p193-240.md` L80–L136,
pp. 197–200), in the repaired form of ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt` §1.2, "Aux. 37:
first-visit progress is already fresh").

> *Then, almost surely, for every interval `[a, b] ⊂ [τ, σ)` on which `η'([a, b]) ∩ C = ∅`, the two functions `u_i`
> are constant on `[a, b]`.*

The proof (p. 198–200) is a contradiction at countably many **rational witnesses**: "Suppose an attachment decreases
on such an interval. By continuity of `u_i`, choose rational counterflow times `a < r < s < b` on which it already
decreases, and choose rational incoming parameters `v < v₁ < v₂` such that `u_i(s) < v < v₁ < v₂ < u_i(r)` (PFI1).
They can be chosen inside one constant-angle piece of the selected open side. […] Use rational choices in (PFI1), the
finitely many angle pieces, and capped first-hit stops `T_v` before the localization horizon. Intersect their countably
many full-probability boundary-comparison events before choosing the witnesses pathwise. Any nontrivial attachment
progress yields one of these witnesses."

This file proves every step of that reduction except the field comparison at one witness:

* `continuousOn_firstVisit_Ici`: the first-visit attachment `u(t) = min {v : α(v) ∈ η([0, t])}` is continuous on
  `[τ₀, ∞)` as soon as every visited set from time `τ₀` on meets the arc and the visited parameters form the suffix
  `[u(t), 1]` (the landed `Sec6.continuousOn_firstVisit` is the case `τ₀ = 0`; in a pocket the arcs are met only from
  `τ = T(y₀)` on);
* `IsAttachWitness`: the rational witness (PFI1) on one side, with the avoidance of `C` on `[r, s]`;
* **`exists_rat_attachWitness`** (deterministic): in a reverse-contained pocket, if attachment constancy fails, there
  is a rational witness on one of the two sides whose parameters `v < v₁ < v₂` avoid any prescribed finite set of
  parameters (the angle-change points);
* `IsAttachWitness.arc_disjoint`, `IsAttachWitness.arc_subset`, `IsAttachWitness.firstVisitTime_mem`: at a witness the
  arc `J = α([v₁, v₂])` is unvisited at `r` and visited by `s`, and the first visit `T_v` of `α(v)` is in `(r, s]`;
* **`ae_attachmentConstancy_of_witness`**: for random pockets, attachment constancy holds almost surely as soon as
  every rational witness has probability zero;
* the same at the junction `∞` (`IsReversePocketInf`, last-visit attachments): `continuousOn_lastVisit_Ici`,
  `IsAttachWitnessInf`, **`exists_rat_attachWitnessInf`**, **`ae_attachmentConstancyInf_of_witness`**;
* **`false_of_side_germs`** (deterministic, (PFI2)–(PFI4)): along one approach filter to the collar of `J`, a
  function with the flow-side germ `ελ − θχ` in one chart and the counterflow-side germ `ελ' − πχ` in another, whose
  derivative-argument lifts differ by `2πk` there, cannot exist for `θ ∈ (−π/2, π/2)`.

What remains for Aux. lemma 37 is the field comparison at one rational witness (pp. 198–199): the marked flat clock
(the conditional harmonic mean of the central component is unchanged on `[r, T_v]`, where the counterflow avoids `C`),
the flow-side germ of that mean at `r` on the `C`-side collar of `J` (the marked single-piece boundary comparison), and
its counterflow-side germ at `T_v` (the contact-stop mean, Aux. lemma 36). With them, `false_of_side_germs` excludes
every witness, and `ae_attachmentConstancy_of_witness` gives Aux. lemma 37.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace InteractingSLE.Sec7.Aux37Attach

open Sec6

/-! ### Continuity of the first-visit attachment from a positive time on -/

section Continuity

variable {η α : ℝ → ℂ}

/-- **The first-visit attachment is continuous on `[τ₀, ∞)`** (Aux. lemma 37, first paragraph of the proof) when
every visited set from time `τ₀` on meets the arc and the visited parameters form the suffix `[u(t), 1]`. The landed
`Sec6.continuousOn_firstVisit` is the case `τ₀ = 0`; the proof is the same. -/
theorem continuousOn_firstVisit_Ici {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀) (hη : ContinuousOn η (Ici 0))
    (hα : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (hne : ∀ t ≥ τ₀, ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ η '' Icc 0 t)
    (hsuf : ∀ t ≥ τ₀, ∀ v ∈ Icc (0 : ℝ) 1,
      firstVisit (fun t => η '' Icc 0 t) α t ≤ v → α v ∈ η '' Icc 0 t) :
    ContinuousOn (firstVisit (fun t => η '' Icc 0 t) α) (Ici τ₀) := by
  set R : ℝ → Set ℂ := fun t => η '' Icc 0 t with hR
  set u := firstVisit R α with hu
  have hRc : ∀ t ≥ (0 : ℝ), IsClosed (R t) := fun t ht =>
    ((isCompact_Icc).image_of_continuousOn (hη.mono fun s hs => hs.1)).isClosed
  have hmem : ∀ t ≥ τ₀, u t ∈ Icc (0 : ℝ) 1 ∧ α (u t) ∈ R t := fun t ht =>
    firstVisit_mem hα (hRc t (hτ₀.trans ht)) (hne t ht)
  have hanti : AntitoneOn u (Ici τ₀) := fun s hs _ _ hst =>
    firstVisit_anti monotone_image_Icc hst (hne s hs)
  -- right continuity
  have hright : ∀ t ≥ τ₀, ∀ ε > 0, ∃ t' > t, u t - ε < u t' := by
    intro t ht ε hε
    by_contra hcon
    push Not at hcon
    set m := sSup (u '' Ioi t) with hm
    have hbdd : BddAbove (u '' Ioi t) := ⟨1, by
      rintro _ ⟨t', ht', rfl⟩; exact (hmem t' (ht.trans (le_of_lt ht'))).1.2⟩
    have hmle : m ≤ u t - ε := csSup_le ((nonempty_Ioi).image u) (by
      rintro _ ⟨t', ht', rfl⟩; exact hcon t' ht')
    have hvis : ∀ t'' > t, α m ∈ R t'' := by
      intro t'' ht''
      have hcl : IsClosed {v ∈ Icc (0 : ℝ) 1 | α v ∈ R t''} :=
        hα.preimage_isClosed_of_isClosed isClosed_Icc (hRc t'' (hτ₀.trans (ht.trans (le_of_lt ht''))))
      have hm' : m = sSup (u '' Ioc t t'') := by
        refine le_antisymm (csSup_le ((nonempty_Ioi).image u) ?_) (csSup_le_csSup hbdd
          ((nonempty_Ioc.2 ht'').image u) (image_mono Ioc_subset_Ioi_self))
        rintro _ ⟨t', ht', rfl⟩
        rcases le_or_gt t' t'' with h | h
        · exact le_csSup (hbdd.mono (image_mono Ioc_subset_Ioi_self)) ⟨t', ⟨ht', h⟩, rfl⟩
        · refine le_trans ?_ (le_csSup (hbdd.mono (image_mono Ioc_subset_Ioi_self))
            ⟨t'', ⟨ht'', le_rfl⟩, rfl⟩)
          exact hanti (ht.trans (le_of_lt ht'')) (ht.trans (le_of_lt ht')) h.le
      have hsub : u '' Ioc t t'' ⊆ {v ∈ Icc (0 : ℝ) 1 | α v ∈ R t''} := by
        rintro _ ⟨t', ht', rfl⟩
        have h1 := hmem t' (ht.trans (le_of_lt ht'.1))
        exact ⟨h1.1, monotone_image_Icc ht'.2 h1.2⟩
      have hmcl : m ∈ closure (u '' Ioc t t'') := by
        rw [hm']
        exact csSup_mem_closure ((nonempty_Ioc.2 ht'').image u)
          (hbdd.mono (image_mono Ioc_subset_Ioi_self))
      exact (hcl.closure_subset_iff.2 hsub hmcl).2
    have hmt : α m ∈ R t := mem_image_Icc_of_forall_lt hη (hτ₀.trans ht) hvis
    have hm01 : m ∈ Icc (0 : ℝ) 1 := by
      have hcl : IsClosed (Icc (0 : ℝ) 1) := isClosed_Icc
      refine hcl.closure_subset_iff.2 ?_ (csSup_mem_closure ((nonempty_Ioi).image u) hbdd)
      rintro _ ⟨t', ht', rfl⟩; exact (hmem t' (ht.trans (le_of_lt ht'))).1
    have := firstVisit_le hm01 hmt
    linarith
  -- left continuity
  have hleft : ∀ t > τ₀, ∀ ε > 0, ∃ t' ∈ Ico τ₀ t, u t' < u t + ε := by
    intro t ht ε hε
    by_contra hcon
    push Not at hcon
    have hu0 := hcon τ₀ ⟨le_rfl, ht⟩
    have h01 := (hmem τ₀ le_rfl).1
    have ht01 := (hmem t ht.le).1
    set w₁ := u t + ε / 3 with hw₁
    set w₂ := u t + 2 * ε / 3 with hw₂
    have hw₁m : w₁ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht01.1], by linarith [h01.2]⟩
    have hw₂m : w₂ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht01.1], by linarith [h01.2]⟩
    have hfresh : ∀ w ∈ Icc (0 : ℝ) 1, u t ≤ w → w < u t + ε → α w = η t := by
      intro w hw hwt hwε
      obtain ⟨s, hs, hsw⟩ := hsuf t ht.le w hw hwt
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [← hsw, h]
      · exfalso
        have hs' : α w ∈ R (max s τ₀) := monotone_image_Icc (le_max_left s τ₀) ⟨s, ⟨hs.1, le_rfl⟩, hsw⟩
        have h1 : u (max s τ₀) ≤ w := firstVisit_le hw hs'
        have h2 := hcon (max s τ₀) ⟨le_max_right _ _, max_lt h ht⟩
        linarith
    have he₁ := hfresh w₁ hw₁m (by linarith) (by linarith)
    have he₂ := hfresh w₂ hw₂m (by linarith) (by linarith)
    have := hαi hw₁m hw₂m (he₁.trans he₂.symm)
    linarith
  -- assemble
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨tR, htR, huR⟩ := hright t ht ε hε
  have hRbound : ∀ t' ∈ Ici τ₀, t ≤ t' → t' < tR → dist (u t') (u t) < ε := by
    intro t' ht' htt' ht'R
    have h1 : u t' ≤ u t := hanti ht ht' htt'
    have h2 : u tR ≤ u t' := hanti ht' (ht.trans (le_of_lt htR)) ht'R.le
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  rcases eq_or_lt_of_le (show τ₀ ≤ t from ht) with h0 | h0
  · refine ⟨tR - t, sub_pos.2 htR, fun t' ht' hd => ?_⟩
    have htt' : t ≤ t' := h0 ▸ ht'
    rw [Real.dist_eq, abs_lt] at hd
    exact hRbound t' ht' htt' (by linarith [hd.2])
  · obtain ⟨tL, htL, huL⟩ := hleft t h0 ε hε
    refine ⟨min (tR - t) (t - tL), lt_min (sub_pos.2 htR) (sub_pos.2 htL.2), fun t' ht' hd => ?_⟩
    rw [Real.dist_eq, abs_lt] at hd
    have hm1 := min_le_left (tR - t) (t - tL)
    have hm2 := min_le_right (tR - t) (t - tL)
    rcases le_total t t' with htt' | ht't
    · exact hRbound t' ht' htt' (by linarith [hd.2])
    · have h1 : u t ≤ u t' := hanti ht' ht ht't
      have h2 : u t' ≤ u tL := hanti htL.1 ht' (by linarith [hd.1])
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith

end Continuity

/-! ### Rational witnesses -/

section Witness

/-- **A rational witness of attachment progress** on the side `α` ((PFI1), p. 198): times `τ ≤ r < s < σ` between
which the counterflow avoids `C`, and incoming parameters `u(s) < v < v₁ < v₂ < u(r)`, `u` the first-visit
attachment. -/
def IsAttachWitness (η : ℝ → ℂ) (C : Set ℂ) (α : ℝ → ℂ) (τ σ r s v v₁ v₂ : ℝ) : Prop :=
  τ ≤ r ∧ r < s ∧ s < σ ∧ (∀ t ∈ Icc r s, η t ∉ C) ∧
    firstVisit (fun t => η '' Icc 0 t) α s < v ∧ v < v₁ ∧ v₁ < v₂ ∧
      v₂ < firstVisit (fun t => η '' Icc 0 t) α r

/-- In an open interval, three increasing rationals whose closed span avoids a prescribed finite set. -/
theorem exists_rat_triple_avoid {p q : ℝ} (hpq : p < q) (B : Finset ℝ) :
    ∃ v v₁ v₂ : ℚ, p < v ∧ (v : ℝ) < v₁ ∧ (v₁ : ℝ) < v₂ ∧ (v₂ : ℝ) < q ∧ ∀ b ∈ B, b ∉ Icc (v : ℝ) v₂ := by
  obtain ⟨x, hxI, hxB⟩ : (Ioo p q \ (B : Set ℝ)).Nonempty :=
    ((Ioo_infinite hpq).sdiff B.finite_toSet).nonempty
  have hO : IsOpen (Ioo p q \ (B : Set ℝ)) := isOpen_Ioo.sdiff B.finite_toSet.isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x ⟨hxI, hxB⟩
  obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn (show x - ε / 2 < x by linarith)
  obtain ⟨v₁, hv₁1, hv₁2⟩ := exists_rat_btwn (show x < x + ε / 2 by linarith)
  obtain ⟨v₂, hv₂1, hv₂2⟩ := exists_rat_btwn hv₁2
  have hsub : Icc (v : ℝ) v₂ ⊆ Metric.ball x ε := fun y hy => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hv : (v : ℝ) ∈ Ioo p q := (hball (hsub ⟨le_rfl, by linarith⟩)).1
  have hv₂ : (v₂ : ℝ) ∈ Ioo p q := (hball (hsub ⟨by linarith, le_rfl⟩)).1
  refine ⟨v, v₁, v₂, hv.1, by linarith, hv₂1, hv₂.2, fun b hb hbI => ?_⟩
  exact (hball (hsub hbI)).2 hb

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β α : ℝ → ℂ} {τ σ : ℝ}

/-- In a reverse-contained pocket, the arcs are met by every visited set from `τ = T(y₀)` on. -/
theorem exists_visited (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂) {t : ℝ} (ht : τ ≤ t) :
    ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ η '' Icc 0 t := by
  obtain ⟨-, -, -, h1, -, -⟩ := hP.arm hα
  exact ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [h1]; exact ⟨τ, ⟨hP.nonneg, ht⟩, hP.first_y⟩⟩

/-- **The first-visit attachments of a reverse-contained pocket are continuous on `[τ, ∞)`.** -/
theorem continuousOn_attach (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂) :
    ContinuousOn (firstVisit (fun t => η '' Icc 0 t) α) (Ici τ) := by
  obtain ⟨hc, hinj, -, -, -, hrev⟩ := hP.arm hα
  refine continuousOn_firstVisit_Ici hP.nonneg hP.trace.2.1 hc hinj (fun t ht => exists_visited hP hα ht)
    fun t ht v hv huv => ?_
  have hmem := firstVisit_mem (R := fun t => η '' Icc 0 t) hc hP.isClosed_range (exists_visited hP hα ht)
  exact hrev t _ hmem.1 v hv huv hmem.2

/-- The first-visit attachments are nonincreasing on `[τ, ∞)`. -/
theorem antitoneOn_attach (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂) :
    AntitoneOn (firstVisit (fun t => η '' Icc 0 t) α) (Ici τ) := fun _ hs _ _ hst =>
  firstVisit_anti monotone_image_Icc hst (exists_visited hP hα hs)

/-- **A strict decrease of an attachment on an interval avoiding `C` gives a rational witness** whose parameters
avoid a prescribed finite set (the choice in (PFI1)). -/
theorem exists_rat_attachWitness_of_lt (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂)
    (B : Finset ℝ) {a b : ℝ} (hτa : τ ≤ a) (hab : a ≤ b) (hbσ : b < σ) (hC : ∀ t ∈ Icc a b, η t ∉ C)
    (hlt : firstVisit (fun t => η '' Icc 0 t) α b < firstVisit (fun t => η '' Icc 0 t) α a) :
    ∃ r s v v₁ v₂ : ℚ, IsAttachWitness η C α τ σ r s v v₁ v₂ ∧ ∀ b ∈ B, b ∉ Icc (v : ℝ) v₂ := by
  set u := firstVisit (fun t => η '' Icc 0 t) α with hu
  have hab' : a < b := lt_of_le_of_ne hab fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  set δ := u a - u b with hδ
  have hδ0 : 0 < δ := sub_pos.2 hlt
  have hcont := continuousOn_attach hP hα
  -- a rational `r` just after `a`
  obtain ⟨ρ, hρ, hρa⟩ := Metric.continuousWithinAt_iff.1 (hcont a hτa) (δ / 3) (by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show a < min (a + ρ) b from lt_min (by linarith) hab')
  have hra : u a - δ / 3 < u r := by
    have h := hρa (show (r : ℝ) ∈ Ici τ from hτa.trans hr1.le) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left (a + ρ) b])
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  have hrb : (r : ℝ) < b := lt_of_lt_of_le hr2 (min_le_right _ _)
  -- a rational `s` just before `b`
  obtain ⟨ρ', hρ', hρb⟩ := Metric.continuousWithinAt_iff.1 (hcont b (hτa.trans hab)) (δ / 3) (by linarith)
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show max (r : ℝ) (b - ρ') < b from max_lt hrb (by linarith))
  have hsb : u s < u b + δ / 3 := by
    have h := hρb (show (s : ℝ) ∈ Ici τ from hτa.trans (hr1.le.trans (le_max_left _ _ |>.trans hs1.le))) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_right (r : ℝ) (b - ρ')])
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  have hrs : (r : ℝ) < s := lt_of_le_of_lt (le_max_left _ _) hs1
  obtain ⟨v, v₁, v₂, hv, hvv₁, hv₁v₂, hv₂, hB⟩ :=
    exists_rat_triple_avoid (show u s < u r by linarith) B
  refine ⟨r, s, v, v₁, v₂, ⟨hτa.trans hr1.le, hrs, hs2.trans hbσ, fun t ht => hC t ⟨hr1.le.trans ht.1,
    ht.2.trans hs2.le⟩, hv, hvv₁, hv₁v₂, hv₂⟩, hB⟩

/-- **Failure of attachment constancy gives a rational witness** on one of the two sides, with parameters avoiding a
prescribed finite set (Aux. lemma 37's proof: "Any nontrivial attachment progress yields one of these witnesses"). -/
theorem exists_rat_attachWitness (hP : IsReversePocket W η C α₁ α₂ β τ σ) (B : Finset ℝ)
    (hAC : ¬ AttachmentConstancy η C α₁ α₂ τ σ) :
    ∃ α : ℝ → ℂ, (α = α₁ ∨ α = α₂) ∧ ∃ r s v v₁ v₂ : ℚ, IsAttachWitness η C α τ σ r s v v₁ v₂ ∧
      ∀ b ∈ B, b ∉ Icc (v : ℝ) v₂ := by
  unfold AttachmentConstancy at hAC
  push Not at hAC
  obtain ⟨a, b, hτa, hab, hbσ, hC, hne⟩ := hAC
  have hlt : ∀ α' : ℝ → ℂ, (α' = α₁ ∨ α' = α₂) →
      firstVisit (fun t => η '' Icc 0 t) α' b ≠ firstVisit (fun t => η '' Icc 0 t) α' a →
      firstVisit (fun t => η '' Icc 0 t) α' b < firstVisit (fun t => η '' Icc 0 t) α' a :=
    fun α' hα' h => lt_of_le_of_ne (antitoneOn_attach hP hα' hτa (hτa.trans hab) hab) h
  by_cases h₁ : firstVisit (fun t => η '' Icc 0 t) α₁ b = firstVisit (fun t => η '' Icc 0 t) α₁ a
  · exact ⟨α₂, Or.inr rfl, exists_rat_attachWitness_of_lt hP (Or.inr rfl) B hτa hab hbσ hC
      (hlt α₂ (Or.inr rfl) (hne h₁))⟩
  · exact ⟨α₁, Or.inl rfl, exists_rat_attachWitness_of_lt hP (Or.inl rfl) B hτa hab hbσ hC
      (hlt α₁ (Or.inl rfl) h₁)⟩

variable {r s v v₁ v₂ : ℝ}

/-- At a witness, the arc `α([v, v₂])` is unvisited at time `r` ("The compact arc `J = α_i([v₁, v₂])` is disjoint
from `R_r`"). -/
theorem IsAttachWitness.arc_disjoint (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂)
    (hw : IsAttachWitness η C α τ σ r s v v₁ v₂) : ∀ x ∈ Icc v v₂, α x ∉ η '' Icc 0 r := by
  obtain ⟨hτr, hrs, hsσ, -, hsv, hvv₁, hv₁v₂, hv₂r⟩ := hw
  obtain ⟨hpos, hle, -, -, -⟩ := hP.chart hτr (hrs.trans hsσ) hα
  obtain ⟨hpos', -, -, -, -⟩ := hP.chart (hτr.trans hrs.le) hsσ hα
  intro x hx hxR
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have := firstVisit_le (R := fun t => η '' Icc 0 t) hx01 hxR
  linarith [hx.2]

/-- At a witness, the arc `α([v, 1])` is visited by time `s` ("is contained in `R_{T_v}`"). -/
theorem IsAttachWitness.arc_subset (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂)
    (hw : IsAttachWitness η C α τ σ r s v v₁ v₂) : ∀ x ∈ Icc v 1, α x ∈ η '' Icc 0 s := by
  obtain ⟨hτr, hrs, hsσ, -, hsv, -, -, -⟩ := hw
  obtain ⟨-, -, -, hsuf, -⟩ := hP.chart (hτr.trans hrs.le) hsσ hα
  exact fun x hx => hsuf x ⟨hsv.le.trans hx.1, hx.2⟩

/-- **The first visit `T_v` of `α(v)` at a witness** lies in `(r, s]`, and it is a fresh visit ("On (PFI1),
`r < T_v < s`"; R41: "this is a positive fresh interior tip"). -/
theorem IsAttachWitness.exists_firstVisitTime (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂)
    (hw : IsAttachWitness η C α τ σ r s v v₁ v₂) :
    ∃ T ∈ Ioc r s, η T = α v ∧ α v ∉ η '' Ico 0 T := by
  have hvR : α v ∈ η '' Icc 0 s := hw.arc_subset hP hα v ⟨le_rfl, by
    obtain ⟨hτr, hrs, hsσ, -, -, hvv₁, hv₁v₂, hv₂r⟩ := hw
    obtain ⟨-, hle, -, -, -⟩ := hP.chart hτr (hrs.trans hsσ) hα
    linarith⟩
  have hvr : α v ∉ η '' Icc 0 r := hw.arc_disjoint hP hα v ⟨le_rfl, by linarith [hw.2.2.2.2.2.1, hw.2.2.2.2.2.2.1]⟩
  set S := {t ∈ Icc (0 : ℝ) s | η t = α v} with hS
  have hSc : IsCompact S := by
    have hηc : ContinuousOn η (Icc 0 s) := hP.trace.2.1.mono fun _ ht => ht.1
    show IsCompact (Icc 0 s ∩ η ⁻¹' {α v})
    exact isCompact_Icc.of_isClosed_subset
      (hηc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, hte⟩ := hvR
    exact ⟨t, ht, hte⟩
  obtain ⟨T, hTS, hTmin⟩ := hSc.exists_isLeast hSne
  refine ⟨T, ⟨?_, hTS.1.2⟩, hTS.2, ?_⟩
  · by_contra hTr
    push Not at hTr
    exact hvr ⟨T, ⟨hTS.1.1, hTr⟩, hTS.2⟩
  · rintro ⟨t, ht, hte⟩
    have : T ≤ t := hTmin ⟨⟨ht.1, ht.2.le.trans hTS.1.2⟩, hte⟩
    linarith [ht.2]

end Witness

/-! ### Almost surely: countably many witnesses -/

section AE

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
  {α₁ α₂ β : Ω → ℝ → ℂ} {τ σ : Ω → ℝ}

/-- **Aux. lemma 37 from the exclusion of each rational witness** ("Intersect their countably many full-probability
boundary-comparison events before choosing the witnesses pathwise. Any nontrivial attachment progress yields one of
these witnesses"): for random reverse-contained pockets, if for every rational witness on either side (with
parameters off the random finite set `B ω` of angle-change points) the witness configuration has probability zero,
then attachment constancy holds almost surely. -/
theorem ae_attachmentConstancy_of_witness
    (hP : ∀ᵐ ω ∂P, IsReversePocket (W ω) (η ω) (C ω) (α₁ ω) (α₂ ω) (β ω) (τ ω) (σ ω)) (B : Ω → Finset ℝ)
    (h₁ : ∀ r s v v₁ v₂ : ℚ, ∀ᵐ ω ∂P,
      ¬ (IsAttachWitness (η ω) (C ω) (α₁ ω) (τ ω) (σ ω) r s v v₁ v₂ ∧ ∀ b ∈ B ω, b ∉ Icc (v : ℝ) v₂))
    (h₂ : ∀ r s v v₁ v₂ : ℚ, ∀ᵐ ω ∂P,
      ¬ (IsAttachWitness (η ω) (C ω) (α₂ ω) (τ ω) (σ ω) r s v v₁ v₂ ∧ ∀ b ∈ B ω, b ∉ Icc (v : ℝ) v₂)) :
    ∀ᵐ ω ∂P, AttachmentConstancy (η ω) (C ω) (α₁ ω) (α₂ ω) (τ ω) (σ ω) := by
  have h₁' : ∀ᵐ ω ∂P, ∀ r s v v₁ v₂ : ℚ,
      ¬ (IsAttachWitness (η ω) (C ω) (α₁ ω) (τ ω) (σ ω) r s v v₁ v₂ ∧ ∀ b ∈ B ω, b ∉ Icc (v : ℝ) v₂) := by
    simp only [ae_all_iff]
    exact h₁
  have h₂' : ∀ᵐ ω ∂P, ∀ r s v v₁ v₂ : ℚ,
      ¬ (IsAttachWitness (η ω) (C ω) (α₂ ω) (τ ω) (σ ω) r s v v₁ v₂ ∧ ∀ b ∈ B ω, b ∉ Icc (v : ℝ) v₂) := by
    simp only [ae_all_iff]
    exact h₂
  filter_upwards [hP, h₁', h₂'] with ω hPω hω₁ hω₂
  by_contra hAC
  obtain ⟨α, hα, r, s, v, v₁, v₂, hw, hB⟩ := exists_rat_attachWitness hPω (B ω) hAC
  rcases hα with rfl | rfl
  · exact hω₁ r s v v₁ v₂ ⟨hw, hB⟩
  · exact hω₂ r s v v₁ v₂ ⟨hw, hB⟩

end AE

/-! ### The phase contradiction along one approach -/

/-- **The contradiction of (PFI2)–(PFI4)** (pp. 199–200), along one approach filter `F` to the collar of `J`: a
function `M` (the unchanged harmonic mean of the central component) cannot have both the flow-side germ
`ελ − θχ` after the flow coordinate's derivative-argument correction `χ L_f` and the counterflow-side germ `ελ' − πχ`
after the counterflow coordinate's correction `χ L_c`, when the two derivative arguments differ by `2πk` along `F`
("Schwarz reflection makes the difference of the derivative argument lifts a constant integer multiple of `2π`"), with
`λ − λ' = πχ/2`, `χ > 0`, `ε = ±1` and `θ ∈ (−π/2, π/2)`. -/
theorem false_of_side_germs {F : Filter ℂ} [F.NeBot] {M Lf Lc : ℂ → ℝ} {χ lam lam' ε θ : ℝ} {k : ℤ}
    (hχ : 0 < χ) (hlam : lam - lam' = π * χ / 2) (hε : ε = 1 ∨ ε = -1) (hθ : θ ∈ Ioo (-(π / 2)) (π / 2))
    (hf : Tendsto (fun z => M z + χ * Lf z) F (𝓝 (ε * lam - θ * χ)))
    (hc : Tendsto (fun z => M z + χ * Lc z) F (𝓝 (ε * lam' - π * χ)))
    (hk : Tendsto (fun z => Lf z - Lc z) F (𝓝 (2 * π * k))) : False := by
  have h1 : Tendsto (fun z => χ * (Lf z - Lc z)) F (𝓝 ((ε * lam - θ * χ) - (ε * lam' - π * χ))) :=
    (hf.sub hc).congr fun z => by ring
  have h2 : Tendsto (fun z => χ * (Lf z - Lc z)) F (𝓝 (χ * (2 * π * k))) := hk.const_mul χ
  have heq := tendsto_nhds_unique h1 h2
  refine aux37_phase_ne hχ hlam hε hθ 0 k ?_
  push_cast
  linarith

/-! ### The junction at infinity -/

section Inf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ α : ℝ → ℂ} {τ : ℝ}

/-- **The attachment of a proper arm is continuous on `[τ₀, ∞)`** (Aux. lemma 37, first paragraph of the proof, for the
last-visit parameter `u(t) = max {v ≥ 0 : α(v) ∈ η([0, t])}` of an arm parametrized from `y₀` towards the junction at
`∞`): when every visited set from `τ₀` on contains `α(0)` and the visited parameters form the prefix `[0, u(t)]`. -/
theorem continuousOn_lastVisit_Ici {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀) (hη : ContinuousOn η (Ici 0))
    (hα : ContinuousOn α (Ici 0)) (hαi : InjOn α (Ici 0)) (hαt : Tendsto (fun v => ‖α v‖) atTop atTop)
    (h0 : ∀ t ≥ τ₀, α 0 ∈ η '' Icc 0 t)
    (hpre : ∀ t ≥ τ₀, ∀ v ∈ Ici (0 : ℝ), v ≤ lastVisit (fun t => η '' Icc 0 t) α t → α v ∈ η '' Icc 0 t) :
    ContinuousOn (lastVisit (fun t => η '' Icc 0 t) α) (Ici τ₀) := by
  set R : ℝ → Set ℂ := fun t => η '' Icc 0 t with hR
  set u := lastVisit R α with hu
  have hRc : ∀ t ≥ (0 : ℝ), IsCompact (R t) := fun t _ =>
    isCompact_Icc.image_of_continuousOn (hη.mono fun s hs => hs.1)
  have hne : ∀ t ≥ τ₀, ∃ v ∈ Ici (0 : ℝ), α v ∈ R t := fun t ht => ⟨0, mem_Ici.2 le_rfl, h0 t ht⟩
  have hmem : ∀ t ≥ τ₀, u t ∈ Ici (0 : ℝ) ∧ α (u t) ∈ R t := fun t ht =>
    lastVisit_mem hα hαt (hRc t (hτ₀.trans ht)) (hne t ht)
  have hmono : MonotoneOn u (Ici τ₀) := fun s hs t ht hst =>
    lastVisit_mono hαt monotone_image_Icc hst (hRc t (hτ₀.trans ht)).isBounded (hne s hs)
  -- right continuity
  have hright : ∀ t ≥ τ₀, ∀ ε > 0, ∃ t' > t, u t' < u t + ε := by
    intro t ht ε hε
    by_contra hcon
    push Not at hcon
    set m := sInf (u '' Ioi t) with hm
    have hbdd : BddBelow (u '' Ioi t) := ⟨0, by
      rintro _ ⟨t', ht', rfl⟩; exact (hmem t' (ht.trans (le_of_lt ht'))).1⟩
    have hmle : u t + ε ≤ m := le_csInf ((nonempty_Ioi).image u) (by
      rintro _ ⟨t', ht', rfl⟩; exact hcon t' ht')
    have hvis : ∀ t'' > t, α m ∈ R t'' := by
      intro t'' ht''
      have hcl : IsClosed {v ∈ Ici (0 : ℝ) | α v ∈ R t''} :=
        hα.preimage_isClosed_of_isClosed isClosed_Ici (hRc t'' (hτ₀.trans (ht.trans (le_of_lt ht'')))).isClosed
      have hm' : m = sInf (u '' Ioc t t'') := by
        refine le_antisymm (csInf_le_csInf hbdd ((nonempty_Ioc.2 ht'').image u)
          (image_mono Ioc_subset_Ioi_self)) (le_csInf ((nonempty_Ioi).image u) ?_)
        rintro _ ⟨t', ht', rfl⟩
        rcases le_or_gt t' t'' with h | h
        · exact csInf_le (hbdd.mono (image_mono Ioc_subset_Ioi_self)) ⟨t', ⟨ht', h⟩, rfl⟩
        · refine le_trans (csInf_le (hbdd.mono (image_mono Ioc_subset_Ioi_self))
            ⟨t'', ⟨ht'', le_rfl⟩, rfl⟩) ?_
          exact hmono (ht.trans (le_of_lt ht'')) (ht.trans (le_of_lt ht')) h.le
      have hsub : u '' Ioc t t'' ⊆ {v ∈ Ici (0 : ℝ) | α v ∈ R t''} := by
        rintro _ ⟨t', ht', rfl⟩
        have h1 := hmem t' (ht.trans (le_of_lt ht'.1))
        exact ⟨h1.1, monotone_image_Icc ht'.2 h1.2⟩
      have hmcl : m ∈ closure (u '' Ioc t t'') := by
        rw [hm']
        exact csInf_mem_closure ((nonempty_Ioc.2 ht'').image u)
          (hbdd.mono (image_mono Ioc_subset_Ioi_self))
      exact (hcl.closure_subset_iff.2 hsub hmcl).2
    have hmt : α m ∈ R t := mem_image_Icc_of_forall_lt hη (hτ₀.trans ht) hvis
    have hm0 : m ∈ Ici (0 : ℝ) := by
      refine isClosed_Ici.closure_subset_iff.2 ?_ (csInf_mem_closure ((nonempty_Ioi).image u) hbdd)
      rintro _ ⟨t', ht', rfl⟩; exact (hmem t' (ht.trans (le_of_lt ht'))).1
    have := le_lastVisit hαt (hRc t (hτ₀.trans ht)).isBounded hm0 hmt
    linarith
  -- left continuity
  have hleft : ∀ t > τ₀, ∀ ε > 0, ∃ t' ∈ Ico τ₀ t, u t - ε < u t' := by
    intro t ht ε hε
    by_contra hcon
    push Not at hcon
    have hu0 := hcon τ₀ ⟨le_rfl, ht⟩
    have h00 := (hmem τ₀ le_rfl).1
    set w₁ := u t - ε / 3 with hw₁
    set w₂ := u t - 2 * ε / 3 with hw₂
    have hw₁m : w₁ ∈ Ici (0 : ℝ) := by simp only [mem_Ici] at h00 ⊢; linarith
    have hw₂m : w₂ ∈ Ici (0 : ℝ) := by simp only [mem_Ici] at h00 ⊢; linarith
    have hfresh : ∀ w ∈ Ici (0 : ℝ), w ≤ u t → u t - ε < w → α w = η t := by
      intro w hw hwt hwε
      obtain ⟨s, hs, hsw⟩ := hpre t ht.le w hw hwt
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [← hsw, h]
      · exfalso
        have hs' : α w ∈ R (max s τ₀) :=
          monotone_image_Icc (le_max_left s τ₀) ⟨s, ⟨hs.1, le_rfl⟩, hsw⟩
        have h1 : w ≤ u (max s τ₀) :=
          le_lastVisit hαt (hRc _ (hτ₀.trans (le_max_right _ _))).isBounded hw hs'
        have h2 := hcon (max s τ₀) ⟨le_max_right _ _, max_lt h ht⟩
        linarith
    have he₁ := hfresh w₁ hw₁m (by linarith) (by linarith)
    have he₂ := hfresh w₂ hw₂m (by linarith) (by linarith)
    have := hαi hw₁m hw₂m (he₁.trans he₂.symm)
    linarith
  -- assemble
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨tR, htR, huR⟩ := hright t ht ε hε
  have hRbound : ∀ t' ∈ Ici τ₀, t ≤ t' → t' < tR → dist (u t') (u t) < ε := by
    intro t' ht' htt' ht'R
    have h1 : u t ≤ u t' := hmono ht ht' htt'
    have h2 : u t' ≤ u tR := hmono ht' (ht.trans (le_of_lt htR)) ht'R.le
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  rcases eq_or_lt_of_le (show τ₀ ≤ t from ht) with h0' | h0'
  · refine ⟨tR - t, sub_pos.2 htR, fun t' ht' hd => ?_⟩
    have htt' : t ≤ t' := h0' ▸ ht'
    rw [Real.dist_eq, abs_lt] at hd
    exact hRbound t' ht' htt' (by linarith [hd.2])
  · obtain ⟨tL, htL, huL⟩ := hleft t h0' ε hε
    refine ⟨min (tR - t) (t - tL), lt_min (sub_pos.2 htR) (sub_pos.2 htL.2), fun t' ht' hd => ?_⟩
    rw [Real.dist_eq, abs_lt] at hd
    have hm1 := min_le_left (tR - t) (t - tL)
    have hm2 := min_le_right (tR - t) (t - tL)
    rcases le_total t t' with htt' | ht't
    · exact hRbound t' ht' htt' (by linarith [hd.2])
    · have h1 : u t' ≤ u t := hmono ht' ht ht't
      have h2 : u tL ≤ u t' := hmono htL.1 ht' (by linarith [hd.1])
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith

/-- **A rational witness of attachment progress at infinity** on the side `α`: times `τ ≤ r < s` between which the
counterflow avoids `C`, and arm parameters `u(r) < v < v₁ < v₂ < u(s)`, `u` the last-visit attachment. -/
def IsAttachWitnessInf (η : ℝ → ℂ) (C : Set ℂ) (α : ℝ → ℂ) (τ r s v v₁ v₂ : ℝ) : Prop :=
  τ ≤ r ∧ r < s ∧ (∀ t ∈ Icc r s, η t ∉ C) ∧
    lastVisit (fun t => η '' Icc 0 t) α r < v ∧ v < v₁ ∧ v₁ < v₂ ∧ v₂ < lastVisit (fun t => η '' Icc 0 t) α s

theorem continuousOn_attachInf (hP : IsReversePocketInf W η C α₁ α₂ τ) (hα : α = α₁ ∨ α = α₂) :
    ContinuousOn (lastVisit (fun t => η '' Icc 0 t) α) (Ici τ) := by
  obtain ⟨hc, hinj, ht, h0, -, hrev, -⟩ := hP.arm hα
  refine continuousOn_lastVisit_Ici hP.nonneg hP.trace.2.1 hc hinj ht (fun t htτ => h0 ▸ hP.y_mem htτ)
    fun t htτ v hv hvu => ?_
  have hmem := lastVisit_mem (R := fun t => η '' Icc 0 t) hc ht (hP.isCompact_range t)
    ⟨0, mem_Ici.2 le_rfl, h0 ▸ hP.y_mem htτ⟩
  exact hrev t v hv _ hmem.1 hvu hmem.2

theorem monotoneOn_attachInf (hP : IsReversePocketInf W η C α₁ α₂ τ) (hα : α = α₁ ∨ α = α₂) :
    MonotoneOn (lastVisit (fun t => η '' Icc 0 t) α) (Ici τ) := by
  obtain ⟨-, -, ht, h0, -, -, -⟩ := hP.arm hα
  exact fun s hs t _ hst => lastVisit_mono ht monotone_image_Icc hst (hP.isCompact_range t).isBounded
    ⟨0, mem_Ici.2 le_rfl, h0 ▸ hP.y_mem hs⟩

/-- **A strict increase of an attachment at infinity on an interval avoiding `C` gives a rational witness.** -/
theorem exists_rat_attachWitnessInf_of_lt (hP : IsReversePocketInf W η C α₁ α₂ τ) (hα : α = α₁ ∨ α = α₂)
    (B : Finset ℝ) {a b : ℝ} (hτa : τ ≤ a) (hab : a ≤ b) (hC : ∀ t ∈ Icc a b, η t ∉ C)
    (hlt : lastVisit (fun t => η '' Icc 0 t) α a < lastVisit (fun t => η '' Icc 0 t) α b) :
    ∃ r s v v₁ v₂ : ℚ, IsAttachWitnessInf η C α τ r s v v₁ v₂ ∧ ∀ b ∈ B, b ∉ Icc (v : ℝ) v₂ := by
  set u := lastVisit (fun t => η '' Icc 0 t) α with hu
  have hab' : a < b := lt_of_le_of_ne hab fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  set δ := u b - u a with hδ
  have hδ0 : 0 < δ := sub_pos.2 hlt
  have hcont := continuousOn_attachInf hP hα
  obtain ⟨ρ, hρ, hρa⟩ := Metric.continuousWithinAt_iff.1 (hcont a hτa) (δ / 3) (by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show a < min (a + ρ) b from lt_min (by linarith) hab')
  have hra : u r < u a + δ / 3 := by
    have h := hρa (show (r : ℝ) ∈ Ici τ from hτa.trans hr1.le) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left (a + ρ) b])
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  have hrb : (r : ℝ) < b := lt_of_lt_of_le hr2 (min_le_right _ _)
  obtain ⟨ρ', hρ', hρb⟩ := Metric.continuousWithinAt_iff.1 (hcont b (hτa.trans hab)) (δ / 3) (by linarith)
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show max (r : ℝ) (b - ρ') < b from max_lt hrb (by linarith))
  have hsb : u b - δ / 3 < u s := by
    have h := hρb (show (s : ℝ) ∈ Ici τ from hτa.trans (hr1.le.trans (le_max_left _ _ |>.trans hs1.le))) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_right (r : ℝ) (b - ρ')])
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  have hrs : (r : ℝ) < s := lt_of_le_of_lt (le_max_left _ _) hs1
  obtain ⟨v, v₁, v₂, hv, hvv₁, hv₁v₂, hv₂, hB⟩ :=
    exists_rat_triple_avoid (show u r < u s by linarith) B
  exact ⟨r, s, v, v₁, v₂, ⟨hτa.trans hr1.le, hrs, fun t ht => hC t ⟨hr1.le.trans ht.1, ht.2.trans hs2.le⟩, hv,
    hvv₁, hv₁v₂, hv₂⟩, hB⟩

/-- **Failure of attachment constancy at infinity gives a rational witness** on one of the two sides. -/
theorem exists_rat_attachWitnessInf (hP : IsReversePocketInf W η C α₁ α₂ τ) (B : Finset ℝ)
    (hAC : ¬ AttachmentConstancyInf η C α₁ α₂ τ) :
    ∃ α : ℝ → ℂ, (α = α₁ ∨ α = α₂) ∧ ∃ r s v v₁ v₂ : ℚ, IsAttachWitnessInf η C α τ r s v v₁ v₂ ∧
      ∀ b ∈ B, b ∉ Icc (v : ℝ) v₂ := by
  unfold AttachmentConstancyInf at hAC
  push Not at hAC
  obtain ⟨a, b, hτa, hab, hC, hne⟩ := hAC
  have hlt : ∀ α' : ℝ → ℂ, (α' = α₁ ∨ α' = α₂) →
      lastVisit (fun t => η '' Icc 0 t) α' b ≠ lastVisit (fun t => η '' Icc 0 t) α' a →
      lastVisit (fun t => η '' Icc 0 t) α' a < lastVisit (fun t => η '' Icc 0 t) α' b :=
    fun α' hα' h => lt_of_le_of_ne (monotoneOn_attachInf hP hα' hτa (hτa.trans hab) hab) (Ne.symm h)
  by_cases h₁ : lastVisit (fun t => η '' Icc 0 t) α₁ b = lastVisit (fun t => η '' Icc 0 t) α₁ a
  · exact ⟨α₂, Or.inr rfl, exists_rat_attachWitnessInf_of_lt hP (Or.inr rfl) B hτa hab hC
      (hlt α₂ (Or.inr rfl) (hne h₁))⟩
  · exact ⟨α₁, Or.inl rfl, exists_rat_attachWitnessInf_of_lt hP (Or.inl rfl) B hτa hab hC
      (hlt α₁ (Or.inl rfl) h₁)⟩

end Inf

section AEInf

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
  {α₁ α₂ : Ω → ℝ → ℂ} {τ : Ω → ℝ}

/-- **Aux. lemma 37 at infinity from the exclusion of each rational witness.** -/
theorem ae_attachmentConstancyInf_of_witness
    (hP : ∀ᵐ ω ∂P, IsReversePocketInf (W ω) (η ω) (C ω) (α₁ ω) (α₂ ω) (τ ω)) (B : Ω → Finset ℝ)
    (h₁ : ∀ r s v v₁ v₂ : ℚ, ∀ᵐ ω ∂P,
      ¬ (IsAttachWitnessInf (η ω) (C ω) (α₁ ω) (τ ω) r s v v₁ v₂ ∧ ∀ b ∈ B ω, b ∉ Icc (v : ℝ) v₂))
    (h₂ : ∀ r s v v₁ v₂ : ℚ, ∀ᵐ ω ∂P,
      ¬ (IsAttachWitnessInf (η ω) (C ω) (α₂ ω) (τ ω) r s v v₁ v₂ ∧ ∀ b ∈ B ω, b ∉ Icc (v : ℝ) v₂)) :
    ∀ᵐ ω ∂P, AttachmentConstancyInf (η ω) (C ω) (α₁ ω) (α₂ ω) (τ ω) := by
  have h₁' : ∀ᵐ ω ∂P, ∀ r s v v₁ v₂ : ℚ,
      ¬ (IsAttachWitnessInf (η ω) (C ω) (α₁ ω) (τ ω) r s v v₁ v₂ ∧ ∀ b ∈ B ω, b ∉ Icc (v : ℝ) v₂) := by
    simp only [ae_all_iff]
    exact h₁
  have h₂' : ∀ᵐ ω ∂P, ∀ r s v v₁ v₂ : ℚ,
      ¬ (IsAttachWitnessInf (η ω) (C ω) (α₂ ω) (τ ω) r s v v₁ v₂ ∧ ∀ b ∈ B ω, b ∉ Icc (v : ℝ) v₂) := by
    simp only [ae_all_iff]
    exact h₂
  filter_upwards [hP, h₁', h₂'] with ω hPω hω₁ hω₂
  by_contra hAC
  obtain ⟨α, hα, r, s, v, v₁, v₂, hw, hB⟩ := exists_rat_attachWitnessInf hPω (B ω) hAC
  rcases hα with rfl | rfl
  · exact hω₁ r s v v₁ v₂ ⟨hw, hB⟩
  · exact hω₂ r s v v₁ v₂ ⟨hw, hB⟩

end AEInf

end InteractingSLE.Sec7.Aux37Attach
