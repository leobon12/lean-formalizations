/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39Chart

/-!
# Aux. lemma 37: the deterministic steps (attachment continuity, the phase mismatch)

Specification §6.2, **Aux.** lemma 37 (`source/spec/p193-240.md` L80–L136, pp. 197–200), with the
repair of ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt` §1.2: the singleton-fibre
hypothesis is unnecessary; `T_v` is the first visit to an interior point and the deterministic
fresh-tip lemma applies there).

The statement of Aux. 37 is a field statement: almost surely the first-visit attachments
`u_i(t) = min {u : α_i(u) ∈ R_t}` are constant on every interval avoiding the open pocket. Its proof
has three deterministic ingredients and one field comparison:

1. (first paragraph) under reverse first-visit order the visited parameters at time `t` form the
   closed suffix `[u_i(t), 1]`; `u_i` is nonincreasing and **continuous**;
2. (the flat clock) the conditional harmonic mean of the central component is constant while
   the pocket is avoided — a marked conditional-law statement (Prop. 6.5's local proof);
3. (the germ identification at `T_v`) the collar of a newly exposed arc carries the old flow-side
   germ and the new counterflow-side germ;
4. (the phase comparison (PFI4)) the two germs `ελ − θχ + 2πk_fχ` and `ελ' − πχ + 2πk_cχ` are
   different whenever `θ ∈ (−π/2, π/2)`.

This file proves 1 and 4. Steps 2–3 need the marked counterflow/flow-line couplings and their
conditional means (Aux. lemmas 32, 34–36), which have no Lean statement yet.

## Main results

* `mem_image_Icc_of_forall_lt`: `⋂_{t' > t} η([0, t']) = η([0, t])`;
* `antitoneOn_firstVisit`, `continuousOn_firstVisit` (step 1);
* `aux37_phase_ne` (step 4, (PFI4)).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Real

namespace InteractingSLE.Sec6

/-! ### Step 1: continuity of the first-visit attachments -/

section Attach

variable {η α : ℝ → ℂ}

/-- A point visited by every time `t' > t` was visited by time `t`. -/
theorem mem_image_Icc_of_forall_lt (hη : ContinuousOn η (Ici 0)) {t : ℝ} (ht : 0 ≤ t) {p : ℂ}
    (hp : ∀ t' > t, p ∈ η '' Icc 0 t') : p ∈ η '' Icc 0 t := by
  by_contra hpt
  -- `p ≠ η t`, so a neighbourhood of `t` maps away from `p`
  have hne : η t ≠ p := fun h => hpt ⟨t, ⟨ht, le_rfl⟩, h⟩
  have hcont : ContinuousWithinAt η (Ici 0) t := hη t ht
  obtain ⟨δ, hδ, hδp⟩ := Metric.continuousWithinAt_iff.1 hcont (dist (η t) p) (dist_pos.2 hne)
  obtain ⟨s, hs, hsp⟩ := hp (t + δ / 2) (by linarith)
  rcases le_or_gt s t with hst | hst
  · exact hpt ⟨s, ⟨hs.1, hst⟩, hsp⟩
  · have hd : dist s t < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith [hs.2]
    have := hδp hs.1 hd
    rw [hsp, dist_comm] at this
    exact lt_irrefl _ this

/-- The visited sets `R_t = η([0, t])` increase. -/
theorem monotone_image_Icc : Monotone fun t : ℝ => η '' Icc 0 t :=
  fun _ _ hst => image_mono (Icc_subset_Icc_right hst)

/-- First-visit parameters are nonincreasing on `[0, ∞)`. -/
theorem antitoneOn_firstVisit (hne : ∀ t ≥ (0 : ℝ), ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ η '' Icc 0 t) :
    AntitoneOn (firstVisit (fun t => η '' Icc 0 t) α) (Ici 0) := fun s hs _ _ hst =>
  firstVisit_anti monotone_image_Icc hst (hne s hs)

/-- **Aux. lemma 37, first paragraph of the proof.** Let `η` be continuous on `[0, ∞)` and `α`
continuous and injective on `[0, 1]`. Suppose every visited set meets `α`, and the visited
parameters at time `t` contain the suffix `[u(t), 1]` (reverse first-visit order). Then the
first-visit parameter `u(t) = min {v : α(v) ∈ η([0, t])}` is continuous on `[0, ∞)`. Right
continuity is compactness; a left jump would put a nontrivial arc of `α` in
`η([0, t]) \ ⋃_{s < t} η([0, s]) ⊆ {η(t)}`. -/
theorem continuousOn_firstVisit (hη : ContinuousOn η (Ici 0)) (hα : ContinuousOn α (Icc 0 1))
    (hαi : InjOn α (Icc 0 1)) (hne : ∀ t ≥ (0 : ℝ), ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ η '' Icc 0 t)
    (hsuf : ∀ t ≥ (0 : ℝ), ∀ v ∈ Icc (0 : ℝ) 1,
      firstVisit (fun t => η '' Icc 0 t) α t ≤ v → α v ∈ η '' Icc 0 t) :
    ContinuousOn (firstVisit (fun t => η '' Icc 0 t) α) (Ici 0) := by
  set R : ℝ → Set ℂ := fun t => η '' Icc 0 t with hR
  set u := firstVisit R α with hu
  have hRc : ∀ t ≥ (0 : ℝ), IsClosed (R t) := fun t ht =>
    ((isCompact_Icc).image_of_continuousOn (hη.mono fun s hs => hs.1)).isClosed
  have hmem : ∀ t ≥ (0 : ℝ), u t ∈ Icc (0 : ℝ) 1 ∧ α (u t) ∈ R t := fun t ht =>
    firstVisit_mem hα (hRc t ht) (hne t ht)
  have hanti : AntitoneOn u (Ici 0) := antitoneOn_firstVisit hne
  -- right continuity
  have hright : ∀ t ≥ (0 : ℝ), ∀ ε > 0, ∃ t' > t, u t - ε < u t' := by
    intro t ht ε hε
    by_contra hcon
    push Not at hcon
    set m := sSup (u '' Ioi t) with hm
    have hbdd : BddAbove (u '' Ioi t) := ⟨1, by
      rintro _ ⟨t', ht', rfl⟩; exact (hmem t' (ht.trans (le_of_lt ht'))).1.2⟩
    have hmle : m ≤ u t - ε := csSup_le ((nonempty_Ioi).image u) (by
      rintro _ ⟨t', ht', rfl⟩; exact hcon t' ht')
    -- `α m` is visited by every time after `t`
    have hvis : ∀ t'' > t, α m ∈ R t'' := by
      intro t'' ht''
      have hcl : IsClosed {v ∈ Icc (0 : ℝ) 1 | α v ∈ R t''} :=
        hα.preimage_isClosed_of_isClosed isClosed_Icc (hRc t'' (ht.trans (le_of_lt ht'')))
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
    have hmt : α m ∈ R t := mem_image_Icc_of_forall_lt hη ht hvis
    have hm01 : m ∈ Icc (0 : ℝ) 1 := by
      have hcl : IsClosed (Icc (0 : ℝ) 1) := isClosed_Icc
      refine hcl.closure_subset_iff.2 ?_ (csSup_mem_closure ((nonempty_Ioi).image u) hbdd)
      rintro _ ⟨t', ht', rfl⟩; exact (hmem t' (ht.trans (le_of_lt ht'))).1
    have := firstVisit_le hm01 hmt
    linarith
  -- left continuity
  have hleft : ∀ t > (0 : ℝ), ∀ ε > 0, ∃ t' ∈ Ico 0 t, u t' < u t + ε := by
    intro t ht ε hε
    by_contra hcon
    push Not at hcon
    have hu0 := hcon 0 ⟨le_rfl, ht⟩
    have h01 := (hmem 0 le_rfl).1
    have ht01 := (hmem t ht.le).1
    set w₁ := u t + ε / 3 with hw₁
    set w₂ := u t + 2 * ε / 3 with hw₂
    have hw₁m : w₁ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht01.1], by linarith [h01.2]⟩
    have hw₂m : w₂ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht01.1], by linarith [h01.2]⟩
    -- each `α w_i` is visited at time `t` but at no earlier time, so equals `η t`
    have hfresh : ∀ w ∈ Icc (0 : ℝ) 1, u t ≤ w → w < u t + ε → α w = η t := by
      intro w hw hwt hwε
      obtain ⟨s, hs, hsw⟩ := hsuf t ht.le w hw hwt
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [← hsw, h]
      · exfalso
        have h1 : u s ≤ w := firstVisit_le hw ⟨s, ⟨hs.1, le_rfl⟩, hsw⟩
        have h2 := hcon s ⟨hs.1, h⟩
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
  have hRbound : ∀ t' ∈ Ici (0 : ℝ), t ≤ t' → t' < tR → dist (u t') (u t) < ε := by
    intro t' ht' htt' ht'R
    have h1 : u t' ≤ u t := hanti ht ht' htt'
    have h2 : u tR ≤ u t' := hanti ht' (ht.trans (le_of_lt htR)) ht'R.le
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with h0 | h0
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

end Attach

/-! ### Step 4: the phase comparison (PFI4) -/

/-- **(PFI4)** (p. 200; repaired form, ZTip note §1.2). With `χ > 0`, `λ − λ' = πχ/2`, a side sign
`ε ∈ {1, −1}`, an angle `θ ∈ (−π/2, π/2)` and integers `k_f, k_c` (the inherited logarithm
branches), the flow-side germ `ελ − θχ + 2πk_fχ` and the counterflow-side germ
`ελ' − πχ + 2πk_cχ` of the same collar are different. -/
theorem aux37_phase_ne {χ lam lam' ε θ : ℝ} (hχ : 0 < χ) (hlam : lam - lam' = π * χ / 2)
    (hε : ε = 1 ∨ ε = -1) (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) (kf kc : ℤ) :
    ε * lam - θ * χ + 2 * π * kf * χ ≠ ε * lam' - π * χ + 2 * π * kc * χ := by
  intro heq
  have hπ := Real.pi_pos
  -- the difference is `χ (επ/2 + π − θ + 2πk)`
  have hdiff : χ * (ε * (π / 2) + π - θ + 2 * π * ((kf : ℝ) - kc)) = 0 := by
    have : ε * lam = ε * lam' + ε * (π * χ / 2) := by rw [← hlam]; ring
    linear_combination heq + (-1 : ℝ) * this
  have hzero : ε * (π / 2) + π - θ + 2 * π * ((kf : ℝ) - kc) = 0 :=
    (mul_eq_zero.1 hdiff).resolve_left hχ.ne'
  set k : ℤ := kf - kc with hk
  have hkR : ((kf : ℝ) - kc) = (k : ℝ) := by rw [hk]; push_cast; ring
  rw [hkR] at hzero
  rcases hε with rfl | rfl
  · -- `θ = 3π/2 + 2πk` is not in `(−π/2, π/2)`
    have h1 : (k : ℝ) < -1 / 2 := by nlinarith [hθ.2]
    have h2 : (-1 : ℝ) < k := by nlinarith [hθ.1]
    have h1' : k < 0 := by exact_mod_cast (show (k : ℝ) < 0 by linarith)
    have h2' : -1 < k := by exact_mod_cast h2
    omega
  · -- `θ = π/2 + 2πk` is not in `(−π/2, π/2)`
    have h1 : (k : ℝ) < 0 := by nlinarith [hθ.2]
    have h2 : (-1 / 2 : ℝ) < k := by nlinarith [hθ.1]
    have h1' : k < 0 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith)
    omega

end InteractingSLE.Sec6
