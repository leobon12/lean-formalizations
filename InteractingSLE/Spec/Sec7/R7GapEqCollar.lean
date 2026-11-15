/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInMixedInf

/-!
# The endpoint exclusions in R.7, supplement §5.4

Packet PROVE-R7-GAPEQ. Two local deterministic arguments used by "Closed gaps have identical
endpoints" (`source/spec/p433-480.md`, pp. 473–474): a forbidden-side collar excludes an outer
endpoint, and Aux. 38 excludes an old endpoint when the local pocket boundary is already visited.
The collar hypotheses are explicit; this file does not assert that the mixed pockets supply them.
No determination theorem is used (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace InteractingSLE.Sec7.R7GapEq

open Sec6 R7StopIn

variable {η : ℝ → ℂ} {C F K U J : Set ℂ} {a b t : ℝ}

/-- A relative time neighborhood of any point of a nondegenerate closed interval contains a
nondegenerate closed subinterval. This includes both endpoints. -/
theorem exists_subinterval_of_mem_nhdsWithin (ha : 0 ≤ a) (hab : a < b)
    (ht : t ∈ Icc a b) {S : Set ℝ} (hS : S ∈ 𝓝[Ici 0] t) :
    ∃ c d : ℝ, 0 ≤ c ∧ c < d ∧ Icc c d ⊆ Icc a b ∩ S := by
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhdsWithin_iff.1 hS
  by_cases htb : t < b
  · let d := min b (t + ε / 2)
    have htd : t < d := lt_min htb (by linarith only [hε])
    refine ⟨t, d, ha.trans ht.1, htd, fun s hs => ⟨⟨ht.1.trans hs.1,
      hs.2.trans (min_le_left _ _)⟩, hεS ⟨?_, (ha.trans ht.1).trans hs.1⟩⟩⟩
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]
    have hsd : s ≤ t + ε / 2 := hs.2.trans (min_le_right _ _)
    linarith only [hsd, hε]
  · have hbt : t = b := le_antisymm ht.2 (le_of_not_gt htb)
    subst t
    let c := max a (b - ε / 2)
    have hcb : c < b := max_lt hab (by linarith only [hε])
    refine ⟨c, b, ha.trans (le_max_left _ _), hcb, fun s hs => ⟨⟨
      (le_max_left _ _).trans hs.1, hs.2⟩, hεS ⟨?_, (ha.trans (le_max_left _ _)).trans hs.1⟩⟩⟩
    rw [mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hs.2)]
    have hcs : b - ε / 2 ≤ s := (le_max_right _ _).trans hs.1
    linarith only [hcs, hε]

/-- **Outer endpoint exclusion.** A trace with no interval in `K`, avoiding `F` and avoiding
`C` on `[a,b]`, cannot visit a neighborhood whose allowed part is contained in `C ∪ K`.
In §5.4, `K` is the outer simple side and `F` its forbidden exterior. -/
theorem not_mem_collar_at_gap (hc : ContinuousOn η (Ici 0))
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ s, 0 ≤ s → η s ∉ F) (ha : 0 ≤ a) (hab : a < b)
    (hgap : ∀ s ∈ Icc a b, η s ∉ C) (ht : t ∈ Icc a b)
    (hU : IsOpen U) (hcollar : U ⊆ C ∪ F ∪ K) : η t ∉ U := by
  intro htU
  have hN : {s | η s ∈ U} ∈ 𝓝[Ici 0] t :=
    (hc t (ha.trans ht.1)).preimage_mem_nhdsWithin (hU.mem_nhds htU)
  obtain ⟨c, d, hc0, hcd, hsub⟩ := exists_subinterval_of_mem_nhdsWithin ha hab ht hN
  apply h42 c d hc0 hcd
  rintro _ ⟨s, hs, rfl⟩
  rcases hcollar (hsub hs).2 with (hsC | hsF) | hsK
  · exact False.elim (hgap s (hsub hs).1 hsC)
  · exact False.elim (havoid s (ha.trans (hsub hs).1.1) hsF)
  · exact hsK

/-- A limit of visits at nonnegative times maps into the closed pocket. Unlike the landed
pocket-specific lemma, only continuity of the trace is needed. -/
theorem mem_closure_of_visits (hc : ContinuousOn η (Ici 0)) {s : ℝ} (hs : 0 ≤ s)
    (ht : t ∈ closure {u | s < u ∧ η u ∈ C}) : η t ∈ closure C := by
  have hsub : {u | s < u ∧ η u ∈ C} ⊆ Ici 0 := fun u hu => hs.trans hu.1.le
  have ht0 : t ∈ Ici (0 : ℝ) := closure_minimal hsub isClosed_Ici ht
  exact closure_mono (image_subset_iff.2 fun u hu => hu.2)
    (((hc t ht0).mono hsub).mem_closure_image ht)

/-- **Fixed-side old endpoint exclusion.** Suppose the pocket boundary in `U` lies in an old
set `J`. Aux. 38 keeps the trace near `t` in the closure of one component of `U ∖ J`. If `t`
is a limit of open-pocket visits, that component meets `C` and hence lies in `C`. A nontrivial
adjacent no-`C` interval would therefore lie in `∂C ∩ U ⊆ K`, contradicting Aux. 42.

There is no assumption about singleton tip fibers or prime-end identification. -/
theorem not_old_boundary_collar_at_gap {W : ℝ → ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hCo : IsOpen C)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (ha : 0 ≤ a) (hab : a < b) (hgap : ∀ s ∈ Icc a b, η s ∉ C)
    (ht : t ∈ Icc a b) {s r : ℝ}
    (hvis : t ∈ closure {u | s < u ∧ η u ∈ C})
    (hr : 0 ≤ r) (hrt : r < t) (hJ : J ⊆ η '' Icc 0 r)
    (hU : IsOpen U) (hfrJ : frontier C ∩ U ⊆ J) (hfrK : frontier C ∩ U ⊆ K) :
    η t ∉ U := by
  intro htU
  obtain ⟨ε, hε, z, hz, hside⟩ := aux38_exists_side hη hW hW0 hr hrt hJ hU htU
  let S := connectedComponentIn (U \ J) z
  have hSU : S ⊆ U := (connectedComponentIn_subset _ _).trans sdiff_subset
  have hSJ : Disjoint S J := Set.disjoint_left.2 fun w hw hwJ =>
    (connectedComponentIn_subset (U \ J) z hw).2 hwJ
  have hSC : (S ∩ C).Nonempty := by
    obtain ⟨u, hu, huC⟩ := _root_.mem_closure_iff.1 hvis (Ioo (t - ε) (t + ε)) isOpen_Ioo
      ⟨by linarith only [hε], by linarith only [hε]⟩
    have hucl : η u ∈ closure S := (hside u hu).2
    obtain ⟨w, hwC, hwS⟩ := _root_.mem_closure_iff.1 hucl C hCo huC.2
    exact ⟨w, hwS, hwC⟩
  have hSfr : Disjoint S (frontier C) := Set.disjoint_left.2 fun w hw hwfr =>
    Set.disjoint_left.1 hSJ hw (hfrJ ⟨hwfr, hSU hw⟩)
  have hSin : S ⊆ C := subset_of_isPreconnected_of_disjoint_frontier
    isPreconnected_connectedComponentIn hCo hSC hSfr
  have hN : Ioo (t - ε) (t + ε) ∈ 𝓝[Ici (0 : ℝ)] t :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith only [hε]) (by linarith only [hε]))
  obtain ⟨c, d, hc0, hcd, hsub⟩ := exists_subinterval_of_mem_nhdsWithin ha hab ht hN
  apply h42 c d hc0 hcd
  rintro _ ⟨u, hu, rfl⟩
  have hucl : η u ∈ closure C := closure_mono hSin (hside u (hsub hu).2).2
  apply hfrK
  refine ⟨⟨hucl, ?_⟩, (hside u (hsub hu).2).1⟩
  rw [hCo.interior_eq]
  exact hgap u (hsub hu).1

end InteractingSLE.Sec7.R7GapEq
