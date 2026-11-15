/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2TipSepAug
import InteractingSLE.Spec.ZhanGT4.CollarBoundary

/-!
# A.2, part 2, step 1: deterministic geometry of the small crosscut and the pre-contact hulls

Packet PROVE-ZHAN-A2TIPSEP. Source: Astra, *Follow-up proofs*, §A.2 L548–L553 (R38, R53).

* `isPreconnected_H_diff`: removing from `ℍ` a closed subset of a crosscut that misses its end point leaves `ℍ`
  connected;
* `fwdHull_subset_trace`, `trace_mem_fwdHull`: for a generating trace whose open part is the open part of a
  crosscut (the small curve of `IsSmallCrosscut`), the hull at time `t` lies in the trace up to `t` and contains the
  trace point at `t`;
* `not_mem_closure_fwdHull_of_isForwardSol`: an alive real point is not in the closed hull.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2TipSep

open QuantumZipper A2X A2Part2

/-! ### Removing part of a crosscut -/

/-- A real translate of a real crosscut is a real crosscut. -/
theorem isRealCrosscut_sub {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) (c : ℝ) :
    IsRealCrosscut fun s => γ s - c := by
  obtain ⟨hc, hinj, hH, h0, h1⟩ := hγ
  refine ⟨hc.sub continuousOn_const, fun a ha b hb hab => hinj ha hb (sub_left_inj.1 hab), ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    have : γ s ∈ H := hH ⟨s, hs, rfl⟩
    show 0 < (γ s - c).im
    simp only [sub_im, ofReal_im, sub_zero]; exact this
  · simpa using h0
  · simpa using h1

/-- **`ℍ` minus a closed piece of a crosscut that misses the end point `γ 1` is preconnected.** The piece lies in
`{γ 0} ∪ γ((0, 1))`; the unbounded side `D` and the inside `V` of the crosscut are joined across the crosscut near
`γ 1`, and every remaining crosscut point has a ball meeting `D`. -/
theorem isPreconnected_H_diff {γ : ℝ → ℂ} {D : Set ℂ} (hD : IsCrosscutDomain D γ) {S : Set ℂ}
    (hSc : IsClosed S) (hS : S ⊆ insert (γ 0) (γ '' Ioo 0 1)) (h1 : γ 1 ∉ S) : IsPreconnected (H \ S) := by
  obtain ⟨V, hVo, hVc, hVH, hVD, hHD, hVfr, hVΓ⟩ := hD.exists_inside
  have hγ := hD.crosscut
  have hγ0H : γ 0 ∉ H := fun h => by
    have : (0 : ℝ) < (γ 0).im := h
    rw [hγ.2.2.2.1] at this; exact lt_irrefl _ this
  -- a crosscut point off `S` has a ball in `ℍ \ S` meeting `D` and `V`
  have hball : ∀ p ∈ γ '' Ioo 0 1, p ∉ S → ∃ r > (0 : ℝ), ball p r ⊆ H \ S ∧ (ball p r ∩ D).Nonempty ∧
      (ball p r ∩ V).Nonempty := by
    intro p hp hpS
    have hpH : p ∈ H := hγ.2.2.1 hp
    have hopen : IsOpen (H \ S) := isOpen_H.sdiff hSc
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hopen p ⟨hpH, hpS⟩
    have hpD : p ∈ closure D := by
      have : p ∈ frontier D ∩ H := by rw [hD.frontier_inter]; exact hp
      exact frontier_subset_closure this.1
    have hpV : p ∈ closure V := by
      have : p ∈ frontier V := by
        rw [hVfr]; obtain ⟨s, hs, rfl⟩ := hp; exact Or.inl ⟨s, Ioo_subset_Icc_self hs, rfl⟩
      exact frontier_subset_closure this
    obtain ⟨d, hd, hdp⟩ := Metric.mem_closure_iff.1 hpD r hr
    obtain ⟨v, hv, hvp⟩ := Metric.mem_closure_iff.1 hpV r hr
    exact ⟨r, hr, hrsub, ⟨d, mem_ball'.2 hdp, hd⟩, ⟨v, mem_ball'.2 hvp, hv⟩⟩
  -- a crosscut point near `γ 1` off `S`
  obtain ⟨p₀, hp₀, hp₀S⟩ : ∃ p ∈ γ '' Ioo 0 1, p ∉ S := by
    have hcw : ContinuousWithinAt γ (Ioo 0 1) 1 :=
      (hγ.1 1 ⟨zero_le_one, le_rfl⟩).mono Ioo_subset_Icc_self
    have hev : ∀ᶠ s in 𝓝[Ioo 0 1] (1 : ℝ), γ s ∈ Sᶜ := hcw.tendsto (hSc.isOpen_compl.mem_nhds h1)
    have hne : (𝓝[Ioo (0 : ℝ) 1] (1 : ℝ)).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsLT zero_lt_one]; infer_instance
    obtain ⟨s, hsS, hs⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨γ s, ⟨s, hs, rfl⟩, hsS⟩
  obtain ⟨r₀, hr₀, hB₀, hB₀D, hB₀V⟩ := hball p₀ hp₀ hp₀S
  have hDS : D ⊆ H \ S := fun z hz => ⟨hD.subset_H hz, fun hzS => by
    rcases hS hzS with h | h
    · exact hγ0H (h ▸ hD.subset_H hz)
    · exact Set.disjoint_left.1 hD.disjoint_crosscut hz h⟩
  have hVS : V ⊆ H \ S := fun z hz => ⟨hVH hz, fun hzS => by
    have hzΓ : z ∈ crosscutCurve γ := by
      rcases hS hzS with h | ⟨s, hs, rfl⟩
      · exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, h.symm⟩
      · exact Or.inl ⟨s, Ioo_subset_Icc_self hs, rfl⟩
    exact Set.disjoint_left.1 hVΓ hz hzΓ⟩
  have hBpc : ∀ p : ℂ, ∀ r : ℝ, IsPreconnected (ball p r) := fun p r => (convex_ball p r).isPreconnected
  have hDB : IsPreconnected (D ∪ ball p₀ r₀) := by
    obtain ⟨d, hdB, hdD⟩ := hB₀D
    exact IsPreconnected.union d hdD hdB hD.isPreconnected (hBpc p₀ r₀)
  refine isPreconnected_of_forall p₀ fun z hz => ?_
  by_cases hzD : z ∈ D
  · exact ⟨D ∪ ball p₀ r₀, union_subset hDS hB₀, Or.inr (mem_ball_self hr₀), Or.inl hzD, hDB⟩
  rcases hHD ⟨hz.1, hzD⟩ with hzV | hzγ
  · obtain ⟨v, hvB, hvV⟩ := hB₀V
    exact ⟨V ∪ ball p₀ r₀, union_subset hVS hB₀, Or.inr (mem_ball_self hr₀), Or.inl hzV,
      IsPreconnected.union v hvV hvB hVc (hBpc p₀ r₀)⟩
  · obtain ⟨r, hr, hB, ⟨d, hdB, hdD⟩, -⟩ := hball z hzγ hz.2
    exact ⟨ball z r ∪ (D ∪ ball p₀ r₀), union_subset hB (union_subset hDS hB₀),
      Or.inr (Or.inr (mem_ball_self hr₀)), Or.inl (mem_ball_self hr),
      IsPreconnected.union d hdB (Or.inl hdD) (hBpc z r) hDB⟩


/-! ### The hulls of the small curve -/

/-- **The hull of a generating trace whose open part is the open part of a crosscut lies in the trace** (the small
curve of `IsSmallCrosscut`): `K_t ⊆ η([0, t])` for `t < ζ`. The trace up to `t` is a closed piece of the crosscut
(translated by `−y`) missing its end point, so `ℍ \ η([0, t])` is connected and the filling adds nothing. -/
theorem fwdHull_subset_trace {y : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ → ℂ} {η : ℝ≥0 → ℂ}
    (hγ : IsRealCrosscut γ) (hγ0 : (γ 0).re = y) (hlt : y < (γ 1).re) (hη : IsGeneratingTrace w ζ η)
    (himg : γ '' Ioo 0 1 = (fun z : ℂ => z + y) '' (η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ}))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : fwdHull (Strip.extPath w) t ⊆ η '' Icc 0 t := by
  set γ' : ℝ → ℂ := fun s => γ s - y with hγ'
  have hγ'c : IsRealCrosscut γ' := isRealCrosscut_sub hγ y
  have h0 : γ 0 = (y : ℂ) := Complex.ext (by simp [hγ0]) (by simp [hγ.2.2.2.1])
  have hγ'0 : γ' 0 = 0 := by simp [hγ', h0]
  have hre : (γ' 0).re < (γ' 1).re := by
    rw [hγ'0]; simp only [hγ', sub_re, ofReal_re, zero_re]; linarith
  obtain ⟨D, hD⟩ := exists_isCrosscutDomain hγ'c hre
  have himg' : γ' '' Ioo 0 1 = η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ} := by
    have e : γ' '' Ioo 0 1 = (fun z : ℂ => z - y) '' (γ '' Ioo 0 1) := by
      rw [image_image]
    rw [e, himg, image_image]
    simp
  set A := η '' Icc 0 t with hA
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans ht.le)
  have hAS : A ⊆ insert (γ' 0) (γ' '' Ioo 0 1) := by
    rintro _ ⟨r, hr, rfl⟩
    rcases eq_or_lt_of_le (zero_le (a := r)) with h | h
    · left; rw [← h, hη.1, hγ'0]
    · right; rw [himg']; exact ⟨r, ⟨h, (ENNReal.coe_le_coe.2 hr.2).trans_lt ht⟩, rfl⟩
  have h1 : γ' 1 ∉ A := by
    intro h1A
    rcases hAS h1A with h | ⟨s, hs, hs1⟩
    · exact one_ne_zero (hγ'c.2.1 (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one) h)
    · exact (ne_of_lt hs.2) (hγ'c.2.1 (Ioo_subset_Icc_self hs) (right_mem_Icc.2 zero_le_one) hs1)
  have hpc := isPreconnected_H_diff hD hAc.isClosed hAS h1
  obtain ⟨⟨z, hzK, hcomp⟩, -⟩ := hη.2.2 t ht
  have hzA : z ∈ H \ A := by
    have : z ∈ connectedComponentIn (H \ A) z := by rw [hcomp]; exact hzK
    exact connectedComponentIn_subset _ _ this
  have hcc : connectedComponentIn (H \ A) z = H \ A := hpc.connectedComponentIn hzA
  intro p hp
  by_contra hpA
  have : p ∈ H \ A := ⟨hp.1, hpA⟩
  rw [← hcc, hcomp] at this
  exact this.2 hp

/-- **The trace point at `t` lies in the hull at `t`** when it is in `ℍ`. -/
theorem trace_mem_fwdHull {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) (hH : η t ∈ H) : η t ∈ fwdHull (Strip.extPath w) t := by
  obtain ⟨⟨z, hzK, hcomp⟩, -⟩ := hη.2.2 t ht
  by_contra h
  have : η t ∈ connectedComponentIn (H \ η '' Icc 0 t) z := by rw [hcomp]; exact ⟨hH, h⟩
  exact (connectedComponentIn_subset _ _ this).2 ⟨t, ⟨zero_le (a := t), le_rfl⟩, rfl⟩

/-! ### Alive real points -/

/-- **An alive real point is not in the closed hull**: points of `ℍ` near it are not swallowed. -/
theorem not_mem_closure_fwdHull_of_isForwardSol {A : ℝ → ℝ} (hA : Continuous A) {T : ℝ} (hT : 0 ≤ T) {y : ℝ}
    {v : ℝ → ℂ} (hv : IsForwardSol A (y : ℂ) T v) : (y : ℂ) ∉ closure (fwdHull A T) := by
  have hev := ZhanGT4.eventually_not_mem_fwdHull hA hT hv
  obtain ⟨U, hUo, hyU, hUsub⟩ := mem_nhdsWithin.1 hev
  intro hy
  obtain ⟨z, hzU, hzK⟩ := mem_closure_iff.1 hy U hUo hyU
  exact (hUsub ⟨hzU, hzK.1⟩).2 hzK

end InteractingSLE.ZhanGT4.A2TipSep
