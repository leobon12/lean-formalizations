/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketCompassBounded
import InteractingSLE.Spec.Sec7.PocketJordan

/-!
# Orientation and order on the right boundary arc

PROVE-POCKETSHAPE. Apply the existing winding-number orientation theorem using
only the component's side of the right crosscut. Then use Mathlib's monotonicity
theorem for a continuous injective real map on an interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.PocketCompass

open GW4Reg WangWu Sec7.Lemma71I Sec7.Lemma71K
open InteractingSLE.Orientation

/-- Winding fixes the sign for any marked pocket on the upper side of its right crosscut. -/
theorem re_pos_of_markedPocket_crossSide {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R)
    {C : Set ℂ} (hCo : IsOpen C) (hCpc : IsPreconnected C) (hCH : C ⊆ H)
    (hCR : Disjoint C (range R)) {a b : ℝ} (hM : IsMarkedPocket R C a b)
    (hside : cayley '' C ⊆ crossSide (wallPt R) 1) {Ψ : ℂ → ℂ}
    (hU : Sec7.PocketJordan.IsBdryUniformizer (cayley '' C) (wallPt R a) (wallPt R b) Ψ) :
    ∀ s ∈ Ioo a b, 0 < (Ψ (wallPt R s)).re := by
  have hα : IsDiscCrosscut (wallPt R) := hR.isProperArc.isDiscCrosscut_toDisc
  obtain ⟨ha0, hab, hb1, hI, -, -, -, -⟩ := id hM
  have hCα : ∀ x ∈ C, cayley x ∉ wallPt R '' Icc 0 1 := fun x hx h =>
    disjoint_left.1 hCR hx (GW3.mem_range_of_cayley_mem_wallPt_image hR.isProperCurve
      (Sec7.Prop74B.mem_Hbar_of_mem_H (hCH hx)) h)
  have hf : IsConformalBijection (Ψ ∘ cayley) C H :=
    isConformalBijection_comp hU.conf (Sec7.Lemma71F.isConformalBijection_cayley_image hCH)
  obtain ⟨hVpc, hVu, hVsub, hVd⟩ := Sec7.Prop74B.crossSide_neg_props hα
  refine Sec7.Prop74B.re_pos_of_crossLoop hα.cont hα.inj hα.zero hα.one hCo hCpc hCH hCα
    ha0 hab hb1 hI hf hU.cont hU.inj hU.mapsTo hU.zero hU.tendsto (fun _ _ => rfl)
    (fun z hz => windNum_crossLoop_of_mem_crossSide_one hα (hside hz)) ?_
  let m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hm01 : m ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hm.1], by linarith [hm.2]⟩
  refine ⟨wallPt R m, ⟨m, hm, rfl⟩, ?_, _, hVpc, hVu,
    closure_mono hVsub (hα.crossRange_subset_closure_crossSide (Or.inr rfl)
      ⟨m, Ioo_subset_Icc_self hm01, rfl⟩), ?_⟩
  · intro h
    have hlt := hα.mem_disc m hm01
    rw [mem_ball, dist_zero_right, h.1] at hlt
    exact lt_irrefl _ hlt
  · refine disjoint_left.2 fun z hz hzc => disjoint_left.1 hVd hz ?_
    rcases hzc with (h | h) | h
    · exact Or.inl (Or.inl (closure_mono hside h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- Boundary values of a two-point uniformizer on the right arc are real. -/
theorem im_eq_zero_on_marked_right {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R)
    {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) (hCR : Disjoint C (range R))
    {a b : ℝ} (hM : IsMarkedPocket R C a b) {Ψ : ℂ → ℂ}
    (hU : Sec7.PocketJordan.IsBdryUniformizer (cayley '' C) (wallPt R a) (wallPt R b) Ψ) :
    ∀ s ∈ Ico a b, (Ψ (wallPt R s)).im = 0 := by
  have hα : IsDiscCrosscut (wallPt R) := hR.isProperArc.isDiscCrosscut_toDisc
  obtain ⟨ha0, hab, hb1, hI, -, -, -, -⟩ := id hM
  have hnot : ∀ q ∈ Icc (0 : ℝ) 1, wallPt R q ∉ cayley '' C := by
    rintro q hq ⟨z, hz, he⟩
    exact disjoint_left.1 hCR hz (GW3.mem_range_of_cayley_mem_wallPt_image hR.isProperCurve
      (Sec7.Prop74B.mem_Hbar_of_mem_H (hCH hz)) ⟨q, hq, he.symm⟩)
  intro s hs
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hs.1, hs.2.le.trans hb1⟩
  have hscl : wallPt R s ∈ closure (cayley '' C) := by
    have : s ∈ {q ∈ Icc (0 : ℝ) 1 | wallPt R q ∈ closure (cayley '' C)} := by
      rw [hI]
      exact Ico_subset_Icc_self hs
    exact this.2
  apply hU.im_eq_zero (Sec7.Lemma71F.isOpen_cayley_image hCo hCH)
    (hnot b ⟨ha0.trans hab.le, hb1⟩)
  · rw [(Sec7.Lemma71F.isOpen_cayley_image hCo hCH).frontier_eq]
    exact ⟨hscl, hnot s hs01⟩
  · exact fun he => hs.2.ne (hα.inj hs01 ⟨ha0.trans hab.le, hb1⟩ he)

/-- Positive right-arc values of the normalized boundary map strictly increase in wall time. -/
theorem strictMonoOn_marked_right {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R)
    {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) (hCR : Disjoint C (range R))
    {a b : ℝ} (hM : IsMarkedPocket R C a b) {Ψ : ℂ → ℂ}
    (hU : Sec7.PocketJordan.IsBdryUniformizer (cayley '' C) (wallPt R a) (wallPt R b) Ψ)
    (hpos : ∀ s ∈ Ioo a b, 0 < (Ψ (wallPt R s)).re) :
    StrictMonoOn (fun s => (Ψ (wallPt R s)).re) (Ico a b) := by
  have hα : IsDiscCrosscut (wallPt R) := hR.isProperArc.isDiscCrosscut_toDisc
  obtain ⟨ha0, hab, hb1, hI, -, -, -, -⟩ := id hM
  have hE : ∀ s ∈ Ico a b, wallPt R s ∈ closure (cayley '' C) \ {wallPt R b} := by
    intro s hs
    refine ⟨?_, fun he => hs.2.ne (hα.inj ⟨ha0.trans hs.1, hs.2.le.trans hb1⟩
      ⟨ha0.trans hab.le, hb1⟩ he)⟩
    have : s ∈ {q ∈ Icc (0 : ℝ) 1 | wallPt R q ∈ closure (cayley '' C)} := by
      rw [hI]
      exact Ico_subset_Icc_self hs
    exact this.2
  have hc : ContinuousOn (fun s => (Ψ (wallPt R s)).re) (Ico a b) :=
    Complex.continuous_re.comp_continuousOn (hU.cont.comp
      (hα.cont.mono fun s hs => ⟨ha0.trans hs.1, hs.2.le.trans hb1⟩) hE)
  have hi : InjOn (fun s => (Ψ (wallPt R s)).re) (Ico a b) := by
    intro s hs t ht he
    apply hα.inj ⟨ha0.trans hs.1, hs.2.le.trans hb1⟩ ⟨ha0.trans ht.1, ht.2.le.trans hb1⟩
    exact hU.inj (hE s hs) (hE t ht) (Complex.ext he (by
      rw [im_eq_zero_on_marked_right hR hCo hCH hCR hM hU s hs,
        im_eq_zero_on_marked_right hR hCo hCH hCR hM hU t ht]))
  intro x hx y hy hxy
  have hay : a < y := hx.1.trans_lt hxy
  have hmono := ContinuousOn.strictMonoOn_of_injOn_Icc hay.le
    (show (Ψ (wallPt R a)).re ≤ (Ψ (wallPt R y)).re by
      rw [hU.zero, Complex.zero_re]
      exact (hpos y ⟨hay, hy.2⟩).le)
    (hc.mono (Icc_subset_Ico_right hy.2)) (hi.mono (Icc_subset_Ico_right hy.2))
  exact hmono ⟨hx.1, hxy.le⟩ ⟨hay.le, le_rfl⟩ hxy

end InteractingSLE.Theorem14.PocketCompass
