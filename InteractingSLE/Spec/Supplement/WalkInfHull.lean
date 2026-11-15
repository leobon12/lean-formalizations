/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72DHull

/-!
# A compact set misses a Loewner hull iff a dense family of its points stays tamed-high

Packet PROVE-T14-WALKINF. The criterion of `Sec7.Lemma72D.disjoint_closedBall_fwdHull_iff_real` (a closed disc misses
`K_q` iff its rational points stay tamed-high at the rational times of `[0, q]`), for an arbitrary compact set
`F ⊂ ℍ` with a dense family of points `y i` (`disjoint_fwdHull_iff_of_dense`). It is used for the closed-disc events of
composed charts: the image of a closed disc under a chart's forward map is compact, with the images of the rational
points of the disc dense in it. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull fwdMap tamedZ drive)

namespace InteractingSLE.Theorem14.WalkInf

open Sec7.Lemma72D Sec7.Coding

/-- **A compact set of `ℍ` misses `K_q` iff a dense family of its points stays tamed-high up to `q`** (real
`q ≥ 0`). -/
theorem disjoint_fwdHull_iff_of_dense {W : ℝ → ℝ} (hW : Continuous W) {q : ℝ} (hq0 : 0 ≤ q) {F : Set ℂ}
    (hF : IsCompact F) (hFH : F ⊆ H) {ι : Type*} (y : ι → ℂ) (hyF : ∀ i, y i ∈ F)
    (hdense : ∀ z ∈ F, ∀ δ > 0, ∃ i, dist z (y i) < δ) :
    Disjoint F (fwdHull W q) ↔
      ∃ k : ℕ, ∀ i, ∀ s : ℚ, 0 ≤ (s : ℝ) → (s : ℝ) ≤ q →
        2 * (1 / ((k : ℝ) + 1)) ≤ (tamedZ W (1 / ((k : ℝ) + 1)) (y i) s).im := by
  constructor
  · intro hdisj
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · exact ⟨0, fun i => absurd (hyF i) (by rw [hFe]; exact Set.notMem_empty _)⟩
    have hsub : F ⊆ H \ fwdHull W q := fun z hz =>
      ⟨hFH hz, fun hzK => Set.disjoint_left.1 hdisj hz hzK⟩
    have hφ : ContinuousOn (fun z => (fwdMap W q z).im) F :=
      (Complex.continuous_im.comp_continuousOn
        (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hq0).continuousOn).mono hsub
    obtain ⟨x₀, hx₀, hmin⟩ := hF.exists_isMinOn hFne hφ
    obtain ⟨u₀, hu₀⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hq0 (hsub hx₀).1 (hsub hx₀).2
    have hm : 0 < (fwdMap W q x₀).im := by
      rw [QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu₀ ⟨hq0, le_rfl⟩]
      exact QuantumZipper.FwdClock.sol_im_pos hW (hsub hx₀).1 hu₀ ⟨hq0, le_rfl⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hm)
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    refine ⟨k, fun i s hs0 hsq => ?_⟩
    have hy := hyF i
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hq0 (hsub hy).1 (hsub hy).2
    have hanti := (QuantumZipper.K3.im_fwdMap_antitoneOn hW (hsub hy).1 ⟨u, hu⟩).1
    have hbound : ∀ s' ∈ Icc (0 : ℝ) q, 2 * (1 / ((k : ℝ) + 1)) ≤ (u s').im := by
      intro s' hs'
      have e1 : u s' = fwdMap W s' (y i) := (QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu hs').symm
      have h1 : (fwdMap W q (y i)).im ≤ (fwdMap W s' (y i)).im :=
        hanti hs' ⟨hq0, le_rfl⟩ hs'.2
      have h2 : (fwdMap W q x₀).im ≤ (fwdMap W q (y i)).im := isMinOn_iff.1 hmin _ hy
      rw [e1]
      linarith
    have heq := QuantumZipper.tamedZ_eq_of_isForwardSol hW hk0 hq0 hu
      (fun s' hs' => by linarith [hbound s' hs']) s ⟨hs0, hsq⟩
    rw [heq]
    exact hbound s ⟨hs0, hsq⟩
  · rintro ⟨k, hk⟩
    set c' : ℝ := 1 / ((k : ℝ) + 1) with hc'
    have hc'0 : 0 < c' := by positivity
    have hIm : ∀ a b : ℂ, |a.im - b.im| ≤ dist a b := fun a b => by
      rw [Complex.dist_eq, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h1a : ∀ i, ∀ s ∈ Icc (0 : ℝ) q, 2 * c' ≤ (tamedZ W c' (y i) s).im := by
      intro i s hs
      have hcont := QuantumZipper.continuousOn_tamedZ hW hc'0 hq0 (y i)
      have hcl : IsClosed {z : ℂ | 2 * c' ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
      have hsubI : {s : ℝ | ∃ r : ℚ, (r : ℝ) = s ∧ 0 ≤ s ∧ s ≤ q} ⊆ Icc 0 q := fun s ⟨_, _, h0, h1⟩ => ⟨h0, h1⟩
      have hmem := ((hcont s hs).mono hsubI).mem_closure_image (Icc_subset_closure_rat hq0 hs)
      refine hcl.closure_subset_iff.2 ?_ hmem
      rintro _ ⟨s', ⟨r, rfl, h0, hq'⟩, rfl⟩
      exact hk i r h0 hq'
    have h1b : ∀ z ∈ F, ∀ s ∈ Icc (0 : ℝ) q, 2 * c' ≤ (tamedZ W c' z s).im := by
      intro z hz s hs
      by_contra hlt
      push Not at hlt
      have hgap : 0 < 2 * c' - (tamedZ W c' z s).im := by linarith
      have hL : 0 < Real.exp (4 * q / c' ^ 2) := Real.exp_pos _
      obtain ⟨i, hzy⟩ := hdense z hz _ (div_pos hgap hL)
      have h1 := h1a i s hs
      have h2 := dist_tamedZ_le hW hc'0 hq0 z (y i) hs
      have h4 : dist z (y i) * Real.exp (4 * q / c' ^ 2) < 2 * c' - (tamedZ W c' z s).im := by
        rwa [lt_div_iff₀ hL] at hzy
      linarith [(abs_le.1 (hIm (tamedZ W c' z s) (tamedZ W c' (y i) s))).1]
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    have hcontq := QuantumZipper.continuousOn_tamedZ hW hc'0 (show (0 : ℝ) ≤ q + 1 by linarith) z
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousOn_iff.1 hcontq q ⟨hq0, by linarith⟩ c' hc'0
    have hmin0 : 0 < min (δ / 2) 1 := lt_min (half_pos hδ) one_pos
    set q' : ℝ := q + min (δ / 2) 1 with hq'
    have hqq' : q < q' := by linarith
    have him : ∀ s ∈ Icc (0 : ℝ) q', c' ≤ (tamedZ W c' z s).im := by
      intro s hs
      by_cases hsq : s ≤ q
      · have := h1b z hz s ⟨hs.1, hsq⟩
        linarith
      · push Not at hsq
        have hs1 : s ∈ Icc (0 : ℝ) (q + 1) := ⟨hs.1, by linarith [hs.2, min_le_right (δ / 2) 1]⟩
        have hd : dist s q < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [hs.2, min_le_left (δ / 2) 1]
        have h1 := hδb s hs1 hd
        have h2 := h1b z hz q ⟨hq0, le_rfl⟩
        linarith [(abs_le.1 (hIm (tamedZ W c' z s) (tamedZ W c' z q))).1]
    have hsol := QuantumZipper.isForwardSol_tamedZ hW hc'0 (by linarith : (0 : ℝ) ≤ q') him
    have hsw : ENNReal.ofReal q' ≤ QuantumZipper.swallowTime W z :=
      le_sSup ⟨q', ⟨by linarith, _, hsol⟩, rfl⟩
    have hlt : ENNReal.ofReal q < ENNReal.ofReal q' :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hqq'
    exact absurd (lt_of_lt_of_le hlt hsw) (not_lt.2 hzK.2)

end InteractingSLE.Theorem14.WalkInf
