/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TsSelect

/-!
# Common-time test selection without a singleton current-tip fiber

PROVE-R6-LANDING. Stop the real interval at its first landing at the
physical tip after the force coordinate. Continuity then supplies an
exposed test point with a physical agreement ball. No assertion about
other accesses to the current tip is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Lw

open PocketStopSide

/-- The physical tip may have other real preimages. Choose the whole
compact interval before the first such preimage after the force mark. -/
theorem sameTimeLeftData_of_local_interval
    {O I : Chart} {EO : ℂ → ℂ} {P : Set ℂ} {p : ℂ} {v w : ℝ}
    (hIncl : (I.dom : Set ℂ) ⊆ O.dom)
    (hEOc : ContinuousOn EO Hbar) (hEO0 : EO 0 = p) (hvtip : EO (v : ℂ) ≠ p)
    {S : Set ℝ} (hSo : IsOpen S) (hSc : IsPreconnected S)
    (hvS : v ∈ S) (h0S : 0 ∈ S) (hv : v < 0)
    (hcollars : ∀ x ∈ S, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ O.1 '' (I.dom : Set ℂ))
    (hlanding : ∀ x ∈ S, EO (x : ℂ) ∈ P)
    {g : ℝ → ℝ} (hg : StrictMonoOn g S) (hg0 : g 0 = 0) (hgv : g v = w)
    (hlim : ∀ x ∈ S, Tendsto (pocketTransitionChart O I).1
      (𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ)) (𝓝 (g x : ℂ)))
    (htip : ∃ r > 0, (O.dom : Set ℂ) ∩ ball p r ⊆ I.dom)
    (hshared : ∀ x ∈ S, x < v →
      ∃ r > 0, (O.dom : Set ℂ) ∩ ball (EO (x : ℂ)) r ⊆ I.dom) :
    Nonempty (R6Tr.SameTimeLeftData O I EO P p v w) := by
  have hEr : Continuous (fun x : ℝ => EO (x : ℂ)) :=
    hEOc.comp_continuous Complex.continuous_ofReal (fun x => R6Fc.real_mem_Hbar x)
  let K := {x ∈ Icc v 0 | EO (x : ℂ) = p}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_eq hEr continuous_const)
  have hKne : K.Nonempty := ⟨0, ⟨hv.le, le_rfl⟩, by simpa using hEO0⟩
  obtain ⟨b₀, hb₀⟩ := hK.exists_isLeast hKne
  have hvb₀ : v < b₀ := lt_of_le_of_ne hb₀.1.1.1 fun he => hvtip (he ▸ hb₀.1.2)
  have hbefore : ∀ x ∈ Ico v b₀, EO (x : ℂ) ≠ p := by
    intro x hx he
    exact (not_le_of_gt hx.2) (hb₀.2 ⟨⟨hx.1, hx.2.le.trans hb₀.1.1.2⟩, he⟩)
  have hopen : IsOpen {x ∈ S | EO (x : ℂ) ≠ p} :=
    hSo.inter (isClosed_eq hEr continuous_const).isOpen_compl
  obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.1 hopen v ⟨hvS, hvtip⟩
  let a := v - δ / 2
  let y := v - δ / 4
  have hay : a < y := by dsimp [a, y]; linarith
  have hyv : y < v := by dsimp [y]; linarith
  have haS : a ∈ S ∧ EO (a : ℂ) ≠ p := by
    apply hδS
    rw [mem_ball, Real.dist_eq, abs_of_neg]
    · dsimp [a]; linarith
    · dsimp [a]; linarith
  obtain ⟨r, hr, htipball⟩ := htip
  have hbE : EO (b₀ : ℂ) = p := hb₀.1.2
  obtain ⟨ε, hε, hεE⟩ := Metric.continuousAt_iff.1 hEr.continuousAt (r / 2) (half_pos hr)
  let d := min ε (b₀ - v) / 2
  have hd : 0 < d := half_pos (lt_min hε (sub_pos.2 hvb₀))
  let ξ := b₀ - d
  let b := (ξ + b₀) / 2
  have hvξ : v < ξ := by
    have := min_le_right ε (b₀ - v)
    dsimp [ξ, d]; linarith
  have hξb : ξ < b := by dsimp [b, ξ]; linarith
  have hbb₀ : b < b₀ := by dsimp [b, ξ]; linarith
  have hb0 : b < 0 := hbb₀.trans_le hb₀.1.1.2
  have hξ0 : ξ < 0 := hξb.trans hb0
  have hbS : b ∈ S := hSc.ordConnected.out hvS h0S ⟨(hvξ.trans hξb).le, hb0.le⟩
  have hKS : Icc a b ⊆ S := hSc.ordConnected.out haS.1 hbS
  have hav : a < v := hay.trans hyv
  have hyJ : y ∈ Ioo a b := ⟨hay, hyv.trans (hvξ.trans hξb)⟩
  have hξJ : ξ ∈ Ioo a b := ⟨hav.trans hvξ, hξb⟩
  have haway : ∀ x ∈ Icc a b, EO (x : ℂ) ≠ p := by
    intro x hx
    by_cases hxv : x ≤ v
    · apply (hδS ?_).2
      rw [mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hxv)]
      dsimp [a] at hx
      linarith [hx.1]
    · exact hbefore x ⟨(lt_of_not_ge hxv).le, hx.2.trans_lt hbb₀⟩
  have hξE : dist (EO (ξ : ℂ)) p < r / 2 := by
    rw [← hbE]
    apply hεE
    rw [Real.dist_eq, abs_of_neg (sub_neg.2 (hξb.trans hbb₀))]
    have := min_le_left ε (b₀ - v)
    dsimp [ξ, d]
    linarith
  have hξball : ∃ e > 0, (O.dom : Set ℂ) ∩ ball (EO (ξ : ℂ)) e ⊆ I.dom := by
    refine ⟨r / 2, half_pos hr, fun z hz => htipball ⟨hz.1, mem_ball.2 ?_⟩⟩
    exact (dist_triangle z (EO (ξ : ℂ)) p).trans_lt
      (by linarith only [mem_ball.1 hz.2, hξE])
  refine ⟨{
    compact := Icc a b, interval := Ioo a b, shared := y, exposed := ξ, boundary := g
    isCompact := isCompact_Icc, interval_subset := Ioo_subset_Icc_self
    isOpen := isOpen_Ioo, isPreconnected := isPreconnected_Ioo
    shared_mem := hyJ, exposed_mem := hξJ
    shared_lt := hyv, lt_exposed := hvξ, exposed_neg := hξ0
    inclusion := hIncl, collars := fun x hx => hcollars x (hKS hx)
    avoids_tip := haway
    landing_mem := fun x hx => hlanding x (hKS (Ioo_subset_Icc_self hx))
    boundary_limit := fun x hx => hlim x (hKS (Ioo_subset_Icc_self hx))
    shared_image_lt := ?_, lt_exposed_image := ?_, exposed_image_neg := ?_
    shared_ball := hshared y (hKS (Ioo_subset_Icc_self hyJ)) hyv
    exposed_ball := hξball }⟩
  · rw [← hgv]
    exact hg (hKS (Ioo_subset_Icc_self hyJ)) hvS hyv
  · rw [← hgv]
    exact hg hvS (hKS (Ioo_subset_Icc_self hξJ)) hvξ
  · rw [← hg0]
    exact hg (hKS (Ioo_subset_Icc_self hξJ)) h0S hξ0

end InteractingSLE.Sec7.R6Lw
