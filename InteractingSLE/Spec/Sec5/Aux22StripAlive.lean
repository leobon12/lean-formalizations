/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripPull
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import Mathlib.Analysis.Complex.Convex

/-!
# Aux. lemma 22 in the strip, step 4b: a trace off `ℝ \ {0}` swallows no force point

Packet PROVE-SEC5-L (specification §4.1, Aux. lemma 22). Two deterministic facts used to exclude a separation of the old
and the new target strictly inside the strip life:

* **`exists_ball_notMem_fillH`** (planar): if a compact set `A` meets the real line at most in `0`, every real `x ≠ 0`
  has a ball outside the filling `fillH A` (a thin box along the real axis joins it to a vertical ray outside a large
  ball);
* **`forcePath_sub_eq_of_isForwardSol`** (ODE): if a real point `x` is alive on `[0, T]` (a forward solution `u`),
  the force path `v = x + ∫ 2/(v − w)` started at `x` satisfies `v − w = u` on `[0, T)` (uniqueness of forward
  solutions, `fwdMap_eq_of_isForwardSol`, applied up to the first meeting time); in particular it never meets the
  driver there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol H fwdMap fwdHull)

namespace InteractingSLE

namespace Sec5

namespace Aux22Strip

/-! ### The planar step -/

theorem convex_reProdIm {s t : Set ℝ} (hs : Convex ℝ s) (ht : Convex ℝ t) : Convex ℝ (s ×ℂ t) := by
  have h := Complex.convexHull_reProdIm s t
  rw [hs.convexHull_eq, ht.convexHull_eq] at h
  rw [← h]
  exact convex_convexHull ℝ _

/-- The box/ray argument for one real segment `[a, b]` avoiding `A` and reaching beyond the bound of `A`. -/
theorem exists_ball_notMem_fillH_aux {A : Set ℂ} (hA : IsCompact A) {R : ℝ} (hAR : A ⊆ closedBall 0 R)
    {a b e x : ℝ} (hab : ∀ r ∈ Icc a b, (r : ℂ) ∉ A) (hx : x ∈ Icc a b) (he : e ∈ Icc a b) (heR : R < |e|) :
    ∃ ρ > 0, ∀ z ∈ ball (x : ℂ) ρ, z ∉ fillH A := by
  set Seg : Set ℂ := ((↑) : ℝ → ℂ) '' Icc a b with hSeg
  have hSegc : IsCompact Seg := isCompact_Icc.image Complex.continuous_ofReal
  have hSegA : Seg ⊆ Aᶜ := by rintro _ ⟨r, hr, rfl⟩; exact hab r hr
  obtain ⟨δ, hδ, hδA⟩ := hSegc.exists_thickening_subset_open hA.isClosed.isOpen_compl hSegA
  set ρ : ℝ := δ / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  set Box : Set ℂ := Ioo (a - ρ) (b + ρ) ×ℂ Ioo 0 ρ with hBox
  set Ray : Set ℂ := {e} ×ℂ Ici (ρ / 2) with hRay
  have hAc : closure A = A := hA.isClosed.closure_eq
  have hBoxA : Box ⊆ H \ closure A := by
    intro w hw
    rw [hBox, Complex.mem_reProdIm] at hw
    refine ⟨hw.2.1, fun hwA => ?_⟩
    rw [hAc] at hwA
    set r : ℝ := max a (min w.re b) with hr
    have hrmem : r ∈ Icc a b := ⟨le_max_left _ _, max_le (hx.1.trans hx.2) (min_le_right _ _)⟩
    have hre : |w.re - r| ≤ ρ := by
      rw [abs_le]
      constructor
      · rcases le_total a (min w.re b) with h | h
        · rw [hr, max_eq_right h]
          rcases le_total w.re b with h' | h'
          · rw [min_eq_left h']; linarith
          · rw [min_eq_right h']; linarith [hw.1.2]
        · rw [hr, max_eq_left h]
          rcases le_total w.re b with h' | h'
          · rw [min_eq_left h'] at h; linarith [hw.1.1]
          · linarith [hw.1.2, hx.1, hx.2]
      · have : min w.re b ≤ r := le_max_right _ _
        rcases le_total w.re b with h' | h'
        · rw [min_eq_left h'] at this; linarith
        · rw [min_eq_right h'] at this; linarith [hw.1.2]
    have hwseg : w ∈ thickening δ Seg := by
      refine mem_thickening_iff.2 ⟨_, ⟨r, hrmem, rfl⟩, ?_⟩
      calc dist w (r : ℂ) ≤ |(w - r).re| + |(w - r).im| := by
            rw [Complex.dist_eq]; exact Complex.norm_le_abs_re_add_abs_im _
        _ = |w.re - r| + |w.im| := by simp
        _ ≤ ρ + ρ := add_le_add hre (by rw [abs_of_pos hw.2.1]; exact hw.2.2.le)
        _ < δ := by rw [hρ]; linarith
    exact hδA hwseg hwA
  have hRayA : Ray ⊆ H \ closure A := by
    intro w hw
    rw [hRay, Complex.mem_reProdIm] at hw
    refine ⟨lt_of_lt_of_le (half_pos hρ0) hw.2, fun hwA => ?_⟩
    rw [hAc] at hwA
    have h1 := hAR hwA
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 := Complex.abs_re_le_norm w
    rw [mem_singleton_iff.1 hw.1] at h2
    linarith
  have hconn : IsPreconnected (Box ∪ Ray) := by
    refine (convex_reProdIm (convex_Ioo _ _) (convex_Ioo _ _)).isPreconnected.union
      ((e : ℂ) + ((3 * ρ / 4 : ℝ) : ℂ) * Complex.I) ?_ ?_
      (convex_reProdIm (convex_singleton e) (convex_Ici _)).isPreconnected
    · rw [Complex.mem_reProdIm]
      have h1 : ((e : ℂ) + ((3 * ρ / 4 : ℝ) : ℂ) * Complex.I).re = e := by simp
      have h2 : ((e : ℂ) + ((3 * ρ / 4 : ℝ) : ℂ) * Complex.I).im = 3 * ρ / 4 := by simp
      rw [h1, h2]
      exact ⟨⟨by linarith [he.1], by linarith [he.2]⟩, by positivity, by linarith⟩
    · rw [Complex.mem_reProdIm]
      have h1 : ((e : ℂ) + ((3 * ρ / 4 : ℝ) : ℂ) * Complex.I).re = e := by simp
      have h2 : ((e : ℂ) + ((3 * ρ / 4 : ℝ) : ℂ) * Complex.I).im = 3 * ρ / 4 := by simp
      rw [h1, h2]
      exact ⟨rfl, by rw [mem_Ici]; linarith⟩
  have hunb : ¬ Bornology.IsBounded (Box ∪ Ray) := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    have h1 : ((e : ℂ) + ((max M 0 + ρ : ℝ) : ℂ) * Complex.I).re = e := by simp
    have h2 : ((e : ℂ) + ((max M 0 + ρ : ℝ) : ℂ) * Complex.I).im = max M 0 + ρ := by simp
    have hmem : (e : ℂ) + ((max M 0 + ρ : ℝ) : ℂ) * Complex.I ∈ Box ∪ Ray := by
      right
      rw [hRay, Complex.mem_reProdIm, h1, h2]
      exact ⟨rfl, by rw [mem_Ici]; linarith [le_max_right M 0]⟩
    have h3 := hM hmem
    rw [mem_closedBall, dist_zero_right] at h3
    have h4 := Complex.abs_im_le_norm ((e : ℂ) + ((max M 0 + ρ : ℝ) : ℂ) * Complex.I)
    rw [h2, abs_of_pos (by linarith [le_max_right M 0])] at h4
    linarith [le_max_left M 0]
  refine ⟨ρ, hρ0, fun z hz hzF => ?_⟩
  obtain ⟨hzH, hzF⟩ := hzF
  have hzBox : z ∈ Box := by
    rw [hBox, Complex.mem_reProdIm]
    have h1 : dist z x < ρ := hz
    rw [Complex.dist_eq] at h1
    have hre := (Complex.abs_re_le_norm (z - x)).trans_lt h1
    have him := (Complex.abs_im_le_norm (z - x)).trans_lt h1
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hre him
    rw [abs_lt] at hre
    rw [abs_lt] at him
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hzH, him.2⟩
  rcases hzF with hzA | hzb
  · exact (hBoxA hzBox).2 hzA
  · have hsub : Box ∪ Ray ⊆ connectedComponentIn (H \ closure A) z :=
      hconn.subset_connectedComponentIn (Or.inl hzBox) (union_subset hBoxA hRayA)
    exact hunb (hzb.subset hsub)

/-- **A real point off a compact set that meets `ℝ` at most in `0` has a ball outside its filling.** -/
theorem exists_ball_notMem_fillH {A : Set ℂ} (hA : IsCompact A) (hAR : ∀ r : ℝ, r ≠ 0 → (r : ℂ) ∉ A) {x : ℝ}
    (hx : x ≠ 0) : ∃ ρ > 0, ∀ z ∈ ball (x : ℂ) ρ, z ∉ fillH A := by
  obtain ⟨R₀, hR₀⟩ := hA.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 0 with hR
  have hAR' : A ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hR0 : 0 ≤ R := le_max_right _ _
  rcases lt_or_gt_of_ne hx with h | h
  · refine exists_ball_notMem_fillH_aux hA hAR' (a := min x (-(R + 1))) (b := x)
      (e := min x (-(R + 1))) (fun r hr => hAR r (by linarith [hr.2])) ⟨min_le_left _ _, le_rfl⟩
      ⟨le_rfl, min_le_left _ _⟩ ?_
    rw [abs_of_neg (by linarith [min_le_right x (-(R + 1))])]
    linarith [min_le_right x (-(R + 1))]
  · refine exists_ball_notMem_fillH_aux hA hAR' (a := x) (b := max x (R + 1)) (e := max x (R + 1))
      (fun r hr => hAR r (by linarith [hr.1])) ⟨le_rfl, le_max_left _ _⟩ ⟨le_max_left _ _, le_rfl⟩ ?_
    rw [abs_of_pos (by linarith [le_max_left x (R + 1)])]
    linarith [le_max_right x (R + 1)]

/-! ### The force path of an alive point -/

section Force

variable {W : ℝ → ℝ} {w v : ℝ≥0 → ℝ} {x : ℝ} {T : ℝ≥0} {u : ℝ → ℂ}

/-- Before a time up to which the force path has not met the driver, its gap is the forward solution. -/
theorem forceGap_eq_of_forall_ne (hW : Continuous W) (hWw : ∀ t : ℝ≥0, t < T → W t = w t)
    (hwc : ContinuousOn w (Iio T)) (hvc : ContinuousOn v (Iio T))
    (hveq : ∀ t : ℝ≥0, t < T → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hu : IsForwardSol W (x : ℂ) T u) {t₁ : ℝ≥0} (ht₁ : t₁ ≤ T) (hne : ∀ s : ℝ≥0, s < t₁ → v s ≠ w s)
    {t : ℝ≥0} (ht : t < t₁) : (((v t - w t : ℝ)) : ℂ) = u t := by
  set f : ℝ → ℂ := fun s => ((v s.toNNReal - w s.toNNReal : ℝ) : ℂ) with hf
  have htT : t < T := lt_of_lt_of_le ht ht₁
  have hmem : ∀ s ∈ Icc (0 : ℝ) t, s.toNNReal < t₁ := fun s hs => by
    refine lt_of_le_of_lt ?_ ht
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
    exact hs.2
  have hfc : ContinuousOn f (Icc 0 (t : ℝ)) := by
    have h1 : ContinuousOn (fun s : ℝ => v s.toNNReal - w s.toNNReal) (Icc 0 (t : ℝ)) :=
      (hvc.comp continuous_real_toNNReal.continuousOn fun s hs => (hmem s hs).trans_le ht₁).sub
        (hwc.comp continuous_real_toNNReal.continuousOn fun s hs => (hmem s hs).trans_le ht₁)
    exact Complex.continuous_ofReal.comp_continuousOn h1
  have hfs : IsForwardSol W (x : ℂ) t f := by
    refine ⟨hfc, fun s hs => ⟨?_, ?_⟩⟩
    · simp only [hf, ne_eq, Complex.ofReal_eq_zero, sub_eq_zero]
      exact hne _ (hmem s hs)
    · have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1
      have h1 := hveq s.toNNReal ((hmem s hs).trans_le ht₁)
      have h2 := hWw s.toNNReal ((hmem s hs).trans_le ht₁)
      rw [hs'] at h1 h2
      have h3 : (∫ r in (0 : ℝ)..s, 2 / f r) = ((∫ r in (0 : ℝ)..s,
          2 / (v r.toNNReal - w r.toNNReal) : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]
        refine intervalIntegral.integral_congr fun r _ => ?_
        simp only [hf]
        push_cast
        ring
      simp only [hf]
      rw [h3, h2, h1]
      push_cast
      ring
  have e1 := fwdMap_eq_of_isForwardSol hW hfs ⟨t.coe_nonneg, le_rfl⟩
  have e2 := fwdMap_eq_of_isForwardSol hW hu ⟨t.coe_nonneg, NNReal.coe_le_coe.2 htT.le⟩
  have e3 : f t = (((v t - w t : ℝ)) : ℂ) := by simp [hf]
  rw [← e3, ← e1, e2]

/-- **The force path of an alive point never meets the driver, and its gap is the forward solution.** -/
theorem forcePath_sub_eq_of_isForwardSol (hW : Continuous W) (hWw : ∀ t : ℝ≥0, t < T → W t = w t)
    (hwc : ContinuousOn w (Iio T)) (hvc : ContinuousOn v (Iio T))
    (hveq : ∀ t : ℝ≥0, t < T → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hu : IsForwardSol W (x : ℂ) T u) :
    ∀ t : ℝ≥0, t < T → (((v t - w t : ℝ)) : ℂ) = u t := by
  have hne : ∀ t : ℝ≥0, t < T → v t ≠ w t := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₀, ht₀T, ht₀⟩ := hcon
    set Z : Set ℝ≥0 := {t | t < T ∧ v t = w t} with hZ
    set t₁ : ℝ≥0 := sInf Z with ht₁
    have ht₁t₀ : t₁ ≤ t₀ := csInf_le (OrderBot.bddBelow _) (show t₀ ∈ Z from ⟨ht₀T, ht₀⟩)
    have ht₁T : t₁ < T := lt_of_le_of_lt ht₁t₀ ht₀T
    have hbefore : ∀ s : ℝ≥0, s < t₁ → v s ≠ w s := fun s hs h =>
      not_lt.2 (csInf_le (OrderBot.bddBelow _) (show s ∈ Z from ⟨hs.trans ht₁T, h⟩)) hs
    have hopen : IsOpen (Iio T) := isOpen_Iio
    have hvat : ContinuousAt v t₁ := hvc.continuousAt (hopen.mem_nhds ht₁T)
    have hwat : ContinuousAt w t₁ := hwc.continuousAt (hopen.mem_nhds ht₁T)
    -- `t₁` is a meeting time
    have hmeet : v t₁ = w t₁ := by
      by_contra hm
      have hev : ∀ᶠ s in 𝓝 t₁, v s - w s ≠ 0 :=
        (hvat.sub hwat).eventually_ne (sub_ne_zero.2 hm)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
      obtain ⟨s, ⟨hsT, hs⟩, hslt⟩ := exists_lt_of_csInf_lt ⟨t₀, show t₀ ∈ Z from ⟨ht₀T, ht₀⟩⟩
        (show t₁ < t₁ + (ε / 2).toNNReal from lt_add_of_pos_right _ (Real.toNNReal_pos.2 (half_pos hε)))
      have hs1 : t₁ ≤ s := csInf_le (OrderBot.bddBelow _) (show s ∈ Z from ⟨hsT, hs⟩)
      refine hball ?_ (sub_eq_zero.2 hs)
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hs1))]
      have := NNReal.coe_lt_coe.2 hslt
      rw [NNReal.coe_add, Real.coe_toNNReal _ (half_pos hε).le] at this
      linarith
    -- but at `t₁` the gap is the forward solution, which does not vanish
    have hu0 : u t₁ ≠ 0 := (hu.2 t₁ ⟨t₁.coe_nonneg, NNReal.coe_le_coe.2 ht₁T.le⟩).1
    have hgap : (((v t₁ - w t₁ : ℝ)) : ℂ) = u t₁ := by
      rcases eq_zero_or_pos t₁ with h0 | h0
      · have h1 := hveq t₁ ht₁T
        have h2 := hWw t₁ ht₁T
        have h3 := (hu.2 t₁ ⟨t₁.coe_nonneg, NNReal.coe_le_coe.2 ht₁T.le⟩).2
        rw [h0] at h1 h2 h3 ⊢
        simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero] at h1 h2 h3
        rw [NNReal.coe_zero, h3, h1, h2]
        push_cast
        ring
      · have hl : Tendsto (fun s : ℝ≥0 => (((v s - w s : ℝ)) : ℂ)) (𝓝[<] t₁) (𝓝 (((v t₁ - w t₁ : ℝ)) : ℂ)) :=
          (Complex.continuous_ofReal.continuousAt.tendsto.comp
            ((hvat.sub hwat).tendsto)).mono_left nhdsWithin_le_nhds
        have hu' : Tendsto (fun s : ℝ≥0 => u s) (𝓝[<] t₁) (𝓝 (u t₁)) := by
          have h1 : ContinuousWithinAt u (Icc 0 (T : ℝ)) t₁ :=
            hu.1 t₁ ⟨t₁.coe_nonneg, NNReal.coe_le_coe.2 ht₁T.le⟩
          have h2 : Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[<] t₁) (𝓝[Icc 0 (T : ℝ)] (t₁ : ℝ)) :=
            tendsto_nhdsWithin_iff.2 ⟨(NNReal.continuous_coe.tendsto _).mono_left nhdsWithin_le_nhds,
              by filter_upwards [self_mem_nhdsWithin] with s (hs : s < t₁) using
                ⟨s.coe_nonneg, NNReal.coe_le_coe.2 (hs.trans ht₁T).le⟩⟩
          exact h1.tendsto.comp h2
        have : (𝓝[<] t₁).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, h0⟩
        refine tendsto_nhds_unique hl (hu'.congr' ?_)
        filter_upwards [self_mem_nhdsWithin] with s (hs : s < t₁)
        exact (forceGap_eq_of_forall_ne hW hWw hwc hvc hveq hu ht₁T.le hbefore hs).symm
    rw [hmeet, sub_self, Complex.ofReal_zero] at hgap
    exact hu0 hgap.symm
  intro t ht
  exact forceGap_eq_of_forall_ne hW hWw hwc hvc hveq hu le_rfl hne ht

end Force

/-! ### Consequences -/

/-- **A force path from an alive point does not collide at the end**: if its gap tends to `0` at `T > 0`, the point is
not alive on `[0, T]`. -/
theorem not_isForwardSol_of_tendsto_gap {W : ℝ → ℝ} (hW : Continuous W) {w v : ℝ≥0 → ℝ} {x : ℝ} {T : ℝ≥0}
    (hT : 0 < T) (hWw : ∀ t : ℝ≥0, t < T → W t = w t) (hwc : ContinuousOn w (Iio T))
    (hvc : ContinuousOn v (Iio T))
    (hveq : ∀ t : ℝ≥0, t < T → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hlim : Tendsto (fun t => v t - w t) (𝓝[<] T) (𝓝 0)) {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u) :
    False := by
  have hrel := forcePath_sub_eq_of_isForwardSol hW hWw hwc hvc hveq hu
  have hu0 : u T ≠ 0 := (hu.2 T ⟨T.coe_nonneg, le_rfl⟩).1
  have hu' : Tendsto (fun s : ℝ≥0 => u s) (𝓝[<] T) (𝓝 (u T)) := by
    have h1 : ContinuousWithinAt u (Icc 0 (T : ℝ)) T := hu.1 T ⟨T.coe_nonneg, le_rfl⟩
    have h2 : Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[<] T) (𝓝[Icc 0 (T : ℝ)] (T : ℝ)) :=
      tendsto_nhdsWithin_iff.2 ⟨(NNReal.continuous_coe.tendsto _).mono_left nhdsWithin_le_nhds,
        by filter_upwards [self_mem_nhdsWithin] with s (hs : s < T) using
          ⟨s.coe_nonneg, NNReal.coe_le_coe.2 hs.le⟩⟩
    exact h1.tendsto.comp h2
  have hl : Tendsto (fun s : ℝ≥0 => u s) (𝓝[<] T) (𝓝 (((0 : ℝ)) : ℂ)) := by
    refine ((Complex.continuous_ofReal.tendsto _).comp hlim).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s < T)
    exact hrel s hs
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact hu0 ((tendsto_nhds_unique hu' hl).trans Complex.ofReal_zero)

/-- **A real point off the trace is alive**: if `η` generates the chain of a continuous driver on `[0, T]` with its
filling at `T`, and `η([0, T])` meets the real line at most in `0`, every real `x ≠ 0` is alive on `[0, T]`. -/
theorem exists_isForwardSol_of_trace_avoid {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {η : ℝ≥0 → ℂ}
    {T : ℝ≥0} (hηc : ContinuousOn η (Icc 0 T)) (hfill : IsFilling (fwdHull W T) (η '' Icc 0 T))
    (havoid : ∀ t : ℝ≥0, t ≤ T → ∀ z : ℝ, z ≠ 0 → η t ≠ z) {x : ℝ} (hx : x ≠ 0) :
    ∃ u, IsForwardSol W (x : ℂ) T u := by
  set A := η '' Icc 0 T with hA
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hηc
  have hK : fwdHull W T = fillH A := by
    have h := hfill
    rw [isFilling_iff_inter_H_eq_fillH hAc.isBounded hAc.isClosed,
      inter_eq_left.2 ((QuantumZipper.fwdHull_mono (W := W)).2 _)] at h
    exact h
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_notMem_fillH hAc (fun r hr ⟨t, ht, hη⟩ => havoid t ht.2 r hr hη) hx
  refine ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hx T.coe_nonneg hρ ?_
  rw [hK, Set.disjoint_left]
  exact fun z hz => hball z hz

end Aux22Strip

end Sec5

end InteractingSLE
