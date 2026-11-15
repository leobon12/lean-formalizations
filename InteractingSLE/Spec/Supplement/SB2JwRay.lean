/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkCorr
import InteractingSLE.Spec.Supplement.FlowDilateFlow
import InteractingSLE.Spec.Supplement.G12Statement
import InteractingSLE.Spec.Sec4.ZeroMarksAvoid
import InteractingSLE.Spec.Exist.StagedLawData

/-!
# SB2(2): the ray correspondence from a boundary profile (item 4a, deterministic)

Packet PROVE-SB2-LIFTSET (round 17). The upper chart maps the free ray `(R, ∞)` right of the upper history onto the
positive ray through its real boundary values `f` (continuous, strictly increasing, `f → e` at `R⁺`, unbounded). With
`ι = rayMap f R e` (`f − e` right of `R`, `0` at `R`), if the conditional data `b'` read through `f` are the original
data `b` (off finite sets), then `ι` is a ray correspondence between `b` and the relative data `affData 1 (−e) b'`:

* `strictMonoOn_Ioi_of_injOn`: a continuous injective profile that increases far out increases on the whole ray;
* `rightLim_comp_eq`, `leftLim_comp_eq`: the one-sided limits of `b'` at `f x` (and at `e`) are those of `b` at `x`;
* **`rayCorr_of_profile`**: `RayCorr b J (affData 1 (−e) b') (affJumps 1 (−e) J') R (rayMap f R e)`;
* `continuousOn_rayMap`: `ι` is continuous on `[R, ∞)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE.Theorem14.SB.Lk

open FlowDilate
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The ray map** of a boundary profile `f` over `R` with entry value `e`: `f − e` right of `R`, `0` elsewhere. -/
def rayMap (f : ℝ → ℝ) (R e : ℝ) (x : ℝ) : ℝ := if R < x then f x - e else 0

section Ray

variable {f : ℝ → ℝ} {R e : ℝ}

theorem rayMap_of_lt {x : ℝ} (hx : R < x) : rayMap f R e x = f x - e := if_pos hx

theorem rayMap_self : rayMap f R e R = 0 := if_neg (lt_irrefl R)

/-- **A continuous injective profile increasing far out increases on the whole ray.** -/
theorem strictMonoOn_Ioi_of_injOn (hc : ContinuousOn f (Ioi R)) (hi : InjOn f (Ioi R)) {a : ℝ}
    (hinc : StrictMonoOn f (Ioi (max R a))) : StrictMonoOn f (Ioi R) := by
  intro x hx y hy hxy
  set w₁ := max y (max R a + 1) with hw₁
  set w₂ := w₁ + 1 with hw₂
  have hyw : y ≤ w₁ := le_max_left _ _
  have hw₁a : max R a < w₁ := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have hsub : Icc x w₂ ⊆ Ioi R := fun z hz => lt_of_lt_of_le hx hz.1
  rcases (hc.mono hsub).strictMonoOn_of_injOn_Icc' (by linarith) (hi.mono hsub) with hm | ha
  · exact hm ⟨le_rfl, by linarith⟩ ⟨hxy.le, by linarith⟩ hxy
  · have h1 := ha ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (lt_add_one w₁)
    have h2 := hinc (show w₁ ∈ Ioi (max R a) from hw₁a) (show w₂ ∈ Ioi (max R a) by
      show max R a < w₁ + 1; linarith) (lt_add_one w₁)
    exact absurd h2 (not_lt.2 h1.le)

variable (hmono : StrictMonoOn f (Ioi R)) (hc : ContinuousOn f (Ioi R)) (hlim : Tendsto f (𝓝[>] R) (𝓝 e))
include hmono hlim

/-- The profile lies strictly above its entry value. -/
theorem lt_of_profile {y : ℝ} (hy : R < y) : e < f y := by
  set z := (R + y) / 2 with hz
  have hRz : R < z := by rw [hz]; linarith
  have hzy : z < y := by rw [hz]; linarith
  have hle : e ≤ f z := le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT hRz] with w hw
    exact (hmono hw.1 hRz hw.2).le)
  exact lt_of_le_of_lt hle (hmono hRz hy hzy)

include hc

/-- The profile tends to `f x` from above as `x' → x⁺` (`x ≥ R`; at `R` the value is `e`). -/
theorem tendsto_nhdsGT_profile {x : ℝ} (hx : R ≤ x) :
    Tendsto f (𝓝[>] x) (𝓝[>] (if R < x then f x else e)) := by
  rcases eq_or_lt_of_le hx with rfl | hlt
  · simp only [lt_irrefl, ↓reduceIte]
    refine tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact lt_of_profile hmono hlim hw
  · simp only [hlt, ↓reduceIte]
    refine tendsto_nhdsWithin_iff.2 ⟨(hc.continuousAt (Ioi_mem_nhds hlt)).tendsto.mono_left nhdsWithin_le_nhds,
      ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hmono hlt (lt_trans hlt hw) hw

/-- The profile tends to `f x` from below as `x' → x⁻` (`x > R`), staying right of `R`. -/
theorem tendsto_nhdsLT_profile {x : ℝ} (hx : R < x) : Tendsto f (𝓝[<] x) (𝓝[<] (f x)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨(hc.continuousAt (Ioi_mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT hx] with w hw hwR
  exact hmono hwR.1 hx hw

variable {b b' : ℝ → ℝ} {J J' : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
  (hb' : IsPiecewiseConstantBoundaryData b' J') {K : Finset ℝ}
  (hdat : ∀ x, R < x → x ∉ J → f x ∉ K → b' (f x) = b x)
include hb hb' hdat

/-- **The right limits correspond** (at `x ≥ R`; at `R` the profile's value is `e`). -/
theorem rightLim_comp_eq {x : ℝ} (hx : R ≤ x) : rightLim b' (if R < x then f x else e) = rightLim b x := by
  set p := if R < x then f x else e with hp
  obtain ⟨δ₁, hδ₁, h₁⟩ := Supp7.exists_pos_eq_lims hb x
  obtain ⟨δ₂, hδ₂, h₂⟩ := Supp7.exists_pos_eq_lims hb' p
  have hT := tendsto_nhdsGT_profile hmono hc hlim hx
  have hev : ∀ᶠ w in 𝓝[>] x, x < w ∧ w < x + δ₁ ∧ w ∉ J ∧ f w ∈ Ioo p (p + δ₂) ∧ f w ∉ K := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show x < x + δ₁ by linarith),
      Sec4.eventually_notMem_nhdsGT J x, hT.eventually (Ioo_mem_nhdsGT (show p < p + δ₂ by linarith)),
      hT.eventually (Sec4.eventually_notMem_nhdsGT K p)] with w h1 h2 h3 h4 h5
    exact ⟨h1, h2.2, h3, h4, h5⟩
  obtain ⟨w, hxw, hwδ, hwJ, ⟨hp1, hp2⟩, hwK⟩ := hev.exists
  have hRw : R < w := lt_of_le_of_lt hx hxw
  have e1 : b w = rightLim b x := by
    have := (h₁ (w - x) (by linarith) (by linarith)).2.2.1
    rwa [add_sub_cancel] at this
  have e2 : b' (f w) = rightLim b' p := by
    have := (h₂ (f w - p) (by linarith) (by linarith)).2.2.1
    rwa [add_sub_cancel] at this
  rw [← e2, hdat w hRw hwJ hwK, e1]

/-- **The left limits correspond** (at `x > R`). -/
theorem leftLim_comp_eq {x : ℝ} (hx : R < x) : leftLim b' (f x) = leftLim b x := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := Supp7.exists_pos_eq_lims hb x
  obtain ⟨δ₂, hδ₂, h₂⟩ := Supp7.exists_pos_eq_lims hb' (f x)
  have hT := tendsto_nhdsLT_profile hmono hc hlim hx
  have hev : ∀ᶠ w in 𝓝[<] x, w < x ∧ x - δ₁ < w ∧ R < w ∧ w ∉ J ∧ f w ∈ Ioo (f x - δ₂) (f x) ∧ f w ∉ K := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show x - δ₁ < x by linarith), Ioo_mem_nhdsLT hx,
      Sec4.eventually_notMem_nhdsLT J x, hT.eventually (Ioo_mem_nhdsLT (show f x - δ₂ < f x by linarith)),
      hT.eventually (Sec4.eventually_notMem_nhdsLT K (f x))] with w h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2.1, h3.1, h4, h5, h6⟩
  obtain ⟨w, hwx, hwδ, hRw, hwJ, ⟨hp1, hp2⟩, hwK⟩ := hev.exists
  have e1 : b w = leftLim b x := by
    have := (h₁ (x - w) (by linarith) (by linarith)).2.2.2
    rwa [sub_sub_cancel] at this
  have e2 : b' (f w) = leftLim b' (f x) := by
    have := (h₂ (f x - f w) (by linarith) (by linarith)).2.2.2
    rwa [sub_sub_cancel] at this
  rw [← e2, hdat w hRw hwJ hwK, e1]

/-- **The ray correspondence from a boundary profile.** -/
theorem rayCorr_of_profile (hunb : ∀ M, ∃ x, R < x ∧ M < f x) :
    RayCorr b J (affData 1 (-e) b') (affJumps 1 (-e) J') R (rayMap f R e) := by
  have hb₂ := isPiecewiseConstantBoundaryData_affData (m := -e) one_pos hb'
  have haff : ∀ x, R < x → (rayMap f R e x - -e) / 1 = f x := fun x hx => by
    rw [rayMap_of_lt hx]; ring
  have haffR : (rayMap f R e R - -e) / 1 = e := by rw [rayMap_self]; ring
  refine ⟨?_, rayMap_self, ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · -- strictly increasing on `[R, ∞)`
    intro x hx y hy hxy
    have hRy : R < y := lt_of_le_of_lt hx hxy
    rw [rayMap_of_lt hRy]
    rcases eq_or_lt_of_le (show R ≤ x from hx) with rfl | hRx
    · rw [rayMap_self]; linarith [lt_of_profile hmono hlim hRy]
    · rw [rayMap_of_lt hRx]; linarith [hmono hRx hRy hxy]
  · -- onto `[0, ∞)`
    intro y hy
    rcases eq_or_lt_of_le hy with rfl | hpos
    · exact ⟨R, le_rfl, rayMap_self⟩
    obtain ⟨x₁, hx₁, hfx₁⟩ := hunb (y + e)
    have hev : ∀ᶠ w in 𝓝[>] R, f w < y + e ∧ w < x₁ ∧ R < w := by
      filter_upwards [hlim.eventually (gt_mem_nhds (show e < y + e by linarith)), Ioo_mem_nhdsGT hx₁]
        with w h1 h2
      exact ⟨h1, h2.2, h2.1⟩
    obtain ⟨x₀, hx₀, hx₀₁, hRx₀⟩ := hev.exists
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hx₀₁.le (hc.mono fun z hz => lt_of_lt_of_le hRx₀ hz.1)
      ⟨hx₀.le, hfx₁.le⟩
    exact ⟨x, (lt_of_lt_of_le hRx₀ hx.1).le, by rw [rayMap_of_lt (lt_of_lt_of_le hRx₀ hx.1), hfx]; ring⟩
  · -- right limits
    rw [rightLim_affData one_pos hb']
    rcases eq_or_lt_of_le (show R ≤ x from hx) with rfl | hRx
    · rw [haffR]
      have := rightLim_comp_eq hmono hc hlim hb hb' hdat (le_refl R)
      simpa only [lt_irrefl, ↓reduceIte] using this
    · rw [haff x hRx]
      have := rightLim_comp_eq hmono hc hlim hb hb' hdat hRx.le
      simpa only [hRx, ↓reduceIte] using this
  · -- left limits
    rw [leftLim_affData one_pos hb', haff x hx]
    exact leftLim_comp_eq hmono hc hlim hb hb' hdat hx
  · -- the genuine jumps
    rw [mem_jumpSet_affData one_pos hb', haff x hx]
    have hr : rightLim b' (f x) = rightLim b x := by
      have := rightLim_comp_eq hmono hc hlim hb hb' hdat hx.le
      simpa only [hx, ↓reduceIte] using this
    have hl := leftLim_comp_eq hmono hc hlim hb hb' hdat hx
    simp only [PiecewiseConstantBoundaryData.jumpSet, Finset.mem_filter, hr, hl]
    constructor
    · rintro ⟨-, hne⟩
      refine ⟨?_, hne⟩
      by_contra hxJ
      exact hne ((Exist.StagedLaw.leftLim_eq_of_notMem hb hxJ).trans
        (Exist.StagedLaw.rightLim_eq_of_notMem hb hxJ).symm)
    · rintro ⟨-, hne⟩
      refine ⟨?_, hne⟩
      by_contra hfJ
      apply hne
      rw [← hl, ← hr]
      exact (Exist.StagedLaw.leftLim_eq_of_notMem hb' hfJ).trans
        (Exist.StagedLaw.rightLim_eq_of_notMem hb' hfJ).symm

end Ray

/-- **The ray map is continuous on `[R, ∞)`.** -/
theorem continuousOn_rayMap {f : ℝ → ℝ} {R e : ℝ} (hc : ContinuousOn f (Ioi R))
    (hlim : Tendsto f (𝓝[>] R) (𝓝 e)) : ContinuousOn (rayMap f R e) (Ici R) := by
  intro x hx
  rcases eq_or_lt_of_le (show R ≤ x from hx) with hRx | hRx
  · subst hRx
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, rayMap_self]
    have h1 : Tendsto (fun w => f w - e) (𝓝[>] R) (𝓝 (e - e)) := hlim.sub_const e
    rw [sub_self] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (rayMap_of_lt hw).symm
  · have h1 : ContinuousAt (fun w => f w - e) x :=
      (hc.continuousAt (Ioi_mem_nhds hRx)).sub continuousAt_const
    have h2 : (fun w => f w - e) =ᶠ[𝓝 x] rayMap f R e := by
      filter_upwards [Ioi_mem_nhds hRx] with w hw
      exact (rayMap_of_lt hw).symm
    exact (h1.congr h2).continuousWithinAt

end InteractingSLE.Theorem14.SB.Lk
