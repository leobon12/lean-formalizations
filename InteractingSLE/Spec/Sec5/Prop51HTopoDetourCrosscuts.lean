/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoDetourIntervals

/-!
# Completing every finite excursion, including its initial endpoint

The initial excursion has chart limit zero at time zero. Completing that case
removes the positive-start restriction from the earlier crosscut constructor.
Under no last contact, every excursion therefore has an actual finite crosscut.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- The initial finite excursion completes to a simple crosscut starting at
zero. The other endpoint is nonzero by the already proved prime-end limit. -/
theorem exists_initialExcursionCrosscut {η β : ℝ → ℂ} {w : ℝ → ℝ} {s b : ℝ}
    (hη : IsProperArc η) (hβ : IsLoewnerTrace w β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) (hb : 0 < b)
    (hD : MapsTo η (Ioo 0 b) (H \ cfHullQ w s))
    (hbD : η b ∉ H \ cfHullQ w s) (htip : negInv (β s) ∉ arcRange η) :
    ∃ c : FiniteExcursionCrosscut η w s 0 b, c.start = 0 := by
  have hmid : (0 : ℝ) < b / 2 := by linarith
  have hmidb : b / 2 < b := by linarith
  obtain ⟨x, hx, hlim₁⟩ := exists_tendsto_revChart_left hη hβ hw hw0 hs hmid hmidb
    (fun u hu => hD ⟨hmid.trans_le hu.1, hu.2⟩) hbD
    (fun he => htip ⟨b, hb.le, he⟩)
  have hη0 : Tendsto η (𝓝[>] 0) (𝓝[H \ cfHullQ w s] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := (hη.cont 0 (mem_Ici.2 le_rfl)).tendsto.mono_left
        (nhdsWithin_mono _ Ioi_subset_Ici_self)
      rwa [hη.zero] at h
    · have he : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 b := Ioo_mem_nhdsGT hb
      exact he.mono fun _ hu => hD hu
  have hlim₀ := (tendsto_revChart_zero hw hw0 hs).comp hη0
  let G : ℝ → ℂ := fun t => revChart w s (η t)
  have hGc : ContinuousOn G (Ioo 0 b) := (continuousOn_revChart hw hs).comp
    (hη.cont.mono fun _ hu => hu.1.le) hD
  let γ : ℝ → ℂ := extendFrom (Ioo 0 b) G
  have hγc : ContinuousOn γ (Icc 0 b) := continuousOn_Icc_extendFrom_Ioo hGc hlim₀ hlim₁
  have hγ₀ : γ 0 = 0 := eq_lim_at_left_extendFrom_Ioo hb hlim₀
  have hγ₁ : γ b = (x : ℂ) := eq_lim_at_right_extendFrom_Ioo hb hlim₁
  have hγG : EqOn γ G (Ioo 0 b) := extendFrom_extends hGc
  have hγH : MapsTo γ (Ioo 0 b) H := fun _ hu =>
    (hγG hu).symm ▸ revChart_mem_H hw hs (hD hu)
  have hi : InjOn γ (Ioo 0 b) := by
    intro u hu v hv he
    rw [hγG hu, hγG hv] at he
    have h := congrArg (revChartInv w s) he
    change revChartInv w s (revChart w s (η u)) =
      revChartInv w s (revChart w s (η v)) at h
    rw [revChartInv_revChart hw hw0 hs (hD hu),
      revChartInv_revChart hw hw0 hs (hD hv)] at h
    exact hη.inj hu.1.le hv.1.le h
  have hnonreal : ∀ u ∈ Ioo 0 b, ∀ y : ℝ, γ u ≠ (y : ℂ) := by
    intro u hu y he
    have h := hγH hu
    rw [he] at h
    exact lt_irrefl _ (show (0 : ℝ) < ((y : ℂ).im) from h)
  have hγi : InjOn γ (Icc 0 b) := by
    intro u hu v hv he
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hu with rfl | rfl | hu
    · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hv with rfl | rfl | hv
      · rfl
      · exact False.elim (hx (ofReal_injective (hγ₁.symm.trans (he.symm.trans hγ₀))))
      · exact False.elim (hnonreal v hv 0 (he.symm.trans hγ₀))
    · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hv with rfl | rfl | hv
      · exact False.elim (hx (ofReal_injective (hγ₁.symm.trans (he.trans hγ₀))))
      · rfl
      · exact False.elim (hnonreal v hv x (he.symm.trans hγ₁))
    · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hv with rfl | rfl | hv
      · exact False.elim (hnonreal u hu 0 (he.trans hγ₀))
      · exact False.elim (hnonreal u hu x (he.trans hγ₁))
      · exact hi hu hv he
  exact ⟨⟨γ, hγc, hγi, 0, x, by simpa using hγ₀, hγ₁, hγG, hγH⟩, rfl⟩

/-- Every bounded excursion interval has a completed finite crosscut. -/
theorem BoundedExcursionInterval.exists_crosscut {η β : ℝ → ℂ} {w : ℝ → ℝ}
    {s t : ℝ} (e : BoundedExcursionInterval η w s t)
    (hη : IsProperArc η) (hβ : IsLoewnerTrace w β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (htip : negInv (β s) ∉ arcRange η) :
    Nonempty (FiniteExcursionCrosscut η w s e.start e.finish) := by
  rcases e.start_nonneg.eq_or_lt with he | he
  · have hb : 0 < e.finish := he.trans_lt (e.start_lt.trans e.lt_finish)
    have hD := e.mapsTo
    rw [← he] at hD
    obtain ⟨c, _⟩ := exists_initialExcursionCrosscut hη hβ hw hw0 hs hb hD
      e.finish_outside htip
    rw [← he]
    exact ⟨c⟩
  · exact exists_finiteExcursionCrosscut hη hβ hw hw0 hs he
      (e.start_lt.trans e.lt_finish) e.mapsTo e.start_outside e.finish_outside htip

/-- The forward gate of a completed finite excursion has the prescribed
western sign. This also covers the initial excursion. -/
theorem FiniteExcursionCrosscut.finish_neg_of_western
    {η : ℝ → ℂ} {w : ℝ → ℝ} {s a b : ℝ}
    (c : FiniteExcursionCrosscut η w s a b) (ha : 0 ≤ a) (hab : a < b)
    (hD : MapsTo η (Ioo a b) (H \ cfHullQ w s))
    (hbD : η b ∉ H \ cfHullQ w s) (hends : HasWesternExcursionEnds η w s) :
    c.finish < 0 := by
  have ham : a < (a + b) / 2 := by linarith
  have hmb : (a + b) / 2 < b := by linarith
  obtain ⟨x, hx, hlim⟩ := hends.1 ((a + b) / 2) b (ha.trans_lt ham) hmb
    (fun u hu => hD ⟨ham.trans_le hu.1, hu.2⟩) hbD
  have he : c.finish = x := ofReal_injective
    (tendsto_nhds_unique (c.tendsto_finish hab) hlim)
  exact he ▸ hx

/-- Distinct time components have disjoint open crosscut ranges. Only the
conformal inverse identity and injectivity of the original proper arc enter. -/
theorem FiniteExcursionCrosscut.disjoint_interiors
    {η : ℝ → ℂ} {w : ℝ → ℝ} {s t u : ℝ}
    (e : BoundedExcursionInterval η w s t) (f : BoundedExcursionInterval η w s u)
    (c : FiniteExcursionCrosscut η w s e.start e.finish)
    (d : FiniteExcursionCrosscut η w s f.start f.finish)
    (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (hne : connectedComponentIn (excursionTimes η w s) t ≠
      connectedComponentIn (excursionTimes η w s) u) :
    Disjoint (c.path '' Ioo e.start e.finish) (d.path '' Ioo f.start f.finish) := by
  refine disjoint_left.2 ?_
  rintro _ ⟨v, hv, rfl⟩ ⟨v', hv', he⟩
  have hc := c.interior_eq hv
  have hd := d.interior_eq hv'
  have hchart : revChart w s (η v) = revChart w s (η v') := hc.symm.trans
    (he.symm.trans hd)
  have h := congrArg (revChartInv w s) hchart
  rw [revChartInv_revChart hw hw0 hs (e.mapsTo hv),
    revChartInv_revChart hw hw0 hs (f.mapsTo hv')] at h
  have hv0 := e.start_nonneg.trans_lt hv.1
  have hv'0 := f.start_nonneg.trans_lt hv'.1
  have heq : v = v' := hη.inj hv0.le hv'0.le h
  have hvC : v ∈ connectedComponentIn (excursionTimes η w s) t := by
    rwa [e.component_eq]
  have hvC' : v ∈ connectedComponentIn (excursionTimes η w s) u := by
    rw [f.component_eq, heq]
    exact hv'
  exact hne ((connectedComponentIn_eq hvC).trans (connectedComponentIn_eq hvC').symm)

end InteractingSLE.Sec5.Prop51HTopo
