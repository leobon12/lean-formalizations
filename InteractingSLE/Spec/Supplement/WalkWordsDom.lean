/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsSide
import InteractingSLE.Spec.Sec5.TimeDensity
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc
import InteractingSLE.Foundations.Loewner.YuanCorollary13

/-!
# Near a fresh trace point the hull is the trace

Packet PROVE-WALK-WORDS (the domain hypothesis of `nonempty_sideIdentification`). Let `η` be a Loewner trace of a
continuous driver `W` (`W 0 = 0`), injective on `[0, τ]`, with `η((s₀, τ]) ⊆ ℍ`. Then:

* `notMem_fwdHull_of_notMem_image`: a point of `ℍ \ K_{s₀}` off `η((s₀, τ])` is off `K_τ` (the hull grows after
  `s₀` only by the trace: `K_τ \ K_{s₀} = F_{s₀}(K̃)` with `K̃` the hull of the shifted trace `γ̃`
  (`Sec5.fwdHull_add_sdiff_eq_image`, `IsLoewnerTrace.isLoewnerTrace_shift`), and `γ̃` is a simple path started on
  `ℝ` and otherwise in `ℍ`, whose filling is the path itself (`YuanCharacterisation.fillH_image_eq`));
* `mem_H_diff_fwdHull_of_lt`: `η(t) ∈ ℍ \ K_{s₀}` for `s₀ < t ≤ τ` (a trace point is adherent to the current domain
  and the filling's frontier in `ℍ` lies on `η([0, s₀])`);
* **`exists_ball_mem_loewner_image`**: in a chart `c₀` (conformal), every physical point near `c₀⁻¹(η(t))` off the
  physical trace `c₀⁻¹(η((s₀, τ]))` lies in the domain of the prefix chart `c₀.loewner W τ`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric Bornology
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.WalkWords

section Dom

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The hull grows only by the trace after `s₀`.** -/
theorem notMem_fwdHull_of_notMem_image (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s₀ τ : ℝ} (hs₀ : 0 ≤ s₀) (hs₀τ : s₀ ≤ τ) (hinj : InjOn η (Icc 0 τ)) (hH : ∀ s ∈ Ioc s₀ τ, η s ∈ H)
    {z : ℂ} (hz : z ∈ H \ fwdHull W s₀) (hzη : z ∉ η '' Ioc s₀ τ) : z ∉ fwdHull W τ := by
  intro hzK
  set u : ℝ := τ - s₀ with hudef
  have hu : 0 ≤ u := by rw [hudef]; linarith
  have hτu : τ = s₀ + u := by rw [hudef]; ring
  have hmem : z ∈ fwdHull W (s₀ + u) \ fwdHull W s₀ := ⟨hτu ▸ hzK, hz.2⟩
  rw [Sec5.fwdHull_add_sdiff_eq_image hW hW0 hs₀ hu] at hmem
  obtain ⟨w, hwK, rfl⟩ := hmem
  -- the shifted trace
  obtain ⟨hγ, hγF⟩ := hη.isLoewnerTrace_shift_and_extendFrom hW hW0 hs₀
  set γ : ℝ → ℂ := InteractingSLE.loewnerTip (shiftDrive W s₀) with hγdef
  have hγc : ContinuousOn γ (Icc 0 u) := hγ.2.1.mono fun r hr => hr.1
  have hγreal : ∀ r ∈ Ioc 0 u, γ r ∈ H := by
    intro r hr
    have hF := hγF r hr.1.le
    have hηH : η (s₀ + r) ∈ H := hH _ ⟨by linarith [hr.1], by linarith [hr.2]⟩
    by_contra hγH
    have him : (γ r).im = 0 := by
      have hbar : 0 ≤ (γ r).im := (hη.extendFrom_shift_tip hW hW0 hs₀ hr.1.le).1
      exact le_antisymm (not_lt.1 hγH) hbar
    have he : γ r = (((γ r).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rcases WalkNorm.extendFrom_real_cases hη hW hW0 hs₀ (γ r).re with h | ⟨s, hs, hse⟩
    · rw [← he, hF] at h
      exact absurd hηH (by show ¬ 0 < (η (s₀ + r)).im; rw [h]; exact lt_irrefl 0)
    · rw [← he, hF] at hse
      have := hinj ⟨hs.1, hs.2.trans hs₀τ⟩ ⟨by linarith [hr.1], by linarith [hr.2]⟩ hse
      linarith [hs.2, hr.1]
  have hγi : InjOn γ (Icc 0 u) := by
    intro r hr r' hr' he
    have h1 := hγF r hr.1
    have h2 := hγF r' hr'.1
    rw [he] at h1
    have := hinj ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ ⟨by linarith [hr.1], by linarith [hr.2]⟩
      (h2.symm.trans h1)
    linarith
  have hγ0 : (γ 0).im = 0 := by rw [hγ.1]; simp
  have hK : fwdHull (shiftDrive W s₀) u = γ '' Ioc 0 u := by
    rw [hγ.2.2 u hu]
    exact YuanCharacterisation.fillH_image_eq hu hγc hγi hγ0 fun r hr => hγreal r hr
  rw [hK] at hwK
  obtain ⟨r, hr, rfl⟩ := hwK
  apply hzη
  refine ⟨s₀ + r, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
  rw [← hγF r hr.1.le, ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hs₀ (hγreal r hr)]

/-- **A later trace point is outside the earlier hull.** -/
theorem mem_H_diff_fwdHull_of_lt (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s₀ t τ : ℝ} (hs₀ : 0 ≤ s₀) (hs₀t : s₀ < t) (htτ : t ≤ τ) (hinj : InjOn η (Icc 0 τ)) (hH : η t ∈ H) :
    η t ∈ H \ fwdHull W s₀ := by
  refine ⟨hH, fun hK => ?_⟩
  have ht0 : 0 ≤ t := hs₀.trans hs₀t.le
  have hcl : η t ∈ closure (H \ fwdHull W s₀) := by
    have hlim := hη.tendsto_fwdMapInv_tip hW hW0 ht0
    have := FiniteEndpoint.neBot_nhdsWithin_H (z := (0 : ℂ)) (by simp)
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have h1 : fwdMapInv W t w ∈ H \ fwdHull W t := by
      rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 ht0]; exact ⟨w, hw, rfl⟩
    exact ⟨h1.1, fun h => h1.2 (WangWu.fwdHull_mono hs₀t.le h)⟩
  rw [hη.2.2 s₀ hs₀] at hK hcl
  have hc := mem_closure_of_mem_fillH_of_mem_closure hK hcl
  have hcomp : IsCompact (η '' Icc 0 s₀) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun r hr => hr.1)
  rw [hcomp.isClosed.closure_eq] at hc
  obtain ⟨r, hr, hre⟩ := hc
  have := hinj ⟨hr.1, hr.2.trans (hs₀t.le.trans htτ)⟩ ⟨ht0, htτ⟩ hre
  linarith [hr.2]

/-- **Physical points near a fresh trace point and off the fresh trace lie in the prefix chart's domain.** -/
theorem exists_ball_mem_loewner_image {c₀ : Chart} (hc₀ : c₀.IsConformal) (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s₀ t τ : ℝ} (hs₀ : 0 ≤ s₀) (hs₀t : s₀ < t) (htτ : t ≤ τ)
    (hinj : InjOn η (Icc 0 τ)) (hH : ∀ s ∈ Ioc s₀ τ, η s ∈ H) :
    ∃ ρ > 0, ∀ w ∈ ball (c₀.2.1 (η t)) ρ, w ∉ c₀.2.1 '' (η '' Ioc s₀ τ) → w ∈ (c₀.loewner W τ).2.1 '' H := by
  have hτ0 : 0 ≤ τ := hs₀.trans (hs₀t.le.trans htτ)
  have htH : η t ∈ H := hH t ⟨hs₀t, htτ⟩
  have hU : IsOpen (H \ fwdHull W s₀) := (isHPHull_fwdHull hW hs₀).isOpen
  have htU : η t ∈ H \ fwdHull W s₀ := mem_H_diff_fwdHull_of_lt hη hW hW0 hs₀ hs₀t htτ hinj htH
  have hmem : c₀.2.1 (η t) ∈ c₀.2.1 '' H := ⟨_, htH, rfl⟩
  have hcont : ContinuousAt c₀.1 (c₀.2.1 (η t)) :=
    (hc₀.differentiableOn_fwd.differentiableAt (by
      rw [hc₀.coe_dom]; exact hc₀.isOpen_image.mem_nhds hmem)).continuousAt
  have hev : ∀ᶠ w in 𝓝 (c₀.2.1 (η t)), w ∈ c₀.2.1 '' H ∧ c₀.1 w ∈ H \ fwdHull W s₀ := by
    refine Filter.Eventually.and (hc₀.isOpen_image.mem_nhds hmem) ?_
    have h := hcont.tendsto
    rw [hc₀.2.2 _ htH] at h
    exact h.eventually (hU.mem_nhds htU)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ρ, hρ, fun w hw hwη => ?_⟩
  obtain ⟨⟨w', hw'H, rfl⟩, hw'U⟩ := hball w hw
  rw [hc₀.2.2 w' hw'H] at hw'U
  have hw'η : w' ∉ η '' Ioc s₀ τ := fun h => hwη ⟨w', h, rfl⟩
  have hw'K := notMem_fwdHull_of_notMem_image hη hW hW0 hs₀ (hs₀t.le.trans htτ) hinj hH hw'U hw'η
  have hw'D : w' ∈ fwdMapInv W τ '' H := by
    rw [QuantumZipper.RS.image_fwdMapInv_H hW hW0 hτ0]; exact ⟨hw'H, hw'K⟩
  obtain ⟨v, hv, hve⟩ := hw'D
  exact ⟨v, hv, by show c₀.2.1 (fwdMapInv W τ v) = c₀.2.1 w'; rw [hve]⟩

end Dom

end InteractingSLE.Theorem14.WalkWords
