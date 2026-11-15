/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkMart9Ito

/-!
# The local spatial stops exhaust first-mark separation

The existing compact-interval argument is adapted from maximal paths to local
paths. It uses only continuity, distinct target gaps, and source exhaustion.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Mart9

open Zhan.Retarget

variable {Ω : Type*} {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω}

/-- The existing numerical localizers increase with the source announcing stops. -/
theorem localizer_mono
    (hgood : ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (hSm : ∀ ω, Monotone (S · ω)) (ω : Ω) :
    Monotone fun n => rLoc 0 G S W VL VR B e n ω := by
  intro m' n hmn
  have h := Sec2.TwoSeed.coe_capTime (fun ω => min (m' : ℝ≥0) (S m' ω))
    (fun ω => min (rHit 0 G W VL VR e m' ω)
      (MathFin.exitTime (Sec2.TwoSeed.brownG G B) m' ω)) ω
  have h' := Sec2.TwoSeed.coe_capTime (fun ω => min (n : ℝ≥0) (S n ω))
    (fun ω => min (rHit 0 G W VL VR e n ω)
      (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω
  show rLoc 0 G S W VL VR B e m' ω ≤ rLoc 0 G S W VL VR B e n ω
  rw [← WithTop.coe_le_coe]
  unfold rLoc
  rw [h, h']
  have hhit : rHit 0 G W VL VR e m' ω ≤ rHit 0 G W VL VR e n ω := by
    by_cases hω : ω ∈ G
    · simp only [rHit, hω, ↓reduceIte]
      exact Zhan.hitBelow_mono_fun fun s => rLev_mono hmn _
    · simp only [rHit, hω, ↓reduceIte, le_refl]
  refine min_le_min ?_ (min_le_min hhit (MathFin.exitTime_mono (continuous_brownG hgood) hmn ω))
  exact WithTop.coe_le_coe.2 (min_le_min (by exact_mod_cast hmn) (hSm ω hmn))

/-- Every source time strictly before first-mark separation is eventually below the localizers. -/
theorem exists_forall_le_localizer (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω)
    {ω : Ω} (hg : IsGood κ a b xL ρL ρR W B VL VR e S ω) (hωG : ω ∈ G)
    (hSm : Monotone (S · ω)) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < sepTime (W · ω) (VR 0 · ω) (e ω)) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → s ≤ rLoc 0 G S W VL VR B e n ω := by
  let k : Fin 2 := 0
  have hF := hg.path
  have hse : (s : ℝ≥0∞) < e ω := hs.trans_le (sepTime_le _ _ _)
  have hd := hg.data ha hab
  have hsub : Icc (0 : ℝ≥0) s ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) < e ω} := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast hr.2) hse
  have hsep : ∀ r ∈ Icc (0 : ℝ≥0) s, (r : ℝ≥0∞) < sepTime (W · ω) (VR k · ω) (e ω) := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast hr.2) hs
  have hne : (Icc (0 : ℝ≥0) s).Nonempty := ⟨0, le_rfl, bot_le⟩
  have hstc : ContinuousOn (fun r => ‖(Coupling.stateAt W VL VR r ω).2‖) (Icc 0 s) :=
    ((continuousOn_pi.2 hF.continuousOn_vL).prodMk (continuousOn_pi.2 hF.continuousOn_vR)).norm.mono hsub
  -- the reciprocal gaps
  set ψ : ℝ≥0 → ℝ := fun r => (VR k r ω - W r ω)⁻¹ +
    ∑ i ∈ Finset.univ.erase k, |VR k r ω - VR i r ω|⁻¹ with hψ
  have hψc : ContinuousOn ψ (Icc 0 s) := by
    refine ((((hF.continuousOn_vR k).sub hF.continuousOn_w).mono hsub).inv₀ fun r hr => ?_).add
      (continuousOn_finsetSum _ fun i hi => ((((hF.continuousOn_vR k).sub
        (hF.continuousOn_vR i)).mono hsub).abs.inv₀ fun r hr => ?_))
    · exact (sub_pos.2 (lt_of_lt_sepTime (hsep r hr))).ne'
    · exact abs_ne_zero.2 (hd.vR_ne (hsep r hr) i (Finset.ne_of_mem_erase hi))
  obtain ⟨r₂, hr₂, hmax₂⟩ := isCompact_Icc.exists_isMaxOn hne hstc
  obtain ⟨r₃, hr₃, hmax₃⟩ := isCompact_Icc.exists_isMaxOn hne (hg.contB.abs.continuousOn (s := Icc 0 s))
  obtain ⟨r₄, hr₄, hmax₄⟩ := isCompact_Icc.exists_isMaxOn hne hψc
  obtain ⟨m₀, hm₀⟩ := hg.cofinal s hs
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (max (s : ℝ) (max (‖(Coupling.stateAt W VL VR r₂ ω).2‖ + |B r₃ ω| + 1)
    (ψ r₄)))
  refine ⟨max m₀ n₁, fun n hn => ?_⟩
  have hn1 : n₁ ≤ n := (le_max_right _ _).trans hn
  have hnR : max (s : ℝ) (max (‖(Coupling.stateAt W VL VR r₂ ω).2‖ + |B r₃ ω| + 1) (ψ r₄)) < n :=
    hn₁.trans_le (by exact_mod_cast hn1)
  have hns : (s : ℝ) < n := (le_max_left _ _).trans_lt hnR
  have hnS : ‖(Coupling.stateAt W VL VR r₂ ω).2‖ + |B r₃ ω| + 1 < n :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hnR
  have hnψ : ψ r₄ < n := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hnR
  have hsS : s ≤ S n ω := hm₀.trans (hSm ((le_max_left _ _).trans hn))
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- a reciprocal below `n + 1` gives a gap above `δ_n`
  have hrecip : ∀ {x : ℝ}, 0 < x → x⁻¹ ≤ ψ r₄ → 1 / ((n : ℝ) + 1) ≤ x := by
    intro x hx hle
    rw [one_div, inv_le_comm₀ hn0 hx]
    linarith
  have hhit : (s : WithTop ℝ≥0) ≤ rHit k G W VL VR e n ω := by
    simp only [rHit, hωG, ↓reduceIte]
    refine Coupling.le_hitBelow fun r hre hr => ?_
    by_contra hlt
    push Not at hlt
    have hrI : r ∈ Icc (0 : ℝ≥0) s := ⟨bot_le, hlt.le⟩
    have hψr : (VR k r ω - W r ω)⁻¹ + ∑ i ∈ Finset.univ.erase k, |VR k r ω - VR i r ω|⁻¹ ≤ ψ r₄ :=
      isMaxOn_iff.1 hmax₄ r hrI
    have hq : 0 < VR k r ω - W r ω := sub_pos.2 (lt_of_lt_sepTime (hsep r hrI))
    have hterms : ∀ i ∈ Finset.univ.erase k, 0 ≤ |VR k r ω - VR i r ω|⁻¹ := fun i _ =>
      inv_nonneg.2 (abs_nonneg _)
    have hsum := Finset.sum_nonneg hterms
    refine absurd (rLev_nonneg_iff.2 ⟨?_, ?_, fun i hi => ?_⟩) (not_le.2 hr)
    · have := isMaxOn_iff.1 hmax₂ r hrI
      have h3 := abs_nonneg (B r₃ ω)
      linarith
    · show 1 / ((n : ℝ) + 1) ≤ VR k r ω - W r ω
      refine hrecip hq ?_
      linarith
    · have hi' : i ∈ Finset.univ.erase k := Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩
      have hpos : 0 < |VR k r ω - VR i r ω| := abs_pos.2 (hd.vR_ne (hsep r hrI) i hi)
      show 1 / ((n : ℝ) + 1) ≤ |VR k r ω - VR i r ω|
      refine hrecip hpos ?_
      have h1 := Finset.single_le_sum hterms hi'
      have h2 : 0 ≤ (VR k r ω - W r ω)⁻¹ := inv_nonneg.2 hq.le
      linarith
  have hexit : (s : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω := by
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    obtain ⟨r, hr, hBr⟩ := (MathFin.exitTime_le_iff (continuous_brownG hgood) n u ω).1 hu.symm.le
    have hus : u < s := by rw [← hu] at hlt; exact WithTop.coe_lt_coe.1 hlt
    have hrs : r ∈ Icc (0 : ℝ≥0) s := ⟨bot_le, hr.2.trans hus.le⟩
    have := isMaxOn_iff.1 hmax₃ r hrs
    simp only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at hBr
    have h2 := norm_nonneg (Coupling.stateAt W VL VR r₂ ω).2
    linarith
  have hsn : s ≤ min (n : ℝ≥0) (S n ω) := le_min (by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact hns.le) hsS
  have h := le_min (WithTop.coe_le_coe.2 hsn) (le_min hhit hexit)
  have hc := Sec2.TwoSeed.coe_capTime (fun ω => min (n : ℝ≥0) (S n ω))
    (fun ω => min (rHit k G W VL VR e n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω
  have h' : (s : WithTop ℝ≥0) ≤ (rLoc k G S W VL VR B e n ω : WithTop ℝ≥0) := by
    unfold rLoc; rw [hc]; exact h
  exact WithTop.coe_le_coe.1 h'

end InteractingSLE.Sec5.TwoMark.Mart9
