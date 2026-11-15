/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWClock
import InteractingSLE.Spec.Sec5.Aux61SlitWGeometry

/-!
# Positive-time glued slit geometry for the selected-access code

Packet PROVE-AUX61-SLITW. The physical trace and the original-target restart
chart supply CONFIG's `IsGluedSlit` at every positive live capacity time.
The code's chart trace, hull and tip are derived from the inverse capacity
clock, without assuming their correspondence with the physical path.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW

open Aux61FibData Aux61GInst Aux61Fib Aux61Conf2
open Aux61Restart (physicalRestartLog stripTargetHull)

/-- The positive-time geometry of the access-based code, with exactly the
physical and original-target chart hypotheses; its chart-side clauses are proved. -/
theorem exists_isGluedSlit_accessExitCode
    {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
    {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
    (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding E c ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
    (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V)
    {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens} {x : X} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life) (hq0 : 0 < q)
    {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ} {D : Set ℂ}
    (hW : Continuous Wph) (hW0 : Wph 0 = 0) (hη : IsLoewnerTrace Wph η) (hr : 0 < r)
    (hi : InjOn η (Ico 0 (r + exitNN E c ρ T V x)))
    (hH : ∀ u ∈ Ioo 0 (r + exitNN E c ρ T V x), η u ∈ H)
    (hρ : ∀ u : ℝ≥0, 0 < u → u < exitNN E c ρ T V x → ρ x u = η (r + u))
    (hdom : ((c x).dom : Set ℂ) = D) (hsub : D ⊆ H \ fwdHull Wph r)
    (hsimply : IsSimplyConnected D) (htarget : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D)
    (hinfty : Tendsto (fun z : ℂ => ‖(c x).1 (z + 1)‖) (𝓝[H] 0) atTop)
    (hlift : ∀ z ∈ D, (c x).2.2 z = (physicalRestartLog (stripTargetHull D) z).im)
    (hcollar : ∃ δ > 0, MapsTo (fwdMapInv Wph r) (ball 0 δ ∩ H) D)
    (hcurrent : Tendsto (fun z => (c x).1 (fwdMapInv Wph r z)) (𝓝[H] 0) (𝓝 0)) :
    ∃ Tc : ℝ, IsGluedSlit Wph η r
      (accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q)
      (c x) D (fun u : ℝ => (accessExitCode E c ρ T V a k h x).driver u.toNNReal)
      (fun u : ℝ => (accessExitCode E c ρ T V a k h x).trace u.toNNReal) Tc q := by
  let s := accessExitCode E c ρ T V a k h x
  let τ := accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q
  have hx := mem_exitEv_of_lt_accessLife hq
  have hτ : τ < exitNN E c ρ T V x := (accessTime_spec hs hV hV0 hland hinj hq).1
  have hτ0 : 0 < τ := accessTime_pos hs hV hV0 hland hinj hq hq0
  have hgood : PathGood d s := pathGood_accessExitCode hs hV hV0 hland hinj d hdV hℓ hx
  obtain ⟨Tc, hqTc, htrace, hcinj, hcmem⟩ := exists_chartTrace_of_code hgood.1 hgood.2.2.2.2.2
    hgood.2.2.2.2.1 hq
  have hcont : ∀ u ∈ Ioc (0 : ℝ) τ, η (r + u) ∈ D := by
    intro u hu
    have hu0 : 0 < u.toNNReal := Real.toNNReal_pos.2 hu.1
    have hue : u.toNNReal < exitNN E c ρ T V x := by
      rw [Real.toNNReal_lt_iff_lt_coe hu.1.le]
      exact hu.2.trans_lt (NNReal.coe_lt_coe.2 hτ)
    have huT : (u.toNNReal : ℝ≥0∞) < T x := (ENNReal.coe_lt_coe.2 hue).trans_le
      (IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le x)
    have hmem := hs.inside x hx.1.1 u.toNNReal hu0 huT
    rw [← SetLike.mem_coe, hdom, hρ u.toNNReal hu0 hue, Real.coe_toNNReal _ hu.1.le] at hmem
    exact hmem
  have hIoc : (fun u : ℝ => s.trace u.toNNReal) '' Ioc 0 (q : ℝ) = s.trace '' Ioc 0 q := by
    apply Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨u.toNNReal, ⟨Real.toNNReal_pos.2 hu.1, Real.toNNReal_le_iff_le_coe.2 hu.2⟩, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨u, ⟨NNReal.coe_pos.2 hu.1, NNReal.coe_le_coe.2 hu.2⟩, by
        dsimp only
        rw [Real.toNNReal_coe]⟩
  have hrτ : r + (τ : ℝ) < r + (exitNN E c ρ T V x : ℝ) :=
    add_lt_add_of_le_of_lt le_rfl (NNReal.coe_lt_coe.2 hτ)
  have hi' : InjOn η (Icc 0 (r + (τ : ℝ))) :=
    hi.mono (show Icc 0 (r + (τ : ℝ)) ⊆ Ico 0 (r + exitNN E c ρ T V x) from
      fun _ hu => ⟨hu.1, hu.2.trans_lt hrτ⟩)
  refine ⟨Tc, ⟨hW, hW0, hη, hr, NNReal.coe_pos.2 hτ0,
    hi',
    fun u hu => hH u ⟨hu.1, hu.2.trans_lt hrτ⟩,
    hs.conf x hx.1.1, hdom, hsub, hsimply, htarget, hinfty, hlift, hcollar, hcurrent,
    hcont, Aux61MeanId.continuous_chartDriver s, Aux61MeanId.chartDriver_zero s,
    htrace, NNReal.coe_pos.2 hq0, hqTc, hcinj, hcmem, ?_, ?_⟩⟩
  · rw [htrace.2.2 _ q.coe_nonneg hqTc, YuanCharacterisation.fillH_image_eq q.coe_nonneg
      (htrace.2.1.mono (fun _ hu => ⟨hu.1, hu.2.trans_lt hqTc⟩)) hcinj
      (by rw [Real.toNNReal_zero, FibCode.trace_zero]; rfl) hcmem, hIoc]
    exact image_accessExitCode_physical hs hV hV0 hland hinj d hdV hℓ hq hρ
  · change s.trace (q : ℝ).toNNReal = (c x).1 (η (r + τ))
    rw [Real.toNNReal_coe, accessExitCode_trace_eq hs hV hV0 hland hinj hq hq0,
      hρ _ hτ0 hτ]

end InteractingSLE.Sec5.Aux61SlitW
