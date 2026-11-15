/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstAccessLocal
import InteractingSLE.Spec.Sec5.Aux61Conf2KB

/-!
# The physical time and slit of the selected-access restart code

Packet PROVE-AUX61-SLITW. Before the lifetime, the code is the original physical
continuation read in the inverse capacity clock. This identifies its tip and
the whole positive-time slit, including the right endpoint of each prefix.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW

open Aux61FibData Aux61GInst Restart Aux61Fib

section Access

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E c ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}

/-- Original elapsed time corresponding to a capacity time of the restart code. -/
def accessTime (x : X) (q : ℝ≥0) : ℝ≥0 :=
  invClock (capClock (exitEv E c ρ T V) (accessExitPath E c ρ T V) (exitNN E c ρ T V) x)
    (exitNN E c ρ T V x) q

include hs hV hV0 hland hinj

/-- The inverse clock is strictly inside the original window-exit interval. -/
theorem accessTime_spec {x : X} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life) :
    accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q < exitNN E c ρ T V x ∧
      capClock (exitEv E c ρ T V) (accessExitPath E c ρ T V) (exitNN E c ρ T V) x
        (accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q) = q := by
  have hx := mem_exitEv_of_lt_accessLife hq
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hc := isClockOn_accessExitPath hs hV hV0 hland hinj
  have hq' : (q : ℝ≥0∞) < capEnd (exitEv E c ρ T V) (accessExitPath E c ρ T V)
      (exitNN E c ρ T V) x := hq
  have hcl := hp.isClockOn_capClock hc hx
  obtain ⟨hle, he⟩ := hcl.invClock_spec ((IsPathSpec.capEnd_eq_capLife hx) ▸ hq'.le)
  refine ⟨lt_of_le_of_ne (ENNReal.coe_le_coe.1 hle) ?_, he⟩
  intro heq
  change accessTime x q = exitNN E c ρ T V x at heq
  change capClock _ _ _ x (accessTime x q) = q at he
  rw [heq] at he
  have hlife : (accessExitCode E c ρ T V a k h x).life = ENNReal.ofReal
      (capClock (exitEv E c ρ T V) (accessExitPath E c ρ T V) (exitNN E c ρ T V) x
        (exitNN E c ρ T V x)) := by
    simp only [accessExitCode_life, capEnd, hx, ↓reduceIte]
  rw [hlife, he, ENNReal.ofReal_coe_nnreal] at hq
  exact lt_irrefl _ hq

/-- Positive capacity times have positive physical duration. -/
theorem accessTime_pos {x : X} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life) (hq0 : 0 < q) :
    0 < accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q := by
  have hx := mem_exitEv_of_lt_accessLife hq
  have hcl := (isPathSpec_accessExitPath hs hV hV0 hland).isClockOn_capClock
    (isClockOn_accessExitPath hs hV hV0 hland hinj) hx
  have he := (accessTime_spec hs hV hV0 hland hinj hq).2
  apply pos_iff_ne_zero.2
  intro hz
  rw [hz, hcl.zero] at he
  exact hq0.ne' (by exact_mod_cast he.symm)

/-- Before the lifetime, the code reads the actual physical continuation. -/
theorem accessExitCode_trace_eq {x : X} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life) (hq0 : 0 < q) :
    (accessExitCode E c ρ T V a k h x).trace q =
      (c x).1 (ρ x (accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q)) := by
  have hx := mem_exitEv_of_lt_accessLife hq
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hc := isClockOn_accessExitPath hs hV hV0 hland hinj
  have hspec := hp.capPath_spec hc hx hq.le
  rw [accessExitCode_trace hs hV hV0 hland hinj x hq.le, hspec.2.2]
  have hlt := (accessTime_spec hs hV hV0 hland hinj hq).1
  have hpos := accessTime_pos hs hV hV0 hland hinj hq hq0
  change accessExitPath E c ρ T V x (accessTime x q) = _
  rw [accessExitPath, ite_eq_left hx, ite_eq_left hlt]
  exact hs.inPath_eq_fwd hx.1.1 hpos ((ENNReal.coe_lt_coe.2 hlt).trans_le
    (IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le x))

/-- The entire initial interval is read in the same inverse clock as its endpoint. -/
theorem image_accessExitCode_Icc {x : X} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life) :
    (accessExitCode E c ρ T V a k h x).trace '' Icc 0 q =
      accessExitPath E c ρ T V x '' Icc 0
        (accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q) := by
  have hx := mem_exitEv_of_lt_accessLife hq
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hc := isClockOn_accessExitPath hs hV hV0 hland hinj
  dsimp only [accessTime]
  rw [← hp.image_capPath_Icc hc hx hq.le]
  exact image_congr fun u hu => accessExitCode_trace hs hV hV0 hland hinj x
    ((ENNReal.coe_le_coe.2 hu.2).trans hq.le)

/-- The positive-time slit, with its terminal point included, is preserved by the code. -/
theorem image_accessExitCode_Ioc (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V)
    {x : X} {q : ℝ≥0} (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life) :
    (accessExitCode E c ρ T V a k h x).trace '' Ioc 0 q =
      accessExitPath E c ρ T V x '' Ioc 0
        (accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q) := by
  have hx := mem_exitEv_of_lt_accessLife hq
  have hg := pathGood_accessExitCode (a := a) (k := k) (h := h) hs hV hV0 hland hinj d hdV hℓ hx
  have hi := hg.2.2.2.2.2.mono (show Icc 0 q ⊆
      {u : ℝ≥0 | (u : ℝ≥0∞) ≤ (accessExitCode E c ρ T V a k h x).life} from
      fun _ hu => (ENNReal.coe_le_coe.2 hu.2).trans hq.le)
  have hp := accessExitPath_facts hs hV hV0 hland hinj hx
  have hj := hp.2.2.1.mono (show Icc 0 (accessTime x q) ⊆ Iic (exitNN E c ρ T V x) from
    fun _ hu => hu.2.trans (accessTime_spec hs hV hV0 hland hinj hq).1.le)
  rw [← Icc_sdiff_left, hi.image_sdiff_subset (singleton_subset_iff.2 ⟨le_rfl, zero_le⟩),
    ← Icc_sdiff_left, hj.image_sdiff_subset (singleton_subset_iff.2 ⟨le_rfl, zero_le⟩),
    image_singleton, image_singleton, FibCode.trace_zero, hp.2.1,
    image_accessExitCode_Icc hs hV hV0 hland hinj hq]

/-- In the original physical parametrization the code traces exactly the new continuation. -/
theorem image_accessExitCode_physical (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V)
    {x : X} {q : ℝ≥0} (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life)
    {η : ℝ → ℂ} {r : ℝ}
    (hρ : ∀ u : ℝ≥0, 0 < u → u < exitNN E c ρ T V x → ρ x u = η (r + u)) :
    (accessExitCode E c ρ T V a k h x).trace '' Ioc 0 q =
      (c x).1 '' ((fun u : ℝ => η (r + u)) '' Ioc 0
        (accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q : ℝ)) := by
  rw [image_accessExitCode_Ioc hs hV hV0 hland hinj d hdV hℓ hq, image_image]
  have hx := mem_exitEv_of_lt_accessLife hq
  let τ := accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q
  have hτ : τ < exitNN E c ρ T V x := (accessTime_spec hs hV hV0 hland hinj hq).1
  have he : ∀ u ∈ Ioc 0 τ, accessExitPath E c ρ T V x u = (c x).1 (η (r + u)) := by
    intro u hu
    have hue := hu.2.trans_lt hτ
    rw [accessExitPath, ite_eq_left hx, ite_eq_left hue,
      hs.inPath_eq_fwd hx.1.1 hu.1 ((ENNReal.coe_lt_coe.2 hue).trans_le
        (IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le x)), hρ u hu.1 hue]
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨NNReal.coe_pos.2 hu.1, NNReal.coe_le_coe.2 hu.2⟩, (he u hu).symm⟩
  · rintro _ ⟨u, hu, rfl⟩
    have hu' : u.toNNReal ∈ Ioc 0 τ :=
      ⟨Real.toNNReal_pos.2 hu.1, Real.toNNReal_le_iff_le_coe.2 hu.2⟩
    refine ⟨u.toNNReal, hu', ?_⟩
    rw [he _ hu', Real.coe_toNNReal _ hu.1.le]

end Access

end InteractingSLE.Sec5.Aux61SlitW
