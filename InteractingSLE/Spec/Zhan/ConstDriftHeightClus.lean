/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftHeightMono

/-!
# The height functional along an actual trace

Packet PROVE-ZHAN-A7. For a sublinear path `f` and a strip path with strip driver `drv κ σ f` (`|σ| < 1`) carrying a
generating trace `η` on its strip life:

* `norm_one_add_mem`: the bounded hull (`IsStripPath.norm_one_add_trace_mem_Icc`) with the measurable sublinearity
  constant `csub`: `e^{−(C + R)} ≤ ‖1 + η‖ ≤ e^{C + R}`, `C = csub κ σ (slope σ) f`, `R = hullR σ`;
* `hgt_eq`: the strip height functional of `ConstDriftHeightMeas.lean` is the height `arg(1 + η)` of the trace at the
  chordal time of the strip time;
* `evLife_of_mm_eq_pi`: if the terminal minimal height `mm κ σ f` is `π`, the trace heights tend to `π` along the strip
  life (the conclusion of `ConstDriftHeightStatement`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMapInv fwdMap fwdHull IsForwardSol)
open QuantumZipper.RS (CPath)

namespace InteractingSLE

namespace Zhan

namespace HeightLaw

open Strip Retarget

variable {κ σ : ℝ} {f : CPath} {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-! ### Arguments in the closed upper half-plane -/

theorem continuousWithinAt_arg_Hbar {z : ℂ} (hz0 : z ≠ 0) :
    ContinuousWithinAt arg {z : ℂ | 0 ≤ z.im} z := by
  by_cases h : z ∈ slitPlane
  · exact (continuousAt_arg h).continuousWithinAt
  · rw [mem_slitPlane_iff] at h
    push Not at h
    have hre : z.re < 0 := by
      rcases h.1.lt_or_eq with h1 | h1
      · exact h1
      · exact absurd (Complex.ext (by simpa using h1) (by simpa using h.2)) hz0
    exact continuousWithinAt_arg_of_re_neg_of_im_zero hre h.2

theorem arg_mem_Icc_zero_pi {z : ℂ} (hz : 0 ≤ z.im) : arg z ∈ Icc 0 Real.pi :=
  ⟨Complex.arg_nonneg_iff.2 hz, Complex.arg_le_pi z⟩

/-! ### The bounded hull with the measurable sublinearity constant -/

/-- The slope `a = (|σ| + 1)/2` of the sublinear bound of the strip driver. -/
def slope (σ : ℝ) : ℝ := (|σ| + 1) / 2

/-- `b = (a + 1)/2`. -/
def bsl (σ : ℝ) : ℝ := (slope σ + 1) / 2

/-- The horizontal radius `R` with `tanh(R/2) ≥ b`. -/
def hullR (σ : ℝ) : ℝ := Real.log ((1 + bsl σ) / (1 - bsl σ))

theorem slope_lt_one (hσ : |σ| < 1) : slope σ < 1 := by unfold slope; linarith

theorem abs_lt_slope (hσ : |σ| < 1) : |σ| < slope σ := by unfold slope; linarith

theorem bsl_bounds (hσ : |σ| < 1) : 0 < bsl σ ∧ bsl σ < 1 ∧ slope σ ≤ bsl σ := by
  unfold bsl slope
  refine ⟨?_, ?_, ?_⟩ <;> linarith [abs_nonneg σ]

theorem hullR_spec (hσ : |σ| < 1) :
    0 < hullR σ ∧ bsl σ ≤ (Real.exp (hullR σ) - 1) / (Real.exp (hullR σ) + 1) :=
  le_tanh_half_log (bsl σ) (bsl_bounds hσ).1 (bsl_bounds hσ).2.1

/-- A sublinear path has a finite sublinearity constant at the slope `a = (|σ| + 1)/2`. -/
theorem bddAbove_of_sublinear (hσ : |σ| < 1) {f : CPath}
    (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0)) :
    BddAbove (range fun q : {q : ℚ // 0 ≤ q} => |drv κ σ f ((q : ℚ) : ℝ)| - slope σ * (q : ℚ)) := by
  obtain ⟨C, hC⟩ := sublinear_of_tendsto f.2 hf (Real.sqrt κ) (slope σ - |σ|)
    (by linarith [abs_lt_slope hσ])
  refine ⟨C + |Real.sqrt κ * f.1 0|, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hq : (0 : ℝ) ≤ (q : ℚ) := by exact_mod_cast q.2
  have h1 := hC _ hq
  simp only [drv]
  have h2 : |Real.sqrt κ * (f.1 ((q : ℚ) : ℝ).toNNReal - f.1 0) + σ * (q : ℚ)| ≤
      |Real.sqrt κ * f.1 ((q : ℚ) : ℝ).toNNReal| + |Real.sqrt κ * f.1 0| + |σ| * (q : ℚ) := by
    have e : Real.sqrt κ * (f.1 ((q : ℚ) : ℝ).toNNReal - f.1 0) + σ * (q : ℚ) =
        Real.sqrt κ * f.1 ((q : ℚ) : ℝ).toNNReal + (-(Real.sqrt κ * f.1 0)) + σ * (q : ℚ) := by ring
    rw [e]
    calc _ ≤ |Real.sqrt κ * f.1 ((q : ℚ) : ℝ).toNNReal + (-(Real.sqrt κ * f.1 0))| + |σ * (q : ℚ)| :=
          abs_add_le _ _
      _ ≤ |Real.sqrt κ * f.1 ((q : ℚ) : ℝ).toNNReal| + |-(Real.sqrt κ * f.1 0)| + |σ * (q : ℚ)| := by
          gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_neg, abs_mul σ, abs_of_nonneg hq]
  nlinarith

/-- **The bounded hull**: `e^{−(C + R)} ≤ ‖1 + η_s‖ ≤ e^{C + R}` on the strip life, `C = csub κ σ (slope σ) f`. -/
theorem norm_one_add_mem (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    ‖1 + η s‖ ∈ Icc (Real.exp (-(csub κ σ (slope σ) f + hullR σ))) (Real.exp (csub κ σ (slope σ) f + hullR σ)) :=
  h.1.norm_one_add_trace_mem_Icc (hullR_spec hσ).1 (hullR_spec hσ).2 (bsl_bounds hσ).2.2
    (fun t => by rw [h.2 t]; exact abs_drv_le_csub (bddAbove_of_sublinear hσ hf) t.coe_nonneg) hη hs

theorem one_add_ne_zero (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    1 + η s ≠ 0 := fun h0 => by
  have hb := (norm_one_add_mem hσ hf h hη hs).1
  rw [h0, norm_zero] at hb
  exact (Real.exp_pos _).not_ge hb

theorem trace_mem_Hbar (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    η s ∈ Hbar :=
  Sec7.IsGeneratingTrace.mem_Hbar (hη s hs) (h.1.continuousOn_lt hs) h.1.1 le_rfl

theorem one_add_im_nonneg (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    0 ≤ (1 + η s).im := by
  have := trace_mem_Hbar h hη hs
  show 0 ≤ (1 + η s).im
  simp only [add_im, one_im, zero_add]
  exact this

/-! ### The height functional is the trace height -/

/-- **The strip height functional is the height of the trace**: `hgt κ σ f t = arg(1 + η(s(t)))`. -/
theorem hgt_eq (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {t : ℝ} (ht : 0 ≤ t) :
    hgt κ σ f t = arg (1 + η (chordT w v t.toNNReal)) := by
  have hl := (h.1.chordT_spec t.toNNReal).1
  have hne := one_add_ne_zero hσ hf h hη hl
  refine limInfQ_eq_of_tendsto (fun y _ => arg_mem_Icc _) ?_
  have h1 : Tendsto (fun y => 1 + rad κ σ f t y) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] (1 + η (chordT w v t.toNNReal))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.add (tendsto_rad h hη ht),
      eventually_mem_nhdsWithin.mono fun y hy => ?_⟩
    have := rad_mem_H (κ := κ) (σ := σ) f ht hy
    show 0 ≤ (1 + rad κ σ f t y).im
    simp only [add_im, one_im, zero_add]
    exact this.le
  exact (continuousWithinAt_arg_Hbar hne).tendsto.comp h1

theorem hgt_mem_Icc_zero_pi (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {t : ℝ} (ht : 0 ≤ t) :
    hgt κ σ f t ∈ Icc 0 Real.pi := by
  rw [hgt_eq hσ hf h hη ht]
  exact arg_mem_Icc_zero_pi (one_add_im_nonneg h hη (h.1.chordT_spec t.toNNReal).1)

/-- **Heights tend to `π` if the terminal minimal height is `π`.** -/
theorem evLife_of_mm_eq_pi (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) (hm : mm κ σ f = Real.pi) :
    ∀ ε > 0, EvLife w v ζ fun s => Real.pi - ε < arg (1 + η s) := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_lt_of_lt_limInfTopQ (c := Real.pi - ε / 2) (fun t _ => hgt_mem f t)
    (by rw [show limInfTopQ (hgt κ σ f) = mm κ σ f from rfl, hm]; linarith)
  have hlN := (h.1.chordT_spec (N : ℝ≥0)).1
  refine ⟨chordT w v N, hlN, fun s hs hsl => ?_⟩
  by_contra hle
  push Not at hle
  -- continuity of the height at `s` from the right
  obtain ⟨s', hss', hs'⟩ := h.1.exists_gt hsl
  have hne := one_add_ne_zero hσ hf h hη hsl
  have hηc : ContinuousWithinAt η {r : ℝ≥0 | (r : ℝ≥0∞) ≤ s'} s :=
    (hη s' hs').2.1 s (ENNReal.coe_le_coe.2 hss'.le)
  have hHb : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ s' → 0 ≤ (1 + η r).im := fun r hr =>
    one_add_im_nonneg h hη (hs'.mono (ENNReal.coe_le_coe.1 hr))
  have hcont : ContinuousWithinAt (fun r => arg (1 + η r)) {r : ℝ≥0 | (r : ℝ≥0∞) ≤ s'} s := by
    have h1 : ContinuousWithinAt (fun r => 1 + η r) {r : ℝ≥0 | (r : ℝ≥0∞) ≤ s'} s :=
      continuousWithinAt_const.add hηc
    exact (continuousWithinAt_arg_Hbar hne).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h1.tendsto, eventually_nhdsWithin_of_forall fun r hr => hHb r hr⟩)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 hcont (ε / 2) (by linarith)
  -- the strip time of `s` and a rational strip time `q ≥ N` just after it
  set t := stripClock (extPath w) (extPath v) s with htdef
  have hmS := h.1.2.1 s hsl
  have ht0 : 0 ≤ t := hmS.stripClock_nonneg ⟨s.coe_nonneg, le_rfl⟩
  have htN : (N : ℝ) ≤ t := by
    have h1 := h.1.stripClock_le hsl hs
    rw [(h.1.chordT_spec (N : ℝ≥0)).2.2] at h1
    exact_mod_cast h1
  have hst : ss κ σ f t = s := by
    rw [← chordalTime_eq_ss h ht0, htdef, hmS.chordalTime_stripClock ⟨s.coe_nonneg, le_rfl⟩]
  have hssc : Continuous (ss κ σ f) := by
    unfold ss Retarget.clk
    exact continuous_iff_continuousAt.2 fun x =>
      (((continuous_rate f).integral_hasStrictDerivAt 0 x).hasDerivAt).continuousAt
  have hs's : (0 : ℝ) < (s' : ℝ) - s := sub_pos.2 (NNReal.coe_lt_coe.2 hss')
  obtain ⟨η'', hη'', hssball⟩ := Metric.continuousAt_iff.1 hssc.continuousAt (min δ ((s' : ℝ) - s))
    (lt_min hδ hs's)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + η'' by linarith)
  have hq0 : (0 : ℝ) ≤ q := ht0.trans hq1.le
  have hqN : (N : ℚ) ≤ q := by exact_mod_cast htN.trans hq1.le
  have hdq := hssball (show dist (q : ℝ) t < η'' by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [hst, Real.dist_eq, abs_lt] at hdq
  set r := chordT w v (q : ℝ).toNNReal with hr
  have hrq : (r : ℝ) = ss κ σ f q := by rw [hr, coe_chordT_eq h, Real.coe_toNNReal _ hq0]
  have hrs' : (r : ℝ≥0∞) ≤ s' := by
    refine ENNReal.coe_le_coe.2 (NNReal.coe_le_coe.1 ?_)
    rw [hrq]
    linarith [hdq.2, min_le_right δ ((s' : ℝ) - s)]
  have hrd : dist r s < δ := by
    rw [NNReal.dist_eq, hrq, abs_lt]
    constructor <;> linarith [hdq.1, hdq.2, min_le_left δ ((s' : ℝ) - s)]
  have h1 := hball hrs' hrd
  have h2 := hN q hqN
  rw [hgt_eq hσ hf h hη hq0, ← hr] at h2
  rw [Real.dist_eq, abs_lt] at h1
  linarith [h1.2]

end HeightLaw

end Zhan

end InteractingSLE
