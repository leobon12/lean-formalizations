import InteractingSLE.Spec.Sec2.MartingaleDefect
import InteractingSLE.Stochastic.LocalTime.Stopped
import InteractingSLE.Stochastic.LocalTime.Bridge
import InteractingSLE.Frozen.Spec.ForceWord_ThresholdCondition
import MathFin.Probability.Brownian.ExitTime

/-!
# Theorem 2.4, converse implication: the singular force-point motions vanish (local step)

Packet PROVE-SEC2-MART2 (step R1 of `planning/handoffs/PROVE-SEC2-MART.md`). Specification, proof of
Theorem 2.4 (`source/spec/p001-048.md`, anchor `thm-2.4-proof`, L900–L925, "The singular motions
vanish"; graph node `SPEC.thm-2.4#no-singular-motion`).

Let the driver satisfy `W = a β − ½ ∑ⱼ ρⱼ (Vʲ − xʲ)` with `β` an `𝓕`-Brownian motion (this is
`MartChar.driver_eq_sqrt_mul_sub` with `a = √κ`), and let the force points be force paths
(`IsForcePath`) with the deterministic properties of geometric images. Fix a left group: a finite
set `S` of left indices and a time `s`. On the event that the merge group of the nearest left point
`V^{i₀}` at time `s` is exactly `S`, stop at the first time `≥ s` at which another left point merges
with it or a right point meets the driver. Up to that stopping time,

  `X = W − V^{i₀} = X_s + a (β − β_s) + ∫ b + (1 + ½ ρ_S) · (J − J_s)`,  `J = −I^{i₀}`,

with `J` non-decreasing and carried by `{X = 0}`, so PROVE-TANAKA's `ae_singular_const_stopped`
shows that `I^{i₀}` is constant there whenever `ρ_S ≠ −2`
(`ae_forceDefect_const_of_group`).

## Main results

* `zeroHit g s`: the first time `≥ s` at which a continuous adapted process vanishes, a stopping
  time (`isStoppingTime_zeroHit`), built from MathFin's `exitTime`;
* `measurable_intervalIntegral_comp`: time integrals of measurable functions of continuous
  adapted processes are adapted;
* `continuous_forceDefect`, `forceDefect_eq_of_forall_ne_Ico`, `stronglyAdapted_forceDefect`;
* `isTanakaPathOn_group`: the pathwise decomposition on a group interval;
* `ae_forceDefect_const_of_group`: the local Tanaka step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

/-! ### First zeros of continuous adapted processes after a deterministic time -/

section ZeroHit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The auxiliary process whose absolute value reaches `1` exactly at the zeros of `g` after `s`. -/
def zeroHitProc (g : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun u ω => 1 - min (|g u ω| + max ((s : ℝ) - u) 0) 1

/-- The first time `≥ s` at which `g` vanishes (`⊤` if there is none). -/
def zeroHit (g : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : Ω → WithTop ℝ≥0 :=
  MathFin.exitTime (zeroHitProc g s) 1

lemma one_le_abs_zeroHitProc_iff (g : ℝ≥0 → Ω → ℝ) (s u : ℝ≥0) (ω : Ω) :
    1 ≤ |zeroHitProc g s u ω| ↔ s ≤ u ∧ g u ω = 0 := by
  simp only [zeroHitProc]
  have h1 : 0 ≤ |g u ω| + max ((s : ℝ) - u) 0 :=
    add_nonneg (abs_nonneg _) (le_max_right _ _)
  have h2 : 0 ≤ 1 - min (|g u ω| + max ((s : ℝ) - u) 0) 1 := by
    have := min_le_right (|g u ω| + max ((s : ℝ) - u) 0) 1
    linarith
  rw [abs_of_nonneg h2]
  constructor
  · intro h
    have hmin : min (|g u ω| + max ((s : ℝ) - u) 0) 1 ≤ 0 := by linarith
    have hle : |g u ω| + max ((s : ℝ) - u) 0 ≤ 0 := by
      rcases min_le_iff.1 hmin with h' | h'
      · exact h'
      · linarith
    have hg : |g u ω| = 0 := le_antisymm (by linarith [le_max_right ((s : ℝ) - u) 0]) (abs_nonneg _)
    have hm : max ((s : ℝ) - u) 0 = 0 := le_antisymm (by linarith [abs_nonneg (g u ω)])
      (le_max_right _ _)
    refine ⟨?_, abs_eq_zero.1 hg⟩
    have : (s : ℝ) - u ≤ 0 := by rw [← hm]; exact le_max_left _ _
    exact_mod_cast (show (s : ℝ) ≤ u by linarith)
  · rintro ⟨hsu, hg⟩
    have hsu' : (s : ℝ) - u ≤ 0 := by
      have : (s : ℝ) ≤ u := hsu
      linarith
    rw [hg, abs_zero, max_eq_right hsu', add_zero, min_eq_left zero_le_one]
    norm_num

lemma continuous_zeroHitProc {g : ℝ≥0 → Ω → ℝ} (hg : ∀ ω, Continuous fun u => g u ω) (s : ℝ≥0)
    (ω : Ω) : Continuous fun u => zeroHitProc g s u ω := by
  simp only [zeroHitProc]
  have : Continuous fun u : ℝ≥0 => (u : ℝ) := NNReal.continuous_coe
  fun_prop

lemma zeroHit_le_iff {g : ℝ≥0 → Ω → ℝ} (hg : ∀ ω, Continuous fun u => g u ω) (s i : ℝ≥0)
    (ω : Ω) : zeroHit g s ω ≤ (i : WithTop ℝ≥0) ↔ ∃ r, s ≤ r ∧ r ≤ i ∧ g r ω = 0 := by
  rw [zeroHit, MathFin.exitTime_le_iff (fun ω => continuous_zeroHitProc hg s ω)]
  simp only [Nat.cast_one, one_le_abs_zeroHitProc_iff, mem_Icc]
  constructor
  · rintro ⟨r, ⟨-, hri⟩, hsr, hr⟩
    exact ⟨r, hsr, hri, hr⟩
  · rintro ⟨r, hsr, hri, hr⟩
    exact ⟨r, ⟨bot_le, hri⟩, hsr, hr⟩

lemma le_zeroHit {g : ℝ≥0 → Ω → ℝ} (hg : ∀ ω, Continuous fun u => g u ω) (s : ℝ≥0) (ω : Ω) :
    (s : WithTop ℝ≥0) ≤ zeroHit g s ω := by
  by_contra h
  push Not at h
  obtain ⟨v, hv, hvs⟩ := WithTop.lt_iff_exists_coe.1 h
  have hle : zeroHit g s ω ≤ (v : WithTop ℝ≥0) := hv.le
  obtain ⟨r, hsr, hrv, -⟩ := (zeroHit_le_iff hg s v ω).1 hle
  have : v < s := WithTop.coe_lt_coe.1 hvs
  exact absurd (hsr.trans hrv) (not_le.2 this)

lemma ne_zero_of_lt_zeroHit {g : ℝ≥0 → Ω → ℝ} (hg : ∀ ω, Continuous fun u => g u ω) {s u : ℝ≥0}
    {ω : Ω} (hsu : s ≤ u) (hu : (u : WithTop ℝ≥0) < zeroHit g s ω) : g u ω ≠ 0 := fun h0 =>
  absurd ((zeroHit_le_iff hg s u ω).2 ⟨u, hsu, le_rfl, h0⟩) (not_le.2 hu)

lemma lt_zeroHit_of_forall_ne {g : ℝ≥0 → Ω → ℝ} (hg : ∀ ω, Continuous fun u => g u ω)
    {s u : ℝ≥0} {ω : Ω} (h : ∀ r, s ≤ r → r ≤ u → g r ω ≠ 0) :
    (u : WithTop ℝ≥0) < zeroHit g s ω := by
  by_contra hle
  push Not at hle
  obtain ⟨r, hsr, hru, hr⟩ := (zeroHit_le_iff hg s u ω).1 hle
  exact h r hsr hru hr

lemma isStoppingTime_zeroHit {𝓕 : Filtration ℝ≥0 mΩ} {g : ℝ≥0 → Ω → ℝ}
    (hg : ∀ ω, Continuous fun u => g u ω) (hga : ∀ u, Measurable[𝓕 u] (g u)) (s : ℝ≥0) :
    IsStoppingTime 𝓕 (zeroHit g s) := by
  refine MathFin.isStoppingTime_exitTime_of_measurable (fun u => ?_)
    (fun ω => continuous_zeroHitProc hg s ω) 1
  have hF : Continuous fun x : ℝ => 1 - min (|x| + max ((s : ℝ) - u) 0) 1 := by fun_prop
  exact hF.measurable.comp (hga u)

end ZeroHit

/-! ### Time integrals of continuous adapted processes are adapted -/

section Integral

/-- `ω ↦ ∫ₐᵇ g(Y_r(ω)) dr` is measurable when `Y` has continuous paths and measurable values. -/
lemma measurable_intervalIntegral_comp {Ω : Type*} {m : MeasurableSpace Ω} {Y : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun r => Y r ω) (hm : ∀ r, Measurable (Y r)) {g : ℝ → ℝ}
    (hg : Measurable g) {a b : ℝ} (hab : a ≤ b) :
    Measurable fun ω => ∫ r in a..b, g (Y r ω) := by
  have hY : Measurable (Function.uncurry Y) := measurable_uncurry_of_continuous_of_measurable hc hm
  have hF : StronglyMeasurable (Function.uncurry fun ω r => g (Y r ω)) := by
    have : (Function.uncurry fun ω r => g (Y r ω)) = (g ∘ Function.uncurry Y) ∘ Prod.swap := by
      funext p; rfl
    rw [this]
    exact ((hg.comp hY).comp measurable_swap).stronglyMeasurable
  have := hF.integral_prod_right (ν := volume.restrict (Ioc a b))
  simp_rw [intervalIntegral.integral_of_le hab]
  exact this.measurable

end Integral

/-! ### The force defect: increments, continuity, constancy, adaptedness -/

section Defect

variable {w v : ℝ≥0 → ℝ}

/-- The increment of the defect. -/
lemma IsForcePath.forceDefect_sub_eq (hv : IsForcePath w v) {a b : ℝ≥0} (hab : a ≤ b) :
    forceDefect w v b - forceDefect w v a
      = v b - v a - ∫ s in (a : ℝ)..b, 2 / (v s.toNNReal - w s.toNNReal) := by
  have h1 := hv.intervalIntegrable_gap le_rfl (NNReal.coe_nonneg a)
  have h2 := hv.intervalIntegrable_gap (NNReal.coe_nonneg a) (NNReal.coe_le_coe.2 hab)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  simp only [forceDefect]
  rw [← hsplit]
  ring

/-- The reciprocal gap (extended constantly to negative times) is interval-integrable on every
interval of `ℝ`. -/
lemma IsForcePath.intervalIntegrable_gap_all (hv : IsForcePath w v) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume a b := by
  have h0 : ∀ x : ℝ, IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal))
      volume 0 x := by
    intro x
    rcases le_total 0 x with hx | hx
    · exact hv.intervalIntegrable_gap le_rfl hx
    · refine IntervalIntegrable.symm ?_
      refine (intervalIntegrable_const (c := 2 / (v 0 - w 0))).congr ?_
      intro r hr
      rw [uIoc_of_le hx] at hr
      simp only [Real.toNNReal_of_nonpos hr.2]
  exact (h0 a).symm.trans (h0 b)

/-- The primitive of the reciprocal gap is continuous. -/
lemma IsForcePath.continuous_integral_gap (hv : IsForcePath w v) :
    Continuous fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal) :=
  (intervalIntegral.continuous_primitive (fun a b => hv.intervalIntegrable_gap_all a b) 0).comp
    NNReal.continuous_coe

/-- The defect is continuous. -/
lemma IsForcePath.continuous_forceDefect (hv : IsForcePath w v) : Continuous (forceDefect w v) :=
  ((hv.1.sub continuous_const).sub hv.continuous_integral_gap)

/-- **The defect is constant on `[a, b]` if there is no collision on `[a, b)`.** -/
lemma IsForcePath.forceDefect_eq_of_forall_ne_Ico (hv : IsForcePath w v) {a b : ℝ≥0}
    (hab : a ≤ b) (hne : ∀ u, a ≤ u → u < b → v u ≠ w u) :
    forceDefect w v b = forceDefect w v a := by
  rcases hab.eq_or_lt with rfl | hlt
  · rfl
  have hEq : EqOn (forceDefect w v) (fun _ => forceDefect w v a) (Ico a b) := fun u hu =>
    hv.forceDefect_eq_of_forall_ne hu.1 fun r hr => hne r hr.1 (hr.2.trans_lt hu.2)
  have h := hEq.of_subset_closure hv.continuous_forceDefect.continuousOn continuousOn_const
    Ico_subset_Icc_self (by rw [closure_Ico hlt.ne])
  exact h ⟨hab, le_rfl⟩

/-- Two force paths that coincide on `[a, b]` have the same defect increment there. -/
lemma IsForcePath.forceDefect_sub_eq_of_eqOn {v' : ℝ≥0 → ℝ} (hv : IsForcePath w v)
    (hv' : IsForcePath w v') {a b : ℝ≥0} (hab : a ≤ b) (heq : ∀ u, a ≤ u → u ≤ b → v' u = v u) :
    forceDefect w v' b - forceDefect w v' a = forceDefect w v b - forceDefect w v a := by
  rw [hv.forceDefect_sub_eq hab, hv'.forceDefect_sub_eq hab, heq a le_rfl hab, heq b hab le_rfl]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le (NNReal.coe_le_coe.2 hab)] at hr
  have h0 : (0 : ℝ) ≤ r := (NNReal.coe_nonneg a).trans hr.1
  have h1 : a ≤ r.toNNReal := (Real.le_toNNReal_iff_coe_le h0).2 hr.1
  have h2 : r.toNNReal ≤ b := Real.toNNReal_le_iff_le_coe.2 hr.2
  simp only [heq _ h1 h2]

end Defect

/-! ### Adaptedness of the defect -/

section DefectAdapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The defect process of continuous adapted coordinates is adapted. -/
lemma measurable_forceDefect {W V : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ ω, Continuous fun t => V t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVa : StronglyAdapted 𝓕 V) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => forceDefect (W · ω) (V · ω) t := by
  set Y : ℝ → Ω → ℝ := fun r ω => V (min r.toNNReal t) ω - W (min r.toNNReal t) ω with hY
  have hYc : ∀ ω, Continuous fun r => Y r ω := fun ω => by
    have hm : Continuous fun r : ℝ => min r.toNNReal t :=
      continuous_real_toNNReal.min continuous_const
    exact ((hVc ω).comp hm).sub ((hWc ω).comp hm)
  have hYm : ∀ r, Measurable[𝓕 t] (Y r) := fun r =>
    ((hVa _).measurable.mono (𝓕.mono (min_le_right _ _)) le_rfl).sub
      ((hWa _).measurable.mono (𝓕.mono (min_le_right _ _)) le_rfl)
  have hint := @measurable_intervalIntegral_comp Ω (𝓕 t) Y hYc hYm (fun x => 2 / x)
    (measurable_const.div measurable_id) 0 t (NNReal.coe_nonneg t)
  have heq : (fun ω => ∫ r in (0 : ℝ)..t, (fun x : ℝ => 2 / x) (Y r ω))
      = fun ω => ∫ r in (0 : ℝ)..t, 2 / (V r.toNNReal ω - W r.toNNReal ω) := by
    funext ω
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hr
    have : min r.toNNReal t = r.toNNReal := min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)
    simp only [hY, this]
  rw [heq] at hint
  simp only [forceDefect]
  exact (((hVa t).measurable).sub ((hVa 0).measurable.mono (𝓕.mono (bot_le : (0 : ℝ≥0) ≤ t)) le_rfl)).sub hint

end DefectAdapted

/-! ### The pathwise decomposition on a group interval -/

section Pathwise

variable {nL nR : ℕ}

/-- The drift `b` of `X = W − V^{i₀}`: `−∑ⱼ ρⱼ/(Vʲ − W) − 2/(V^{i₀} − W)`. -/
def groupDrift (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL) (u : ℝ≥0) : ℝ :=
  -((∑ i, ρL i / (vL i u - w u)) + ∑ j, ρR j / (vR j u - w u)) - 2 / (vL i₀ u - w u)

/-- The dominating process `ψ = ∑ᵢ |ρᵢ|/2 · (∓Vⁱ) − V^{i₀}` of the Tanaka argument. -/
def groupDom (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL) (u : ℝ≥0) : ℝ :=
  (∑ i, |ρL i| / 2 * (-vL i u)) + (∑ j, |ρR j| / 2 * vR j u) - vL i₀ u

lemma intervalIntegrable_fun_sum {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun r => ∑ i, f i r) volume a b := by
  exact ⟨integrable_finsetSum _ fun i _ => (h i).1, integrable_finsetSum _ fun i _ => (h i).2⟩

variable {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
  {vR : Fin nR → ℝ≥0 → ℝ}

lemma groupDrift_eq (i₀ : Fin nL) (u : ℝ≥0) :
    groupDrift ρL ρR w vL vR i₀ u
      = -((∑ i, ρL i / 2 * (2 / (vL i u - w u))) + ∑ j, ρR j / 2 * (2 / (vR j u - w u)))
        - 2 / (vL i₀ u - w u) := by
  have h1 : ∀ i, ρL i / (vL i u - w u) = ρL i / 2 * (2 / (vL i u - w u)) := fun i => by ring
  have h2 : ∀ j, ρR j / (vR j u - w u) = ρR j / 2 * (2 / (vR j u - w u)) := fun j => by ring
  simp only [groupDrift, h1, h2]

lemma intervalIntegrable_groupDrift (hpL : ∀ i, IsForcePath w (vL i))
    (hpR : ∀ j, IsForcePath w (vR j)) (i₀ : Fin nL) {s u : ℝ≥0} (hsu : s ≤ u) :
    IntervalIntegrable (fun r : ℝ => groupDrift ρL ρR w vL vR i₀ r.toNNReal) volume s u := by
  have hsu' : (s : ℝ) ≤ u := hsu
  have hIL := fun i => (hpL i).intervalIntegrable_gap (NNReal.coe_nonneg s) hsu'
  have hIR := fun j => (hpR j).intervalIntegrable_gap (NNReal.coe_nonneg s) hsu'
  simp only [groupDrift_eq]
  exact ((intervalIntegrable_fun_sum fun i => (hIL i).const_mul (ρL i / 2)).add
    (intervalIntegrable_fun_sum fun j => (hIR j).const_mul (ρR j / 2))).neg.sub (hIL i₀)

lemma integral_groupDrift (hpL : ∀ i, IsForcePath w (vL i)) (hpR : ∀ j, IsForcePath w (vR j))
    (i₀ : Fin nL) {s u : ℝ≥0} (hsu : s ≤ u) :
    ∫ r in (s : ℝ)..u, groupDrift ρL ρR w vL vR i₀ r.toNNReal
      = -((∑ i, ρL i / 2 * ∫ r in (s : ℝ)..u, 2 / (vL i r.toNNReal - w r.toNNReal))
          + ∑ j, ρR j / 2 * ∫ r in (s : ℝ)..u, 2 / (vR j r.toNNReal - w r.toNNReal))
        - ∫ r in (s : ℝ)..u, 2 / (vL i₀ r.toNNReal - w r.toNNReal) := by
  have hsu' : (s : ℝ) ≤ u := hsu
  have hIL := fun i => (hpL i).intervalIntegrable_gap (NNReal.coe_nonneg s) hsu'
  have hIR := fun j => (hpR j).intervalIntegrable_gap (NNReal.coe_nonneg s) hsu'
  have hSL := intervalIntegrable_fun_sum fun i => (hIL i).const_mul (ρL i / 2)
  have hSR := intervalIntegrable_fun_sum fun j => (hIR j).const_mul (ρR j / 2)
  have hA : IntervalIntegrable (fun r : ℝ => (∑ i, ρL i / 2 * (2 / (vL i r.toNNReal - w r.toNNReal)))
      + ∑ j, ρR j / 2 * (2 / (vR j r.toNNReal - w r.toNNReal))) volume s u := hSL.add hSR
  have hN : IntervalIntegrable (fun r : ℝ => -((∑ i, ρL i / 2 * (2 / (vL i r.toNNReal - w r.toNNReal)))
      + ∑ j, ρR j / 2 * (2 / (vR j r.toNNReal - w r.toNNReal)))) volume s u := hA.neg
  simp only [groupDrift_eq]
  rw [intervalIntegral.integral_sub hN (hIL i₀), intervalIntegral.integral_neg,
    intervalIntegral.integral_add hSL hSR,
    intervalIntegral.integral_finsetSum fun i _ => (hIL i).const_mul (ρL i / 2),
    intervalIntegral.integral_finsetSum fun j _ => (hIR j).const_mul (ρR j / 2)]
  simp only [intervalIntegral.integral_const_mul]

lemma groupDom_sub_eq (i₀ : Fin nL) (s u : ℝ≥0) :
    groupDom ρL ρR vL vR i₀ u - groupDom ρL ρR vL vR i₀ s
      = (∑ i, |ρL i| / 2 * -(vL i u - vL i s)) + (∑ j, |ρR j| / 2 * (vR j u - vR j s))
        + -(vL i₀ u - vL i₀ s) := by
  simp only [groupDom, mul_neg, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  ring

lemma le_groupDom_sub (hantiL : ∀ i, Antitone (vL i)) (hmonoR : ∀ j, Monotone (vR j))
    (i₀ : Fin nL) {s u : ℝ≥0} (hsu : s ≤ u) :
    -(vL i₀ u - vL i₀ s) ≤ groupDom ρL ρR vL vR i₀ u - groupDom ρL ρR vL vR i₀ s := by
  rw [groupDom_sub_eq]
  have h1 : 0 ≤ ∑ i, |ρL i| / 2 * -(vL i u - vL i s) := Finset.sum_nonneg fun i _ =>
    mul_nonneg (by positivity) (neg_nonneg.2 (sub_nonpos.2 (hantiL i hsu)))
  have h2 : 0 ≤ ∑ j, |ρR j| / 2 * (vR j u - vR j s) := Finset.sum_nonneg fun j _ =>
    mul_nonneg (by positivity) (sub_nonneg.2 (hmonoR j hsu))
  linarith

lemma integral_abs_groupDrift_le (hpL : ∀ i, IsForcePath w (vL i))
    (hpR : ∀ j, IsForcePath w (vR j)) (hantiL : ∀ i, Antitone (vL i))
    (hmonoR : ∀ j, Monotone (vR j)) (i₀ : Fin nL) {s u : ℝ≥0} (hsu : s ≤ u) :
    ∫ r in (s : ℝ)..u, |groupDrift ρL ρR w vL vR i₀ r.toNNReal|
      ≤ groupDom ρL ρR vL vR i₀ u - groupDom ρL ρR vL vR i₀ s := by
  have hsu' : (s : ℝ) ≤ u := hsu
  have hIL := fun i => (hpL i).intervalIntegrable_gap (NNReal.coe_nonneg s) hsu'
  have hIR := fun j => (hpR j).intervalIntegrable_gap (NNReal.coe_nonneg s) hsu'
  have hbL : ∀ i, ∫ r in (s : ℝ)..u, |2 / (vL i r.toNNReal - w r.toNNReal)|
      ≤ -(vL i u - vL i s) := fun i => by
    have h := (hpL i).integral_abs_gap_le (NNReal.coe_nonneg s) hsu'
    simp only [Real.toNNReal_coe] at h
    rwa [abs_of_nonpos (sub_nonpos.2 (hantiL i hsu))] at h
  have hbR : ∀ j, ∫ r in (s : ℝ)..u, |2 / (vR j r.toNNReal - w r.toNNReal)|
      ≤ vR j u - vR j s := fun j => by
    have h := (hpR j).integral_abs_gap_le (NNReal.coe_nonneg s) hsu'
    simp only [Real.toNNReal_coe] at h
    rwa [abs_of_nonneg (sub_nonneg.2 (hmonoR j hsu))] at h
  have hFL := intervalIntegrable_fun_sum fun i => (hIL i).abs.const_mul (|ρL i| / 2)
  have hFR := intervalIntegrable_fun_sum fun j => (hIR j).abs.const_mul (|ρR j| / 2)
  have hF2 : IntervalIntegrable (fun r : ℝ =>
      (∑ i, |ρL i| / 2 * |2 / (vL i r.toNNReal - w r.toNNReal)|)
        + ∑ j, |ρR j| / 2 * |2 / (vR j r.toNNReal - w r.toNNReal)|) volume s u := hFL.add hFR
  have hF : IntervalIntegrable (fun r : ℝ =>
      ((∑ i, |ρL i| / 2 * |2 / (vL i r.toNNReal - w r.toNNReal)|)
        + ∑ j, |ρR j| / 2 * |2 / (vR j r.toNNReal - w r.toNNReal)|)
        + |2 / (vL i₀ r.toNNReal - w r.toNNReal)|) volume s u := hF2.add (hIL i₀).abs
  have hle : ∀ r ∈ Icc (s : ℝ) u, |groupDrift ρL ρR w vL vR i₀ r.toNNReal|
      ≤ ((∑ i, |ρL i| / 2 * |2 / (vL i r.toNNReal - w r.toNNReal)|)
        + ∑ j, |ρR j| / 2 * |2 / (vR j r.toNNReal - w r.toNNReal)|)
        + |2 / (vL i₀ r.toNNReal - w r.toNNReal)| := fun r _ => by
    rw [groupDrift_eq]
    have hA : |∑ i, ρL i / 2 * (2 / (vL i r.toNNReal - w r.toNNReal))|
        ≤ ∑ i, |ρL i| / 2 * |2 / (vL i r.toNNReal - w r.toNNReal)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => by
        rw [abs_mul, abs_div, abs_two]))
    have hB : |∑ j, ρR j / 2 * (2 / (vR j r.toNNReal - w r.toNNReal))|
        ≤ ∑ j, |ρR j| / 2 * |2 / (vR j r.toNNReal - w r.toNNReal)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => by
        rw [abs_mul, abs_div, abs_two]))
    set A := ∑ i, ρL i / 2 * (2 / (vL i r.toNNReal - w r.toNNReal))
    set B := ∑ j, ρR j / 2 * (2 / (vR j r.toNNReal - w r.toNNReal))
    set C := 2 / (vL i₀ r.toNNReal - w r.toNNReal)
    have h1 := abs_add_le (-(A + B)) (-C)
    have h2 := abs_add_le A B
    rw [← sub_eq_add_neg, abs_neg, abs_neg] at h1
    linarith
  have hmono := intervalIntegral.integral_mono_on hsu'
    (intervalIntegrable_groupDrift hpL hpR i₀ hsu).abs hF hle
  rw [intervalIntegral.integral_add hF2 (hIL i₀).abs, intervalIntegral.integral_add hFL hFR,
    intervalIntegral.integral_finsetSum fun i _ => (hIL i).abs.const_mul (|ρL i| / 2),
    intervalIntegral.integral_finsetSum fun j _ => (hIR j).abs.const_mul (|ρR j| / 2)] at hmono
  simp only [intervalIntegral.integral_const_mul] at hmono
  rw [groupDom_sub_eq]
  have hsL : ∑ i, |ρL i| / 2 * ∫ r in (s : ℝ)..u, |2 / (vL i r.toNNReal - w r.toNNReal)|
      ≤ ∑ i, |ρL i| / 2 * -(vL i u - vL i s) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbL i) (by positivity)
  have hsR : ∑ j, |ρR j| / 2 * ∫ r in (s : ℝ)..u, |2 / (vR j r.toNNReal - w r.toNNReal)|
      ≤ ∑ j, |ρR j| / 2 * (vR j u - vR j s) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbR j) (by positivity)
  linarith [hbL i₀]

/-- The Tanaka hypotheses are trivial on a degenerate interval. -/
lemma isTanakaPathOn_self (a c : ℝ) (s : ℝ≥0) (x β j b ψ : ℝ≥0 → ℝ) :
    LocalTime.IsTanakaPathOn a c s s x β j b ψ := by
  have hI : Icc s s = {s} := Icc_self s
  refine ⟨?_, ?_, ?_, ?_, IntervalIntegrable.refl, ?_, ?_, ?_, ?_⟩
  · rw [hI]; exact continuousOn_singleton _ _
  · rw [hI]; exact continuousOn_singleton _ _
  · rw [hI]; exact continuousOn_singleton _ _
  · rw [hI]; exact continuousOn_singleton _ _
  · intro u hu
    rw [hI, mem_singleton_iff] at hu
    subst hu
    simp
  · rw [hI]; exact (subsingleton_singleton).monotoneOn _
  · intro u v hsu huv hvs _
    have h1 : u = s := le_antisymm (huv.trans hvs) hsu
    have h2 : v = s := le_antisymm hvs (hsu.trans huv)
    rw [h1, h2]
  · intro u hu
    rw [hI, mem_singleton_iff] at hu
    subst hu
    simp

/-- The reciprocal of `X = W − V^{i₀}` is dominated by the same process. -/
lemma intervalIntegrable_inv_and_le_groupDom (hpL : ∀ i, IsForcePath w (vL i))
    (hordL : ∀ t i, vL i t ≤ w t) (hantiL : ∀ i, Antitone (vL i))
    (hmonoR : ∀ j, Monotone (vR j)) (i₀ : Fin nL) {s e : ℝ≥0} (hse : s ≤ e) :
    IntervalIntegrable (fun r : ℝ => (w r.toNNReal - vL i₀ r.toNNReal)⁻¹) volume s e ∧
      ∀ u ∈ Icc s e, ∫ r in (s : ℝ)..u, (w r.toNNReal - vL i₀ r.toNNReal)⁻¹
        ≤ groupDom ρL ρR vL vR i₀ u - groupDom ρL ρR vL vR i₀ s := by
  have hpt : ∀ r : ℝ, (w r.toNNReal - vL i₀ r.toNNReal)⁻¹
      = (1 / 2) * |2 / (vL i₀ r.toNNReal - w r.toNNReal)| := fun r => by
    have h0 : 0 ≤ w r.toNNReal - vL i₀ r.toNNReal := sub_nonneg.2 (hordL _ i₀)
    have h1 : 2 / (vL i₀ r.toNNReal - w r.toNNReal)
        = -(2 * (w r.toNNReal - vL i₀ r.toNNReal)⁻¹) := by
      rw [show vL i₀ r.toNNReal - w r.toNNReal = -(w r.toNNReal - vL i₀ r.toNNReal) by ring,
        div_neg, div_eq_mul_inv]
    rw [h1, abs_neg, abs_of_nonneg (mul_nonneg zero_le_two (inv_nonneg.2 h0))]
    ring
  simp only [hpt]
  refine ⟨((hpL i₀).intervalIntegrable_gap (NNReal.coe_nonneg s)
    (NNReal.coe_le_coe.2 hse)).abs.const_mul _, fun u hu => ?_⟩
  have hsu' : (s : ℝ) ≤ u := hu.1
  rw [intervalIntegral.integral_const_mul]
  have h := (hpL i₀).integral_abs_gap_le (NNReal.coe_nonneg s) hsu'
  simp only [Real.toNNReal_coe] at h
  rw [abs_of_nonpos (sub_nonpos.2 (hantiL i₀ hu.1))] at h
  have h2 := le_groupDom_sub (ρL := ρL) (ρR := ρR) (vR := vR) hantiL hmonoR i₀ hu.1
  have h3 : 0 ≤ ∫ r in (s : ℝ)..u, |2 / (vL i₀ r.toNNReal - w r.toNNReal)| :=
    intervalIntegral.integral_nonneg hsu' fun r _ => abs_nonneg _
  linarith

/-- **The pathwise decomposition on a group interval.** On `[s, e]`, if the merge group of the
nearest left point `V^{i₀}` is `S` from `s` on and no other left point merges with it and no right
point meets the driver before `e`, then `X = W − V^{i₀}` satisfies the Tanaka hypotheses with
`a`, `c = 1 + ½ ∑_{i ∈ S} ρᵢ`, the singular push `J = −I^{i₀}`, the drift `groupDrift` and the
dominating process `groupDom`. -/
theorem isTanakaPathOn_group {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {β : ℝ≥0 → ℝ}
    (hw : ∀ t, w t = a * β t
      - (1 / 2) * ((∑ i, ρL i * (vL i t - xL i)) + ∑ j, ρR j * (vR j t - xR j)))
    (hβc : Continuous β) (hwc : Continuous w)
    (hpL : ∀ i, IsForcePath w (vL i)) (hpR : ∀ j, IsForcePath w (vR j))
    (hordL : ∀ t i, vL i t ≤ w t) (hantiL : ∀ i, Antitone (vL i))
    (hmonoR : ∀ j, Monotone (vR j))
    (hmerge : ∀ i j s t, s ≤ t → vL i s = vL j s → vL i t = vL j t)
    {i₀ : Fin nL} (hi₀ : ∀ t i, vL i t ≤ vL i₀ t) {S : Finset (Fin nL)} {s e : ℝ≥0}
    (hse : s ≤ e) (hS : ∀ i ∈ S, vL i s = vL i₀ s)
    (hgroup : ∀ u, s ≤ u → u < e → ∀ i ∉ S, vL i u ≠ vL i₀ u)
    (hright : ∀ u, s ≤ u → u < e → ∀ j, vR j u ≠ w u) :
    LocalTime.IsTanakaPathOn a (1 + (1 / 2) * ∑ i ∈ S, ρL i) s e (fun u => w u - vL i₀ u) β
      (fun u => -forceDefect w (vL i₀) u) (groupDrift ρL ρR w vL vR i₀)
      (groupDom ρL ρR vL vR i₀) := by
  have hcL : ∀ i, Continuous (vL i) := fun i => (hpL i).1
  have hcR : ∀ j, Continuous (vR j) := fun j => (hpR j).1
  have hdefL : ∀ u, s ≤ u → u ≤ e → ∀ i, forceDefect w (vL i) u - forceDefect w (vL i) s
      = if i ∈ S then forceDefect w (vL i₀) u - forceDefect w (vL i₀) s else 0 := by
    intro u hsu hue i
    split_ifs with hi
    · exact (hpL i₀).forceDefect_sub_eq_of_eqOn (hpL i) hsu
        (fun r hsr _ => hmerge i i₀ s r hsr (hS i hi))
    · rw [(hpL i).forceDefect_eq_of_forall_ne_Ico hsu (fun r hsr hru h =>
        hgroup r hsr (hru.trans_le hue) i hi
          (le_antisymm (hi₀ r i) (by rw [h]; exact hordL r i₀))), sub_self]
  have hdefR : ∀ u, s ≤ u → u ≤ e → ∀ j, forceDefect w (vR j) u - forceDefect w (vR j) s = 0 :=
    fun u hsu hue j => by
      rw [(hpR j).forceDefect_eq_of_forall_ne_Ico hsu
        (fun r hsr hru => hright r hsr (hru.trans_le hue) j), sub_self]
  have hψc : Continuous (groupDom ρL ρR vL vR i₀) :=
    ((continuous_finsetSum _ fun i _ => continuous_const.mul (hcL i).neg).add
      (continuous_finsetSum _ fun j _ => continuous_const.mul (hcR j))).sub (hcL i₀)
  refine ⟨(hwc.sub (hcL i₀)).continuousOn, hβc.continuousOn,
    (hpL i₀).continuous_forceDefect.neg.continuousOn, hψc.continuousOn,
    intervalIntegrable_groupDrift hpL hpR i₀ hse, ?_, ?_, ?_,
    fun u hu => integral_abs_groupDrift_le hpL hpR hantiL hmonoR i₀ hu.1⟩
  · intro u hu
    obtain ⟨hsu, hue⟩ := hu
    have hD := integral_groupDrift (ρL := ρL) (ρR := ρR) hpL hpR i₀ hsu
    have h0 := (hpL i₀).forceDefect_sub_eq hsu
    have hwu := hw u
    have hws := hw s
    set ΔI := forceDefect w (vL i₀) u - forceDefect w (vL i₀) s with hΔI
    have hSL : (∑ i, ρL i * (vL i u - xL i)) - (∑ i, ρL i * (vL i s - xL i))
        = (∑ i ∈ S, ρL i) * ΔI
          + ∑ i, ρL i * ∫ r in (s : ℝ)..u, 2 / (vL i r.toNNReal - w r.toNNReal) := by
      rw [← Finset.sum_sub_distrib]
      have hpt : ∀ i, ρL i * (vL i u - xL i) - ρL i * (vL i s - xL i)
          = ρL i * (if i ∈ S then ΔI else 0)
            + ρL i * ∫ r in (s : ℝ)..u, 2 / (vL i r.toNNReal - w r.toNNReal) := fun i => by
        have h1 := (hpL i).forceDefect_sub_eq hsu
        rw [hdefL u hsu hue i] at h1
        rw [← mul_add, h1]
        ring
      rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      simp only [mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
    have hSR : (∑ j, ρR j * (vR j u - xR j)) - (∑ j, ρR j * (vR j s - xR j))
        = ∑ j, ρR j * ∫ r in (s : ℝ)..u, 2 / (vR j r.toNNReal - w r.toNNReal) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 := (hpR j).forceDefect_sub_eq hsu
      rw [hdefR u hsu hue j] at h1
      linear_combination ρR j * (-h1)
    have hhL : ∑ i, ρL i / 2 * ∫ r in (s : ℝ)..u, 2 / (vL i r.toNNReal - w r.toNNReal)
        = (1 / 2) * ∑ i, ρL i * ∫ r in (s : ℝ)..u, 2 / (vL i r.toNNReal - w r.toNNReal) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hhR : ∑ j, ρR j / 2 * ∫ r in (s : ℝ)..u, 2 / (vR j r.toNNReal - w r.toNNReal)
        = (1 / 2) * ∑ j, ρR j * ∫ r in (s : ℝ)..u, 2 / (vR j r.toNNReal - w r.toNNReal) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only
    linear_combination hwu - hws - hD + h0 - (1 / 2) * hSL - (1 / 2) * hSR + hhL + hhR
  · intro x _ y _ hxy
    have h := (hpL i₀).forceDefect_sub_mem_uIcc hxy
    rw [uIcc_of_ge (sub_nonpos.2 (hantiL i₀ hxy))] at h
    simp only
    linarith [h.2]
  · intro u v _ huv _ hne
    simp only
    rw [(hpL i₀).forceDefect_eq_of_forall_ne huv (fun r hr h => hne r hr (by
      simp only [h, sub_self]))]

end Pathwise

/-! ### The local Tanaka step -/

section Stochastic

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The event that the merge group of `V^{i₀}` at time `s` is exactly `S`. -/
def groupEvent (VL : Fin nL → ℝ≥0 → Ω → ℝ) (i₀ : Fin nL) (S : Finset (Fin nL)) (s : ℝ≥0) :
    Set Ω :=
  {ω | ∀ i, VL i s ω = VL i₀ s ω ↔ i ∈ S}

/-- A process that vanishes exactly when a left point outside `S` merges with `V^{i₀}` or a right
point meets the driver. -/
def groupStopProc (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (i₀ : Fin nL) (S : Finset (Fin nL)) : ℝ≥0 → Ω → ℝ :=
  fun u ω => (∏ i ∈ Sᶜ, (VL i u ω - VL i₀ u ω)) * ∏ j, (VR j u ω - W u ω)

open scoped Classical in
/-- The end of a group interval started at `s`: on the group event, the first time `≥ s` at which
the group changes or a right point meets the driver; `s` otherwise. -/
def groupStop (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (i₀ : Fin nL) (S : Finset (Fin nL)) (s : ℝ≥0) : Ω → WithTop ℝ≥0 :=
  (groupEvent VL i₀ S s).piecewise (zeroHit (groupStopProc W VL VR i₀ S) s)
    (fun _ => (s : WithTop ℝ≥0))

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

lemma groupStopProc_ne_zero_iff (i₀ : Fin nL) (S : Finset (Fin nL)) (u : ℝ≥0) (ω : Ω) :
    groupStopProc W VL VR i₀ S u ω ≠ 0 ↔
      (∀ i ∉ S, VL i u ω ≠ VL i₀ u ω) ∧ ∀ j, VR j u ω ≠ W u ω := by
  simp only [groupStopProc, mul_ne_zero_iff, Finset.prod_ne_zero_iff, Finset.mem_compl,
    sub_ne_zero, Finset.mem_univ, true_imp_iff]

lemma continuous_groupStopProc (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVLc : ∀ i ω, Continuous fun t => VL i t ω) (hVRc : ∀ j ω, Continuous fun t => VR j t ω)
    (i₀ : Fin nL) (S : Finset (Fin nL)) (ω : Ω) :
    Continuous fun u => groupStopProc W VL VR i₀ S u ω :=
  (continuous_finsetProd _ fun i _ => (hVLc i ω).sub (hVLc i₀ ω)).mul
    (continuous_finsetProd _ fun j _ => (hVRc j ω).sub (hWc ω))

lemma measurable_groupStopProc (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ j, StronglyAdapted 𝓕 (VR j)) (i₀ : Fin nL) (S : Finset (Fin nL)) (u : ℝ≥0) :
    Measurable[𝓕 u] (groupStopProc W VL VR i₀ S u) :=
  (Finset.measurable_prod _ fun i _ => ((hVLa i u).measurable.sub (hVLa i₀ u).measurable)).mul
    (Finset.measurable_prod _ fun j _ => ((hVRa j u).measurable.sub (hWa u).measurable))

lemma measurableSet_groupEvent (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (i₀ : Fin nL)
    (S : Finset (Fin nL)) (s : ℝ≥0) : MeasurableSet[𝓕 s] (groupEvent VL i₀ S s) := by
  have : groupEvent VL i₀ S s = ⋂ i, {ω | VL i s ω = VL i₀ s ω ↔ i ∈ S} := by
    ext ω; simp [groupEvent]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : MeasurableSet[𝓕 s] {ω | VL i s ω = VL i₀ s ω} :=
    measurableSet_eq_fun (hVLa i s).measurable (hVLa i₀ s).measurable
  by_cases hi : i ∈ S
  · have h : {ω | VL i s ω = VL i₀ s ω ↔ i ∈ S} = {ω | VL i s ω = VL i₀ s ω} := by
      ext ω; simp [hi]
    rw [h]; exact hm
  · have h : {ω | VL i s ω = VL i₀ s ω ↔ i ∈ S} = {ω | VL i s ω = VL i₀ s ω}ᶜ := by
      ext ω; simp [hi]
    rw [h]; exact hm.compl

lemma isStoppingTime_groupStop (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVLc : ∀ i ω, Continuous fun t => VL i t ω) (hVRc : ∀ j ω, Continuous fun t => VR j t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ j, StronglyAdapted 𝓕 (VR j)) (i₀ : Fin nL) (S : Finset (Fin nL)) (s : ℝ≥0) :
    IsStoppingTime 𝓕 (groupStop W VL VR i₀ S s) := by
  classical
  exact IsStoppingTime.piecewise_of_le
    (isStoppingTime_zeroHit (continuous_groupStopProc hWc hVLc hVRc i₀ S)
      (measurable_groupStopProc hWa hVLa hVRa i₀ S) s)
    (isStoppingTime_const 𝓕 s) (le_zeroHit (continuous_groupStopProc hWc hVLc hVRc i₀ S) s)
    (fun _ => le_rfl) (measurableSet_groupEvent hVLa i₀ S s)

/-- **The local Tanaka step** (Specification p. 37, "The singular motions vanish"). Let
`W = a β − ½ ∑ⱼ ρⱼ (Vʲ − xʲ)` with `β` an `𝓕`-Brownian motion, the force points force paths with
the monotonicity and merging properties of geometric images, and `V^{i₀}` the left point nearest
to the driver. If `1 + ½ ∑_{i ∈ S} ρᵢ ≠ 0`, then almost surely, whenever the merge group of
`V^{i₀}` at `s` is exactly `S`, and on `[s, u]` no other left point merges with `V^{i₀}` and no
right point meets the driver, the defect `I^{i₀}` is constant on `[s, u]` (`u ≤ t`). -/
theorem ae_forceDefect_const_of_group {P : Measure Ω} [IsProbabilityMeasure P] {a : ℝ}
    (ha : a ≠ 0) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {β : ℝ≥0 → Ω → ℝ} (hβ : IsFilteredPreBrownian β 𝓕 P)
    (hβc : ∀ ω, Continuous fun t => β t ω)
    (hW : ∀ t ω, W t ω = a * β t ω
      - (1 / 2) * ((∑ i, ρL i * (VL i t ω - xL i)) + ∑ j, ρR j * (VR j t ω - xR j)))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓕 (VR j))
    (hpL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpR : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => VR j t ω))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hantiL : ∀ ω i, Antitone fun t => VL i t ω)
    (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hmerge : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    {i₀ : Fin nL} (hi₀ : ∀ ω t i, VL i t ω ≤ VL i₀ t ω) (S : Finset (Fin nL))
    (hS : 1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0) {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, (∀ i, VL i s ω = VL i₀ s ω ↔ i ∈ S) → ∀ u, s ≤ u → u ≤ t →
      (∀ r, s ≤ r → r ≤ u → (∀ i ∉ S, VL i r ω ≠ VL i₀ r ω) ∧ ∀ j, VR j r ω ≠ W r ω) →
      forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u
        = forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) s := by
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpL ω i).1
  have hVRc : ∀ j ω, Continuous fun t => VR j t ω := fun j ω => (hpR ω j).1
  set τ := groupStop W VL VR i₀ S s with hτdef
  have hτ : IsStoppingTime 𝓕 τ := isStoppingTime_groupStop hWc hVLc hVRc hWa hVLa hVRa i₀ S s
  have hgc := continuous_groupStopProc hWc hVLc hVRc i₀ S
  have hsτ : ∀ ω, (s : WithTop ℝ≥0) ≤ τ ω := fun ω => by
    classical
    by_cases hE : ω ∈ groupEvent VL i₀ S s
    · rw [hτdef, groupStop, Set.piecewise_eq_of_mem _ _ _ hE]; exact le_zeroHit hgc s ω
    · rw [hτdef, groupStop, Set.piecewise_eq_of_notMem _ _ _ hE]
  -- the processes of the Tanaka argument
  have hX : ∀ u, Measurable[𝓕 u] fun ω => W u ω - VL i₀ u ω := fun u =>
    (hWa u).measurable.sub (hVLa i₀ u).measurable
  have hJ : ∀ u, Measurable[𝓕 u] fun ω => -forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u :=
    fun u => (measurable_forceDefect hWc (hVLc i₀) hWa (hVLa i₀) u).neg
  have hψ : ∀ u, Measurable[𝓕 u] fun ω =>
      groupDom ρL ρR (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ u := fun u => by
    simp only [groupDom]
    exact ((Finset.measurable_sum _ fun i _ => ((hVLa i u).measurable.neg.const_mul _)).add
      (Finset.measurable_sum _ fun j _ => ((hVRa j u).measurable.const_mul _))).sub
        (hVLa i₀ u).measurable
  have hP : ∀ᵐ ω ∂P, (s : WithTop ℝ≥0) ≤ τ ω →
      LocalTime.IsTanakaPathOn a (1 + (1 / 2) * ∑ i ∈ S, ρL i) s (LocalTime.stopEnd τ t ω)
        ((fun u ω => W u ω - VL i₀ u ω) · ω) (β · ω)
        ((fun u ω => -forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u) · ω)
        ((fun u ω => groupDrift ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
          (fun j t => VR j t ω) i₀ u) · ω)
        ((fun u ω => groupDom ρL ρR (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ u) · ω) := by
    refine Eventually.of_forall fun ω hsτω => ?_
    classical
    by_cases hE : ω ∈ groupEvent VL i₀ S s
    · have hτω : τ ω = zeroHit (groupStopProc W VL VR i₀ S) s ω := by
        rw [hτdef, groupStop, Set.piecewise_eq_of_mem _ _ _ hE]
      have hlt : ∀ u, u < LocalTime.stopEnd τ t ω → (u : WithTop ℝ≥0) < τ ω := fun u hu =>
        (WithTop.coe_lt_coe.2 hu).trans_le (LocalTime.coe_stopEnd_le τ t ω)
      have hne : ∀ u, s ≤ u → u < LocalTime.stopEnd τ t ω →
          (∀ i ∉ S, VL i u ω ≠ VL i₀ u ω) ∧ ∀ j, VR j u ω ≠ W u ω := fun u hsu hu =>
        (groupStopProc_ne_zero_iff i₀ S u ω).1
          (ne_zero_of_lt_zeroHit hgc hsu (hτω ▸ hlt u hu))
      exact isTanakaPathOn_group (xL := xL) (xR := xR) (fun t => hW t ω) (hβc ω) (hWc ω)
        (hpL ω) (hpR ω) (hordL ω) (hantiL ω) (hmonoR ω) (hmerge ω) (hi₀ ω)
        (LocalTime.s_le_stopEnd hst hsτω) (fun i hi => (hE i).2 hi)
        (fun u hsu hu => (hne u hsu hu).1) (fun u hsu hu => (hne u hsu hu).2)
    · have hτω : τ ω = (s : WithTop ℝ≥0) := by
        rw [hτdef, groupStop, Set.piecewise_eq_of_notMem _ _ _ hE]
      have he : LocalTime.stopEnd τ t ω = s := by
        simp only [LocalTime.stopEnd, hτω]
        exact min_eq_right hst
      rw [he]
      exact isTanakaPathOn_self _ _ _ _ _ _ _ _
  have hnn : ∀ᵐ ω ∂P, (s : WithTop ℝ≥0) ≤ τ ω →
      ∀ u ∈ Icc s (LocalTime.stopEnd τ t ω), 0 ≤ W u ω - VL i₀ u ω :=
    Eventually.of_forall fun ω _ u _ => sub_nonneg.2 (hordL ω u i₀)
  have hrec : ∀ᵐ ω ∂P, (s : WithTop ℝ≥0) ≤ τ ω →
      IntervalIntegrable (fun r : ℝ => (W r.toNNReal ω - VL i₀ r.toNNReal ω)⁻¹) volume s
        (LocalTime.stopEnd τ t ω) ∧
      ∀ u ∈ Icc s (LocalTime.stopEnd τ t ω), ∫ r in (s : ℝ)..u,
        (W r.toNNReal ω - VL i₀ r.toNNReal ω)⁻¹
          ≤ groupDom ρL ρR (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ u
            - groupDom ρL ρR (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ s :=
    Eventually.of_forall fun ω hsτω => intervalIntegrable_inv_and_le_groupDom (hpL ω) (hordL ω)
      (hantiL ω) (hmonoR ω) i₀ (LocalTime.s_le_stopEnd hst hsτω)
  have hmain := LocalTime.ae_singular_const_stopped hβ hst hτ hX hJ hψ ha hS hP hnn hrec
  filter_upwards [hmain] with ω hω hE u hsu hut hgood
  classical
  have hE' : ω ∈ groupEvent VL i₀ S s := hE
  have hτω : τ ω = zeroHit (groupStopProc W VL VR i₀ S) s ω := by
    rw [hτdef, groupStop, Set.piecewise_eq_of_mem _ _ _ hE']
  have hu : (u : WithTop ℝ≥0) ≤ τ ω := by
    rw [hτω]
    exact (lt_zeroHit_of_forall_ne hgc fun r hsr hru =>
      (groupStopProc_ne_zero_iff i₀ S r ω).2 (hgood r hsr hru)).le
  exact neg_inj.1 (hω u hsu hut hu)

end Stochastic

end MartChar

end InteractingSLE
