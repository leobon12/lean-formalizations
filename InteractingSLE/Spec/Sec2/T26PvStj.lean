/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.GenCvClock
import InteractingSLE.Spec.Sec2.MartingaleStieltjes
import InteractingSLE.Spec.Sec2.MartingaleLevy

/-!
# Theorem 2.6, the provider, part 2: the gap times a force-point measure is twice Lebesgue measure

Packet PROVE-T26-PROVIDER. Specification, proof of Theorem 2.4 (`source/spec/p001-048.md` L842–L854; used by the
proof of Theorem 2.6, L977–L986): a geometric force-point image `V` is continuous and monotone, solves
`dV = 2/(V − W) dt` away from its Lebesgue-null collision set, and its singular motion is carried by the collision set.
In measure form: for the Stieltjes measure `dV` (of `ε V`, `ε = ±1` the direction of `V`),

  `ε (V − W) · d(ε V) = 2 dt`.

* `stj f hf hc`: the Stieltjes function of a continuous nondecreasing `f : ℝ≥0 → ℝ`;
* `integral_Ioc_gap_eq`: `∫_{(a, b]} ε (V − W) d(ε V) = 2 (b − a)`, from the landed Riemann–Stieltjes estimate of the
  gap (`MartChar.exists_delta_abs_sum_gap_mul_sub_sub_le`) and the convergence of left-point Stieltjes sums
  (`Ito.Gen.tendsto_stieltjes_sum`);
* `withDensity_gap_restrict_eq`: the measure identity on every `(0, T]`;
* **`setIntegral_gap_mul_eq`**: `∫_{(0, t]} ε (V − W) g d(ε V) = 2 ∫_{(0, t]} g dt` for `g` continuous on `[0, t]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T26Pv

/-- The Stieltjes function of a continuous nondecreasing path. -/
def stj (f : ℝ≥0 → ℝ) (hf : Monotone f) (hc : Continuous f) : StieltjesFunction ℝ≥0 where
  toFun := f
  mono' := hf
  right_continuous' _ := hc.continuousWithinAt

@[simp] theorem stj_apply (f : ℝ≥0 → ℝ) (hf : Monotone f) (hc : Continuous f) (t : ℝ≥0) :
    stj f hf hc t = f t := rfl

/-- The time integrator: the identity clock. -/
abbrev clk : StieltjesFunction ℝ≥0 := Ito.GenCont.clockPath id monotone_id continuous_id

theorem clk_measure_Ioc (a b : ℝ≥0) : clk.measure (Ioc a b) = ENNReal.ofReal ((b : ℝ) - a) := by
  rw [StieltjesFunction.measure_Ioc]
  rfl

section Gap

variable {w v : ℝ≥0 → ℝ} {ε : ℝ}

theorem continuous_mul_path (hv : Continuous v) : Continuous fun t => ε * v t :=
  continuous_const.mul hv

/-- **The Riemann–Stieltjes identity**: `∫_{(a, b]} ε (V − W) d(ε V) = 2 (b − a)`. -/
theorem integral_Ioc_gap_eq (hw : Continuous w) (hv : MartChar.IsForcePath w v) (hε : ε * ε = 1)
    (hU : Monotone fun t => ε * v t) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ u in Ioc a b, ε * (v u - w u) ∂(stj (fun t => ε * v t) hU (continuous_mul_path hv.1)).measure =
      2 * ((b : ℝ) - a) := by
  set A := stj (fun t => ε * v t) hU (continuous_mul_path hv.1) with hA
  have hg : Continuous fun u => ε * (v u - w u) := continuous_const.mul (hv.1.sub hw)
  have hlim := Ito.Gen.tendsto_stieltjes_sum A hg hab
  set π := MathFin.unifPartIcc a b with hπ
  -- the same sums tend to `2 (b − a)`
  set v' : ℝ → ℝ := fun u => v u.toNNReal with hv'
  set w' : ℝ → ℝ := fun u => w u.toNNReal with hw'
  have hvc : Continuous v' := hv.1.comp continuous_real_toNNReal
  have hwc : Continuous w' := hw.comp continuous_real_toNNReal
  have hmono : MonotoneOn v' (Icc (a : ℝ) b) ∨ AntitoneOn v' (Icc (a : ℝ) b) := by
    rcases hv.2.1 with h | h
    · exact Or.inl ((h.comp (fun _ _ hxy => Real.toNNReal_mono hxy)).monotoneOn _)
    · exact Or.inr ((h.comp_monotone (fun _ _ hxy => Real.toNNReal_mono hxy)).antitoneOn _)
  have hderiv : ∀ u ∈ Ioo (a : ℝ) b, v' u ≠ w' u → HasDerivAt v' (2 / (v' u - w' u)) u := by
    intro u hu hne
    exact hv.2.2.1 u ((a.coe_nonneg).trans_lt hu.1) hne
  have hnull : MeasureTheory.volume {u ∈ Icc (a : ℝ) b | v' u = w' u} = 0 := by
    refine measure_mono_null (fun u hu => ?_) hv.2.2.2
    exact ⟨(a.coe_nonneg).trans hu.1.1, hu.2⟩
  have hsum_eq : ∀ n, (∑ k ∈ Finset.range n, (ε * (v (π n k) - w (π n k))) * (A (π n (k + 1)) - A (π n k))) =
      ∑ k ∈ Finset.range n, (v' (π n k) - w' (π n k)) * (v' (π n (k + 1)) - v' (π n k)) := by
    intro n
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hA, stj_apply, hv', hw', Real.toNNReal_coe]
    linear_combination (v (π n k) - w (π n k)) * (v (π n (k + 1)) - v (π n k)) * hε
  have hlim2 : Tendsto (fun n => ∑ k ∈ Finset.range n,
      (ε * (v (π n k) - w (π n k))) * (A (π n (k + 1)) - A (π n k))) atTop (𝓝 (2 * ((b : ℝ) - a))) := by
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨δ, hδ, hest⟩ := MartChar.exists_delta_abs_sum_gap_mul_sub_sub_le hvc.continuousOn
      hwc.continuousOn hmono hderiv hnull (half_pos he)
    obtain ⟨N, hN⟩ := exists_nat_gt (((b : ℝ) - a) / δ)
    refine ⟨N + 1, fun n hn => ?_⟩
    have hn0 : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hmesh : ∀ k < n, ((π n (k + 1) : ℝ≥0) : ℝ) - (π n k : ℝ) < δ := by
      intro k _
      rw [hπ, MathFin.unifPartIcc_succ_sub hab]
      have hba : 0 ≤ (b : ℝ) - a := sub_nonneg.2 (by exact_mod_cast hab)
      rw [div_lt_iff₀ hnpos]
      have h1 : ((b : ℝ) - a) / δ < n := hN.trans (by exact_mod_cast (Nat.lt_of_succ_le hn))
      rw [div_lt_iff₀ hδ] at h1
      linarith
    have h := hest n (fun k => (π n k : ℝ)) (fun i j hij => by exact_mod_cast MathFin.unifPartIcc_mono a b n hij)
      (by simp [hπ, MathFin.unifPartIcc_zero]) (by simp [hπ, MathFin.unifPartIcc_self hab hn0]) hmesh
    rw [Real.dist_eq, hsum_eq n]
    exact h.trans_lt (half_lt_self he)
  exact tendsto_nhds_unique hlim hlim2

/-- `ε (V − W) d(ε V)` and `2 dt` agree on every interval. -/
theorem withDensity_gap_Ioc (hw : Continuous w) (hv : MartChar.IsForcePath w v) (hε : ε * ε = 1)
    (hU : Monotone fun t => ε * v t) (h0 : ∀ u, 0 ≤ ε * (v u - w u)) (a b : ℝ≥0) :
    (stj (fun t => ε * v t) hU (continuous_mul_path hv.1)).measure.withDensity
        (fun u => ((ε * (v u - w u)).toNNReal : ℝ≥0∞)) (Ioc a b) =
      ((2 : ℝ≥0∞) • clk.measure) (Ioc a b) := by
  set A := stj (fun t => ε * v t) hU (continuous_mul_path hv.1) with hA
  rcases le_or_gt a b with hab | hab
  · have hg : Continuous fun u => ε * (v u - w u) := continuous_const.mul (hv.1.sub hw)
    have hint : IntegrableOn (fun u => ε * (v u - w u)) (Ioc a b) A.measure :=
      (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [withDensity_apply _ measurableSet_Ioc, Measure.smul_apply, clk_measure_Ioc]
    have e : ∫⁻ u in Ioc a b, ((ε * (v u - w u)).toNNReal : ℝ≥0∞) ∂A.measure =
        ENNReal.ofReal (∫ u in Ioc a b, ε * (v u - w u) ∂A.measure) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun u => h0 u)]
      rfl
    rw [e, integral_Ioc_gap_eq hw hv hε hU hab, smul_eq_mul, ENNReal.ofReal_mul (by norm_num)]
    simp
  · rw [Ioc_eq_empty (not_lt.2 hab.le)]
    simp

/-- **The measure identity** `ε (V − W) d(ε V) = 2 dt` on `(0, T]`. -/
theorem withDensity_gap_restrict_eq (hw : Continuous w) (hv : MartChar.IsForcePath w v) (hε : ε * ε = 1)
    (hU : Monotone fun t => ε * v t) (h0 : ∀ u, 0 ≤ ε * (v u - w u)) (T : ℝ≥0) :
    ((stj (fun t => ε * v t) hU (continuous_mul_path hv.1)).measure.withDensity
        (fun u => ((ε * (v u - w u)).toNNReal : ℝ≥0∞))).restrict (Ioc 0 T) =
      ((2 : ℝ≥0∞) • clk.measure).restrict (Ioc 0 T) := by
  have hI := withDensity_gap_Ioc hw hv hε hU h0
  have : IsFiniteMeasure (((stj (fun t => ε * v t) hU (continuous_mul_path hv.1)).measure.withDensity
      (fun u => ((ε * (v u - w u)).toNNReal : ℝ≥0∞))).restrict (Ioc 0 T)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, hI, Measure.smul_apply, clk_measure_Ioc, smul_eq_mul]
    exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
  refine Measure.ext_of_Ioc_finite _ _ ?_ fun a b _ => ?_
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ, hI]
  · rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc, hI]

/-- **The force-point integral identity**: `∫_{(0, t]} ε (V − W) g d(ε V) = 2 ∫_{(0, t]} g dt`. -/
theorem setIntegral_gap_mul_eq (hw : Continuous w) (hv : MartChar.IsForcePath w v) (hε : ε * ε = 1)
    (hU : Monotone fun t => ε * v t) (h0 : ∀ u, 0 ≤ ε * (v u - w u)) (g : ℝ≥0 → ℝ) (t : ℝ≥0) :
    ∫ u in Ioc 0 t, ε * (v u - w u) * g u ∂(stj (fun t => ε * v t) hU (continuous_mul_path hv.1)).measure =
      2 * ∫ u in Ioc 0 t, g u ∂clk.measure := by
  set A := stj (fun t => ε * v t) hU (continuous_mul_path hv.1) with hA
  have hmeas : Measurable fun u => (ε * (v u - w u)).toNNReal :=
    (continuous_const.mul (hv.1.sub hw)).measurable.real_toNNReal
  have e1 : ∫ u in Ioc 0 t, ε * (v u - w u) * g u ∂A.measure =
      ∫ u in Ioc 0 t, (ε * (v u - w u)).toNNReal • g u ∂A.measure := by
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (h0 u)]
  rw [e1, ← setIntegral_withDensity_eq_setIntegral_smul hmeas g measurableSet_Ioc]
  have e2 := withDensity_gap_restrict_eq hw hv hε hU h0 t
  rw [show (∫ u in Ioc 0 t, g u ∂A.measure.withDensity fun u => ((ε * (v u - w u)).toNNReal : ℝ≥0∞)) =
      ∫ u, g u ∂((A.measure.withDensity fun u => ((ε * (v u - w u)).toNNReal : ℝ≥0∞)).restrict (Ioc 0 t))
      from rfl, e2, Measure.restrict_smul, integral_smul_measure]
  simp

end Gap

end InteractingSLE.Sec2.T26Pv
