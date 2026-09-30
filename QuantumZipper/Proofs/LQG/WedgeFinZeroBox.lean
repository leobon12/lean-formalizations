import QuantumZipper.Proofs.LQG.FiniteArea

/-!
# WEDGE-FIN0, part 1: the area near the boundary point `0` at scale `2^{-m}` (boxes)

Fix `m` and `δ = 2^{-m}`. For the normalized field `Z = aZ X 2` we cover
`B(0, 2^{-m-5}) ∩ ℍ` by the Whitney boxes `boxU (m+6+i) j`, `j ∈ jSet i` (`ball_subset_boxes`), and
factor the approximating masses of each box through the **single** semicircle average at `0` of
radius `δ` (`FinArea.ae_areaApprox_eq_omega_mul` with `t = 0`):

* `ae_qAreaMeasure_ball_le`: a.s. `μ_Z(B(0,2^{-m-5}) ∩ ℍ) ≤ A_m · S_m`, with the lognormal factor
  `A_m = e^{γ Z(fc(0,δ))} δ^{γ²/2}` (`Af`) and `S_m = Σ_boxes liminf_k W_k(box)` (`Sf`), a
  function of the inner field `innerSampleC X 0 δ` (hence independent of `A_m`);
* `lintegral_Mb_rpow_le`: the `p`-th moment of each box term, by the box's **own** lognormal
  factor at `(j 2^{-n}, 5·2^{-n})` (`FinArea.lintegral_liminf_areaApprox_rpow_le` for the field
  `aZ X δ`, whose area approximations are `δ^{γ²/2} W_k`);
* `lintegral_Sf_rpow_le`: `E S_m^p ≤ C 2^{-2pm}` whenever `eA(p) = p(2 + γ²/2) − p²γ² > 1`.

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
§3 (circle averages have independent increments; fractional moments of the bulk measure); the
box decomposition and the constants are those of `FiniteArea` (M4-A3). Using the Ω-factor
centred at `0` together with the box factors (so that small moments `p' < p` are available,
part 2) is the route of handoff `M4-A5-WEDGE.md`; the bookkeeping is our own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace WedgeFinZero

open FinArea

/-! ### Geometry -/

/-- Box indices at level `m + 6 + i`. -/
def jSet (i : ℕ) : Finset ℤ := Finset.Icc (-((2 : ℤ) ^ (i + 1) + 1)) ((2 : ℤ) ^ (i + 1) + 1)

theorem card_jSet_le (i : ℕ) : ((jSet i).card : ℝ) ≤ 8 * 2 ^ i := by
  have h0 : (0 : ℤ) ≤ (2 : ℤ) ^ (i + 1) := by positivity
  have hc : ((jSet i).card : ℤ) = 2 * 2 ^ (i + 1) + 3 := by
    rw [jSet, Int.card_Icc_of_le _ _ (by linarith)]; ring
  have hcR : ((jSet i).card : ℝ) = 2 * 2 ^ (i + 1) + 3 := by exact_mod_cast hc
  have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  rw [hcR, pow_succ]; linarith

theorem abs_le_of_mem_jSet {i : ℕ} {j : ℤ} (hj : j ∈ jSet i) : |(j : ℝ)| ≤ 2 ^ (i + 1) + 1 := by
  rw [jSet, Finset.mem_Icc] at hj
  have h1 : (j : ℝ) ≤ ((2 : ℤ) ^ (i + 1) + 1 : ℤ) := by exact_mod_cast hj.2
  have h2 : ((-((2 : ℤ) ^ (i + 1) + 1) : ℤ) : ℝ) ≤ j := by exact_mod_cast hj.1
  push_cast at h1 h2
  rw [abs_le]; constructor <;> linarith

theorem radius_add (m k : ℕ) : radius (m + k) = radius m * radius k := by
  simp only [radius, pow_add]

theorem radius_shift (m i : ℕ) : radius (m + 5) = 2 ^ (i + 1) * radius (m + 6 + i) := by
  rw [show m + 6 + i = (m + 5) + (i + 1) by omega, radius_add (m + 5) (i + 1)]
  have h : radius (i + 1) * 2 ^ (i + 1) = 1 := by rw [radius, ← mul_pow]; norm_num
  linear_combination (-(radius (m + 5))) * h

theorem radius_le_div64 (m i : ℕ) : radius (m + 6 + i) ≤ radius m / 64 := by
  have h := AreaExist.aradius_anti (show m + 6 ≤ m + 6 + i by omega)
  have h6 : radius (m + 6) = radius m * radius 6 := radius_add m 6
  have : radius 6 = 1 / 64 := by norm_num [radius]
  rw [this] at h6; linarith

theorem radius5 (m : ℕ) : radius (m + 5) = radius m / 32 := by
  rw [radius_add]; norm_num [radius]; ring

/-- Geometry of the boxes of level `m + 6 + i`. -/
theorem box_spec {m i : ℕ} {j : ℤ} (hj : j ∈ jSet i) :
    |(j * radius (m + 6 + i) : ℝ)| + 5 * radius (m + 6 + i) ≤ radius m ∧
      ∀ z ∈ boxK (m + 6 + i) j, ‖z‖ ≤ radius m / 8 := by
  set n := m + 6 + i
  have hr := radius_pos n
  have hm := radius_pos m
  have hc : |(j * radius n : ℝ)| ≤ radius (m + 5) + radius n := by
    rw [abs_mul, abs_of_pos hr, radius_shift m i]
    have := mul_le_mul_of_nonneg_right (abs_le_of_mem_jSet hj) hr.le
    linarith
  have h64 := radius_le_div64 m i
  have h5 := radius5 m
  refine ⟨by linarith, fun z hz => ?_⟩
  have h1 := norm_sub_le_of_mem_boxK hz
  have h2 : ‖z‖ ≤ ‖z - ((j * radius n : ℝ) : ℂ)‖ + |(j * radius n : ℝ)| := by
    have := norm_add_le (z - ((j * radius n : ℝ) : ℂ)) ((j * radius n : ℝ) : ℂ)
    rwa [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at this
  linarith

/-- **Covering** of `B(0, 2^{-m-5}) ∩ ℍ` by the boxes of levels `≥ m + 6`. -/
theorem ball_subset_boxes (m : ℕ) :
    Metric.ball (0 : ℂ) (radius (m + 5)) ∩ H ⊆ ⋃ i, ⋃ j ∈ jSet i, boxU (m + 6 + i) j := by
  classical
  rintro z ⟨hzb, hzH⟩
  have hza : ‖z‖ < radius (m + 5) := by simpa using hzb
  have hzH' : 0 < z.im := hzH
  have hex : ∃ n, radius n < z.im := exists_pow_lt_of_lt_one hzH' (by norm_num : (2 : ℝ)⁻¹ < 1)
  set n := Nat.find hex with hn
  have hspec : radius n < z.im := Nat.find_spec hex
  have him : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)
  have hn6 : m + 6 ≤ n := by
    by_contra h
    push Not at h
    have : radius (m + 5) ≤ radius n := AreaExist.aradius_anti (by omega)
    linarith
  obtain ⟨i, hi⟩ : ∃ i, n = m + 6 + i := ⟨n - (m + 6), by omega⟩
  have hmin : ¬ radius (n - 1) < z.im := Nat.find_min hex (by omega)
  have hup : z.im ≤ 2 * radius n := by
    have h1 : radius n = radius (n - 1) / 2 := by
      rw [← BdryExist.radius_succ, Nat.sub_add_cancel (by omega)]
    linarith [not_lt.1 hmin]
  have hr := radius_pos n
  set j := ⌊z.re / radius n⌋ with hj
  have hj1' : (j : ℝ) * radius n ≤ z.re := by rw [← le_div_iff₀ hr]; exact Int.floor_le _
  have hj2' : z.re < (j + 1) * radius n := by rw [← div_lt_iff₀ hr]; exact Int.lt_floor_add_one _
  have hre : |z.re| < radius (m + 5) := lt_of_le_of_lt (Complex.abs_re_le_norm z) hza
  have hsh := radius_shift m i
  rw [← hi] at hsh
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨j, ?_, ?_⟩⟩
  · rw [jSet, Finset.mem_Icc]
    have hre' := abs_lt.1 hre
    have e1 : (j : ℝ) < 2 ^ (i + 1) + 1 := by
      have h : (j : ℝ) * radius n < 2 ^ (i + 1) * radius n := by linarith
      have := lt_of_mul_lt_mul_right h hr.le
      linarith
    have e2 : -((2 : ℝ) ^ (i + 1) + 1) < j := by
      have h : -(2 ^ (i + 1)) * radius n < (j + 1) * radius n := by linarith
      have := lt_of_mul_lt_mul_right h hr.le
      linarith
    constructor
    · have : (((-((2 : ℤ) ^ (i + 1) + 1)) : ℤ) : ℝ) < j := by push_cast; linarith
      exact_mod_cast this.le
    · have : (j : ℝ) ≤ (((2 : ℤ) ^ (i + 1) + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · rw [← hi]
    refine ⟨?_, by linarith, by linarith⟩
    rw [abs_lt]; constructor <;> linarith

/-- Outer admissibility (centre `0`, radius `δ = 2^{-m}`) of the box `(m+6+i, j)` at level `k`. -/
theorem adm_outer {m i : ℕ} {j : ℤ} (hj : j ∈ jSet i) {k : ℕ} (hk : m + 7 + i ≤ k) :
    Adm 0 (radius m) (radius (m + 6 + i) / 2) k (boxK (m + 6 + i) j) := by
  have hk' : radius k ≤ radius (m + 6 + i) / 2 := by
    rw [← BdryExist.radius_succ]; exact AreaExist.aradius_anti (by omega)
  have hkm : radius k ≤ radius m / 2 := by
    rw [← BdryExist.radius_succ]; exact AreaExist.aradius_anti (by omega)
  have hm := radius_pos m
  refine ⟨hk', fun z hz => ⟨hz.2.1, ?_⟩⟩
  simp only [Complex.ofReal_zero, sub_zero]
  have := (box_spec hj).2 z hz
  linarith

/-! ### The decomposition -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Rescaled inner mass of the box `(m+6+i, j)` (a function of the inner field at `(0, 2^{-m})`). -/
def Mb (γ : ℝ) (m i : ℕ) (j : ℤ) (y : FieldSample) : ℝ≥0∞ :=
  liminf (fun k => massFunC γ (boxK (m + 6 + i) j) (radius m) k y) atTop

/-- Sum of the box terms. -/
def Sf (γ : ℝ) (m : ℕ) (y : FieldSample) : ℝ≥0∞ := ∑' i, ∑ j ∈ jSet i, Mb γ m i j y

theorem measurable_Mb (γ : ℝ) (m i : ℕ) (j : ℤ) : Measurable (Mb γ m i j) :=
  Measurable.liminf fun k => measurable_massFunC γ _ _ k

theorem measurable_Sf (γ : ℝ) (m : ℕ) : Measurable (Sf γ m) :=
  Measurable.tsum fun i => Finset.measurable_sum _ fun j _ => measurable_Mb γ m i j

/-- The outer lognormal factor `e^{γ Z(fc(0,δ))} δ^{γ²/2}`, `δ = 2^{-m}`, `Z = aZ X 2`. -/
def Af (X : Ω → FieldSample) (γ : ℝ) (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (exp (γ * FracMom.omegaAvg X 2 0 (radius m) ω) * radius m ^ (γ ^ 2 / 2))

/-- **Pathwise bound** `μ_Z(B(0,2^{-m-5}) ∩ ℍ) ≤ A_m S_m`, almost surely. -/
theorem ae_qAreaMeasure_ball_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (m : ℕ) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (AreaExist.aZ X 2 ω) (Metric.ball 0 (radius (m + 5)) ∩ H) ≤
      Af X γ m ω * Sf γ m (innerSampleC X 0 (radius m) ω) := by
  have hδ := radius_pos m
  have hdec : ∀ᵐ ω ∂P, ∀ i : ℕ, ∀ j : ℤ, ∀ k : ℕ,
      Adm 0 (radius m) (radius (m + 6 + i) / 2) k (boxK (m + 6 + i) j) →
      areaApprox γ (AreaExist.aZ X 2 ω) k (boxK (m + 6 + i) j) =
        Af X γ m ω *
          massFunC γ (boxK (m + 6 + i) j) (radius m) k (innerSampleC X 0 (radius m) ω) := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    exact ae_areaApprox_eq_omega_mul hX γ 2 (t := 0) (d := radius (m + 6 + i) / 2) hδ
      (isClosed_boxK _ j).measurableSet
  filter_upwards [hdec, AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX (P := P) hγ hγ2 2]
    with ω hd hv
  set μ := qAreaMeasure γ (AreaExist.aZ X 2 ω)
  have hbox : ∀ i, ∀ j ∈ jSet i, μ (boxU (m + 6 + i) j) ≤
      Af X γ m ω * Mb γ m i j (innerSampleC X 0 (radius m) ω) := by
    intro i j hj
    have h1 := rpow_le_liminf_of_isVagueLimitOn hv (isOpen_boxU (m + 6 + i) j)
      (isCompact_boxK (m + 6 + i) j) (boxU_subset_boxK (m + 6 + i) j)
      (boxK_subset_H (m + 6 + i) j) one_pos
    simp only [ENNReal.rpow_one] at h1
    refine h1.trans (le_of_eq ?_)
    rw [Mb, ← ENNReal.liminf_const_mul_of_ne_top (show Af X γ m ω ≠ ⊤ from ENNReal.ofReal_ne_top)]
    exact liminf_congr (eventually_atTop.2 ⟨m + 7 + i, fun k hk => hd i j k (adm_outer hj hk)⟩)
  calc μ (Metric.ball 0 (radius (m + 5)) ∩ H)
      ≤ μ (⋃ i, ⋃ j ∈ jSet i, boxU (m + 6 + i) j) := measure_mono (ball_subset_boxes m)
    _ ≤ ∑' i, ∑ j ∈ jSet i, μ (boxU (m + 6 + i) j) :=
        (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun i => measure_biUnion_finset_le _ _)
    _ ≤ ∑' i, ∑ j ∈ jSet i, Af X γ m ω * Mb γ m i j (innerSampleC X 0 (radius m) ω) :=
        ENNReal.tsum_le_tsum fun i => Finset.sum_le_sum fun j hj => hbox i j hj
    _ = _ := by rw [Sf, ← ENNReal.tsum_mul_left]; simp_rw [Finset.mul_sum]

theorem omegaAvg_self (X : Ω → FieldSample) (δ : ℝ) (ω : Ω) :
    FracMom.omegaAvg X δ 0 δ ω = 0 := by
  simp [FracMom.omegaAvg, GaussTK.fcPairVal]

/-- **Moment of one box term**, through the box's own lognormal factor. -/
theorem lintegral_Mb_rpow_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {m i : ℕ} {j : ℤ} (hj : j ∈ jSet i) :
    ENNReal.ofReal (radius m ^ (γ ^ 2 / 2)) ^ p *
        ∫⁻ ω, Mb γ m i j (innerSampleC X 0 (radius m) ω) ^ p ∂P ≤
      fracBoundC γ (radius m) (5 * radius (m + 6 + i)) (radius (m + 6 + i) / 2) p
        (boxK (m + 6 + i) j) := by
  have hδ : 0 < radius m := radius_pos m
  have hbs := box_spec (m := m) hj
  have hdec := ae_areaApprox_eq_omega_mul hX γ (radius m) (P := P) (t := 0)
    (d := radius (m + 6 + i) / 2) hδ (isClosed_boxK (m + 6 + i) j).measurableSet
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
  refine le_trans (lintegral_mono_ae ?_) (lintegral_liminf_areaApprox_rpow_le hX γ
    (R := radius m) (t := j * radius (m + 6 + i)) (δ := 5 * radius (m + 6 + i))
    (d := radius (m + 6 + i) / 2) (mul_pos (by norm_num) (radius_pos _))
    (half_pos (radius_pos _)) hbs.1 hp0 hp1
    (isClosed_boxK _ j).measurableSet (boxK_spec _ j))
  filter_upwards [hdec] with ω hω
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, Mb,
    ← ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  have heq : liminf (fun k => ENNReal.ofReal (radius m ^ (γ ^ 2 / 2)) *
        massFunC γ (boxK (m + 6 + i) j) (radius m) k (innerSampleC X 0 (radius m) ω)) atTop =
      liminf (fun k => areaApprox γ (AreaExist.aZ X (radius m) ω) k (boxK (m + 6 + i) j))
        atTop := by
    refine liminf_congr (eventually_atTop.2 ⟨m + 7 + i, fun k hk => ?_⟩)
    rw [hω k (adm_outer hj hk), omegaAvg_self, mul_zero, exp_zero, one_mul]
  rw [heq]
  exact le_of_eq ((ENNReal.monotone_rpow_of_nonneg hp0.le).map_liminf_of_continuousAt _
    ENNReal.continuous_rpow_const.continuousAt)

end WedgeFinZero
end QuantumZipper
