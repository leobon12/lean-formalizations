import GaussianLQG.Medians.LawM.Basic
import GaussianLQG.Core.Interfaces
import GaussianLQG.Energy.Segments

/-!
# The law of `M` (blueprint Lemma `lem:law-M`, source Lemma 6.1)

For a `Setup` `S`, with `H(s,t) = (h, λ_{is,1+it})`, `M = inf_{y ∈ 𝔻} H(y,y)` and `q = med M`
(blueprint Definition `def:HMq`):

* (a) `measure_M_mem_Ioo_pos`: `P[a < M < b] > 0` for all `a < b`; consequently
  `isMedian_q_and_unique`: `q` is a median of `M` and it is the only one;
* (b) `half_lt_measure_M_neg`: `P[M < 0] > 1/2`; consequently `q_neg`: `q < 0`;
* `lawM`: the interface proposition `Setup.LawM` (blueprint Lemma `lem:law-M`);
* `measurable_M_of_measurable_H`: `M` is measurable.

The inputs from blueprint Lemma `lem:field` and Lemma `lem:H-continuity` enter as the hypotheses

* `hshift`: for regular `μ`, a.s. `(h, μ)(ω + v) = (h, μ)(ω) + ∫ f_v dμ` for every `v ∈ c₀₀`
  (Lemma `lem:field`(a));
* `hqi`: the law of `ω + v` is absolutely continuous with respect to `P` (Lemma `lem:field`(c));
* `hfin`: a.s. `{H(y,y) : y ∈ 𝔻}` is bounded below, i.e. `M ∈ ℝ` (Lemma `lem:H-continuity`(c));
* `hmeas`: each `H(s,t)` is measurable;
* `hlaw`: `H(0,0) ∼ 𝒩(0, 3/2)` (Lemma `lem:field`(b) with Lemma `lem:segments`(a)).

The proof follows the blueprint: finite-dimensional Cameron–Martin shifts in a direction `v`
whose pairings with all the segments `λ_y` are positive, and Fubini over the shift parameter `t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped ENNReal

namespace GaussianLQG

namespace LawMAux

variable (S : Setup)

/-- Lemma `lem:field`(a) for the segment measures: a.s., for every finitely supported `v`,
`H(s,t)(ω + v) = H(s,t)(ω) + ∫ f_v dλ_{is,1+it}`. -/
theorem ae_H_shift
    (hshift : ∀ μ : Measure ℂ, IsRegular μ → ∀ᵐ ω ∂stdP, ∀ v : ℕ →₀ ℝ,
      pairing S.e μ (shiftBy ω v) = pairing S.e μ ω + ∫ z, frameFun S.e v z ∂μ)
    (s t : ℝ) :
    ∀ᵐ ω ∂stdP, ∀ v : ℕ →₀ ℝ, S.H s t (shiftBy ω v) =
      S.H s t ω + ∫ z, frameFun S.e v z ∂(segMeasure ((s : ℂ) * I) (1 + (t : ℂ) * I)) :=
  hshift _ (isRegular_segMeasure (sI_ne_one_add_tI s t))

/-- **The shift direction of Lemma `lem:law-M` (a).** There are a finitely supported `v` and
constants `0 < m ≤ L` with `m ≤ ∫ f_v dλ_y ≤ L` for every `y ∈ [0,1]`, where
`λ_y = λ_{iy,1+iy}`. Here `v` truncates the coefficient sequence `u = (∫ e_j dμ₀)_j` of the disc
measure `μ₀` of Lemma `lem:segments`(e): `⟨u, a(y)⟩ = ℰ(μ₀, λ_y) ≥ c_*` and
`‖a(y)‖² = ℰ(λ_y, λ_y) ≤ 3/2 + log 2` by Lemma `lem:segments`(d), (e) and the polarized frame
identity. -/
theorem exists_shift_direction : ∃ v : ℕ →₀ ℝ, ∃ m L : ℝ, 0 < m ∧ ∀ y ∈ Icc (0 : ℝ) 1,
    m ≤ ∫ z, frameFun S.e v z ∂(segMeasure ((y : ℂ) * I) (1 + (y : ℂ) * I)) ∧
      ∫ z, frameFun S.e v z ∂(segMeasure ((y : ℂ) * I) (1 + (y : ℂ) * I)) ≤ L := by
  have hu : HasSum (fun j => (∫ z, S.e j z ∂muZero) * ∫ z, S.e j z ∂muZero)
      (energy muZero muZero) := S.frame.2.2 _ _ isRegular_muZero isRegular_muZero
  have hτ : 0 < 3 / 2 + Real.log 2 := by
    have := Real.log_pos one_lt_two
    linarith
  obtain ⟨n, hn⟩ := exists_trunc_pairing_bounds hu cStar_pos hτ
  refine ⟨truncFs (fun j => ∫ z, S.e j z ∂muZero) n, -Real.log (1 / 4 + √2 / 2) / 2,
    1 + energy muZero muZero * (3 / 2 + Real.log 2), half_pos cStar_pos, fun y hy => ?_⟩
  have hlam : IsRegular (segMeasure ((y : ℂ) * I) (1 + (y : ℂ) * I)) :=
    isRegular_segMeasure (sI_ne_one_add_tI y y)
  rw [integral_frameFun_truncFs S.frame]
  exact hn _ _ _ (S.frame.2.2 _ _ hlam hlam) (energy_segMeasure_sI_le hy hy)
    (S.frame.2.2 _ _ isRegular_muZero hlam) (neg_log_le_energy_muZero_segMeasure hy)

end LawMAux

namespace Setup

variable (S : Setup)

/-- `M` is measurable: a countable infimum of the measurable `H(y,y)`. -/
theorem measurable_M_of_measurable_H (hmeas : ∀ s t : ℝ, Measurable (S.H s t)) :
    Measurable S.M :=
  Measurable.iInf fun y : dyadicUnit => hmeas y y

/-- **Blueprint Lemma `lem:law-M` (a).** `P[a < M < b] > 0` for all `a < b`. -/
theorem measure_M_mem_Ioo_pos
    (hshift : ∀ μ : Measure ℂ, IsRegular μ → ∀ᵐ ω ∂stdP, ∀ v : ℕ →₀ ℝ,
      pairing S.e μ (shiftBy ω v) = pairing S.e μ ω + ∫ z, frameFun S.e v z ∂μ)
    (hqi : ∀ v : ℕ →₀ ℝ, (stdP.map fun ω => shiftBy ω v) ≪ stdP)
    (hfin : ∀ᵐ ω ∂stdP, BddBelow (Set.range fun y : Setup.dyadicUnit => S.H y y ω))
    (hmeas : ∀ s t : ℝ, Measurable (S.H s t)) :
    ∀ a b : ℝ, a < b → 0 < stdP {ω | a < S.M ω ∧ S.M ω < b} := by
  intro a b hab
  obtain ⟨v, m, L, hm, hvc⟩ := LawMAux.exists_shift_direction S
  have hM := S.measurable_M_of_measurable_H hmeas
  have hshiftH : ∀ᵐ ω ∂stdP, ∀ y : dyadicUnit, ∀ w : ℕ →₀ ℝ, S.H y y (shiftBy ω w) =
      S.H y y ω + ∫ z, frameFun S.e w z ∂(segMeasure (((y : ℝ) : ℂ) * I) (1 + ((y : ℝ) : ℂ) * I)) :=
    ae_all_iff.2 fun y => LawMAux.ae_H_shift S hshift y y
  refine LawMAux.measure_pos_of_ae_volume_shift_pos (B := {ω | a < S.M ω ∧ S.M ω < b})
    ((measurableSet_lt measurable_const hM).inter (measurableSet_lt hM measurable_const)) v
    (fun t => hqi (t • v)) ?_
  filter_upwards [hshiftH, hfin] with ω hω hbdd
  -- the slopes `c(y) = ∫ f_v dλ_y`
  set c : dyadicUnit → ℝ := fun y =>
    ∫ z, frameFun S.e v z ∂(segMeasure (((y : ℝ) : ℂ) * I) (1 + ((y : ℝ) : ℂ) * I))
  -- along the shift, `M(ω + t v) = inf_y (H(y,y)(ω) + t c(y))`
  have key : ∀ t : ℝ,
      S.M (shiftBy ω (t • v)) = LawMAux.infAffine (fun y : dyadicUnit => S.H y y ω) c t := by
    intro t
    show ⨅ y : dyadicUnit, S.H y y (shiftBy ω (t • v)) = ⨅ y : dyadicUnit, (S.H y y ω + t * c y)
    congr 1
    funext y
    rw [hω y (t • v), LawMAux.integral_frameFun_smul]
  simp only [key]
  exact LawMAux.volume_pos_infAffine hbdd (fun y => hvc y (LawMAux.dyadicUnit_subset_Icc y.2))
    hm hab

/-- **Blueprint Lemma `lem:law-M` (a), consequence.** `q = med M` is a median of `M`, and it is
the only median. -/
theorem isMedian_q_and_unique
    (hshift : ∀ μ : Measure ℂ, IsRegular μ → ∀ᵐ ω ∂stdP, ∀ v : ℕ →₀ ℝ,
      pairing S.e μ (shiftBy ω v) = pairing S.e μ ω + ∫ z, frameFun S.e v z ∂μ)
    (hqi : ∀ v : ℕ →₀ ℝ, (stdP.map fun ω => shiftBy ω v) ≪ stdP)
    (hfin : ∀ᵐ ω ∂stdP, BddBelow (Set.range fun y : Setup.dyadicUnit => S.H y y ω))
    (hmeas : ∀ s t : ℝ, Measurable (S.H s t)) :
    LQGMetric.IsMedian (stdP.map S.M) S.q ∧
      ∀ m, LQGMetric.IsMedian (stdP.map S.M) m → m = S.q := by
  have hM := S.measurable_M_of_measurable_H hmeas
  have hq : S.q = LQGMetric.lowerMedianLaw (stdP.map S.M) :=
    LQGMetric.lowerMedian_eq_lowerMedianLaw hM.aemeasurable
  have hU : LQGMetric.lowerMedianLaw (stdP.map S.M) =
      LQGMetric.upperMedianLaw (stdP.map S.M) :=
    LQGMetric.lowerMedianLaw_eq_upperMedianLaw_of_noGap fun a b hab _ => by
      rw [Measure.map_apply hM measurableSet_Ioo]
      exact S.measure_M_mem_Ioo_pos hshift hqi hfin hmeas a b hab
  rw [hq]
  exact ⟨LQGMetric.isMedian_lowerMedianLaw, fun m hm =>
    LQGMetric.IsMedian.eq_of_unique hU hm LQGMetric.isMedian_lowerMedianLaw⟩

/-- **Blueprint Lemma `lem:law-M` (b).** `P[M < 0] > 1/2`. -/
theorem half_lt_measure_M_neg
    (hshift : ∀ μ : Measure ℂ, IsRegular μ → ∀ᵐ ω ∂stdP, ∀ v : ℕ →₀ ℝ,
      pairing S.e μ (shiftBy ω v) = pairing S.e μ ω + ∫ z, frameFun S.e v z ∂μ)
    (hqi : ∀ v : ℕ →₀ ℝ, (stdP.map fun ω => shiftBy ω v) ≪ stdP)
    (hfin : ∀ᵐ ω ∂stdP, BddBelow (Set.range fun y : Setup.dyadicUnit => S.H y y ω))
    (hmeas : ∀ s t : ℝ, Measurable (S.H s t))
    (hlaw : stdP.map (S.H 0 0) = ProbabilityTheory.gaussianReal 0 (3 / 2 : NNReal)) :
    (1 / 2 : ℝ≥0∞) < stdP {ω | S.M ω < 0} := by
  -- the segments `λ₀ = λ_{0,1}` and `λ₁ = λ_{i,1+i}`
  have e0 : segMeasure (((0 : ℝ) : ℂ) * I) (1 + ((0 : ℝ) : ℂ) * I) = segMeasure 0 1 := by
    simp only [ofReal_zero, zero_mul, add_zero]
  have e1 : segMeasure (((1 : ℝ) : ℂ) * I) (1 + ((1 : ℝ) : ℂ) * I) = segMeasure I (1 + I) := by
    simp only [ofReal_one, one_mul]
  have r0 : IsRegular (segMeasure 0 1) := isRegular_segMeasure zero_ne_one_complex
  have r1 : IsRegular (segMeasure I (1 + I)) := isRegular_segMeasure I_ne_one_add_I
  -- the coefficient sequences `α = a(0)`, `β = a(1)` and their Gram matrix
  set α : ℕ → ℝ := fun j => ∫ z, S.e j z ∂(segMeasure 0 1)
  set β : ℕ → ℝ := fun j => ∫ z, S.e j z ∂(segMeasure I (1 + I))
  set E00 := energy (segMeasure 0 1) (segMeasure 0 1)
  set E01 := energy (segMeasure 0 1) (segMeasure I (1 + I))
  set E11 := energy (segMeasure I (1 + I)) (segMeasure I (1 + I))
  have hαα : HasSum (fun j => α j * α j) E00 := S.frame.2.2 _ _ r0 r0
  have hαβ : HasSum (fun j => α j * β j) E01 := S.frame.2.2 _ _ r0 r1
  have hββ : HasSum (fun j => β j * β j) E11 := S.frame.2.2 _ _ r1 r1
  obtain ⟨hdet, hdet0⟩ := segMeasure_gram_det_pos
  have hD : 0 < E00 * E11 - E01 ^ 2 := lt_of_lt_of_le hdet0 hdet
  -- `u = x α + y β` solves `⟨u, α⟩ = 1`, `⟨u, β⟩ = -1`
  set x : ℝ := (E11 + E01) / (E00 * E11 - E01 ^ 2) with hx_def
  set y : ℝ := -(E00 + E01) / (E00 * E11 - E01 ^ 2) with hy_def
  have hx1 : x * E00 + y * E01 = 1 := by
    rw [hx_def, hy_def, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hD.ne']
    ring
  have hx2 : x * E01 + y * E11 = -1 := by
    rw [hx_def, hy_def, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hD.ne']
    ring
  set w : ℕ → ℝ := fun j => x * α j + y * β j with hw_def
  have hwα : Tendsto (fun N => ∑ j ∈ Finset.range N, w j * α j) atTop (𝓝 1) := by
    rw [← hx1]
    refine ((hαα.tendsto_sum_nat.const_mul x).add
      (hαβ.tendsto_sum_nat.const_mul y)).congr fun N => ?_
    simp only [hw_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hwβ : Tendsto (fun N => ∑ j ∈ Finset.range N, w j * β j) atTop (𝓝 (-1)) := by
    rw [← hx2]
    refine ((hαβ.tendsto_sum_nat.const_mul x).add
      (hββ.tendsto_sum_nat.const_mul y)).congr fun N => ?_
    simp only [hw_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- a truncation `v` of `u` with `⟨v, α⟩ > 1/2` and `⟨v, β⟩ < -1/2`
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, 1 / 2 < ∑ j ∈ Finset.range n, w j * α j ∧
      ∑ j ∈ Finset.range n, w j * β j < -1 / 2 :=
    ((hwα.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)).and
      (hwβ.eventually_lt_const (by norm_num : (-1 : ℝ) < -1 / 2))).exists
  set v : ℕ →₀ ℝ := LawMAux.truncFs w n
  have hv0 : ∫ z, frameFun S.e v z ∂(segMeasure 0 1) = ∑ j ∈ Finset.range n, w j * α j :=
    LawMAux.integral_frameFun_truncFs S.frame w n _
  have hv1 : ∫ z, frameFun S.e v z ∂(segMeasure I (1 + I)) =
      ∑ j ∈ Finset.range n, w j * β j :=
    LawMAux.integral_frameFun_truncFs S.frame w n _
  -- the event `𝖡 = {H(0,0) > 0 > H(1,1)}` has positive probability
  set B : Set Coord := {ω | 0 < S.H 0 0 ω ∧ S.H 1 1 ω < 0}
  have hBm : MeasurableSet B :=
    (measurableSet_lt measurable_const (hmeas 0 0)).inter
      (measurableSet_lt (hmeas 1 1) measurable_const)
  have hBpos : 0 < stdP B := by
    refine LawMAux.measure_pos_of_ae_volume_shift_pos hBm v (fun t => hqi (t • v)) ?_
    filter_upwards [LawMAux.ae_H_shift S hshift 0 0, LawMAux.ae_H_shift S hshift 1 1]
      with ω h0 h1
    rw [e0] at h0
    rw [e1] at h1
    have hsub : Ioi (2 * (|S.H 0 0 ω| + |S.H 1 1 ω|)) ⊆ {t : ℝ | shiftBy ω (t • v) ∈ B} := by
      intro t ht
      rw [mem_Ioi] at ht
      have hs0 := h0 (t • v)
      have hs1 := h1 (t • v)
      rw [LawMAux.integral_frameFun_smul, hv0] at hs0
      rw [LawMAux.integral_frameFun_smul, hv1] at hs1
      show 0 < S.H 0 0 (shiftBy ω (t • v)) ∧ S.H 1 1 (shiftBy ω (t • v)) < 0
      rw [hs0, hs1]
      have a0 := neg_abs_le (S.H 0 0 ω)
      have a1 := le_abs_self (S.H 1 1 ω)
      have b0 := abs_nonneg (S.H 0 0 ω)
      have b1 := abs_nonneg (S.H 1 1 ω)
      have ht0 : 0 < t := by linarith
      have k0 : t / 2 < t * ∑ j ∈ Finset.range n, w j * α j := by nlinarith
      have k1 : t * ∑ j ∈ Finset.range n, w j * β j < -(t / 2) := by nlinarith
      constructor <;> linarith
    calc (0 : ℝ≥0∞) < ∞ := ENNReal.zero_lt_top
      _ = volume (Ioi (2 * (|S.H 0 0 ω| + |S.H 1 1 ω|))) := Real.volume_Ioi.symm
      _ ≤ volume {t : ℝ | shiftBy ω (t • v) ∈ B} := measure_mono hsub
  -- `M ≤ H(0,0)` and `M ≤ H(1,1)` a.s., since `0, 1 ∈ 𝔻`
  have hle : ∀ᵐ ω ∂stdP, S.M ω ≤ S.H 0 0 ω ∧ S.M ω ≤ S.H 1 1 ω := by
    filter_upwards [hfin] with ω hω
    exact ⟨ciInf_le hω ⟨0, LawMAux.zero_mem_dyadicUnit⟩,
      ciInf_le hω ⟨1, LawMAux.one_mem_dyadicUnit⟩⟩
  -- `P[H(0,0) < 0] = 1/2`
  have hhalf : stdP {ω | S.H 0 0 ω < 0} = 2⁻¹ := by
    have h := Measure.map_apply (μ := stdP) (hmeas 0 0) (measurableSet_Iio (a := (0 : ℝ)))
    rw [hlaw, LawMAux.gaussianReal_Iio_zero (by norm_num)] at h
    exact h.symm
  have hdisj : Disjoint {ω | S.H 0 0 ω < 0} B := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    exact absurd h2.1 (not_lt.2 h1.le)
  have hsub : {ω | S.H 0 0 ω < 0} ∪ B ≤ᵐ[stdP] {ω | S.M ω < 0} := by
    filter_upwards [hle] with ω hω hmem
    rcases hmem with h | h
    · exact lt_of_le_of_lt hω.1 h
    · exact lt_of_le_of_lt hω.2 h.2
  calc (1 / 2 : ℝ≥0∞) = 2⁻¹ := one_div 2
    _ < 2⁻¹ + stdP B := ENNReal.lt_add_right (ENNReal.inv_ne_top.2 two_ne_zero) hBpos.ne'
    _ = stdP ({ω | S.H 0 0 ω < 0} ∪ B) := by rw [measure_union hdisj hBm, hhalf]
    _ ≤ stdP {ω | S.M ω < 0} := measure_mono_ae hsub

/-- **Blueprint Lemma `lem:law-M` (b), consequence.** `q < 0`. -/
theorem q_neg
    (hshift : ∀ μ : Measure ℂ, IsRegular μ → ∀ᵐ ω ∂stdP, ∀ v : ℕ →₀ ℝ,
      pairing S.e μ (shiftBy ω v) = pairing S.e μ ω + ∫ z, frameFun S.e v z ∂μ)
    (hqi : ∀ v : ℕ →₀ ℝ, (stdP.map fun ω => shiftBy ω v) ≪ stdP)
    (hfin : ∀ᵐ ω ∂stdP, BddBelow (Set.range fun y : Setup.dyadicUnit => S.H y y ω))
    (hmeas : ∀ s t : ℝ, Measurable (S.H s t))
    (hlaw : stdP.map (S.H 0 0) = ProbabilityTheory.gaussianReal 0 (3 / 2 : NNReal)) :
    S.q < 0 := by
  have hM := S.measurable_M_of_measurable_H hmeas
  have hmed : LQGMetric.IsMedian (stdP.map S.M) S.q := by
    rw [show S.q = LQGMetric.lowerMedianLaw (stdP.map S.M) from
      LQGMetric.lowerMedian_eq_lowerMedianLaw hM.aemeasurable]
    exact LQGMetric.isMedian_lowerMedianLaw
  have h2 : (2 : ℝ≥0∞)⁻¹ ≤ stdP {ω | S.q ≤ S.M ω} :=
    ((LQGMetric.isMedian_map_iff hM.aemeasurable).1 hmed).2
  have hlt := S.half_lt_measure_M_neg hshift hqi hfin hmeas hlaw
  rw [one_div] at hlt
  by_contra hq
  push Not at hq
  have h3 : stdP {ω | S.q ≤ S.M ω} ≤ stdP {ω | S.M ω < 0}ᶜ := by
    refine measure_mono fun ω hω => ?_
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
    exact hq.trans hω
  have hsum : stdP {ω | S.M ω < 0} + stdP {ω | S.M ω < 0}ᶜ = 1 := by
    rw [measure_add_measure_compl (measurableSet_lt hM measurable_const), measure_univ]
  have h4 := ENNReal.add_lt_add_of_lt_of_le (ENNReal.inv_ne_top.2 two_ne_zero) hlt (h2.trans h3)
  rw [ENNReal.inv_two_add_inv_two, hsum] at h4
  exact lt_irrefl _ h4

/-- **Blueprint Lemma `lem:law-M`** (the interface proposition `Setup.LawM`): `q` is the unique
median of `M`, and `q < 0`. -/
theorem lawM
    (hshift : ∀ μ : Measure ℂ, IsRegular μ → ∀ᵐ ω ∂stdP, ∀ v : ℕ →₀ ℝ,
      pairing S.e μ (shiftBy ω v) = pairing S.e μ ω + ∫ z, frameFun S.e v z ∂μ)
    (hqi : ∀ v : ℕ →₀ ℝ, (stdP.map fun ω => shiftBy ω v) ≪ stdP)
    (hfin : ∀ᵐ ω ∂stdP, BddBelow (Set.range fun y : Setup.dyadicUnit => S.H y y ω))
    (hmeas : ∀ s t : ℝ, Measurable (S.H s t))
    (hlaw : stdP.map (S.H 0 0) = ProbabilityTheory.gaussianReal 0 (3 / 2 : NNReal)) :
    S.LawM := by
  unfold Setup.LawM
  exact ⟨S.isMedian_q_and_unique hshift hqi hfin hmeas,
    S.q_neg hshift hqi hfin hmeas hlaw⟩

end Setup

end GaussianLQG
