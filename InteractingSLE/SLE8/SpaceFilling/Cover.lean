import InteractingSLE.SLE8.SpaceFilling.CoverEnergy
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# κ = 8 space filling, Lemma 4: the deterministic dyadic cover

Source: the user's note *Space filling of a continuous SLE₈ trace*
(`source/external/SLE8SF/sle8_space_filling_formalization.pdf`, §3, Lemma 4 and its proof, p. 4).

**Lemma 4.** Let `f : ℍ → ℂ` be injective and holomorphic, with a continuous extension to `ℍ̄`.
Fix an integer `L ≥ 1` and `h > 0`. If `E_{L,h}(f) < ∞` (3.3), then
`H^{14/9}(f([-L, L]) ∩ {Im w ≥ 2h}) = 0`.

Here `f : ℂ → ℂ` is differentiable and injective on `ℍ` and continuous on `ℍ̄` (its values on `ℍ̄`
are the extension); `E_{L,h}(f) = dyEnergy f L h` uses `f` and `f'` only at the Whitney points.

## Proof (the note's, p. 4)

* **Uniform continuity** (`exists_forall_le_im_of_le_im`): for `n` large, if `f(I)`, `I ∈ D_n(L)`,
  meets `{Im w ≥ 2h}` then `Im f(z_J) ≥ h` for every descendant `J ⊂ I`, so every descendant
  indicator in `a_J` equals `1`.
* **Telescoping** (`edist_le_of_mem_dyIcc`): along the nested chain of dyadic intervals through
  `x ∈ I`, (3.4) and boundary continuity give `|f(x) - f(z_I)| ≤ C Σ_{k ≥ 0} b_k`, with
  `b_k = (Σ_{J ⊂ I, J ∈ D_{n+k}} a_J^p)^{1/p}` (`dyDescNorm`), a bound for every chain term.
* **Hölder** (3.5) (`tsum_rpow_le_holder`): `(diam f(I))^p ≤ C_p Σ_k 2^{k/18} Σ_{J ⊂ I} a_J^p`
  (`ediam_image_dyIcc_rpow_le`).
* **Summation** (`sum_tsum_dyDesc_le`): every descendant has exactly one level-`n` ancestor, so
  `Σ_{I relevant} (diam f(I))^p ≤ C_p 2^{-n/18} E_{L,h}(f) → 0` (3.6). These covers have
  vanishing maximal diameter and total `p`-content, and Mathlib's
  `Measure.hausdorffMeasure_le_liminf_sum` gives the claim.

## Main results

* `hausdorffMeasure_image_Icc_inter_eq_zero` — **Lemma 4**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.SLE8.SpaceFilling

open QuantumZipper

variable {f : ℂ → ℂ} {h : ℝ} {L n : ℕ} {j : ℤ}

/-! ## Descendant norms -/

/-- `b_k = (Σ_{J ⊂ I_{n,j}, J ∈ D_{n+k}(L)} a_J^{14/9})^{9/14}`. -/
def dyDescNorm (f : ℂ → ℂ) (h : ℝ) (L n k : ℕ) (j : ℤ) : ℝ≥0∞ :=
  (∑ j' ∈ dyDesc L n k j, ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ))) ^
    (14 / 9 : ℝ)⁻¹

theorem dyDescNorm_rpow (f : ℂ → ℂ) (h : ℝ) (L n k : ℕ) (j : ℤ) :
    dyDescNorm f h L n k j ^ (14 / 9 : ℝ) =
      ∑ j' ∈ dyDesc L n k j, ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ)) :=
  ENNReal.rpow_inv_rpow (by norm_num) _

theorem ofReal_dyWeight_le_dyDescNorm {k : ℕ} {j' : ℤ} (hj' : j' ∈ dyDesc L n k j) :
    ENNReal.ofReal (dyWeight f h (n + k) j') ≤ dyDescNorm f h L n k j := by
  calc ENNReal.ofReal (dyWeight f h (n + k) j')
      = (ENNReal.ofReal (dyWeight f h (n + k) j') ^ (14 / 9 : ℝ)) ^ (14 / 9 : ℝ)⁻¹ :=
        (ENNReal.rpow_rpow_inv (by norm_num) _).symm
    _ ≤ dyDescNorm f h L n k j := by
        unfold dyDescNorm
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [ENNReal.ofReal_rpow_of_nonneg (dyWeight_nonneg f h _ _) (by norm_num)]
        exact Finset.single_le_sum
          (f := fun j' => ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ)))
          (fun _ _ => bot_le) hj'

/-! ## Telescoping along the nested chain -/

/-- The telescoping bound along the chain through `x ∈ [j 2^{-n}, (j+1) 2^{-n})`, when every
descendant indicator equals `1`. -/
theorem edist_le_of_mem_Ico (hfd : DifferentiableOn ℂ f H) (hfi : InjOn f H)
    (hfc : ContinuousOn f Hbar) (hj : j ∈ dyIdx L n)
    (hgood : ∀ k, ∀ j' ∈ dyDesc L n k j, h ≤ (f (dyPt (n + k) j')).im) {x : ℝ}
    (hx : x ∈ Ico ((j : ℝ) / 2 ^ n) (((j : ℝ) + 1) / 2 ^ n)) :
    edist (f (dyPt n j)) (f x) ≤
      ENNReal.ofReal koebeChildConst * ∑' k, dyDescNorm f h L n k j := by
  let c : ℕ → ℂ := fun k => dyPt (n + k) ⌊x * 2 ^ (n + k)⌋
  have hc0 : c 0 = dyPt n j := by
    show dyPt (n + 0) ⌊x * 2 ^ (n + 0)⌋ = dyPt n j
    rw [Nat.add_zero, floor_mul_two_pow_eq hx]
  have hstep : ∀ i, edist (f (c i)) (f (c (i + 1))) ≤
      ENNReal.ofReal koebeChildConst * dyDescNorm f h L n i j := by
    intro i
    have hfl : ⌊x * 2 ^ (n + i + 1)⌋ / 2 = ⌊x * 2 ^ (n + i)⌋ :=
      floor_mul_two_pow_succ_ediv_two x (n + i)
    have hmem := floor_mem_dyDesc hj hx i
    have hle : h ≤ (f (dyPt (n + i) (⌊x * 2 ^ (n + i + 1)⌋ / 2))).im := by
      rw [hfl]; exact hgood i _ hmem
    have h1 := edist_dyPt_succ_le hfd hfi (n + i) ⌊x * 2 ^ (n + i + 1)⌋ hle
    rw [hfl] at h1
    calc edist (f (c i)) (f (c (i + 1)))
        = edist (f (dyPt (n + i) ⌊x * 2 ^ (n + i)⌋))
            (f (dyPt (n + i + 1) ⌊x * 2 ^ (n + i + 1)⌋)) := rfl
      _ ≤ ENNReal.ofReal koebeChildConst * ENNReal.ofReal (dyWeight f h (n + i) ⌊x * 2 ^ (n + i)⌋) :=
          h1
      _ ≤ ENNReal.ofReal koebeChildConst * dyDescNorm f h L n i j :=
          mul_le_mul' le_rfl (ofReal_dyWeight_le_dyDescNorm hmem)
  have hpartial : ∀ K, edist (f (dyPt n j)) (f (c K)) ≤
      ENNReal.ofReal koebeChildConst * ∑' k, dyDescNorm f h L n k j := by
    intro K
    rw [← hc0]
    calc edist (f (c 0)) (f (c K)) ≤ ∑ i ∈ Finset.range K, edist (f (c i)) (f (c (i + 1))) :=
          edist_le_range_sum_edist (fun i => f (c i)) K
      _ ≤ ∑ i ∈ Finset.range K, ENNReal.ofReal koebeChildConst * dyDescNorm f h L n i j :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = ENNReal.ofReal koebeChildConst * ∑ i ∈ Finset.range K, dyDescNorm f h L n i j :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ ENNReal.ofReal koebeChildConst * ∑' k, dyDescNorm f h L n k j :=
          mul_le_mul' le_rfl (ENNReal.sum_le_tsum _)
  -- boundary continuity: `f(z_{n+K}(x)) → f(x)`
  have hxH : (x : ℂ) ∈ Hbar := show 0 ≤ (x : ℂ).im by simp
  have hcx : Tendsto c atTop (𝓝[Hbar] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun K =>
      QuantumZipper.H_subset_Hbar (dyPt_mem_H _ _)⟩
    have h1 := (tendsto_dyPt_floor x).comp (tendsto_add_atTop_nat n)
    refine h1.congr fun K => ?_
    simp only [Function.comp_apply, c, Nat.add_comm K n]
  have hfx : Tendsto (fun K => f (c K)) atTop (𝓝 (f x)) := (hfc _ hxH).tendsto.comp hcx
  exact le_of_tendsto' (tendsto_const_nhds.edist hfx) hpartial

/-- The telescoping bound on the closed interval `I_{n,j}` (by continuity of `f` on `ℝ`). -/
theorem edist_le_of_mem_dyIcc (hfd : DifferentiableOn ℂ f H) (hfi : InjOn f H)
    (hfc : ContinuousOn f Hbar) (hj : j ∈ dyIdx L n)
    (hgood : ∀ k, ∀ j' ∈ dyDesc L n k j, h ≤ (f (dyPt (n + k) j')).im) {x : ℝ}
    (hx : x ∈ dyIcc n j) :
    edist (f (dyPt n j)) (f x) ≤
      ENNReal.ofReal koebeChildConst * ∑' k, dyDescNorm f h L n k j := by
  have hg : Continuous fun x : ℝ => f x :=
    hfc.comp_continuous continuous_ofReal fun x => show 0 ≤ (x : ℂ).im by simp
  have hclosed : IsClosed {x : ℝ | edist (f (dyPt n j)) (f x) ≤
      ENNReal.ofReal koebeChildConst * ∑' k, dyDescNorm f h L n k j} :=
    isClosed_le (continuous_const.edist hg) continuous_const
  have hsub : Ico ((j : ℝ) / 2 ^ n) (((j : ℝ) + 1) / 2 ^ n) ⊆ {x : ℝ | edist (f (dyPt n j)) (f x) ≤
      ENNReal.ofReal koebeChildConst * ∑' k, dyDescNorm f h L n k j} :=
    fun x hx => edist_le_of_mem_Ico hfd hfi hfc hj hgood hx
  have hne : (j : ℝ) / 2 ^ n ≠ ((j : ℝ) + 1) / 2 ^ n := by
    have hn := two_pow_pos_real n
    exact ne_of_lt (div_lt_div_of_pos_right (by linarith) hn)
  have h1 := closure_minimal hsub hclosed
  rw [closure_Ico hne] at h1
  exact h1 hx

/-! ## Diameter bounds -/

/-- `diam f(I) ≤ 2 C Σ_k b_k`. -/
theorem ediam_image_dyIcc_le (hfd : DifferentiableOn ℂ f H) (hfi : InjOn f H)
    (hfc : ContinuousOn f Hbar) (hj : j ∈ dyIdx L n)
    (hgood : ∀ k, ∀ j' ∈ dyDesc L n k j, h ≤ (f (dyPt (n + k) j')).im) :
    ediam ((fun x : ℝ => f x) '' dyIcc n j) ≤
      2 * (ENNReal.ofReal koebeChildConst * ∑' k, dyDescNorm f h L n k j) := by
  refine ediam_le ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
  calc edist (f x) (f x') ≤ edist (f x) (f (dyPt n j)) + edist (f (dyPt n j)) (f x') :=
        edist_triangle _ _ _
    _ ≤ _ := by
        rw [two_mul, edist_comm]
        exact add_le_add (edist_le_of_mem_dyIcc hfd hfi hfc hj hgood hx)
          (edist_le_of_mem_dyIcc hfd hfi hfc hj hgood hx')

/-- The constant `C_p = (2C)^p S^{p-1}` of (3.6). -/
def dyCoverConst : ℝ≥0∞ :=
  (2 * ENNReal.ofReal koebeChildConst) ^ (14 / 9 : ℝ) * holderGeomSum ^ (5 / 9 : ℝ)

theorem dyCoverConst_ne_top : dyCoverConst ≠ ∞ := by
  unfold dyCoverConst
  refine ENNReal.mul_ne_top ?_ ?_
  · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
  · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) holderGeomSum_ne_top

/-- `(diam f(I))^p ≤ C_p Σ_{k ≥ 0} 2^{k/18} Σ_{J ⊂ I, J ∈ D_{n+k}(L)} a_J^p`. -/
theorem ediam_image_dyIcc_rpow_le (hfd : DifferentiableOn ℂ f H) (hfi : InjOn f H)
    (hfc : ContinuousOn f Hbar) (hj : j ∈ dyIdx L n)
    (hgood : ∀ k, ∀ j' ∈ dyDesc L n k j, h ≤ (f (dyPt (n + k) j')).im) :
    ediam ((fun x : ℝ => f x) '' dyIcc n j) ^ (14 / 9 : ℝ) ≤
      dyCoverConst * ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) *
        ∑ j' ∈ dyDesc L n k j, ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ)) := by
  calc ediam ((fun x : ℝ => f x) '' dyIcc n j) ^ (14 / 9 : ℝ)
      ≤ (2 * (ENNReal.ofReal koebeChildConst * ∑' k, dyDescNorm f h L n k j)) ^ (14 / 9 : ℝ) :=
        ENNReal.rpow_le_rpow (ediam_image_dyIcc_le hfd hfi hfc hj hgood) (by norm_num)
    _ = (2 * ENNReal.ofReal koebeChildConst) ^ (14 / 9 : ℝ) *
          (∑' k, dyDescNorm f h L n k j) ^ (14 / 9 : ℝ) := by
        rw [← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ ≤ (2 * ENNReal.ofReal koebeChildConst) ^ (14 / 9 : ℝ) *
          (holderGeomSum ^ (5 / 9 : ℝ) * ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) *
            dyDescNorm f h L n k j ^ (14 / 9 : ℝ)) :=
        mul_le_mul' le_rfl (tsum_rpow_le_holder _)
    _ = _ := by
        rw [dyCoverConst, mul_assoc]
        simp_rw [dyDescNorm_rpow]

/-! ## Summation over the relevant intervals -/

/-- `Σ_{I ∈ D_n(L)} Σ_k 2^{k/18} Σ_{J ⊂ I, J ∈ D_{n+k}} a_J^p ≤ 2^{-n/18} E_{L,h}(f)`. -/
theorem sum_tsum_dyDesc_le (f : ℂ → ℂ) (h : ℝ) (L n : ℕ) :
    ∑ j ∈ dyIdx L n, ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) *
        ∑ j' ∈ dyDesc L n k j, ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) / 18)) * dyEnergy f L h := by
  set g : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) / 18)) *
    ∑ j ∈ dyIdx L m, ENNReal.ofReal (dyWeight f h m j ^ (14 / 9 : ℝ)) with hg
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have e : ∀ k : ℕ, ∑ j ∈ dyIdx L n, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) *
        ∑ j' ∈ dyDesc L n k j, ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ)) =
      ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) / 18)) * g (n + k) := by
    intro k
    rw [← Finset.mul_sum, sum_dyIdx_sum_dyDesc L n k
      (fun j' => ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ))), hg]
    simp only
    rw [← mul_assoc, ofReal_two_rpow_mul]
    congr 3
    push_cast; ring
  rw [tsum_congr e, ENNReal.tsum_mul_left]
  refine mul_le_mul' le_rfl ?_
  exact ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective n) g

/-! ## Uniform continuity -/

/-- **Uniform continuity step.** For `n` large, if `x₀ ∈ I ∈ D_n(L)` has `Im f(x₀) ≥ 2h`, then
`Im f(z_J) ≥ h` for every descendant `J ⊂ I`. -/
theorem exists_forall_le_im_of_le_im (hfc : ContinuousOn f Hbar) (L : ℕ) (hh : 0 < h) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ j ∈ dyIdx L n, ∀ x₀ ∈ dyIcc n j, 2 * h ≤ (f x₀).im →
      ∀ k, ∀ j' ∈ dyDesc L n k j, h ≤ (f (dyPt (n + k) j')).im := by
  set K : Set ℂ := closedBall (0 : ℂ) ((L : ℝ) + 1) ∩ Hbar
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have huc := (hK.uniformContinuousOn_of_continuous (hfc.mono inter_subset_right))
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc h hh
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 / δ) (by norm_num : (1 : ℝ) < 2)
  refine ⟨N, fun n hn j hj x₀ hx₀ hfx₀ k j' hj' => ?_⟩
  have hjd := (mem_dyDesc.1 hj').1
  have hre := dyPt_re_mem_dyIcc_of_mem_dyDesc hj'
  have hzK : dyPt (n + k) j' ∈ K := by
    refine ⟨?_, QuantumZipper.H_subset_Hbar (dyPt_mem_H _ _)⟩
    rw [mem_closedBall, dist_zero_right]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h1 := abs_dyPt_re_le hjd
    have h2 : |(dyPt (n + k) j').im| ≤ 1 := by
      rw [abs_of_pos (dyPt_im_pos _ _), dyPt_im, div_le_one (two_pow_pos_real _)]
      exact one_le_pow₀ (by norm_num)
    linarith
  have hx₀I := dyIcc_subset_Icc hj hx₀
  have hx₀K : (x₀ : ℂ) ∈ K := by
    refine ⟨?_, show 0 ≤ (x₀ : ℂ).im by simp⟩
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_le.2 hx₀I]
  have hdist : dist (dyPt (n + k) j') (x₀ : ℂ) < δ := by
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    have h1 := dyIcc_length hre hx₀
    have h2 : |(dyPt (n + k) j').im| ≤ 1 / 2 ^ n := by
      rw [abs_of_pos (dyPt_im_pos _ _), dyPt_im]
      exact one_div_le_one_div_of_le (two_pow_pos_real n)
        (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n k))
    have h3 : (2 : ℝ) / 2 ^ n < δ := by
      have h2N : (2 : ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
      rw [div_lt_iff₀ (two_pow_pos_real n)]
      rw [div_lt_iff₀ hδ] at hN
      nlinarith
    have : 1 / (2 : ℝ) ^ n + 1 / 2 ^ n = 2 / 2 ^ n := by ring
    linarith
  have hfd := hδf _ hzK _ hx₀K hdist
  rw [dist_eq_norm] at hfd
  have him : |(f (dyPt (n + k) j')).im - (f x₀).im| < h :=
    (by simpa using Complex.abs_im_le_norm (f (dyPt (n + k) j') - f x₀) :
      |(f (dyPt (n + k) j')).im - (f x₀).im| ≤ ‖f (dyPt (n + k) j') - f x₀‖).trans_lt hfd
  linarith [(abs_lt.1 him).1]

/-! ## Lemma 4 -/

/-- **Lemma 4 (deterministic dyadic cover).** Let `f` be holomorphic and injective on `ℍ` and
continuous on `ℍ̄`. Fix an integer `L ≥ 1` and `h > 0`. If `E_{L,h}(f) < ∞` (3.3), then
`H^{14/9}(f([-L, L]) ∩ {Im w ≥ 2h}) = 0`. -/
theorem hausdorffMeasure_image_Icc_inter_eq_zero (hfd : DifferentiableOn ℂ f H)
    (hfi : InjOn f H) (hfc : ContinuousOn f Hbar) (hL : 1 ≤ L) (hh : 0 < h)
    (hE : dyEnergy f L h ≠ ∞) :
    μH[14 / 9] ((fun x : ℝ => f x) '' Icc (-(L : ℝ)) L ∩ {w | 2 * h ≤ w.im}) = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_le_im_of_le_im hfc L hh
  set S := (fun x : ℝ => f x) '' Icc (-(L : ℝ)) L ∩ {w | 2 * h ≤ w.im}
  let t : ∀ n : ℕ, (dyIdx L n) → Set ℂ := fun n i =>
    (fun x : ℝ => f x) '' dyIcc n i ∩ {w | 2 * h ≤ w.im}
  set u : ℕ → ℝ≥0∞ := fun n =>
    dyCoverConst * (ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) / 18)) * dyEnergy f L h)
  -- each covering set
  have hterm : ∀ n ≥ N, ∀ i : dyIdx L n, ediam (t n i) ^ (14 / 9 : ℝ) ≤
      dyCoverConst * ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) *
        ∑ j' ∈ dyDesc L n k i, ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ)) := by
    intro n hn i
    rcases (t n i).eq_empty_or_nonempty with he | ⟨w, ⟨x₀, hx₀, rfl⟩, hw⟩
    · rw [he, ediam_empty, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact bot_le
    · have hgood := hN n hn i i.2 x₀ hx₀ hw
      exact (ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) (by norm_num)).trans
        (ediam_image_dyIcc_rpow_le hfd hfi hfc i.2 hgood)
  have hsum : ∀ n ≥ N, ∑ i : dyIdx L n, ediam (t n i) ^ (14 / 9 : ℝ) ≤ u n := by
    intro n hn
    calc ∑ i : dyIdx L n, ediam (t n i) ^ (14 / 9 : ℝ)
        ≤ ∑ i : dyIdx L n, dyCoverConst * ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) *
            ∑ j' ∈ dyDesc L n k i, ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ)) :=
          Finset.sum_le_sum fun i _ => hterm n hn i
      _ = dyCoverConst * ∑ j ∈ dyIdx L n, ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) *
            ∑ j' ∈ dyDesc L n k j, ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ)) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_coe_sort (dyIdx L n) (fun j => ∑' k : ℕ,
            ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) *
              ∑ j' ∈ dyDesc L n k j, ENNReal.ofReal (dyWeight f h (n + k) j' ^ (14 / 9 : ℝ)))
      _ ≤ u n := mul_le_mul' le_rfl (sum_tsum_dyDesc_le f h L n)
  -- the bound tends to zero
  have hu : Tendsto u atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) / 18))) atTop (𝓝 0) := by
      have e : ∀ n : ℕ, (2 : ℝ) ^ (-(n : ℝ) / 18) = ((2 : ℝ) ^ (-(1 / 18 : ℝ))) ^ n := fun n => by
        rw [← two_rpow_mul_nat]; congr 1; ring
      simp_rw [e]
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hE)
    rw [zero_mul] at h2
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr dyCoverConst_ne_top)
    rwa [mul_zero] at h3
  set r : ℕ → ℝ≥0∞ := fun n => u n ^ (14 / 9 : ℝ)⁻¹
  have hr : Tendsto r atTop (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := (14 / 9 : ℝ)⁻¹)).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact this.comp hu
  have hdiam : ∀ᶠ n in atTop, ∀ i, ediam (t n i) ≤ r n := by
    filter_upwards [eventually_ge_atTop N] with n hn i
    have h1 : ediam (t n i) ^ (14 / 9 : ℝ) ≤ u n :=
      (Finset.single_le_sum (f := fun i : dyIdx L n => ediam (t n i) ^ (14 / 9 : ℝ))
        (fun _ _ => bot_le) (Finset.mem_univ i)).trans (hsum n hn)
    calc ediam (t n i) = (ediam (t n i) ^ (14 / 9 : ℝ)) ^ (14 / 9 : ℝ)⁻¹ :=
          (ENNReal.rpow_rpow_inv (by norm_num) _).symm
      _ ≤ r n := ENNReal.rpow_le_rpow h1 (by norm_num)
  have hcover : ∀ᶠ n in atTop, S ⊆ ⋃ i, t n i := by
    refine Eventually.of_forall fun n => ?_
    rintro _ ⟨⟨x, hx, rfl⟩, hw⟩
    obtain ⟨j, hj, hxj⟩ := exists_mem_dyIdx_mem_dyIcc hL hx n
    exact mem_iUnion.2 ⟨⟨j, hj⟩, ⟨x, hxj, rfl⟩, hw⟩
  have hle := Measure.hausdorffMeasure_le_liminf_sum (14 / 9 : ℝ) S r hr t hdiam hcover
  have hlim : liminf (fun n => ∑ i : dyIdx L n, ediam (t n i) ^ (14 / 9 : ℝ)) atTop ≤ 0 := by
    calc liminf (fun n => ∑ i : dyIdx L n, ediam (t n i) ^ (14 / 9 : ℝ)) atTop
        ≤ liminf u atTop := liminf_le_liminf (by
          filter_upwards [eventually_ge_atTop N] with n hn using hsum n hn)
      _ = 0 := hu.liminf_eq
  exact le_antisymm (hle.trans hlim) bot_le

end InteractingSLE.SLE8.SpaceFilling
