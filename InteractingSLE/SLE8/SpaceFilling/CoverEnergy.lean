import InteractingSLE.SLE8.SpaceFilling.CoverDyadic
import QuantumZipper.Proofs.Complex.KoebeHalfPlane
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.MeanValue

/-!
# κ = 8 space filling, Lemma 4: weights, the weighted energy, Koebe step and Hölder

Source: the user's note *Space filling of a continuous SLE₈ trace*
(`source/external/SLE8SF/sle8_space_filling_formalization.pdf`, §3, Lemma 4 and its proof, p. 4).

For `f : ℂ → ℂ` (holomorphic and injective on `ℍ`), `h > 0` and a dyadic interval `I = I_{m,j}`:

* `dyWeight f h m j = a_I = |I| |f'(z_I)| 1{Im f(z_I) ≥ h}`;
* `dyEnergy f L h = E_{L,h}(f) = Σ_m 2^{m/18} Σ_{I ∈ D_m(L)} a_I^{14/9}` (3.3), in `[0, ∞]`.

## Main results

* `norm_sub_le_koebe`: **Koebe distortion step (3.4)**: if `dist w z ≤ (3/5) Im z` then
  `|f(w) - f(z)| ≤ C Im z |f'(z)|` with the absolute constant `C = koebeChildConst`
  (QuantumZipper's non-sharp disk distortion `CA.Koebe.norm_deriv_le_distortion` on the disk
  `B(z, Im z) ⊆ ℍ`, `CA.Koebe.ball_im_subset_upperHalfPlane`, and the mean value inequality);
* `edist_dyPt_succ_le`: (3.4) for a child `J` of `I`: `|f(z_J) - f(z_I)| ≤ C a_I` when
  `Im f(z_I) ≥ h`;
* `tsum_rpow_le_holder`: **weighted Hölder (3.5)**:
  `(Σ_k b_k)^{14/9} ≤ (Σ_k 2^{-k/10})^{5/9} Σ_k 2^{k/18} b_k^{14/9}`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.SLE8.SpaceFilling

open QuantumZipper

/-! ## Weights and energy -/

/-- The weight `a_I = |I| |f'(z_I)| 1{Im f(z_I) ≥ h}` of the dyadic interval `I = I_{m,j}`. -/
def dyWeight (f : ℂ → ℂ) (h : ℝ) (m : ℕ) (j : ℤ) : ℝ :=
  if h ≤ (f (dyPt m j)).im then 1 / 2 ^ m * ‖deriv f (dyPt m j)‖ else 0

/-- The weighted energy `E_{L,h}(f) = Σ_{m ≥ 0} 2^{m/18} Σ_{I ∈ D_m(L)} a_I^{14/9}` of (3.3). -/
def dyEnergy (f : ℂ → ℂ) (L : ℕ) (h : ℝ) : ℝ≥0∞ :=
  ∑' m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) / 18)) *
    ∑ j ∈ dyIdx L m, ENNReal.ofReal (dyWeight f h m j ^ (14 / 9 : ℝ))

variable {f : ℂ → ℂ} {h : ℝ}

theorem dyWeight_nonneg (f : ℂ → ℂ) (h : ℝ) (m : ℕ) (j : ℤ) : 0 ≤ dyWeight f h m j := by
  unfold dyWeight; split_ifs <;> positivity

theorem dyWeight_of_le {m : ℕ} {j : ℤ} (hle : h ≤ (f (dyPt m j)).im) :
    dyWeight f h m j = 1 / 2 ^ m * ‖deriv f (dyPt m j)‖ := by
  simp only [dyWeight, hle, ↓reduceIte]

theorem dyWeight_congr {f g : ℂ → ℂ} (heq : EqOn f g H) (h : ℝ) (m : ℕ) (j : ℤ) :
    dyWeight f h m j = dyWeight g h m j := by
  have hz := dyPt_mem_H m j
  have hev : f =ᶠ[𝓝 (dyPt m j)] g := Filter.eventually_of_mem (isOpen_H.mem_nhds hz) heq
  unfold dyWeight
  rw [heq hz, hev.deriv_eq]

theorem dyEnergy_congr {f g : ℂ → ℂ} (heq : EqOn f g H) (L : ℕ) (h : ℝ) :
    dyEnergy f L h = dyEnergy g L h := by
  unfold dyEnergy
  simp_rw [dyWeight_congr heq h]

/-! ## The Koebe step (3.4) -/

/-- The absolute constant of the Koebe step (3.4): `(5/2)^{koebeDistExp}`. -/
def koebeChildConst : ℝ := (5 / 2 : ℝ) ^ CA.Koebe.koebeDistExp

theorem koebeChildConst_pos : 0 < koebeChildConst := by
  unfold koebeChildConst; positivity

/-- **Koebe distortion step (3.4).** For `f` holomorphic and injective on `ℍ`, if
`dist w z ≤ (3/5) Im z` then `|f(w) - f(z)| ≤ C Im z |f'(z)|`, `C = koebeChildConst`. -/
theorem norm_sub_le_koebe (hfd : DifferentiableOn ℂ f H) (hfi : InjOn f H) {z w : ℂ}
    (hz : 0 < z.im) (hw : dist w z ≤ 3 / 5 * z.im) :
    ‖f w - f z‖ ≤ koebeChildConst * (z.im * ‖deriv f z‖) := by
  set s := closedBall z (3 / 5 * z.im)
  have hsb : s ⊆ ball z z.im := closedBall_subset_ball (by linarith)
  have hsH : s ⊆ H := hsb.trans CA.Koebe.ball_im_subset_upperHalfPlane
  have hdiff : ∀ u ∈ s, DifferentiableAt ℂ f u := fun u hu =>
    hfd.differentiableAt (isOpen_H.mem_nhds (hsH hu))
  have hbound : ∀ u ∈ s, ‖deriv f u‖ ≤ ‖deriv f z‖ * koebeChildConst := by
    intro u hu
    have hd := CA.Koebe.norm_deriv_le_distortion (hfd.mono CA.Koebe.ball_im_subset_upperHalfPlane)
      (hfi.mono CA.Koebe.ball_im_subset_upperHalfPlane) (hsb hu)
    refine hd.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have hdu : dist u z ≤ 3 / 5 * z.im := hu
    have h25 : (2 / 5 : ℝ) ≤ 1 - dist u z / z.im := by
      rw [le_sub_comm, div_le_iff₀ hz]; linarith
    have hmono := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2 / 5) h25
      (neg_nonpos.2 CA.Koebe.koebeDistExp_pos.le)
    refine hmono.trans_eq ?_
    rw [koebeChildConst, Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
    norm_num
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_closedBall _ _)
    (mem_closedBall_self (by linarith)) hw
  calc ‖f w - f z‖ ≤ ‖deriv f z‖ * koebeChildConst * dist w z := by
        rw [dist_eq_norm]; exact hmvt
    _ ≤ ‖deriv f z‖ * koebeChildConst * z.im := by
        refine mul_le_mul_of_nonneg_left (hw.trans (by linarith)) ?_
        exact mul_nonneg (norm_nonneg _) koebeChildConst_pos.le
    _ = koebeChildConst * (z.im * ‖deriv f z‖) := by ring

/-- (3.4) for a child: if `Im f(z_I) ≥ h` for the parent `I = I_{m, j'/2}` of `J = I_{m+1, j'}`,
then `|f(z_I) - f(z_J)| ≤ C a_I`. -/
theorem edist_dyPt_succ_le (hfd : DifferentiableOn ℂ f H) (hfi : InjOn f H) (m : ℕ) (j' : ℤ)
    (hle : h ≤ (f (dyPt m (j' / 2))).im) :
    edist (f (dyPt m (j' / 2))) (f (dyPt (m + 1) j')) ≤
      ENNReal.ofReal koebeChildConst * ENNReal.ofReal (dyWeight f h m (j' / 2)) := by
  rw [edist_dist, ← ENNReal.ofReal_mul koebeChildConst_pos.le, dyWeight_of_le hle]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [dist_comm, dist_eq_norm]
  have := norm_sub_le_koebe hfd hfi (dyPt_im_pos m (j' / 2)) (dist_dyPt_succ_le m j')
  rwa [dyPt_im] at this

/-! ## Weighted Hölder (3.5) -/

/-- The geometric sum `S = Σ_k 2^{-k/10}` of (3.5). -/
def holderGeomSum : ℝ≥0∞ := ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) / 10))

theorem two_rpow_mul_nat (a : ℝ) (k : ℕ) : (2 : ℝ) ^ (a * k) = ((2 : ℝ) ^ a) ^ k := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

theorem holderGeomSum_ne_top : holderGeomSum ≠ ∞ := by
  have e : ∀ k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) / 10)) =
      ENNReal.ofReal ((2 : ℝ) ^ (-(1 / 10 : ℝ))) ^ k := fun k => by
    rw [← ENNReal.ofReal_pow (by positivity), ← two_rpow_mul_nat]
    congr 2; ring
  rw [holderGeomSum, tsum_congr e, ENNReal.tsum_geometric, ne_eq, ENNReal.inv_eq_top,
    tsub_eq_zero_iff_le, not_le, ← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 ?_
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem ofReal_two_rpow_mul (a b : ℝ) :
    ENNReal.ofReal ((2 : ℝ) ^ a) * ENNReal.ofReal ((2 : ℝ) ^ b) = ENNReal.ofReal ((2 : ℝ) ^ (a + b)) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by norm_num)]

theorem ofReal_two_rpow_rpow (a b : ℝ) (hb : 0 ≤ b) :
    ENNReal.ofReal ((2 : ℝ) ^ a) ^ b = ENNReal.ofReal ((2 : ℝ) ^ (a * b)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hb, ← Real.rpow_mul (by norm_num)]

/-- **Weighted Hölder (3.5)** with `p = 14/9`, `η = 1/18` (`η/(p - 1) = 1/10`):
`(Σ_k b_k)^p ≤ (Σ_k 2^{-k/10})^{p-1} Σ_k 2^{k/18} b_k^p`. -/
theorem tsum_rpow_le_holder (b : ℕ → ℝ≥0∞) :
    (∑' k, b k) ^ (14 / 9 : ℝ) ≤
      holderGeomSum ^ (5 / 9 : ℝ) *
        ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) * b k ^ (14 / 9 : ℝ) := by
  set T := ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) * b k ^ (14 / 9 : ℝ)
  have hpq : (14 / 5 : ℝ).HolderConjugate (14 / 9) := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have key : ∀ K : ℕ, ∑ k ∈ Finset.range K, b k ≤
      holderGeomSum ^ (5 / 14 : ℝ) * T ^ (9 / 14 : ℝ) := by
    intro K
    set u : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) / 28))
    set v : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 28)) * b k
    have huv : ∀ k, u k * v k = b k := fun k => by
      simp only [u, v]
      rw [← mul_assoc, ofReal_two_rpow_mul, show -(k : ℝ) / 28 + k / 28 = 0 by ring,
        Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    have hu : ∀ k, u k ^ (14 / 5 : ℝ) = ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) / 10)) := fun k => by
      simp only [u]
      rw [ofReal_two_rpow_rpow _ _ (by norm_num)]
      congr 2; ring
    have hv : ∀ k, v k ^ (14 / 9 : ℝ) =
        ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 18)) * b k ^ (14 / 9 : ℝ) := fun k => by
      simp only [v]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ofReal_two_rpow_rpow _ _ (by norm_num)]
      congr 3; ring
    calc ∑ k ∈ Finset.range K, b k = ∑ k ∈ Finset.range K, u k * v k := by simp_rw [huv]
      _ ≤ (∑ k ∈ Finset.range K, u k ^ (14 / 5 : ℝ)) ^ (1 / (14 / 5 : ℝ)) *
            (∑ k ∈ Finset.range K, v k ^ (14 / 9 : ℝ)) ^ (1 / (14 / 9 : ℝ)) :=
          ENNReal.inner_le_Lp_mul_Lq _ _ _ hpq
      _ ≤ holderGeomSum ^ (5 / 14 : ℝ) * T ^ (9 / 14 : ℝ) := by
          rw [show (1 / (14 / 5 : ℝ)) = 5 / 14 by norm_num,
            show (1 / (14 / 9 : ℝ)) = 9 / 14 by norm_num]
          gcongr
          · simp_rw [hu]; exact ENNReal.sum_le_tsum _
          · simp_rw [hv]; exact ENNReal.sum_le_tsum _
  have hsum : ∑' k, b k ≤ holderGeomSum ^ (5 / 14 : ℝ) * T ^ (9 / 14 : ℝ) := by
    rw [ENNReal.tsum_eq_iSup_nat]; exact iSup_le key
  calc (∑' k, b k) ^ (14 / 9 : ℝ) ≤ (holderGeomSum ^ (5 / 14 : ℝ) * T ^ (9 / 14 : ℝ)) ^ (14 / 9 : ℝ) :=
        ENNReal.rpow_le_rpow hsum (by norm_num)
    _ = holderGeomSum ^ (5 / 9 : ℝ) * T := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

end InteractingSLE.SLE8.SpaceFilling
