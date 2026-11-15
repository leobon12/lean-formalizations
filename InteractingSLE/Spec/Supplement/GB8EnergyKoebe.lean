/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoTime2Other
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Foundations.Loewner.YuanShift
import QuantumZipper.Proofs.Complex.KoebeDistortion
import InteractingSLE.Spec.Sec5.Aux22StripAlive
import InteractingSLE.Spec.Supplement.LPProbReflect
import Mathlib.Algebra.Order.Chebyshev


/-!
# Lemma GB8, the finite-energy buffer: bounded distortion and finite energy (deterministic)

Packet PROVE-T14-TIP5 (route of `planning/handoffs/PROVE-T14-TIP4.md` §5.2). Specification supplement §8.8, proof of
**Lemma GB8** (`source/spec/p481-528.md` L1027–L1043, pp. 523–524): "On the proposed entirely interior transient future,
its completed spherical range is disjoint from the compact boundary support … Aux. 108 gives equivalence on the entire
stopped history … by one strictly positive finite-energy density."

In driver form the buffer is a **finite energy** of the change of weights from the actual word to the GB8 reference
(all weight of a side on its outermost mark). Its coefficients `c = ρ′ − ρ` have **zero total on each side**, so the
energy density is a combination of `1/(w − vᵢ) − 1/(w − v_last)`, and

  `2(Σ cᵢ/aᵢ)² ≤ Σ n cᵢ² (2/aᵢ² − 2/a_last²)`,  `aᵢ = w − vᵢ` (`two_mul_sq_sum_div_le`),

while `∫₀ᵀ 2/aᵢ² = −log f_T′(yᵢ)` is minus the logarithm of the derivative of the Loewner map at the real mark
(`norm_deriv_fwdMap_mark`). If the transient trace never visits the marks' side of the real line, it stays a positive
distance from the marks' segment (`exists_clearance`), every point of a fixed disc around the segment is alive at every
time (two boxes and a ray avoid the filled trace, `notMem_fillH_of_boxes`; `alive_of_ball`), the Loewner maps are
univalent there (`differentiableOn_fwdMap_of_alive`, `injOn_fwdMap_of_alive`), and Koebe distortion along the segment
(QuantumZipper's non-sharp distortion, `norm_deriv_le_chain`) bounds `log f_T′(y_last) − log f_T′(yᵢ)` uniformly in
`T` (`exists_side_bound`). Hence the energy is bounded uniformly in the horizon (`exists_energy_bound`).

## Main results

* `notMem_fillH_of_boxes`, `alive_of_ball`, `differentiableOn_fwdMap_of_alive`, `injOn_fwdMap_of_alive`;
* `norm_deriv_le_koebeK`, `norm_deriv_le_chain` (Koebe distortion along a real segment);
* `isForwardSol_of_mark`, `norm_deriv_fwdMap_mark` (`‖f_T′(y)‖ = exp(−∫₀ᵀ 2/(w − v)²)` at a real mark);
* `exists_clearance`, **`exists_side_bound`** (bounded distortion on one side);
* `two_mul_sq_sum_div_le`, **`exists_energy_bound`** (finite energy for zero side totals).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped ComplexConjugate NNReal ENNReal

namespace InteractingSLE.Supp8.GB8

open QuantumZipper (H IsForwardSol fwdMap fwdHull logDerivFwd)

/-! ### Points off the filled trace near a real segment -/

/-- **Two boxes and a ray.** Let `A` be closed and bounded by `R`. If the box `(a − ρ, b + ρ) × (0, ρ)` over the
segment `[a, b]` and a thin box `(e − 1, b) × (0, ε)` running to a real point `e < −R` avoid `A`, then the first box
avoids the filling `fillH A`: its points are joined to `∞` in `ℍ ∖ A` through the thin box and the vertical ray at
`e`. -/
theorem notMem_fillH_of_boxes {A : Set ℂ} (hA : IsClosed A) {R : ℝ} (hAR : A ⊆ closedBall 0 R)
    {a b e ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hea : e < a - ρ) (hab : a ≤ b) (heR : e < -R)
    (h1 : ∀ w ∈ Ioo (a - ρ) (b + ρ) ×ℂ Ioo 0 ρ, w ∉ A)
    (h2 : ∀ w ∈ Ioo (e - 1) b ×ℂ Ioo 0 ε, w ∉ A) :
    ∀ z ∈ Ioo (a - ρ) (b + ρ) ×ℂ Ioo 0 ρ, z ∉ fillH A := by
  set Box1 : Set ℂ := Ioo (a - ρ) (b + ρ) ×ℂ Ioo 0 ρ with hB1
  set Box2 : Set ℂ := Ioo (e - 1) b ×ℂ Ioo 0 ε with hB2
  set Ray : Set ℂ := {e} ×ℂ Ici (ε / 2) with hRay
  have hAc : closure A = A := hA.closure_eq
  have hRayA : Ray ⊆ H \ closure A := by
    intro w hw
    rw [hRay, Complex.mem_reProdIm] at hw
    refine ⟨lt_of_lt_of_le (half_pos hε) hw.2, fun hwA => ?_⟩
    rw [hAc] at hwA
    have h3 := hAR hwA
    rw [mem_closedBall, dist_zero_right] at h3
    have h4 := Complex.abs_re_le_norm w
    rw [mem_singleton_iff.1 hw.1, abs_of_neg (by linarith [(norm_nonneg w).trans h3])] at h4
    linarith
  have hB1A : Box1 ⊆ H \ closure A := fun w hw => ⟨by
    rw [hB1, Complex.mem_reProdIm] at hw; exact hw.2.1, by rw [hAc]; exact h1 w hw⟩
  have hB2A : Box2 ⊆ H \ closure A := fun w hw => ⟨by
    rw [hB2, Complex.mem_reProdIm] at hw; exact hw.2.1, by rw [hAc]; exact h2 w hw⟩
  -- a common point of the two boxes and a common point of the thin box and the ray
  set m : ℝ := min ρ ε with hm
  have hm0 : 0 < m := lt_min hρ hε
  set p₁ : ℂ := ((a - ρ / 2 : ℝ) : ℂ) + ((m / 2 : ℝ) : ℂ) * Complex.I with hp₁
  set p₂ : ℂ := (e : ℂ) + ((3 * ε / 4 : ℝ) : ℂ) * Complex.I with hp₂
  have hp₁re : p₁.re = a - ρ / 2 := by simp [hp₁]
  have hp₁im : p₁.im = m / 2 := by simp [hp₁]
  have hp₂re : p₂.re = e := by simp [hp₂]
  have hp₂im : p₂.im = 3 * ε / 4 := by simp [hp₂]
  have hmρ : m ≤ ρ := min_le_left _ _
  have hmε : m ≤ ε := min_le_right _ _
  have hconn : IsPreconnected (Box1 ∪ Box2 ∪ Ray) := by
    refine ((Sec5.Aux22Strip.convex_reProdIm (convex_Ioo _ _) (convex_Ioo _ _)).isPreconnected.union p₁ ?_ ?_
      (Sec5.Aux22Strip.convex_reProdIm (convex_Ioo _ _) (convex_Ioo _ _)).isPreconnected).union p₂ ?_ ?_
      (Sec5.Aux22Strip.convex_reProdIm (convex_singleton e) (convex_Ici _)).isPreconnected
    · rw [Complex.mem_reProdIm, hp₁re, hp₁im]
      exact ⟨⟨by linarith, by linarith⟩, by positivity, by linarith⟩
    · rw [Complex.mem_reProdIm, hp₁re, hp₁im]
      exact ⟨⟨by linarith, by linarith⟩, by positivity, by linarith⟩
    · refine Or.inr ?_
      rw [Complex.mem_reProdIm, hp₂re, hp₂im]
      exact ⟨⟨by linarith, by linarith⟩, by positivity, by linarith⟩
    · rw [Complex.mem_reProdIm, hp₂re, hp₂im]
      exact ⟨rfl, by rw [mem_Ici]; linarith⟩
  have hunb : ¬ Bornology.IsBounded (Box1 ∪ Box2 ∪ Ray) := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    set q : ℂ := (e : ℂ) + ((max M 0 + ε : ℝ) : ℂ) * Complex.I with hq
    have hqre : q.re = e := by simp [hq]
    have hqim : q.im = max M 0 + ε := by simp [hq]
    have hmem : q ∈ Box1 ∪ Box2 ∪ Ray := by
      right
      rw [hRay, Complex.mem_reProdIm, hqre, hqim]
      exact ⟨rfl, by rw [mem_Ici]; linarith [le_max_right M 0]⟩
    have h3 := hM hmem
    rw [mem_closedBall, dist_zero_right] at h3
    have h4 := Complex.abs_im_le_norm q
    rw [hqim, abs_of_pos (by linarith [le_max_right M 0])] at h4
    linarith [le_max_left M 0]
  intro z hz hzF
  obtain ⟨-, hzF⟩ := hzF
  rcases hzF with hzA | hzb
  · rw [hAc] at hzA; exact h1 z hz hzA
  · have hsub : Box1 ∪ Box2 ∪ Ray ⊆ connectedComponentIn (H \ closure A) z :=
      hconn.subset_connectedComponentIn (Or.inl (Or.inl hz))
        (union_subset (union_subset hB1A hB2A) hRayA)
    exact hunb (hzb.subset hsub)


/-! ### Alive discs around real points -/

/-- **A disc around a real point is alive** if the disc of twice its radius misses the hull in `ℍ` and stays off the
seed `0`: points of `ℍ` off the hull are alive, points of the lower half-plane by conjugation, real points by
`ZhanGT4.exists_isForwardSol_of_disjoint_ball`. -/
theorem alive_of_ball {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {x ρ : ℝ}
    (hρ : 0 < ρ) (hx0 : ρ < |x|) (hK : ∀ z ∈ ball (x : ℂ) ρ, 0 < z.im → z ∉ fwdHull W T) :
    ∀ z ∈ ball (x : ℂ) (ρ / 2), ∃ u, IsForwardSol W z T u := by
  intro z hz
  have hzρ : z ∈ ball (x : ℂ) ρ := ball_subset_ball (by linarith) hz
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have hc : conj z ∈ ball (x : ℂ) ρ := by
      rw [mem_ball, dist_eq_norm] at hzρ ⊢
      rw [show conj z - (x : ℂ) = conj (z - x) by simp, Complex.norm_conj]
      exact hzρ
    have hcH : 0 < (conj z).im := by rw [Complex.conj_im]; linarith
    obtain ⟨-, T', hT', u, hu⟩ := (QuantumZipper.FwdHolo.mem_compl_fwdHull_iff hT).1 ⟨hcH, hK _ hc hcH⟩
    have h := isForwardSol_conj (QuantumZipper.isForwardSol_restrict hu hT hT'.le)
    rw [Complex.conj_conj] at h
    exact ⟨_, h⟩
  · have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hzero])
    have hdist : |z.re - x| < ρ / 2 := by
      have h1 : ‖z - (x : ℂ)‖ < ρ / 2 := by rw [← dist_eq_norm]; exact mem_ball.1 hz
      have h2 := (Complex.abs_re_le_norm (z - x)).trans_lt h1
      simpa using h2
    have hre0 : z.re ≠ 0 := by
      intro h0
      rw [h0, zero_sub, abs_neg] at hdist
      linarith
    rw [hz']
    refine ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hre0 hT (half_pos hρ) ?_
    rw [Set.disjoint_left]
    intro w hw hwK
    have hwH : 0 < w.im := (QuantumZipper.fwdHull_mono.2 T hwK)
    refine hK w ?_ hwH hwK
    rw [mem_ball] at hw ⊢
    calc dist w (x : ℂ) ≤ dist w ((z.re : ℝ) : ℂ) + dist ((z.re : ℝ) : ℂ) (x : ℂ) := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := by
          refine add_lt_add hw ?_
          rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact hdist
      _ = ρ := by ring
  · obtain ⟨-, T', hT', u, hu⟩ := (QuantumZipper.FwdHolo.mem_compl_fwdHull_iff hT).1 ⟨hpos, hK z hzρ hpos⟩
    exact ⟨u, QuantumZipper.isForwardSol_restrict hu hT hT'.le⟩

/-- The Loewner map is holomorphic on every set of points alive at `T`. -/
theorem differentiableOn_fwdMap_of_alive {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {U : Set ℂ}
    (hU : ∀ z ∈ U, ∃ u, IsForwardSol W z T u) : DifferentiableOn ℂ (fwdMap W T) U := by
  intro z hz
  obtain ⟨u, hu⟩ := hU z hz
  obtain ⟨δ, hδ, hlow, hzz⟩ := ZhanGT4.exists_aliveDisc_self hu hT
  exact (ZhanGT4.hasDerivAt_fwdMap_aliveDisc hW hu hδ hlow hzz ⟨hT, le_rfl⟩).differentiableAt.differentiableWithinAt

/-- The Loewner map is injective on every set of points alive at `T` (the linear identity
`f_T w − f_T z = (w − z) exp(−∫ 2/(f_s w f_s z))`). -/
theorem injOn_fwdMap_of_alive {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {U : Set ℂ}
    (hU : ∀ z ∈ U, ∃ u, IsForwardSol W z T u) : InjOn (fwdMap W T) U := by
  intro z hz w hw h
  obtain ⟨u, hu⟩ := hU z hz
  obtain ⟨v, hv⟩ := hU w hw
  have e := QuantumZipper.FwdHolo.sol_sub_eq hu hv T ⟨hT, le_rfl⟩
  rw [← fwdMap_eq_of_isForwardSol hW hu ⟨hT, le_rfl⟩, ← fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩, h,
    sub_self] at e
  rcases mul_eq_zero.1 e.symm with h1 | h1
  · exact (sub_eq_zero.1 h1).symm
  · exact absurd h1 (Complex.exp_ne_zero _)

/-! ### Koebe distortion along a real segment -/

/-- The one-step Koebe constant `(1/2)^{−C₂}` (QuantumZipper's non-sharp distortion exponent). -/
def koebeK : ℝ := (1 / 2 : ℝ) ^ (-QuantumZipper.CA.Koebe.koebeDistExp)

theorem koebeK_pos : 0 < koebeK := Real.rpow_pos_of_pos (by norm_num) _

/-- **One Koebe step**: at distance at most `r/2` from the centre of a disc of univalence of radius `r`, the
derivative is at most `koebeK` times the derivative at the centre. -/
theorem norm_deriv_le_koebeK {f : ℂ → ℂ} {c w : ℂ} {r : ℝ} (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball c r))
    (hi : InjOn f (ball c r)) (hw : dist w c ≤ r / 2) : ‖deriv f w‖ ≤ ‖deriv f c‖ * koebeK := by
  have hwB : w ∈ ball c r := mem_ball.2 (by linarith)
  refine (QuantumZipper.CA.Koebe.norm_deriv_le_distortion hd hi hwB).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have h1 : dist w c / r ≤ 1 / 2 := by rw [div_le_iff₀ hr]; linarith
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith)
    (neg_nonpos.2 QuantumZipper.CA.Koebe.koebeDistExp_pos.le)

/-- **Koebe chain along a real segment**: if `f` is univalent on the disc of radius `r` around every point of
`[a, b]`, then `‖f′(x)‖ ≤ koebeK^n ‖f′(y)‖` for `x, y ∈ [a, b]` with `|x − y| ≤ n r/2`. -/
theorem norm_deriv_le_chain {f : ℂ → ℂ} {a b r : ℝ} (hr : 0 < r)
    (hd : ∀ x ∈ Icc a b, DifferentiableOn ℂ f (ball (x : ℂ) r))
    (hi : ∀ x ∈ Icc a b, InjOn f (ball (x : ℂ) r)) (n : ℕ) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| ≤ n * (r / 2) →
      ‖deriv f (x : ℂ)‖ ≤ ‖deriv f (y : ℂ)‖ * koebeK ^ n := by
  induction n with
  | zero =>
    intro x _ y _ h
    have : x = y := by
      have := abs_nonneg (x - y)
      simp only [CharP.cast_eq_zero, zero_mul] at h
      linarith [abs_eq_zero.1 (le_antisymm h this), sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm h this))]
    rw [this, pow_zero, mul_one]
  | succ n ih =>
    intro x hx y hy h
    set z : ℝ := x - (x - y) / ((n : ℝ) + 1) with hzdef
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hz : z ∈ Icc a b := by
      have e : z = (n / ((n : ℝ) + 1)) * x + (1 / ((n : ℝ) + 1)) * y := by
        rw [hzdef]; field_simp; ring
      rw [e]
      have hw0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
      have hw1 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      have hs : (n : ℝ) / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) = 1 := by field_simp
      exact (convex_Icc a b) hx hy hw0 hw1 hs
    have hxz : |x - z| ≤ r / 2 := by
      rw [hzdef, show x - (x - (x - y) / ((n : ℝ) + 1)) = (x - y) / ((n : ℝ) + 1) by ring, abs_div,
        abs_of_pos hn1, div_le_iff₀ hn1]
      push_cast at h
      nlinarith [abs_nonneg (x - y)]
    have hzy : |z - y| ≤ n * (r / 2) := by
      rw [hzdef, show x - (x - y) / ((n : ℝ) + 1) - y = (x - y) * (n / ((n : ℝ) + 1)) by field_simp; ring,
        abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n / ((n : ℝ) + 1))]
      push_cast at h
      have h2 : (n : ℝ) / ((n : ℝ) + 1) * ((n + 1) * (r / 2)) = n * (r / 2) := by field_simp
      calc |x - y| * (n / ((n : ℝ) + 1)) ≤ ((n + 1) * (r / 2)) * (n / ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right h (by positivity)
        _ = n * (r / 2) := by rw [mul_comm]; exact h2
    have hstep : ‖deriv f (x : ℂ)‖ ≤ ‖deriv f (z : ℂ)‖ * koebeK :=
      norm_deriv_le_koebeK hr (hd z hz) (hi z hz) (by
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hxz)
    calc ‖deriv f (x : ℂ)‖ ≤ ‖deriv f (z : ℂ)‖ * koebeK := hstep
      _ ≤ ‖deriv f (y : ℂ)‖ * koebeK ^ n * koebeK :=
          mul_le_mul_of_nonneg_right (ih z hz y hy hzy) koebeK_pos.le
      _ = ‖deriv f (y : ℂ)‖ * koebeK ^ (n + 1) := by ring


/-! ### Real marks as real points of the flow -/

section Marks

variable {w : ℝ≥0 → ℝ} {v : ℝ≥0 → ℝ} {y : ℝ}

/-- A mark `v` solving the Loewner equation `v_t = y + ∫₀ᵗ 2/(v − w)` and never meeting the driver gives the forward
solution `v − w` from the real point `y`, on every `[0, T]`. -/
theorem isForwardSol_of_mark (hw : Continuous w) (hv : Continuous v)
    (hveq : ∀ t : ℝ≥0, v t = y + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hne : ∀ t, v t ≠ w t) (T : ℝ) :
    IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) T (fun s => ((v s.toNNReal - w s.toNNReal : ℝ) : ℂ)) := by
  refine ⟨(Complex.continuous_ofReal.comp ((hv.sub hw).comp continuous_real_toNNReal)).continuousOn,
    fun t ht => ⟨?_, ?_⟩⟩
  · exact Complex.ofReal_ne_zero.2 (sub_ne_zero.2 (hne _))
  · have h1 : (∫ s in (0 : ℝ)..t, (2 : ℂ) / ((v s.toNNReal - w s.toNNReal : ℝ) : ℂ)) =
        ((∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun s _ => ?_
      push_cast; rfl
    have h2 := hveq t.toNNReal
    rw [Real.coe_toNNReal _ ht.1] at h2
    rw [h1]
    have h3 : ((v t.toNNReal - w t.toNNReal : ℝ) : ℂ) = ((y - w t.toNNReal + ∫ s in (0 : ℝ)..t,
        2 / (v s.toNNReal - w s.toNNReal) : ℝ) : ℂ) := by rw [h2]; ring_nf
    show ((v t.toNNReal - w t.toNNReal : ℝ) : ℂ) = (y : ℂ) - (w t.toNNReal : ℂ) + _
    rw [h3]
    push_cast
    ring

/-- **The derivative at a real mark**: `‖f_T′(y)‖ = exp(−∫₀ᵀ 2/(w − v)²)`. -/
theorem norm_deriv_fwdMap_mark (hw : Continuous w) (hv : Continuous v)
    (hveq : ∀ t : ℝ≥0, v t = y + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hne : ∀ t, v t ≠ w t) {T : ℝ} (hT : 0 ≤ T) :
    ‖deriv (fwdMap (fun s : ℝ => w s.toNNReal) T) (y : ℂ)‖ =
      Real.exp (-∫ s in (0 : ℝ)..T, 2 / (w s.toNNReal - v s.toNNReal) ^ 2) := by
  have hW : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have hu := isForwardSol_of_mark hw hv hveq hne T
  obtain ⟨δ, hδ, hlow, hyy⟩ := ZhanGT4.exists_aliveDisc_self hu hT
  rw [ZhanGT4.deriv_fwdMap_aliveDisc hW hu hδ hlow hyy ⟨hT, le_rfl⟩, Complex.norm_exp]
  congr 1
  rw [logDerivFwd, Complex.neg_re]
  congr 1
  have e : ∫ s in (0 : ℝ)..T, (2 : ℂ) / (fwdMap (fun s : ℝ => w s.toNNReal) s (y : ℂ)) ^ 2 =
      ((∫ s in (0 : ℝ)..T, 2 / (w s.toNNReal - v s.toNNReal) ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hT] at hs
    rw [fwdMap_eq_of_isForwardSol hW hu hs]
    push_cast
    ring
  rw [e, Complex.ofReal_re]

end Marks

/-! ### A positive clearance between a transient trace and a segment it never visits -/

/-- A continuous transient path that never visits a compact real segment stays a positive distance from it. -/
theorem exists_clearance {η : ℝ≥0 → ℂ} (hc : Continuous η) (htr : Tendsto (fun t => ‖η t‖) atTop atTop)
    {a b : ℝ} (havoid : ∀ t, ∀ x ∈ Icc a b, η t ≠ x) :
    ∃ δ > 0, ∀ t, ∀ x ∈ Icc a b, δ ≤ ‖η t - x‖ := by
  set C : ℝ := |a| + |b| + 1 with hC
  obtain ⟨T₀, hT₀⟩ := (htr.eventually_ge_atTop C).exists_forall_of_atTop
  have hK : IsCompact (Icc (0 : ℝ≥0) T₀ ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hne : (Icc (0 : ℝ≥0) T₀ ×ˢ Icc a b).Nonempty ∨ ¬ (Icc a b).Nonempty := by
    by_cases h : (Icc a b).Nonempty
    · exact Or.inl ⟨(0, h.some), ⟨zero_le, zero_le⟩, h.some_mem⟩
    · exact Or.inr h
  have hxb : ∀ x ∈ Icc a b, ‖((x : ℝ) : ℂ)‖ ≤ |a| + |b| := fun x hx => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self b, hx.2, abs_nonneg a]
    · rw [abs_of_nonpos h]; linarith [neg_abs_le a, hx.1, abs_nonneg b]
  rcases hne with hne | hne
  · have hf : ContinuousOn (fun p : ℝ≥0 × ℝ => ‖η p.1 - (p.2 : ℂ)‖) (Icc (0 : ℝ≥0) T₀ ×ˢ Icc a b) :=
      ((hc.comp continuous_fst).sub (Complex.continuous_ofReal.comp continuous_snd)).norm.continuousOn
    obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hf
    have hp0 : 0 < ‖η p.1 - (p.2 : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 (havoid p.1 p.2 hp.2))
    refine ⟨min ‖η p.1 - (p.2 : ℂ)‖ 1, lt_min hp0 one_pos, fun t x hx => ?_⟩
    rcases le_total t T₀ with ht | ht
    · exact (min_le_left _ _).trans (show ‖η p.1 - (p.2 : ℂ)‖ ≤ ‖η (t, x).1 - ((t, x).2 : ℂ)‖ from
        hmin (show (t, x) ∈ Icc (0 : ℝ≥0) T₀ ×ˢ Icc a b from ⟨⟨zero_le, ht⟩, hx⟩))
    · refine (min_le_right _ _).trans ?_
      have h1 := hT₀ t ht
      have h2 := norm_sub_norm_le (η t) (x : ℂ)
      linarith [hxb x hx]
  · exact ⟨1, one_pos, fun t x hx => absurd ⟨x, hx⟩ hne⟩


/-! ### Bounded distortion on one side -/

/-- **Bounded distortion on one side** (Koebe). Let `w` (`w 0 = 0`) have a continuous transient generating trace `η`
on `[0, ∞)`, and let the marks `v i` (`n > 0`, antitone in `i`) solve the Loewner equation from `y i`, stay strictly
left of `w`, while `η` never visits a real point `x ≤ y 0`. Then `∫₀ᵀ (2/(w − vᵢ)² − 2/(w − v_last)²)` is bounded
uniformly in `T`: the Loewner maps are univalent on a fixed neighbourhood of the marks' segment for all times, so their
derivatives `exp(−∫₀ᵀ 2/(w − v)²)` at the marks are comparable (Koebe). -/
theorem exists_side_bound {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (htr : Tendsto (fun t => ‖η t‖) atTop atTop)
    {n : ℕ} (hn : 0 < n) {y : Fin n → ℝ} {v : Fin n → ℝ≥0 → ℝ} (hv : ∀ i, Continuous (v i))
    (hveq : ∀ i (t : ℝ≥0), v i t = y i + ∫ s in (0 : ℝ)..t, 2 / (v i s.toNNReal - w s.toNNReal))
    (hlt : ∀ i t, v i t < w t) (hanti : ∀ t, Antitone fun i => v i t)
    (havoid : ∀ t (x : ℝ), x ≤ y ⟨0, hn⟩ → η t ≠ x) :
    ∃ M : ℝ, ∀ i, ∀ T : ℝ, 0 ≤ T →
      ∫ s in (0 : ℝ)..T, (2 / (w s.toNNReal - v i s.toNNReal) ^ 2 -
        2 / (w s.toNNReal - v ⟨n - 1, Nat.sub_lt hn one_pos⟩ s.toNNReal) ^ 2) ≤ M := by
  set l : Fin n := ⟨n - 1, Nat.sub_lt hn one_pos⟩ with hl
  set o : Fin n := ⟨0, hn⟩ with ho
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  have hy : ∀ i, y i = v i 0 := fun i => by rw [hveq i 0]; simp
  have hseg : ∀ i, y i ∈ Icc (y l) (y o) := fun i => by
    rw [hy, hy, hy]
    exact ⟨hanti 0 (Fin.le_def.2 (by simp only [hl]; omega)), hanti 0 (Fin.le_def.2 (by simp [ho]))⟩
  set a := y l with ha
  set b := y o with hb
  have hab : a ≤ b := (hseg o).1
  have hb0 : b < 0 := by rw [hb, hy]; have := hlt o 0; rwa [hw0] at this
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  obtain ⟨δ, hδ, hcl⟩ := exists_clearance hηc htr (a := a) (b := b) fun t x hx => havoid t x hx.2
  set ρ : ℝ := min (δ / 4) (-b / 4) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (by linarith)
  have hρδ : ρ ≤ δ / 4 := min_le_left _ _
  have hρb : ρ ≤ -b / 4 := min_le_right _ _
  -- the box over the segment avoids the trace
  have hbox1 : ∀ z ∈ Ioo (a - ρ) (b + ρ) ×ℂ Ioo 0 ρ, ∀ t, η t ≠ z := by
    intro z hz t hzt
    rw [Complex.mem_reProdIm] at hz
    set x : ℝ := max a (min z.re b) with hx
    have hxI : x ∈ Icc a b := ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
    have hre : |z.re - x| ≤ ρ := by
      rw [abs_le]; constructor
      · rcases le_total z.re b with h | h
        · rw [hx, min_eq_left h]; rcases le_total a z.re with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith [hz.1.1]
        · rw [hx, min_eq_right h, max_eq_right hab]; linarith [hz.1.2]
      · rcases le_total z.re b with h | h
        · rw [hx, min_eq_left h]; linarith [le_max_right a z.re]
        · rw [hx, min_eq_right h, max_eq_right hab]; linarith [hz.1.2]
    have h1 : ‖η t - (x : ℂ)‖ < δ := by
      rw [hzt]
      calc ‖z - (x : ℂ)‖ ≤ |(z - x).re| + |(z - x).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |z.re - x| + |z.im| := by simp
        _ ≤ ρ + ρ := add_le_add hre (by rw [abs_of_pos hz.2.1]; exact hz.2.2.le)
        _ < δ := by linarith
    exact absurd (hcl t x hxI) (not_le.2 h1)
  -- at every time, the discs around the segment are alive
  have halive : ∀ T : ℝ, 0 ≤ T → ∀ x ∈ Icc a b, ∀ z ∈ ball (x : ℂ) (ρ / 2), ∃ u, IsForwardSol W z T u := by
    intro T hT x hx
    set A : Set ℂ := (fun s : ℝ => η s.toNNReal) '' Icc 0 T with hA
    have hAc : IsCompact A :=
      isCompact_Icc.image_of_continuousOn (hηc.comp continuous_real_toNNReal).continuousOn
    obtain ⟨R, hR⟩ := hAc.isBounded.subset_closedBall 0
    set e : ℝ := min (a - ρ) (-R) - 1 with he
    have hSeg : IsCompact (((↑) : ℝ → ℂ) '' Icc (e - 1) b) := isCompact_Icc.image Complex.continuous_ofReal
    have hdisj : ((↑) : ℝ → ℂ) '' Icc (e - 1) b ⊆ Aᶜ := by
      rintro _ ⟨r, hr, rfl⟩ ⟨s, -, hs⟩
      exact havoid _ r hr.2 hs
    obtain ⟨ε, hε, hεA⟩ := hSeg.exists_thickening_subset_open hAc.isClosed.isOpen_compl hdisj
    have hfill := notMem_fillH_of_boxes hAc.isClosed hR (a := a) (b := b) (e := e) (ε := ε / 2) hρ
      (by positivity) (by rw [he]; linarith [min_le_left (a - ρ) (-R)]) hab
      (by rw [he]; linarith [min_le_right (a - ρ) (-R)])
      (fun w hw hwA => by obtain ⟨s, -, hs⟩ := hwA; exact hbox1 w hw _ hs)
      (fun w hw hwA => by
        rw [Complex.mem_reProdIm] at hw
        refine hεA (mem_thickening_iff.2 ⟨_, ⟨w.re, ⟨hw.1.1.le, hw.1.2.le⟩, rfl⟩, ?_⟩) hwA
        rw [Complex.dist_eq]
        have : w - ((w.re : ℝ) : ℂ) = ((w.im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hw.2.1]
        linarith [hw.2.2])
    have hK : ∀ z ∈ ball (x : ℂ) ρ, 0 < z.im → z ∉ fwdHull W T := by
      intro z hz hzH
      rw [(isLoewnerTrace_of_isGeneratingTrace hη).2.2 T hT]
      refine hfill z ?_
      rw [Complex.mem_reProdIm]
      have h1 : ‖z - (x : ℂ)‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hz
      have hre := (Complex.abs_re_le_norm (z - x)).trans_lt h1
      have him := (Complex.abs_im_le_norm (z - x)).trans_lt h1
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hre him
      rw [abs_lt] at hre him
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hzH, him.2⟩
    exact alive_of_ball hW hW0 hT hρ (by rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.2]) hK
  set N : ℕ := ⌈(b - a) / (ρ / 4)⌉₊ with hN
  refine ⟨N * Real.log koebeK, fun i T hT => ?_⟩
  have hd : ∀ x ∈ Icc a b, DifferentiableOn ℂ (fwdMap W T) (ball (x : ℂ) (ρ / 2)) := fun x hx =>
    differentiableOn_fwdMap_of_alive hW hT (halive T hT x hx)
  have hi : ∀ x ∈ Icc a b, InjOn (fwdMap W T) (ball (x : ℂ) (ρ / 2)) := fun x hx =>
    injOn_fwdMap_of_alive hW hT (halive T hT x hx)
  have hdist : |a - y i| ≤ N * (ρ / 2 / 2) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [(hseg i).1])]
    have h1 : (b - a) / (ρ / 4) ≤ N := Nat.le_ceil _
    rw [div_le_iff₀ (by positivity)] at h1
    linarith [(hseg i).2]
  have hch := norm_deriv_le_chain (r := ρ / 2) (by positivity) hd hi N a ⟨le_rfl, hab⟩ (y i) (hseg i) hdist
  have hne : ∀ j t, v j t ≠ w t := fun j t => (hlt j t).ne
  rw [norm_deriv_fwdMap_mark hw (hv l) (hveq l) (hne l) hT,
    norm_deriv_fwdMap_mark hw (hv i) (hveq i) (hne i) hT] at hch
  have hint : ∀ j, IntervalIntegrable (fun s : ℝ => 2 / (w s.toNNReal - v j s.toNNReal) ^ 2) volume 0 T :=
    fun j => (continuous_const.div (((hw.sub (hv j)).comp continuous_real_toNNReal).pow 2)
      fun s => pow_ne_zero 2 (sub_ne_zero.2 (hlt j _).ne')).intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub (hint i) (hint l)]
  have hlog := Real.log_le_log (Real.exp_pos _) hch
  rw [Real.log_exp, Real.log_mul (Real.exp_pos _).ne' (pow_pos koebeK_pos N).ne', Real.log_exp,
    Real.log_pow] at hlog
  linarith


/-! ### The energy of a change of weights with zero side totals -/

/-- **One side with zero total weight**: if `Σ cᵢ = 0` and `0 < aᵢ ≤ a_last`, then
`2 (Σ cᵢ/aᵢ)² ≤ Σ n cᵢ² (2/aᵢ² − 2/a_last²)` (write `Σ cᵢ/aᵢ = Σ cᵢ(1/aᵢ − 1/a_last)`, then Cauchy–Schwarz and
`(p − q)² ≤ p² − q²` for `p ≥ q ≥ 0`). -/
theorem two_mul_sq_sum_div_le {n : ℕ} (hn : 0 < n) {c a : Fin n → ℝ} (hc : ∑ i, c i = 0)
    (ha : ∀ i, 0 < a i) (hle : ∀ i, a i ≤ a ⟨n - 1, Nat.sub_lt hn one_pos⟩) :
    2 * (∑ i, c i / a i) ^ 2 ≤
      ∑ i, (n * c i ^ 2) * (2 / a i ^ 2 - 2 / a ⟨n - 1, Nat.sub_lt hn one_pos⟩ ^ 2) := by
  set l : Fin n := ⟨n - 1, Nat.sub_lt hn one_pos⟩ with hl
  have hsum : ∑ i, c i / a i = ∑ i, c i * (1 / a i - 1 / a l) := by
    have h0 : ∑ i, c i * (1 / a l) = 0 := by rw [← Finset.sum_mul, hc, zero_mul]
    rw [← sub_zero (∑ i, c i / a i), ← h0, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => c i * (1 / a i - 1 / a l))
  rw [Finset.card_univ, Fintype.card_fin] at hcs
  rw [hsum]
  have hterm : ∀ i, (c i * (1 / a i - 1 / a l)) ^ 2 ≤ c i ^ 2 * (1 / a i ^ 2 - 1 / a l ^ 2) := by
    intro i
    have hal := ha l
    have hpq : 1 / a l ≤ 1 / a i := one_div_le_one_div_of_le (ha i) (hle i)
    have hq : 0 ≤ 1 / a l := by positivity
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [show 1 / a i ^ 2 = (1 / a i) ^ 2 by rw [one_div_pow],
      show 1 / a l ^ 2 = (1 / a l) ^ 2 by rw [one_div_pow]]
    nlinarith
  calc 2 * (∑ i, c i * (1 / a i - 1 / a l)) ^ 2
      ≤ 2 * (n * ∑ i, (c i * (1 / a i - 1 / a l)) ^ 2) := by linarith
    _ ≤ 2 * (n * ∑ i, c i ^ 2 * (1 / a i ^ 2 - 1 / a l ^ 2)) := by
        gcongr with i
        exact hterm i
    _ = ∑ i, (n * c i ^ 2) * (2 / a i ^ 2 - 2 / a l ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **Finite energy of a change of weights with zero side totals** (deterministic). Let `w` (`w 0 = 0`) have a
continuous transient generating trace `η` on `[0, ∞)`; let the left marks `vL` (antitone) and the right marks `vR`
(monotone) solve the Loewner equation, stay strictly on their sides of `w`, and let `η` never visit a real point
`x ≤ yL 0` or `x ≥ yR 0`. For coefficients with `Σ cL = Σ cR = 0`, the energy
`∫₀ᵀ (Σ cLᵢ/(w − vLᵢ) + Σ cRⱼ/(w − vRⱼ))²` is bounded uniformly in `T`. -/
theorem exists_energy_bound {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (htr : Tendsto (fun t => ‖η t‖) atTop atTop)
    {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) {yL : Fin nL → ℝ} {yR : Fin nR → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} (hvL : ∀ i, Continuous (vL i))
    (hvR : ∀ j, Continuous (vR j))
    (hvLeq : ∀ i (t : ℝ≥0), vL i t = yL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal))
    (hvReq : ∀ j (t : ℝ≥0), vR j t = yR j + ∫ s in (0 : ℝ)..t, 2 / (vR j s.toNNReal - w s.toNNReal))
    (hltL : ∀ i t, vL i t < w t) (hltR : ∀ j t, w t < vR j t)
    (hantiL : ∀ t, Antitone fun i => vL i t) (hmonoR : ∀ t, Monotone fun j => vR j t)
    (havoidL : ∀ t (x : ℝ), x ≤ yL ⟨0, hnL⟩ → η t ≠ x) (havoidR : ∀ t (x : ℝ), yR ⟨0, hnR⟩ ≤ x → η t ≠ x)
    (cL : Fin nL → ℝ) (cR : Fin nR → ℝ) (hcL : ∑ i, cL i = 0) (hcR : ∑ j, cR j = 0) :
    ∃ m : ℝ, ∀ T : ℝ, 0 ≤ T → ∫ s in (0 : ℝ)..T,
      (∑ i, cL i / (w s.toNNReal - vL i s.toNNReal) + ∑ j, cR j / (w s.toNNReal - vR j s.toNNReal)) ^ 2 ≤ m := by
  set lL : Fin nL := ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ with hlL
  set lR : Fin nR := ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ with hlR
  obtain ⟨ML, hML⟩ := exists_side_bound hw hw0 hη htr hnL hvL hvLeq hltL hantiL havoidL
  -- the right side, by reflection
  have hRrefl := exists_side_bound (w := -w) (hw.neg) (by simp [hw0]) (LP.isGeneratingTrace_reflect hη)
    (by simpa [LP.reflectC] using htr) hnR (y := fun j => -yR j) (v := fun j => -vR j)
    (fun j => (hvR j).neg) (fun j t => by
      rw [Pi.neg_apply, hvReq j t, neg_add, ← intervalIntegral.integral_neg]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [Pi.neg_apply]
      rw [show -vR j s.toNNReal - -w s.toNNReal = -(vR j s.toNNReal - w s.toNNReal) by ring, div_neg])
    (fun j t => by simp only [Pi.neg_apply]; linarith [hltR j t])
    (fun t j j' hjj' => by simp only [Pi.neg_apply]; linarith [hmonoR t hjj'])
    (fun t x hx he => havoidR t (-x) (by linarith) (by
      have := congrArg LP.reflectC he
      rw [LP.reflectC_reflectC] at this
      rw [this]; simp [LP.reflectC]))
  obtain ⟨MR, hMR⟩ := hRrefl
  have hMR' : ∀ j, ∀ T : ℝ, 0 ≤ T → ∫ s in (0 : ℝ)..T, (2 / (vR j s.toNNReal - w s.toNNReal) ^ 2 -
      2 / (vR lR s.toNNReal - w s.toNNReal) ^ 2) ≤ MR := fun j T hT => by
    have := hMR j T hT
    simp only [Pi.neg_apply, neg_sub_neg] at this
    convert this using 3
  set KL : ℝ := ∑ i, (nL * cL i ^ 2) * ML with hKL
  set KR : ℝ := ∑ j, (nR * cR j ^ 2) * MR with hKR
  refine ⟨KL + KR, fun T hT => ?_⟩
  -- the pointwise bound
  set gL : Fin nL → ℝ → ℝ := fun i s => 2 / (w s.toNNReal - vL i s.toNNReal) ^ 2 -
    2 / (w s.toNNReal - vL lL s.toNNReal) ^ 2 with hgL
  set gR : Fin nR → ℝ → ℝ := fun j s => 2 / (vR j s.toNNReal - w s.toNNReal) ^ 2 -
    2 / (vR lR s.toNNReal - w s.toNNReal) ^ 2 with hgR
  have hcontL : ∀ i, Continuous (fun s : ℝ => 2 / (w s.toNNReal - vL i s.toNNReal) ^ 2) := fun i =>
    continuous_const.div (((hw.sub (hvL i)).comp continuous_real_toNNReal).pow 2)
      fun s => pow_ne_zero 2 (sub_ne_zero.2 (hltL i _).ne')
  have hcontR : ∀ j, Continuous (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal) ^ 2) := fun j =>
    continuous_const.div ((((hvR j).sub hw).comp continuous_real_toNNReal).pow 2)
      fun s => pow_ne_zero 2 (sub_ne_zero.2 (hltR j _).ne')
  have hgLc : ∀ i, Continuous (gL i) := fun i => (hcontL i).sub (hcontL lL)
  have hgRc : ∀ j, Continuous (gR j) := fun j => (hcontR j).sub (hcontR lR)
  have hpt : ∀ s : ℝ, (∑ i, cL i / (w s.toNNReal - vL i s.toNNReal) +
      ∑ j, cR j / (w s.toNNReal - vR j s.toNNReal)) ^ 2 ≤
      ∑ i, (nL * cL i ^ 2) * gL i s + ∑ j, (nR * cR j ^ 2) * gR j s := by
    intro s
    have hL := two_mul_sq_sum_div_le hnL hcL (a := fun i => w s.toNNReal - vL i s.toNNReal)
      (fun i => sub_pos.2 (hltL i _)) (fun i => sub_le_sub_left (hantiL _ (Fin.le_def.2 (by
        show (i : ℕ) ≤ nL - 1; omega))) _)
    have hR := two_mul_sq_sum_div_le hnR hcR (a := fun j => vR j s.toNNReal - w s.toNNReal)
      (fun j => sub_pos.2 (hltR j _)) (fun j => sub_le_sub_right (hmonoR _ (Fin.le_def.2 (by
        show (j : ℕ) ≤ nR - 1; omega))) _)
    have hRe : ∑ j, cR j / (w s.toNNReal - vR j s.toNNReal) = -∑ j, cR j / (vR j s.toNNReal - w s.toNNReal) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← div_neg, neg_sub]
    rw [hRe]
    simp only [hgL, hgR]
    nlinarith [sq_nonneg ((∑ i, cL i / (w s.toNNReal - vL i s.toNNReal)) +
      (∑ j, cR j / (vR j s.toNNReal - w s.toNNReal)))]
  have hlhs : Continuous fun s : ℝ => (∑ i, cL i / (w s.toNNReal - vL i s.toNNReal) +
      ∑ j, cR j / (w s.toNNReal - vR j s.toNNReal)) ^ 2 := by
    refine Continuous.pow ((continuous_finsetSum _ fun i _ => continuous_const.div
      ((hw.sub (hvL i)).comp continuous_real_toNNReal) fun s => (sub_ne_zero.2 (hltL i _).ne')).add
      (continuous_finsetSum _ fun j _ => continuous_const.div
      ((hw.sub (hvR j)).comp continuous_real_toNNReal) fun s => (sub_ne_zero.2 (hltR j _).ne))) 2
  have hint : ∀ i, IntervalIntegrable (gL i) volume 0 T := fun i => (hgLc i).intervalIntegrable 0 T
  have hintR : ∀ j, IntervalIntegrable (gR j) volume 0 T := fun j => (hgRc j).intervalIntegrable 0 T
  calc ∫ s in (0 : ℝ)..T, (∑ i, cL i / (w s.toNNReal - vL i s.toNNReal) +
        ∑ j, cR j / (w s.toNNReal - vR j s.toNNReal)) ^ 2
      ≤ ∫ s in (0 : ℝ)..T, (∑ i, (nL * cL i ^ 2) * gL i s + ∑ j, (nR * cR j ^ 2) * gR j s) :=
        intervalIntegral.integral_mono_on hT (hlhs.intervalIntegrable 0 T)
          (((continuous_finsetSum _ fun i _ => continuous_const.mul (hgLc i)).add
            (continuous_finsetSum _ fun j _ => continuous_const.mul (hgRc j))).intervalIntegrable 0 T)
          fun s _ => hpt s
    _ = (∑ i, ∫ s in (0 : ℝ)..T, (nL * cL i ^ 2) * gL i s) +
          ∑ j, ∫ s in (0 : ℝ)..T, (nR * cR j ^ 2) * gR j s := by
        have h1 : IntervalIntegrable (fun s => ∑ i, (nL * cL i ^ 2) * gL i s) volume 0 T :=
          (continuous_finsetSum _ fun i _ => continuous_const.mul (hgLc i)).intervalIntegrable 0 T
        have h2 : IntervalIntegrable (fun s => ∑ j, (nR * cR j ^ 2) * gR j s) volume 0 T :=
          (continuous_finsetSum _ fun j _ => continuous_const.mul (hgRc j)).intervalIntegrable 0 T
        rw [intervalIntegral.integral_add h1 h2,
          intervalIntegral.integral_finsetSum fun i _ => (hint i).const_mul _,
          intervalIntegral.integral_finsetSum fun j _ => (hintR j).const_mul _]
    _ ≤ KL + KR := by
        rw [hKL, hKR]
        refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun j _ => ?_)
        · rw [intervalIntegral.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (hML i T hT) (by positivity)
        · rw [intervalIntegral.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (hMR' j T hT) (by positivity)

end InteractingSLE.Supp8.GB8
