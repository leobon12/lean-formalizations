/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeStage

/-!
# A free real point has one real preimage on each side of the chart's tip

Packet PROVE-AUX61-NOJUMP (round 22, component F), deterministic. Let `c` be a conformal chart, `g` a continuous
extension of `c⁻¹` to `ℍ̄` with `‖w‖ ≤ C₁ ‖g w‖ + C₂`, `g 0 = R`, and `x₀ ≠ R` a real point near which `ℍ` lies in the
chart's domain. Then `x₀` is not read back from both a negative and a positive real point
(**`not_two_sides`**): the forward image of a small free half-disc at `x₀` is connected and contains points near both,
so it meets the imaginary axis; those points cluster at `0` (where `g` is `R`) or in `ℍ` (where `g` is in `ℍ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Ne

variable {c : Chart} {g : ℂ → ℂ}

/-- **A point of the forward image of a free half-disc near each real preimage.** -/
theorem exists_mem_fwd_near (hcc : c.IsConformal) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {y x₀ : ℝ} (hy : g (y : ℂ) = x₀) {ρ : ℝ} (hρ : 0 < ρ) {U : Set ℝ} (hU : IsOpen U)
    (hyU : y ∈ U) :
    ∃ w ∈ H, w.re ∈ U ∧ g w ∈ ball (x₀ : ℂ) ρ ∧ c.1 (g w) = w := by
  have h1 : Tendsto g (𝓝[H] (y : ℂ)) (𝓝 (x₀ : ℂ)) := by
    rw [← hy]; exact tendsto_g_H hgc (y : ℂ) (by simp)
  have h2 : ∀ᶠ w in 𝓝[H] (y : ℂ), w.re ∈ U := by
    have : Complex.re ⁻¹' U ∈ 𝓝 (y : ℂ) :=
      Complex.continuous_re.continuousAt.preimage_mem_nhds (by rw [Complex.ofReal_re]; exact hU.mem_nhds hyU)
    exact nhdsWithin_le_nhds this
  have : (𝓝[H] (y : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((y : ℝ) : ℂ).im by simp)
  have hev : ∀ᶠ w in 𝓝[H] (y : ℂ), w ∈ H ∧ w.re ∈ U ∧ g w ∈ ball (x₀ : ℂ) ρ := by
    filter_upwards [self_mem_nhdsWithin, h2, h1 (ball_mem_nhds _ hρ)] with w hw1 hw2 hw3 using ⟨hw1, hw2, hw3⟩
  obtain ⟨w, hwH, hwU, hwb⟩ := hev.exists
  refine ⟨w, hwH, hwU, hwb, ?_⟩
  rw [hgi hwH]
  exact hcc.2.2 w hwH

/-- **A free real point is not read back from both sides of the tip.** -/
theorem not_two_sides (hcc : c.IsConformal) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {C₁ C₂ : ℝ} (hprop : ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) {R x₀ : ℝ}
    (hg0 : g 0 = R) (hx₀ : x₀ ≠ R) {r : ℝ} (hr : 0 < r) (hfree : ∀ z ∈ H, dist z (x₀ : ℂ) < r → z ∈ c.2.1 '' H)
    {y₀ y₁ : ℝ} (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) (h0 : g (y₀ : ℂ) = x₀) (h1 : g (y₁ : ℂ) = x₀) : False := by
  -- for every `n`, a point of the imaginary axis read back within `1/(n+1)` of `x₀`
  have hpts : ∀ n : ℕ, ∃ v ∈ H, v.re = 0 ∧ g v ∈ ball (x₀ : ℂ) (min r (1 / (n + 1))) := by
    intro n
    set ρ : ℝ := min r (1 / (n + 1)) with hρ
    have hρ0 : 0 < ρ := lt_min hr (by positivity)
    set D : Set ℂ := ball (x₀ : ℂ) ρ ∩ H with hD
    have hDc : IsPreconnected D := ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
    have hDsub : D ⊆ c.dom := by
      intro z hz
      show z ∈ interior (c.2.1 '' H)
      have hopen : IsOpen D := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
      refine interior_maximal (fun z' hz' => hfree z' hz'.2 ?_) hopen hz
      exact lt_of_lt_of_le (mem_ball.1 hz'.1) (min_le_left _ _)
    have hcD : ContinuousOn c.1 D := hcc.differentiableOn_fwd.continuousOn.mono hDsub
    have hI : IsPreconnected (Complex.re '' (c.1 '' D)) :=
      (hDc.image _ hcD).image _ Complex.continuous_re.continuousOn
    obtain ⟨w₀, hw₀H, hw₀U, hw₀b, hw₀e⟩ := exists_mem_fwd_near hcc hgc hgi h0 hρ0 isOpen_Iio (show y₀ ∈ Iio 0 from hy₀)
    obtain ⟨w₁, hw₁H, hw₁U, hw₁b, hw₁e⟩ := exists_mem_fwd_near hcc hgc hgi h1 hρ0 isOpen_Ioi (show y₁ ∈ Ioi 0 from hy₁)
    have hm₀ : w₀.re ∈ Complex.re '' (c.1 '' D) := ⟨w₀, ⟨g w₀, ⟨hw₀b, by rw [hgi hw₀H]; exact hcc.2.1 hw₀H⟩, hw₀e⟩, rfl⟩
    have hm₁ : w₁.re ∈ Complex.re '' (c.1 '' D) := ⟨w₁, ⟨g w₁, ⟨hw₁b, by rw [hgi hw₁H]; exact hcc.2.1 hw₁H⟩, hw₁e⟩, rfl⟩
    obtain ⟨_, ⟨z, hzD, rfl⟩, hre⟩ := hI.ordConnected.out hm₀ hm₁ ⟨le_of_lt hw₀U, le_of_lt hw₁U⟩
    obtain ⟨u, huH, hu⟩ := hfree z hzD.2 (lt_of_lt_of_le (mem_ball.1 hzD.1) (min_le_left _ _))
    have hcu : c.1 z = u := by rw [← hu]; exact hcc.2.2 u huH
    refine ⟨u, huH, by rw [← hcu]; exact hre, ?_⟩
    rw [hgi huH, hu]
    exact hzD.1
  choose v hvH hvre hvb using hpts
  -- the points are bounded
  set M : ℝ := |C₁| * (|x₀| + 1) + |C₂| with hM
  have hvM : ∀ n, v n ∈ closedBall (0 : ℂ) M ∩ {z : ℂ | 0 ≤ z.im} := by
    intro n
    refine ⟨?_, le_of_lt (show (0 : ℝ) < (v n).im from hvH n)⟩
    rw [mem_closedBall_zero_iff]
    have hgv : ‖g (v n)‖ ≤ |x₀| + 1 := by
      have h := mem_ball.1 (hvb n)
      have h' : dist (g (v n)) (x₀ : ℂ) < 1 := lt_of_lt_of_le h ((min_le_right _ _).trans (by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
      have := norm_le_of_mem_closedBall (show g (v n) ∈ closedBall ((x₀ : ℝ) : ℂ) 1 from le_of_lt h')
      simpa [Complex.norm_real] using this
    have h1 := hprop (v n) (le_of_lt (hvH n))
    have h2 : C₁ * ‖g (v n)‖ ≤ |C₁| * (|x₀| + 1) :=
      (le_abs_self C₁ |>.trans_eq rfl |> fun _ => by
        calc C₁ * ‖g (v n)‖ ≤ |C₁| * ‖g (v n)‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
          _ ≤ |C₁| * (|x₀| + 1) := mul_le_mul_of_nonneg_left hgv (abs_nonneg _))
    linarith [le_abs_self C₂]
  have hKc : IsCompact (closedBall (0 : ℂ) M ∩ {z : ℂ | 0 ≤ z.im}) :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  obtain ⟨v₀, hv₀K, φ, hφ, hlim⟩ := hKc.tendsto_subseq hvM
  -- the limit is read back to `x₀`
  have hgl : Tendsto (fun n => g (v (φ n))) atTop (𝓝 (g v₀)) :=
    (hgc v₀ hv₀K.2).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n =>
      le_of_lt (show (0 : ℝ) < (v (φ n)).im from hvH _)⟩)
  have hgx : Tendsto (fun n => g (v (φ n))) atTop (𝓝 (x₀ : ℂ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop) (fun n => dist_nonneg) fun n => ?_
    exact (le_of_lt (mem_ball.1 (hvb (φ n)))).trans (min_le_right _ _)
  have hv₀ : g v₀ = x₀ := tendsto_nhds_unique hgl hgx
  have hre0 : v₀.re = 0 := by
    have := (Complex.continuous_re.tendsto v₀).comp hlim
    exact tendsto_nhds_unique this (by simp only [Function.comp_def, hvre]; exact tendsto_const_nhds)
  rcases (show (0 : ℝ) ≤ v₀.im from hv₀K.2).lt_or_eq with him | him
  · have hH : g v₀ ∈ H := by rw [hgi him]; exact hcc.2.1 him
    rw [hv₀] at hH
    exact absurd hH (by show ¬ (0 : ℝ) < ((x₀ : ℝ) : ℂ).im; simp)
  · have h0' : v₀ = 0 := Complex.ext (by simp [hre0]) (by simp [← him])
    rw [h0', hg0] at hv₀
    exact hx₀ (by exact_mod_cast hv₀.symm)

end InteractingSLE.Theorem14.SB.Ne
