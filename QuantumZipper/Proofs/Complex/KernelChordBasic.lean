import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The disk model of the slit plane `ℂ \ [0,∞)` (EXT-CA KT2, helper)

KT2 (DECISIONS D7) applies the kernel theorem KT1 to doubled domains whose uniformizers map
onto `ℂ \ [0,∞)` with `−1 ↦ −1`. KT1 is stated for maps from the unit disk, so we need an
explicit conformal map `slitDiskMap : 𝔻 → ℂ \ [0,∞)` with `0 ↦ −1` and positive derivative
at `0`:
`slitDiskMap w = −((1 − w)/(1 + w))²`, the Möbius map `w ↦ (1 − w)/(1 + w)` of `𝔻` onto the
right half-plane followed by `u ↦ −u²` of the right half-plane onto `ℂ \ [0,∞)`.

These are textbook elementary conformal maps (e.g. Ahlfors, *Complex Analysis*, 3rd ed.,
§3.4 and §4.3); the Lean proof is an own elementary proof.
-/

noncomputable section

open Set Metric Filter Topology Complex

namespace QuantumZipper.CA.Kernel

/-- The slit plane `ℂ \ [0,∞)`. -/
def slitNeg : Set ℂ := {z | -z ∈ slitPlane}

/-- The Möbius map `w ↦ (1 − w)/(1 + w)` (an involution, `𝔻 → {Re > 0}`). -/
def halfMob (w : ℂ) : ℂ := (1 - w) / (1 + w)

/-- The conformal map `𝔻 → ℂ \ [0,∞)`, `0 ↦ −1`, `slitDiskMap'(0) = 4`. -/
def slitDiskMap (w : ℂ) : ℂ := -(halfMob w) ^ 2

theorem isOpen_slitNeg : IsOpen slitNeg := isOpen_slitPlane.preimage continuous_neg

theorem one_add_ne_zero_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 1 + w ≠ 0 := by
  intro h
  have : w = -1 := by linear_combination h
  rw [this, mem_ball_zero_iff, norm_neg, norm_one] at hw
  exact lt_irrefl _ hw

theorem one_add_ne_zero_of_re_pos {u : ℂ} (hu : 0 < u.re) : 1 + u ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem halfMob_re_pos {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 0 < (halfMob w).re := by
  have hne := one_add_ne_zero_of_mem_ball hw
  have hn : 0 < normSq (1 + w) := normSq_pos.2 hne
  have hw2 : w.re * w.re + w.im * w.im < 1 := by
    have h1 : ‖w‖ ^ 2 < 1 := by
      rw [mem_ball_zero_iff] at hw; nlinarith [norm_nonneg w]
    rw [← normSq_eq_norm_sq, normSq_apply] at h1
    exact h1
  rw [halfMob, div_re]
  simp only [sub_re, one_re, add_re, sub_im, one_im, add_im]
  rw [← add_div]
  apply div_pos _ hn
  nlinarith

theorem halfMob_halfMob {u : ℂ} (hu : 1 + u ≠ 0) : halfMob (halfMob u) = u := by
  unfold halfMob
  have h2 : (1 + u) + (1 - u) ≠ 0 := by
    ring_nf; norm_num
  rw [div_eq_iff (by rw [one_add_div hu]; exact div_ne_zero h2 hu)]
  field_simp
  ring

theorem norm_halfMob_lt_one {u : ℂ} (hu : 0 < u.re) : halfMob u ∈ ball (0 : ℂ) 1 := by
  have hne := one_add_ne_zero_of_re_pos hu
  rw [mem_ball_zero_iff, halfMob, norm_div, div_lt_one (norm_pos_iff.2 hne)]
  have : normSq (1 - u) < normSq (1 + u) := by
    simp only [normSq_apply, sub_re, one_re, sub_im, one_im, add_re, add_im]
    nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at this
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

theorem halfMob_injOn : InjOn halfMob (ball (0 : ℂ) 1) := by
  intro w hw v hv h
  have h1 := one_add_ne_zero_of_mem_ball hw
  have h2 := one_add_ne_zero_of_mem_ball hv
  unfold halfMob at h
  rw [div_eq_div_iff h1 h2] at h
  linear_combination -h / 2

theorem sq_mem_slitPlane_of_re_pos {u : ℂ} (hu : 0 < u.re) : u ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : u.im = 0
  · left
    rw [sq, mul_re, h]
    nlinarith
  · right
    rw [sq, mul_im]
    intro h'
    have : 2 * u.re * u.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · linarith
    · exact h h3

theorem mapsTo_slitDiskMap : MapsTo slitDiskMap (ball (0 : ℂ) 1) slitNeg := fun w hw => by
  show -slitDiskMap w ∈ slitPlane
  rw [slitDiskMap, neg_neg]
  exact sq_mem_slitPlane_of_re_pos (halfMob_re_pos hw)

theorem injOn_slitDiskMap : InjOn slitDiskMap (ball (0 : ℂ) 1) := by
  intro w hw v hv h
  apply halfMob_injOn hw hv
  have h' : (halfMob w - halfMob v) * (halfMob w + halfMob v) = 0 := by
    unfold slitDiskMap at h; linear_combination -h
  rcases mul_eq_zero.1 h' with h1 | h1
  · linear_combination h1
  · exfalso
    have := congrArg Complex.re h1
    simp only [add_re, zero_re] at this
    linarith [halfMob_re_pos hw, halfMob_re_pos hv]

/-- Every point of `ℂ \ [0,∞)` is `−u²` with `Re u > 0`. -/
theorem exists_re_pos_sq {z : ℂ} (hz : z ∈ slitNeg) : ∃ u : ℂ, 0 < u.re ∧ -u ^ 2 = z := by
  have hz' : -z ∈ slitPlane := hz
  have hne : -z ≠ 0 := slitPlane_ne_zero hz'
  refine ⟨exp (log (-z) / 2), ?_, ?_⟩
  · rw [exp_re]
    apply mul_pos (Real.exp_pos _)
    apply Real.cos_pos_of_mem_Ioo
    have h1 := neg_pi_lt_arg (-z)
    have h2 : arg (-z) < Real.pi :=
      lt_of_le_of_ne (arg_le_pi _) (mem_slitPlane_iff_arg.1 hz').1
    have : (log (-z) / 2).im = arg (-z) / 2 := by
      simp [div_ofNat_im, log_im]
    rw [this]
    constructor <;> linarith
  · rw [← exp_nat_mul]
    push_cast
    rw [show (2 : ℂ) * (log (-z) / 2) = log (-z) by ring, exp_log hne, neg_neg]

theorem image_slitDiskMap : slitDiskMap '' ball (0 : ℂ) 1 = slitNeg := by
  refine Subset.antisymm mapsTo_slitDiskMap.image_subset fun z hz => ?_
  obtain ⟨u, hu, rfl⟩ := exists_re_pos_sq hz
  exact ⟨halfMob u, norm_halfMob_lt_one hu, by
    rw [slitDiskMap, halfMob_halfMob (one_add_ne_zero_of_re_pos hu)]⟩

theorem slitDiskMap_zero : slitDiskMap 0 = -1 := by
  simp [slitDiskMap, halfMob]

theorem hasDerivAt_halfMob {w : ℂ} (hw : 1 + w ≠ 0) :
    HasDerivAt halfMob (-2 / (1 + w) ^ 2) w := by
  have h := HasDerivAt.div (HasDerivAt.const_sub 1 (hasDerivAt_id w))
    (HasDerivAt.const_add 1 (hasDerivAt_id w)) hw
  exact h.congr_deriv (by simp only [id]; ring)

theorem hasDerivAt_slitDiskMap {w : ℂ} (hw : 1 + w ≠ 0) :
    HasDerivAt slitDiskMap (-(2 * halfMob w * (-2 / (1 + w) ^ 2))) w := by
  have h := HasDerivAt.neg ((hasDerivAt_halfMob hw).pow 2)
  exact h.congr_deriv (by norm_num)

theorem differentiableOn_slitDiskMap : DifferentiableOn ℂ slitDiskMap (ball (0 : ℂ) 1) :=
  fun _w hw => (hasDerivAt_slitDiskMap (one_add_ne_zero_of_mem_ball hw)).differentiableAt
    |>.differentiableWithinAt

theorem deriv_slitDiskMap_zero : deriv slitDiskMap 0 = 4 := by
  rw [(hasDerivAt_slitDiskMap (by norm_num)).deriv]
  simp [halfMob]
  norm_num

end QuantumZipper.CA.Kernel
