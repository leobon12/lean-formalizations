/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Observable
import InteractingSLE.Spec.Ito.Localize
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Aux. lemma 104: the test function and its Itô generator

Packet PROVE-STRIPSYS3. Aux. lemma 104 (`source/spec/p337-384.md` L308–L345, no common-seed entrance with
opposite-sign Jacobi parameters) is proved in physical time with one smooth test function of the coordinates
`Λ = (L − √κ B, D)` and of `B` (`L = W − V^L`, `D = V^R − V^L`):

`Φ(Λ, x) = ψ(D) · (L/D) − c · ψ(D) · (log D + n)`, with `L = Λ₁ + √κ x`,

where `ψ` is a smooth cutoff, `0` below `α` and `1` above `β` (`cut`). Since `ψ` vanishes near `D ≤ α` and `α > 0`,
`Φ` is smooth on all of `(ℝ × ℝ) × ℝ` (`contDiff_phi`). It is affine in `x`, so its Itô generator is its derivative
along the absolutely continuous coordinates (`itoGen_phi`). In the source's logarithmic clock `v = log D` the two
terms are `U = L/D` and `c · v`; here `ψ` replaces the restart at the first time `D = e^{−n}`.

**`itoGen_phi_nonneg`** (the drift bound of the proof of Aux. 104, with `c = m/4`, `m = min(a, −b)`): if `a ≥ m`,
`−b ≥ m`, `|e| ≤ C`, `C d ≤ 2m`, `0 < L`, `0 < R`, `D = L + R ≤ d`, and `log D + n ≤ 0` wherever `ψ' ≠ 0`
(`β ≤ e^{−n}`), then the generator along the density `(a/L − ρ_R/R + e, 2/L + 2/R)` is nonnegative. The
computation (added here): with `U D' = 2/R`, the generator is
`ψ′ D′ (U − c(log D + n)) + (ψ/D)(a/L − b/R + e − (m/2)(1/L + 1/R))`, and `a/L − b/R ≥ m(1/L + 1/R) ≥ 4m/D`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace Sec7

namespace Aux104

/-! ### The cutoff -/

/-- The smooth cutoff `ψ(y) = s((y − α)/(β − α))`: `0` for `y ≤ α`, `1` for `y ≥ β`. -/
def cut (α β y : ℝ) : ℝ := Real.smoothTransition ((y - α) / (β - α))

variable {α β : ℝ}

theorem cut_eq_zero (hαβ : α < β) {y : ℝ} (hy : y ≤ α) : cut α β y = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem cut_eq_one (hαβ : α < β) {y : ℝ} (hy : β ≤ y) : cut α β y = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).2 (by linarith))

theorem cut_nonneg (y : ℝ) : 0 ≤ cut α β y := Real.smoothTransition.nonneg _

theorem cut_le_one (y : ℝ) : cut α β y ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_cut {k : ℕ∞} : ContDiff ℝ k (cut α β) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem monotone_cut (hαβ : α < β) : Monotone (cut α β) := fun x y hxy =>
  Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))

theorem deriv_cut_nonneg (hαβ : α < β) (y : ℝ) : 0 ≤ deriv (cut α β) y :=
  (monotone_cut hαβ).deriv_nonneg

theorem cut_eventuallyEq_zero (hαβ : α < β) {y : ℝ} (hy : y < α) : cut α β =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds hy] with z hz using cut_eq_zero hαβ (le_of_lt hz)

theorem cut_eventuallyEq_one (hαβ : α < β) {y : ℝ} (hy : β < y) : cut α β =ᶠ[𝓝 y] fun _ => 1 := by
  filter_upwards [Ioi_mem_nhds hy] with z hz using cut_eq_one hαβ (le_of_lt hz)

theorem deriv_cut_eq_zero_of_lt (hαβ : α < β) {y : ℝ} (hy : y < α) : deriv (cut α β) y = 0 := by
  rw [(cut_eventuallyEq_zero hαβ hy).deriv_eq]; exact deriv_const _ _

theorem deriv_cut_eq_zero_of_gt (hαβ : α < β) {y : ℝ} (hy : β < y) : deriv (cut α β) y = 0 := by
  rw [(cut_eventuallyEq_one hαβ hy).deriv_eq]; exact deriv_const _ _

theorem hasDerivAt_cut (y : ℝ) : HasDerivAt (cut α β) (deriv (cut α β) y) y :=
  (contDiff_cut (k := 1).differentiable one_ne_zero y).hasDerivAt

/-! ### The two profiles `ψ(y)/y` and `ψ(y)(log y + n)` -/

/-- `g₁(y) = ψ(y)/y`. -/
def g1 (α β y : ℝ) : ℝ := cut α β y / y

/-- `g₂(y) = ψ(y)(log y + n)`. -/
def g2 (α β n y : ℝ) : ℝ := cut α β y * (Real.log y + n)

/-- `g₁′(y) = ψ′(y)/y − ψ(y)/y²`. -/
def g1' (α β y : ℝ) : ℝ := deriv (cut α β) y / y - cut α β y / y ^ 2

/-- `g₂′(y) = ψ′(y)(log y + n) + ψ(y)/y`. -/
def g2' (α β n y : ℝ) : ℝ := deriv (cut α β) y * (Real.log y + n) + cut α β y / y

variable {n : ℝ}

theorem g1_eventuallyEq_zero (hαβ : α < β) {y : ℝ} (hy : y < α) : g1 α β =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [cut_eventuallyEq_zero hαβ hy] with z hz
  simp only [g1, hz, zero_div]

theorem g2_eventuallyEq_zero (hαβ : α < β) {y : ℝ} (hy : y < α) : g2 α β n =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [cut_eventuallyEq_zero hαβ hy] with z hz
  simp only [g2, hz, zero_mul]

theorem hasDerivAt_g1 (hα : 0 < α) (hαβ : α < β) (y : ℝ) : HasDerivAt (g1 α β) (g1' α β y) y := by
  rcases lt_or_ge y α with hy | hy
  · have h0 : g1' α β y = 0 := by
      simp only [g1', deriv_cut_eq_zero_of_lt hαβ hy, cut_eq_zero hαβ hy.le, zero_div, sub_zero]
    rw [h0]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq (g1_eventuallyEq_zero hαβ hy)
  · have hy0 : y ≠ 0 := (lt_of_lt_of_le hα hy).ne'
    have h : HasDerivAt (fun z => cut α β z / z) ((deriv (cut α β) y * y - cut α β y * 1) / y ^ 2) y :=
      (hasDerivAt_cut (α := α) (β := β) y).div (hasDerivAt_id' y) hy0
    show HasDerivAt (fun z => cut α β z / z) _ y
    refine h.congr_deriv ?_
    unfold g1'
    field_simp

theorem hasDerivAt_g2 (hα : 0 < α) (hαβ : α < β) (y : ℝ) : HasDerivAt (g2 α β n) (g2' α β n y) y := by
  rcases lt_or_ge y α with hy | hy
  · have h0 : g2' α β n y = 0 := by
      simp only [g2', deriv_cut_eq_zero_of_lt hαβ hy, cut_eq_zero hαβ hy.le, zero_div, zero_mul, add_zero]
    rw [h0]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq (g2_eventuallyEq_zero hαβ hy)
  · have hy0 : y ≠ 0 := (lt_of_lt_of_le hα hy).ne'
    have h : HasDerivAt (fun z => cut α β z * (Real.log z + n))
        (deriv (cut α β) y * (Real.log y + n) + cut α β y * y⁻¹) y :=
      (hasDerivAt_cut (α := α) (β := β) y).mul ((Real.hasDerivAt_log hy0).add_const n)
    show HasDerivAt (fun z => cut α β z * (Real.log z + n)) _ y
    refine h.congr_deriv ?_
    unfold g2'
    rw [div_eq_mul_inv]

theorem contDiff_g1 (hα : 0 < α) (hαβ : α < β) {k : ℕ∞} : ContDiff ℝ k (g1 α β) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases lt_or_ge y α with hy | hy
  · exact contDiffAt_const.congr_of_eventuallyEq (g1_eventuallyEq_zero hαβ hy)
  · exact (contDiff_cut.contDiffAt).div contDiffAt_id (lt_of_lt_of_le hα hy).ne'

theorem contDiff_g2 (hα : 0 < α) (hαβ : α < β) {k : ℕ∞} : ContDiff ℝ k (g2 α β n) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases lt_or_ge y α with hy | hy
  · exact contDiffAt_const.congr_of_eventuallyEq (g2_eventuallyEq_zero hαβ hy)
  · exact (contDiff_cut.contDiffAt).mul
      ((Real.contDiffAt_log.2 (lt_of_lt_of_le hα hy).ne').add contDiffAt_const)

/-! ### The test function -/

/-- **The test function** `Φ((l, D), x) = g₁(D) (l + √κ x) − c g₂(D)`. -/
def phi (κ c α β n : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  g1 α β p.1.2 * (p.1.1 + Real.sqrt κ * p.2) - c * g2 α β n p.1.2

variable {κ c : ℝ}

theorem contDiff_phi (hα : 0 < α) (hαβ : α < β) {k : ℕ∞} : ContDiff ℝ k (phi κ c α β n) := by
  unfold phi
  have h2 : ContDiff ℝ k fun p : (ℝ × ℝ) × ℝ => p.1.2 := contDiff_snd.comp contDiff_fst
  have h1 : ContDiff ℝ k fun p : (ℝ × ℝ) × ℝ => p.1.1 := contDiff_fst.comp contDiff_fst
  exact (((contDiff_g1 hα hαβ).comp h2).mul (h1.add (contDiff_const.mul contDiff_snd))).sub
    (contDiff_const.mul ((contDiff_g2 hα hαβ).comp h2))

/-- The derivative of `Φ` along the coordinates. -/
theorem partialFst_phi (hα : 0 < α) (hαβ : α < β) (p : (ℝ × ℝ) × ℝ) (v : ℝ × ℝ) :
    Ito.partialFst (phi κ c α β n) p v =
      g1' α β p.1.2 * v.2 * (p.1.1 + Real.sqrt κ * p.2) + g1 α β p.1.2 * v.1 - c * (g2' α β n p.1.2 * v.2) := by
  refine Ito.partialFst_eq_of_hasDerivAt ((contDiff_phi (k := 1) hα hαβ).differentiable one_ne_zero p) ?_
  have hD : HasDerivAt (fun t : ℝ => p.1.2 + t * v.2) v.2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add p.1.2
  have hL : HasDerivAt (fun t : ℝ => p.1.1 + t * v.1 + Real.sqrt κ * p.2) v.1 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_add p.1.1).add_const (Real.sqrt κ * p.2)
  have hg1 : HasDerivAt (fun t : ℝ => g1 α β (p.1.2 + t * v.2)) (g1' α β p.1.2 * v.2) 0 :=
    (hasDerivAt_g1 hα hαβ p.1.2).comp_of_eq (0 : ℝ) hD (by simp)
  have hg2 : HasDerivAt (fun t : ℝ => g2 α β n (p.1.2 + t * v.2)) (g2' α β n p.1.2 * v.2) 0 :=
    (hasDerivAt_g2 (n := n) hα hαβ p.1.2).comp_of_eq (0 : ℝ) hD (by simp)
  have h := (hg1.mul hL).sub (hg2.const_mul c)
  have e : (fun t : ℝ => phi κ c α β n (p.1 + t • v, p.2)) = fun t =>
      g1 α β (p.1.2 + t * v.2) * (p.1.1 + t * v.1 + Real.sqrt κ * p.2) - c * g2 α β n (p.1.2 + t * v.2) := by
    funext t
    simp only [phi, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [e]
  refine h.congr_deriv ?_
  simp only [zero_mul, add_zero]

/-- `Φ` is affine in `x`: its second `x`-derivative vanishes. -/
theorem partialSndSnd_phi (hα : 0 < α) (hαβ : α < β) (p : (ℝ × ℝ) × ℝ) :
    Ito.partialSndSnd (phi κ c α β n) p = 0 := by
  have hsnd : ∀ y : ℝ, Ito.partialSnd (phi κ c α β n) (p.1, y) = g1 α β p.1.2 * Real.sqrt κ := by
    intro y
    refine Ito.partialSnd_eq_of_hasDerivAt ((contDiff_phi (k := 1) hα hαβ).differentiable one_ne_zero _) ?_
    have h : HasDerivAt (fun y : ℝ => g1 α β p.1.2 * (p.1.1 + Real.sqrt κ * y) - c * g2 α β n p.1.2)
        (g1 α β p.1.2 * Real.sqrt κ) y := by
      simpa using (((hasDerivAt_id y).const_mul (Real.sqrt κ)).const_add p.1.1).const_mul (g1 α β p.1.2)
        |>.sub_const (c * g2 α β n p.1.2)
    exact h
  exact Ito.partialSndSnd_eq_of_hasDerivAt ((contDiff_phi (k := 2) hα hαβ).contDiffAt)
    (Eventually.of_forall fun y => hsnd y) (hasDerivAt_const _ _)

/-- **The Itô generator of `Φ`.** -/
theorem itoGen_phi (hα : 0 < α) (hαβ : α < β) (p : (ℝ × ℝ) × ℝ) (v : ℝ × ℝ) :
    Ito.itoGen (phi κ c α β n) p v =
      g1' α β p.1.2 * v.2 * (p.1.1 + Real.sqrt κ * p.2) + g1 α β p.1.2 * v.1 - c * (g2' α β n p.1.2 * v.2) := by
  rw [Ito.itoGen, partialFst_phi hα hαβ, partialSndSnd_phi hα hαβ, mul_zero, add_zero]

/-- The generator of `Φ` regrouped at a point with gaps `L, R > 0`: the cutoff term and the main term. -/
theorem itoGen_phi_eq (hα : 0 < α) (hαβ : α < β) {a ρR e L R l x : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hl : l + Real.sqrt κ * x = L) :
    Ito.itoGen (phi κ c α β n) ((l, L + R), x) (a / L - ρR / R + e, 2 / L + 2 / R) =
      deriv (cut α β) (L + R) * (2 / L + 2 / R) * (L / (L + R) - c * (Real.log (L + R) + n)) +
        cut α β (L + R) / (L + R) * (a / L - (ρR + 2) / R + e - c * (2 / L + 2 / R)) := by
  rw [itoGen_phi hα hαβ]
  simp only [g1', g1, g2']
  rw [hl]
  have hD : L + R ≠ 0 := (add_pos hL hR).ne'
  field_simp
  ring

/-- **The drift bound of Aux. lemma 104**: the Itô generator of `Φ` (with `c = m/4`) along the density
`(a/L − ρ_R/R + e, 2/L + 2/R)` of the coordinates is nonnegative while `D = L + R ≤ d`. -/
theorem itoGen_phi_nonneg (hα : 0 < α) (hαβ : α < β) {m a ρR e C d L R l x : ℝ} (hm : 0 < m) (ha : m ≤ a)
    (hb : m ≤ -(ρR + 2)) (he : |e| ≤ C) (hCd : C * d ≤ 2 * m) (hL : 0 < L) (hR : 0 < R) (hDd : L + R ≤ d)
    (hβn : Real.log β + n ≤ 0) (hl : l + Real.sqrt κ * x = L) :
    0 ≤ Ito.itoGen (phi κ (m / 4) α β n) ((l, L + R), x) (a / L - ρR / R + e, 2 / L + 2 / R) := by
  rw [itoGen_phi_eq hα hαβ hL hR hl]
  have hD : 0 < L + R := add_pos hL hR
  refine add_nonneg ?_ ?_
  · -- the cutoff term: `ψ′ ≥ 0`, and `log D + n ≤ 0` where `ψ′ ≠ 0`
    rcases le_or_gt (L + R) β with hDβ | hDβ
    · refine mul_nonneg (mul_nonneg (deriv_cut_nonneg hαβ _) (by positivity)) ?_
      have hlog : Real.log (L + R) + n ≤ 0 := by linarith [Real.log_le_log hD hDβ]
      have : 0 ≤ L / (L + R) := by positivity
      nlinarith
    · rw [deriv_cut_eq_zero_of_gt hαβ hDβ]; simp
  · -- the main term: `a/L − b/R − (m/2)(1/L + 1/R) ≥ (m/2)(1/L + 1/R) ≥ 2m/D ≥ C ≥ −e`
    refine mul_nonneg (div_nonneg (cut_nonneg _) hD.le) ?_
    have h1 : m / L ≤ a / L := div_le_div_of_nonneg_right ha hL.le
    have h2 : m / R ≤ -(ρR + 2) / R := div_le_div_of_nonneg_right hb hR.le
    have h3 : 4 / (L + R) ≤ 1 / L + 1 / R := by
      rw [div_add_div _ _ hL.ne' hR.ne', div_le_div_iff₀ hD (mul_pos hL hR)]
      nlinarith [sq_nonneg (L - R)]
    have h4 : 4 / d ≤ 4 / (L + R) := div_le_div_of_nonneg_left (by norm_num) hD hDd
    have hd : 0 < d := lt_of_lt_of_le hD hDd
    have h5 : C ≤ m / 2 * (4 / d) := by
      rw [show m / 2 * (4 / d) = 2 * m / d by ring, le_div_iff₀ hd]; exact hCd
    have h6 : -C ≤ e := neg_le_of_abs_le he
    have e1 : (ρR + 2) / R = -(-(ρR + 2) / R) := by ring
    have e2 : m / 4 * (2 / L + 2 / R) = m / 2 * (1 / L + 1 / R) := by ring
    have e3 : m / L + m / R = m * (1 / L + 1 / R) := by ring
    rw [e1, e2]
    nlinarith

end Aux104

end Sec7

end InteractingSLE
