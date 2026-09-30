import QuantumZipper.Proofs.Thm18.G1FMAdm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE round 2 (energy), part 1: the pulled-back Neumann kernel on a small disc

For a map `f` holomorphic on `ℍ` whose derivative is `M₂`-Lipschitz on a closed disc
`D = B̄(c, r) ⊆ ℍ` we write `f x − f y = q(x, y) (x − y)` with
`q(x, y) = ∫_0^1 f'(y + t (x − y)) dt` (`G1FM2.fmQ`, `fmQ_spec`); then `‖q − f'(c)‖ ≤ M₂ r` and
`q` is `M₂`-Lipschitz in its first argument. Hence the kernel difference
`Ek f x y = neumannH x y − neumannH (f x) (f y)` is, off the diagonal, Lipschitz in `x`
(`G1FM2.abs_ek_sub_le`): it is `−log ‖q‖ + log ‖x − ȳ‖ − log ‖f x − conj (f y)‖`.

This is the classical fact that the pulled-back Neumann Green's function of `ℍ` is
`−log |x − y|` plus a smooth function near the diagonal (conformal invariance of the GFF,
Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), §2), done by hand with
elementary estimates (own argument, AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM2

/-- `|log u − log v| ≤ |u − v| / a` for `u, v ≥ a > 0`. -/
theorem abs_log_sub_log_le {a u v : ℝ} (ha : 0 < a) (hu : a ≤ u) (hv : a ≤ v) :
    |Real.log u - Real.log v| ≤ |u - v| / a := by
  have hu0 : 0 < u := ha.trans_le hu
  have hv0 : 0 < v := ha.trans_le hv
  have h1 : Real.log u - Real.log v ≤ (u - v) / v := by
    rw [← Real.log_div hu0.ne' hv0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
    have e : u / v - 1 = (u - v) / v := by field_simp
    linarith
  have h2 : Real.log v - Real.log u ≤ (v - u) / u := by
    rw [← Real.log_div hv0.ne' hu0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
    have e : v / u - 1 = (v - u) / u := by field_simp
    linarith
  rw [abs_le]
  constructor
  · have : (v - u) / u ≤ |u - v| / a := by
      rw [div_le_div_iff₀ hu0 ha]
      have := neg_abs_le (u - v)
      have hv' : v - u ≤ |u - v| := by rw [abs_sub_comm]; exact le_abs_self _
      nlinarith [abs_nonneg (u - v)]
    linarith
  · have : (u - v) / v ≤ |u - v| / a := by
      rw [div_le_div_iff₀ hv0 ha]
      have hu' : u - v ≤ |u - v| := le_abs_self _
      nlinarith [abs_nonneg (u - v)]
    linarith

/-- The difference quotient as an average of the derivative along the segment. -/
def fmQ (f : ℂ → ℂ) (x y : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, deriv f (y + (t : ℂ) * (x - y))

theorem seg_mem {c : ℂ} {r : ℝ} {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : y + (t : ℂ) * (x - y) ∈ closedBall c r := by
  have e : y + (t : ℂ) * (x - y) = (1 - t) • y + t • x := by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]; ring
  rw [e]
  exact (convex_closedBall c r) hy hx (by linarith [ht.2]) ht.1 (by ring)

variable {f : ℂ → ℂ} {c : ℂ} {r M₂ : ℝ}

theorem closedBall_subset_H (hr : r < c.im) : closedBall c r ⊆ H := by
  intro z hz
  have h1 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, ← dist_eq_norm] at h1
  show 0 < z.im
  linarith [neg_abs_le (z.im - c.im), mem_closedBall.1 hz]

/-- `f x − f y = q(x, y) (x − y)` on the disc. -/
theorem fmQ_spec (hd : DifferentiableOn ℂ f H) (hr : r < c.im) {x y : ℂ}
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) : f x - f y = fmQ f x y * (x - y) := by
  have hDH := closedBall_subset_H hr
  have hcont : ContinuousOn (deriv f) H := (hd.deriv isOpen_H).continuousOn
  set p : ℝ → ℂ := fun t => y + (t : ℂ) * (x - y) with hp
  have hpc : Continuous p := by rw [hp]; fun_prop
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => f (p t))
      (deriv f (p t) * (x - y)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hpt : p t ∈ H := hDH (seg_mem hx hy ht)
    have h1 : HasDerivAt p (x - y) t := by
      have := (((hasDerivAt_id t).ofReal_comp).mul_const (x - y)).const_add y
      simpa [hp] using this
    have h2 : HasDerivAt f (deriv f (p t)) (p t) :=
      (hd.differentiableAt (isOpen_H.mem_nhds hpt)).hasDerivAt
    exact h2.comp t h1
  have hint : IntervalIntegrable (fun t => deriv f (p t) * (x - y)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul ?_ continuousOn_const
    exact hcont.comp hpc.continuousOn fun t ht => hDH (seg_mem hx hy ht)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [hp, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero,
    add_sub_cancel] at this
  rw [← this, intervalIntegral.integral_mul_const]
  rfl

/-- Integrability of `f'` along the segment. -/
theorem intervalIntegrable_seg (hd : DifferentiableOn ℂ f H) (hr : r < c.im) {x y : ℂ}
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    IntervalIntegrable (fun t : ℝ => deriv f (y + (t : ℂ) * (x - y))) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  exact ((hd.deriv isOpen_H).continuousOn).comp (by fun_prop)
    fun t ht => closedBall_subset_H hr (seg_mem hx hy ht)

/-- `q` stays within `M₂ r` of `f'(c)`. -/
theorem norm_fmQ_sub_le (hd : DifferentiableOn ℂ f H) (hr : r < c.im)
    (hL : ∀ x ∈ closedBall c r, ‖deriv f x - deriv f c‖ ≤ M₂ * r) {x y : ℂ}
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    ‖fmQ f x y - deriv f c‖ ≤ M₂ * r := by
  have e : fmQ f x y - deriv f c =
      ∫ t in (0 : ℝ)..1, (deriv f (y + (t : ℂ) * (x - y)) - deriv f c) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_seg hd hr hx hy)
      intervalIntegrable_const]
    simp [fmQ]
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := M₂ * r)
    (f := fun t : ℝ => deriv f (y + (t : ℂ) * (x - y)) - deriv f c) fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      exact hL _ (seg_mem hx hy ⟨ht.1.le, ht.2⟩)
  simpa using this

/-- `q` is `M₂`-Lipschitz in its first argument. -/
theorem norm_fmQ_sub_fmQ_le (hd : DifferentiableOn ℂ f H) (hr : r < c.im) (hM : 0 ≤ M₂)
    (hL : ∀ x ∈ closedBall c r, ∀ x' ∈ closedBall c r,
      ‖deriv f x - deriv f x'‖ ≤ M₂ * ‖x - x'‖) {x x' y : ℂ}
    (hx : x ∈ closedBall c r) (hx' : x' ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    ‖fmQ f x y - fmQ f x' y‖ ≤ M₂ * ‖x - x'‖ := by
  have e : fmQ f x y - fmQ f x' y = ∫ t in (0 : ℝ)..1,
      (deriv f (y + (t : ℂ) * (x - y)) - deriv f (y + (t : ℂ) * (x' - y))) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_seg hd hr hx hy)
      (intervalIntegrable_seg hd hr hx' hy)]
    rfl
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := M₂ * ‖x - x'‖)
    (f := fun t : ℝ => deriv f (y + (t : ℂ) * (x - y)) - deriv f (y + (t : ℂ) * (x' - y)))
    fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      refine (hL _ (seg_mem hx hy ht') _ (seg_mem hx' hy ht')).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hM
      have e2 : y + (t : ℂ) * (x - y) - (y + (t : ℂ) * (x' - y)) = (t : ℂ) * (x - x') := by ring
      rw [e2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  simpa using this

/-- The kernel difference of the pull-back. -/
def ek (f : ℂ → ℂ) (x y : ℂ) : ℝ := neumannH x y - neumannH (f x) (f y)

theorem neumannH_comp (f : ℂ → ℂ) (x y : ℂ) : neumannH (f x) (f y) = neumannH x y - ek f x y := by
  unfold ek; ring

theorem norm_sub_conj_ge {x y : ℂ} : x.im + y.im ≤ ‖x - conj y‖ := by
  have := Complex.abs_im_le_norm (x - conj y)
  rw [Complex.sub_im, Complex.conj_im] at this
  linarith [le_abs_self (x.im - -y.im)]

/-- Off the diagonal, `ek` is the smooth expression. -/
theorem ek_eq (hd : DifferentiableOn ℂ f H) (hinj : InjOn f H) (hr : r < c.im) {x y : ℂ}
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) (hxy : x ≠ y) :
    ek f x y = Real.log ‖fmQ f x y‖ - Real.log ‖x - conj y‖ + Real.log ‖f x - conj (f y)‖ := by
  have hs := fmQ_spec hd hr hx hy
  have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hq : fmQ f x y ≠ 0 := by
    intro h0
    rw [h0, zero_mul, sub_eq_zero] at hs
    exact hxy (hinj (closedBall_subset_H hr hx) (closedBall_subset_H hr hy) hs)
  unfold ek neumannH
  rw [hs, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hq) (norm_ne_zero_iff.2 hxy')]
  ring

theorem im_ge_of_mem {x : ℂ} (hx : x ∈ closedBall c r) : c.im - r ≤ x.im := by
  have h1 : |(x - c).im| ≤ ‖x - c‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, ← dist_eq_norm] at h1
  linarith [neg_abs_le (x.im - c.im), mem_closedBall.1 hx]

/-- **Off-diagonal Lipschitz bound** for the kernel difference in its first argument. -/
theorem abs_ek_sub_le (hd : DifferentiableOn ℂ f H) (hinj : InjOn f H) (hr : r < c.im)
    (hM : 0 ≤ M₂) (hL : ∀ x ∈ closedBall c r, ∀ x' ∈ closedBall c r,
      ‖deriv f x - deriv f x'‖ ≤ M₂ * ‖x - x'‖)
    {α M₁ c₀ : ℝ} (hα : 0 < α) (hq : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      α ≤ ‖fmQ f x y‖) (hc₀ : 0 < c₀) (him : ∀ x ∈ closedBall c r, c₀ ≤ (f x).im)
    (hM₁ : ∀ x ∈ closedBall c r, ∀ x' ∈ closedBall c r, ‖f x - f x'‖ ≤ M₁ * ‖x - x'‖)
    {x x' y : ℂ} (hx : x ∈ closedBall c r) (hx' : x' ∈ closedBall c r)
    (hy : y ∈ closedBall c r) (hxy : x ≠ y) (hx'y : x' ≠ y) :
    |ek f x y - ek f x' y| ≤ (M₂ / α + 1 / (2 * (c.im - r)) + M₁ / (2 * c₀)) * ‖x - x'‖ := by
  rw [ek_eq hd hinj hr hx hy hxy, ek_eq hd hinj hr hx' hy hx'y]
  have hr0 : 0 < c.im - r := by linarith
  have t1 : |Real.log ‖fmQ f x y‖ - Real.log ‖fmQ f x' y‖| ≤ M₂ / α * ‖x - x'‖ := by
    refine (abs_log_sub_log_le hα (hq x hx y hy) (hq x' hx' y hy)).trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hα]
    exact (abs_norm_sub_norm_le _ _).trans (norm_fmQ_sub_fmQ_le hd hr hM hL hx hx' hy)
  have lb : ∀ z ∈ closedBall c r, 2 * (c.im - r) ≤ ‖z - conj y‖ := fun z hz => by
    have := norm_sub_conj_ge (x := z) (y := y)
    linarith [im_ge_of_mem hz, im_ge_of_mem hy]
  have t2 : |Real.log ‖x - conj y‖ - Real.log ‖x' - conj y‖| ≤
      1 / (2 * (c.im - r)) * ‖x - x'‖ := by
    refine (abs_log_sub_log_le (by positivity) (lb x hx) (lb x' hx')).trans ?_
    rw [one_div_mul_eq_div, div_le_div_iff_of_pos_right (by positivity)]
    refine (abs_norm_sub_norm_le _ _).trans (le_of_eq ?_)
    congr 1; ring
  have lb2 : ∀ z ∈ closedBall c r, 2 * c₀ ≤ ‖f z - conj (f y)‖ := fun z hz => by
    have := norm_sub_conj_ge (x := f z) (y := f y)
    linarith [him z hz, him y hy]
  have t3 : |Real.log ‖f x - conj (f y)‖ - Real.log ‖f x' - conj (f y)‖| ≤
      M₁ / (2 * c₀) * ‖x - x'‖ := by
    refine (abs_log_sub_log_le (by positivity) (lb2 x hx) (lb2 x' hx')).trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have e : f x - conj (f y) - (f x' - conj (f y)) = f x - f x' := by ring
    rw [e]; exact hM₁ x hx x' hx'
  have e : Real.log ‖fmQ f x y‖ - Real.log ‖x - conj y‖ + Real.log ‖f x - conj (f y)‖ -
      (Real.log ‖fmQ f x' y‖ - Real.log ‖x' - conj y‖ + Real.log ‖f x' - conj (f y)‖) =
      (Real.log ‖fmQ f x y‖ - Real.log ‖fmQ f x' y‖) -
        (Real.log ‖x - conj y‖ - Real.log ‖x' - conj y‖) +
        (Real.log ‖f x - conj (f y)‖ - Real.log ‖f x' - conj (f y)‖) := by ring
  rw [e, add_mul, add_mul]
  refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add t1 t2)) t3)

/-! ## Constants for the selected maps on compact parts of `ℍ` -/

/-- The compact region `{‖z‖ ≤ R, Im z ≥ h}`. -/
def reg (R h : ℝ) : Set ℂ := {z | ‖z‖ ≤ R ∧ h ≤ z.im}

theorem isCompact_reg (R h : ℝ) : IsCompact (reg R h) := by
  have : reg R h = closedBall (0 : ℂ) R ∩ {z | h ≤ z.im} := by
    ext z; simp [reg, dist_zero_right]
  rw [this]
  exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)

theorem reg_subset_H {R h : ℝ} (hh : 0 < h) : reg R h ⊆ H := fun z hz =>
  show 0 < z.im from hh.trans_le hz.2

/-- **Uniform constants** of a selected map on a compact region. -/
theorem psi_consts {ψ : ℂ → ℂ} (hψ : G1RC.PsiGood ψ) (R h : ℝ) (hh : 0 < h) :
    ∃ M₀ M₁ M₂ a₀ c₀ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ 0 < a₀ ∧ 0 < c₀ ∧
      ∀ z ∈ reg R h, ‖ψ z‖ ≤ M₀ ∧ ‖deriv ψ z‖ ≤ M₁ ∧ a₀ ≤ ‖deriv ψ z‖ ∧
        ‖deriv (deriv ψ) z‖ ≤ M₂ ∧ c₀ ≤ (ψ z).im := by
  obtain ⟨-, hd, hinj, hmaps, -⟩ := hψ
  have hK := isCompact_reg R h
  have hKH := reg_subset_H (R := R) hh
  have h1 : DifferentiableOn ℂ (deriv ψ) H := hd.deriv isOpen_H
  have h2 : DifferentiableOn ℂ (deriv (deriv ψ)) H := h1.deriv isOpen_H
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hd.continuousOn.mono hKH)
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn (h1.continuousOn.mono hKH)
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn (h2.continuousOn.mono hKH)
  rcases (reg R h).eq_empty_or_nonempty with he | hne
  · refine ⟨|M₀|, |M₁|, |M₂|, 1, 1, abs_nonneg _, abs_nonneg _, abs_nonneg _, one_pos, one_pos,
      fun z hz => ?_⟩
    rw [he] at hz; exact absurd hz (notMem_empty z)
  obtain ⟨z₁, hz₁, hmin₁⟩ := hK.exists_isMinOn hne
    ((h1.continuousOn.mono hKH).norm)
  obtain ⟨z₂, hz₂, hmin₂⟩ := hK.exists_isMinOn hne
    (Complex.continuous_im.comp_continuousOn (hd.continuousOn.mono hKH))
  have ha : 0 < ‖deriv ψ z₁‖ :=
    norm_pos_iff.2 (CA.Koebe.deriv_ne_zero_of_injOn isOpen_H hd hinj (hKH hz₁))
  have hc : 0 < (ψ z₂).im := hmaps (hKH hz₂)
  refine ⟨|M₀|, |M₁|, |M₂|, _, _, abs_nonneg _, abs_nonneg _, abs_nonneg _, ha, hc,
    fun z hz => ⟨(hM₀ z hz).trans (le_abs_self _), (hM₁ z hz).trans (le_abs_self _),
      hmin₁ hz, (hM₂ z hz).trans (le_abs_self _), hmin₂ hz⟩⟩

/-- Mean value bound on a disc inside the region. -/
theorem norm_sub_le_of_deriv {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g H) {M : ℝ} {c : ℂ} {r : ℝ}
    (hr : r < c.im) (hb : ∀ z ∈ closedBall c r, ‖deriv g z‖ ≤ M) {x x' : ℂ}
    (hx : x ∈ closedBall c r) (hx' : x' ∈ closedBall c r) : ‖g x - g x'‖ ≤ M * ‖x - x'‖ :=
  (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => hg.differentiableAt (isOpen_H.mem_nhds (closedBall_subset_H hr hz))) hb hx' hx

end G1FM2
end Thm18Asm
end QuantumZipper
