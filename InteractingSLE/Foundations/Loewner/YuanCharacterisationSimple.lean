import InteractingSLE.Foundations.Loewner.YuanCharacterisationSlit
import InteractingSLE.Foundations.Loewner.YuanCharacterisationBeurling

/-!
# [Law05, Proposition 3.76] for simple paths, and [Yua22, Theorem 1.1 (iii) ⇒ (i)]

Packet PROVE-YUAN-M23. G. F. Lawler, *Conformally invariant processes in the plane* (2005),
Proposition 3.76: if `A` is a compact `ℍ`-hull and `γ` a curve with `γ(0) ∈ A ∪ ℝ`,
`γ(0, 1] ⊆ ℍ \ A`, then `diam g_A(γ(0, 1]) ≤ c d^{1/2} r^{1/2}`, `d = diam γ(0, 1]`.

`simpleCurveLocalGrowth` proves it, with a universal constant, for the case used by [Yua22,
Theorem 1.1 (iii) ⇒ (i)]: `A = fill(γ[0, s])` and the curve `γ|[s, t]`, `γ` simple
(`SimpleCurveLocalGrowth`). Then `exists_loewner_of_simpleApprox` is the unconditional form of
`YuanCharacterisation.exists_loewner_of_tendstoUniformlyOn`: **a uniform limit of simple paths
with strictly increasing fillings is a Loewner trace after the capacity time change, with a
continuous driver**.

## Proof of the estimate (`0 < s < t`)

Write `A = fill(γ[0, s]) = γ((0, s])` (simple paths do not separate `ℍ`, `fillH_image_eq`),
`g = g_A`, `F_A` the continuous extension of `g⁻¹` to `ℍ̄`.

1. **The tip** (`exists_tendsto_mapOut_tip`): `g(γ(u)) → U ∈ ℝ` as `u ↓ s`, `F_A(U) = γ(s)`.
2. **The slit** `B = g(γ((s, t]))` is the filling of the simple path `β = g ∘ γ(s + ·)` (with
   `β(0) = U`), the increment hull: `g_{A₂} = g_B ∘ g` for `A₂ = fill(γ[0, t])`.
3. **Koebe** (`IsBdryExt.norm_sub_le`): the real points `x` with `F_B(x) ∈ closure B` form an
   interval `[a, b]`, and `diam B ≤ 12 (b − a)`.
4. **Harmonic measure from `∞`**: `φ(z) = ω_ℍ(g_B(g(z)), (a, b))` is harmonic in `V = ℍ \ A₂`,
   vanishes at boundary points of `V` away from `γ([s, t]) ⊆ B̄(γ(s), d)` (because
   `F_A ∘ F_B` maps `[a, b]` into `γ([s, t])`) and at `∞`. The complement of `V` contains the
   continuum `ℝ ∪ γ([0, s])` through `γ(s)`. So (`le_mul_hmIoo`)
   `φ(iY) ≤ C₁ √(d/R) ω_ℍ(iY, (−10R, 10R)) ≤ 20 C₁ √(dR) / (π Y)`, while
   `φ(iY) ≥ (b − a)(Y − M)/(π (Y + K)²)`; letting `Y → ∞`, `b − a ≤ 20 C₁ √(dR)`.
5. Hence `|g(γ(u)) − U| ≤ 240 C₁ √(d R)` for `u ∈ (s, t]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped Real

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace YuanCharacterisation

/-! ### Two auxiliary lemmas -/

/-- If `D (Y − M) Y ≤ Q (Y + K)²` for all large `Y`, then `D ≤ Q`. -/
theorem le_of_forall_ge_mul {D Q M K : ℝ}
    (h : ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, D * (Y - M) * Y ≤ Q * (Y + K) ^ 2) : D ≤ Q := by
  obtain ⟨Y₀, hY₀⟩ := h
  have hinv : Tendsto (fun Y : ℝ => Y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h1 : Tendsto (fun Y : ℝ => D * (1 - M * Y⁻¹)) atTop (𝓝 (D * (1 - M * 0))) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)).const_mul D
  have h2 : Tendsto (fun Y : ℝ => Q * (1 + K * Y⁻¹) ^ 2) atTop (𝓝 (Q * (1 + K * 0) ^ 2)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).pow 2).const_mul Q
  simp only [mul_zero, sub_zero, add_zero, one_pow, mul_one] at h1 h2
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [eventually_ge_atTop (max Y₀ 1)] with Y hY
  have hY1 : 1 ≤ Y := le_of_max_le_right hY
  have hYpos : 0 < Y := by linarith
  have := hY₀ Y (le_of_max_le_left hY)
  have e1 : D * (1 - M * Y⁻¹) = D * (Y - M) * Y / Y ^ 2 := by field_simp
  have e2 : Q * (1 + K * Y⁻¹) ^ 2 = Q * (Y + K) ^ 2 / Y ^ 2 := by field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right this (by positivity)

/-- The Poisson kernel at a point far from a real point is small. -/
theorem poissonKernelH_le_inv {ξ : ℂ} {t r : ℝ} (hr : 0 < r) (hξt : r ≤ ‖ξ - t‖)
    (hξ : 0 ≤ ξ.im) : poissonKernelH ξ t ≤ ξ.im / (π * r ^ 2) := by
  unfold poissonKernelH
  exact div_le_div_of_nonneg_left hξ (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hξt 2) Real.pi_pos.le)

/-- `P(ξ, t) ≤ 1/(π r)` when `|ξ − t| ≥ r`. -/
theorem poissonKernelH_le_inv' {ξ : ℂ} {t r : ℝ} (hr : 0 < r) (hξt : r ≤ ‖ξ - t‖)
    (hξ : 0 ≤ ξ.im) : poissonKernelH ξ t ≤ 1 / (π * r) := by
  unfold poissonKernelH
  have hpos : 0 < ‖ξ - t‖ := hr.trans_le hξt
  have him : ξ.im ≤ ‖ξ - t‖ := by
    have := abs_im_le_norm (ξ - t)
    rw [sub_im, ofReal_im, sub_zero, abs_of_nonneg hξ] at this
    exact this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : ξ.im * (π * r) ≤ ‖ξ - t‖ * (π * ‖ξ - t‖) := by
    apply mul_le_mul him (mul_le_mul_of_nonneg_left hξt Real.pi_pos.le) (by positivity)
      (norm_nonneg _)
  nlinarith [Real.pi_pos]

/-- **Boundary decay** of `z ↦ ω_ℍ(g₂(z), (a, b))` on `V`, at boundary points of `V` outside
`B̄(c, d)`, when `g₂ : V → ℍ` has a continuous left inverse `F₂` on `ℍ̄` mapping `ℍ` into `V` and
`[a, b]` into `B̄(c, d)`. -/
theorem hmIoo_comp_decay {V : Set ℂ} (hV : IsOpen V) {g₂ F₂ : ℂ → ℂ} {a b d M₂ : ℝ} {c : ℂ}
    (hgV : ∀ z ∈ V, g₂ z ∈ H) (hFg : ∀ z ∈ V, F₂ (g₂ z) = z) (hFc : ContinuousOn F₂ Hbar)
    (hFH : ∀ ξ ∈ H, F₂ ξ ∈ V) (hFab : ∀ x : ℝ, x ∈ Icc a b → ‖F₂ x - c‖ ≤ d)
    (hbd : ∀ z ∈ V, ‖g₂ z‖ ≤ ‖z‖ + M₂) :
    ∀ p ∈ frontier V, d < ‖p - c‖ → ∀ ε > 0, ∃ δ > 0, ∀ z ∈ V, dist z p < δ →
      hmIoo a b (g₂ z) ≤ ε := by
  intro p hp hpc ε hε
  by_contra hcon
  push Not at hcon
  have hab' : a ≤ b := by
    by_contra hba
    obtain ⟨z, hz, -, hzε⟩ := hcon 1 one_pos
    have : Ioo a b = ∅ := Ioo_eq_empty (not_lt.2 (not_le.1 hba).le)
    simp only [hmIoo, this, measure_empty, ENNReal.toReal_zero] at hzε
    linarith
  have hcon' : ∀ n : ℕ, ∃ z ∈ V, dist z p < 1 / ((n : ℝ) + 1) ∧ ε < hmIoo a b (g₂ z) :=
    fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose z hzV hzd hzε using hcon'
  have hzlim : Tendsto z atTop (𝓝 p) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg)
      (fun n => (hzd n).le) ?_)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  set ξ : ℕ → ℂ := fun n => g₂ (z n) with hξ
  have hξbd : ∀ n, ξ n ∈ closedBall (0 : ℂ) (‖p‖ + 1 + M₂) := by
    intro n
    rw [mem_closedBall, dist_zero_right]
    have h1 := hbd (z n) (hzV n)
    have h2 : ‖z n‖ ≤ ‖p‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (z n) p
      have h3 : dist (z n) p < 1 := (hzd n).trans_le (by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      rw [dist_eq_norm] at h3
      linarith
    linarith
  obtain ⟨ξl, -, φ, hφ, hξlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hξbd
  have hξl : ξl ∈ Hbar :=
    isClosed_Hbar.mem_of_tendsto hξlim (Eventually.of_forall fun n => H_subset_Hbar
      (hgV _ (hzV _)))
  have hpF : p = F₂ ξl := by
    have h1 : Tendsto (fun n => F₂ (ξ (φ n))) atTop (𝓝 (F₂ ξl)) :=
      ((hFc ξl hξl).tendsto).comp (tendsto_nhdsWithin_iff.2 ⟨hξlim, Eventually.of_forall
        fun n => H_subset_Hbar (hgV _ (hzV _))⟩)
    have h2 : Tendsto (fun n => F₂ (ξ (φ n))) atTop (𝓝 p) := by
      refine (hzlim.comp hφ.tendsto_atTop).congr fun n => ?_
      simp only [Function.comp, hξ]
      exact (hFg _ (hzV _)).symm
    exact tendsto_nhds_unique h2 h1
  have hpV : p ∉ V := by rw [hV.frontier_eq] at hp; exact hp.2
  by_cases hξH : ξl ∈ H
  · exact hpV (hpF ▸ hFH ξl hξH)
  have hξim : ξl.im = 0 := le_antisymm (not_lt.1 hξH) hξl
  have hξeq : ξl = (ξl.re : ℂ) := eq_ofReal_re_of_im_eq_zero hξim
  by_cases hab : ξl.re ∈ Icc a b
  · have := hFab _ hab
    rw [← hξeq, ← hpF] at this
    linarith
  -- `ξl` is real and outside `[a, b]`: the harmonic measures tend to `0`
  set r : ℝ := max (a - ξl.re) (ξl.re - b) / 2 with hr
  have hrpos : 0 < r := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hab
    rcases hab with h | h
    · have := le_max_left (a - ξl.re) (ξl.re - b); simp only [hr]; linarith
    · have := le_max_right (a - ξl.re) (ξl.re - b); simp only [hr]; linarith
  have hev : ∀ᶠ n in atTop, hmIoo a b (ξ (φ n)) ≤ (ξ (φ n)).im / (π * r ^ 2) * (b - a) := by
    have hclose : ∀ᶠ n in atTop, ‖ξ (φ n) - ξl‖ < r :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hξlim).eventually (gt_mem_nhds hrpos)
    filter_upwards [hclose] with n hn
    have him0 : 0 ≤ (ξ (φ n)).im := le_of_lt (hgV _ (hzV (φ n)))
    refine hmIoo_le hab' (div_nonneg him0 (by positivity)) fun t ht => ?_
    refine poissonKernelH_le_inv hrpos ?_ (le_of_lt (hgV _ (hzV (φ n))))
    have h1 : |(ξ (φ n)).re - ξl.re| < r := by
      have := abs_re_le_norm (ξ (φ n) - ξl)
      rw [sub_re] at this
      linarith
    have h2 : r ≤ |(ξ (φ n)).re - t| := by
      rw [abs_lt] at h1
      rw [mem_Icc, not_and_or, not_le, not_le] at hab
      rcases hab with h | h
      · have : max (a - ξl.re) (ξl.re - b) = a - ξl.re := max_eq_left (by linarith)
        rw [hr, this] at h1 ⊢
        rw [abs_of_neg (by linarith [ht.1])]
        linarith [ht.1]
      · have : max (a - ξl.re) (ξl.re - b) = ξl.re - b := max_eq_right (by linarith)
        rw [hr, this] at h1 ⊢
        rw [abs_of_pos (by linarith [ht.2])]
        linarith [ht.2]
    calc r ≤ |(ξ (φ n)).re - t| := h2
      _ = |(ξ (φ n) - t).re| := by simp
      _ ≤ ‖ξ (φ n) - t‖ := abs_re_le_norm _
  have hlim0 : Tendsto (fun n => (ξ (φ n)).im / (π * r ^ 2) * (b - a)) atTop (𝓝 0) := by
    have : Tendsto (fun n => (ξ (φ n)).im) atTop (𝓝 0) := by
      rw [← hξim]; exact (continuous_im.tendsto _).comp hξlim
    have := (this.div_const (π * r ^ 2)).mul_const (b - a)
    simpa using this
  obtain ⟨n, hn1, hn2⟩ := (hev.and (hlim0.eventually (gt_mem_nhds hε))).exists
  have := hzε (φ n)
  simp only [hξ] at hn1
  linarith

/-! ### The main case `0 < s < t` -/

/-- The comparison statement of `le_mul_hmIoo`, with constant `C₁`. -/
def HmComparison (C₁ : ℝ) : Prop :=
  ∀ (V L : Set ℂ) (c : ℂ) (d R : ℝ) (h : ℂ → ℝ),
    IsOpen V → V ⊆ H → c ∉ V → 0 < d → d ≤ R → ‖c‖ ≤ R → IsClosed L → Disjoint L V →
    IsConnected (closure ((fun z => (z - c)⁻¹) '' (L \ {c}))) → ¬ Bornology.IsBounded L →
    (∃ z ∈ L, z ≠ c ∧ ‖z - c‖ ≤ d / 2) →
    InnerProductSpace.HarmonicOnNhd h V → (∀ z ∈ V, 0 ≤ h z ∧ h z ≤ 1) →
    (∀ p ∈ frontier V, d < ‖p - c‖ → ∀ ε > 0, ∃ δ > 0, ∀ z ∈ V, dist z p < δ → h z ≤ ε) →
    (∀ ε > 0, ∃ M : ℝ, ∀ z ∈ V, M ≤ ‖z‖ → h z ≤ ε) →
    ∀ z ∈ V, 4 * R < ‖z - c‖ → h z ≤ C₁ * √(d / R) * hmIoo (-10 * R) (10 * R) z

theorem le_of_hmIoo_bounds {a b R M₂ C₁ d : ℝ} {g₂ : ℂ → ℂ} {V : Set ℂ} {c : ℂ} (hab : a ≤ b)
    (hR : 0 < R) (hC₁ : 0 ≤ C₁) (hM₂ : 0 ≤ M₂) (hcR : ‖c‖ ≤ R) {Y₁ : ℝ}
    (hYV : ∀ Y : ℝ, Y₁ < Y → (Y : ℂ) * I ∈ V) (hg₂V : ∀ z ∈ V, g₂ z ∈ H)
    (hg₂bd : ∀ z ∈ V, ‖g₂ z - z‖ ≤ M₂)
    (hmain : ∀ z ∈ V, 4 * R < ‖z - c‖ →
      hmIoo a b (g₂ z) ≤ C₁ * √(d / R) * hmIoo (-10 * R) (10 * R) z) :
    b - a ≤ 20 * C₁ * R * √(d / R) := by
  set K := |a| + |b| with hK
  have hK0 : 0 ≤ K := by positivity
  refine le_of_forall_ge_mul (M := M₂) (K := M₂ + K)
    ⟨max (R + 2) (5 * R + 1) + M₂ + |Y₁| + 1, fun Y hY => ?_⟩
  have hY1 : R + 2 ≤ Y := by linarith [le_max_left (R + 2) (5 * R + 1), abs_nonneg Y₁]
  have hY2 : 5 * R + 1 ≤ Y := by linarith [le_max_right (R + 2) (5 * R + 1), abs_nonneg Y₁]
  have hY3 : Y₁ < Y := by
    linarith [le_max_left (R + 2) (5 * R + 1), le_abs_self Y₁]
  have hYpos : 0 < Y := by linarith
  set z : ℂ := (Y : ℂ) * I with hz
  have hzV : z ∈ V := hYV Y hY3
  have hzim : z.im = Y := by simp [hz]
  have hzn : ‖z‖ = Y := by
    rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hYpos]
  have hzc : 4 * R < ‖z - c‖ := by
    have := norm_sub_norm_le z c
    linarith
  have h1 := hmain z hzV hzc
  have h2 : hmIoo (-10 * R) (10 * R) z ≤ 1 / (π * Y) * (10 * R - -10 * R) := by
    refine hmIoo_le (by linarith) (by positivity) fun t' _ => ?_
    refine poissonKernelH_le_inv' hYpos ?_ (by rw [hzim]; exact hYpos.le)
    have := abs_im_le_norm (z - t')
    rw [sub_im, ofReal_im, sub_zero, hzim, abs_of_pos hYpos] at this
    exact this
  set ξ := g₂ z with hξ
  have hξH : ξ ∈ H := hg₂V z hzV
  have hξim : Y - M₂ ≤ ξ.im := by
    have h3 := hg₂bd z hzV
    have h4 := abs_im_le_norm (ξ - z)
    rw [sub_im, hzim] at h4
    have h5 := neg_abs_le (ξ.im - Y)
    linarith
  have hξn : ‖ξ‖ ≤ Y + M₂ := by
    have := norm_le_norm_add_norm_sub' ξ z
    rw [hzn] at this
    linarith [hg₂bd z hzV]
  set W := Y + (M₂ + K) with hW
  have hWpos : 0 < W := by rw [hW]; linarith
  have h3 : ξ.im / (π * W ^ 2) * (b - a) ≤ hmIoo a b ξ := by
    refine le_hmIoo (div_nonneg (le_of_lt hξH) (by positivity)) hξH fun t' ht' => ?_
    unfold poissonKernelH
    have hpos : 0 < ‖ξ - t'‖ := norm_pos_iff.2 fun h' => by
      have := congrArg Complex.im h'
      rw [sub_im, ofReal_im, sub_zero, zero_im] at this
      exact (ne_of_gt hξH) this
    have hle : ‖ξ - t'‖ ≤ W := by
      have h6 := norm_sub_le ξ (t' : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at h6
      have h7 : |t'| ≤ K := by
        rw [abs_le]; constructor <;>
          linarith [ht'.1, ht'.2, neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
      rw [hW]; linarith
    exact div_le_div_of_nonneg_left (le_of_lt hξH) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le hle 2) Real.pi_pos.le)
  have h4 : (b - a) * (Y - M₂) / (π * W ^ 2) ≤ ξ.im / (π * W ^ 2) * (b - a) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right hξim (by linarith)
  have h5 : hmIoo a b ξ ≤ C₁ * √(d / R) * (1 / (π * Y) * (10 * R - -10 * R)) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hchain : (b - a) * (Y - M₂) / (π * W ^ 2) ≤ 20 * C₁ * R * √(d / R) / (π * Y) := by
    calc (b - a) * (Y - M₂) / (π * W ^ 2) ≤ ξ.im / (π * W ^ 2) * (b - a) := h4
      _ ≤ hmIoo a b ξ := h3
      _ ≤ C₁ * √(d / R) * (1 / (π * Y) * (10 * R - -10 * R)) := h5
      _ = 20 * C₁ * R * √(d / R) / (π * Y) := by field_simp; ring
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hchain
  have hpi := Real.pi_pos
  refine le_of_mul_le_mul_left ?_ hpi
  calc π * ((b - a) * (Y - M₂) * Y) = (b - a) * (Y - M₂) * (π * Y) := by ring
    _ ≤ 20 * C₁ * R * √(d / R) * (π * W ^ 2) := hchain
    _ = π * (20 * C₁ * R * √(d / R) * W ^ 2) := by ring

/-- The continuum `ℝ ∪ γ([0, s])` through `γ(s)`, outside `ℍ \ fill(γ[0, t])`. -/
theorem continuum_props {γ : ℝ → ℂ} {s t d : ℝ} (hc : ContinuousOn γ (Icc 0 t))
    (hi : InjOn γ (Icc 0 t)) (h0 : γ 0 = 0) (hH : MapsTo γ (Ioc 0 t) H) (hs : 0 < s)
    (hst : s < t) (hd : 0 < d) :
    IsClosed ({z : ℂ | z.im = 0} ∪ γ '' Icc 0 s) ∧
      Disjoint ({z : ℂ | z.im = 0} ∪ γ '' Icc 0 s) (H \ fillH (γ '' Icc 0 t)) ∧
      IsConnected (({z : ℂ | z.im = 0} ∪ γ '' Icc 0 s) \ {γ s}) ∧
      ¬ Bornology.IsBounded ({z : ℂ | z.im = 0} ∪ γ '' Icc 0 s) ∧
      ∃ z ∈ {z : ℂ | z.im = 0} ∪ γ '' Icc 0 s, z ≠ γ s ∧ ‖z - γ s‖ ≤ d / 2 := by
  have hcs : ContinuousOn γ (Icc 0 s) := hc.mono (Icc_subset_Icc_right hst.le)
  set L : Set ℂ := {z | z.im = 0} ∪ γ '' Icc 0 s with hL
  set V := H \ fillH (γ '' Icc 0 t) with hV
  have hγsH : γ s ∈ H := hH ⟨hs, hst.le⟩
  have hLc : IsClosed L := (isClosed_eq continuous_im continuous_const).union
    (isCompact_Icc.image_of_continuousOn hcs).isClosed
  have hLV : Disjoint L V := by
    refine Set.disjoint_left.2 fun z hzL hzV => ?_
    rcases hzL with hz | ⟨u, hu, rfl⟩
    · exact absurd hz (ne_of_gt hzV.1)
    · refine hzV.2 (mem_fillH_image ⟨hu.1, hu.2.trans hst.le⟩ hzV.1)
  have hLeq : L \ {γ s} = {z | z.im = 0} ∪ γ '' Ico 0 s := by
    ext z
    constructor
    · rintro ⟨hz | ⟨u, hu, rfl⟩, hzs⟩
      · exact Or.inl hz
      · refine Or.inr ⟨u, ⟨hu.1, lt_of_le_of_ne hu.2 fun he => hzs (by rw [he]; rfl)⟩, rfl⟩
    · rintro (hz | ⟨u, hu, rfl⟩)
      · refine ⟨Or.inl hz, fun he => ?_⟩
        rw [mem_singleton_iff] at he
        have : (0 : ℝ) < z.im := he ▸ hγsH
        exact (ne_of_gt this) hz
      · refine ⟨Or.inr ⟨u, Ico_subset_Icc_self hu, rfl⟩, fun he => ?_⟩
        rw [mem_singleton_iff] at he
        have := hi ⟨hu.1, hu.2.le.trans hst.le⟩ ⟨hs.le, hst.le⟩ he
        linarith [hu.2]
  have hLconn : IsConnected (L \ {γ s}) := by
    rw [hLeq]
    refine ⟨⟨0, Or.inl (by simp)⟩, ?_⟩
    refine IsPreconnected.union 0 (by simp) ⟨0, ⟨le_rfl, hs⟩, h0⟩
      QuantumZipper.CA.Uniformizer.isPreconnected_setOf_im_eq_zero
      (isPreconnected_Ico.image _ (hcs.mono Ico_subset_Icc_self))
  have hLub : ¬ Bornology.IsBounded L := by
    intro hb'
    obtain ⟨r, hr⟩ := hb'.exists_norm_le
    have := hr ((r + 1 : ℝ) : ℂ) (Or.inl (by simp))
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith [le_abs_self (r + 1)]
  have hLnear : ∃ z ∈ L, z ≠ γ s ∧ ‖z - γ s‖ ≤ d / 2 := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hcs s ⟨hs.le, le_rfl⟩) (d / 2)
      (by positivity)
    set u := max 0 (s - δ / 2) with hu
    have hu0 : 0 ≤ u := le_max_left _ _
    have hus : u < s := max_lt hs (by linarith)
    have hdist : dist u s < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have := le_max_right 0 (s - δ / 2)
      linarith
    refine ⟨γ u, Or.inr ⟨u, ⟨hu0, hus.le⟩, rfl⟩, fun he => ?_, ?_⟩
    · have := hi ⟨hu0, hus.le.trans hst.le⟩ ⟨hs.le, hst.le⟩ he
      linarith
    · have := hδ' ⟨hu0, hus.le⟩ hdist
      rw [dist_eq_norm] at this
      exact this.le
  exact ⟨hLc, hLV, hLconn, hLub, hLnear⟩

/-- The harmonic-measure bound on the boundary interval. -/
theorem hm_bound {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hcmp : HmComparison C₁) {V L : Set ℂ} {c : ℂ}
    {a b d R M₂ : ℝ} {g₂ F₂ : ℂ → ℂ} (hVo : IsOpen V) (hVH : V ⊆ H) (hcV : c ∉ V) (hab : a ≤ b)
    (hd : 0 < d) (hdR : d ≤ R) (hcR : ‖c‖ ≤ R) (hLc : IsClosed L) (hLV : Disjoint L V)
    (hLconn : IsConnected (closure ((fun z => (z - c)⁻¹) '' (L \ {c}))))
    (hLub : ¬ Bornology.IsBounded L)
    (hLnear : ∃ z ∈ L, z ≠ c ∧ ‖z - c‖ ≤ d / 2) (hg₂V : ∀ z ∈ V, g₂ z ∈ H)
    (hg₂an : ∀ z ∈ V, AnalyticAt ℂ g₂ z) (hF₂g : ∀ z ∈ V, F₂ (g₂ z) = z)
    (hF₂c : ContinuousOn F₂ Hbar) (hF₂H : ∀ ξ ∈ H, F₂ ξ ∈ V)
    (hF₂ab : ∀ x : ℝ, x ∈ Icc a b → ‖F₂ x - c‖ ≤ d) (hg₂bd : ∀ z ∈ V, ‖g₂ z - z‖ ≤ M₂)
    {Y₁ : ℝ} (hYV : ∀ Y : ℝ, Y₁ < Y → (Y : ℂ) * I ∈ V) :
    b - a ≤ 20 * C₁ * √(d * R) := by
  have hRpos : 0 < R := hd.trans_le hdR
  have hbd : ∀ z ∈ V, ‖g₂ z‖ ≤ ‖z‖ + M₂ := fun z hz => by
    have := norm_le_norm_add_norm_sub' (g₂ z) z
    linarith [hg₂bd z hz]
  have hdecay := hmIoo_comp_decay hVo hg₂V hF₂g hF₂c hF₂H hF₂ab hbd
  set φ : ℂ → ℝ := fun z => hmIoo a b (g₂ z) with hφ
  have hφharm : InnerProductSpace.HarmonicOnNhd φ V := fun z hz =>
    QuantumZipper.Thm18Asm.LWFar.pocket_harmonicAt_comp (hg₂an z hz)
      (harmonicOnNhd_hmIoo a b _ (hg₂V z hz))
  have hφ01 : ∀ z ∈ V, 0 ≤ φ z ∧ φ z ≤ 1 := fun z hz =>
    ⟨hmIoo_nonneg _ _ _, hmIoo_le_one _ _ (hg₂V z hz)⟩
  set K := |a| + |b| with hK
  have hinf : ∀ ε > 0, ∃ M : ℝ, ∀ z ∈ V, M ≤ ‖z‖ → φ z ≤ ε := by
    intro ε hε
    refine ⟨M₂ + K + (b - a) / (π * ε) + 1, fun z hz hzM => ?_⟩
    set r := (b - a) / (π * ε) + 1 with hr
    have hrpos : 0 < r := by
      have : 0 ≤ (b - a) / (π * ε) := div_nonneg (by linarith) (by positivity)
      linarith
    have hP : ∀ t' ∈ Ioo a b, poissonKernelH (g₂ z) t' ≤ 1 / (π * r) := by
      intro t' ht'
      refine poissonKernelH_le_inv' hrpos ?_ (le_of_lt (hg₂V z hz))
      have h1 : ‖z‖ - M₂ ≤ ‖g₂ z‖ := by
        have := norm_sub_norm_le z (g₂ z)
        rw [norm_sub_rev] at this
        linarith [hg₂bd z hz]
      have h2 : |t'| ≤ K := by
        rw [abs_le]; constructor <;>
          linarith [ht'.1, ht'.2, neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
      have h3 : ‖g₂ z‖ - |t'| ≤ ‖g₂ z - t'‖ := by
        have := norm_sub_norm_le (g₂ z) (t' : ℂ)
        rwa [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have := hmIoo_le hab (by positivity) hP
    calc φ z ≤ 1 / (π * r) * (b - a) := this
      _ ≤ ε := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        have : (b - a) / (π * ε) ≤ r := by linarith
        rw [div_le_iff₀ (by positivity)] at this
        nlinarith [Real.pi_pos]
  have hmain := hcmp V L c d R φ hVo hVH hcV hd hdR hcR hLc hLV hLconn hLub
    hLnear hφharm hφ01 hdecay hinf
  have hM₂0 : 0 ≤ M₂ :=
    (norm_nonneg _).trans (hg₂bd _ (hYV (|Y₁| + 1) (by linarith [le_abs_self Y₁])))
  have hkey := le_of_hmIoo_bounds hab hRpos hC₁ hM₂0 hcR hYV hg₂V hg₂bd hmain
  have hsq : R * √(d / R) = √(d * R) := by
    have : √(d * R) = √(R ^ 2 * (d / R)) := by congr 1; field_simp
    rw [this, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hRpos.le]
  rw [mul_assoc (20 * C₁), hsq] at hkey
  exact hkey

theorem exists_norm_mapOut_sub_le_main {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hcmp : HmComparison C₁)
    {γ : ℝ → ℂ} {R s t d : ℝ} (hc : ContinuousOn γ (Icc 0 t)) (hi : InjOn γ (Icc 0 t))
    (h0 : γ 0 = 0) (hH : MapsTo γ (Ioc 0 t) H) (hR : ∀ u ∈ Icc 0 t, ‖γ u‖ ≤ R) (hs : 0 < s)
    (hst : s < t) (hd : 0 < d) (hdR : d ≤ R) (hosc : ∀ u ∈ Icc s t, ‖γ u - γ s‖ ≤ d) :
    ∃ x : ℝ, ∀ u ∈ Ioc s t,
      ‖ConformalImage.mapOut (fillH (γ '' Icc 0 s)) (γ u) - x‖ ≤ 240 * C₁ * √(d * R) := by
  have hRpos : 0 < R := hd.trans_le hdR
  -- the hull `A = fill(γ[0, s])`, its mapping-out function `g`, and the extension `F_A`
  set A := fillH (γ '' Icc 0 s) with hAdef
  have hcs : ContinuousOn γ (Icc 0 s) := hc.mono (Icc_subset_Icc_right hst.le)
  have hHbar : ∀ u ∈ Icc 0 t, γ u ∈ Hbar := fun u hu => by
    rcases eq_or_lt_of_le hu.1 with h' | h'
    · rw [← h', h0]; exact show (0 : ℝ) ≤ (0 : ℂ).im by simp
    · exact H_subset_Hbar (hH ⟨h', hu.2⟩)
  have hA : IsHPHull A := isHPHull_fillH_image hcs hs.le h0
  set g := ConformalImage.mapOut A with hgdef
  have hg : IsMapOut A g := ConformalImage.isMapOut_mapOut hA
  obtain ⟨FA, hFA1, hFA2, hFAd, hFAc, hFAi, hFAR, -, -, -⟩ := exists_extension_symm hs.le hcs
    (fun u hu => hHbar u ⟨hu.1, hu.2.trans hst.le⟩) (by rw [h0, zero_im])
  have hmemA : ∀ u ∈ Ioc s t, γ u ∈ H \ A := fun u hu =>
    mem_H_diff_fillH_of_lt hc hi h0 hH hs.le hu.1 hu.2
  -- the tip
  obtain ⟨U, hUt, hFAU⟩ :=
    exists_tendsto_mapOut_tip hc hi h0 hH hs hst hFA1 hFA2 hFAd hFAc hFAi hFAR
  -- the slit `β(v) = g(γ(s + v))`, `β(0) = U`
  set T' := t - s with hT'
  have hT'pos : 0 < T' := by rw [hT']; linarith
  set β : ℝ → ℂ := fun v => if v = 0 then (U : ℂ) else g (γ (s + v)) with hβ
  have hβ0 : β 0 = U := by simp [hβ]
  have hβv : ∀ v, v ≠ 0 → β v = g (γ (s + v)) := fun v hv => by simp [hβ, hv]
  have hsv : ∀ v ∈ Ioc 0 T', s + v ∈ Ioc s t := fun v hv =>
    ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hβH : MapsTo β (Ioc 0 T') H := fun v hv => by
    rw [hβv v hv.1.ne']; exact hg.1.2.mapsTo (hmemA _ (hsv v hv))
  have hgc : ContinuousOn g (H \ A) := hg.1.1.continuousOn
  have hβc : ContinuousOn β (Icc 0 T') := by
    intro v hv
    rcases eq_or_lt_of_le hv.1 with h' | h'
    · subst h'
      refine (continuousWithinAt_Ioi_iff_Ici.1 ?_).mono Icc_subset_Ici_self
      show Tendsto β (𝓝[>] 0) (𝓝 (β 0))
      rw [hβ0]
      have h1 : Tendsto (fun v : ℝ => s + v) (𝓝[>] 0) (𝓝[>] s) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := ((continuous_const_add s).tendsto (0 : ℝ)).mono_left
            (nhdsWithin_le_nhds (s := Ioi 0))
          simpa using this
        · filter_upwards [self_mem_nhdsWithin] with v hv
          show s < s + v; linarith [show (0 : ℝ) < v from hv]
      refine (hUt.comp h1).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact (hβv v (ne_of_gt hv)).symm
    · have hev : β =ᶠ[𝓝 v] fun v => g (γ (s + v)) := by
        filter_upwards [isOpen_ne.mem_nhds h'.ne'] with w hw
        exact hβv w hw
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (hev.filter_mono nhdsWithin_le_nhds)
        (hev.eq_of_nhds)
      have hsvm : s + v ∈ Ioc s t := hsv v ⟨h', hv.2⟩
      have hγw : ContinuousWithinAt (fun w => γ (s + w)) (Icc 0 T') v :=
        (hc (s + v) ⟨by linarith, hsvm.2⟩).comp (continuous_const_add s).continuousWithinAt
          fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
      exact ContinuousAt.comp_continuousWithinAt (g := g)
        (hgc.continuousAt (hA.isOpen.mem_nhds (hmemA _ hsvm))) hγw
  have hβi : InjOn β (Icc 0 T') := by
    intro v hv v' hv' hvv'
    rcases eq_or_lt_of_le hv.1 with h1 | h1 <;> rcases eq_or_lt_of_le hv'.1 with h2 | h2
    · rw [← h1, ← h2]
    · exfalso
      have := hβH ⟨h2, hv'.2⟩
      rw [← hvv', ← h1, hβ0] at this
      exact absurd (show (0 : ℝ) < (U : ℂ).im from this) (by simp)
    · exfalso
      have := hβH ⟨h1, hv.2⟩
      rw [hvv', ← h2, hβ0] at this
      exact absurd (show (0 : ℝ) < (U : ℂ).im from this) (by simp)
    · rw [hβv v h1.ne', hβv v' h2.ne'] at hvv'
      have h3 := hg.1.2.injOn (hmemA _ (hsv v ⟨h1, hv.2⟩)) (hmemA _ (hsv v' ⟨h2, hv'.2⟩)) hvv'
      have h4 := hi ⟨by linarith, by linarith [hv.2]⟩ ⟨by linarith, by linarith [hv'.2]⟩ h3
      linarith
  have hβ0im : (β 0).im = 0 := by rw [hβ0]; simp
  set B := fillH (β '' Icc 0 T') with hBdef
  have hBeq : B = β '' Ioc 0 T' := fillH_image_eq hT'pos.le hβc hβi hβ0im hβH
  have hB : IsHPHull B := isHPHull_fillH_image_of_im hβc hT'pos.le hβ0im
  set gB := ConformalImage.mapOut B with hgBdef
  have hgB : IsMapOut B gB := ConformalImage.isMapOut_mapOut hB
  have hβHbar : MapsTo β (Icc 0 T') Hbar := fun v hv => by
    rcases eq_or_lt_of_le hv.1 with h' | h'
    · rw [← h', hβ0]; exact show (0 : ℝ) ≤ (U : ℂ).im by simp
    · exact H_subset_Hbar (hβH ⟨h', hv.2⟩)
  obtain ⟨FB, hFB1, hFB2, hFBd, hFBc, -, -, -, hFBfr, MB', hMB'⟩ :=
    exists_extension_symm hT'pos.le hβc hβHbar hβ0im
  have hext : IsBdryExt B gB FB := ⟨hB, hgB, hFB1, hFBd, hFBc, fun x =>
    hFBfr ⟨IsBdryExt.ofReal_mem_Hbar x, fun h' => by
      have : (0 : ℝ) < (x : ℂ).im := h'; simp at this⟩, MB', hMB'⟩
  have hBne : B.Nonempty := ⟨β T', by rw [hBeq]; exact ⟨T', ⟨hT'pos, le_rfl⟩, rfl⟩⟩
  have hclB : closure B ⊆ β '' Icc 0 T' := by
    rw [hBeq]
    exact closure_minimal (image_mono Ioc_subset_Icc_self)
      (isCompact_Icc.image_of_continuousOn hβc).isClosed
  have hUcl : ∀ z ∈ closure B, z.im = 0 → z = U := by
    intro z hz hzim
    obtain ⟨v, hv, rfl⟩ := hclB hz
    rcases eq_or_lt_of_le hv.1 with h' | h'
    · rw [← h', hβ0]
    · exact absurd hzim (ne_of_gt (hβH ⟨h', hv.2⟩))
  set a := sInf (bdrySet B FB) with ha
  set b := sSup (bdrySet B FB) with hb
  have hX : bdrySet B FB = Icc a b := hext.bdrySet_eq_Icc hBne hUcl
  have hab : a ≤ b := by
    obtain ⟨x, hx⟩ := hext.bdrySet_nonempty hBne
    rw [hX] at hx
    exact hx.1.trans hx.2
  have hkoebe : ∀ e ∈ B, ∀ e' ∈ B, ‖e' - e‖ ≤ 12 * (b - a) := fun e he e' he' =>
    hext.norm_sub_le hX.subset hab he he'
  -- the hull `A₂ = fill(γ[0, t])` and `V = ℍ \ A₂`
  have hAeq : A = γ '' Ioc 0 s := fillH_image_eq_of_le hc hi h0 hH hs.le hst.le
  set A₂ := fillH (γ '' Icc 0 t) with hA₂def
  have hA₂eq : A₂ = γ '' Ioc 0 t := fillH_image_eq_of_le hc hi h0 hH (hs.trans hst).le le_rfl
  have hA₂ : IsHPHull A₂ := isHPHull_fillH_image hc (hs.trans hst).le h0
  set V := H \ A₂ with hV
  have hVo : IsOpen V := hA₂.isOpen
  have hVA : ∀ z ∈ V, z ∈ H \ A := fun z hz => ⟨hz.1, fun hzA => hz.2 (by
    rw [hA₂eq]; rw [hAeq] at hzA
    exact image_mono (Ioc_subset_Ioc_right hst.le) hzA)⟩
  have hgB_of : ∀ u ∈ Ioc s t, g (γ u) = β (u - s) := fun u hu => by
    rw [hβv _ (by linarith [hu.1]), add_sub_cancel]
  have hgzB : ∀ z ∈ V, g z ∉ B := by
    intro z hz hzB
    rw [hBeq] at hzB
    obtain ⟨v, hv, hve⟩ := hzB
    rw [hβv v hv.1.ne'] at hve
    have := hg.1.2.injOn (hmemA _ (hsv v hv)) (hVA z hz) hve
    exact hz.2 (by rw [hA₂eq, ← this]; exact ⟨s + v, ⟨by linarith [hv.1], (hsv v hv).2⟩, rfl⟩)
  set g₂ : ℂ → ℂ := fun z => gB (g z) with hg₂
  set F₂ : ℂ → ℂ := fun ξ => FA (FB ξ) with hF₂
  have hgzHB : ∀ z ∈ V, g z ∈ H \ B := fun z hz => ⟨hg.1.2.mapsTo (hVA z hz), hgzB z hz⟩
  have hg₂V : ∀ z ∈ V, g₂ z ∈ H := fun z hz => hgB.1.2.mapsTo (hgzHB z hz)
  have hF₂g : ∀ z ∈ V, F₂ (g₂ z) = z := fun z hz => by
    simp only [hF₂, hg₂]
    rw [hFB2 _ (hgzHB z hz)]
    exact hFA2 z (hVA z hz)
  have hFBHbar : MapsTo FB Hbar Hbar := by
    intro w hw
    by_cases hwH : w ∈ H
    · exact H_subset_Hbar (hFB1 w hwH).1.1
    · have hwim : w.im = 0 := le_antisymm (not_lt.1 hwH) hw
      have hfr := hFBfr ⟨hw, hwH⟩
      have : closure (H \ B) ⊆ Hbar :=
        closure_minimal (fun z hz => H_subset_Hbar hz.1) isClosed_Hbar
      exact this hfr.1
  have hF₂c : ContinuousOn F₂ Hbar := hFAc.comp hFBc hFBHbar
  have hF₂H : ∀ ξ ∈ H, F₂ ξ ∈ V := by
    intro ξ hξ
    obtain ⟨⟨hFBH, hFBnB⟩, hgFB⟩ := hFB1 ξ hξ
    obtain ⟨⟨hFAH, hFAnA⟩, hgFA⟩ := hFA1 _ hFBH
    refine ⟨hFAH, fun hA₂mem => ?_⟩
    rw [hA₂eq] at hA₂mem
    obtain ⟨u, hu, hue⟩ := hA₂mem
    have hue' : γ u = FA (FB ξ) := hue
    have hus : s < u := by
      by_contra hle
      exact hFAnA (by rw [← hue']; exact mem_fillH_image ⟨hu.1.le, not_lt.1 hle⟩ (hH hu))
    apply hFBnB
    have h1 : g (FA (FB ξ)) = FB ξ := hgFA
    rw [← h1, ← hue', hgB_of u ⟨hus, hu.2⟩]
    show β (u - s) ∈ B
    rw [hBeq]
    exact ⟨u - s, ⟨by linarith, by linarith [hu.2]⟩, rfl⟩
  have hF₂ab : ∀ x : ℝ, x ∈ Icc a b → ‖F₂ x - γ s‖ ≤ d := by
    intro x hx
    rw [← hX] at hx
    obtain ⟨v, hv, hve⟩ := hclB hx
    simp only [hF₂]
    rw [← hve]
    rcases eq_or_lt_of_le hv.1 with h' | h'
    · rw [← h', hβ0, hFAU, sub_self, norm_zero]; exact hd.le
    · rw [hβv v h'.ne', hFA2 _ (hmemA _ (hsv v ⟨h', hv.2⟩))]
      exact hosc _ ⟨by linarith, (hsv v ⟨h', hv.2⟩).2⟩
  obtain ⟨MA, hMA⟩ := hg.exists_norm_sub_le hA
  obtain ⟨MB, hMB⟩ := hgB.exists_norm_sub_le hB
  set M₂ := MA + MB with hM₂
  have hg₂bd : ∀ z ∈ V, ‖g₂ z - z‖ ≤ M₂ := by
    intro z hz
    have h1 := hMA z (hVA z hz)
    have h2 := hMB (g z) (hgzHB z hz)
    calc ‖g₂ z - z‖ = ‖(gB (g z) - g z) + (g z - z)‖ := by simp only [hg₂]; ring_nf
      _ ≤ ‖gB (g z) - g z‖ + ‖g z - z‖ := norm_add_le _ _
      _ ≤ M₂ := by linarith
  have hbd : ∀ z ∈ V, ‖g₂ z‖ ≤ ‖z‖ + M₂ := fun z hz => by
    have := norm_le_norm_add_norm_sub' (g₂ z) z
    linarith [hg₂bd z hz]
  have hcR : ‖γ s‖ ≤ R := hR s ⟨hs.le, hst.le⟩
  have hγsH : γ s ∈ H := hH ⟨hs, hst.le⟩
  have hcV : γ s ∉ V := fun h' => h'.2 (mem_fillH_image ⟨hs.le, hst.le⟩ hγsH)
  obtain ⟨hLc, hLV, hLconn, hLub, hLnear⟩ := continuum_props hc hi h0 hH hs hst hd
  have hYV : ∀ Y : ℝ, R + 1 < Y → (Y : ℂ) * I ∈ V := fun Y hY =>
    mem_H_diff_fillH_of_lt_im (R := R + 1) (by linarith) hc
      (fun u hu => by linarith [hR u hu]) (by simp; linarith)
  have hg₂an : ∀ z ∈ V, AnalyticAt ℂ g₂ z := fun z hz =>
    (hgB.1.1.analyticAt (hB.isOpen.mem_nhds (hgzHB z hz))).comp
      (hg.1.1.analyticAt (hA.isOpen.mem_nhds (hVA z hz)))
  have hba := hm_bound hC₁ hcmp hVo (fun z hz => hz.1) hcV hab hd hdR hcR hLc hLV
    (isConnected_closure_inv_image hLconn) hLub
    hLnear hg₂V hg₂an hF₂g hF₂c hF₂H hF₂ab hg₂bd hYV
  -- conclusion
  have hUcl : (U : ℂ) ∈ closure B := by
    refine mem_closure_of_tendsto hUt ?_
    filter_upwards [Ioo_mem_nhdsGT hst] with u hu
    show g (γ u) ∈ B
    rw [hgB_of u ⟨hu.1, hu.2.le⟩, hBeq]
    exact ⟨u - s, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩
  refine ⟨U, fun u hu => ?_⟩
  have heB : g (γ u) ∈ B := by
    rw [hgB_of u hu, hBeq]
    exact ⟨u - s, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩
  have hclosed : IsClosed {w : ℂ | ‖w - g (γ u)‖ ≤ 12 * (b - a)} :=
    isClosed_le (continuous_id.sub continuous_const).norm continuous_const
  have h1 : ‖(U : ℂ) - g (γ u)‖ ≤ 12 * (b - a) :=
    closure_minimal (fun e' he' => hkoebe _ heB e' he') hclosed hUcl
  rw [norm_sub_rev] at h1
  show ‖g (γ u) - U‖ ≤ 240 * C₁ * √(d * R)
  linarith

/-! ### The estimate, and (iii) ⇒ (i) -/

/-- **[Law05, Proposition 3.76] for simple paths** (with constant `240 C₁ + 1`, `C₁` the
constant of `le_mul_hmIoo`). -/
theorem simpleCurveLocalGrowth : SimpleCurveLocalGrowth := by
  obtain ⟨C₁, hC₁, hcmp⟩ := le_mul_hmIoo
  refine ⟨240 * C₁ + 1, by positivity, ?_⟩
  intro γ S R hc hi h0 hH hR s t d hs hst htS hd hdR hosc
  have hRpos : 0 < R := hd.trans_le hdR
  have hdsq : d ≤ √(d * R) := by
    calc d = √(d * d) := (Real.sqrt_mul_self hd.le).symm
      _ ≤ √(d * R) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdR hd.le)
  have hC : 240 * C₁ * √(d * R) ≤ (240 * C₁ + 1) * √(d * R) := by
    nlinarith [Real.sqrt_nonneg (d * R)]
  rcases eq_or_lt_of_le hst with hst' | hst'
  · refine ⟨0, fun u hu => ?_⟩
    rw [hst'] at hu
    exact absurd (hu.1.trans_le hu.2) (lt_irrefl _)
  rcases eq_or_lt_of_le hs with hs' | hs'
  · -- `s = 0`: the hull is empty
    subst hs'
    refine ⟨0, fun u hu => ?_⟩
    have hA : fillH (γ '' Icc 0 0) = ∅ := fillH_image_Icc_zero h0
    have hγu : γ u ∈ H := hH ⟨hu.1, hu.2.trans htS⟩
    have hid : ConformalImage.mapOut (fillH (γ '' Icc 0 0)) (γ u) = γ u := by
      rw [hA]
      exact (ConformalImage.isMapOut_mapOut isHPHull_empty).eqOn isHPHull_empty
        isMapOut_empty_id ⟨hγu, notMem_empty _⟩
    rw [hid, ofReal_zero, sub_zero]
    have := hosc u ⟨le_of_lt hu.1, hu.2⟩
    rw [h0, sub_zero] at this
    nlinarith [Real.sqrt_nonneg (d * R)]
  -- `0 < s < t`
  have hcmp' : HmComparison C₁ := hcmp
  obtain ⟨x, hx⟩ := exists_norm_mapOut_sub_le_main hC₁ hcmp'
    (hc.mono (Icc_subset_Icc_right htS)) (hi.mono (Icc_subset_Icc_right htS)) h0
    (hH.mono_left (Ioc_subset_Ioc_right htS)) (fun u hu => hR u ⟨hu.1, hu.2.trans htS⟩) hs' hst'
    hd hdR hosc
  exact ⟨x, fun u hu => (hx u hu).trans hC⟩

/-- **[Yua22, Theorem 1.1, (iii) ⇒ (i)] with Loewner's theorem**: a continuous path `η` on
`[0, S]` with `η 0 = 0`, strictly increasing fillings `K_t = fill(η[0, t])`, and a uniform
approximation by simple paths `γ_n` (`γ_n 0 = 0`, `γ_n((0, S]) ⊆ ℍ`) generates a Loewner chain:
there are a continuous driver `W` with `W 0 = 0` and a continuous strictly increasing time change
`σ` with `σ 0 = 0` such that the hull of `W` at time `σ(t)` is `K_t` for every `t ∈ [0, S]`. -/
theorem exists_loewner_of_simpleApprox {η : ℝ → ℂ} {S : ℝ} (hS : 0 < S)
    (hη : ContinuousOn η (Icc 0 S)) (h0 : η 0 = 0)
    (hmono : StrictMonoOn (fun t => fillH (η '' Icc 0 t)) (Icc 0 S)) {γ : ℕ → ℝ → ℂ}
    (hγ : ∀ n, ContinuousOn (γ n) (Icc 0 S) ∧ InjOn (γ n) (Icc 0 S) ∧ γ n 0 = 0 ∧
      MapsTo (γ n) (Ioc 0 S) H)
    (hconv : TendstoUniformlyOn γ η atTop (Icc 0 S)) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 S) ∧
      ContinuousOn σ (Icc 0 S) ∧
      ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (σ t) = fillH (η '' Icc 0 t) :=
  exists_loewner_of_tendstoUniformlyOn simpleCurveLocalGrowth hS hη h0 hmono hγ hconv

end YuanCharacterisation

end InteractingSLE
