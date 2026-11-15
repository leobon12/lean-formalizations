import InteractingSLE.Foundations.Harmonic.MaxPrinciple
import QuantumZipper.Statements.CouplingFields
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.Interval.Finset.Fin

/-!
# Bounded harmonic extension of piecewise-constant boundary data on `ℍ`

Packet GEO-STEP (`planning/INFRA-GEO.md` §4; design handoff `planning/handoffs/INFRA-GEO-ARCH.md` §D.4).

Specification p. 2 ("their harmonic extension means the bounded harmonic extension in that
specified chart") and Theorem 1.1, p. 9 (the mean `𝔥⁰_t`, "intervals of zero length are
omitted"). The extension is the literal formula
`stepHarmonicH n x v z = v n + ∑ⱼ (vⱼ − vⱼ₊₁) arg(z − xⱼ)/π`.

## Main statements
* `InteractingSLE.StepData.harmonicOnNhd_harmonicExtH`: harmonic on `ℍ`;
* `InteractingSLE.StepData.harmonicExtH_mem_Icc`: bounded by the extreme values;
* `InteractingSLE.StepData.tendsto_harmonicExtH`: boundary values off the breakpoints;
* `InteractingSLE.StepData.eqOn_harmonicExtH`: uniqueness among bounded harmonic functions;
* `InteractingSLE.StepData.harmonicExtH_one_jump`: the one-jump word `(−π/√κ, π/√κ)` at `0` is
  QZ's `h0fwd κ + π/√κ`.

Proof route: `arg (z − x) = Im log (z − x)` (analytic off the slit); the formula is a convex
combination after Abel summation (`arg (z − x)` is increasing in `x` on `ℍ`); boundary limits by
continuity of `arg` from `{0 ≤ Im}`; uniqueness by Lindelöf's maximum principle
(`InteractingSLE.eqOn_of_tendsto_sub_H`).
-/

set_option autoImplicit false

noncomputable section

open Complex Metric Filter Topology Finset
open Set (EqOn)
open scoped Real
open QuantumZipper (H Hbar)

namespace InteractingSLE

/-- The explicit bounded harmonic extension to `ℍ` of the step function with (weakly increasing)
breakpoints `x 0 ≤ ⋯ ≤ x (n−1)` and values `v 0, …, v n` on the successive intervals:
`v n + ∑ⱼ (v j − v (j+1)) arg(z − xⱼ)/π`. Coincident breakpoints (zero-length intervals) are
handled correctly by the formula. -/
def stepHarmonicH (n : ℕ) (x : Fin n → ℝ) (v : Fin (n + 1) → ℝ) (z : ℂ) : ℝ :=
  v (Fin.last n) + ∑ j : Fin n, (v j.castSucc - v j.succ) * (arg (z - x j) / π)

/-- Bounded piecewise-constant boundary data on `ℝ = ∂ℍ` (Specification p. 2 and Theorem 1.1,
p. 9): `n` weakly increasing breakpoints and `n + 1` values; the value `v k` is taken on
`[x (k−1), x k)` (right-continuous, as in Theorem 1.1's intervals `[V̂^{j,R}, V̂^{j+1,R})`). -/
structure StepData where
  /-- number of breakpoints -/
  n : ℕ
  /-- breakpoints -/
  x : Fin n → ℝ
  monotone_x : Monotone x
  /-- values on the `n + 1` intervals -/
  v : Fin (n + 1) → ℝ

/-! ### `arg (z − x)` on `ℍ` -/

private theorem mul_sqrt_le_mul_sqrt {p q A B : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : p ^ 2 * A ≤ q ^ 2 * B) : p * √A ≤ q * √B := by
  have e1 : p * √A = √(p ^ 2 * A) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp]
  have e2 : q * √B = √(q ^ 2 * B) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq]
  rw [e1, e2]
  exact Real.sqrt_le_sqrt h

/-- `s ↦ s / √(s² + b²)` is monotone for `b > 0`. -/
private theorem div_sqrt_sq_add_le {b s₁ s₂ : ℝ} (hb : 0 < b) (h : s₁ ≤ s₂) :
    s₁ / √(s₁ ^ 2 + b ^ 2) ≤ s₂ / √(s₂ ^ 2 + b ^ 2) := by
  have hA : 0 < √(s₁ ^ 2 + b ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < √(s₂ ^ 2 + b ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_div_iff₀ hA hB]
  rcases le_total 0 s₁ with h1 | h1
  · have hs : s₁ ^ 2 ≤ s₂ ^ 2 := pow_le_pow_left₀ h1 h 2
    exact mul_sqrt_le_mul_sqrt h1 (h1.trans h)
      (by nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg b)])
  rcases le_total 0 s₂ with h2 | h2
  · nlinarith [mul_nonneg h2 hA.le, mul_nonneg (neg_nonneg.2 h1) hB.le]
  · have hs : (-s₂) ^ 2 ≤ (-s₁) ^ 2 := pow_le_pow_left₀ (neg_nonneg.2 h2) (neg_le_neg h) 2
    have := mul_sqrt_le_mul_sqrt (neg_nonneg.2 h2) (neg_nonneg.2 h1)
      (A := s₁ ^ 2 + b ^ 2) (B := s₂ ^ 2 + b ^ 2)
      (by nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg b)])
    linarith

/-- On `ℍ`, `arg (z − x)` is increasing in the real point `x`. -/
theorem arg_sub_ofReal_le_arg_sub_ofReal {z : ℂ} (hz : z ∈ H) {a b : ℝ} (hab : a ≤ b) :
    arg (z - a) ≤ arg (z - b) := by
  have hz0 : 0 < z.im := hz
  have h1 : 0 < (z - a).im := by simpa using hz0
  have h2 : 0 < (z - b).im := by simpa using hz0
  rw [arg_of_im_pos h1, arg_of_im_pos h2]
  apply Real.arccos_le_arccos
  have n1 : ‖z - a‖ = √((z.re - a) ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
  have n2 : ‖z - b‖ = √((z.re - b) ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
  rw [n1, n2]
  simp only [sub_re, ofReal_re]
  exact div_sqrt_sq_add_le hz0 (by linarith)

theorem arg_mem_Ioo_of_mem_H {w : ℂ} (hw : w ∈ H) : arg w ∈ Set.Ioo 0 π := by
  have hw0 : 0 < w.im := hw
  refine ⟨lt_of_le_of_ne (arg_nonneg_iff.2 hw0.le) fun h => ?_, lt_of_le_of_ne (arg_le_pi w)
    (fun h => by rw [arg_eq_pi_iff] at h; linarith [h.2])⟩
  rw [eq_comm, arg_eq_zero_iff] at h
  linarith [h.2]

theorem sub_ofReal_mem_H {z : ℂ} (hz : z ∈ H) (a : ℝ) : z - a ∈ H := by
  show 0 < (z - a).im
  simpa using (show 0 < z.im from hz)

/-! ### Abel summation -/

/-- Abel summation for the step formula on `ℕ`. -/
private theorem abel_step (θ V : ℕ → ℝ) (n : ℕ) :
    V n + ∑ j ∈ range n, θ j * (V j - V (j + 1)) =
      θ 0 * V 0 + ∑ k ∈ range n, (θ (k + 1) - θ k) * V (k + 1) + (1 - θ n) * V n := by
  induction n with
  | zero => simp only [range_zero, sum_empty]; ring
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    linear_combination ih

/-- The step formula with weakly increasing weights in `[0, 1]` is a convex combination of the
values. -/
private theorem step_mem_Icc_of_monotone (n : ℕ) (θ V : ℕ → ℝ) {m M : ℝ} (h0 : 0 ≤ θ 0)
    (hmono : ∀ j < n, θ j ≤ θ (j + 1)) (h1 : θ n ≤ 1) (hV : ∀ k ≤ n, V k ∈ Set.Icc m M) :
    V n + ∑ j ∈ range n, θ j * (V j - V (j + 1)) ∈ Set.Icc m M := by
  rw [abel_step]
  have htel : ∑ k ∈ range n, (θ (k + 1) - θ k) = θ n - θ 0 := sum_range_sub θ n
  have hw : ∀ k ∈ range n, 0 ≤ θ (k + 1) - θ k := fun k hk =>
    sub_nonneg.2 (hmono k (mem_range.1 hk))
  have hV0 := hV 0 (Nat.zero_le _)
  have hVn := hV n le_rfl
  constructor
  · have hs : ∑ k ∈ range n, (θ (k + 1) - θ k) * m ≤
        ∑ k ∈ range n, (θ (k + 1) - θ k) * V (k + 1) :=
      sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
        (hV (k + 1) (mem_range.1 hk)).1 (hw k hk)
    rw [← sum_mul, htel] at hs
    nlinarith [hV0.1, hVn.1]
  · have hs : ∑ k ∈ range n, (θ (k + 1) - θ k) * V (k + 1) ≤
        ∑ k ∈ range n, (θ (k + 1) - θ k) * M :=
      sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
        (hV (k + 1) (mem_range.1 hk)).2 (hw k hk)
    rw [← sum_mul, htel] at hs
    nlinarith [hV0.2, hVn.2]

/-- Rewriting a `Fin`-indexed step sum as a `range` sum, with the values extended by
`V k = v (min k n)`. -/
private theorem step_sum_eq_range (n : ℕ) (v : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (θ : ℕ → ℝ)
    (hθ : ∀ j : Fin n, θ j = c j) :
    v (Fin.last n) + ∑ j : Fin n, (v j.castSucc - v j.succ) * c j =
      (fun k : ℕ => v ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩) n +
        ∑ j ∈ range n, θ j * ((fun k : ℕ => v ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩) j -
          (fun k : ℕ => v ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩) (j + 1)) := by
  congr 1
  · congr 1; ext; simp
  · rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hθ j, mul_comm]
    congr 2
    · congr 1; ext; simp
    · congr 1; ext; simp

/-! ### Harmonicity: `stepHarmonicH` is the imaginary part of an analytic function -/

private theorem stepHarmonicH_eq_im (n : ℕ) (x : Fin n → ℝ) (v : Fin (n + 1) → ℝ) (z : ℂ) :
    stepHarmonicH n x v z = ((v (Fin.last n) : ℂ) * I +
      ∑ j : Fin n, (((v j.castSucc - v j.succ) / π : ℝ) : ℂ) * log (z - x j)).im := by
  rw [stepHarmonicH, add_im, im_sum]
  simp only [log_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero,
    add_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `stepHarmonicH ∘ g` is harmonic at every point where `g` is analytic with values in `ℍ`. -/
theorem harmonicAt_stepHarmonicH_comp (n : ℕ) (x : Fin n → ℝ) (v : Fin (n + 1) → ℝ)
    {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hz : g z ∈ H) :
    InnerProductSpace.HarmonicAt (fun w => stepHarmonicH n x v (g w)) z := by
  have hfun : (fun w => stepHarmonicH n x v (g w)) = fun w => ((v (Fin.last n) : ℂ) * I +
      ∑ j : Fin n, (((v j.castSucc - v j.succ) / π : ℝ) : ℂ) * log (g w - x j)).im :=
    funext fun w => stepHarmonicH_eq_im n x v (g w)
  rw [hfun]
  refine AnalyticAt.harmonicAt_im (analyticAt_const.add ?_)
  have hsum : (fun w => ∑ j : Fin n, (((v j.castSucc - v j.succ) / π : ℝ) : ℂ) *
      log (g w - x j)) = ∑ j : Fin n, fun w => (((v j.castSucc - v j.succ) / π : ℝ) : ℂ) *
      log (g w - x j) := by
    funext w; simp [Finset.sum_apply]
  rw [hsum]
  refine Finset.analyticAt_sum _ fun j _ => analyticAt_const.mul ?_
  have hslit : g z - x j ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    exact Or.inr (ne_of_gt (sub_ofReal_mem_H hz (x j)))
  exact (analyticAt_clog hslit).comp (f := fun w => g w - x j) (hg.sub analyticAt_const)

/-! ### Counting breakpoints -/

/-- For monotone breakpoints, `x j ≤ t` iff `j` is below the number of breakpoints `≤ t`. -/
theorem le_iff_lt_card_filter {n : ℕ} {x : Fin n → ℝ} (hx : Monotone x) (t : ℝ) (j : Fin n) :
    x j ≤ t ↔ (j : ℕ) < (univ.filter fun i => x i ≤ t).card := by
  constructor
  · intro h
    have hsub : Finset.Iic j ⊆ univ.filter fun i => x i ≤ t := fun i hi =>
      mem_filter.2 ⟨mem_univ _, (hx (Finset.mem_Iic.1 hi)).trans h⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hne
    have hsub : (univ.filter fun i => x i ≤ t) ⊆ Finset.Iio j := fun i hi => by
      rw [Finset.mem_Iio]
      by_contra hji
      exact hne ((hx (not_lt.1 hji)).trans (mem_filter.1 hi).2)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- The number of `j : Fin n` with `p j`, when `p j ↔ j < k`. -/
theorem card_filter_eq_of_forall_iff {n : ℕ} {p : Fin n → Prop} [DecidablePred p] {k : ℕ}
    (hk : k ≤ n) (h : ∀ j : Fin n, p j ↔ (j : ℕ) < k) : (univ.filter p).card = k := by
  rcases hk.lt_or_eq with hk | rfl
  · have : univ.filter p = Finset.Iio (⟨k, hk⟩ : Fin n) := by
      ext j
      simp only [mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, h j, Fin.lt_def]
    rw [this, Fin.card_Iio]
  · have : univ.filter p = univ := by
      ext j
      simp only [mem_filter, mem_univ, true_and, h j, j.2]
    rw [this, card_univ, Fintype.card_fin]

/-! ### Boundary limits of `arg` -/

private theorem tendsto_sub_ofReal_nhdsWithin (t a : ℝ) :
    Tendsto (fun z : ℂ => z - a) (𝓝[H] (t : ℂ)) (𝓝[{w : ℂ | 0 ≤ w.im}] ((t : ℂ) - a)) :=
  tendsto_nhdsWithin_iff.2
    ⟨((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz =>
        (show (0 : ℝ) < (z - a).im from sub_ofReal_mem_H hz a).le⟩

private theorem tendsto_arg_sub_ofReal {t a : ℝ} (hta : a ≠ t) :
    Tendsto (fun z : ℂ => arg (z - a)) (𝓝[H] (t : ℂ)) (𝓝 (if a < t then 0 else π)) := by
  split_ifs with h
  · have hslit : ((t : ℂ) - a) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left; simpa using h
    have h0 : arg ((t : ℂ) - a) = 0 := by
      rw [← ofReal_sub, arg_ofReal_of_nonneg (by linarith)]
    rw [← h0]
    exact (continuousAt_arg hslit).tendsto.comp
      ((tendsto_sub_ofReal_nhdsWithin t a).mono_right nhdsWithin_le_nhds)
  · have hlt : t < a := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hta)
    exact (tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (by simpa using hlt)
      (by simp)).comp (tendsto_sub_ofReal_nhdsWithin t a)

/-- Telescoping over the breakpoints to the right of the first `K`. -/
private theorem sum_range_ite_sub (V : ℕ → ℝ) {K n : ℕ} (hK : K ≤ n) :
    ∑ j ∈ range n, (if j < K then (0 : ℝ) else 1) * (V j - V (j + 1)) = V K - V n := by
  rw [← sum_range_add_sum_Ico _ hK]
  have h1 : ∑ j ∈ range K, (if j < K then (0 : ℝ) else 1) * (V j - V (j + 1)) = 0 :=
    sum_eq_zero fun j hj => by simp [mem_range.1 hj]
  have h2 : ∑ j ∈ Ico K n, (if j < K then (0 : ℝ) else 1) * (V j - V (j + 1)) =
      ∑ j ∈ Ico K n, (V j - V (j + 1)) :=
    sum_congr rfl fun j hj => by simp [not_lt.2 (mem_Ico.1 hj).1]
  rw [h1, h2, zero_add, sum_Ico_eq_sum_range]
  have := Finset.sum_range_sub' (fun k => V (K + k)) (n - K)
  simp only [← add_assoc, add_zero, Nat.add_sub_cancel' hK] at this
  exact this

namespace StepData

variable (s : StepData)

/-- The boundary function: the value on the interval containing `t` (number of breakpoints
`≤ t`). -/
def bdry (t : ℝ) : ℝ :=
  s.v ⟨(Finset.univ.filter fun j => s.x j ≤ t).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

/-- The bounded harmonic extension in `ℍ` (Specification p. 2: "their harmonic extension means
the bounded harmonic extension in that specified chart"). -/
def harmonicExtH (z : ℂ) : ℝ :=
  stepHarmonicH s.n s.x s.v z

/-- `bdry t = v k` when exactly the breakpoints `x j` with `j < k` are `≤ t`. -/
theorem bdry_eq_of_forall_le_iff {t : ℝ} {k : ℕ} (hk : k ≤ s.n)
    (h : ∀ j : Fin s.n, s.x j ≤ t ↔ (j : ℕ) < k) :
    s.bdry t = s.v ⟨k, Nat.lt_succ_of_le hk⟩ := by
  unfold bdry
  congr 2
  exact card_filter_eq_of_forall_iff hk h

theorem harmonicOnNhd_harmonicExtH : InnerProductSpace.HarmonicOnNhd s.harmonicExtH H :=
  fun _ hz => harmonicAt_stepHarmonicH_comp s.n s.x s.v analyticAt_id hz

theorem harmonicExtH_mem_Icc {z : ℂ} (hz : z ∈ H) :
    s.harmonicExtH z ∈ Set.Icc (⨅ k, s.v k) (⨆ k, s.v k) := by
  unfold harmonicExtH stepHarmonicH
  rw [step_sum_eq_range s.n s.v (fun j => arg (z - s.x j) / π)
    (fun k => if h : k < s.n then arg (z - s.x ⟨k, h⟩) / π else 1) (fun j => by simp)]
  refine step_mem_Icc_of_monotone s.n
    (fun k => if h : k < s.n then arg (z - s.x ⟨k, h⟩) / π else 1)
    (fun k => s.v ⟨min k s.n, Nat.lt_succ_of_le (min_le_right _ _)⟩) ?_ ?_ ?_ ?_
  · split_ifs
    · exact div_nonneg (arg_nonneg_iff.2 (sub_ofReal_mem_H hz _).le) Real.pi_pos.le
    · exact zero_le_one
  · intro j hj
    simp only [hj, ↓reduceDIte]
    split_ifs with hj'
    · exact div_le_div_of_nonneg_right
        (arg_sub_ofReal_le_arg_sub_ofReal hz (s.monotone_x (Fin.mk_le_mk.2 (Nat.le_succ j))))
        Real.pi_pos.le
    · exact (div_le_one Real.pi_pos).2 (arg_le_pi _)
  · simp
  · intro k _
    exact ⟨ciInf_le (Set.finite_range _).bddBelow _, le_ciSup (Set.finite_range _).bddAbove _⟩

theorem isBounded_image_harmonicExtH : Bornology.IsBounded (s.harmonicExtH '' H) :=
  (Metric.isBounded_Icc (⨅ k, s.v k) (⨆ k, s.v k)).subset
    (Set.image_subset_iff.2 fun _ hz => s.harmonicExtH_mem_Icc hz)

theorem tendsto_harmonicExtH {t : ℝ} (ht : ∀ j, s.x j ≠ t) :
    Tendsto s.harmonicExtH (𝓝[H] (t : ℂ)) (𝓝 (s.bdry t)) := by
  set K := (univ.filter fun i => s.x i ≤ t).card with hKdef
  have hKn : K ≤ s.n := (card_filter_le _ _).trans (by simp)
  have hlim : Tendsto s.harmonicExtH (𝓝[H] (t : ℂ)) (𝓝 (s.v (Fin.last s.n) +
      ∑ j : Fin s.n, (s.v j.castSucc - s.v j.succ) * ((if s.x j < t then 0 else π) / π))) :=
    tendsto_const_nhds.add (tendsto_finsetSum _ fun j _ =>
      tendsto_const_nhds.mul ((tendsto_arg_sub_ofReal (ht j)).div_const π))
  convert hlim using 2
  have hc : ∀ j : Fin s.n, (if s.x j < t then (0 : ℝ) else π) / π =
      if (j : ℕ) < K then 0 else 1 := by
    intro j
    have hiff : s.x j < t ↔ (j : ℕ) < K := by
      rw [← le_iff_lt_card_filter s.monotone_x t j]
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (ht j)⟩
    by_cases h : s.x j < t
    · simp [h, hiff.1 h]
    · simp [h, mt hiff.2 h, Real.pi_ne_zero]
  rw [step_sum_eq_range s.n s.v _ (fun k => if k < K then 0 else 1) (fun j => (hc j).symm),
    sum_range_ite_sub _ hKn]
  simp only [add_sub_cancel]
  unfold bdry
  congr 2
  rw [Nat.min_eq_left hKn]

/-- **Uniqueness of the bounded harmonic extension** (Phragmén–Lindelöf with a finite
exceptional set): a bounded harmonic function on `ℍ` with the boundary values of `s` off the
breakpoints is `s.harmonicExtH`. -/
theorem eqOn_harmonicExtH {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hbdd : Bornology.IsBounded (u '' H))
    (hlim : ∀ t : ℝ, (∀ j, s.x j ≠ t) → Tendsto u (𝓝[H] (t : ℂ)) (𝓝 (s.bdry t))) :
    EqOn u s.harmonicExtH H := by
  refine eqOn_of_tendsto_sub_H (univ.image s.x) hu s.harmonicOnNhd_harmonicExtH hbdd
    s.isBounded_image_harmonicExtH fun t ht => ?_
  have ht' : ∀ j, s.x j ≠ t := fun j hj => ht (mem_image.2 ⟨j, mem_univ _, hj⟩)
  simpa using (hlim t ht').sub (s.tendsto_harmonicExtH ht')

/-- The one-jump word: value `−lam` on `(−∞, 0)` and `lam` on `[0, ∞)`. -/
def oneJump (lam : ℝ) : StepData where
  n := 1
  x := ![0]
  monotone_x := fun _ _ _ => by simp
  v := ![-lam, lam]

/-- The one-jump word `(−λ, λ)` at `0` with `λ = π/√κ` is QZ's `h0fwd κ + λ`
(REUSE-GEOM handoff: the specification's `ρ = 0` mean). -/
theorem harmonicExtH_one_jump (κ : ℝ) (z : ℂ) :
    (oneJump (π / √κ)).harmonicExtH z = QuantumZipper.h0fwd κ z + π / √κ := by
  show stepHarmonicH 1 ![0] ![-(π / √κ), π / √κ] z = _
  rw [stepHarmonicH, Fin.sum_univ_one]
  simp [QuantumZipper.h0fwd]
  field_simp
  ring

end StepData

end InteractingSLE
