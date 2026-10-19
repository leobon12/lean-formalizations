import HigherDimLFPP.Var.EnergyBall
import LQGDimension.Gaussian.Concentration

/-!
# Lemma 2.2, (2.8): `0 ≤ A_{n,d} - β_{n,d} ≤ C √n`, `e_{n,d} ≤ C n`; and `β_{n,d}/(n log 2) → κ_d`

Paper §2, Lemma 2.2 (`source/higher-dimensional-lfpp-limit.txt` l. 254–279), with the corrections
and explicit constants of audit HA1 (§3.4, findings HA1-F3 and HA1-F8, Details D9).

* `Var.gEM_le_shell` (the shell bound, paper l. 265–276): for every finite `F ⊆ V_n(E)` and
  `γ ∈ [1/2, 1)`, with `w_{n} = 4q³` and `τ = 1 - γ³`,
  `𝕄_F(gCov, -E) ≤ 3q⁴/γ + 1 + c/τ` (`c = cShell = (π³/4)²/2 + 5/2`).
  Proof: split `F` into the energy shells `k ≤ E(f) < k+1`; on a shell
  `M_k - k = X_k + (E M_k - (1-τ)k)` with `X_k = M_k - E M_k - τk`;
  `E M_k ≤ W(k+1) = (k+1)^{1/4} w ≤ γ³(k+1) + 3q⁴/γ` (AM–GM, `amgm_four`);
  `E max_k X_k ≤ log Σ_k E e^{X_k}` (`integral_fsup_le_log_sum`), and Gaussian concentration
  (`LQGDimension.maxConcentration`, constant `π²/8`, HA1-F3) with `Var G(f) ≤ 2π E(f)^{1/2}` gives
  `E e^{X_k} ≤ exp((π³/4)(k+1)^{1/2} - τk)`, whose sum is `≤ exp(c/τ)` (`log_sum_exp_shell_le`).
  The paper's parametrization `(1-τ)^{-1/3}` is replaced by `γ = (1-τ)^{1/3}`, which keeps all the
  algebra polynomial.
* `lemma22a` ((2.8) for every `n ≥ 1`, HA1-F8): `γ = 1 - 1/(2√n)` gives
  `A - β ≤ β/√n + 1 + 2c√n ≤ (A_{1,d} + 1 + 2c) √n`, using `β ≤ A ≤ n A_{1,d}`.
* `betaRateLimit`: `β_{n,d}/(n log 2) → κ_d` (HA4's `BetaRateLimit`), from (2.8) and
  `tendsto_A_div` (Fekete, P-V).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

/-! ## Statements (HA1 Details (c), HA4) -/

/-- **(2.8)** (HA1 Details (c)): `0 ≤ A_{n,d} - β_{n,d} ≤ C √n` and `e_{n,d} ≤ C n` for `n ≥ 1`. -/
def Lemma22a (d : ℕ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    0 ≤ (A n d).toReal - betaN n d ∧ (A n d).toReal - betaN n d ≤ C * Real.sqrt n ∧
    eN n d ≤ C * n

/-- `β_{n,d}/(n log 2) → κ_d` (the last sentence of Lemma 2.2; HA4 `BetaRateLimit`). -/
def BetaRateLimit (d : ℕ) : Prop :=
  Tendsto (fun n : ℕ => betaN n d / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d))

namespace Var

/-! ## Elementary inequalities -/

/-- `E max_k Y_k ≤ log Σ_k a_k` when `E e^{Y_k} ≤ a_k` (from `y ≤ e^{y - L} + L - 1`). -/
lemma integral_fsup_le_log_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {κ : Type*} (K : Finset κ) (hK : K.Nonempty) (Y : κ → Ω → ℝ)
    (hY : ∀ k ∈ K, Integrable (Y k) μ)
    (hYe : ∀ k ∈ K, Integrable (fun x => Real.exp (Y k x)) μ) (a : κ → ℝ)
    (ha : ∀ k ∈ K, ∫ x, Real.exp (Y k x) ∂μ ≤ a k) (hS : 0 < ∑ k ∈ K, a k) :
    ∫ x, (⨆ k : K, Y k x) ∂μ ≤ Real.log (∑ k ∈ K, a k) := by
  set S := ∑ k ∈ K, a k with hSdef
  set L := Real.log S with hL
  have hpt : ∀ x, (⨆ k : K, Y k x) ≤ (L - 1) + Real.exp (-L) * ∑ k ∈ K, Real.exp (Y k x) := by
    intro x
    obtain ⟨k₀, hk₀, heq⟩ := LQGDimension.L23.exists_eq_fsup hK (fun k => Y k x)
    rw [heq]
    have h1 := Real.add_one_le_exp (Y k₀ x - L)
    have h2 : Real.exp (Y k₀ x - L) = Real.exp (-L) * Real.exp (Y k₀ x) := by
      rw [← Real.exp_add]
      ring_nf
    have h3 : Real.exp (Y k₀ x) ≤ ∑ k ∈ K, Real.exp (Y k x) :=
      Finset.single_le_sum (f := fun k => Real.exp (Y k x)) (fun k _ => (Real.exp_pos _).le) hk₀
    have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-L)).le
    linarith
  have hint_main := LQGDimension.L23.integrable_fsup K Y hY
  have hsumint : Integrable (fun x => ∑ k ∈ K, Real.exp (Y k x)) μ := integrable_finsetSum K hYe
  have hRint : Integrable (fun x => (L - 1) + Real.exp (-L) * ∑ k ∈ K, Real.exp (Y k x)) μ :=
    (integrable_const _).add (hsumint.const_mul _)
  have hmono := integral_mono hint_main hRint hpt
  rw [integral_add (integrable_const _) (hsumint.const_mul _), integral_const, integral_const_mul,
    integral_finsetSum K hYe] at hmono
  simp only [probReal_univ, one_smul] at hmono
  have hsum : ∑ k ∈ K, ∫ x, Real.exp (Y k x) ∂μ ≤ S := Finset.sum_le_sum ha
  have hexp : Real.exp (-L) * S = 1 := by
    rw [hL, Real.exp_neg, Real.exp_log hS]
    field_simp
  have h5 := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (-L)).le
  linarith

/-- AM–GM: `4 q³ s ≤ γ³ s⁴ + 3 q⁴ / γ` for `q, s ≥ 0`, `γ > 0`.  With `w = 4q³`, `e = q⁴`,
`s = r^{1/4}` and `c = γ³` this is `w r^{1/4} - c r ≤ 3 c^{-1/3} e` (paper l. 263–264). -/
lemma amgm_four {q s γ : ℝ} (hq : 0 ≤ q) (hs : 0 ≤ s) (hγ : 0 < γ) :
    s * (4 * q ^ 3) ≤ γ ^ 3 * s ^ 4 + 3 * q ^ 4 / γ := by
  have key : γ ^ 3 * s ^ 4 + 3 * q ^ 4 / γ - s * (4 * q ^ 3) =
      (γ * s - q) ^ 2 * ((γ * s) ^ 2 + 2 * (γ * s) * q + 3 * q ^ 2) / γ := by
    field_simp
    ring
  have h : 0 ≤ (γ * s - q) ^ 2 * ((γ * s) ^ 2 + 2 * (γ * s) * q + 3 * q ^ 2) / γ := by
    positivity
  linarith

/-- The absolute constant of the shell bound: `c = (π³/4)²/2 + 5/2`. -/
def cShell : ℝ := (Real.pi ^ 3 / 4) ^ 2 / 2 + 5 / 2

lemma cShell_pos : 0 < cShell := by
  unfold cShell
  positivity

/-- `log Σ_{k ∈ K} exp((π³/4)(k+1)^{1/2} - τ k) ≤ c / τ` for `0 < τ ≤ 1` (paper l. 276–278:
`C√(k+1) ≤ τ(k+1)/2 + C²/(2τ)` and the geometric series). -/
lemma log_sum_exp_shell_le (K : Finset ℕ) (hK : K.Nonempty) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    Real.log (∑ k ∈ K, Real.exp (Real.pi ^ 3 / 4 * √((k : ℝ) + 1) - τ * k)) ≤ cShell / τ := by
  set c₁ : ℝ := Real.pi ^ 3 / 4 with hc₁
  set D : ℝ := c₁ ^ 2 / (2 * τ) + τ / 2 with hD
  set ρ : ℝ := Real.exp (-(τ / 2)) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    calc ρ = Real.exp (-(τ / 2)) := hρ
      _ < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have hterm : ∀ k : ℕ, Real.exp (c₁ * √((k : ℝ) + 1) - τ * k) ≤ Real.exp D * ρ ^ k := by
    intro k
    have hy := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
    set y := √((k : ℝ) + 1) with hydef
    have h1 : c₁ * y - τ * k ≤ D + k * (-(τ / 2)) := by
      have h0 : 0 ≤ (τ * y - c₁) ^ 2 / (2 * τ) := by positivity
      have e : (τ * y - c₁) ^ 2 / (2 * τ) = τ * y ^ 2 / 2 - c₁ * y + c₁ ^ 2 / (2 * τ) := by
        field_simp
        ring
      rw [hy] at e
      rw [hD]
      have e2 : τ * ((k : ℝ) + 1) / 2 = τ * k / 2 + τ / 2 := by ring
      linarith
    calc Real.exp (c₁ * y - τ * k) ≤ Real.exp (D + k * (-(τ / 2))) := Real.exp_le_exp.2 h1
      _ = Real.exp D * ρ ^ k := by rw [Real.exp_add, Real.exp_nat_mul]
  set N := K.sup id + 1 with hN
  have hKN : K ⊆ Finset.range N := fun k hk =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  have hgeom : ∑ k ∈ Finset.range N, ρ ^ k ≤ 1 / (1 - ρ) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hρ0 hρ1
    rwa [← Finset.range_eq_Ico, pow_zero] at h
  have hinv : 1 / (1 - ρ) ≤ 1 + 2 / τ := by
    have he : 1 + τ / 2 ≤ Real.exp (τ / 2) := by linarith [Real.add_one_le_exp (τ / 2)]
    have hρ' : ρ ≤ 1 / (1 + τ / 2) := by
      rw [hρ, Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) he
    have h1ρ : 0 < 1 - ρ := by linarith
    rw [div_le_iff₀ h1ρ]
    have e : (1 + 2 / τ) * (1 - 1 / (1 + τ / 2)) = 1 := by
      field_simp
      ring
    calc (1 : ℝ) = (1 + 2 / τ) * (1 - 1 / (1 + τ / 2)) := e.symm
      _ ≤ (1 + 2 / τ) * (1 - ρ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsum : ∑ k ∈ K, Real.exp (c₁ * √((k : ℝ) + 1) - τ * k) ≤ Real.exp D * (1 + 2 / τ) := by
    calc _ ≤ ∑ k ∈ K, Real.exp D * ρ ^ k := Finset.sum_le_sum fun k _ => hterm k
      _ ≤ ∑ k ∈ Finset.range N, Real.exp D * ρ ^ k :=
          Finset.sum_le_sum_of_subset_of_nonneg hKN (fun _ _ _ => by positivity)
      _ = Real.exp D * ∑ k ∈ Finset.range N, ρ ^ k := (Finset.mul_sum _ _ _).symm
      _ ≤ Real.exp D * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left hgeom (Real.exp_pos _).le
      _ ≤ Real.exp D * (1 + 2 / τ) := mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
  have hpos : 0 < ∑ k ∈ K, Real.exp (c₁ * √((k : ℝ) + 1) - τ * k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) hK
  have h2τ : 0 < 1 + 2 / τ := by positivity
  calc Real.log (∑ k ∈ K, Real.exp (c₁ * √((k : ℝ) + 1) - τ * k))
      ≤ Real.log (Real.exp D * (1 + 2 / τ)) := Real.log_le_log hpos hsum
    _ = D + Real.log (1 + 2 / τ) := by
        rw [Real.log_mul (Real.exp_pos _).ne' h2τ.ne', Real.log_exp]
    _ ≤ D + 2 / τ := by
        have := Real.log_le_sub_one_of_pos h2τ
        linarith
    _ ≤ cShell / τ := by
        have hτ2 : τ / 2 ≤ 1 / (2 * τ) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith
        have e : cShell / τ = c₁ ^ 2 / (2 * τ) + 1 / (2 * τ) + 2 / τ := by
          rw [cShell, ← hc₁]
          field_simp
          ring
        rw [e, hD]
        linarith

/-! ## The shell bound -/

section Shell

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The shell bound** (paper l. 265–276; HA1 D9, step 2).  Let `F ⊆ V_n(E)` be finite, `q ≥ 0`
with `𝕄_G(gCov, 0) ≤ s · 4q³` for every finite `G` in the energy ball of radius `s⁴`
(homogeneity, with `w = 4q³`), and `γ ∈ [1/2, 1)`.  Then
`𝕄_F(gCov, -E) ≤ 3q⁴/γ + 1 + c/(1 - γ³)`. -/
theorem gEM_le_shell {n : ℕ} (F : Finset (Vg E n)) {q γ : ℝ} (hq : 0 ≤ q) (hγ : 1 / 2 ≤ γ)
    (hγ1 : γ < 1)
    (hW : ∀ G : Finset (Vg E n), ∀ s : ℝ, 0 < s → (∀ f ∈ G, energy (f : ℝ → E) ≤ s ^ 4) →
      gaussianExpectedMax G (fun f g => gCov (f : ℝ → E) g) 0 ≤ s * (4 * q ^ 3)) :
    gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g) (fun f => -energy (f : ℝ → E)) ≤
      3 * q ^ 4 / γ + 1 + cShell / (1 - γ ^ 3) := by
  classical
  have hγ0 : 0 < γ := by linarith
  have hγ3 : γ ^ 3 < 1 := pow_lt_one₀ hγ0.le hγ1 (by norm_num)
  have hγ3' : 0 < γ ^ 3 := by positivity
  set τ : ℝ := 1 - γ ^ 3 with hτ
  have hτ0 : 0 < τ := by linarith
  have hτ1 : τ ≤ 1 := by linarith
  have hRHS : 0 ≤ 3 * q ^ 4 / γ + 1 + cShell / τ := by
    have := cShell_pos
    positivity
  rcases F.eq_empty_or_nonempty with hF | hFne
  · rw [hF, gEM_empty]
    exact hRHS
  obtain ⟨v, hv, hvb⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F
    (fun f g => gCov (f : ℝ → E) g) (gCov_psdOn_Vg n F)
  set sh : Vg E n → ℕ := fun f => ⌊energy (f : ℝ → E)⌋₊ with hsh
  set K : Finset ℕ := F.image sh with hK
  have hKne : K.Nonempty := hFne.image sh
  set Fk : ℕ → Finset (Vg E n) := fun k => F.filter (fun f => sh f = k) with hFk
  have hFkF : ∀ k, Fk k ⊆ F := fun k => Finset.filter_subset _ _
  have hEk : ∀ k, ∀ f ∈ Fk k, energy (f : ℝ → E) ≤ (k : ℝ) + 1 := by
    intro k f hf
    have h1 : sh f = k := (Finset.mem_filter.1 hf).2
    have h2 := Nat.lt_floor_add_one (energy (f : ℝ → E))
    have h3 : ⌊energy (f : ℝ → E)⌋₊ = k := h1
    rw [h3] at h2
    exact h2.le
  set m : ℕ → ℝ := fun k => vecExpectedMax (Fk k) v (fun _ => 0) with hm
  set Y : ℕ → EuclideanSpace ℝ F → ℝ := fun k x => (⨆ f : Fk k, ⟪v f, x⟫) - m k - τ * k
    with hY
  -- the mean of the shell maximum
  have hmean : ∀ k : ℕ, m k ≤ γ ^ 3 * k + γ ^ 3 + 3 * q ^ 4 / γ := by
    intro k
    have hs : 0 < ((k : ℝ) + 1) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    have hs4 : (((k : ℝ) + 1) ^ (1 / 4 : ℝ)) ^ 4 = (k : ℝ) + 1 := by
      have := Real.rpow_inv_natCast_pow (x := (k : ℝ) + 1) (n := 4) (by positivity) (by norm_num)
      rwa [show ((4 : ℕ) : ℝ)⁻¹ = (1 / 4 : ℝ) by norm_num] at this
    have hE : ∀ f ∈ Fk k, energy (f : ℝ → E) ≤ (((k : ℝ) + 1) ^ (1 / 4 : ℝ)) ^ 4 := by
      intro f hf
      rw [hs4]
      exact hEk k f hf
    have h1 := hW (Fk k) _ hs hE
    rw [gEM_eq_vec_of_subset (hFkF k) _ v hv] at h1
    have h2 := amgm_four hq hs.le hγ0 (s := ((k : ℝ) + 1) ^ (1 / 4 : ℝ))
    rw [hs4] at h2
    have h3 : m k ≤ γ ^ 3 * ((k : ℝ) + 1) + 3 * q ^ 4 / γ := h1.trans h2
    linarith [show γ ^ 3 * ((k : ℝ) + 1) = γ ^ 3 * k + γ ^ 3 by ring]
  -- pointwise reduction to the shells
  have hpt : ∀ x : EuclideanSpace ℝ F, (⨆ f : F, ⟪v f, x⟫ + -energy (f : ℝ → E)) ≤
      (⨆ k : K, Y k x) + (1 + 3 * q ^ 4 / γ) := by
    intro x
    refine LQGDimension.L23.fsup_le' hFne (g := fun f => ⟪v f, x⟫ + -energy (f : ℝ → E))
      fun f hf => ?_
    have hfk : f ∈ Fk (sh f) := Finset.mem_filter.2 ⟨hf, rfl⟩
    have hkK : sh f ∈ K := Finset.mem_image_of_mem sh hf
    have h1 : ⟪v f, x⟫ ≤ ⨆ g : Fk (sh f), ⟪v g, x⟫ :=
      LQGDimension.L23.le_fsup (fun g => ⟪v g, x⟫) hfk
    have h2 : ((sh f : ℕ) : ℝ) ≤ energy (f : ℝ → E) := Nat.floor_le (energy_nonneg _)
    have h3 : Y (sh f) x ≤ ⨆ j : K, Y j x := LQGDimension.L23.le_fsup (fun j => Y j x) hkK
    have h4 := hmean (sh f)
    have h5 : Y (sh f) x = (⨆ g : Fk (sh f), ⟪v g, x⟫) - m (sh f) - τ * (sh f : ℕ) := rfl
    have h6 : τ * ((sh f : ℕ) : ℝ) = (sh f : ℕ) - γ ^ 3 * (sh f : ℕ) := by
      rw [hτ]
      ring
    linarith
  -- exponential moments of the shell fluctuations
  have hYint : ∀ k ∈ K, Integrable (Y k) (stdGaussian (EuclideanSpace ℝ F)) := fun k _ =>
    ((LQGDimension.L23.integrable_fsup_inner (Fk k) v).sub (integrable_const _)).sub
      (integrable_const _)
  have hYe : ∀ k ∈ K, Integrable (fun x => Real.exp (Y k x))
      (stdGaussian (EuclideanSpace ℝ F)) := by
    intro k _
    have h := LQGDimension.L23.integrable_exp_mul_fsup (Fk k) v (fun _ => 0) zero_le_one
      (m k + τ * k)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [hY, add_zero, one_mul]
    congr 1
    ring
  have hexp : ∀ k ∈ K, ∫ x, Real.exp (Y k x) ∂(stdGaussian (EuclideanSpace ℝ F)) ≤
      Real.exp (Real.pi ^ 3 / 4 * √((k : ℝ) + 1) - τ * k) := by
    intro k _
    have hσ : ∀ f ∈ Fk k, ‖v f‖ ≤ √(2 * Real.pi * √((k : ℝ) + 1)) := by
      intro f hf
      apply Real.le_sqrt_of_sq_le
      have hfF := hFkF k hf
      rw [← real_inner_self_eq_norm_sq, hv f hfF f hfF]
      have h1 := gCov_self_le f.2
      have h3 : √(energy (f : ℝ → E)) ≤ √((k : ℝ) + 1) := Real.sqrt_le_sqrt (hEk k f hf)
      calc gCov (f : ℝ → E) f ≤ 2 * Real.pi * √(energy (f : ℝ → E)) := h1
        _ ≤ 2 * Real.pi * √((k : ℝ) + 1) := by gcongr
    have hconc := LQGDimension.L23.integral_exp_mul_fsup_sub_le LQGDimension.maxConcentration
      (Fk k) v hσ 1
    have e : ∀ x, Real.exp (Y k x) = Real.exp (-(τ * k)) *
        Real.exp (1 * ((⨆ f : Fk k, ⟪v f, x⟫) - vecExpectedMax (Fk k) v (fun _ => 0))) := by
      intro x
      rw [← Real.exp_add]
      congr 1
      simp only [hY, hm]
      ring
    rw [integral_congr_ae (Eventually.of_forall e), integral_const_mul]
    have hσ2 : √(2 * Real.pi * √((k : ℝ) + 1)) ^ 2 = 2 * Real.pi * √((k : ℝ) + 1) :=
      Real.sq_sqrt (by positivity)
    calc Real.exp (-(τ * k)) * ∫ x, Real.exp (1 * ((⨆ f : Fk k, ⟪v f, x⟫) -
          vecExpectedMax (Fk k) v (fun _ => 0))) ∂(stdGaussian (EuclideanSpace ℝ F))
        ≤ Real.exp (-(τ * k)) *
          Real.exp (Real.pi ^ 2 / 8 * 1 ^ 2 * √(2 * Real.pi * √((k : ℝ) + 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left hconc (Real.exp_pos _).le
      _ = Real.exp (Real.pi ^ 3 / 4 * √((k : ℝ) + 1) - τ * k) := by
          rw [← Real.exp_add, hσ2]
          congr 1
          ring
  have hlse := integral_fsup_le_log_sum K hKne Y hYint hYe _ hexp
    (Finset.sum_pos (fun k _ => Real.exp_pos _) hKne)
  have hser := log_sum_exp_shell_le K hKne hτ0 hτ1
  -- assemble
  rw [hvb]
  unfold vecExpectedMax
  have hint1 := LQGDimension.integrable_iSup_inner_add F v (fun f => -energy (f : ℝ → E))
  have hint0 := LQGDimension.L23.integrable_fsup K Y hYint
  have hint2 : Integrable (fun x => (⨆ k : K, Y k x) + (1 + 3 * q ^ 4 / γ))
      (stdGaussian (EuclideanSpace ℝ F)) := hint0.add (integrable_const _)
  calc ∫ x, (⨆ f : F, ⟪v f, x⟫ + -energy (f : ℝ → E)) ∂(stdGaussian (EuclideanSpace ℝ F))
      ≤ ∫ x, ((⨆ k : K, Y k x) + (1 + 3 * q ^ 4 / γ)) ∂(stdGaussian (EuclideanSpace ℝ F)) :=
        integral_mono hint1 hint2 hpt
    _ = (∫ x, (⨆ k : K, Y k x) ∂(stdGaussian (EuclideanSpace ℝ F))) + (1 + 3 * q ^ 4 / γ) := by
        rw [integral_add hint0 (integrable_const _), integral_const]
        simp
    _ ≤ cShell / τ + (1 + 3 * q ^ 4 / γ) := by linarith
    _ = 3 * q ^ 4 / γ + 1 + cShell / τ := by ring

end Shell

/-! ## (2.8) -/

/-- `A_{n,d} ≤ n A_{1,d}` (subadditivity and `A_{0,d} = 0`). -/
lemma A_toReal_le_mul {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : (A n d).toReal ≤ n * (A 1 d).toReal := by
  induction n with
  | zero =>
    have h0 : A 0 d = 0 := Ag_zero
    simp [h0]
  | succ k ih =>
    have h := A_toReal_subadd hd k 1
    push_cast
    linarith

/-- **The shell bound for `A_{n,d}`**: `A_{n,d} ≤ β_{n,d}/γ + 1 + c/(1 - γ³)` for `γ ∈ [1/2, 1)`. -/
theorem A_le_shell {d : ℕ} (hd : 2 ≤ d) (n : ℕ) {γ : ℝ} (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) :
    (A n d).toReal ≤ betaN n d / γ + 1 + cShell / (1 - γ ^ 3) := by
  have hW : ∀ G : Finset (Vg (Rd (d - 1)) n), ∀ s : ℝ, 0 < s →
      (∀ f ∈ G, energy (f : ℝ → Rd (d - 1)) ≤ s ^ 4) →
      gaussianExpectedMax G (fun f g => gCov (f : ℝ → Rd (d - 1)) g) 0 ≤
        s * (4 * qN n d ^ 3) := by
    intro G s hs hG
    rw [← wN_eq]
    exact gEM_le_of_energy_le hd G hs hG
  have h : A n d ≤ ((3 * qN n d ^ 4 / γ + 1 + cShell / (1 - γ ^ 3) : ℝ) : EReal) :=
    Ag_le_of_forall fun F =>
      EReal.coe_le_coe_iff.2 (gEM_le_shell F (qN_nonneg n d) hγ hγ1 hW)
  rw [← A_coe_toReal hd n] at h
  have h' := EReal.coe_le_coe_iff.1 h
  rw [betaN, eN_eq]
  linarith

end Var

open Var

/-- **Lemma 2.2, (2.8)** (HA1 D9), for every `d ≥ 2`: there is `C` with
`0 ≤ A_{n,d} - β_{n,d} ≤ C √n` and `e_{n,d} ≤ C n` for all `n ≥ 1`. -/
theorem lemma22a (d : ℕ) (hd : 2 ≤ d) : Lemma22a d := by
  set A1 := (A 1 d).toReal with hA1def
  have hA1 : 0 ≤ A1 := A_toReal_nonneg 1 d
  refine ⟨A1 + 1 + 2 * cShell, fun n hn => ?_⟩
  have hc := cShell_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hβ := betaN_le_A hd n
  have hβ0 := betaN_nonneg n d
  have hAn : (A n d).toReal ≤ n * A1 := A_toReal_le_mul hd n
  set r := √(n : ℝ) with hrdef
  have hr2 : r ^ 2 = n := Real.sq_sqrt (by positivity)
  have hr1 : 1 ≤ r := by
    rw [hrdef]
    exact Real.one_le_sqrt.2 hn1
  have hr0 : 0 < r := by linarith
  set t : ℝ := 1 / r with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hr0]
    exact hr1
  have htr : t * r = 1 := by
    rw [htdef]
    field_simp
  set γ : ℝ := 1 - t / 2 with hγdef
  have hγ : 1 / 2 ≤ γ := by linarith
  have hγ1 : γ < 1 := by linarith
  have hγ0 : 0 < γ := by linarith
  have hA := A_le_shell hd n hγ hγ1
  -- `1/γ ≤ 1 + t`
  have hγinv : betaN n d / γ ≤ betaN n d * (1 + t) := by
    rw [div_le_iff₀ hγ0]
    have : 1 ≤ (1 + t) * γ := by
      rw [hγdef]
      nlinarith
    nlinarith
  -- `1/(1 - γ³) ≤ 2 r`
  have hτ : cShell / (1 - γ ^ 3) ≤ cShell * (2 * r) := by
    have hγ3 : γ ^ 3 ≤ γ := by
      have h1 : γ ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have hpos : 0 < 1 - γ ^ 3 := by linarith
    rw [div_le_iff₀ hpos]
    have h2 : t / 2 ≤ 1 - γ ^ 3 := by linarith
    have h3 : 1 ≤ 2 * r * (t / 2) := by nlinarith
    have h4 : 2 * r * (t / 2) ≤ 2 * r * (1 - γ ^ 3) := by
      apply mul_le_mul_of_nonneg_left h2
      linarith
    nlinarith
  -- `β t ≤ A t ≤ n A₁ / r = r A₁`
  have hβt : betaN n d * t ≤ r * A1 := by
    have h1 : betaN n d * t ≤ (n * A1) * t := by
      apply mul_le_mul_of_nonneg_right (hβ.trans hAn) ht0.le
    have h2 : (n * A1) * t = r * A1 := by
      rw [← hr2, htdef]
      field_simp
    linarith
  refine ⟨by linarith, ?_, ?_⟩
  · have e : (A1 + 1 + 2 * cShell) * r = r * A1 + r + cShell * (2 * r) := by ring
    rw [e]
    nlinarith
  · have he : eN n d = betaN n d / 3 := by
      rw [betaN]
      ring
    rw [he]
    have h1 : betaN n d / 3 ≤ n * A1 / 3 := by linarith
    have h2 : (n : ℝ) * A1 / 3 ≤ (A1 + 1 + 2 * cShell) * n := by nlinarith
    linarith

/-- **`β_{n,d}/(n log 2) → κ_d`** (last sentence of Lemma 2.2; HA4 `BetaRateLimit`), for every
`d ≥ 2`. -/
theorem betaRateLimit (d : ℕ) (hd : 2 ≤ d) : BetaRateLimit d := by
  obtain ⟨C, hC⟩ := lemma22a d hd
  have hA := tendsto_A_div hd
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have herr : Tendsto (fun n : ℕ => C / Real.log 2 * √(1 / (n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
    rw [Real.sqrt_zero] at h
    simpa using h.const_mul (C / Real.log 2)
  have hlow : Tendsto (fun n : ℕ => (A n d).toReal / ((n : ℝ) * Real.log 2) -
      C / Real.log 2 * √(1 / (n : ℝ))) atTop (𝓝 (kappa d)) := by
    simpa using hA.sub herr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hA ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨-, h1, -⟩ := hC n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hs2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by linarith)
    have hden : 0 < (n : ℝ) * Real.log 2 := by positivity
    have e : C / Real.log 2 * √(1 / (n : ℝ)) = C * √(n : ℝ) / ((n : ℝ) * Real.log 2) := by
      rw [one_div, Real.sqrt_inv, ← Real.sqrt_div_self]
      ring
    rw [e, sub_le_iff_le_add, ← add_div, div_le_div_iff_of_pos_right hden]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨h0, -, -⟩ := hC n hn
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end HigherDimLFPP
