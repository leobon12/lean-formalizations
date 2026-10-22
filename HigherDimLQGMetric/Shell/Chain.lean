import HigherDimLQGMetric.Shell.ChainExit

/-!
# Sphere-chain estimates in `ℝ^d`

Port of `LQGMetric.LM.lm_chain_det` from `ℂ` to `Rd d`, generalized to an
extended directed distance. The counting variant follows the same backward search.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Time-increment sphere chain (MA6 P1, Statement A). -/
theorem sphere_chain (hd : 2 ≤ d) (δ : Rd d → Rd d → ℝ≥0∞)
    (hδ0 : ∀ x, δ x x = 0) (hδt : ∀ x y z, δ x z ≤ δ x y + δ y z)
    {ρ ε : ℝ} (hρ : 0 < ρ) (P : ℝ → Rd d)
    (hP : ContinuousOn P (Icc 0 1)) (ℓ : ℝ → ℝ) (hℓ : MonotoneOn ℓ (Icc 0 1))
    (good : Rd d → ℝ → Prop)
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∃ w r, ρ ≤ r ∧ r ≤ ε ∧ ‖P s - w‖ < r / 2 ∧ good w r)
    (C : ℝ≥0∞)
    (hgood : ∀ w r, good w r → ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      a ≤ b → ‖P a - w‖ < r / 2 → ‖P b - w‖ = r →
      ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
        δ u v ≤ C * ENNReal.ofReal (ℓ b - ℓ a)) :
    ∃ x y, ‖x - P 0‖ ≤ 2 * ε ∧ ‖y - P 1‖ ≤ 2 * ε ∧
      δ x y ≤ C * ENNReal.ofReal (ℓ 1 - ℓ 0) := by
  obtain ⟨W, R, S, J, hρR, hRε, hin, hg, hS0, hSI, hSmono, hbefore, hstop⟩ :=
    exists_sphere_exits hρ P hP good hcov
  let p : ℕ → Rd d := fun n => P (S n)
  let w : ℕ → Rd d := fun n => W (S (n - 1))
  let r : ℕ → ℝ := fun n => R (S (n - 1))
  let T : ℕ → ℝ := fun n => ℓ (S n)
  have hT : Monotone T := fun i j hij => hℓ (hSI i) (hSI j) (hSmono hij)
  have hin' : ∀ i, 1 ≤ i → i ≤ J + 1 → ‖p (i - 1) - w i‖ < r i / 2 :=
    fun i _ _ => hin _ (hSI _)
  have hon' : ∀ i, 1 ≤ i → i < J + 1 → ‖p i - w i‖ = r i := by
    intro i hi1 hiJ
    change ‖P (S i) - W (S (i - 1))‖ = R (S (i - 1))
    simpa only [show (i - 1) + 1 = i by omega] using hbefore (i - 1) (by omega)
  have hr' : ∀ i, 0 < r i := fun i => lt_of_lt_of_le hρ (hρR _ (hSI _))
  have hrε : ∀ i, r i ≤ ε := fun i => hRε _ (hSI _)
  have hdiam : ∀ i, 1 ≤ i → i < J + 1 →
      ∀ u ∈ sphere (w i) (r i), ∀ v ∈ sphere (w i) (r i),
      δ u v ≤ C * ENNReal.ofReal (T i - T (i - 1)) := by
    intro i hi1 hiJ
    have hcross : ‖P (S i) - W (S (i - 1))‖ = R (S (i - 1)) := by
      simpa only [show (i - 1) + 1 = i by omega] using hbefore (i - 1) (by omega)
    exact hgood _ _ (hg _ (hSI _)) _ (hSI _) _ (hSI _) (hSmono (Nat.sub_le i 1))
      (hin' i hi1 (by omega)) hcross
  have hend : ‖P (S J) - P 1‖ ≤ 2 * ε := by
    have h2 := hin _ (hSI J)
    have h3 := hRε _ (hSI J)
    have h4 := hρR _ (hSI J)
    calc
      ‖P (S J) - P 1‖ = ‖(P (S J) - W (S J)) - (P 1 - W (S J))‖ := by
        congr 1; abel
      _ ≤ ‖P (S J) - W (S J)‖ + ‖P 1 - W (S J)‖ := norm_sub_le _ _
      _ ≤ 2 * ε := by linarith [hstop]
  have hℓ1 : ℓ (S J) - ℓ (S 0) ≤ ℓ 1 - ℓ 0 := by
    rw [hS0]
    linarith [hℓ (hSI J) ⟨zero_le_one, le_rfl⟩ (hSI J).2]
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · refine ⟨P (S J), P (S J), ?_, hend, ?_⟩
    · rw [hJ0, hS0, sub_self, norm_zero]
      linarith [hRε _ (hSI 0), hρR _ (hSI 0)]
    · rw [hδ0]
      exact bot_le
  · obtain ⟨x, hx, hxu⟩ := sphere_chain_main hd δ hδ0 hδt C p w r T (J + 1)
      hT hin' hon' hr' hrε hdiam J hJ0 (by omega) (P (S J))
      (by rw [mem_sphere, dist_eq_norm]; exact hon' J hJ0 (by omega))
    refine ⟨x, P (S J), by simpa only [p, hS0] using hx, hend, ?_⟩
    calc
      δ x (P (S J)) ≤ C * ENNReal.ofReal (ℓ (S J) - ℓ (S 0)) := hxu
      _ ≤ C * ENNReal.ofReal (ℓ 1 - ℓ 0) := by gcongr

/-- Counting, set-to-set sphere chain (MA6 P1, Statement B). -/
theorem chain_setDist (hd : 2 ≤ d) (δ : Rd d → Rd d → ℝ≥0∞)
    (_hδ0 : ∀ x, δ x x = 0) (hδt : ∀ x y z, δ x z ≤ δ x y + δ y z)
    {ρ ε Λ : ℝ} (hρ : 0 < ρ) (hΛ : 0 ≤ Λ)
    (P : ℝ → Rd d) (hP : LipschitzOnWith (Real.toNNReal Λ) P (Icc 0 1))
    (good : Rd d → ℝ → Prop)
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∃ w r, ρ ≤ r ∧ r ≤ ε ∧ ‖P s - w‖ < r / 2 ∧ good w r)
    (M : ℝ≥0∞) (hM : ∀ w r, good w r →
      ∀ u ∈ sphere w r, ∀ v ∈ sphere w r, δ u v ≤ M)
    {K₁ K₂ : Set (Rd d)} (hK₁ : IsConnected K₁) (hK₂ : IsConnected K₂)
    (h₀ : P 0 ∈ K₁) (h₁ : P 1 ∈ K₂)
    (hK₁b : ∀ c : Rd d, ¬ K₁ ⊆ ball c ε)
    (hK₂b : ∀ c : Rd d, ¬ K₂ ⊆ ball c ε) :
    ∃ x ∈ K₁, ∃ y ∈ K₂, δ x y ≤ ENNReal.ofReal (2 * Λ / ρ + 2) * M := by
  have hPc : ContinuousOn P (Icc 0 1) := hP.continuousOn
  obtain ⟨W, R, S, J, hρR, hRε, hin, hg, hS0, hSI, hSmono, hbefore, hstop⟩ :=
    exists_sphere_exits hρ P hPc good hcov
  let p : ℕ → Rd d := fun n => P (S n)
  let w : ℕ → Rd d := fun n => W (S (n - 1))
  let r : ℕ → ℝ := fun n => R (S (n - 1))
  have hin' : ∀ i, 1 ≤ i → i ≤ J + 1 → ‖p (i - 1) - w i‖ < r i / 2 :=
    fun i _ _ => hin _ (hSI _)
  have hon' : ∀ i, 1 ≤ i → i < J + 1 → ‖p i - w i‖ = r i := by
    intro i hi1 hiJ
    change ‖P (S i) - W (S (i - 1))‖ = R (S (i - 1))
    simpa only [show (i - 1) + 1 = i by omega] using hbefore (i - 1) (by omega)
  have hr' : ∀ i, 0 < r i := fun i => lt_of_lt_of_le hρ (hρR _ (hSI _))
  have hrε : ∀ i, r i ≤ ε := fun i => hRε _ (hSI _)
  have hdiam : ∀ i, 1 ≤ i → i ≤ J + 1 →
      ∀ u ∈ sphere (w i) (r i), ∀ v ∈ sphere (w i) (r i), δ u v ≤ M := by
    intro i _ _
    exact hM _ _ (hg _ (hSI _))
  have hstep : ∀ i < J, ρ / 2 ≤ Λ * (S (i + 1) - S i) := by
    intro i hi
    have hmove : ρ / 2 ≤ ‖P (S (i + 1)) - P (S i)‖ := by
      have htri : ‖P (S (i + 1)) - W (S i)‖ ≤
          ‖P (S (i + 1)) - P (S i)‖ + ‖P (S i) - W (S i)‖ := by
        calc
          ‖P (S (i + 1)) - W (S i)‖ =
              ‖(P (S (i + 1)) - P (S i)) + (P (S i) - W (S i))‖ := by
                congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith [hbefore i hi, hin _ (hSI i), hρR _ (hSI i)]
    have hLip := hP.dist_le_mul (S (i + 1)) (hSI (i + 1)) (S i) (hSI i)
    rw [dist_eq_norm, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (hSmono (Nat.le_succ i))),
      Real.coe_toNNReal Λ hΛ] at hLip
    linarith
  have hlin : ∀ n ≤ J, (n : ℝ) * ρ / 2 ≤ Λ * S n := by
    intro n hn
    induction n with
    | zero => simp [hS0]
    | succ n ih =>
      have hi := ih (by omega)
      have hs := hstep n (by omega)
      push_cast
      nlinarith
  have hJbound : (J : ℝ) ≤ 2 * Λ / ρ := by
    have hsj := (hSI J).2
    have hh := hlin J le_rfl
    have hmul : Λ * S J ≤ Λ := by nlinarith
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hK₂not : ¬ K₂ ⊆ ball (W (S J)) (R (S J)) := by
    intro hs
    exact hK₂b (W (S J)) (hs.trans (ball_subset_ball (hRε _ (hSI J))))
  obtain ⟨y, hyK₂, hyS⟩ := connected_inter_sphere K₂ hK₂
    ⟨P 1, h₁, by rwa [mem_ball, dist_eq_norm]⟩ hK₂not
  obtain ⟨x, hxK₁, hxy⟩ := sphere_chain_main_set hd δ hδt M p w r (J + 1)
    hin' hon' hr' hrε hdiam hK₁ (by simpa only [p, hS0] using h₀) hK₁b
    (J + 1) (by omega) le_rfl y (by simpa only [w, r, Nat.add_sub_cancel] using hyS)
  refine ⟨x, hxK₁, y, hyK₂, ?_⟩
  calc
    δ x y ≤ ((J + 1 : ℕ) : ℝ≥0∞) * M := hxy
    _ ≤ ENNReal.ofReal (2 * Λ / ρ + 2) * M := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      have hcast : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

end HigherDimLQGMetric
