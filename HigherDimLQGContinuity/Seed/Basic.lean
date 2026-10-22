import HigherDimLQGContinuity.Amplify.Prop33
import HigherDimLQGContinuity.Endpoint.Profile

/-!
# Propositions 3.6–3.7 (packet P8b), part 1: deterministic and probabilistic helpers

Blueprint Part A, §3.3–3.4 (`a:prop36`, `a:prop37-seed`, `a:prop37`) and Part C `c:lem-p37`; NA1 items 28–29, R11,
R12. This file collects the small facts used by the three propositions:

* monotonicity of `CompOn` in the coefficient and the error, and antitonicity of `H↑` in the coefficient;
* `supDistLU ≤ u` from pointwise bounds, and the identification of the event of `a:prop37` with the `supDistLU`
  form of the logarithmic profiles (`p8b_logEvent_eq`);
* the two-sided comparison `E ≤ cD + e`, `D ≤ cE + e` turned into a bound on `|D - E|` (given a bound `M` on both
  metrics) and into a bound on the logarithmic profiles;
* the uniform diameter quantile `M_s` of Proposition 3.6 (from (E3) of Lemma 2.1 and Markov's inequality).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Comparisons and the bad events -/

/-- `CompOn` is monotone in the coefficient and in the error (distances are nonnegative). -/
theorem p8b_compOn_mono {E' D' : ContMetric d} {c c' e e' R : ℝ} (hc : c ≤ c') (he : e ≤ e')
    (h : CompOn E' D' c e R) : CompOn E' D' c' e' R := by
  intro x hx y hy
  have h1 := h x hx y hy
  have h2 : c * D'.1 (x, y) ≤ c' * D'.1 (x, y) := mul_le_mul_of_nonneg_right hc (D'.nonneg x y)
  linarith

/-- The bad comparison event shrinks when the coefficient grows. -/
theorem p8b_notCompOn_anti {D E : DistRd d → ContMetric d} {c c' e R : ℝ} (hc : c ≤ c') :
    {g | ¬ CompOn (rho E g) (rho D g) c' e R} ⊆ {g | ¬ CompOn (rho E g) (rho D g) c e R} :=
  fun _ hg hcomp => hg (p8b_compOn_mono hc le_rfl hcomp)

/-- The bad comparison event shrinks when the error grows. -/
theorem p8b_notCompOn_anti_err {D E : DistRd d → ContMetric d} {c e e' R : ℝ} (he : e ≤ e') :
    {g | ¬ CompOn (rho E g) (rho D g) c e' R} ⊆ {g | ¬ CompOn (rho E g) (rho D g) c e R} :=
  fun _ hg hcomp => hg (p8b_compOn_mono le_rfl he hcomp)

/-- `H↑(D, E; b)` is antitone in `b`. -/
theorem p8b_hup_anti {D E : DistRd d → ContMetric d} {b b' : ℝ} (h : b ≤ b') :
    Hup D E b' ⊆ Hup D E b := by
  rintro g ⟨γ, hγ, hlt⟩
  refine ⟨γ, hγ, lt_of_le_of_lt ?_ hlt⟩
  gcongr

/-! ## `supDistLU` and logarithmic profiles -/

/-- `supDistLU d R F G ≤ u` from the pointwise bound `|F - G| ≤ u` on `B̄_R × B̄_R`. -/
theorem p8b_supDistLU_le_of_abs_le {F G : C(Rd d × Rd d, ℝ)} {R u : ℝ}
    (h : ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R, |F (x, y) - G (x, y)| ≤ u) :
    supDistLU d R F G ≤ ENNReal.ofReal u :=
  endpt_supDistLU_le_iff.2 fun p hp => by
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal (h p.1 hp.1 p.2 hp.2)

/-- `ofReal u < supDistLU d R F G` iff `|F - G| > u` somewhere on `B̄_R × B̄_R`. -/
theorem p8b_lt_supDistLU_iff {F G : C(Rd d × Rd d, ℝ)} {R u : ℝ} (hu : 0 ≤ u) :
    ENNReal.ofReal u < supDistLU d R F G ↔
      ∃ x ∈ closedBall (0 : Rd d) R, ∃ y ∈ closedBall (0 : Rd d) R, u < |F (x, y) - G (x, y)| := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd (p8b_supDistLU_le_of_abs_le hcon) (not_le.2 h)
  · rintro ⟨x, hx, y, hy, hlt⟩
    refine lt_of_lt_of_le ?_ (endpt_edist_le_supDistLU (F := F) (G := G) (mk_mem_prod hx hy))
    rw [edist_dist, Real.dist_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hu hlt)).2 hlt

/-- **The event of `a:prop37`** (`∃ x, y ∈ B̄_R`, `|log(1 + ρ^D(x, y)) − log(1 + ρ^E(x, y))| > δ`) is the
`supDistLU` event of the logarithmic profiles used by `Prop37Shape` (Part C `c:lem-p37`, first sentence). -/
theorem p8b_logEvent_eq (D E : DistRd d → ContMetric d) (R : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    {g | ENNReal.ofReal δ < supDistLU d R (logProfile (rho D g).1) (logProfile (rho E g).1)} =
      {g | ∃ x ∈ closedBall (0 : Rd d) R, ∃ y ∈ closedBall (0 : Rd d) R,
        δ < |Real.log (1 + (rho D g).1 (x, y)) - Real.log (1 + (rho E g).1 (x, y))|} := by
  ext g
  simp only [mem_ofPred_eq, p8b_lt_supDistLU_iff hδ, endpt_logProfile_apply,
    abs_of_nonneg ((rho D g).nonneg _ _), abs_of_nonneg ((rho E g).nonneg _ _)]

/-- The two-sided comparison with coefficient `1 + t` and error `t` bounds the logarithmic profiles by `t`. -/
theorem p8b_abs_log_sub_le {D' E' : ContMetric d} {t R : ℝ} (ht : 0 ≤ t)
    (h₁ : CompOn E' D' (1 + t) t R) (h₂ : CompOn D' E' (1 + t) t R) {x y : Rd d}
    (hx : x ∈ closedBall (0 : Rd d) R) (hy : y ∈ closedBall (0 : Rd d) R) :
    |Real.log (1 + D'.1 (x, y)) - Real.log (1 + E'.1 (x, y))| ≤ t := by
  have hD := D'.nonneg x y
  have hE := E'.nonneg x y
  have hlt : Real.log (1 + t) ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith)
    linarith
  -- `1 + a ≤ (1 + t)(1 + b)` gives `log (1 + a) - log (1 + b) ≤ log (1 + t)`
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ (1 + t) * b + t →
      Real.log (1 + a) - Real.log (1 + b) ≤ t := by
    intro a b ha hb hab
    have h1 : 1 + a ≤ (1 + t) * (1 + b) := by nlinarith
    have h2 : Real.log (1 + a) ≤ Real.log ((1 + t) * (1 + b)) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by linarith) (by linarith)] at h2
    linarith
  have k₁ := key _ _ hD hE (h₂ x hx y hy)
  have k₂ := key _ _ hE hD (h₁ x hx y hy)
  rw [abs_le]
  constructor <;> linarith

/-- The two-sided comparison with coefficient `1 + t` and error `t` bounds `supDistLU` of the profiles by `t`. -/
theorem p8b_supDistLU_logProfile_le_of_compOn {D' E' : ContMetric d} {t R : ℝ} (ht : 0 ≤ t)
    (h₁ : CompOn E' D' (1 + t) t R) (h₂ : CompOn D' E' (1 + t) t R) :
    supDistLU d R (logProfile D'.1) (logProfile E'.1) ≤ ENNReal.ofReal t := by
  refine p8b_supDistLU_le_of_abs_le fun x hx y hy => ?_
  rw [endpt_logProfile_apply, endpt_logProfile_apply, abs_of_nonneg (D'.nonneg x y),
    abs_of_nonneg (E'.nonneg x y)]
  exact p8b_abs_log_sub_le ht h₁ h₂ hx hy

/-- The two-sided comparison with coefficient `1 + w` and error `e`, together with the bound `M` on both metrics on
`B̄_R × B̄_R`, bounds `supDistLU` of the metrics by `w M + e`. -/
theorem p8b_supDistLU_le_of_compOn {D' E' : ContMetric d} {w e M R : ℝ} (hw : 0 ≤ w)
    (h₁ : CompOn E' D' (1 + w) e R) (h₂ : CompOn D' E' (1 + w) e R)
    (hD : ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R, D'.1 (x, y) ≤ M)
    (hE : ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R, E'.1 (x, y) ≤ M) :
    supDistLU d R D'.1 E'.1 ≤ ENNReal.ofReal (w * M + e) := by
  refine p8b_supDistLU_le_of_abs_le fun x hx y hy => ?_
  have a₁ := h₁ x hx y hy
  have a₂ := h₂ x hx y hy
  have b₁ : w * D'.1 (x, y) ≤ w * M := mul_le_mul_of_nonneg_left (hD x hx y hy) hw
  have b₂ : w * E'.1 (x, y) ≤ w * M := mul_le_mul_of_nonneg_left (hE x hx y hy) hw
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The uniform diameter quantile of Proposition 3.6 -/

/-- **The diameter quantile `M_s`** (blueprint `a:prop36`, fixed data; NA1 R11): from (E3) of Lemma 2.1 at the pin
`s` (`U = B_{R+1}`, `K_c = B̄_R`) and Markov's inequality, for every `p > 0` there is `M ≥ 1` with
`𝐏ₛ(∃ x, y ∈ B̄_R, ρ^D(x, y) > M) ≤ p` for all `ξ ∈ (0, ξ̄]` and `D` strong. -/
theorem p8b_diam_quantile (hd : 2 ≤ d) {ξbar s : ℝ} (hs : 0 < s) (hU : UniformEstimates d ξbar s)
    {R p : ℝ} (hR : 0 ≤ R) (hp : 0 < p) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
        pinLaw d s {g | ¬ ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
          (rho D g).1 (x, y) ≤ M} ≤ ENNReal.ofReal p := by
  obtain ⟨pp, hpp, hdiam⟩ := hU.diam
  have hRpos : (0 : ℝ) < R + 1 := by linarith
  obtain ⟨K, hK⟩ := hdiam (ball (0 : Rd d) (R + 1)) (closedBall (0 : Rd d) R) isOpen_ball isBounded_ball
    (isConnected_ball hRpos) (isCompact_closedBall _ _) (closedBall_subset_ball (by linarith))
  set K' : ℝ := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  set M : ℝ := max 1 ((K' / p) ^ pp⁻¹) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMpp : K' / p ≤ M ^ pp := by
    calc K' / p = ((K' / p) ^ pp⁻¹) ^ pp :=
          (Real.rpow_inv_rpow (div_pos (lt_of_lt_of_le one_pos hK'1) hp).le hpp.ne').symm
      _ ≤ M ^ pp := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hpp.le
  have hMpos : 0 < M ^ pp := Real.rpow_pos_of_pos hM0 pp
  refine ⟨M, hM1, fun ξ hξ D hD => ?_⟩
  have hl := p5b_ae_isLength_rho hd hD hs
  have hY : AEMeasurable (fun g => diamIn (rho D g) (ball (0 : Rd d) (R + 1)) (closedBall (0 : Rd d) R))
      (pinLaw d s) :=
    aemeasurable_diamIn_of_ae_length (pinLaw d s) (rho D) (measurable_rho hD.measurable) hl isOpen_ball
      (closedBall_subset_ball (by linarith))
  have hmk := p5b_markov (μ := pinLaw d s)
    (f := fun g => diamIn (rho D g) (ball (0 : Rd d) (R + 1)) (closedBall (0 : Rd d) R) ^ pp)
    (hY.pow_const pp) hMpos (hK ξ hξ D hD)
  have hsub : {g | ¬ ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
      (rho D g).1 (x, y) ≤ M} ⊆
      {g | ENNReal.ofReal (M ^ pp) ≤
        diamIn (rho D g) (ball (0 : Rd d) (R + 1)) (closedBall (0 : Rd d) R) ^ pp} := by
    intro g hg
    simp only [mem_ofPred_eq, not_forall, not_le] at hg
    obtain ⟨x, hx, y, hy, hlt⟩ := hg
    have h1 : ENNReal.ofReal ((rho D g).1 (x, y)) ≤
        diamIn (rho D g) (ball (0 : Rd d) (R + 1)) (closedBall (0 : Rd d) R) :=
      ((rho D g).ofReal_le_internal _ x y).trans (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl))
    have h2 : ENNReal.ofReal M ≤
        diamIn (rho D g) (ball (0 : Rd d) (R + 1)) (closedBall (0 : Rd d) R) :=
      (ENNReal.ofReal_le_ofReal hlt.le).trans h1
    show ENNReal.ofReal (M ^ pp) ≤
      diamIn (rho D g) (ball (0 : Rd d) (R + 1)) (closedBall (0 : Rd d) R) ^ pp
    rw [← ENNReal.ofReal_rpow_of_nonneg hM0.le hpp.le]
    exact ENNReal.rpow_le_rpow h2 hpp.le
  refine (measure_mono hsub).trans (hmk.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [div_le_iff₀ hMpos]
  rw [div_le_iff₀ hp] at hMpp
  have : K ≤ K' := le_max_left _ _
  nlinarith

end HigherDimLQGContinuity
