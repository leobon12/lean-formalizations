import GaussianLQG.Uniform.RSW.Law
import LQGMetric.Papers.DDDF.P18Max
import LQGMetric.Papers.DDDF.P18Ell
import LQGMetric.Papers.DDDF.P5ULarge

/-!
# Leaves of DDDF Proposition 18 with their constants before the probability space

Phase B, packet B-3 (worker PB-U6). Uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`,
§5 (row `subsec:ledger-upper`), Recipe B and Finding `fd:opaque`. Three inputs of the proof of
DDDF20 Prop 18 have constants that do not depend on `ξ` or on the white noise, but are stated
after the noise (or after `ξ`) in `LQGMetric`:

* `prop2_tail_R31_W`: DDDF Prop 2 (2.10) on `R_{3,1}` (template `prop2_tail_R31`,
  `LQGMetric/Papers/DDDF/P18Max.lean`), with the constant of `prop2_tail` chosen before the
  probability space. Recipe B2 (copy): the template's witness is that of `prop2_tail`, which is
  already chosen before `Ω`; the proof is the template's.
* `prop5_X3k_tail_W`: the tail of `X_{3k,k}` uniform in `k` (template `prop5_X3k_tail`,
  `P5ULarge.lean`), by law transfer from a reference white noise (Recipe B1;
  `measure_XAB_shift_eq`, `GaussianLQG/Uniform/RSW/Law.lean`).
* `p18_ell_lower_W` (ledger U6): the a-priori bound `ℓ_n(φ,p) ≥ e^{-ξ(n log 4 + C√n)}` (template
  `dddf_p18_ell_lower`, `P18Ell.lean`), with its `ξ`-free constant
  `C = C₂ log 4 + β + β C₂`, `β = max(0, log(C₂/p)/2) + 1` (`C₂` from `prop2_tail`) chosen before
  the probability space and before `ξ` (Finding `fd:opaque`; Recipe B2, copy).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

/-- **DDDF Prop 2 (2.10) on `R_{3,1}`, constant before the probability space** (template
`prop2_tail_R31`; same proof, with the constant `C` of `prop2_tail`):
`P(α(m + C√m) ≤ max_{R_{3,1}} |φ_{0,m}|) ≤ 3 C 4^m e^{-α² m / log 4}`. -/
theorem prop2_tail_R31_W : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (m : ℕ) (α : ℝ), 0 < α →
    P.real {ω | α * (m + C * Real.sqrt m) ≤ ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω|} ≤
      3 * (C * 4 ^ m * Real.exp (-α ^ 2 * m / Real.log 4)) := by
  obtain ⟨C, hC, h2⟩ := prop2_tail
  refine ⟨C, hC, fun {Ω} _ {P} {W} hW m α hα => ?_⟩
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le m)
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  set Y : Fin 3 → ℂ → Ω → ℝ := fun j x ω => phiMN W P 0 m (x + ((j : ℕ) : ℂ)) ω with hYdef
  have hYc : ∀ j ω, Continuous fun x => Y j x ω := fun j ω =>
    (hφ.cont ω).comp (continuous_id.add continuous_const)
  have hbound : ∀ j : Fin 3, P.real {ω | α * (m + C * Real.sqrt m) ≤
      ⨆ z : ferniqueBox 0 1, |Y j z ω|} ≤ C * 4 ^ m * Real.exp (-α ^ 2 * m / Real.log 4) := by
    intro j
    have hV := isWhiteNoise_isometry hW (motionL2 1 ((j : ℕ) : ℂ))
    refine h2 hV m (Y j) (fun x => ?_) (hYc j) α hα
    have e := hφ.ae_eq (x + ((j : ℕ) : ℂ))
    have e2 := phi_motion W ha ((2 : ℝ)⁻¹ ^ 0) 1 x ((j : ℕ) : ℂ)
    simp only [Circle.coe_one, one_mul] at e2
    rw [e2] at e
    simpa [inv_pow] using e
  have hsub : {ω | α * (m + C * Real.sqrt m) ≤
      ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω|} ⊆
      ⋃ j : Fin 3, {ω | α * (m + C * Real.sqrt m) ≤ ⨆ z : ferniqueBox 0 1, |Y j z ω|} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_iUnion] at hω ⊢
    by_contra hcon
    push Not at hcon
    have hbdd : ∀ j : Fin 3, BddAbove (range fun z : ferniqueBox 0 1 => |Y j z ω|) := by
      intro j
      have := (isCompact_ferniqueBox 0 1).bddAbove_image
        (continuous_abs.comp (hYc j ω)).continuousOn
      rwa [image_eq_range] at this
    have hle : ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω| <
        α * (m + C * Real.sqrt m) := by
      have hM : ∀ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω| ≤
          (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty
            (fun j => ⨆ z : ferniqueBox 0 1, |Y j z ω|) := by
        intro z
        obtain ⟨j, hj⟩ := exists_shift_mem_ferniqueBox z.2
        have h1 : |phiMN W P 0 m z ω| = |Y j ((z : ℂ) - ((j : ℕ) : ℂ)) ω| := by
          simp only [hYdef, sub_add_cancel]
        rw [h1]
        exact (le_ciSup (hbdd j) (⟨_, hj⟩ : ferniqueBox 0 1)).trans
          (Finset.le_sup' (fun j => ⨆ z : ferniqueBox 0 1, |Y j z ω|) (Finset.mem_univ j))
      have hne : Nonempty (rectAB 3 1).toSet :=
        ⟨⟨0, by simp [MarkedRect.toSet, rectAB, Complex.mem_reProdIm]⟩⟩
      refine (ciSup_le hM).trans_lt ?_
      rw [Finset.sup'_lt_iff]
      exact fun j _ => hcon j
    exact absurd hω (not_le.2 hle)
  calc _ ≤ P.real (⋃ j : Fin 3, {ω | α * (m + C * Real.sqrt m) ≤
        ⨆ z : ferniqueBox 0 1, |Y j z ω|}) := measureReal_mono hsub
    _ ≤ ∑ j : Fin 3, P.real {ω | α * (m + C * Real.sqrt m) ≤
        ⨆ z : ferniqueBox 0 1, |Y j z ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin 3, C * 4 ^ m * Real.exp (-α ^ 2 * m / Real.log 4) :=
        Finset.sum_le_sum fun j _ => hbound j
    _ = _ := by simp

/-- **`X_{3k,k}` tail uniform in `k`, constants before the probability space** (template
`prop5_X3k_tail`, by law transfer from a reference white noise, Recipe B1):
`P(X_{3k,k} ≥ A√k) ≤ 4 e^{-ck}` for all `k ≥ 1`. -/
theorem prop5_X3k_tail_W (Q : PsiParams) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ k : ℕ, 1 ≤ k →
      P {ω | ENNReal.ofReal (A * √k) ≤
          XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) (3 * k) k} ≤
        ENNReal.ofReal (4 * Real.exp (-(c * k))) := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  obtain ⟨A, c, hA, hc, h⟩ := prop5_X3k_tail hW₀ Q
  refine ⟨A, c, hA, hc, fun {Ω} _ {P} {W} hW k hk => ?_⟩
  have e := measure_XAB_shift_eq hW hW₀ Q 0 (3 * k) k (S := Ici (ENNReal.ofReal (A * √k)))
    measurableSet_Ici
  simp only [add_zero, mem_Ici] at e
  rw [e]
  exact h k hk

/-- **DDDF Prop 18, Step 4, the a-priori bound, constant before `ξ` and before the probability
space** (ledger U6 `p18_ell_lower_W`; template `dddf_p18_ell_lower`, same proof): for
`p ∈ (0,1)` there is `C`, depending only on `p`, with `ℓ_n(φ, p) ≥ e^{-ξ(n log 4 + C√n)}` for
every white noise, every `ξ > 0` and every `n ≥ 1`. -/
theorem p18_ell_lower_W {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
      IsWhiteNoise P W → ∀ ξ : ℝ, 0 < ξ → ∀ n : ℕ, 1 ≤ n →
        Real.exp (-(ξ * (n * Real.log 4 + C * √n))) ≤
          ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) := by
  obtain ⟨C₂, hC₂, h2⟩ := prop2_tail
  set β : ℝ := max 0 (Real.log (C₂ / p) / 2) + 1
  have hβ : 0 < β := by positivity
  have hβp : C₂ * Real.exp (-(2 * β)) < p := by
    have h1 : Real.log (C₂ / p) < 2 * β := by
      have := le_max_right 0 (Real.log (C₂ / p) / 2); simp only [β]; linarith
    have h2' : Real.exp (-(2 * β)) < Real.exp (-Real.log (C₂ / p)) :=
      Real.exp_lt_exp.2 (by linarith)
    have e : Real.exp (-Real.log (C₂ / p)) = p / C₂ := by
      rw [Real.exp_neg, Real.exp_log (div_pos hC₂ hp0), inv_div]
    rw [e] at h2'
    calc C₂ * Real.exp (-(2 * β)) < C₂ * (p / C₂) := mul_lt_mul_of_pos_left h2' hC₂
      _ = p := by field_simp
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨C₂ * Real.log 4 + β + β * C₂, by positivity, fun {Ω} _ {P} {W} hW ξ hξ n hn => ?_⟩
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 hn'
  have hsn2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  set t : ℝ := √(n : ℝ) with ht_def
  have ht0 : 0 < t := by linarith
  set α : ℝ := Real.log 4 + β / t
  have hα : 0 < α := by positivity
  set M : ℝ := α * (n + C₂ * √n)
  -- the bad event
  set B := {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiMN W P 0 n z ω|}
  have hB := h2 hW n (phiMN W P 0 n) (fun x => by simpa [inv_pow] using hφ.ae_eq x) hφ.cont α hα
  have hBp : P.real B < p := by
    refine lt_of_le_of_lt hB (lt_of_le_of_lt ?_ hβp)
    have e4 : (4 : ℝ) ^ n = Real.exp (n * Real.log 4) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul,
        Real.exp_log (by norm_num)]
    rw [e4, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₂.le
    have hαsq : α ^ 2 * n / Real.log 4 = n * Real.log 4 + 2 * β * t + β ^ 2 / Real.log 4 := by
      rw [← hsn2]
      simp only [α]
      field_simp
      ring
    rw [neg_mul, neg_div, hαsq]
    have : 2 * β ≤ 2 * β * t := le_mul_of_one_le_right (by positivity) hsn
    have : 0 ≤ β ^ 2 / Real.log 4 := by positivity
    linarith
  -- off `B`, the crossing length is at least `e^{-ξ M}`
  have hM : M ≤ n * Real.log 4 + (C₂ * Real.log 4 + β + β * C₂) * t := by
    simp only [M, α]
    have e : (Real.log 4 + β / t) * (n + C₂ * t) =
        n * Real.log 4 + C₂ * Real.log 4 * t + β * t + β * C₂ := by
      rw [← hsn2]; field_simp; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hsn (by positivity : (0 : ℝ) ≤ β * C₂)]
  have hlow : ∀ ω, ω ∉ B → Real.exp (-(ξ * M)) ≤ lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω := by
    intro ω hω
    have hω' : (⨆ z : ferniqueBox 0 1, |phiMN W P 0 n z ω|) < M := not_le.1 hω
    have hb : ∀ x ∈ (rectAB 1 1).toSet, |phiMN W P 0 n x ω| ≤ M := by
      intro x hx
      rw [rectAB_one_toSet] at hx
      exact (le_ciSup (bddAbove_abs_of_compact
        (by rw [← rectAB_one_toSet]; exact MarkedRect.isCompact_toSet _) (hφ.cont ω))
        (⟨x, hx⟩ : ferniqueBox 0 1)).trans hω'.le
    have h := exp_neg_le_lenObs (ξ := ξ) hφ.cont (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) hb
    simpa [abs_of_pos hξ, rectAB, MarkedRect.crossWidth] using h
  -- the quantile
  have hfin : Real.exp (-(ξ * (n * Real.log 4 + (C₂ * Real.log 4 + β + β * C₂) * t))) ≤
      Real.exp (-(ξ * M)) :=
    Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_left hM hξ.le; linarith)
  refine hfin.trans ?_
  by_contra hcon
  push Not at hcon
  have hq := prob_le_ellQ (ξ := ξ) (P := P) hφ.cont hφ.meas (rectAB 1 1)
    (ENNReal.ofReal_pos.2 hp0) (by rw [ENNReal.ofReal_lt_one]; exact hp1)
  have hsub : {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤
      ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)} ⊆ B := by
    intro ω hω
    by_contra hωB
    have := hlow ω hωB
    exact absurd (lt_of_le_of_lt hω hcon) (not_lt.2 this)
  have h3 := hq.trans (measure_mono hsub)
  rw [← ofReal_measureReal (measure_ne_top P B), ENNReal.ofReal_le_ofReal_iff measureReal_nonneg]
    at h3
  linarith

end Uniform
end GaussianLQG
