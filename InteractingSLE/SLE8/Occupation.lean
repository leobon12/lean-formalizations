import QuantumZipper.Proofs.RS.LocalDynkinSuper
import QuantumZipper.Proofs.Thm11.NonSwallowing
import QuantumZipper.Proofs.ItoLite.OptionalStopping
import QuantumZipper.Proofs.RS.TransienceCanon
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Brownian occupation during a long interval (SLE₈ note, Lemma 3.3)

SLE₈ note `source/sle8-continuity.pdf`, §3.3, p. 7 (transcription `source/sle8/sle8-continuity.md`,
anchors `lem-3.3`, `lem-3.3-proof`).

**Lemma 3.3.** There is a universal `C_tr < ∞` such that for every `r ≥ 2` a Brownian motion `J` of
variance rate `4` satisfies `sup_{|x| ≤ 2r} P_x[∫₀^{2r⁵} 𝟙{|J_u| ≤ 1} du ≤ r] ≤ C_tr / r` (3.19).

Here `J = x + 2B` with `B` a standard real Brownian motion (`IsBrownianReal B P`).
`InteractingSLE.SLE8.exists_measure_occupation_le` is the statement with the constant quantified first;
`InteractingSLE.SLE8.measure_occupation_le` gives the explicit constant `C_tr = 38`.

## Proof (the note's route, with a smooth supersolution)

Let `η` be the exit time of `J` from `(-r², r²)` and `T = 2r⁵`.

* *Exit bound* (3.20), weak form (`measure_forall_abs_lt_le`): if `|J| < r²` on `[0, T]`, then each of
  the `n = ⌈r⌉` independent increments of `B` over the blocks `[k r⁴, (k+1) r⁴] ⊆ [0, T]` is less than
  `r²` in absolute value. Each has law `N(0, r⁴)`, so each such event has probability at most
  `2/√(2π) ≤ 5/6` (density bound), and `P[η > T] ≤ (5/6)^n ≤ 5/r`.
* *Feynman–Kac step* (`measureReal_hit_and_occupation_le`): instead of identifying `E_x[e^{-I/r}]`
  with the `C¹`, piecewise `C²` solution (3.22) of (3.21), we use the smooth supersolution
  `g(y) = 1 + (1 + (y² - 1)/√(1 + y²))/(6r)` of `2g'' ≤ (w/r) g`, where
  `w(j) = min 1 (2 (1 - |j|)⁺) ≤ 𝟙{|j| ≤ 1}` is Lipschitz (`dynkinGen_occF_nonpos`; indeed
  `2g'' = (1 - y²)/(r (1 + y²)^{5/2}) ≤ w/r`). For the state `U = (J, A)`,
  `A_t = ∫₀ᵗ w(J_s)/r ds`, which solves `dU = (0, w(J)/r) dt + (2, 0) dB`, the function
  `F(j, a) = e^{-a} g(j)` has generator `≤ 0`, so QuantumZipper's local Dynkin supermartingale
  inequality (`QuantumZipper.RS.integral_localDynkin_stopped_le`, stopped at `η ∧ T`) gives
  `E F(U_{η ∧ T}) ≤ F(x, 0) = g(x) ≤ 2`. On `{η ≤ T, I_T ≤ r}` one has `A_η ≤ I_T/r ≤ 1` and
  `g(J_η) ≥ r/6`, so `F(U_η) ≥ e^{-1} r/6`; Markov's inequality gives probability `≤ 12e/r`.
* `P[I_T ≤ r] ≤ P[η ≤ T, I_T ≤ r] + P[η > T] ≤ (12e + 5)/r ≤ 38/r`. A good version of `B`
  (`QuantumZipper.RS.exists_good_version0`) transfers the bound to an arbitrary `IsBrownianReal`.

No Itô formula for non-`C²` functions and no identification of `E_x[e^{-I/r}]` is needed: only the
supersolution inequality, which is all the note's argument uses.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace InteractingSLE.SLE8.Occupation

/-- `h(y) = (y² - 1)/√(1 + y²)`. -/
noncomputable def occH (y : ℝ) : ℝ := (y ^ 2 - 1) / √(1 + y ^ 2)
/-- `h'(y) = y (y² + 3)/(1 + y²)^{3/2}`. -/
noncomputable def occH1 (y : ℝ) : ℝ := y * (y ^ 2 + 3) / √(1 + y ^ 2) ^ 3
/-- `h''(y) = 3 (1 - y²)/(1 + y²)^{5/2}`. -/
noncomputable def occH2 (y : ℝ) : ℝ := 3 * (1 - y ^ 2) / √(1 + y ^ 2) ^ 5

theorem sqrt_one_add_sq_pos (y : ℝ) : 0 < √(1 + y ^ 2) := Real.sqrt_pos.2 (by positivity)

theorem sq_sqrt_one_add_sq (y : ℝ) : √(1 + y ^ 2) ^ 2 = 1 + y ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem hasDerivAt_sqrt_one_add_sq (y : ℝ) :
    HasDerivAt (fun y : ℝ => √(1 + y ^ 2)) (y / √(1 + y ^ 2)) y := by
  have h := ((hasDerivAt_pow 2 y).const_add 1).sqrt (by positivity)
  convert h using 1
  field_simp
  ring

theorem hasDerivAt_occH (y : ℝ) : HasDerivAt occH (occH1 y) y := by
  have hs := hasDerivAt_sqrt_one_add_sq y
  have hp := (hasDerivAt_pow 2 y).sub_const 1
  have h : HasDerivAt (fun y : ℝ => (y ^ 2 - 1) / √(1 + y ^ 2)) _ y :=
    hp.div hs (sqrt_one_add_sq_pos y).ne'
  refine h.congr_deriv ?_
  have h0 := sqrt_one_add_sq_pos y
  have h2 := sq_sqrt_one_add_sq y
  simp only [occH1]
  field_simp
  linear_combination (2 * y) * h2

theorem hasDerivAt_occH1 (y : ℝ) : HasDerivAt occH1 (occH2 y) y := by
  have hs := hasDerivAt_sqrt_one_add_sq y
  have hp : HasDerivAt (fun y : ℝ => y * (y ^ 2 + 3)) _ y :=
    (hasDerivAt_id' y).mul ((hasDerivAt_pow 2 y).add_const 3)
  have hs3 : HasDerivAt (fun y : ℝ => √(1 + y ^ 2) ^ 3) _ y := hs.pow 3
  have h0 := sqrt_one_add_sq_pos y
  have h : HasDerivAt (fun y : ℝ => y * (y ^ 2 + 3) / √(1 + y ^ 2) ^ 3) _ y :=
    hp.div hs3 (pow_pos h0 3).ne'
  refine h.congr_deriv ?_
  have h2 := sq_sqrt_one_add_sq y
  simp only [occH2]
  field_simp
  linear_combination (3 * √(1 + y ^ 2) ^ 2 * (y ^ 2 + 1)) * h2

theorem contDiff_occH : ContDiff ℝ 3 occH := by
  have hs : ContDiff ℝ 3 (fun y : ℝ => √(1 + y ^ 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt fun y => by positivity
  exact ((contDiff_id.pow 2).sub contDiff_const).div hs fun y => (sqrt_one_add_sq_pos y).ne'

/-- The Lipschitz weight `w(j) = min 1 (2 (1 - |j|)⁺)`; `0 ≤ w ≤ 𝟙{|j| ≤ 1}`. -/
noncomputable def occW (j : ℝ) : ℝ := min 1 (2 * max 0 (1 - |j|))

theorem occW_nonneg (j : ℝ) : 0 ≤ occW j :=
  le_min zero_le_one (mul_nonneg zero_le_two (le_max_left _ _))

theorem occW_le_one (j : ℝ) : occW j ≤ 1 := min_le_left _ _

theorem occW_eq_zero {j : ℝ} (hj : 1 ≤ |j|) : occW j = 0 := by
  have : max 0 (1 - |j|) = 0 := max_eq_left (by linarith)
  simp [occW, this]

theorem occW_le_indicator (j : ℝ) :
    occW j ≤ {y : ℝ | |y| ≤ 1}.indicator (fun _ => (1 : ℝ)) j := by
  by_cases hj : |j| ≤ 1
  · rw [Set.indicator_of_mem (show j ∈ {y : ℝ | |y| ≤ 1} from hj)]
    exact occW_le_one j
  · rw [Set.indicator_of_notMem (show j ∉ {y : ℝ | |y| ≤ 1} from hj),
      occW_eq_zero (le_of_lt (not_le.1 hj))]

theorem lipschitzWith_occW : LipschitzWith 2 occW := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [Real.dist_eq, NNReal.coe_ofNat, occW]
  have h1 : |min (1 : ℝ) (2 * max 0 (1 - |a|)) - min 1 (2 * max 0 (1 - |b|))|
      ≤ |2 * max 0 (1 - |a|) - 2 * max 0 (1 - |b|)| :=
    (abs_min_sub_min_le_max (1 : ℝ) _ 1 _).trans (max_le (by simp) le_rfl)
  have h2 : |max (0 : ℝ) (1 - |a|) - max 0 (1 - |b|)| ≤ |(1 - |a|) - (1 - |b|)| := by
    rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
  have h3 : |(1 - |a|) - (1 - |b|)| ≤ |a - b| := by
    rw [show (1 - |a|) - (1 - |b|) = -(|a| - |b|) by ring, abs_neg]
    exact abs_abs_sub_abs_le_abs_sub a b
  rw [← mul_sub, abs_mul, abs_two] at h1
  linarith

theorem one_sub_sq_div_le_occW (j : ℝ) : (1 - j ^ 2) / √(1 + j ^ 2) ^ 5 ≤ occW j := by
  have hs : 1 ≤ √(1 + j ^ 2) ^ 5 := one_le_pow₀ (Real.le_sqrt_of_sq_le (by nlinarith))
  by_cases hj : |j| ≤ 1
  · have h1 : 0 ≤ 1 - j ^ 2 := by
      have := sq_abs j; nlinarith [abs_nonneg j]
    refine (div_le_self h1 hs).trans (le_min ?_ ?_)
    · nlinarith
    · have : 1 - j ^ 2 = (1 - |j|) * (1 + |j|) := by rw [← sq_abs j]; ring
      rw [this]
      have ha := abs_nonneg j
      calc (1 - |j|) * (1 + |j|) ≤ (1 - |j|) * 2 := by
            apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        _ ≤ 2 * max 0 (1 - |j|) := by rw [mul_comm]; gcongr; exact le_max_right _ _
  · have h1 : 1 - j ^ 2 ≤ 0 := by
      have := sq_abs j; nlinarith [abs_nonneg j, not_le.1 hj]
    exact (div_nonpos_of_nonpos_of_nonneg h1 (by positivity)).trans (occW_nonneg j)

theorem neg_one_le_occH (y : ℝ) : -1 ≤ occH y := by
  have h0 := sqrt_one_add_sq_pos y
  have h1 : 1 ≤ √(1 + y ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  rw [occH, le_div_iff₀ h0]
  nlinarith

theorem occH_le_abs (y : ℝ) : occH y ≤ |y| := by
  have h0 := sqrt_one_add_sq_pos y
  have h1 : |y| ≤ √(1 + y ^ 2) := Real.abs_le_sqrt (by nlinarith)
  rw [occH, div_le_iff₀ h0]
  have := sq_abs y
  nlinarith [abs_nonneg y]

theorem abs_sub_one_le_occH {y : ℝ} (hy : 1 ≤ |y|) : |y| - 1 ≤ occH y := by
  have h0 := sqrt_one_add_sq_pos y
  have h2 := sq_sqrt_one_add_sq y
  have h1 : √(1 + y ^ 2) ≤ |y| + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    have := sq_abs y
    nlinarith [abs_nonneg y]
  rw [occH, le_div_iff₀ h0]
  have := sq_abs y
  nlinarith [abs_nonneg y]

/-- The supersolution `g_r(y) = 1 + (1 + h(y))/(6r)` of `2 g'' ≤ (w/r) g`. -/
noncomputable def occG (r y : ℝ) : ℝ := 1 + (1 + occH y) / (6 * r)

theorem contDiff_occG (r : ℝ) : ContDiff ℝ 3 (occG r) :=
  contDiff_const.add ((contDiff_const.add contDiff_occH).div_const _)

theorem one_le_occG {r : ℝ} (hr : 0 < r) (y : ℝ) : 1 ≤ occG r y := by
  have := neg_one_le_occH y
  have : 0 ≤ (1 + occH y) / (6 * r) := div_nonneg (by linarith) (by positivity)
  simp only [occG]; linarith

theorem occG_le {r : ℝ} (hr : 0 < r) (y : ℝ) : occG r y ≤ 1 + (1 + |y|) / (6 * r) := by
  have := occH_le_abs y
  simp only [occG]; gcongr

theorem occG_le_two {r : ℝ} (hr : 2 ≤ r) {x : ℝ} (hx : |x| ≤ 2 * r) : occG r x ≤ 2 := by
  refine (occG_le (by linarith) x).trans ?_
  rw [← sub_nonneg]
  have : 2 - (1 + (1 + |x|) / (6 * r)) = (6 * r - 1 - |x|) / (6 * r) := by
    field_simp; ring
  rw [this]
  exact div_nonneg (by linarith) (by linarith)

theorem le_occG {r : ℝ} (hr : 2 ≤ r) {y : ℝ} (hy : r ^ 2 ≤ |y|) : r / 6 ≤ occG r y := by
  have h1 : 1 ≤ |y| := le_trans (by nlinarith) hy
  have h := abs_sub_one_le_occH h1
  have hr0 : 0 < 6 * r := by linarith
  simp only [occG]
  have : r / 6 ≤ (1 + occH y) / (6 * r) := by
    rw [div_le_div_iff₀ (by norm_num) hr0]
    nlinarith
  linarith

theorem hasDerivAt_occG (r y : ℝ) : HasDerivAt (occG r) (occH1 y / (6 * r)) y := by
  have h := ((hasDerivAt_occH y).const_add 1).div_const (6 * r)
  exact h.const_add 1

theorem hasDerivAt_occH1_div (r y : ℝ) :
    HasDerivAt (fun y => occH1 y / (6 * r)) (occH2 y / (6 * r)) y :=
  (hasDerivAt_occH1 y).div_const _

/-- The Feynman–Kac test function `F(j, a) = e^{-a} g_r(j)` on `ℝ × ℝ`. -/
noncomputable def occF (r : ℝ) (p : ℝ × ℝ) : ℝ := Real.exp (-p.2) * occG r p.1

/-- Drift `(0, w(j)/r)` of the state `(J, A)`. -/
noncomputable def occDrift (r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (0, occW p.1 / r)

/-- Noise vector `(2, 0)`: `J = x + 2B` has variance rate `4`. -/
def occNoise : ℝ × ℝ := (2, 0)

theorem contDiff_occF (r : ℝ) : ContDiff ℝ 3 (occF r) :=
  (Real.contDiff_exp.comp contDiff_snd.neg).mul ((contDiff_occG r).comp contDiff_fst)

theorem deriv_line_occDrift (r : ℝ) (p : ℝ × ℝ) :
    deriv (fun s : ℝ => occF r (p + s • occDrift r p)) 0 =
      -(occW p.1 / r) * Real.exp (-p.2) * occG r p.1 := by
  have e1 : (fun s : ℝ => occF r (p + s • occDrift r p)) =
      fun s => Real.exp (-(p.2 + s * (occW p.1 / r))) * occG r p.1 := by
    funext s; simp [occF, occDrift]
  have d1 : HasDerivAt (fun s : ℝ => Real.exp (-(p.2 + s * (occW p.1 / r))) * occG r p.1) _ 0 :=
    ((((hasDerivAt_id' (0 : ℝ)).mul_const (occW p.1 / r)).const_add p.2).neg.exp).mul_const
      (occG r p.1)
  rw [e1, d1.deriv]
  simp only [Pi.neg_apply, zero_mul, add_zero, one_mul]
  ring

theorem deriv_deriv_line_occNoise (r : ℝ) (p : ℝ × ℝ) :
    deriv (deriv (fun s : ℝ => occF r (p + s • occNoise))) 0 =
      Real.exp (-p.2) * (occH2 p.1 / (6 * r) * 2 * 2) := by
  have e2 : (fun s : ℝ => occF r (p + s • occNoise)) =
      fun s => Real.exp (-p.2) * occG r (p.1 + s * 2) := by
    funext s; simp [occF, occNoise]
  have hl : ∀ s : ℝ, HasDerivAt (fun s : ℝ => p.1 + s * 2) 2 s := fun s => by
    simpa using ((hasDerivAt_id' s).mul_const (2 : ℝ)).const_add p.1
  have d1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-p.2) * occG r (p.1 + s * 2))
      (Real.exp (-p.2) * (occH1 (p.1 + s * 2) / (6 * r) * 2)) s := fun s =>
    ((hasDerivAt_occG r (p.1 + s * 2)).comp s (hl s)).const_mul _
  have hd : deriv (fun s : ℝ => Real.exp (-p.2) * occG r (p.1 + s * 2)) =
      fun s => Real.exp (-p.2) * (occH1 (p.1 + s * 2) / (6 * r) * 2) :=
    funext fun s => (d1 s).deriv
  have d2 : HasDerivAt (fun s : ℝ => Real.exp (-p.2) * (occH1 (p.1 + s * 2) / (6 * r) * 2))
      (Real.exp (-p.2) * (occH2 (p.1 + 0 * 2) / (6 * r) * 2 * 2)) 0 :=
    ((((hasDerivAt_occH1_div r (p.1 + 0 * 2)).comp (0 : ℝ) (hl 0)).mul_const 2).const_mul _)
  rw [e2, hd, d2.deriv]
  simp

/-- **Generator inequality.** `L F = e^{-a} ((1 - j²)/(r (1+j²)^{5/2}) - (w(j)/r) g_r(j)) ≤ 0`. -/
theorem dynkinGen_occF_nonpos {r : ℝ} (hr : 0 < r) (p : ℝ × ℝ) :
    QuantumZipper.dynkinGen (occDrift r) occNoise (occF r) p ≤ 0 := by
  have hF := (contDiff_occF r).contDiffAt (x := p)
  unfold QuantumZipper.dynkinGen
  rw [QuantumZipper.FrozenMart.fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num)),
    QuantumZipper.FrozenMart.iteratedFDeriv_two_eq_deriv_deriv_line (hF.of_le (by norm_num)),
    deriv_line_occDrift, deriv_deriv_line_occNoise]
  set E := Real.exp (-p.2) with hE
  set G := occG r p.1
  set W := occW p.1
  set Q := (1 - p.1 ^ 2) / √(1 + p.1 ^ 2) ^ 5 with hQ
  have hE0 : 0 < E := Real.exp_pos _
  have hG : 1 ≤ G := one_le_occG hr _
  have hW : 0 ≤ W := occW_nonneg _
  have hQW : Q ≤ W := one_sub_sq_div_le_occW _
  have h2 : occH2 p.1 = 3 * Q := by rw [occH2, hQ, mul_div_assoc]
  have key : -(W / r) * E * G + 1 / 2 * (E * (occH2 p.1 / (6 * r) * 2 * 2)) =
      E * (Q - W * G) / r := by
    rw [h2]; field_simp; ring
  rw [key]
  refine div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hE0.le ?_) hr.le
  nlinarith

theorem lipschitzWith_occDrift {r : ℝ} (hr : 0 < r) :
    LipschitzWith (Real.toNNReal (2 / r)) (occDrift r) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ (by positivity), Prod.dist_eq]
  simp only [occDrift, dist_self, Real.dist_eq]
  have hw : |occW p.1 - occW q.1| ≤ 2 * |p.1 - q.1| := by
    have := lipschitzWith_occW.dist_le_mul p.1 q.1
    simpa [Real.dist_eq] using this
  have hpq : |p.1 - q.1| ≤ dist p q := by
    rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _
  refine max_le (by positivity) ?_
  rw [← sub_div, abs_div, abs_of_pos hr, div_le_iff₀ hr]
  calc |occW p.1 - occW q.1| ≤ 2 * dist p q := hw.trans (by linarith)
    _ = 2 / r * dist p q * r := by field_simp

theorem norm_occDrift_le {r : ℝ} (hr : 1 ≤ r) (p : ℝ × ℝ) : ‖occDrift r p‖ ≤ 1 := by
  simp only [occDrift, Prod.norm_def, norm_zero, Real.norm_eq_abs]
  refine max_le zero_le_one ?_
  rw [abs_div, abs_of_nonneg (occW_nonneg _), abs_of_pos (by linarith), div_le_one (by linarith)]
  exact (occW_le_one _).trans hr

/-! ### Pathwise facts -/

/-- At the hitting time of a closed set, a continuous path is in the set (if it meets it). -/
theorem hittingBtwn_mem_of_exists {Ω β : Type*} [TopologicalSpace β] {X : ℝ≥0 → Ω → β}
    {S : Set β} (hS : IsClosed S) {ω : Ω} (hc : Continuous (X · ω)) {T : ℝ≥0}
    (hex : ∃ j ∈ Icc 0 T, X j ω ∈ S) : X (hittingBtwn X S 0 T ω) ω ∈ S := by
  classical
  rw [hittingBtwn_def]
  simp only [hex, ↓reduceIte]
  obtain ⟨j, hj, hjS⟩ := hex
  have hcl : IsClosed (Icc 0 T ∩ {i : ℝ≥0 | X i ω ∈ S}) :=
    isClosed_Icc.inter (hS.preimage hc)
  exact (hcl.csInf_mem ⟨j, hj, hjS⟩ ⟨0, fun _ h => h.1.1⟩).2

/-- The indicator `𝟙{|y| ≤ 1}`. -/
noncomputable def unitInd (y : ℝ) : ℝ := {y : ℝ | |y| ≤ 1}.indicator (fun _ => (1 : ℝ)) y

theorem measurable_unitInd : Measurable unitInd :=
  measurable_const.indicator (isClosed_le continuous_abs continuous_const).measurableSet

theorem intervalIntegrable_unitInd_comp {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (fun s => unitInd (f s)) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    (measurable_unitInd.comp hf.measurable).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  simp only [unitInd, Real.norm_eq_abs, norm_one]
  by_cases h : |f s| ≤ 1
  · rw [Set.indicator_of_mem (show f s ∈ {y : ℝ | |y| ≤ 1} from h)]; simp
  · rw [Set.indicator_of_notMem (show f s ∉ {y : ℝ | |y| ≤ 1} from h)]; simp

theorem continuous_occW : Continuous occW := lipschitzWith_occW.continuous

/-- `∫₀ᵗ w(f)/r ≤ (∫₀ᵀ 𝟙{|f| ≤ 1})/r` for `0 ≤ t ≤ T`. -/
theorem integral_occW_div_le {f : ℝ → ℝ} (hf : Continuous f) {r t T : ℝ} (hr : 0 < r)
    (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ s in (0 : ℝ)..t, occW (f s) / r ≤ (∫ s in (0 : ℝ)..T, unitInd (f s)) / r := by
  have hc : Continuous fun s => occW (f s) / r := (continuous_occW.comp hf).div_const r
  have h1 : ∫ s in (0 : ℝ)..t, occW (f s) / r ≤ ∫ s in (0 : ℝ)..T, occW (f s) / r :=
    intervalIntegral.integral_mono_interval le_rfl ht htT
      (ae_of_all _ fun s => div_nonneg (occW_nonneg _) hr.le) (hc.intervalIntegrable _ _)
  have h2 : ∫ s in (0 : ℝ)..T, occW (f s) / r ≤ ∫ s in (0 : ℝ)..T, unitInd (f s) / r :=
    intervalIntegral.integral_mono_on (ht.trans htT) (hc.intervalIntegrable _ _)
      ((intervalIntegrable_unitInd_comp hf 0 T).div_const r)
      fun s _ => div_le_div_of_nonneg_right (occW_le_indicator _) hr.le
  have h3 : ∫ s in (0 : ℝ)..T, unitInd (f s) / r = (∫ s in (0 : ℝ)..T, unitInd (f s)) / r :=
    intervalIntegral.integral_div _ _
  exact h1.trans (h2.trans_eq h3)

/-! ### The state process `(J, A)` -/

section State

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}

/-- The state `(J_t, A_t) = (x + 2 B_t, ∫₀ᵗ w(J_s)/r ds)`. -/
noncomputable def occState (r x : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ × ℝ :=
  (x + 2 * B t ω, ∫ s in (0 : ℝ)..t, occW (x + 2 * B s.toNNReal ω) / r)

theorem continuous_path_toNNReal (hBc : ∀ ω, Continuous (B · ω)) (x : ℝ) (ω : Ω) :
    Continuous fun s : ℝ => x + 2 * B s.toNNReal ω :=
  continuous_const.add (continuous_const.mul ((hBc ω).comp continuous_real_toNNReal))

/-- The state solves `U_t = (x, 0) + ∫₀ᵗ b(U_s) ds + B_t (2, 0)`. -/
theorem occState_integralEq (hBc : ∀ ω, Continuous (B · ω)) (r x : ℝ) (ω : Ω) (t : ℝ≥0) :
    occState r x B t ω = (x, 0) +
      (∫ s in (0 : ℝ)..t, occDrift r (occState r x B s.toNNReal ω)) + B t ω • occNoise := by
  have hc : Continuous fun s : ℝ => occW (x + 2 * B s.toNNReal ω) / r :=
    (continuous_occW.comp (continuous_path_toNNReal hBc x ω)).div_const r
  have hint : (∫ s in (0 : ℝ)..t, occDrift r (occState r x B s.toNNReal ω)) =
      ContinuousLinearMap.inr ℝ ℝ ℝ (∫ s in (0 : ℝ)..t, occW (x + 2 * B s.toNNReal ω) / r) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc.intervalIntegrable _ _)]
    rfl
  rw [hint]
  ext
  · simp [occState, occNoise]; ring
  · simp [occState, occNoise]

end State

/-! ### The Feynman–Kac step -/

/-- The exit set `{r² ≤ |j|}`. -/
def occCl (r : ℝ) : Set (ℝ × ℝ) := {p | r ^ 2 ≤ |p.1|}

/-- The region `{|j| ≤ r², 0 ≤ a}` in which the state stays before exit. -/
def occK (r : ℝ) : Set (ℝ × ℝ) := {p | |p.1| ≤ r ^ 2 ∧ 0 ≤ p.2}

theorem isClosed_occCl (r : ℝ) : IsClosed (occCl r) :=
  isClosed_le continuous_const (continuous_abs.comp continuous_fst)

theorem isClosed_occK (r : ℝ) : IsClosed (occK r) :=
  (isClosed_le (continuous_abs.comp continuous_fst) continuous_const).inter
    (isClosed_le continuous_const continuous_snd)

theorem occF_nonneg {r : ℝ} (hr : 0 < r) (p : ℝ × ℝ) : 0 ≤ occF r p :=
  mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (one_le_occG hr _))

section Hit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Feynman–Kac step of Lemma 3.3.** For a Brownian motion with measurable coordinates and
continuous paths started at `0`, `r ≥ 2` and `|x| ≤ 2r`, the probability that `J = x + 2B` reaches
`±r²` by time `T` while `∫₀ᵀ 𝟙{|J_u| ≤ 1} du ≤ r` is at most `12e/r`. -/
theorem measureReal_hit_and_occupation_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {r : ℝ} (hr : 2 ≤ r) {x : ℝ} (hx : |x| ≤ 2 * r) (T : ℝ≥0) :
    P.real {ω | (∃ t ≤ T, r ^ 2 ≤ |x + 2 * B t ω|) ∧
        ∫ u in (0 : ℝ)..T, unitInd (x + 2 * B u.toNNReal ω) ≤ r} ≤ 12 * Real.exp 1 / r := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hr0 : 0 < r := by linarith
  set U := occState r x B with hU_def
  have hU := occState_integralEq hBc r x (B := B)
  have hb := lipschitzWith_occDrift hr0
  have hbM := norm_occDrift_le (by linarith : (1 : ℝ) ≤ r)
  have hUc : ∀ ω, Continuous (U · ω) :=
    QuantumZipper.Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  set 𝓕 := QuantumZipper.NonSwallow.bmFilt hBm
  have hUad : Adapted 𝓕 U := QuantumZipper.Dynkin.measurable_of_integralEq 𝓕
    (QuantumZipper.NonSwallow.bmFilt_adapted hBm) hBc hb hbM hU hUc
  have hU0 : ∀ ω, U 0 ω = (x, 0) := fun ω => by simp [hU_def, occState, hB0 ω]
  have hK := isClosed_occK r
  have hCl := isClosed_occCl r
  have hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ occCl r) → U t ω ∈ occK r := by
    intro ω t _ ht
    refine ⟨?_, ?_⟩
    · have hsub : Iio t ⊆ (fun s => U s ω) ⁻¹' {p : ℝ × ℝ | |p.1| ≤ r ^ 2} := by
        intro s hs
        have := ht s hs
        simp only [occCl, mem_ofPred_eq, not_le] at this
        exact this.le
      rcases eq_or_ne t 0 with h0 | hne
      · rw [h0, hU0]
        show |x| ≤ r ^ 2
        nlinarith
      have hcl := closure_minimal hsub
        ((isClosed_le (continuous_abs.comp continuous_fst) continuous_const).preimage (hUc ω))
      have hne' : (Iio t).Nonempty := ⟨0, pos_iff_ne_zero.2 hne⟩
      exact hcl (by rw [closure_Iio' hne']; exact mem_Iic.2 le_rfl)
    · exact intervalIntegral.integral_nonneg t.coe_nonneg fun s _ =>
        div_nonneg (occW_nonneg _) hr0.le
  set M := 1 + (1 + r ^ 2) / (6 * r)
  have hFM : ∀ p ∈ occK r, |occF r p| ≤ M := by
    intro p hp
    have hgle := occG_le hr0 p.1
    have he : Real.exp (-p.2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hp.2])
    rw [abs_of_nonneg (occF_nonneg hr0 p)]
    have h1 : occG r p.1 ≤ M := hgle.trans (by
      show 1 + (1 + |p.1|) / (6 * r) ≤ 1 + (1 + r ^ 2) / (6 * r)
      gcongr; exact hp.1)
    calc occF r p = Real.exp (-p.2) * occG r p.1 := rfl
      _ ≤ 1 * occG r p.1 :=
        mul_le_mul_of_nonneg_right he (zero_le_one.trans (one_le_occG hr0 _))
      _ ≤ M := by rw [one_mul]; exact h1
  have hsup := QuantumZipper.RS.integral_localDynkin_stopped_le hB hBc 𝓕
    (QuantumZipper.NonSwallow.bmFilt_adapted hBm) (QuantumZipper.NonSwallow.bmFilt_le_past hBm)
    hb hbM hU isOpen_univ hCl hK (subset_univ _) (contDiff_occF r).contDiffOn
    (fun p _ _ => dynkinGen_occF_nonpos hr0 p) T hUK hFM
  have hFu : occF r (x, 0) ≤ 2 := by
    simp only [occF, neg_zero, Real.exp_zero, one_mul]
    exact occG_le_two hr hx
  set τ := hittingBtwn U (occCl r) 0 T with hτ_def
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hfK : ∀ ω, U (min T (τ ω)) ω ∈ occK r := fun ω => by
    rw [min_eq_right (hτT ω)]
    exact hUK ω _ (hτT ω) fun q hq => notMem_of_lt_hittingBtwn hq zero_le
  have hτst : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) :=
    QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUad hUc hCl T
  have hprog : IsStronglyProgressive 𝓕 U :=
    (hUad.stronglyAdapted).isStronglyProgressive_of_continuous hUc
  have hgm : StronglyMeasurable fun ω => U (min T (τ ω)) ω := by
    have h := hprog.stronglyMeasurable_stoppedProcess hτst T
    have heq : stoppedProcess U (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) T =
        fun ω => U (min T (τ ω)) ω := by
      funext ω
      simp only [stoppedProcess, ← WithTop.coe_min]
      rfl
    rw [heq] at h
    exact h
  have hfsm : StronglyMeasurable fun ω => occF r (U (min T (τ ω)) ω) :=
    ((contDiff_occF r).continuous.measurable.comp hgm.measurable).stronglyMeasurable
  have hfi : Integrable (fun ω => occF r (U (min T (τ ω)) ω)) P :=
    QuantumZipper.ItoLite.integrable_of_bound_abs hfsm fun ω => hFM _ (hfK ω)
  set ε := Real.exp (-1) * (r / 6) with hε_def
  have hε : 0 < ε := by positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (ae_of_all _ fun ω => occF_nonneg hr0 (U (min T (τ ω)) ω)) hfi ε
  have hsub : {ω | (∃ t ≤ T, r ^ 2 ≤ |x + 2 * B t ω|) ∧
      ∫ u in (0 : ℝ)..T, unitInd (x + 2 * B u.toNNReal ω) ≤ r} ⊆
      {ω | ε ≤ occF r (U (min T (τ ω)) ω)} := by
    rintro ω ⟨⟨t, htT, ht⟩, hI⟩
    have hmemt : U t ω ∈ occCl r := ht
    have hmemCl := hittingBtwn_mem_of_exists hCl (hUc ω) ⟨t, ⟨zero_le, htT⟩, hmemt⟩
    show ε ≤ occF r (U (min T (τ ω)) ω)
    rw [min_eq_right (hτT ω)]
    have hA : (U (τ ω) ω).2 ≤ 1 := by
      have h := integral_occW_div_le (continuous_path_toNNReal hBc x ω) hr0 (τ ω).coe_nonneg
        (NNReal.coe_le_coe.2 (hτT ω))
      calc (U (τ ω) ω).2 ≤ (∫ u in (0 : ℝ)..T, unitInd (x + 2 * B u.toNNReal ω)) / r := h
        _ ≤ r / r := by gcongr
        _ = 1 := div_self hr0.ne'
    have hg := le_occG hr hmemCl
    calc ε = Real.exp (-1) * (r / 6) := rfl
      _ ≤ Real.exp (-(U (τ ω) ω).2) * occG r (U (τ ω) ω).1 :=
        mul_le_mul (Real.exp_le_exp.2 (by linarith)) hg (by positivity) (Real.exp_pos _).le
      _ = occF r (U (τ ω) ω) := rfl
  calc _ ≤ P.real {ω | ε ≤ occF r (U (min T (τ ω)) ω)} := measureReal_mono hsub
    _ ≤ 2 / ε := by
        rw [le_div_iff₀ hε, mul_comm]
        linarith
    _ = 12 * Real.exp 1 / r := by
        rw [hε_def, Real.exp_neg]
        field_simp
        ring

end Hit

/-! ### The exit bound (3.20) -/

/-- Small-ball bound: `N(0, c²)((-c, c)) ≤ 5/6`. -/
theorem gaussianReal_Ioo_le {v : ℝ≥0} {c : ℝ} (hc : 0 < c) (hv : (v : ℝ) = c ^ 2) :
    gaussianReal 0 v (Ioo (-c) c) ≤ ENNReal.ofReal (5 / 6) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h, NNReal.coe_zero] at hv; nlinarith
  rw [gaussianReal_apply 0 hv0]
  have hbound : ∀ y, gaussianPDF 0 v y ≤ ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ := by
    intro y
    rw [gaussianPDF]
    apply ENNReal.ofReal_le_ofReal
    rw [gaussianPDFReal]
    have h1 : Real.exp (-(y - 0) ^ 2 / (2 * v)) ≤ 1 := Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity))
    calc (√(2 * Real.pi * v))⁻¹ * Real.exp (-(y - 0) ^ 2 / (2 * v)) ≤ (√(2 * Real.pi * v))⁻¹ * 1 := by gcongr
      _ = (√(2 * Real.pi * v))⁻¹ := mul_one _
  have hs : √(2 * Real.pi * v) = √(2 * Real.pi) * c := by
    rw [Real.sqrt_mul (by positivity), hv, Real.sqrt_sq hc.le]
  have hpi : 12 / 5 ≤ √(2 * Real.pi) := Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_three])
  calc ∫⁻ y in Ioo (-c) c, gaussianPDF 0 v y
      ≤ ∫⁻ _ in Ioo (-c) c, ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ := lintegral_mono fun y => hbound y
    _ = ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ * volume (Ioo (-c) c) := setLIntegral_const _ _
    _ = ENNReal.ofReal ((√(2 * Real.pi * v))⁻¹ * (2 * c)) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring
    _ ≤ ENNReal.ofReal (5 / 6) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hs]
        have h1 : (√(2 * Real.pi) * c)⁻¹ * (2 * c) = 2 / √(2 * Real.pi) := by field_simp
        rw [h1, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith

/-- `(5/6)^n ≤ 5/r` when `r ≤ n`. -/
theorem five_sixths_pow_le {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : r ≤ n) :
    (5 / 6 : ℝ) ^ n ≤ 5 / r := by
  have h := one_add_mul_le_pow (a := (1 / 5 : ℝ)) (by norm_num) n
  have hpos : 0 < (1 + 1 / 5 : ℝ) ^ n := by positivity
  have heq : (5 / 6 : ℝ) ^ n = 1 / (1 + 1 / 5 : ℝ) ^ n := by
    rw [one_div, ← inv_pow]; norm_num
  rw [heq, div_le_div_iff₀ hpos hr]
  nlinarith

section Exit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Exit bound (3.20), in the weak form used here.** The probability that `J = x + 2B` stays in
`(-r², r²)` during `[0, 2r⁵]` is at most `5/r`. -/
theorem measure_forall_abs_lt_le (hB : IsPreBrownianReal B P) {r : ℝ} (hr : 1 ≤ r) (x : ℝ) :
    P {ω | ∀ t ≤ (2 * r ^ 5).toNNReal, |x + 2 * B t ω| < r ^ 2} ≤ ENNReal.ofReal (5 / r) := by
  have hr0 : 0 < r := by linarith
  set n := ⌈r⌉₊ with hn_def
  have hn : r ≤ n := Nat.le_ceil r
  have hn2 : (n : ℝ) ≤ 2 * r := by
    have := Nat.ceil_lt_add_one hr0.le; linarith
  set s : ℝ≥0 := (r ^ 4).toNNReal with hs_def
  have hs : (s : ℝ) = r ^ 4 := Real.coe_toNNReal _ (by positivity)
  set tt : ℕ → ℝ≥0 := fun k => k * s with htt_def
  have htt : Monotone tt := fun a b hab => mul_le_mul_of_nonneg_right (Nat.cast_le.2 hab) zero_le
  have hind := hB.hasIndepIncrements.nat htt
  have hsub : {ω | ∀ t ≤ (2 * r ^ 5).toNNReal, |x + 2 * B t ω| < r ^ 2} ⊆
      ⋂ k ∈ Finset.range n, (fun ω => B (tt (k + 1)) ω - B (tt k) ω) ⁻¹' Ioo (-(r ^ 2)) (r ^ 2) := by
    intro ω hω
    simp only [mem_iInter, mem_preimage, mem_Ioo, Finset.mem_range]
    intro k hk
    have hk1 : tt (k + 1) ≤ (2 * r ^ 5).toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
      simp only [htt_def, NNReal.coe_mul, NNReal.coe_natCast, hs]
      have hk' : ((k + 1 : ℕ) : ℝ) ≤ n := Nat.cast_le.2 hk
      have : ((k + 1 : ℕ) : ℝ) * r ^ 4 ≤ 2 * r * r ^ 4 :=
        mul_le_mul_of_nonneg_right (hk'.trans hn2) (by positivity)
      calc ((k + 1 : ℕ) : ℝ) * r ^ 4 ≤ 2 * r * r ^ 4 := this
        _ = 2 * r ^ 5 := by ring
    have hk0 : tt k ≤ (2 * r ^ 5).toNNReal := (htt (Nat.le_succ k)).trans hk1
    have h1 := abs_lt.1 (hω _ hk1)
    have h0 := abs_lt.1 (hω _ hk0)
    constructor <;> linarith [h1.1, h1.2, h0.1, h0.2]
  have hlaw : ∀ k, P ((fun ω => B (tt (k + 1)) ω - B (tt k) ω) ⁻¹' Ioo (-(r ^ 2)) (r ^ 2)) ≤
      ENNReal.ofReal (5 / 6) := by
    intro k
    have h := hB.hasLaw_sub (tt (k + 1)) (tt k)
    show P ((B (tt (k + 1)) - B (tt k)) ⁻¹' Ioo (-(r ^ 2)) (r ^ 2)) ≤ _
    rw [← Measure.map_apply_of_aemeasurable h.aemeasurable measurableSet_Ioo, h.map_eq]
    refine gaussianReal_Ioo_le (by positivity) ?_
    rw [coe_nndist, Real.dist_eq]
    have e1 : ((tt (k + 1) : ℝ≥0) : ℝ) = ((k : ℝ) + 1) * r ^ 4 := by simp [htt_def, hs]
    have e0 : ((tt k : ℝ≥0) : ℝ) = (k : ℝ) * r ^ 4 := by simp [htt_def, hs]
    show |((tt (k + 1) : ℝ≥0) : ℝ) - ((tt k : ℝ≥0) : ℝ)| = (r ^ 2) ^ 2
    rw [e1, e0, show ((k : ℝ) + 1) * r ^ 4 - k * r ^ 4 = r ^ 4 by ring,
      abs_of_nonneg (by positivity)]
    ring
  calc P {ω | ∀ t ≤ (2 * r ^ 5).toNNReal, |x + 2 * B t ω| < r ^ 2}
      ≤ P (⋂ k ∈ Finset.range n,
          (fun ω => B (tt (k + 1)) ω - B (tt k) ω) ⁻¹' Ioo (-(r ^ 2)) (r ^ 2)) := measure_mono hsub
    _ = ∏ k ∈ Finset.range n,
          P ((fun ω => B (tt (k + 1)) ω - B (tt k) ω) ⁻¹' Ioo (-(r ^ 2)) (r ^ 2)) :=
        hind.measure_inter_preimage_eq_mul _ fun _ _ => measurableSet_Ioo
    _ ≤ ∏ _k ∈ Finset.range n, ENNReal.ofReal (5 / 6) := Finset.prod_le_prod fun k _ => hlaw k
    _ = ENNReal.ofReal ((5 / 6) ^ n) := by
        rw [Finset.prod_const, Finset.card_range, ENNReal.ofReal_pow (by norm_num)]
    _ ≤ ENNReal.ofReal (5 / r) := ENNReal.ofReal_le_ofReal (five_sixths_pow_le hr0 hn)

end Exit

/-! ### Lemma 3.3 -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Lemma 3.3 with the explicit constant `38`, for a version of Brownian motion with measurable
coordinates and continuous paths started at `0`. -/
theorem measure_occupation_le_of_continuous (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {r : ℝ} (hr : 2 ≤ r) {x : ℝ} (hx : |x| ≤ 2 * r) :
    P {ω | ∫ u in (0 : ℝ)..(2 * r ^ 5), unitInd (x + 2 * B u.toNNReal ω) ≤ r} ≤
      ENNReal.ofReal (38 / r) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hr0 : 0 < r := by linarith
  set T : ℝ≥0 := (2 * r ^ 5).toNNReal with hT_def
  have hT : (T : ℝ) = 2 * r ^ 5 := Real.coe_toNNReal _ (by positivity)
  set E := {ω | (∃ t ≤ T, r ^ 2 ≤ |x + 2 * B t ω|) ∧
    ∫ u in (0 : ℝ)..T, unitInd (x + 2 * B u.toNNReal ω) ≤ r} with hE
  set X := {ω | ∀ t ≤ T, |x + 2 * B t ω| < r ^ 2} with hX
  have hsub : {ω | ∫ u in (0 : ℝ)..(2 * r ^ 5), unitInd (x + 2 * B u.toNNReal ω) ≤ r} ⊆ E ∪ X := by
    intro ω hω
    by_cases h : ∃ t ≤ T, r ^ 2 ≤ |x + 2 * B t ω|
    · left; exact ⟨h, by rw [hT]; exact hω⟩
    · right
      intro t ht
      exact lt_of_not_ge fun h' => h ⟨t, ht, h'⟩
  have h1 : P E ≤ ENNReal.ofReal (12 * Real.exp 1 / r) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (measureReal_hit_and_occupation_le hB hBm hBc hB0 hr hx T)
  have h2 : P X ≤ ENNReal.ofReal (5 / r) := measure_forall_abs_lt_le hB (by linarith) x
  have he := Real.exp_one_lt_d9
  calc _ ≤ P (E ∪ X) := measure_mono hsub
    _ ≤ P E + P X := measure_union_le _ _
    _ ≤ ENNReal.ofReal (12 * Real.exp 1 / r) + ENNReal.ofReal (5 / r) := add_le_add h1 h2
    _ = ENNReal.ofReal ((12 * Real.exp 1 + 5) / r) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_div]
    _ ≤ ENNReal.ofReal (38 / r) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by linarith) hr0.le)

end Main

end InteractingSLE.SLE8.Occupation

namespace InteractingSLE.SLE8

open Occupation

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Lemma 3.3 of the SLE₈ note** (occupation during a long interval), explicit constant
`C_tr = 38`. For a standard Brownian motion `B`, `r ≥ 2` and `|x| ≤ 2r`, the Brownian motion
`J = x + 2B` of variance rate `4` started at `x` satisfies
`P[∫₀^{2r⁵} 𝟙{|J_u| ≤ 1} du ≤ r] ≤ 38/r`. -/
theorem measure_occupation_le (hB : IsBrownianReal B P) {r : ℝ} (hr : 2 ≤ r) {x : ℝ}
    (hx : |x| ≤ 2 * r) :
    P {ω | ∫ u in (0 : ℝ)..(2 * r ^ 5),
        {y : ℝ | |y| ≤ 1}.indicator (fun _ => (1 : ℝ)) (x + 2 * B u.toNNReal ω) ≤ r} ≤
      ENNReal.ofReal (38 / r) := by
  obtain ⟨B', hBm, hBc, hB0, hB', hae⟩ := QuantumZipper.RS.exists_good_version0 hB
  refine le_trans (measure_mono_ae ?_)
    (measure_occupation_le_of_continuous hB'.toIsPreBrownianReal hBm hBc hB0 hr hx)
  filter_upwards [hae] with ω hω hmem
  have heq : (fun u : ℝ => unitInd (x + 2 * B' u.toNNReal ω)) =
      fun u => {y : ℝ | |y| ≤ 1}.indicator (fun _ => (1 : ℝ)) (x + 2 * B u.toNNReal ω) :=
    funext fun u => by rw [hω]; rfl
  show ∫ u in (0 : ℝ)..(2 * r ^ 5), unitInd (x + 2 * B' u.toNNReal ω) ≤ r
  rw [heq]
  exact hmem

/-- **Lemma 3.3 of the SLE₈ note** (`source/sle8-continuity.pdf`, p. 7, (3.19)). There is a
universal constant `C_tr < ∞` such that, for every `r ≥ 2`, a Brownian motion `J = x + 2B` of
variance rate `4` started at any `x` with `|x| ≤ 2r` satisfies
`P_x[∫₀^{2r⁵} 𝟙{|J_u| ≤ 1} du ≤ r] ≤ C_tr / r`. -/
theorem exists_measure_occupation_le : ∃ C : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}, IsBrownianReal B P → ∀ r : ℝ, 2 ≤ r → ∀ x : ℝ,
      |x| ≤ 2 * r →
        P {ω | ∫ u in (0 : ℝ)..(2 * r ^ 5),
            {y : ℝ | |y| ≤ 1}.indicator (fun _ => (1 : ℝ)) (x + 2 * B u.toNNReal ω) ≤ r} ≤
          ENNReal.ofReal (C / r) :=
  ⟨38, fun hB _ hr _ hx => measure_occupation_le hB hr hx⟩

end InteractingSLE.SLE8
