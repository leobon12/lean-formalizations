import QuantumZipper.Proofs.LQG.AreaOffsetsBasic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Area analogue of M4-B4, part 2: the modulus in the offset for interior circles (B4a)

At an interior point `z` with `2ε ≤ Im z`, folded circles are genuine circles and
`d°_{aε}(z) = d°_{2ε}(z) · H(a)` with `H(a) = (a/2)^{γ²/2} e^{γ Φ(a)}`,
`Φ(a) = Z_{aε}(z) − Z_{2ε}(z)` independent of `Z_{2ε}(z)`. This is the boundary computation with
`γ ↦ 2γ` and all variances halved; the dyadic chaining of `AllOffsetsModulus` is reused.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaOffsets

open BdryExist GaussTK TwoRadius TwoRadiusC AreaExist AllOffsets

theorem tilt_moment_bound2 {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    6 * exp x - 4 * exp (3 * x) + exp (6 * x) - 3 ≤ 339776 * x ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ u, u = exp x - 1 := ⟨_, rfl⟩
  have ex : exp x = 1 + u := by linarith
  have hu0 : 0 ≤ u := by linarith [add_one_le_exp x]
  have hexp2 : exp x ≤ 8 := by
    have h1 := Real.exp_one_lt_d9
    have : exp x ≤ exp 1 ^ 2 := by
      rw [← exp_nat_mul]; exact exp_le_exp.2 (by push_cast; linarith)
    nlinarith [exp_pos 1]
  have hux : u ≤ 8 * x := by
    have h := add_one_le_exp (-x)
    have hm : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    have : exp x * (1 - x) ≤ 1 := by
      calc exp x * (1 - x) = exp x * (-x + 1) := by ring
        _ ≤ exp x * exp (-x) := mul_le_mul_of_nonneg_left h (exp_pos _).le
        _ = 1 := hm
    nlinarith
  have hu7 : u ≤ 7 := by linarith
  have e3 : exp (3 * x) = exp x ^ 3 := by rw [← exp_nat_mul]; norm_num
  have e6 : exp (6 * x) = exp x ^ 6 := by rw [← exp_nat_mul]; norm_num
  rw [e3, e6, ex]
  have hpoly : 6 * (1 + u) - 4 * (1 + u) ^ 3 + (1 + u) ^ 6 - 3 =
      u ^ 2 * (3 + 16 * u + 15 * u ^ 2 + 6 * u ^ 3 + u ^ 4) := by ring
  rw [hpoly]
  have p2 := pow_le_pow_left₀ hu0 hu7 2
  have p3 := pow_le_pow_left₀ hu0 hu7 3
  have p4 := pow_le_pow_left₀ hu0 hu7 4
  have hb : 3 + 16 * u + 15 * u ^ 2 + 6 * u ^ 3 + u ^ 4 ≤ 5309 := by
    norm_num at p2 p3 p4; linarith
  have hu2sq : u ^ 2 ≤ 64 * x ^ 2 := by nlinarith
  calc u ^ 2 * (3 + 16 * u + 15 * u ^ 2 + 6 * u ^ 3 + u ^ 4) ≤ u ^ 2 * 5309 :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg u)
    _ ≤ 64 * x ^ 2 * 5309 := by nlinarith
    _ = 339776 * x ^ 2 := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Band increment at an interior point. -/
def bandΦc (X : Ω → FieldSample) (z : ℂ) (ε a : ℝ) (ω : Ω) : ℝ :=
  fcPairVal X (z, a * ε, z, 2 * ε) ω

/-- `H(a) = (a/2)^{γ²/2} e^{γ Φ(a)}`. -/
def bandHc (γ : ℝ) (X : Ω → FieldSample) (z : ℂ) (ε a : ℝ) (ω : Ω) : ℝ :=
  (a / 2) ^ (γ ^ 2 / 2) * exp (γ * bandΦc X z ε a ω)

theorem fcPairCov_nested_zero_int {z : ℂ} {ρ r r2 : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hr2 : r ≤ r2) (hr2z : r2 ≤ z.im) :
    fcPairCov (z, ρ, z, r) (z, r, z, r2) = 0 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hr2' : 0 < r2 := hr.trans_le hr2
  have hrz : r ≤ z.im := hr2.trans hr2z
  have hρz : ρ ≤ z.im := hρr.trans hrz
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_sameCenter hρ hr hρz hrz,
    kernelCov_fc_interior_sameCenter hρ hr2' hρz hr2z,
    kernelCov_fc_interior_sameCenter hr hr hrz hrz,
    kernelCov_fc_interior_sameCenter hr hr2' hrz hr2z]
  simp only [max_eq_right hρr, max_eq_right (hρr.trans hr2), max_eq_right hr2, max_self]
  ring

theorem bandHc_moment [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {z : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : 2 * ε ≤ z.im) {b b' : ℝ}
    (hb'1 : 1 ≤ b') (hbb' : b' ≤ b) (hb2 : b ≤ 2) (hd : b - b' ≤ 1 / 2) :
    Integrable (fun ω => (bandHc γ X z ε b ω - bandHc γ X z ε b' ω) ^ 4) P ∧
    ∫ ω, (bandHc γ X z ε b ω - bandHc γ X z ε b' ω) ^ 4 ∂P ≤
      5436416 * exp 32 * (b - b') ^ 2 := by
  have hb0 : 0 < b' := by linarith
  have hb : 0 < b := by linarith
  have hbε : 0 < b * ε := mul_pos hb hε
  have hb'ε : 0 < b' * ε := mul_pos hb0 hε
  have h2ε : 0 < 2 * ε := by positivity
  have hbε2 : b * ε ≤ 2 * ε := by nlinarith
  have hb'εb : b' * ε ≤ b * ε := by nlinarith
  have hzH : z ∈ Hbar := mem_Hbar_of_le_im h2ε hz
  set Δ : Ω → ℝ := fcPairVal X (z, b' * ε, z, b * ε) with hΔ
  set s : ℝ := log (b / b') with hs
  have hs0 : 0 ≤ s := log_nonneg ((one_le_div hb0).2 hbb')
  have hsle : s ≤ b - b' := by
    have h1 := log_le_sub_one_of_pos (div_pos hb hb0)
    have h2 : b / b' - 1 ≤ b - b' := by
      rw [div_sub_one hb0.ne', div_le_iff₀ hb0]; nlinarith
    rw [hs]; linarith
  have hsplit : ∀ ω, bandΦc X z ε b' ω = bandΦc X z ε b ω + Δ ω := by
    intro ω; simp only [bandΦc, hΔ, fcPairVal]; ring
  have hrp : (b' / 2) ^ (γ ^ 2 / 2) = (b / 2) ^ (γ ^ 2 / 2) * exp (-((2 * γ) ^ 2 / 8 * s)) := by
    rw [show b' / 2 = (b / 2) * (b' / b) by field_simp, mul_rpow (by positivity) (by positivity),
      rpow_def_of_pos (div_pos hb0 hb), hs, log_div hb0.ne' hb.ne', log_div hb.ne' hb0.ne']
    congr 2; ring
  set A : Ω → ℝ := fun ω => ((b / 2) ^ (γ ^ 2 / 2)) ^ 4 * exp (4 * γ * bandΦc X z ε b ω)
    with hA
  set B : Ω → ℝ := fun ω => tiltY (2 * γ) s (Δ ω) ^ 4 with hB
  have hH : (fun ω => (bandHc γ X z ε b ω - bandHc γ X z ε b' ω) ^ 4) = A * B := by
    funext ω
    simp only [Pi.mul_apply, hA, hB, bandHc, hsplit ω, hrp, tiltY]
    have e4 : exp (4 * γ * bandΦc X z ε b ω) = exp (γ * bandΦc X z ε b ω) ^ 4 := by
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    rw [e4, mul_add, exp_add]
    have e5 : exp (-((2 * γ) ^ 2 / 8 * s) + 2 * γ / 2 * Δ ω) =
        exp (-((2 * γ) ^ 2 / 8 * s)) * exp (γ * Δ ω) := by
      rw [← exp_add]; congr 1; ring
    rw [e5]
    ring
  have hLΦ : HasLaw (bandΦc X z ε b) (gaussianReal 0 (log (2 * ε) - log (b * ε)).toNNReal) P := by
    have := hasLaw_fcPairVal hX (p := (z, b * ε, z, 2 * ε)) ⟨hzH, hbε, hzH, h2ε⟩
    rwa [fcPairCov_incr_self_int_gen hbε hbε2 hz] at this
  have hLΔ : HasLaw Δ (gaussianReal 0 s.toNNReal) P := by
    have := hasLaw_fcPairVal hX (p := (z, b' * ε, z, b * ε)) ⟨hzH, hb'ε, hzH, hbε⟩
    rwa [fcPairCov_incr_self_int_gen hb'ε hb'εb (hbε2.trans hz), log_mul hb.ne' hε.ne',
      log_mul hb0.ne' hε.ne', show log b + log ε - (log b' + log ε) = s by
        rw [hs, log_div hb.ne' hb0.ne']; ring] at this
  have hI : IndepFun Δ (bandΦc X z ε b) P := by
    have h := indepFun_fcPair hX
      (fun _ : Unit => (⟨(z, b' * ε, z, b * ε), ⟨hzH, hb'ε, hzH, hbε⟩⟩ :
        {p : FcIdx // p.Good}))
      (fun _ : Unit => (⟨(z, b * ε, z, 2 * ε), ⟨hzH, hbε, hzH, h2ε⟩⟩ :
        {p : FcIdx // p.Good}))
      (fun _ _ => fcPairCov_nested_zero_int hb'ε hb'εb hbε2 hz)
    exact h.comp (measurable_pi_apply ()) (measurable_pi_apply ())
  have hIAB : IndepFun A B P := by
    have hmA : Measurable (fun x : ℝ => ((b / 2) ^ (γ ^ 2 / 2)) ^ 4 * exp (4 * γ * x)) := by
      fun_prop
    have hmB : Measurable (fun d : ℝ => tiltY (2 * γ) s d ^ 4) :=
      (measurable_tiltY (2 * γ) s).pow_const 4
    exact (hI.symm.comp hmA hmB)
  have hiA : Integrable A P := by
    have := hLΦ.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (4 * γ) 0)
    simp only [zero_add] at this
    exact this.const_mul _
  have hmomB := tiltY_pow4_moment (2 * γ) s.toNNReal
  rw [Real.coe_toNNReal _ hs0] at hmomB
  have hiB : Integrable B P := hLΔ.integrable_fun_comp hmomB.1
  have hEA : ∫ ω, A ω ∂P ≤ exp 32 := by
    have h1 : ∫ ω, exp (0 + 4 * γ * bandΦc X z ε b ω) ∂P =
        exp (0 + (log (2 * ε) - log (b * ε)).toNNReal * (4 * γ) ^ 2 / 2) := by
      rw [← integral_exp_mul_add_gaussianReal]
      exact hLΦ.integral_comp (f := fun x => exp (0 + 4 * γ * x)) (by fun_prop)
    simp only [zero_add] at h1
    rw [hA, integral_const_mul, h1]
    have hq1 : ((b / 2) ^ (γ ^ 2 / 2)) ^ 4 ≤ 1 :=
      pow_le_one₀ (by positivity) (rpow_le_one (by positivity) (by linarith) (by positivity))
    have hv : ((log (2 * ε) - log (b * ε)).toNNReal : ℝ) ≤ 1 := by
      rw [log_mul two_ne_zero hε.ne', log_mul hb.ne' hε.ne',
        show log 2 + log ε - (log b + log ε) = log 2 - log b by ring]
      have hl : log 2 ≤ 1 := by
        have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have hlb : 0 ≤ log b := log_nonneg (by linarith)
      have hl0 : 0 ≤ log 2 - log b := by
        have := log_le_log hb hb2; linarith
      rw [Real.coe_toNNReal _ hl0]; linarith
    have hexp : exp ((log (2 * ε) - log (b * ε)).toNNReal * (4 * γ) ^ 2 / 2) ≤ exp 32 := by
      apply exp_le_exp.2
      have : (4 * γ) ^ 2 ≤ 64 := by nlinarith
      have h0 : (0 : ℝ) ≤ ((log (2 * ε) - log (b * ε)).toNNReal : ℝ) := NNReal.coe_nonneg _
      nlinarith
    calc ((b / 2) ^ (γ ^ 2 / 2)) ^ 4 *
          exp ((log (2 * ε) - log (b * ε)).toNNReal * (4 * γ) ^ 2 / 2)
        ≤ 1 * exp 32 := mul_le_mul hq1 hexp (exp_pos _).le zero_le_one
      _ = exp 32 := one_mul _
  have hEB : ∫ ω, B ω ∂P ≤ 5436416 * (b - b') ^ 2 := by
    simp only [hB]
    rw [show (∫ ω, tiltY (2 * γ) s (Δ ω) ^ 4 ∂P) =
        ∫ d, tiltY (2 * γ) s d ^ 4 ∂(gaussianReal 0 s.toNNReal)
      from hLΔ.integral_comp (f := fun d => tiltY (2 * γ) s d ^ 4)
        ((measurable_tiltY (2 * γ) s).pow_const 4).aestronglyMeasurable]
    rw [hmomB.2]
    set x := γ ^ 2 * s with hx
    have hx0 : 0 ≤ x := by positivity
    have hxs : x ≤ 4 * s := by
      rw [hx]; have : γ ^ 2 ≤ 4 := by nlinarith
      nlinarith
    have hx2 : x ≤ 2 := by linarith
    have e2 : 2 * ((2 * γ) ^ 2 / 8 * s) = x := by rw [hx]; ring
    have e6 : 6 * ((2 * γ) ^ 2 / 8 * s) = 3 * x := by rw [hx]; ring
    have e12 : 12 * ((2 * γ) ^ 2 / 8 * s) = 6 * x := by rw [hx]; ring
    rw [e2, e6, e12]
    have := tilt_moment_bound2 hx0 hx2
    have hxb : x ^ 2 ≤ 16 * (b - b') ^ 2 := by nlinarith
    nlinarith
  have hB0 : 0 ≤ ∫ ω, B ω ∂P := integral_nonneg fun ω => by simp only [hB]; positivity
  rw [hH]
  refine ⟨hIAB.integrable_mul hiA hiB, ?_⟩
  rw [hIAB.integral_mul_eq_mul_integral hiA.aestronglyMeasurable hiB.aestronglyMeasurable]
  calc (∫ ω, A ω ∂P) * ∫ ω, B ω ∂P ≤ exp 32 * (5436416 * (b - b') ^ 2) :=
        mul_le_mul hEA hEB hB0 (exp_pos _).le
    _ = 5436416 * exp 32 * (b - b') ^ 2 := by ring

/-- `E chainT m n H ≤ C θ^m` at an interior point. -/
theorem chainT_bandc_moment [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {z : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : 2 * ε ≤ z.im) (m n : ℕ) :
    Integrable (fun ω => chainT m n (fun a => bandHc γ X z ε a ω)) P ∧
    ∫ ω, chainT m n (fun a => bandHc γ X z ε a ω) ∂P ≤
      (8 + 4 * (5436416 * exp 32)) * θm ^ m := by
  set Cm := 5436416 * exp 32 with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  have hpair : ∀ j l : ℕ, l ∈ Finset.range (2 ^ (j + 1) + 1) →
      Integrable (fun ω => (bandHc γ X z ε (dpt (j + 1) l) ω -
        bandHc γ X z ε (dpt j (l / 2)) ω) ^ 4) P ∧
      ∫ ω, (bandHc γ X z ε (dpt (j + 1) l) ω - bandHc γ X z ε (dpt j (l / 2)) ω) ^ 4 ∂P ≤
        Cm * (1 / 2 ^ (j + 1)) ^ 2 := by
    intro j l hl
    have hl' := Finset.mem_range.1 hl
    have hd0 := dpt_diff_nonneg j l
    have hd1 := dpt_diff_le j l
    have h12 : (1 : ℝ) / 2 ^ (j + 1) ≤ 1 / 2 := by
      have : (2 : ℝ) ≤ 2 ^ (j + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact one_div_le_one_div_of_le (by norm_num) this
    obtain ⟨hi, hb⟩ := bandHc_moment hX hγ hγ2 hε hz (b := dpt (j + 1) l)
      (b' := dpt j (l / 2)) (dpt_ge_one j (l / 2)) (by linarith) (dpt_le_two (by omega))
      (by linarith)
    exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0 hd1 2) hCm0)⟩
  have hincr : ∀ j, Integrable (fun ω => incr j (fun a => bandHc γ X z ε a ω)) P ∧
      ∫ ω, incr j (fun a => bandHc γ X z ε a ω) ∂P ≤ Cm / 2 ^ j := by
    intro j
    have hint : Integrable (fun ω => incr j (fun a => bandHc γ X z ε a ω)) P := by
      unfold incr
      exact integrable_finset_sum _ fun l hl => (hpair j l hl).1
    refine ⟨hint, ?_⟩
    unfold incr
    rw [integral_finset_sum _ fun l hl => (hpair j l hl).1]
    refine (Finset.sum_le_sum fun l hl => (hpair j l hl).2).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hy : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    push_cast
    rw [pow_succ, div_pow, one_pow, mul_pow,
      show ((2 : ℝ) ^ j * 2 + 1) * (Cm * (1 / ((2 ^ j) ^ 2 * 2 ^ 2))) =
        Cm * (2 ^ j * 2 + 1) / ((2 ^ j) ^ 2 * 4) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hCm0 (by linarith : (0 : ℝ) ≤ 2 ^ j - 1),
      mul_nonneg (mul_nonneg hCm0 (by linarith : (0 : ℝ) ≤ 2 ^ j - 1))
        (by linarith : (0:ℝ) ≤ 2 ^ j)]
  have hjint : ∀ j, Integrable (fun ω => θm ^ j +
      incr j (fun a => bandHc γ X z ε a ω) / θm ^ (3 * j)) P :=
    fun j => (integrable_const _).add ((hincr j).1.div_const _)
  have hint : Integrable (fun ω => chainT m n (fun a => bandHc γ X z ε a ω)) P := by
    unfold chainT
    exact integrable_finset_sum _ fun j _ => hjint j
  refine ⟨hint, ?_⟩
  unfold chainT
  rw [integral_finset_sum _ fun j _ => hjint j]
  have hterm : ∀ j ∈ Finset.Ico m n, ∫ ω, (θm ^ j +
      incr j (fun a => bandHc γ X z ε a ω) / θm ^ (3 * j)) ∂P ≤
      θm ^ j + Cm * (256 / 343 : ℝ) ^ j := by
    intro j _
    rw [integral_add (integrable_const _) ((hincr j).1.div_const _), integral_const,
      integral_div]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have h := div_le_div_of_nonneg_right (hincr j).2 (pow_pos θm_pos (3 * j)).le
    rw [div_eq_mul_one_div Cm, mul_div_assoc, ratio_eq] at h
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_Ico_geom_le θm_pos.le θm_lt_one m n
  have h2 := sum_Ico_geom_le (q := 256 / 343) (by norm_num) (by norm_num) m n
  have hq : (256 / 343 : ℝ) ^ m ≤ θm ^ m :=
    pow_le_pow_left₀ (by norm_num) (by norm_num [θm]) m
  have hθ0 := pow_nonneg θm_pos.le m
  have h2' : ∑ j ∈ Finset.Ico m n, (256 / 343 : ℝ) ^ j ≤ 4 * θm ^ m := by
    refine h2.trans ?_
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have h1' : ∑ j ∈ Finset.Ico m n, θm ^ j ≤ 8 * θm ^ m := by
    refine h1.trans (le_of_eq ?_)
    rw [show (1 : ℝ) - θm = 1 / 8 by norm_num [θm]]
    ring
  nlinarith [mul_le_mul_of_nonneg_left h2' hCm0]

theorem indepFun_bandc (hX : IsFreeGFFModConstH X P) {z : ℂ} {ε R : ℝ} (hε : 0 < ε)
    (hz : 2 * ε ≤ z.im) (hR : ‖z‖ + 2 * ε ≤ R) :
    IndepFun (fun ω (a : Set.Icc (1 : ℝ) 2) => fcPairVal X (z, a.1 * ε, z, 2 * ε) ω)
      (fun ω (_ : Unit) => fcPairVal X (z, 2 * ε, 0, R) ω) P := by
  have hR0 : 0 < R := by linarith [norm_nonneg z]
  have h2ε : (0 : ℝ) < 2 * ε := by positivity
  have hzH : z ∈ Hbar := mem_Hbar_of_le_im h2ε hz
  refine indepFun_fcPair hX
    (fun a => ⟨_, ⟨hzH, mul_pos (by linarith [a.2.1]) hε, hzH, h2ε⟩⟩)
    (fun _ => ⟨_, good_Z hzH h2ε hR0⟩) ?_
  intro a _
  exact fcPairCov_incr_Zsame_int (mul_pos (by linarith [a.2.1]) hε)
    (mul_le_mul_of_nonneg_right a.2.2 hε.le) hz hR

/-- `H̃(a) = (a/2)^{γ²/2} e^{γ(Z_{aε}(z) − Z_{2ε}(z))}`. -/
def Htc (γ : ℝ) (X : Ω → FieldSample) (R ε : ℝ) (z : ℂ) (a : ℝ) (ω : Ω) : ℝ :=
  (a / 2) ^ (γ ^ 2 / 2) * exp (γ * (zVc X R (a * ε) z ω - zVc X R (2 * ε) z ω))

theorem areaDens_eq_mul_Htc (γ R : ℝ) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) (z : ℂ) (ω : Ω) :
    areaDens γ (zField X R ω) (a * ε) z =
      areaDens γ (zField X R ω) (2 * ε) z * Htc γ X R ε z a ω := by
  have h1 : (a * ε) ^ (γ ^ 2 / 2) = (2 * ε) ^ (γ ^ 2 / 2) * (a / 2) ^ (γ ^ 2 / 2) := by
    rw [← mul_rpow (by positivity) (by positivity)]; congr 1; ring
  rw [areaDens_zField, areaDens_zField, Htc, h1]
  have h2 : exp (γ * zVc X R (a * ε) z ω) = exp (γ * zVc X R (2 * ε) z ω) *
      exp (γ * (zVc X R (a * ε) z ω - zVc X R (2 * ε) z ω)) := by
    rw [← exp_add]; congr 1; ring
  rw [h2]; ring

/-- **Area modulus bound**: `E[d°_{2ε}(z) · chainT m n H̃] ≤ e^{γ² K/2} C θ^m`,
`K = 2 log R − log(2d)`. -/
theorem lintegral_densA_chainT_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R d ε : ℝ} {z : ℂ} (hε : 0 < ε) (h2εd : 2 * ε ≤ d)
    (hd1 : 2 * d ≤ 1) (hdz : d ≤ z.im) (hR : ‖z‖ + 1 ≤ R) (m n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (areaDens γ (zField X R ω) (2 * ε) z *
        chainT m n (fun a => Htc γ X R ε z a ω)) ∂P ≤
      ENNReal.ofReal (exp (γ ^ 2 / 2 * (2 * log R - log (2 * d))) *
        ((8 + 4 * (5436416 * exp 32)) * θm ^ m)) := by
  have h2ε : 0 < 2 * ε := by positivity
  have hd : 0 < d := by linarith
  have hz : 2 * ε ≤ z.im := h2εd.trans hdz
  have hzH : z ∈ Hbar := mem_Hbar_of_le_im h2ε hz
  have hR2 : ‖z‖ + 2 * ε ≤ R := by linarith
  have hR0 : 0 < R := by linarith [norm_nonneg z]
  set V2 : Ω → ℝ := fcPairVal X (z, 2 * ε, 0, R) with hV2
  have hae_pts : ∀ᵐ ω ∂P, ∀ j l : ℕ,
      zVc X R (dpt j l * ε) z ω = fcPairVal X (z, dpt j l * ε, 0, R) ω :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun l =>
      ae_zVc_eq hX R hzH (mul_pos (by linarith [dpt_ge_one j l]) hε)
  have hae2 := ae_zVc_eq hX R hzH h2ε
  set G : Ω → ℝ := fun ω => chainT m n (fun a => bandHc γ X z ε a ω) with hG
  set E0 : Ω → ℝ := fun ω => (2 * ε) ^ (γ ^ 2 / 2) * exp (γ * V2 ω) with hE0
  have hae : ∀ᵐ ω ∂P, areaDens γ (zField X R ω) (2 * ε) z *
      chainT m n (fun a => Htc γ X R ε z a ω) = E0 ω * G ω := by
    filter_upwards [hae_pts, hae2] with ω h1 h2
    rw [areaDens_zField, h2]
    congr 1
    refine chainT_congr m n fun j l _ => ?_
    simp only [Htc, bandHc, bandΦc, h1 j l, h2, fcPairVal]
    congr 2
    ring
  refine (lintegral_congr_ae (hae.mono fun ω h => congrArg ENNReal.ofReal h)).trans_le ?_
  have hI0 := indepFun_bandc (P := P) hX hε hz hR2
  let hfun : (Icc (1 : ℝ) 2 → ℝ) → ℝ → ℝ := fun φ a =>
    if h : a ∈ Icc (1 : ℝ) 2 then (a / 2) ^ (γ ^ 2 / 2) * exp (γ * φ ⟨a, h⟩) else 0
  have hmeas_pt : ∀ a : ℝ, Measurable (fun φ : Icc (1 : ℝ) 2 → ℝ => hfun φ a) := by
    intro a
    by_cases ha : a ∈ Icc (1 : ℝ) 2
    · simp only [hfun, dif_pos ha]
      exact measurable_const.mul (((measurable_pi_apply _).const_mul _).exp)
    · simp only [hfun, dif_neg ha]; exact measurable_const
  have hmG : Measurable (fun φ : Icc (1 : ℝ) 2 → ℝ => chainT m n (hfun φ)) := by
    unfold chainT incr
    exact Finset.measurable_sum _ fun j _ => measurable_const.add
      ((Finset.measurable_sum _ fun l _ =>
        ((hmeas_pt _).sub (hmeas_pt _)).pow_const 4).div_const _)
  have hGeq : G = (fun φ => chainT m n (hfun φ)) ∘
      (fun ω (a : Icc (1 : ℝ) 2) => fcPairVal X (z, a.1 * ε, z, 2 * ε) ω) := by
    funext ω
    simp only [Function.comp, hG]
    refine chainT_congr m n fun j l hl => ?_
    have hmem : dpt j l ∈ Icc (1 : ℝ) 2 := ⟨dpt_ge_one j l, dpt_le_two hl⟩
    simp only [hfun, dif_pos hmem, bandHc, bandΦc]
  have hE0eq : E0 = (fun v : Unit → ℝ => (2 * ε) ^ (γ ^ 2 / 2) * exp (γ * v ())) ∘
      (fun ω (_ : Unit) => V2 ω) := rfl
  have hI : IndepFun E0 G P := by
    rw [hGeq, hE0eq]
    exact (hI0.comp hmG (by fun_prop :
      Measurable (fun v : Unit → ℝ => (2 * ε) ^ (γ ^ 2 / 2) * exp (γ * v ())))).symm
  have hLV : HasLaw V2 (gaussianReal 0 (fcPairCov (z, 2 * ε, 0, R)
      (z, 2 * ε, 0, R)).toNNReal) P :=
    hasLaw_fcPairVal hX (good_Z hzH h2ε hR0)
  have hiE : Integrable E0 P := by
    have := hLV.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ γ 0)
    simp only [zero_add] at this
    exact this.const_mul _
  have hEV : ∫ ω, E0 ω ∂P ≤ exp (γ ^ 2 / 2 * (2 * log R - log (2 * d))) := by
    simp only [hE0]
    rw [integral_const_mul]
    have h1 : ∫ ω, exp (0 + γ * V2 ω) ∂P =
        exp (0 + (fcPairCov (z, 2 * ε, 0, R) (z, 2 * ε, 0, R)).toNNReal * γ ^ 2 / 2) := by
      rw [← integral_exp_mul_add_gaussianReal]
      exact hLV.integral_comp (f := fun x => exp (0 + γ * x)) (by fun_prop)
    simp only [zero_add] at h1
    have hv := var_zVc_le h2ε (by linarith) hz hR2 hd hd1 hdz
      (by linarith [norm_nonneg z])
    rw [h1, rpow_def_of_pos h2ε, ← exp_add]
    apply exp_le_exp.2
    rw [show log (1 / (2 * ε)) = -log (2 * ε) by rw [one_div, log_inv]] at hv
    have hg : 0 ≤ γ ^ 2 := sq_nonneg γ
    nlinarith
  obtain ⟨hiG, hEG⟩ := chainT_bandc_moment hX hγ hγ2 hε hz m n
  have hint : Integrable (fun ω => E0 ω * G ω) P := hI.integrable_mul hiE hiG
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω =>
    mul_nonneg (by simp only [hE0]; positivity) (chainT_nonneg _ _ _))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmul : ∫ ω, E0 ω * G ω ∂P = (∫ ω, E0 ω ∂P) * ∫ ω, G ω ∂P :=
    hI.integral_mul_eq_mul_integral hiE.aestronglyMeasurable hiG.aestronglyMeasurable
  rw [hmul]
  exact mul_le_mul hEV hEG (integral_nonneg fun ω => chainT_nonneg _ _ _) (exp_pos _).le

end AreaOffsets
end QuantumZipper
