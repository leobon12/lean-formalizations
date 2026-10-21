import LQGMetric.Field.MarkovWeyl3
import LQGMetric.Field.CircleAvgRate

/-!
# NIC, part 2 (step 8, deterministic part): scaled radial bumps and their `logCov` increments

Packet P-G2; D-P2 step 8 of `planning/handoffs/P-G1.md`, corrected (see below).

The radial mollifier `rbump s` of `LQGMetric.MarkovWeyl2` is **not** a rescaling of `rbump 1`
(its profile `exp(−1/(s² − |y|²))` concentrates at scale `s²` as `s → 0`), so its `logCov`
increments are not bounded uniformly in `s` by a function of `t = |z − w|/s`. We use instead the
**scaled radial bump** `ψ_{s,c}(x) := s⁻² ψ(s⁻¹ (x − c))` with the fixed radial profile
`ψ := rbump 1`:

* `sbump`, `sbumpOn`, `sbumpC`: the bump as a function, as a test function on an open
  `V ⊇ B̄(c, s)`, and on `ℂ`; `∫ ψ_{s,c} = 1` (`integral_sbump`, change of variables
  `integral_scale`);
* `weylFun_eq_sbumpOn`: for a weakly harmonic distribution `T` on `V`,
  `weylFun T c = T ψ_{s,c}` (both are radial of mass one, `MarkovWeyl2.pair_eq_of_radial`);
* `logPot_sbump`: `logPot ψ_{s,c} (x) = −log s + F(s⁻¹ (x − c))` with `F := logPot ψ`;
* `F` is smooth (`F = −logConv ψ`, `MarkovWeyl2.contDiff_logConv`), hence Lipschitz on
  `B̄(0, 2)`, and `F(a) ≥ −log(|a| + 1)` (`neg_log_le_Fp`);
* **`exists_logCov_sbump_le`**: there is `C_var > 0` with, for all `s > 0` and `z, w`,
  `logCov (ψ_{s,z} − ψ_{s,w}) (ψ_{s,z} − ψ_{s,w}) ≤ C_var · min(t, 1 + log(1 + t))`,
  `t = |z − w|/s`. Proof: `logCov g g = ∫ g(x) (F(s⁻¹(x − z)) − F(s⁻¹(x − w))) dx`; for `t ≤ 1`
  the Lipschitz bound gives `≤ 2 L t`; for all `t`, the four terms give `≤ 2E + 2 log(t + 2)`
  with `E := ∫ ψ F`. Newton's theorem is not needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric LQGMetric.MarkovWeyl2 LQGMetric.CircleAvg

/-! ## The scaled radial bump -/

/-- the scaled radial bump `ψ_{s,c}(x) = s⁻² ψ(s⁻¹ (x − c))`, `ψ = rbump 1` -/
def sbump (s : ℝ) (c x : ℂ) : ℝ := (s ^ 2)⁻¹ * rbump 1 (s⁻¹ • (x - c))

lemma contDiff_sbump (s : ℝ) (c : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sbump s c) :=
  contDiff_const.mul ((contDiff_rbump 1).comp ((contDiff_id.sub contDiff_const).const_smul s⁻¹))

/-- the centred profile `y ↦ s⁻² ψ(s⁻¹ y)` is smooth -/
lemma contDiff_scaled (s : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => (s ^ 2)⁻¹ * rbump 1 (s⁻¹ • y)) :=
  contDiff_const.mul ((contDiff_rbump 1).comp (contDiff_id.const_smul s⁻¹))

lemma norm_inv_smul_sub {s : ℝ} (hs : 0 < s) (x c : ℂ) : ‖s⁻¹ • (x - c)‖ = ‖x - c‖ / s := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_eq_div]

lemma sbump_eq_zero {s : ℝ} (hs : 0 < s) {c x : ℂ} (hx : s < ‖x - c‖) : sbump s c x = 0 := by
  rw [sbump, rbump_eq_zero zero_le_one, mul_zero]
  rw [norm_inv_smul_sub hs, lt_div_iff₀ hs, one_mul]
  exact hx

lemma sbump_nonneg (s : ℝ) (c x : ℂ) : 0 ≤ sbump s c x :=
  mul_nonneg (inv_nonneg.2 (sq_nonneg s)) (rbump_nonneg 1 _)

lemma hasCompactSupport_sbump {s : ℝ} (hs : 0 < s) (c : ℂ) : HasCompactSupport (sbump s c) :=
  HasCompactSupport.intro (isCompact_closedBall c s) fun x hx =>
    sbump_eq_zero hs (by simpa [mem_closedBall, dist_eq_norm] using hx)

lemma integrable_sbump {s : ℝ} (hs : 0 < s) (c : ℂ) : Integrable (sbump s c) :=
  (contDiff_sbump s c).continuous.integrable_of_hasCompactSupport (hasCompactSupport_sbump hs c)

/-- change of variables `x = c + s v`: `∫ s⁻² f(s⁻¹ (x − c)) dx = ∫ f` -/
lemma integral_scale {s : ℝ} (hs : 0 < s) (c : ℂ) (f : ℂ → ℝ) :
    ∫ x, (s ^ 2)⁻¹ * f (s⁻¹ • (x - c)) = ∫ v, f v := by
  rw [integral_const_mul]
  have h1 : ∫ x, f (s⁻¹ • (x - c)) = ∫ x, f (s⁻¹ • x) :=
    integral_sub_right_eq_self (fun x => f (s⁻¹ • x)) c
  rw [h1, Measure.integral_comp_smul, Complex.finrank_real_complex, smul_eq_mul, ← mul_assoc]
  have h2 : (s ^ 2)⁻¹ * |((s⁻¹) ^ 2)⁻¹| = 1 := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
    field_simp
  rw [h2, one_mul]

lemma integral_sbump {s : ℝ} (hs : 0 < s) (c : ℂ) : ∫ x, sbump s c x = 1 := by
  simp only [sbump]
  rw [integral_scale hs c (rbump 1), integral_rbump one_pos]

/-- `ψ_{s,c}` as a test function on an open `V ⊇ B̄(c, s)` -/
def sbumpOn {V : Opens ℂ} {s : ℝ} (hs : 0 < s) {c : ℂ} (hV : closedBall c s ⊆ V) : TestOn V :=
  ofBall (contDiff_sbump s c) (fun _ hx => sbump_eq_zero hs hx) hV

@[simp] lemma sbumpOn_apply {V : Opens ℂ} {s : ℝ} (hs : 0 < s) {c : ℂ} (hV : closedBall c s ⊆ V)
    (x : ℂ) : sbumpOn hs hV x = sbump s c x := rfl

/-- `ψ_{s,c}` as a test function on `ℂ` -/
def sbumpC {s : ℝ} (hs : 0 < s) (c : ℂ) : TestC :=
  sbumpOn (V := ⊤) (c := c) hs (fun _ _ => trivial)

@[simp] lemma sbumpC_apply {s : ℝ} (hs : 0 < s) (c x : ℂ) : sbumpC hs c x = sbump s c x := rfl

/-! ## Radial identification -/

/-- the centred profile `y ↦ s⁻² ψ(s⁻¹ y)` is radial -/
lemma isRad_scaled (s : ℝ) : IsRad (fun y : ℂ => (s ^ 2)⁻¹ * rbump 1 (s⁻¹ • y)) := fun a y => by
  simp only
  rw [show s⁻¹ • ((a : ℂ) * y) = (a : ℂ) * (s⁻¹ • y) from (mul_smul_comm _ _ _).symm,
    isRad_rbump 1 a]

/-- **Weakly harmonic distributions at a point**: `weylFun T c = T ψ_{s,c}` -/
theorem weylFun_eq_sbumpOn {V : Opens ℂ} (T : DistOn V)
    (hT : ∀ f : MarkovZB.zsSub (V : Set ℂ), T (MarkovHarm.cmTestOn f) = 0) {c : ℂ} {s : ℝ}
    (hs : 0 < s) (hV : closedBall c s ⊆ V) : weylFun T c = T (sbumpOn hs hV) := by
  rw [weylFun_eq T hT hs hV]
  refine pair_eq_of_radial T hT (contDiff_rbump s) (contDiff_scaled s)
    (isRad_rbump s) (isRad_scaled s) (r := s) (fun y hy => rbump_eq_zero hs.le hy)
    (fun y hy => ?_) ?_ hV (fun _ => rfl) (fun _ => rfl)
  · have := sbump_eq_zero hs (c := 0) (x := y) (by rwa [sub_zero])
    simpa only [sbump, sub_zero] using this
  · rw [integral_rbump hs]
    have := integral_scale hs 0 (rbump 1)
    simp only [sub_zero] at this
    rw [this, integral_rbump one_pos]

/-! ## The log potential of the profile -/

/-- the profile `ψ = rbump 1` as a test function -/
def psiT : TestC :=
  ofBall (V := ⊤) (c := 0) (r := 1) (contDiff_rbump 1)
    (fun x hx => rbump_eq_zero zero_le_one (by simpa using hx)) (fun _ _ => trivial)

lemma integrable_rbump_one : Integrable (rbump 1) := integrable_testC psiT

lemma integrable_log_mul_rbump (a : ℂ) :
    Integrable fun y => -Real.log ‖a - y‖ * rbump 1 y :=
  integrable_log_mul_test psiT a

/-- `F := logPot ψ` -/
def Fp : ℂ → ℝ := logPot (rbump 1)

lemma Fp_apply (a : ℂ) : Fp a = ∫ y, -Real.log ‖a - y‖ * rbump 1 y := rfl

lemma Fp_eq_neg_logConv : Fp = fun a => -logConv (rbump 1) a := by
  funext a
  rw [Fp_apply, logConv_apply', ← integral_neg]
  congr 1
  funext y
  ring

lemma contDiff_Fp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fp := by
  rw [Fp_eq_neg_logConv]
  exact (contDiff_logConv (contDiff_rbump 1) psiT.hasCompactSupport).neg

lemma continuous_Fp : Continuous Fp := contDiff_Fp.continuous

lemma exists_lipschitzOnWith_Fp : ∃ L : NNReal, LipschitzOnWith L Fp (closedBall 0 2) :=
  contDiff_Fp.contDiffOn.exists_lipschitzOnWith (by simp) (convex_closedBall 0 2)
    (isCompact_closedBall 0 2)

/-- `F(a) ≥ −log(|a| + 1)` -/
lemma neg_log_le_Fp (a : ℂ) : -Real.log (‖a‖ + 1) ≤ Fp a := by
  calc -Real.log (‖a‖ + 1) = ∫ y, -Real.log (‖a‖ + 1) * rbump 1 y := by
        rw [integral_const_mul, integral_rbump one_pos, mul_one]
    _ ≤ ∫ y, -Real.log ‖a - y‖ * rbump 1 y := by
        refine integral_mono (integrable_rbump_one.const_mul _) (integrable_log_mul_rbump a)
          fun y => ?_
        by_cases hy : ‖y‖ ≤ 1
        · refine mul_le_mul_of_nonneg_right ?_ (rbump_nonneg 1 y)
          rcases eq_or_lt_of_le (norm_nonneg (a - y)) with h0 | hpos
          · rw [← h0, Real.log_zero, neg_zero, neg_nonpos]
            exact Real.log_nonneg (by linarith [norm_nonneg a])
          · rw [neg_le_neg_iff]
            exact Real.log_le_log hpos (by linarith [norm_sub_le a y])
        · rw [rbump_eq_zero zero_le_one (not_le.1 hy), mul_zero, mul_zero]
    _ = Fp a := rfl

/-- **Scaling of the log potential**: `logPot ψ_{s,c} (x) = −log s + F(s⁻¹ (x − c))` -/
lemma logPot_sbump {s : ℝ} (hs : 0 < s) (c x : ℂ) :
    logPot (sbump s c) x = -Real.log s + Fp (s⁻¹ • (x - c)) := by
  set a : ℂ := s⁻¹ • (x - c) with ha
  have e1 : logPot (sbump s c) x = ∫ v, -Real.log ‖x - c - s • v‖ * rbump 1 v := by
    rw [logPot, ← integral_scale hs c (fun v => -Real.log ‖x - c - s • v‖ * rbump 1 v)]
    congr 1
    funext y
    simp only [sbump]
    rw [smul_inv_smul₀ hs.ne', sub_sub_sub_cancel_right]
    ring
  rw [e1]
  have hae : (fun v => -Real.log ‖x - c - s • v‖ * rbump 1 v) =ᵐ[volume]
      fun v => -Real.log s * rbump 1 v + -Real.log ‖a - v‖ * rbump 1 v := by
    filter_upwards [Measure.ae_ne volume a] with v hv
    have h1 : x - c - s • v = s • (a - v) := by
      rw [smul_sub, ha, smul_inv_smul₀ hs.ne']
    have h2 : ‖a - v‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hv.symm)
    rw [h1, norm_smul, Real.norm_of_nonneg hs.le, Real.log_mul hs.ne' h2]
    ring
  rw [integral_congr_ae hae, integral_add (integrable_rbump_one.const_mul _)
    (integrable_log_mul_rbump a), integral_const_mul, integral_rbump one_pos, mul_one]
  rfl

/-! ## The four terms -/

lemma integrable_sbump_mul_Fp {s : ℝ} (hs : 0 < s) (c c' : ℂ) :
    Integrable fun x => sbump s c x * Fp (s⁻¹ • (x - c')) := by
  have hc : Continuous fun x : ℂ => sbump s c x * Fp (s⁻¹ • (x - c')) :=
    (contDiff_sbump s c).continuous.mul
      (continuous_Fp.comp ((continuous_id.sub continuous_const).const_smul s⁻¹))
  have hk : HasCompactSupport fun x : ℂ => sbump s c x * Fp (s⁻¹ • (x - c')) :=
    (hasCompactSupport_sbump hs c).mul_right
  exact hc.integrable_of_hasCompactSupport hk

/-- `∫ ψ_{s,c} F(s⁻¹ (· − c)) = E := ∫ ψ F` -/
lemma integral_sbump_mul_Fp_self {s : ℝ} (hs : 0 < s) (c : ℂ) :
    ∫ x, sbump s c x * Fp (s⁻¹ • (x - c)) = ∫ v, rbump 1 v * Fp v := by
  rw [← integral_scale hs c (fun v => rbump 1 v * Fp v)]
  congr 1
  funext x
  simp only [sbump]
  ring

/-- `∫ ψ_{s,c} F(s⁻¹ (· − c')) ≥ −log(|c − c'|/s + 2)` -/
lemma neg_log_le_integral_sbump_mul_Fp {s : ℝ} (hs : 0 < s) (c c' : ℂ) :
    -Real.log (‖c - c'‖ / s + 2) ≤ ∫ x, sbump s c x * Fp (s⁻¹ • (x - c')) := by
  calc -Real.log (‖c - c'‖ / s + 2) = ∫ x, sbump s c x * -Real.log (‖c - c'‖ / s + 2) := by
        rw [integral_mul_const, integral_sbump hs, one_mul]
    _ ≤ ∫ x, sbump s c x * Fp (s⁻¹ • (x - c')) := by
        refine integral_mono ((integrable_sbump hs c).mul_const _)
          (integrable_sbump_mul_Fp hs c c') fun x => ?_
        by_cases hx : ‖x - c‖ ≤ s
        · refine mul_le_mul_of_nonneg_left ((neg_le_neg_iff.2 ?_).trans (neg_log_le_Fp _))
            (sbump_nonneg s c x)
          refine Real.log_le_log (by positivity) ?_
          rw [norm_inv_smul_sub hs]
          have h1 : ‖x - c'‖ ≤ ‖x - c‖ + ‖c - c'‖ := norm_sub_le_norm_sub_add_norm_sub x c c'
          have h2 : ‖x - c'‖ / s ≤ 1 + ‖c - c'‖ / s := by
            rw [div_le_iff₀ hs, add_mul, one_mul, div_mul_cancel₀ _ hs.ne']
            linarith
          linarith
        · rw [sbump_eq_zero hs (not_le.1 hx), zero_mul, zero_mul]

/-- the Lipschitz bound: for `|z − w| ≤ s` and `c ∈ {z, w}`,
`|∫ ψ_{s,c} (F(s⁻¹(· − z)) − F(s⁻¹(· − w)))| ≤ L |z − w|/s` -/
lemma abs_integral_sbump_mul_Fp_sub_le {s : ℝ} (hs : 0 < s) {L : NNReal}
    (hL : LipschitzOnWith L Fp (closedBall 0 2)) {z w c : ℂ} (hzw : ‖z - w‖ ≤ s)
    (hc : ‖c - z‖ ≤ ‖z - w‖ ∧ ‖c - w‖ ≤ ‖z - w‖) :
    |∫ x, sbump s c x * (Fp (s⁻¹ • (x - z)) - Fp (s⁻¹ • (x - w)))| ≤ L * (‖z - w‖ / s) := by
  have hint : Integrable fun x => sbump s c x * (Fp (s⁻¹ • (x - z)) - Fp (s⁻¹ • (x - w))) := by
    simp_rw [mul_sub]
    exact (integrable_sbump_mul_Fp hs c z).sub (integrable_sbump_mul_Fp hs c w)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((integrable_sbump hs c).mul_const (L * (‖z - w‖ / s)))
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, Real.norm_of_nonneg (sbump_nonneg s c x)]
    by_cases hx : ‖x - c‖ ≤ s
    · refine mul_le_mul_of_nonneg_left ?_ (sbump_nonneg s c x)
      have hmem : ∀ c'' : ℂ, ‖c - c''‖ ≤ ‖z - w‖ → s⁻¹ • (x - c'') ∈ closedBall (0 : ℂ) 2 := by
        intro c'' hc''
        rw [mem_closedBall, dist_zero_right, norm_inv_smul_sub hs, div_le_iff₀ hs]
        linarith [norm_sub_le_norm_sub_add_norm_sub x c c'']
      have h := hL.dist_le_mul _ (hmem z hc.1) _ (hmem w hc.2)
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_left,
        norm_inv_smul_sub hs, norm_sub_rev w z] at h
      exact h
    · rw [sbump_eq_zero hs (not_le.1 hx), zero_mul, zero_mul]
  · rw [integral_mul_const, integral_sbump hs, one_mul]

/-! ## The `logCov` bound -/

/-- the elementary combination of the two regimes -/
lemma le_cVar_mul_min {t E L V : ℝ} (ht : 0 ≤ t) (h1 : t ≤ 1 → V ≤ 2 * L * t)
    (h2 : V ≤ 2 * E + 2 * Real.log (t + 2)) :
    V ≤ max (2 * L) (4 * |E| + 4) * min t (1 + Real.log (1 + t)) := by
  have hlog1 : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hM : 0 ≤ max (2 * L) (4 * |E| + 4) := le_max_of_le_right (by positivity)
  rcases le_or_gt t 1 with ht1 | ht1
  · have hmin : min t (1 + Real.log (1 + t)) = t := min_eq_left (by linarith)
    rw [hmin]
    exact (h1 ht1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)
  · have hlt : Real.log (1 + t) ≤ t := (Real.log_le_sub_one_of_pos (by linarith)).trans
      (by linarith)
    have hmin : (1 + Real.log (1 + t)) / 2 ≤ min t (1 + Real.log (1 + t)) :=
      le_min (by linarith) (by linarith)
    have hl2 : Real.log (t + 2) ≤ Real.log 2 + Real.log (1 + t) := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
    have hE : E ≤ |E| := le_abs_self E
    have hEl : 0 ≤ |E| * Real.log (1 + t) := mul_nonneg (abs_nonneg E) hlog1
    calc V ≤ 2 * E + 2 * Real.log (t + 2) := h2
      _ ≤ (4 * |E| + 4) * ((1 + Real.log (1 + t)) / 2) := by
        have e : (4 * |E| + 4) * ((1 + Real.log (1 + t)) / 2) =
            2 * |E| + 2 + 2 * Real.log (1 + t) + 2 * (|E| * Real.log (1 + t)) := by ring
        rw [e]
        linarith
      _ ≤ max (2 * L) (4 * |E| + 4) * min t (1 + Real.log (1 + t)) :=
        mul_le_mul (le_max_right _ _) hmin (by positivity) hM

/-- **The new deterministic lemma (D-P2 step 8)**: the `logCov` increments of the scaled radial
bumps are bounded by `C_var · min(t, 1 + log(1 + t))`, `t = |z − w|/s`, uniformly in `s`. -/
theorem exists_logCov_sbump_le : ∃ Cv : ℝ, 0 < Cv ∧ ∀ (s : ℝ) (hs : 0 < s) (z w : ℂ),
    logCov (sbumpC hs z - sbumpC hs w : TestC) (sbumpC hs z - sbumpC hs w : TestC) ≤
      Cv * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s)) := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_Fp
  set E : ℝ := ∫ v, rbump 1 v * Fp v
  refine ⟨max (2 * (L : ℝ)) (4 * |E| + 4), lt_max_of_lt_right (by positivity),
    fun s hs z w => ?_⟩
  set t := ‖z - w‖ / s with htdef
  have ht : 0 ≤ t := by positivity
  set G : TestC := sbumpC hs z - sbumpC hs w
  set Dz : ℂ → ℝ := fun x => Fp (s⁻¹ • (x - z))
  set Dw : ℂ → ℝ := fun x => Fp (s⁻¹ • (x - w))
  -- `logCov G G = ∫ ψ_z (Dz − Dw) − ∫ ψ_w (Dz − Dw)`
  have hpot : ∀ x, logPot G x = Dz x - Dw x := fun x => by
    rw [logPot_sub]
    show logPot (sbump s z) x - logPot (sbump s w) x = _
    rw [logPot_sbump hs, logPot_sbump hs]
    ring
  have hiz : Integrable fun x => sbump s z x * (Dz x - Dw x) := by
    simp_rw [mul_sub]
    exact (integrable_sbump_mul_Fp hs z z).sub (integrable_sbump_mul_Fp hs z w)
  have hiw : Integrable fun x => sbump s w x * (Dz x - Dw x) := by
    simp_rw [mul_sub]
    exact (integrable_sbump_mul_Fp hs w z).sub (integrable_sbump_mul_Fp hs w w)
  have hdec : logCov G G = (∫ x, sbump s z x * (Dz x - Dw x)) -
      ∫ x, sbump s w x * (Dz x - Dw x) := by
    rw [logCov_eq_integral_logPot, ← integral_sub hiz hiw]
    congr 1
    funext x
    rw [hpot x]
    show (sbump s z x - sbump s w x) * _ = _
    ring
  have hzz := integral_sbump_mul_Fp_self hs z
  have hww := integral_sbump_mul_Fp_self hs w
  have hzw := neg_log_le_integral_sbump_mul_Fp hs z w
  have hwz := neg_log_le_integral_sbump_mul_Fp hs w z
  rw [norm_sub_rev w z] at hwz
  have e1 : ∫ x, sbump s z x * (Dz x - Dw x) =
      (∫ x, sbump s z x * Fp (s⁻¹ • (x - z))) - ∫ x, sbump s z x * Fp (s⁻¹ • (x - w)) := by
    rw [← integral_sub (integrable_sbump_mul_Fp hs z z) (integrable_sbump_mul_Fp hs z w)]
    congr 1
    funext x
    ring
  have e2 : ∫ x, sbump s w x * (Dz x - Dw x) =
      (∫ x, sbump s w x * Fp (s⁻¹ • (x - z))) - ∫ x, sbump s w x * Fp (s⁻¹ • (x - w)) := by
    rw [← integral_sub (integrable_sbump_mul_Fp hs w z) (integrable_sbump_mul_Fp hs w w)]
    congr 1
    funext x
    ring
  refine le_cVar_mul_min ht (fun ht1 => ?_) ?_
  · have hzw' : ‖z - w‖ ≤ s := by
      rw [htdef, div_le_iff₀ hs, one_mul] at ht1
      exact ht1
    have b1 := abs_integral_sbump_mul_Fp_sub_le hs hL hzw' (c := z)
      ⟨by simp, le_of_eq rfl⟩
    have b2 := abs_integral_sbump_mul_Fp_sub_le hs hL hzw' (c := w)
      ⟨by rw [norm_sub_rev], by simp⟩
    rw [hdec]
    have := abs_le.1 b1
    have := abs_le.1 b2
    rw [← htdef] at b1 b2
    linarith [(abs_le.1 b1).2, (abs_le.1 b2).1]
  · rw [hdec, e1, e2, hzz, hww]
    rw [← htdef] at hzw hwz
    linarith
