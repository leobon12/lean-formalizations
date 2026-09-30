import QuantumZipper.Proofs.Thm11.NonSwallowingClock
import QuantumZipper.Statements.CouplingFields

/-!
# DF-2 (real points), DF-3 (clock integrability) and integrability of `ρ·𝔥_T`

Blueprint `THM11_BLUEPRINT.md` §4 FD-5, §5 DF-2/DF-3, §6 MF-6 (domination).

1. **Real points.** For `κ ∈ (0,4]` and real `x ≠ 0`, a.s. the real forward flow from `x`
   survives on `[0,T]`. We run a *tamed real flow* `U = x + ∫ 2/(σ max(σU, ρ)) + B·(−√κ)`
   (`σ = sign x`) and apply the stopped Dynkin identity to a cutoff of
   `Φ(z) = −log Re z + ε (Re z)²`, whose generator is `(κ−4)/(2 (Re z)²) + ε(κ+4)`.
   Hence a.s. all barriers `±(n+1)` survive (the form used by `norm_fwdMap_le_of_barriers`).
2. **DF-3, limit `ρ, c → 0`.** `E[S_T(a); a ∉ K_T, |f_s(a)| < R on [0,T]] ≤ C_R(a)` (Fatou).
3. **Integrability.** A.s. `∫_{ℍ∖K_T} φ S_T < ∞` for bounded `φ` supported in a compact subset
   of `ℍ` (`κ < 4`), and a.s. `ρ·hTfwd` is integrable (`κ ≤ 4`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace QuantumZipper
namespace ClockInt

open FwdClock Thm11Lyap FwdHolo NonSwallow

variable {W : ℝ → ℝ}

/-! ### 1. The tamed real flow -/

/-- The clamped real field `σ·2/max(σ Re z, ρ)`, as a (real) complex number. -/
def realField (σ ρ : ℝ) (z : ℂ) : ℂ := ((σ * (2 / max (σ * z.re) ρ) : ℝ) : ℂ)

theorem abs_sigma {σ : ℝ} (hσ : σ * σ = 1) : |σ| = 1 := by
  have h := abs_mul_abs_self σ
  rw [hσ] at h
  nlinarith [abs_nonneg σ]

theorem realField_lipschitz {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) :
    LipschitzWith (Real.toNNReal (2 / ρ ^ 2)) (realField σ ρ) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  set m1 := max (σ * z.re) ρ with hm1
  set m2 := max (σ * w.re) ρ with hm2
  have h1 : ρ ≤ m1 := le_max_right _ _
  have h2 : ρ ≤ m2 := le_max_right _ _
  have hm1p : 0 < m1 := hρ.trans_le h1
  have hm2p : 0 < m2 := hρ.trans_le h2
  have hmm : |m1 - m2| ≤ ‖z - w‖ := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_sigma hσ, one_mul]
    have := Complex.abs_re_le_norm (z - w)
    simpa using this
  simp only [realField]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul,
    abs_sigma hσ, one_mul, div_sub_div _ _ hm1p.ne' hm2p.ne', abs_div,
    abs_of_pos (mul_pos hm1p hm2p)]
  have hnum : |2 * m2 - m1 * 2| = 2 * |m1 - m2| := by
    rw [show 2 * m2 - m1 * 2 = -(2 * (m1 - m2)) by ring, abs_neg, abs_mul, abs_two]
  rw [hnum, div_le_iff₀ (mul_pos hm1p hm2p)]
  have hρ2 : ρ ^ 2 ≤ m1 * m2 := by nlinarith
  have hnn : 0 ≤ ‖z - w‖ := norm_nonneg _
  calc 2 * |m1 - m2| ≤ 2 * ‖z - w‖ := by linarith
    _ = 2 / ρ ^ 2 * ‖z - w‖ * ρ ^ 2 := by field_simp
    _ ≤ 2 / ρ ^ 2 * ‖z - w‖ * (m1 * m2) := by gcongr

theorem norm_realField_le {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) (z : ℂ) :
    ‖realField σ ρ z‖ ≤ 2 / ρ := by
  simp only [realField]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_sigma hσ, one_mul]
  have h1 : ρ ≤ max (σ * z.re) ρ := le_max_right _ _
  rw [abs_of_pos (div_pos two_pos (hρ.trans_le h1))]
  exact div_le_div_of_nonneg_left (by norm_num) hρ h1

theorem realField_of_le {σ ρ : ℝ} (hσ : σ * σ = 1) {z : ℂ} (h : ρ ≤ σ * z.re) :
    realField σ ρ z = ((2 / z.re : ℝ) : ℂ) := by
  simp only [realField, max_eq_left h]
  congr 1
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  rw [mul_div_assoc', show σ * 2 = σ * 2 * 1 by ring]
  by_cases hr : z.re = 0
  · simp [hr]
  field_simp

theorem lipschitz_realField_shift {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) (c : ℂ) :
    LipschitzWith (Real.toNNReal (2 / ρ ^ 2)) (fun v => realField σ ρ (v - c)) :=
  LipschitzWith.of_dist_le_mul fun v u => by
    have := (realField_lipschitz hσ hρ).dist_le_mul (v - c) (u - c)
    rwa [dist_sub_right] at this

/-- Global existence for the (uncentered) tamed real field on `[0,T]`. -/
theorem exists_realUnc_sol (hW : Continuous W) {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) {T : ℝ}
    (hT : 0 ≤ T) (w : ℂ) :
    ∃ v : ℝ → ℂ, v 0 = w ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (realField σ ρ (v t - W t)) (Icc 0 T) t := by
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  set t0 : Icc (0 : ℝ) T := ⟨0, h0mem⟩ with ht0_def
  have ht0_coe : (t0 : ℝ) = 0 := rfl
  have hf : IsPicardLindelof (fun t v => realField σ ρ (v - W t)) t0 w
      (Real.toNNReal (2 / ρ * T)) 0 (Real.toNNReal (2 / ρ)) (Real.toNNReal (2 / ρ ^ 2)) := by
    refine ⟨fun t _ => (lipschitz_realField_shift hσ hρ _).lipschitzOnWith,
      fun x _ => ?_, ?_, ?_⟩
    · exact ((realField_lipschitz hσ hρ).continuous.comp
        (continuous_const.sub (Complex.continuous_ofReal.comp hW))).continuousOn
    · intro t _ x _
      rw [Real.coe_toNNReal _ (by positivity)]
      exact norm_realField_le hσ hρ _
    · simp only [ht0_coe, sub_zero, NNReal.coe_zero, max_eq_left hT,
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 / ρ),
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 / ρ * T), le_refl]
  have hx : w ∈ Metric.closedBall w ((0 : ℝ≥0) : ℝ) := Metric.mem_closedBall_self (le_refl _)
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_⟩
  · show α.compProj (t0 : ℝ) = w
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
      w ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

open Classical in
/-- The un-centered tamed real flow (junk `0` unless `W` is continuous, `σ² = 1`, `ρ > 0`). -/
def realUnc (W : ℝ → ℝ) (σ ρ : ℝ) (x : ℂ) (t : ℝ) : ℂ :=
  if h : Continuous W ∧ σ * σ = 1 ∧ 0 < ρ then
    Classical.choose (exists_realUnc_sol h.1 h.2.1 h.2.2 (le_max_right t 0) x) t else 0

/-- The centered tamed real flow. -/
def realZ (W : ℝ → ℝ) (σ ρ : ℝ) (x : ℂ) (t : ℝ) : ℂ := realUnc W σ ρ x t - W t

theorem realUnc_eq_of_sol (hW : Continuous W) {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) {T : ℝ}
    {V : ℝ → ℂ} {x : ℂ} (hV0 : V 0 = x)
    (hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (realField σ ρ (V t - W t)) (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, realUnc W σ ρ x t = V t := by
  intro t ht
  rw [realUnc, dif_pos ⟨hW, hσ, hρ⟩]
  obtain ⟨hv0, hvd⟩ := Classical.choose_spec (exists_realUnc_sol hW hσ hρ (le_max_right t 0) x)
  set v := Classical.choose (exists_realUnc_sol hW hσ hρ (le_max_right t 0) x) with hvdef
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 (max t 0) := Icc_subset_Icc_right (le_max_left _ _)
  have hsubT : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have key := ODE_solution_unique (v := fun s v => realField σ ρ (v - (W s : ℂ)))
    (fun s => lipschitz_realField_shift hσ hρ _) (f := v) (g := V) (a := 0) (b := t)
    (fun s hs => (hvd s (hsub hs)).continuousWithinAt.mono hsub)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc ((hvd s (hsub (Ico_subset_Icc_self hs))).mono hsub)
      hs)
    (fun s hs => (hV s (hsubT hs)).continuousWithinAt.mono hsubT)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc ((hV s (hsubT (Ico_subset_Icc_self hs))).mono hsubT)
      hs)
    (by rw [hv0, hV0])
  exact key ⟨ht.1, le_rfl⟩

theorem realUnc_zero (hW : Continuous W) {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) (x : ℂ) :
    realUnc W σ ρ x 0 = x := by
  rw [realUnc, dif_pos ⟨hW, hσ, hρ⟩]
  exact (Classical.choose_spec (exists_realUnc_sol hW hσ hρ (le_max_right 0 0) x)).1

theorem realUnc_hasDerivWithinAt (hW : Continuous W) {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ)
    {T : ℝ} (hT : 0 ≤ T) (x : ℂ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (realUnc W σ ρ x) (realField σ ρ (realZ W σ ρ x t)) (Icc 0 T) t := by
  obtain ⟨v, hv0, hvd⟩ := exists_realUnc_sol hW hσ hρ hT x
  have heq := realUnc_eq_of_sol hW hσ hρ hv0 hvd
  intro t ht
  have e : realZ W σ ρ x t = v t - W t := by rw [realZ, heq t ht]
  rw [e]
  exact (hvd t ht).congr_of_mem heq ht

theorem continuousOn_realZ (hW : Continuous W) {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) {T : ℝ}
    (hT : 0 ≤ T) (x : ℂ) : ContinuousOn (realZ W σ ρ x) (Icc 0 T) :=
  have h : ContinuousOn (realUnc W σ ρ x) (Icc 0 T) := fun t ht =>
    (realUnc_hasDerivWithinAt hW hσ hρ hT x t ht).continuousWithinAt
  h.sub (Complex.continuous_ofReal.comp hW).continuousOn

/-- Integral equation of the tamed real flow. -/
theorem realZ_eq (hW : Continuous W) {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) (x : ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    realZ W σ ρ x t = x - W t + ∫ s in (0 : ℝ)..t, realField σ ρ (realZ W σ ρ x s) := by
  have hcont : ContinuousOn (realUnc W σ ρ x) (Icc 0 t) := fun s hs =>
    (realUnc_hasDerivWithinAt hW hσ hρ ht x s hs).continuousWithinAt
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivAt (realUnc W σ ρ x) (realField σ ρ (realZ W σ ρ x s)) s := fun s hs =>
    (realUnc_hasDerivWithinAt hW hσ hρ ht x s (Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  have hint : IntervalIntegrable (fun s => realField σ ρ (realZ W σ ρ x s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact (realField_lipschitz hσ hρ).continuous.comp_continuousOn
      (continuousOn_realZ hW hσ hρ ht x)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
  rw [realUnc_zero hW hσ hρ] at key
  show realUnc W σ ρ x t - W t = _
  rw [key]; ring

/-- The tamed real flow from a real point stays real. -/
theorem im_realZ (hW : Continuous W) {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) (x : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : (realZ W σ ρ x t).im = 0 := by
  rw [realZ_eq hW hσ hρ x ht]
  have e : (∫ s in (0 : ℝ)..t, realField σ ρ (realZ W σ ρ x s))
      = ((∫ s in (0 : ℝ)..t, σ * (2 / max (σ * (realZ W σ ρ x s).re) ρ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; rfl
  rw [e]
  simp

/-- A tamed real flow staying in `{σ Re ≥ ρ}` is a forward solution from `x`. -/
theorem isForwardSol_realZ (hW : Continuous W) {σ ρ : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) {T : ℝ}
    (hT : 0 ≤ T) {x : ℝ} (hreg : ∀ t ∈ Icc (0 : ℝ) T, ρ ≤ σ * (realZ W σ ρ x t).re) :
    IsForwardSol W (x : ℂ) T (realZ W σ ρ x) := by
  have hreal : ∀ t ∈ Icc (0 : ℝ) T, realZ W σ ρ x t = (((realZ W σ ρ x t).re : ℝ) : ℂ) :=
    fun t ht => Complex.ext (by simp) (by simp [im_realZ hW hσ hρ x ht.1])
  have hre0 : ∀ t ∈ Icc (0 : ℝ) T, (realZ W σ ρ x t).re ≠ 0 := by
    intro t ht h
    have := hreg t ht
    rw [h, mul_zero] at this
    linarith
  have hfield : ∀ t ∈ Icc (0 : ℝ) T, realField σ ρ (realZ W σ ρ x t) = 2 / realZ W σ ρ x t := by
    intro t ht
    rw [realField_of_le hσ (hreg t ht)]
    nth_rw 2 [hreal t ht]
    push_cast; rfl
  refine ⟨continuousOn_realZ hW hσ hρ hT x, fun t ht => ⟨?_, ?_⟩⟩
  · intro h
    exact hre0 t ht (by rw [h, Complex.zero_re])
  · rw [realZ_eq hW hσ hρ x ht.1]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hfield s ⟨hs.1, hs.2.trans ht.2⟩

/-! ### 2. The Lyapunov function `−log Re z + ε (Re z)²` -/

/-- `Φ(z) = −log Re z + ε (Re z)²` (`Real.log` is even, so this is `−log|Re z| + ε(Re z)²`). -/
def realLyap (ε : ℝ) (z : ℂ) : ℝ := -Real.log z.re + ε * z.re ^ 2

theorem contDiffAt_realLyap (ε : ℝ) {z : ℂ} (hz : z.re ≠ 0) {n : ℕ∞} :
    ContDiffAt ℝ n (realLyap ε) z := by
  have hre : ContDiffAt ℝ n (fun z : ℂ => z.re) z := Complex.reCLM.contDiff.contDiffAt
  exact ((Real.contDiffAt_log.2 hz).comp z hre).neg.add (contDiffAt_const.mul (hre.pow 2))

theorem hasFDerivAt_realLyap (ε : ℝ) {z : ℂ} (hz : z.re ≠ 0) :
    HasFDerivAt (realLyap ε) ((-(z.re)⁻¹ + ε * (2 * z.re)) • Complex.reCLM) z := by
  have hre : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  have h1 := (Real.hasDerivAt_log hz).comp_hasFDerivAt z hre
  have h2 := (hre.pow 2).const_mul ε
  refine (h1.neg.add h2).congr_fderiv ?_
  ext w
  simp [smul_eq_mul]
  ring

theorem fderiv_realLyap_apply (ε : ℝ) {z : ℂ} (hz : z.re ≠ 0) (w : ℂ) :
    fderiv ℝ (realLyap ε) z w = (-(z.re)⁻¹ + ε * (2 * z.re)) * w.re := by
  rw [(hasFDerivAt_realLyap ε hz).fderiv]
  simp [smul_eq_mul]

/-- **Generator of `Φ`** where the clamp is inactive:
`LΦ = (κ−4)/(2 (Re z)²) + ε(κ+4)`. -/
theorem dynkinGen_realLyap {κ ε σ ρ : ℝ} (hκ : 0 ≤ κ) (hσ : σ * σ = 1) (hρ : 0 < ρ) {z : ℂ}
    (hz : ρ ≤ σ * z.re) :
    dynkinGen (realField σ ρ) (-((Real.sqrt κ : ℝ) : ℂ)) (realLyap ε) z
      = (κ - 4) / (2 * z.re ^ 2) + ε * (κ + 4) := by
  have hz0 : z.re ≠ 0 := by
    intro h; rw [h, mul_zero] at hz; linarith
  set e : ℂ := -((Real.sqrt κ : ℝ) : ℂ) with he
  set r : ℝ := z.re with hr
  set a : ℝ := e.re with ha
  have hae : a = -Real.sqrt κ := by simp [ha, he]
  set q : ℝ → ℝ := fun s => r + s * a with hq
  have hqd : HasDerivAt q a 0 := by
    simpa [hq] using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add r
  have hq0 : q 0 = r := by simp [hq]
  have hinv := hqd.inv (by rw [hq0]; exact hz0)
  have hφ := ((hinv.neg.add ((hqd.const_mul 2).const_mul ε)).mul_const a)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), fderiv ℝ (realLyap ε) (z + ((s : ℝ) : ℂ) * e) e =
      (fun s => (-(q s)⁻¹ + ε * (2 * q s)) * a) s := by
    have hcont : ContinuousAt q 0 := hqd.continuousAt
    have hmem : {y : ℝ | y ≠ 0} ∈ 𝓝 (q 0) := isOpen_ne.mem_nhds (by rw [hq0]; exact hz0)
    filter_upwards [hcont.preimage_mem_nhds hmem] with s hs
    have hre : (z + ((s : ℝ) : ℂ) * e).re = q s := by simp [hq, hr, ha]
    rw [fderiv_realLyap_apply ε (by rw [hre]; exact hs), hre]
  have hC2 : ContDiffAt ℝ 2 (realLyap ε) z := contDiffAt_realLyap ε hz0
  unfold dynkinGen
  rw [realField_of_le hσ hz, fderiv_realLyap_apply ε hz0,
    iteratedFDeriv_two_eq_of_line hC2 e hev hφ]
  simp only [hq0, Complex.ofReal_re]
  rw [hae, ← hr]
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 2 = κ := ⟨_, Real.sqrt_nonneg κ, Real.sq_sqrt hκ⟩
  rw [Real.sqrt_sq hs]
  field_simp
  ring

/-! ### 3. Regions and the smooth cutoff -/

/-- `{a ≤ σ Re z ≤ b, |Im z| ≤ c}`. -/
def rReg (σ a b c : ℝ) : Set ℂ := {z | a ≤ σ * z.re ∧ σ * z.re ≤ b ∧ |z.im| ≤ c}

/-- `{a < σ Re z < b, |Im z| < c}`. -/
def rOpen (σ a b c : ℝ) : Set ℂ := {z | a < σ * z.re ∧ σ * z.re < b ∧ |z.im| < c}

theorem isClosed_rReg (σ a b c : ℝ) : IsClosed (rReg σ a b c) := by
  have hr : Continuous fun z : ℂ => σ * z.re := continuous_const.mul Complex.continuous_re
  exact (isClosed_le continuous_const hr).inter ((isClosed_le hr continuous_const).inter
    (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))

theorem isOpen_rOpen (σ a b c : ℝ) : IsOpen (rOpen σ a b c) := by
  have hr : Continuous fun z : ℂ => σ * z.re := continuous_const.mul Complex.continuous_re
  exact (isOpen_lt continuous_const hr).inter ((isOpen_lt hr continuous_const).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))

theorem isCompact_rReg {σ : ℝ} (hσ : σ * σ = 1) (a b c : ℝ) : IsCompact (rReg σ a b c) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_rReg σ a b c) ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨|a| + |b| + |c|, fun z hz => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |z.re| ≤ |a| + |b| := by
    have : |σ * z.re| ≤ |a| + |b| := abs_le.2 ⟨by
      linarith [neg_abs_le a, abs_nonneg b, hz.1], by linarith [le_abs_self b, abs_nonneg a, hz.2.1]⟩
    rwa [abs_mul, abs_sigma hσ, one_mul] at this
  have him : |z.im| ≤ |c| := hz.2.2.trans (le_abs_self c)
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

theorem rReg_subset_rOpen {σ a b c a' b' c' : ℝ} (h1 : a' < a) (h2 : b < b') (h3 : c < c') :
    rReg σ a b c ⊆ rOpen σ a' b' c' := fun _ hz =>
  ⟨h1.trans_le hz.1, hz.2.1.trans_lt h2, hz.2.2.trans_lt h3⟩

theorem rOpen_subset_rReg {σ a b c : ℝ} : rOpen σ a b c ⊆ rReg σ a b c := fun _ hz =>
  ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

/-- A `C³` function with bounded derivatives agreeing with `Φ` near the real segment
`{ρ ≤ σ Re z ≤ R, Im z = 0}`. -/
theorem exists_realLyap_cutoff (ε : ℝ) {σ ρ R : ℝ} (hσ : σ * σ = 1) (hρ : 0 < ρ) (hR : 0 < R) :
    ∃ F : ℂ → ℝ, ∃ C : ℝ, ContDiff ℝ 3 F ∧
      (∀ x, |F x| ≤ C ∧ ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 F x‖ ≤ C) ∧
      ∀ z ∈ rReg σ ρ R 0, F =ᶠ[𝓝 z] realLyap ε := by
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      (isOpen_rOpen σ (ρ / 4) (4 * R) 1) (isClosed_rReg σ (ρ / 2) (2 * R) (1 / 2))
      (rReg_subset_rOpen (by linarith) (by linarith) (by norm_num))
  have hts : tsupport χ ⊆ rReg σ (ρ / 4) (4 * R) 1 := by
    rw [tsupport, hχs]; exact closure_minimal rOpen_subset_rReg (isClosed_rReg _ _ _ _)
  have hχc : HasCompactSupport χ :=
    (isCompact_rReg hσ _ _ _).of_isClosed_subset (isClosed_tsupport χ) hts
  set F : ℂ → ℝ := χ * realLyap ε with hFdef
  have hFs : ContDiff ℝ 3 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x.re ≠ 0
    · exact (hχ.contDiffAt.of_le three_le_smooth).mul (contDiffAt_realLyap ε hx)
    · push Not at hx
      have hxt : x ∉ tsupport χ := fun h => by
        have := (hts h).1; rw [hx, mul_zero] at this; linarith
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hxt
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (h0.mono fun y hy => by simp [hFdef, hy])
  have hFc : HasCompactSupport F := hχc.mul_right
  obtain ⟨C0, h0⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  obtain ⟨C1, h1⟩ := (hFs.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hFc.fderiv (𝕜 := ℝ))
  obtain ⟨C2, h2⟩ := (hFs.continuous_iteratedFDeriv (m := 2) (by norm_num)).bounded_above_of_compact_support
    (hFc.iteratedFDeriv 2)
  obtain ⟨C3, h3⟩ := (hFs.continuous_iteratedFDeriv (m := 3) le_rfl).bounded_above_of_compact_support
    (hFc.iteratedFDeriv 3)
  refine ⟨F, max (max C0 C1) (max C2 C3), hFs, fun x => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← Real.norm_eq_abs]
    exact (h0 x).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h1 x).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (h2 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 x).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro z hz
    have hmem : rOpen σ (ρ / 2) (2 * R) (1 / 2) ∈ 𝓝 z :=
      (isOpen_rOpen _ _ _ _).mem_nhds
        (rReg_subset_rOpen (by linarith) (by linarith) (by norm_num) hz)
    filter_upwards [hmem] with y hy
    have : χ y = 1 := (hχ1 y).1 (rOpen_subset_rReg hy)
    simp [hFdef, this]

/-! ### 4. The exit estimate for real points -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Exit set of the real region `{ρ < σ Re z < R}`. -/
def rExit (σ ρ R : ℝ) : Set ℂ := {z | σ * z.re ≤ ρ} ∪ {z | R ≤ σ * z.re}

theorem isClosed_rExit (σ ρ R : ℝ) : IsClosed (rExit σ ρ R) := by
  have hr : Continuous fun z : ℂ => σ * z.re := continuous_const.mul Complex.continuous_re
  exact (isClosed_le hr continuous_const).union (isClosed_le continuous_const hr)

theorem realZ_integralEq (hBc : ∀ ω, Continuous fun t => B t ω) {σ ρ : ℝ} (hσ : σ * σ = 1)
    (hρ : 0 < ρ) (κ : ℝ) (x : ℂ) (ω : Ω) (t : ℝ≥0) :
    realZ (drive κ B ω) σ ρ x t = x
      + (∫ r in (0 : ℝ)..t, realField σ ρ (realZ (drive κ B ω) σ ρ x (r.toNNReal : ℝ)))
      + B t ω • (-((Real.sqrt κ : ℝ) : ℂ)) := by
  rw [realZ_eq (continuous_drive_ns hBc κ ω) hσ hρ x t.coe_nonneg]
  have hint : ∫ s in (0 : ℝ)..t, realField σ ρ (realZ (drive κ B ω) σ ρ x s)
      = ∫ r in (0 : ℝ)..t, realField σ ρ (realZ (drive κ B ω) σ ρ x (r.toNNReal : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [Real.coe_toNNReal r hr.1]
  rw [hint]
  simp only [drive, Real.toNNReal_coe, Complex.real_smul]
  push_cast
  ring

theorem log_sigma_mul {σ : ℝ} (hσ : σ * σ = 1) (r : ℝ) : Real.log (σ * r) = Real.log r := by
  rw [← Real.log_abs, abs_mul, abs_sigma hσ, one_mul, Real.log_abs]

/-- **DF-2, real points: exit estimate.** For the tamed real flow started at `x` with
`ρ < σx < R`, `P(exit of {ρ < σ Re < R} before T) ≤ (Φ(x) + Tε(κ+4) + log R)/m`,
`m = min(log R − log ρ, εR²)`. -/
theorem prob_real_exit_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {σ : ℝ} (hσ : σ * σ = 1) {x ρ R ε : ℝ} (T : ℝ≥0) (hρ : 0 < ρ) (hρR : ρ < R) (hε : 0 < ε)
    (hx : ρ < σ * x) (hxR : σ * x < R) :
    P {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, realZ (drive κ B ω) σ ρ (x : ℂ) s ∈ rExit σ ρ R}
      ≤ ENNReal.ofReal ((realLyap ε (x : ℂ) + T * (ε * (κ + 4)) + Real.log R)
        / min (Real.log R - Real.log ρ) (ε * R ^ 2)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hR : 0 < R := hρ.trans hρR
  set e : ℂ := -((Real.sqrt κ : ℝ) : ℂ) with he
  set 𝓕 := bmFilt hBm with h𝓕
  set U : ℝ≥0 → Ω → ℂ := fun t ω => realZ (drive κ B ω) σ ρ (x : ℂ) t with hUdef
  have hU : ∀ ω (t : ℝ≥0),
      U t ω = (x : ℂ) + (∫ r in (0 : ℝ)..t, realField σ ρ (U r.toNNReal ω)) + B t ω • e :=
    fun ω t => realZ_integralEq hBc hσ hρ κ x ω t
  have hbM : ∀ z, ‖realField σ ρ z‖ ≤ 2 / ρ := norm_realField_le hσ hρ
  have hb := realField_lipschitz hσ hρ
  have hUc : ∀ ω, Continuous (U · ω) :=
    Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  have hUm : ∀ t, Measurable[𝓕 t] (U t) :=
    Dynkin.measurable_of_integralEq 𝓕 (bmFilt_adapted hBm) hBc hb hbM hU hUc
  have hUim : ∀ ω (t : ℝ≥0), (U t ω).im = 0 := fun ω t =>
    im_realZ (continuous_drive_ns hBc κ ω) hσ hρ x t.coe_nonneg
  obtain ⟨F, C, hF, hFC, hFV⟩ := exists_realLyap_cutoff ε hσ hρ hR
  set E := rExit σ ρ R with hE
  set τ : Ω → ℝ≥0 := hittingBtwn U E 0 T with hτdef
  have hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUm hUc (isClosed_rExit σ ρ R) T
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hB0 := hB.eval_zero_ae_eq_zero
  have hU0' : ∀ ω, B 0 ω = 0 → U 0 ω = x := by
    intro ω hω; rw [hU ω 0]; simp [hω]
  have hU0 : ∀ᵐ ω ∂P, U 0 ω = x := by
    filter_upwards [hB0] with ω hω using hU0' ω hω
  obtain ⟨hint, hzero⟩ := dynkin_stopped hB hBc 𝓕 (bmFilt_adapted hBm) (bmFilt_le_past hBm)
    hb hbM hU hF (fun z => (hFC z).2) (fun z => (hFC z).1) hU0 hτ T hτT
  have hxK : (x : ℂ) ∈ rReg σ ρ R 0 :=
    ⟨by simp only [Complex.ofReal_re]; linarith, by simp only [Complex.ofReal_re]; linarith,
      by simp⟩
  -- the path stays in the closed region up to `τ`
  have hK : ∀ ω, B 0 ω = 0 → ∀ t ≤ τ ω, U t ω ∈ rReg σ ρ R 0 := by
    intro ω hω
    refine mem_of_le_of_forall_lt (isClosed_rReg σ ρ R 0) (hUc ω) ?_ ?_
    · rw [hU0' ω hω]; exact hxK
    · intro t ht
      have hnot : U t ω ∉ E := notMem_of_lt_hittingBtwn ht zero_le
      simp only [hE, rExit, mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
      exact ⟨hnot.1.le, hnot.2.le, by rw [hUim ω t, abs_zero]⟩
  -- the generator bound along the stopped path
  have hGint : ∀ ω, B 0 ω = 0 →
      ∫ r in (0 : ℝ)..(τ ω), dynkinGen (realField σ ρ) e F (U r.toNNReal ω)
        ≤ T * (ε * (κ + 4)) := by
    intro ω hω
    have hGc : Continuous fun r : ℝ => dynkinGen (realField σ ρ) e F (U r.toNNReal ω) :=
      (Dynkin.continuous_dynkinGen hF hb.continuous e).comp ((hUc ω).comp continuous_real_toNNReal)
    have hmono := intervalIntegral.integral_mono_on (NNReal.coe_nonneg (τ ω))
      (hGc.intervalIntegrable (μ := volume) _ _)
      (continuous_const.intervalIntegrable (μ := volume) (u := fun _ => ε * (κ + 4)) _ _)
      (fun r hr => by
        have hle : r.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.2 hr.2
        have hmem := hK ω hω _ hle
        rw [dynkinGen_congr (hFV _ hmem), dynkinGen_realLyap hκ.le hσ hρ hmem.1]
        have : (κ - 4) / (2 * (U r.toNNReal ω).re ^ 2) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    have hτT' : ((τ ω : ℝ≥0) : ℝ) ≤ T := by exact_mod_cast hτT ω
    have hpos : 0 ≤ ε * (κ + 4) := by positivity
    nlinarith
  -- measurability of `F(U_τ)`
  have hτm : Measurable τ := by
    refine measurable_of_Iic fun y => ?_
    have h := 𝓕.le y _ (hτ y)
    have e : τ ⁻¹' Iic y = {ω | ((τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (y : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_preimage, mem_Iic]; exact WithTop.coe_le_coe.symm
    rw [e]; exact h
  have hUj : Measurable (Function.uncurry U) :=
    measurable_uncurry_of_continuous_of_measurable hUc fun t => (hUm t).mono (𝓕.le t) le_rfl
  have hFUm : Measurable fun ω => F (U (τ ω) ω) :=
    hF.continuous.measurable.comp (hUj.comp (hτm.prodMk measurable_id))
  have hFUi : Integrable (fun ω => F (U (τ ω) ω)) P :=
    ItoLite.integrable_of_bound_abs hFUm.stronglyMeasurable fun ω => (hFC _).1
  have hFa : F x = realLyap ε x := (hFV x hxK).eq_of_nhds
  have hEF : ∫ ω, F (U (τ ω) ω) ∂P ≤ F x + T * (ε * (κ + 4)) := by
    have hle : ∀ᵐ ω ∂P, F (U (τ ω) ω) ≤ (F (U (τ ω) ω) - F x
        - ∫ r in (0 : ℝ)..(τ ω), dynkinGen (realField σ ρ) e F (U r.toNNReal ω))
        + (F x + T * (ε * (κ + 4))) := by
      filter_upwards [hB0] with ω hω
      have := hGint ω hω
      linarith
    have h1 : ∫ ω, F (U (τ ω) ω) ∂P ≤ ∫ ω, ((F (U (τ ω) ω) - F x
        - ∫ r in (0 : ℝ)..(τ ω), dynkinGen (realField σ ρ) e F (U r.toNNReal ω))
        + (F x + T * (ε * (κ + 4)))) ∂P :=
      integral_mono_ae hFUi (hint.add (integrable_const (F x + T * (ε * (κ + 4))))) hle
    rw [integral_add hint (integrable_const _), hzero, integral_const] at h1
    simpa using h1
  -- the nonnegative variable `Y`
  set Y : Ω → ℝ := fun ω => F (U (τ ω) ω) + Real.log R with hYdef
  have hFUV : ∀ ω, B 0 ω = 0 → F (U (τ ω) ω) = realLyap ε (U (τ ω) ω) := fun ω hω =>
    (hFV _ (hK ω hω _ le_rfl)).eq_of_nhds
  have hlogU : ∀ ω, B 0 ω = 0 →
      Real.log (U (τ ω) ω).re = Real.log (σ * (U (τ ω) ω).re) := fun ω _ =>
    (log_sigma_mul hσ _).symm
  have hYnn : 0 ≤ᵐ[P] Y := by
    filter_upwards [hB0] with ω hω
    have hmem := hK ω hω _ le_rfl
    have hlog : Real.log (σ * (U (τ ω) ω).re) ≤ Real.log R :=
      Real.log_le_log (hρ.trans_le hmem.1) hmem.2.1
    have : 0 ≤ ε * (U (τ ω) ω).re ^ 2 := by positivity
    show 0 ≤ F (U (τ ω) ω) + Real.log R
    rw [hFUV ω hω, realLyap, hlogU ω hω]
    linarith
  have hYi : Integrable Y P := hFUi.add (integrable_const _)
  set m : ℝ := min (Real.log R - Real.log ρ) (ε * R ^ 2) with hm
  have hm0 : 0 < m := lt_min (by linarith [Real.log_lt_log hρ hρR]) (by positivity)
  have hEY : ∫ ω, Y ω ∂P ≤ realLyap ε x + T * (ε * (κ + 4)) + Real.log R := by
    have : ∫ ω, Y ω ∂P = ∫ ω, F (U (τ ω) ω) ∂P + Real.log R := by
      simp only [hYdef]
      rw [integral_add hFUi (integrable_const _)]
      simp
    rw [this, ← hFa]; linarith
  have hMarkov := mul_meas_ge_le_integral_of_nonneg hYnn hYi m
  -- the event inclusion
  have hsub : {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, realZ (drive κ B ω) σ ρ (x : ℂ) s ∈ E}
      ⊆ {ω | m ≤ Y ω} := by
    rintro ω ⟨hB0ω, s, hs, hsE⟩
    have hsE' : U s.toNNReal ω ∈ E := by
      simp only [hUdef, Real.coe_toNNReal s hs.1]; exact hsE
    have hτE : U (τ ω) ω ∈ E := hittingBtwn_mem_of_isClosed (isClosed_rExit σ ρ R) (hUc ω)
      ⟨s.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩, hsE'⟩
    have hmem := hK ω hB0ω _ le_rfl
    show m ≤ F (U (τ ω) ω) + Real.log R
    rw [hFUV ω hB0ω, realLyap, hlogU ω hB0ω]
    rcases hτE with h1 | h2
    · have heq : σ * (U (τ ω) ω).re = ρ := le_antisymm h1 hmem.1
      rw [heq]
      have : 0 ≤ ε * (U (τ ω) ω).re ^ 2 := by positivity
      have := min_le_left (Real.log R - Real.log ρ) (ε * R ^ 2)
      linarith
    · have heq : σ * (U (τ ω) ω).re = R := le_antisymm hmem.2.1 h2
      have hsq : (U (τ ω) ω).re ^ 2 = R ^ 2 := by
        rw [← heq, mul_pow, show σ ^ 2 = σ * σ by ring, hσ, one_mul]
      rw [heq, hsq]
      have := min_le_right (Real.log R - Real.log ρ) (ε * R ^ 2)
      linarith
  calc P {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, realZ (drive κ B ω) σ ρ (x : ℂ) s ∈ rExit σ ρ R}
      ≤ P {ω | m ≤ Y ω} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | m ≤ Y ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal ((realLyap ε x + T * (ε * (κ + 4)) + Real.log R) / m) := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ hm0]
        linarith

/-- **DF-2, real points.** For `κ ∈ (0,4]` and real `x ≠ 0`, a.s. the real forward flow from
`x` survives up to time `T`. -/
theorem prob_not_isForwardSol_real (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {x : ℝ} (hx : x ≠ 0) (T : ℝ≥0) :
    P {ω | ¬ ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v} = 0 := by
  set σ : ℝ := if 0 < x then 1 else -1 with hσdef
  have hσ : σ * σ = 1 := by simp only [hσdef]; split_ifs <;> norm_num
  have hσx : σ * x = |x| := by
    simp only [hσdef]
    split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hx)]; ring
  have hax : 0 < |x| := abs_pos.2 hx
  have hnull : P {ω | ¬ B 0 ω = 0} = 0 := ae_iff.1 hB.eval_zero_ae_eq_zero
  have hbound : ∀ {ρ R ε : ℝ}, 0 < ρ → ρ < R → 0 < ε → ρ < |x| → |x| < R →
      P {ω | ¬ ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v} ≤ ENNReal.ofReal
        ((realLyap ε (x : ℂ) + T * (ε * (κ + 4)) + Real.log R)
          / min (Real.log R - Real.log ρ) (ε * R ^ 2)) := by
    intro ρ R ε hρ hρR hε hρx hxR
    have hsub : {ω | ¬ ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v} ⊆
        {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T,
          realZ (drive κ B ω) σ ρ (x : ℂ) s ∈ rExit σ ρ R} ∪ {ω | ¬ B 0 ω = 0} := by
      intro ω hω
      by_cases h : B 0 ω = 0
      · refine Or.inl ⟨h, ?_⟩
        by_contra hcon
        push Not at hcon
        apply hω
        refine ⟨_, isForwardSol_realZ (continuous_drive_ns hBc κ ω) hσ hρ T.coe_nonneg
          (fun t ht => ?_)⟩
        have := hcon t ht
        simp only [rExit, mem_union, Set.mem_ofPred_eq, not_or, not_le] at this
        exact this.1.le
      · exact Or.inr h
    calc P {ω | ¬ ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v}
        ≤ P ({ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T,
          realZ (drive κ B ω) σ ρ (x : ℂ) s ∈ rExit σ ρ R} ∪ {ω | ¬ B 0 ω = 0}) :=
          measure_mono hsub
      _ ≤ P {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T,
          realZ (drive κ B ω) σ ρ (x : ℂ) s ∈ rExit σ ρ R} + P {ω | ¬ B 0 ω = 0} :=
          measure_union_le _ _
      _ ≤ _ := by
          rw [hnull, add_zero]
          exact prob_real_exit_le hB hBm hBc hκ hκ4 hσ T hρ hρR hε (by rwa [hσx])
            (by rwa [hσx])
  set A : ℝ := -Real.log x with hA
  set Bc : ℝ := x ^ 2 + (T : ℝ) * (κ + 4) with hBc'
  set f : ℝ → ℝ := fun R => A / R + Bc / R / R + Real.log R / R with hf
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => A / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun R : ℝ => Bc / R / R) atTop (𝓝 0) :=
      (tendsto_const_nhds.div_atTop tendsto_id).div_atTop tendsto_id
    have h3 : Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    simpa using (h1.add h2).add h3
  have hev : ∀ᶠ R in atTop,
      P {ω | ¬ ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v} ≤ ENNReal.ofReal (f R) := by
    filter_upwards [eventually_gt_atTop (max 1 (max |x| (-Real.log |x|)))] with R hR
    have hR1 : 1 < R := (le_max_left _ _).trans_lt hR
    have hRa : |x| < R := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hR
    have hRl : -Real.log |x| < R := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hR
    set ρ : ℝ := Real.exp (-R) with hρdef
    have hρ : 0 < ρ := Real.exp_pos _
    have hρa : ρ < |x| := by
      rw [hρdef, ← Real.exp_log hax]; exact Real.exp_lt_exp.2 (by linarith)
    have hρR : ρ < R := hρa.trans hRa
    have hε : 0 < 1 / R := by positivity
    refine (hbound hρ hρR hε hρa hRa).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have hlogρ : Real.log ρ = -R := Real.log_exp _
    have hRR : 1 / R * R ^ 2 = R := by field_simp
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1.le
    have hm : min (Real.log R - Real.log ρ) (1 / R * R ^ 2) = R := by
      rw [hlogρ, hRR]; apply min_eq_right; linarith
    rw [hm]
    simp only [hf, realLyap, Complex.ofReal_re, hA, hBc']
    field_simp
    ring
  have hlim' : Tendsto (fun R => ENNReal.ofReal (f R)) atTop (𝓝 (ENNReal.ofReal 0)) :=
    ENNReal.tendsto_ofReal hlim
  refine le_antisymm ?_ zero_le
  simpa using ge_of_tendsto hlim' hev

/-- **DF-2, real points (a.s. form).** -/
theorem ae_isForwardSol_real (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {x : ℝ} (hx : x ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v := by
  lift T to ℝ≥0 using hT
  exact ae_iff.2 (prob_not_isForwardSol_real hB hBm hBc hκ hκ4 hx T)

theorem drive_zero_of {κ : ℝ} {ω : Ω} (h : B 0 ω = 0) : drive κ B ω 0 = 0 := by
  simp [drive, h]

/-- **FD-5 barriers, a.s.** For `κ ∈ (0,4]`, a.s. `W₀ = 0` and every barrier `±(n+1)` survives
up to time `T` (the hypotheses of `norm_fwdMap_le_of_barriers`). -/
theorem ae_barriers (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, drive κ B ω 0 = 0 ∧ ∀ n : ℕ,
      (∃ v, IsForwardSol (drive κ B ω) ((((n : ℝ) + 1 : ℝ)) : ℂ) T v) ∧
      ∃ v, IsForwardSol (drive κ B ω) ((-((n : ℝ) + 1) : ℝ) : ℂ) T v := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∃ v, IsForwardSol (drive κ B ω) ((((n : ℝ) + 1 : ℝ)) : ℂ) T v) ∧
      ∃ v, IsForwardSol (drive κ B ω) ((-((n : ℝ) + 1) : ℝ) : ℂ) T v := by
    rw [ae_all_iff]
    intro n
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    filter_upwards [ae_isForwardSol_real hB hBm hBc hκ hκ4 h1 hT,
      ae_isForwardSol_real hB hBm hBc hκ hκ4 (neg_ne_zero.2 h1) hT] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hall, hB.eval_zero_ae_eq_zero] with ω h hω
  exact ⟨drive_zero_of hω, h⟩

/-! ### 5. The clock through `Im f_T`, and joint measurability -/

/-- **FD-1.** `S_T(a) = ½ log(Im a / Im f_T(a))` while `a` is alive. -/
theorem fwdClock_eq_log (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a : ℂ} (ha : 0 < a.im)
    (hsol : ∃ u, IsForwardSol W a T u) :
    fwdClock W T a = 1 / 2 * Real.log (a.im / (fwdMap W T a).im) := by
  rw [im_fwdMap_eq_clock hW ha hsol ⟨hT, le_rfl⟩, div_mul_cancel_left₀ ha.ne', Real.log_inv,
    Real.log_exp]
  ring

theorem fwdClock_nonneg' {T : ℝ} (hT : 0 ≤ T) (a : ℂ) : 0 ≤ fwdClock W T a :=
  intervalIntegral.integral_nonneg hT fun _ _ => by positivity

/-- For `a` alive at `T`, the `1/(k+1)`-tamed flow and argument process agree with the true ones
on `[0,T]` for all large `k`. -/
theorem eventually_tamed_eq (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a : ℂ}
    (ha : a ∈ H \ fwdHull W T) :
    ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      tamedZ W (1 / ((k : ℝ) + 1)) a t = fwdMap W t a ∧
        tamedA W (1 / ((k : ℝ) + 1)) a t = (logDerivFwd W t a).im := by
  have ha0 : 0 < a.im := ha.1
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT ha.1 ha.2
  have hfu : ∀ t ∈ Icc (0 : ℝ) T, fwdMap W t a = u t := fun t ht => fwdMap_eq hW ha0 hu ht
  obtain ⟨hanti, hpos⟩ := im_isForwardSol_le hW ha0 hu
  have hTm : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hm : 0 < (u T).im := hpos T hTm
  have hge : ∀ t ∈ Icc (0 : ℝ) T, (u T).im ≤ (u t).im := fun t ht => hanti ht hTm ht.2
  obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt hm
  filter_upwards [eventually_ge_atTop k0] with k hk
  have hc : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have hkk : (k0 : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have : (k0 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcm : 1 / ((k : ℝ) + 1) ≤ (u T).im :=
    (one_div_le_one_div_of_le (by positivity) hkk).trans hk0.le
  have htz := tamedZ_eq_of_isForwardSol hW hc hT hu (fun t ht => hcm.trans (hge t ht))
  have htA := im_logDerivFwd_eq_tamedA hW hc hT ha0
    (fun t ht => by rw [htz t ht]; exact hcm.trans (hge t ht))
  intro t ht
  exact ⟨by rw [htz t ht, hfu t ht], (htA t ht).symm⟩

theorem measurableSet_dom_prod (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    MeasurableSet {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T} := by
  have e : {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T}
      = {p : ℂ × Ω | 0 < p.1.im} \ {p | p.1 ∈ fwdHull (drive κ B p.2) T} := by
    ext p; exact Iff.rfl
  rw [e]
  exact (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).diff
    (measurableSet_fwdHull_prod hBm hBc κ hT)

/-- Joint measurability of `(a, ω) ↦ f_s(a)` on `{a ∈ ℍ ∖ K_T}`, `s ≤ T`. -/
theorem measurable_fwdMap_dom (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T s : ℝ} (hT : 0 ≤ T)
    (hs : s ∈ Icc (0 : ℝ) T) :
    Measurable ({p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T}.indicator
      (fun p => fwdMap (drive κ B p.2) s p.1)) := by
  have hD := measurableSet_dom_prod hBm hBc κ hT
  refine measurable_of_tendsto_metrizable (f := fun (k : ℕ) =>
    {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T}.indicator
      (fun p => tamedZ (drive κ B p.2) (1 / ((k : ℝ) + 1)) p.1 s)) (fun k => ?_) ?_
  · exact (measurable_tamed_drive κ (by positivity) B hBc hs.1 (fun r _ => hBm r)).1.indicator hD
  · rw [tendsto_pi_nhds]
    intro p
    by_cases hp : p ∈ {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T}
    · simp only [indicator_of_mem hp]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_tamed_eq (continuous_drive_ns hBc κ p.2) hT hp] with k hk
      exact (hk s hs).1.symm
    · simp only [indicator_of_notMem hp]; exact tendsto_const_nhds

/-- Joint measurability of `(a, ω) ↦ Im log f_T'(a)` on `{a ∈ ℍ ∖ K_T}`. -/
theorem measurable_imLogDeriv_dom (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Measurable ({p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T}.indicator
      (fun p => (logDerivFwd (drive κ B p.2) T p.1).im)) := by
  have hD := measurableSet_dom_prod hBm hBc κ hT
  refine measurable_of_tendsto_metrizable (f := fun (k : ℕ) =>
    {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T}.indicator
      (fun p => tamedA (drive κ B p.2) (1 / ((k : ℝ) + 1)) p.1 T)) (fun k => ?_) ?_
  · exact (measurable_tamed_drive κ (by positivity) B hBc hT (fun r _ => hBm r)).2.indicator hD
  · rw [tendsto_pi_nhds]
    intro p
    by_cases hp : p ∈ {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T}
    · simp only [indicator_of_mem hp]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_tamed_eq (continuous_drive_ns hBc κ p.2) hT hp] with k hk
      exact (hk T ⟨hT, le_rfl⟩).2.symm
    · simp only [indicator_of_notMem hp]; exact tendsto_const_nhds

/-- Joint measurability of the clock `(a, ω) ↦ S_T(a)` on `{a ∈ ℍ ∖ K_T}`. -/
theorem measurable_fwdClock_dom (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Measurable ({p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T}.indicator
      (fun p => fwdClock (drive κ B p.2) T p.1)) := by
  set D := {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T} with hDdef
  have hD := measurableSet_dom_prod hBm hBc κ hT
  have hF := measurable_fwdMap_dom hBm hBc κ hT ⟨hT, le_rfl⟩
  have e : D.indicator (fun p => fwdClock (drive κ B p.2) T p.1)
      = D.indicator (fun p => 1 / 2 * Real.log (p.1.im /
          (D.indicator (fun p => fwdMap (drive κ B p.2) T p.1) p).im)) := by
    funext p
    by_cases hp : p ∈ D
    · rw [indicator_of_mem hp, indicator_of_mem hp, indicator_of_mem hp]
      exact fwdClock_eq_log (continuous_drive_ns hBc κ p.2) hT hp.1
        (exists_isForwardSol_of_not_mem_fwdHull hT hp.1 hp.2)
    · rw [indicator_of_notMem hp, indicator_of_notMem hp]
  rw [e]
  exact (((Complex.measurable_im.comp measurable_fst).div
    (Complex.measurable_im.comp hF)).log.const_mul _).indicator hD

/-- A closed condition holding at the rational times of `[0,T]` holds on `[0,T]`. -/
theorem forall_Icc_of_forall_rat {X : ℝ → ℂ} {T : ℝ} (hX : ContinuousOn X (Icc 0 T))
    {K : Set ℂ} (hK : IsClosed K) (h : ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T → X q ∈ K) :
    ∀ s ∈ Icc (0 : ℝ) T, X s ∈ K := by
  intro s hs
  have hcl : IsClosed (Icc (0 : ℝ) T ∩ X ⁻¹' K) :=
    hX.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hsub : Icc (0 : ℝ) T ∩ range ((↑) : ℚ → ℝ) ⊆ Icc 0 T ∩ X ⁻¹' K := by
    rintro _ ⟨hq, q, rfl⟩; exact ⟨hq, h q hq⟩
  rcases hs.1.eq_or_lt with h0 | h0
  · rw [← h0]
    have hT0 : (0 : ℝ) ≤ T := hs.1.trans hs.2
    have := h 0 (by simpa using hT0)
    simpa using this
  · have h1 : Ioo (0 : ℝ) s ⊆ closure (Icc (0 : ℝ) T ∩ range ((↑) : ℚ → ℝ)) :=
      (Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo).trans
        (closure_mono (inter_subset_inter_left _
          (Ioo_subset_Icc_self.trans (Icc_subset_Icc_right hs.2))))
    have h2 := closure_minimal h1 isClosed_closure
    rw [closure_Ioo h0.ne] at h2
    exact (closure_minimal hsub hcl (h2 ⟨h0.le, le_rfl⟩)).2

/-! ### 6. DF-3: the limit `ρ, c → 0` -/

theorem continuousOn_lyapV (κ ε : ℝ) : ContinuousOn (lyapV κ ε) H := fun _ hz =>
  (contDiffAt_lyapV κ ε hz).continuousAt.continuousWithinAt

/-- **DF-3 (clock integrability, `κ < 4`).** For `a ∈ ℍ` with `|a| < R`:
`E[S_T(a); a ∉ K_T, |f_s(a)| < R on [0,T]] ≤ C_R(a) := 2(V(a) + log R + C_g)/(4−κ)`.
`C_R` is continuous (hence locally bounded) on `ℍ` (`continuousOn_lyapV`). -/
theorem lintegral_fwdClock_ball_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {a : ℂ} (ha : 0 < a.im) (T : ℝ≥0) {R : ℝ} (haR : ‖a‖ < R) :
    ∫⁻ ω, {ω | a ∉ fwdHull (drive κ B ω) T ∧ ∀ s ∈ Icc (0 : ℝ) T,
        ‖fwdMap (drive κ B ω) s a‖ < R}.indicator
        (fun ω => ENNReal.ofReal (fwdClock (drive κ B ω) T a)) ω ∂P
      ≤ ENNReal.ofReal
        (2 * (lyapV κ 0 a + Real.log R + (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ)) / (4 - κ)) := by
  set Cb := ENNReal.ofReal
    (2 * (lyapV κ 0 a + Real.log R + (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ)) / (4 - κ)) with hCb
  set S := {ω | a ∉ fwdHull (drive κ B ω) T ∧ ∀ s ∈ Icc (0 : ℝ) T,
    ‖fwdMap (drive κ B ω) s a‖ < R} with hS
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (fwdClock (drive κ B ω) T a) with hg
  have hnorm : a.im ≤ ‖a‖ := (le_abs_self _).trans (Complex.abs_im_le_norm a)
  have hR : 0 < R := (norm_nonneg a).trans_lt haR
  set c : ℕ → ℝ := fun n => a.im / 2 * (1 / ((n : ℝ) + 1)) with hcdef
  have hc : ∀ n, 0 < c n := fun n => by positivity
  have hca : ∀ n, c n < a.im := fun n => by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have h2 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hcdef]; nlinarith
  set A' : ℕ → Set Ω := fun n => {ω | B 0 ω = 0 ∧ ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
    tamedZ (drive κ B ω) (c n) a q ∈ annReg (2 * c n) (R - c n) (2 * c n)} with hA'
  set hseq : ℕ → Ω → ℝ≥0∞ := fun n => (A' n).indicator g with hhseq
  have hA'm : ∀ n, MeasurableSet (A' n) := by
    intro n
    simp only [hA', Set.setOf_and, Set.setOf_forall]
    refine (measurableSet_eq_fun (hBm 0) measurable_const).inter
      (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_)
    have hmeas : Measurable fun ω => tamedZ (drive κ B ω) (c n) a q :=
      (measurable_tamed_drive κ (hc n) B hBc hq.1 (fun r _ => hBm r)).1.comp
        (measurable_const.prodMk measurable_id)
    exact hmeas (isClosed_annReg _ _ _).measurableSet
  have hstay : ∀ n ω, ω ∈ A' n → ∀ s ∈ Icc (0 : ℝ) T,
      tamedZ (drive κ B ω) (c n) a s ∈ annReg (2 * c n) (R - c n) (2 * c n) := fun n ω hω =>
    forall_Icc_of_forall_rat (continuousOn_tamedZ (continuous_drive_ns hBc κ ω) (hc n)
      T.coe_nonneg a) (isClosed_annReg _ _ _) hω.2
  have hhm : ∀ n, Measurable (hseq n) := by
    intro n
    have e : hseq n = (A' n).indicator (fun ω => ENNReal.ofReal
        (1 / 2 * Real.log (a.im / (tamedZ (drive κ B ω) (c n) a T).im))) := by
      funext ω
      by_cases hω : ω ∈ A' n
      · simp only [hhseq, indicator_of_mem hω, hg]
        have hW := continuous_drive_ns hBc κ ω
        have him : ∀ t ∈ Icc (0 : ℝ) T, c n ≤ (tamedZ (drive κ B ω) (c n) a t).im :=
          fun t ht => by have := (hstay n ω hω t ht).2.2; linarith [hc n]
        obtain ⟨hsol, heq⟩ := fwdMap_eq_tamedZ hW (hc n) T.coe_nonneg ha him
        rw [fwdClock_eq_log hW T.coe_nonneg ha hsol, heq T ⟨T.coe_nonneg, le_rfl⟩]
      · simp only [hhseq, indicator_of_notMem hω]
    rw [e]
    refine Measurable.indicator ?_ (hA'm n)
    have hm : Measurable fun ω => tamedZ (drive κ B ω) (c n) a T :=
      (measurable_tamed_drive κ (hc n) B hBc T.coe_nonneg (fun r _ => hBm r)).1.comp
        (measurable_const.prodMk measurable_id)
    exact ENNReal.measurable_ofReal.comp
      ((measurable_const.div (Complex.measurable_im.comp hm)).log.const_mul _)
  have hhle : ∀ n, ∫⁻ ω, hseq n ω ∂P ≤ Cb := by
    intro n
    have haO : a ∈ annOpen (c n) R (c n) := ⟨(hca n).trans_le hnorm, haR, hca n⟩
    refine le_trans (lintegral_mono fun ω => ?_)
      (lintegral_fwdClock_stay_le hB hBm hBc hκ hκ4 T (hc n) hR (hc n) haO)
    have hsub : A' n ⊆ {ω | B 0 ω = 0 ∧ ∀ s ∈ Icc (0 : ℝ) T,
        tamedZ (drive κ B ω) (c n) a s ∈ annOpen (c n) R (c n)} := fun ω hω =>
      ⟨hω.1, fun s hs => annReg_subset_annOpen (by linarith [hc n]) (by linarith [hc n])
        (by linarith [hc n]) (hstay n ω hω s hs)⟩
    exact indicator_le_indicator_of_subset hsub (fun _ => zero_le) ω
  have hlim : ∀ᵐ ω ∂P, S.indicator g ω ≤ liminf (fun n => hseq n ω) atTop := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω0
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω]
      refine le_liminf_of_le (by isBoundedDefault) ?_
      have hW := continuous_drive_ns hBc κ ω
      have haD : a ∈ H \ fwdHull (drive κ B ω) T := ⟨ha, hω.1⟩
      obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull T.coe_nonneg ha hω.1
      have hfu : ∀ t ∈ Icc (0 : ℝ) T, fwdMap (drive κ B ω) t a = u t := fun t ht =>
        fwdMap_eq hW ha hu ht
      obtain ⟨hanti, hpos⟩ := im_isForwardSol_le hW ha hu
      have hTm : (T : ℝ) ∈ Icc (0 : ℝ) T := ⟨T.coe_nonneg, le_rfl⟩
      have hm : 0 < (u T).im := hpos T hTm
      have hge : ∀ t ∈ Icc (0 : ℝ) T, (u T).im ≤ (fwdMap (drive κ B ω) t a).im := fun t ht => by
        rw [hfu t ht]; exact hanti ht hTm ht.2
      obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 T.coe_nonneg)
        (continuous_norm.comp_continuousOn (continuousOn_fwdMap_time hW T.coe_nonneg haD))
      have hM : ‖fwdMap (drive κ B ω) s0 a‖ < R := hω.2 s0 hs0
      have hle : ∀ t ∈ Icc (0 : ℝ) T,
          ‖fwdMap (drive κ B ω) t a‖ ≤ ‖fwdMap (drive κ B ω) s0 a‖ := fun t ht =>
        isMaxOn_iff.1 hmax t ht
      have hct : Tendsto c atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (a.im / 2)
        simpa [hcdef] using this
      have hpos' : 0 < min ((u T).im / 2) (R - ‖fwdMap (drive κ B ω) s0 a‖) :=
        lt_min (by linarith) (by linarith)
      filter_upwards [(tendsto_order.1 hct).2 _ hpos'] with n hn
      have hn1 : c n < (u T).im / 2 := hn.trans_le (min_le_left _ _)
      have hn2 : c n < R - ‖fwdMap (drive κ B ω) s0 a‖ := hn.trans_le (min_le_right _ _)
      have hωA : ω ∈ A' n := by
        refine ⟨hω0, fun q hq => ?_⟩
        have htz := tamedZ_eq_fwdMap hW (hc n) T.coe_nonneg ha ⟨u, hu⟩
          (fun t ht => by linarith [hge t ht]) q hq
        rw [htz]
        have h1 := hge q hq
        have h2 := hle q hq
        have h3 : (fwdMap (drive κ B ω) q a).im ≤ ‖fwdMap (drive κ B ω) q a‖ :=
          (le_abs_self _).trans (Complex.abs_im_le_norm _)
        exact ⟨by linarith, by linarith, by linarith⟩
      show g ω ≤ (A' n).indicator g ω
      rw [indicator_of_mem hωA]
    · rw [indicator_of_notMem hω]; exact zero_le
  calc ∫⁻ ω, S.indicator g ω ∂P ≤ ∫⁻ ω, liminf (fun n => hseq n ω) atTop ∂P :=
        lintegral_mono_ae hlim
    _ ≤ liminf (fun n => ∫⁻ ω, hseq n ω ∂P) atTop := lintegral_liminf_le hhm
    _ ≤ Cb := liminf_le_of_frequently_le' (Frequently.of_forall hhle)

/-! ### 7. A.s. clock integrability and integrability of `ρ·𝔥_T` -/

/-- **FD-5, uniform bound.** With barriers `±R₀` surviving to `T` and `W 0 = 0`, the images
`f_s(a)`, `a ∈ K ∖ K_T`, `s ∈ [0,T]`, are uniformly bounded (`|Re| < R₀`, `Im ≤ M` on `K`). -/
theorem exists_bound_fwdMap_of_barriers (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hp : ∃ v, IsForwardSol W (R₀ : ℂ) T v)
    (hm : ∃ v, IsForwardSol W ((-R₀ : ℝ) : ℂ) T v) {K : Set ℂ} {M : ℝ}
    (hK : ∀ a ∈ K, |a.re| < R₀ ∧ a.im ≤ M) :
    ∃ C, ∀ a ∈ K, a ∈ H \ fwdHull W T → ∀ s ∈ Icc (0 : ℝ) T, ‖fwdMap W s a‖ ≤ C := by
  obtain ⟨vp, hp⟩ := hp
  obtain ⟨vm, hm⟩ := hm
  obtain ⟨Cp, hCp⟩ := isCompact_Icc.exists_bound_of_continuousOn hp.1
  obtain ⟨Cm, hCm⟩ := isCompact_Icc.exists_bound_of_continuousOn hm.1
  refine ⟨Cp + Cm + M, fun a haK ha s hs => ?_⟩
  have hsK : a ∈ H \ fwdHull W s := ⟨ha.1, fun h => ha.2 (fwdHull_mono.1 hs.2 h)⟩
  have h := norm_fwdMap_le_of_barriers hW hs.1 (by rw [hW0, abs_zero]; exact hR₀)
    (isForwardSol_restrict hp hs.1 hs.2) (isForwardSol_restrict hm hs.1 hs.2) hsK (hK a haK).1
  have h1 : |(vp s).re| ≤ Cp := (Complex.abs_re_le_norm _).trans (hCp s hs)
  have h2 : |(vm s).re| ≤ Cm := (Complex.abs_re_le_norm _).trans (hCm s hs)
  linarith [(hK a haK).2]

/-- **DF-3, a.s. clock integrability (`κ < 4`).** For a measurable bounded `φ ≥ 0` vanishing
off a compact `K ⊆ ℍ`: a.s. `∫_{ℍ∖K_T} φ S_T < ∞`. -/
theorem ae_lintegral_clock_lt_top (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (T : ℝ≥0)
    {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) {cφ : ℝ≥0∞} (hcφ : cφ < ⊤) (hφc : ∀ z, φ z ≤ cφ)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hφK : ∀ z ∉ K, φ z = 0) :
    ∀ᵐ ω ∂P, ∫⁻ a in H \ fwdHull (drive κ B ω) T,
      φ a * ENNReal.ofReal (fwdClock (drive κ B ω) T a) < ⊤ := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hT := T.coe_nonneg
  set D := {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) (T : ℝ)} with hDdef
  have hD := measurableSet_dom_prod hBm hBc κ hT
  set J : ℂ × Ω → ℝ≥0∞ := fun p => φ p.1 *
    ENNReal.ofReal (D.indicator (fun p => fwdClock (drive κ B p.2) T p.1) p) with hJ
  have hJm : Measurable J :=
    (hφ.comp measurable_fst).mul (measurable_fwdClock_dom hBm hBc κ hT).ennreal_ofReal
  obtain ⟨R₁, hR₁⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  set Rn : ℕ → ℝ := fun n => (n : ℝ) + |R₁| + 1 with hRn
  set Sn : ℕ → Set (ℂ × Ω) := fun n => {p | ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
    ‖D.indicator (fun p => fwdMap (drive κ B p.2) q p.1) p‖ ≤ Rn n} with hSn
  have hSnm : ∀ n, MeasurableSet (Sn n) := by
    intro n
    simp only [hSn, Set.setOf_forall]
    exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq =>
      measurableSet_le (measurable_fwdMap_dom hBm hBc κ hT hq).norm measurable_const
  set JR : ℕ → ℂ × Ω → ℝ≥0∞ := fun n => (Sn n).indicator J with hJR
  have hJRm : ∀ n, Measurable (JR n) := fun n => hJm.indicator (hSnm n)
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn ((continuousOn_lyapV κ 0).mono hKH)
  set μG : ℝ := (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ) with hμG
  set Cn : ℕ → ℝ≥0∞ := fun n =>
    cφ * ENNReal.ofReal (2 * (L + Real.log (Rn n + 1) + μG) / (4 - κ)) with hCn
  have hsec : ∀ n a, ∫⁻ ω, JR n (a, ω) ∂P ≤ K.indicator (fun _ => Cn n) a := by
    intro n a
    by_cases haK : a ∈ K
    · rw [indicator_of_mem haK]
      have ha0 : 0 < a.im := hKH haK
      have haR : ‖a‖ < Rn n + 1 := by
        have := hR₁ a haK
        simp only [id] at this
        simp only [hRn]
        linarith [le_abs_self R₁, (n.cast_nonneg : (0 : ℝ) ≤ n)]
      set Sa := {ω | a ∉ fwdHull (drive κ B ω) T ∧ ∀ s ∈ Icc (0 : ℝ) T,
        ‖fwdMap (drive κ B ω) s a‖ < Rn n + 1} with hSa
      have hpt : ∀ ω, JR n (a, ω) ≤ cφ * Sa.indicator
          (fun ω => ENNReal.ofReal (fwdClock (drive κ B ω) T a)) ω := by
        intro ω
        by_cases hmem : (a, ω) ∈ Sn n ∧ (a, ω) ∈ D
        · have hW := continuous_drive_ns hBc κ ω
          have hin : ω ∈ Sa := by
            refine ⟨hmem.2.2, fun s hs => ?_⟩
            have hball := forall_Icc_of_forall_rat (continuousOn_fwdMap_time hW hT hmem.2)
              (Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := Rn n)) (fun q hq => by
                have := hmem.1 q hq
                rw [indicator_of_mem hmem.2] at this
                simpa using this) s hs
            rw [Metric.mem_closedBall, dist_zero_right] at hball
            linarith
          rw [indicator_of_mem hin]
          simp only [hJR, hJ, indicator_of_mem hmem.1, indicator_of_mem hmem.2]
          exact mul_le_mul_of_nonneg_right (hφc a) zero_le
        · rcases not_and_or.1 hmem with h | h
          · simp only [hJR, indicator_of_notMem h]; exact zero_le
          · simp only [hJR, hJ]
            by_cases h' : (a, ω) ∈ Sn n
            · rw [indicator_of_mem h', indicator_of_notMem h]; simp
            · rw [indicator_of_notMem h']; exact zero_le
      calc ∫⁻ ω, JR n (a, ω) ∂P
          ≤ ∫⁻ ω, cφ * Sa.indicator (fun ω => ENNReal.ofReal (fwdClock (drive κ B ω) T a)) ω ∂P :=
            lintegral_mono hpt
        _ = cφ * ∫⁻ ω, Sa.indicator
              (fun ω => ENNReal.ofReal (fwdClock (drive κ B ω) T a)) ω ∂P :=
            lintegral_const_mul' _ _ hcφ.ne
        _ ≤ cφ * ENNReal.ofReal
              (2 * (lyapV κ 0 a + Real.log (Rn n + 1) + μG) / (4 - κ)) :=
            mul_le_mul_of_nonneg_left
              (lintegral_fwdClock_ball_le hB hBm hBc hκ hκ4 ha0 T haR) zero_le
        _ ≤ Cn n := by
            refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal
              (div_le_div_of_nonneg_right ?_ (by linarith))) zero_le
            have h := hL a haK
            rw [Real.norm_eq_abs] at h
            linarith [le_abs_self (lyapV κ 0 a)]
    · rw [indicator_of_notMem haK]
      have : ∀ ω, JR n (a, ω) = 0 := fun ω => by
        simp only [hJR, hJ]
        by_cases h' : (a, ω) ∈ Sn n
        · rw [indicator_of_mem h', hφK a haK, zero_mul]
        · rw [indicator_of_notMem h']
      simp [this]
  have hfin : ∀ n, ∫⁻ ω, ∫⁻ a, JR n (a, ω) ∂volume ∂P < ⊤ := by
    intro n
    rw [lintegral_lintegral_swap (by exact ((hJRm n).comp measurable_swap).aemeasurable)]
    calc ∫⁻ a, ∫⁻ ω, JR n (a, ω) ∂P ∂volume ≤ ∫⁻ a, K.indicator (fun _ => Cn n) a :=
          lintegral_mono (hsec n)
      _ ≤ Cn n * volume K := lintegral_indicator_const_le _ _
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hcφ ENNReal.ofReal_lt_top)
          hK.measure_lt_top
  have hae : ∀ᵐ ω ∂P, ∀ n, ∫⁻ a, JR n (a, ω) < ⊤ := by
    rw [ae_all_iff]
    intro n
    exact ae_lt_top (hJRm n).lintegral_prod_left' (hfin n).ne
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt R₁
  filter_upwards [hae, ae_barriers hB hBm hBc hκ hκ4.le hT] with ω hfinω hbarω
  obtain ⟨hW0, hbar⟩ := hbarω
  have hW := continuous_drive_ns hBc κ ω
  obtain ⟨Cb, hCb⟩ := exists_bound_fwdMap_of_barriers hW hW0 (R₀ := (n₀ : ℝ) + 1)
    (by positivity) (hbar n₀).1 (hbar n₀).2 (K := K) (M := R₁) (fun a haK => by
      have := hR₁ a haK
      simp only [id] at this
      exact ⟨by linarith [Complex.abs_re_le_norm a],
        by linarith [(le_abs_self a.im).trans (Complex.abs_im_le_norm a)]⟩)
  obtain ⟨n, hn⟩ := exists_nat_gt Cb
  have heq : ∀ a, (H \ fwdHull (drive κ B ω) T).indicator
      (fun a => φ a * ENNReal.ofReal (fwdClock (drive κ B ω) T a)) a = JR n (a, ω) := by
    intro a
    have hJa : (H \ fwdHull (drive κ B ω) T).indicator
        (fun a => φ a * ENNReal.ofReal (fwdClock (drive κ B ω) T a)) a = J (a, ω) := by
      by_cases hD' : (a, ω) ∈ D
      · rw [indicator_of_mem (show a ∈ H \ fwdHull (drive κ B ω) T from hD'), hJ]
        simp only [indicator_of_mem hD']
      · rw [indicator_of_notMem (show a ∉ H \ fwdHull (drive κ B ω) T from hD'), hJ]
        simp only [indicator_of_notMem hD']; simp
    rw [hJa]
    by_cases hmem : (a, ω) ∈ Sn n
    · simp only [hJR, indicator_of_mem hmem]
    · by_cases haK : a ∈ K
      · by_cases hD' : (a, ω) ∈ D
        · exfalso
          apply hmem
          intro q hq
          rw [indicator_of_mem hD']
          have := hCb a haK hD' q hq
          simp only [hRn]
          linarith [abs_nonneg R₁]
        · simp only [hJR, indicator_of_notMem hmem, hJ, indicator_of_notMem hD']; simp
      · simp only [hJR, indicator_of_notMem hmem, hJ, hφK a haK, zero_mul]
  have hSm : MeasurableSet (H \ fwdHull (drive κ B ω) T) :=
    hD.preimage (measurable_id.prodMk measurable_const)
  rw [← lintegral_indicator hSm]
  simp_rw [heq]
  exact hfinω n

/-- **DF-3, a.s. clock integrability**, real time. -/
theorem ae_lintegral_clock_lt_top' (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 ≤ T) {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) {cφ : ℝ≥0∞} (hcφ : cφ < ⊤)
    (hφc : ∀ z, φ z ≤ cφ) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (hφK : ∀ z ∉ K, φ z = 0) :
    ∀ᵐ ω ∂P, ∫⁻ a in H \ fwdHull (drive κ B ω) T,
      φ a * ENNReal.ofReal (fwdClock (drive κ B ω) T a) < ⊤ := by
  lift T to ℝ≥0 using hT
  exact ae_lintegral_clock_lt_top hB hBm hBc hκ hκ4 T hφ hcφ hφc hK hKH hφK

/-- **FD-1 domination.** `|𝔥_T| ≤ 1_{ℍ∖K_T}(2π/√κ + 2|χ| S_T)`. -/
theorem abs_hTfwd_le (hW : Continuous W) {κ : ℝ} (hκ : 0 < κ) {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    |hTfwd κ W T z| ≤ (H \ fwdHull W T).indicator
      (fun z => 2 * Real.pi / Real.sqrt κ + 2 * |chiC κ| * fwdClock W T z) z := by
  by_cases hz : z ∈ H \ fwdHull W T
  · rw [hTfwd, if_pos hz, indicator_of_mem hz]
    have hsol := exists_isForwardSol_of_not_mem_fwdHull hT hz.1 hz.2
    have h1 : |h0fwd κ (fwdMap W T z)| ≤ 2 * Real.pi / Real.sqrt κ := by
      rw [h0fwd, abs_mul, abs_neg, abs_div, abs_two, abs_of_pos (Real.sqrt_pos.2 hκ)]
      have := Complex.abs_arg_le_pi (fwdMap W T z)
      calc 2 / Real.sqrt κ * |Complex.arg (fwdMap W T z)| ≤ 2 / Real.sqrt κ * Real.pi := by
            gcongr
        _ = 2 * Real.pi / Real.sqrt κ := by ring
    have h2 := abs_im_logDerivFwd_le hW hz.1 hsol ⟨hT, le_rfl⟩
    calc |h0fwd κ (fwdMap W T z) - chiC κ * (logDerivFwd W T z).im|
        ≤ |h0fwd κ (fwdMap W T z)| + |chiC κ * (logDerivFwd W T z).im| := abs_sub _ _
      _ ≤ _ := by
          rw [abs_mul]
          have := mul_le_mul_of_nonneg_left h2 (abs_nonneg (chiC κ))
          linarith
  · rw [hTfwd, if_neg hz, indicator_of_notMem hz, abs_zero]

theorem measurable_hTfwd (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous fun t => B t ω)
    {κ T : ℝ} (hT : 0 ≤ T) (ω : Ω) : Measurable (hTfwd κ (drive κ B ω) T) := by
  set D := {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T} with hDdef
  have hF := measurable_fwdMap_dom hBm hBc κ hT ⟨hT, le_rfl⟩
  have hA := measurable_imLogDeriv_dom hBm hBc κ hT
  have hD := measurableSet_dom_prod hBm hBc κ hT
  have hj : Measurable fun a : ℂ => ((a, ω) : ℂ × Ω) := measurable_id.prodMk measurable_const
  have e : hTfwd κ (drive κ B ω) T = fun a => D.indicator (fun p =>
      h0fwd κ (D.indicator (fun p => fwdMap (drive κ B p.2) T p.1) p)
        - chiC κ * D.indicator (fun p => (logDerivFwd (drive κ B p.2) T p.1).im) p) (a, ω) := by
    funext a
    by_cases ha : (a, ω) ∈ D
    · rw [indicator_of_mem ha, indicator_of_mem ha, indicator_of_mem ha, hTfwd,
        if_pos (show a ∈ H \ fwdHull (drive κ B ω) T from ha)]
    · rw [indicator_of_notMem ha, hTfwd,
        if_neg (show a ∉ H \ fwdHull (drive κ B ω) T from ha)]
  rw [e]
  have hh0 : Measurable (h0fwd κ) := by
    show Measurable fun z => -(2 / Real.sqrt κ) * Complex.arg z
    exact measurable_const.mul Complex.measurable_arg
  exact (((hh0.comp hF).sub (hA.const_mul _)).indicator hD).comp hj

theorem chiC_four : chiC 4 = 0 := by
  have : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [chiC, this]; norm_num

/-- **MF-6 domination.** For `κ ∈ (0,4]` and `ρ ∈ C_c^∞(ℍ)`, a.s. `ρ·𝔥_T` is integrable. -/
theorem ae_integrable_mul_hTfwd (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {T : ℝ}
    (hT : 0 ≤ T) (ρ : TestFun H) :
    ∀ᵐ ω ∂P, Integrable (fun z => ρ.1 z * hTfwd κ (drive κ B ω) T z) := by
  obtain ⟨hρs, hρc, hρH⟩ := ρ.2
  have hρcont : Continuous ρ.1 := hρs.continuous
  have hρi : Integrable ρ.1 := hρcont.integrable_of_hasCompactSupport hρc
  obtain ⟨Cρ, hCρ⟩ := hρcont.bounded_above_of_compact_support hρc
  set cst : ℝ := 2 * Real.pi / Real.sqrt κ with hcst
  have hclock : ∀ᵐ ω ∂P, chiC κ = 0 ∨ ∫⁻ a in H \ fwdHull (drive κ B ω) T,
      ENNReal.ofReal |ρ.1 a| * ENNReal.ofReal (fwdClock (drive κ B ω) T a) < ⊤ := by
    rcases hκ4.lt_or_eq with hlt | heq
    · have h := ae_lintegral_clock_lt_top' hB hBm hBc hκ hlt hT
        (φ := fun a => ENNReal.ofReal |ρ.1 a|)
        ((continuous_abs.comp hρcont).measurable.ennreal_ofReal) (cφ := ENNReal.ofReal Cρ)
        ENNReal.ofReal_lt_top (fun z => ENNReal.ofReal_le_ofReal (by
          have := hCρ z; rwa [Real.norm_eq_abs] at this))
        (K := tsupport ρ.1) hρc hρH (fun z hz => by
          simp [image_eq_zero_of_notMem_tsupport hz])
      filter_upwards [h] with ω hω using Or.inr hω
    · exact Eventually.of_forall fun _ => Or.inl (by rw [heq]; exact chiC_four)
  filter_upwards [hclock] with ω hω
  have hW := continuous_drive_ns hBc κ ω
  refine ⟨(hρcont.measurable.mul (measurable_hTfwd hBm hBc hT ω)).aestronglyMeasurable, ?_⟩
  set S := H \ fwdHull (drive κ B ω) T with hS
  have hSm : MeasurableSet S :=
    (measurableSet_dom_prod hBm hBc κ hT).preimage (measurable_id.prodMk measurable_const)
  have hpt : ∀ z, ‖ρ.1 z * hTfwd κ (drive κ B ω) T z‖ₑ ≤ ENNReal.ofReal (|ρ.1 z| * cst)
      + ENNReal.ofReal (2 * |chiC κ|) * S.indicator (fun a => ENNReal.ofReal |ρ.1 a| *
        ENNReal.ofReal (fwdClock (drive κ B ω) T a)) z := by
    intro z
    rw [Real.enorm_eq_ofReal_abs, abs_mul]
    have hb := abs_hTfwd_le hW hκ hT z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz] at hb ⊢
      have hc0 : 0 ≤ fwdClock (drive κ B ω) T z := fwdClock_nonneg' hT z
      have hn : 0 ≤ 2 * |chiC κ| * (|ρ.1 z| * fwdClock (drive κ B ω) T z) :=
        mul_nonneg (by positivity) (mul_nonneg (abs_nonneg _) hc0)
      have e : ENNReal.ofReal (|ρ.1 z| * cst) + ENNReal.ofReal (2 * |chiC κ|) *
          (ENNReal.ofReal |ρ.1 z| * ENNReal.ofReal (fwdClock (drive κ B ω) T z))
          = ENNReal.ofReal (|ρ.1 z| * cst
            + 2 * |chiC κ| * (|ρ.1 z| * fwdClock (drive κ B ω) T z)) := by
        rw [ENNReal.ofReal_add (by positivity) hn,
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * |chiC κ| by positivity),
          ENNReal.ofReal_mul (abs_nonneg (ρ.1 z)) (q := fwdClock (drive κ B ω) T z)]
      rw [e]
      apply ENNReal.ofReal_le_ofReal
      calc |ρ.1 z| * |hTfwd κ (drive κ B ω) T z|
          ≤ |ρ.1 z| * (cst + 2 * |chiC κ| * fwdClock (drive κ B ω) T z) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = _ := by ring
    · rw [indicator_of_notMem hz] at hb ⊢
      have : |hTfwd κ (drive κ B ω) T z| = 0 := le_antisymm hb (abs_nonneg _)
      rw [this, mul_zero, ENNReal.ofReal_zero]; exact zero_le
  have hm1 : Measurable fun z => ENNReal.ofReal (|ρ.1 z| * cst) :=
    ((continuous_abs.comp hρcont).measurable.mul_const _).ennreal_ofReal
  show ∫⁻ z, ‖ρ.1 z * hTfwd κ (drive κ B ω) T z‖ₑ < ⊤
  calc ∫⁻ z, ‖ρ.1 z * hTfwd κ (drive κ B ω) T z‖ₑ
      ≤ ∫⁻ z, (ENNReal.ofReal (|ρ.1 z| * cst) + ENNReal.ofReal (2 * |chiC κ|) *
          S.indicator (fun a => ENNReal.ofReal |ρ.1 a| *
            ENNReal.ofReal (fwdClock (drive κ B ω) T a)) z) := lintegral_mono hpt
    _ = (∫⁻ z, ENNReal.ofReal (|ρ.1 z| * cst)) + ENNReal.ofReal (2 * |chiC κ|) *
          ∫⁻ z, S.indicator (fun a => ENNReal.ofReal |ρ.1 a| *
            ENNReal.ofReal (fwdClock (drive κ B ω) T a)) z := by
        rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨(hρi.abs.mul_const cst).lintegral_lt_top, ?_⟩
        rcases hω with hχ | hfin
        · rw [hχ]; simp
        · rw [lintegral_indicator hSm]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ClockInt
end QuantumZipper
