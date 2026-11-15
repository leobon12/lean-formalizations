import QuantumZipper.Proofs.Thm11.NonSwallowing
import QuantumZipper.Proofs.Zipper.Collision
import InteractingSLE.Foundations.SLE.SpaceFilling

/-!
# Points near the origin are swallowed with probability `≥ 1/2` (`κ > 4`)

Packet `planning/packets/PROVE-RS05-74c.md`; the positivity half of [RS05, Lemma 6.5] (`posvol`,
`SLEcont.tex` lines 2048–2128), used in the proof of [RS05, Lemma 7.3] for `κ > 8` ("We know from
Theorem 6.4 and Lemma 6.5 that a.s. `z_0 ∈ γ[0,∞)`").

For `κ > 4` let `b = 1 − 4/κ ∈ (0,1)` and `θ = e^{2πi/κ}` (`arg θ = π(1−b)/2`). The function
`h(z) = Im(θ z^b)` is harmonic for the one-point flow `Z_t = g_t(z) − W_t`
(`dZ = 2/Z dt − √κ dB`): its Dynkin generator `Im(θ b z^{b−2}(2 + κ(b−1)/2))` vanishes; and
`h(z) ≥ cos(πb/2) |z|^b` on `ℍ̄`. The function `(Re z)²` has generator `4 (Re z)²/|z|² + κ ≥ κ`.
Running both through the Dynkin formula for the tamed flow stopped at the exit time `τ` of
`{|z| < 1, Im z > c}` (capped at `T`):

* `κ E τ ≤ 1`, so `P(τ = T) ≤ 1/(κT)`;
* `E h(Z_τ) = h(a)`, so `P(|Z_τ| = 1) ≤ |a|^b / cos(πb/2)`;

otherwise the flow reaches `Im Z ≤ c` before time `T`. Letting `c → 0`: if `a ∉ K_T` the true flow
stays above a positive height on `[0,T]` and coincides with the tamed flows, so for small `c` it
does not reach `Im Z ≤ c`. Hence `P(a ∉ K_T) ≤ |a|^b/cos(πb/2) + 1/(κT)`. RS's "sprint times"
(needed for probability one) are replaced by the bound on `E τ`; positivity is all that is used.

## Main results

* `exists_cutoff_eq`: smooth bounded cutoffs.
* `dynkinGen_sqRe_tamed`, `dynkinGen_hPos`: the two generators.
* `prob_mem_fwdHull_ge`: for `κ > 4`, `a ∈ ℍ`, `|a|^b ≤ cos(πb/2)/4`:
  `P(a ∈ K_{4/κ}) ≥ 1/2`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

/-! ### Smooth cutoffs -/

/-- A smooth function with bounded derivatives (orders `≤ 3`) and compact support that agrees
with `G` near the region `{|z| ≤ 1, Im z ≥ c}`, for `G` of class `C³` on `ℍ`. -/
theorem exists_cutoff_eq {G : ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hG : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 3 G z) :
    ∃ F : ℂ → ℝ, ∃ C : ℝ, ContDiff ℝ 3 F ∧
      (∀ x, |F x| ≤ C ∧ ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 F x‖ ≤ C) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ z.im → F =ᶠ[𝓝 z] G := by
  set O : Set ℂ := {z | ‖z‖ < 2 ∧ c / 2 < z.im} with hO
  set K₁ : Set ℂ := {z | ‖z‖ ≤ 3 / 2 ∧ 3 * c / 4 ≤ z.im} with hK₁
  set K₂ : Set ℂ := {z | ‖z‖ ≤ 2 ∧ c / 2 ≤ z.im} with hK₂
  have hOo : IsOpen O := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hK₁c : IsClosed K₁ := (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_im)
  have hK₂c : IsClosed K₂ := (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_im)
  have hK₁O : K₁ ⊆ O := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hOK₂ : O ⊆ K₂ := fun z hz => ⟨hz.1.le, hz.2.le⟩
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hOo hK₁c hK₁O
  have hts : tsupport χ ⊆ K₂ := by
    rw [tsupport, hχs]; exact closure_minimal hOK₂ hK₂c
  have hK₂b : K₂ ⊆ closedBall 0 2 := fun z hz => mem_closedBall_zero_iff.2 hz.1
  have hχc : HasCompactSupport χ :=
    (isCompact_closedBall 0 2).of_isClosed_subset (isClosed_tsupport χ) (hts.trans hK₂b)
  set F : ℂ → ℝ := χ * G with hFdef
  have hFs : ContDiff ℝ 3 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : 0 < x.im
    · exact (hχ.contDiffAt.of_le (by exact WithTop.coe_le_coe.2 le_top)).mul (hG x hx)
    · have hxt : x ∉ tsupport χ := fun h => hx (by have := (hts h).2; linarith)
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
  · intro z hz1 hzc
    have hmem : ball z (min (1 / 2) (c / 4)) ∈ 𝓝 z := ball_mem_nhds z (by positivity)
    filter_upwards [hmem] with y hy
    have hyK : y ∈ K₁ := by
      rw [mem_ball] at hy
      have h1 : dist y z < 1 / 2 := hy.trans_le (min_le_left _ _)
      have h2 : dist y z < c / 4 := hy.trans_le (min_le_right _ _)
      refine ⟨?_, ?_⟩
      · have := norm_le_norm_add_norm_sub' y z
        rw [dist_eq_norm] at h1
        linarith
      · have := Complex.abs_im_le_norm (y - z)
        rw [Complex.sub_im] at this
        rw [dist_eq_norm] at h2
        linarith [(abs_le.1 this).1]
    have : χ y = 1 := (hχ1 y).1 hyK
    simp [hFdef, this]

/-! ### The generator of `(Re z)²` -/

/-- **Generator of `(Re z)²`** for the tamed forward flow where the taming is inactive:
`L (Re z)² = 4 (Re z)² / |z|² + κ`. -/
theorem dynkinGen_sqRe_tamed {κ c : ℝ} (hκ : 0 ≤ κ) {z : ℂ} (hz : c ≤ z.im) (hz0 : 0 < z.im) :
    dynkinGen (tamedZField c) (-((Real.sqrt κ : ℝ) : ℂ)) Collision.sqRe z =
      4 * z.re ^ 2 / (z.re ^ 2 + z.im ^ 2) + κ := by
  have hqd : HasDerivAt (fun s : ℝ => z.re + s * (-Real.sqrt κ)) (-Real.sqrt κ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (-Real.sqrt κ)).const_add z.re
  have hφ := (hqd.const_mul 2).mul_const (-Real.sqrt κ)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ),
      fderiv ℝ Collision.sqRe (z + ((s : ℝ) : ℂ) * (-((Real.sqrt κ : ℝ) : ℂ)))
        (-((Real.sqrt κ : ℝ) : ℂ)) =
      (fun s : ℝ => 2 * (z.re + s * (-Real.sqrt κ)) * (-Real.sqrt κ)) s :=
    Filter.Eventually.of_forall fun s => by
      rw [Collision.fderiv_sqRe_apply]; simp
  have hC2 : ContDiffAt ℝ 2 Collision.sqRe z := Collision.contDiff_sqRe.contDiffAt
  unfold dynkinGen
  rw [NonSwallow.tamedZField_of_le hz, Collision.fderiv_sqRe_apply,
    NonSwallow.iteratedFDeriv_two_eq_of_line hC2 _ hev hφ]
  have hn : z.re ^ 2 + z.im ^ 2 ≠ 0 := by positivity
  simp only [Complex.div_re, Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat]
  have hk : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ
  field_simp
  nlinarith [hk]

/-! ### The harmonic function `h(z) = Im(θ z^b)` -/

/-- The rotation `θ = e^{2πi/κ}`. -/
def hTheta (κ : ℝ) : ℂ := Complex.exp (((2 * π / κ : ℝ) : ℂ) * I)

/-- The exponent `b = 1 − 4/κ` (as a complex number). -/
def hExp (κ : ℝ) : ℂ := ((1 - 4 / κ : ℝ) : ℂ)

/-- **[RS05, Lemma 6.5]'s harmonic function** `h(z) = Im(θ z^b)`, `θ = e^{2πi/κ}`, `b = 1 − 4/κ`. -/
def hPos (κ : ℝ) (z : ℂ) : ℝ := (hTheta κ * z ^ hExp κ).im

theorem mem_slitPlane_of_im_pos' {z : ℂ} (hz : 0 < z.im) : z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr hz.ne')

theorem hasDerivAt_hPosC (κ : ℝ) {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt (fun w => hTheta κ * w ^ hExp κ) (hTheta κ * (hExp κ * w ^ (hExp κ - 1))) w :=
  ((Complex.hasStrictDerivAt_cpow_const hw).hasDerivAt).const_mul _

theorem hasDerivAt_hPosC' (κ : ℝ) {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt (fun w => hTheta κ * (hExp κ * w ^ (hExp κ - 1)))
      (hTheta κ * (hExp κ * ((hExp κ - 1) * w ^ (hExp κ - 1 - 1)))) w :=
  (((Complex.hasStrictDerivAt_cpow_const hw).hasDerivAt).const_mul _).const_mul _

theorem hasFDerivAt_hPos (κ : ℝ) {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasFDerivAt (hPos κ) (Complex.imCLM.comp (((ContinuousLinearMap.smulRight
      (1 : ℂ →L[ℂ] ℂ) (hTheta κ * (hExp κ * w ^ (hExp κ - 1))))).restrictScalars ℝ)) w :=
  Complex.imCLM.hasFDerivAt.comp w ((hasDerivAt_hPosC κ hw).hasFDerivAt.restrictScalars ℝ)

theorem fderiv_hPos_apply (κ : ℝ) {w : ℂ} (hw : w ∈ Complex.slitPlane) (v : ℂ) :
    fderiv ℝ (hPos κ) w v = (v * (hTheta κ * (hExp κ * w ^ (hExp κ - 1)))).im := by
  rw [(hasFDerivAt_hPos κ hw).fderiv]
  simp

theorem contDiffAt_hPos (κ : ℝ) {w : ℂ} (hw : w ∈ Complex.slitPlane) (n : ℕ) :
    ContDiffAt ℝ n (hPos κ) w := by
  have ha : AnalyticAt ℂ (fun w : ℂ => w ^ hExp κ) w :=
    analyticAt_id.cpow analyticAt_const hw
  have hc : ContDiffAt ℂ n (fun w => hTheta κ * w ^ hExp κ) w :=
    contDiffAt_const.mul ha.contDiffAt
  exact Complex.imCLM.contDiff.contDiffAt.comp w (hc.restrict_scalars ℝ)

/-- **`h` is harmonic for the forward one-point flow**: its Dynkin generator vanishes where the
taming is inactive, because `2 + κ (b − 1)/2 = 0` for `b = 1 − 4/κ`. -/
theorem dynkinGen_hPos {κ c : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : c ≤ z.im) (hz0 : 0 < z.im) :
    dynkinGen (tamedZField c) (-((Real.sqrt κ : ℝ) : ℂ)) (hPos κ) z = 0 := by
  set e : ℂ := -((Real.sqrt κ : ℝ) : ℂ) with he
  have hzs := mem_slitPlane_of_im_pos' hz0
  have hz0' : z ≠ 0 := fun h => by simp [h] at hz0
  have hline : HasDerivAt (fun s : ℝ => z + (s : ℂ) * e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const e).const_add z
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), fderiv ℝ (hPos κ) (z + ((s : ℝ) : ℂ) * e) e =
      (fun s : ℝ => (e * (hTheta κ * (hExp κ * (z + (s : ℂ) * e) ^ (hExp κ - 1)))).im) s := by
    refine Filter.Eventually.of_forall fun s => ?_
    have hs : z + (s : ℂ) * e ∈ Complex.slitPlane := mem_slitPlane_of_im_pos' (by simpa [he])
    exact fderiv_hPos_apply κ hs e
  have hφ : HasDerivAt (fun s : ℝ => (e * (hTheta κ * (hExp κ * (z + (s : ℂ) * e) ^ (hExp κ - 1)))).im)
      (e * (hTheta κ * (hExp κ * ((hExp κ - 1) * z ^ (hExp κ - 1 - 1))) * e)).im 0 := by
    have h1 := HasDerivAt.comp (0 : ℝ) (by simpa using hasDerivAt_hPosC' κ hzs) hline
    have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 (h1.const_mul e) rfl
    refine h3.congr_deriv ?_
    simp only [Complex.imCLM_apply]
  have hC2 : ContDiffAt ℝ 2 (hPos κ) z := contDiffAt_hPos κ hzs 2
  unfold dynkinGen
  rw [NonSwallow.tamedZField_of_le hz, fderiv_hPos_apply κ hzs,
    NonSwallow.iteratedFDeriv_two_eq_of_line hC2 e hev hφ]
  -- algebra: `z^{b−1} = z^{b−2} z` and `2 + κ (b−1)/2 = 0`
  have hpow : z ^ (hExp κ - 1) = z ^ (hExp κ - 1 - 1) * z := by
    conv_lhs => rw [show hExp κ - 1 = (hExp κ - 1 - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hz0', Complex.cpow_one]
  have hee : e * e = (κ : ℂ) := by
    rw [he, neg_mul_neg, ← Complex.ofReal_mul, Real.mul_self_sqrt hκ.le]
  have hb' : (hExp κ - 1) * (κ : ℂ) = -4 := by
    have hk : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ.ne'
    simp only [hExp]
    push_cast
    field_simp
    ring
  set Q : ℂ := z ^ (hExp κ - 1 - 1) with hQ
  have key : 2 / z * (hTheta κ * (hExp κ * z ^ (hExp κ - 1))) +
      1 / 2 * (e * (hTheta κ * (hExp κ * ((hExp κ - 1) * Q))) * e) = 0 := by
    rw [hpow]
    have hzz : (2 : ℂ) / z * (hTheta κ * (hExp κ * (Q * z))) = 2 * (hTheta κ * hExp κ * Q) := by
      field_simp
    have h2 : 1 / 2 * (e * (hTheta κ * (hExp κ * ((hExp κ - 1) * Q))) * e) =
        1 / 2 * ((hExp κ - 1) * (e * e)) * (hTheta κ * hExp κ * Q) := by ring
    rw [hzz, h2, hee, hb']
    ring
  have hre := congrArg Complex.im key
  have h12 : ∀ w : ℂ, ((1 : ℂ) / 2 * w).im = 1 / 2 * w.im := fun w => by
    simp [Complex.mul_im]
  simp only [Complex.add_im, Complex.zero_im, h12] at hre
  rw [← hre, mul_assoc e]

/-- `h(z) = |z|^b sin(b arg z + 2π/κ)` for `z ≠ 0`. -/
theorem hPos_eq {κ : ℝ} {z : ℂ} (hz : z ≠ 0) :
    hPos κ z = ‖z‖ ^ (1 - 4 / κ) * Real.sin ((1 - 4 / κ) * Complex.arg z + 2 * π / κ) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold hPos hTheta hExp
  rw [Complex.cpow_def_of_ne_zero hz, ← Complex.exp_add, Complex.exp_im]
  congr 1
  · rw [Real.rpow_def_of_pos hn]
    congr 1
    simp [Complex.log_re, Complex.mul_re, mul_comm]
  · congr 1
    simp [Complex.log_im, Complex.mul_im]
    ring

/-- `sin x ≥ sin α` for `x ∈ [α, π − α]`, `0 ≤ α ≤ π/2`. -/
theorem sin_ge_of_mem {α x : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ π / 2) (h1 : α ≤ x) (h2 : x ≤ π - α) :
    Real.sin α ≤ Real.sin x := by
  rcases le_total x (π / 2) with hx | hx
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx h1
  · rw [← Real.sin_pi_sub x]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

/-- **Bounds on `h` in the closed half-plane** (`κ > 4`):
`sin(2π/κ) |z|^b ≤ h(z) ≤ |z|^b` for `z ≠ 0`, `Im z ≥ 0`. -/
theorem hPos_bounds {κ : ℝ} (hκ : 4 < κ) {z : ℂ} (hz : z ≠ 0) (hzi : 0 ≤ z.im) :
    Real.sin (2 * π / κ) * ‖z‖ ^ (1 - 4 / κ) ≤ hPos κ z ∧ hPos κ z ≤ ‖z‖ ^ (1 - 4 / κ) := by
  have hκ0 : 0 < κ := by linarith
  have hb0 : 0 ≤ 1 - 4 / κ := by rw [sub_nonneg, div_le_one hκ0]; linarith
  have hnb : 0 ≤ ‖z‖ ^ (1 - 4 / κ) := Real.rpow_nonneg (norm_nonneg _) _
  have harg0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.2 hzi
  have hargπ : Complex.arg z ≤ π := Complex.arg_le_pi z
  have hα0 : 0 ≤ 2 * π / κ := by positivity
  have hα2 : 2 * π / κ ≤ π / 2 := by
    rw [div_le_div_iff₀ hκ0 (by norm_num)]; nlinarith [Real.pi_pos]
  rw [hPos_eq hz]
  constructor
  · rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (sin_ge_of_mem hα0 hα2 ?_ ?_) hnb
    · nlinarith
    · have : (1 - 4 / κ) * Complex.arg z ≤ (1 - 4 / κ) * π := mul_le_mul_of_nonneg_left hargπ hb0
      have e : (1 - 4 / κ) * π + 2 * π / κ = π - 2 * π / κ := by field_simp; ring
      linarith
  · exact mul_le_of_le_one_right hnb (Real.sin_le_one _)

/-! ### The exit bound at a fixed taming level -/

/-- The exit set `{|z| ≥ 1} ∪ {Im z ≤ c}`. -/
def exitSetOne (c : ℝ) : Set ℂ := {z | 1 ≤ ‖z‖} ∪ {z | z.im ≤ c}

theorem isClosed_exitSetOne (c : ℝ) : IsClosed (exitSetOne c) :=
  (isClosed_le continuous_const continuous_norm).union
    (isClosed_le Complex.continuous_im continuous_const)

/-- The region `{|z| ≤ 1, Im z ≥ c}`. -/
def regOne (c : ℝ) : Set ℂ := {z | ‖z‖ ≤ 1 ∧ c ≤ z.im}

theorem isClosed_regOne (c : ℝ) : IsClosed (regOne c) :=
  (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_im)

/-- The exit time from `{|z| < 1, Im z > c}` of the `c`-tamed one-point flow, capped at `T`. -/
def exitTimeOne {Ω : Type*} (κ c : ℝ) (a : ℂ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  hittingBtwn (fun t ω => tamedZ (drive κ B ω) c a t) (exitSetOne c) 0 T ω

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The exit bound at level `c`.** For `κ > 4`, `|a| < 1`, `0 < c < Im a`, `T > 0`, the `c`-tamed
flow from `a` is still above height `c` at its exit time from `{|z| < 1, Im z > c}` (capped at `T`)
with probability at most `1/(κT) + |a|^b / sin(2π/κ)`. -/
theorem prob_exit_high_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 4 < κ) {a : ℂ} {c : ℝ} (hc : 0 < c)
    (hca : c < a.im) (ha1 : ‖a‖ < 1) (T : ℝ≥0) (hT : 0 < T) :
    P {ω | B 0 ω = 0 ∧ c < (tamedZ (drive κ B ω) c a (exitTimeOne κ c a B T ω)).im}
      ≤ ENNReal.ofReal (1 / (κ * T)) +
        ENNReal.ofReal (‖a‖ ^ (1 - 4 / κ) / Real.sin (2 * π / κ)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hκ0 : 0 < κ := by linarith
  set e : ℂ := -((Real.sqrt κ : ℝ) : ℂ) with he
  set 𝓕 := NonSwallow.bmFilt hBm with h𝓕
  set U : ℝ≥0 → Ω → ℂ := fun t ω => tamedZ (drive κ B ω) c a t with hUdef
  have hU : ∀ ω (t : ℝ≥0),
      U t ω = a + (∫ r in (0 : ℝ)..t, tamedZField c (U r.toNNReal ω)) + B t ω • e :=
    fun ω t => NonSwallow.tamedZ_integralEq hBc hc κ a ω t
  have hbM : ∀ x, ‖tamedZField c x‖ ≤ 2 / c := norm_tamedZField_le hc
  have hb := NonSwallow.lipschitz_tamedZField hc
  have hUc : ∀ ω, Continuous (U · ω) :=
    Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  have hUm : ∀ t, Measurable[𝓕 t] (U t) :=
    Dynkin.measurable_of_integralEq 𝓕 (NonSwallow.bmFilt_adapted hBm) hBc hb hbM hU hUc
  set τ : Ω → ℝ≥0 := exitTimeOne κ c a B T with hτdef
  have hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUm hUc (isClosed_exitSetOne c) T
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hB0 := hB.eval_zero_ae_eq_zero
  have hU0' : ∀ ω, B 0 ω = 0 → U 0 ω = a := by
    intro ω hω; rw [hU ω 0]; simp [hω]
  have hU0 : ∀ᵐ ω ∂P, U 0 ω = a := by
    filter_upwards [hB0] with ω hω using hU0' ω hω
  have haR : a ∈ regOne c := ⟨ha1.le, hca.le⟩
  -- the path stays in the closed region up to `τ`
  have hK : ∀ ω, B 0 ω = 0 → ∀ t ≤ τ ω, U t ω ∈ regOne c := by
    intro ω hω
    refine NonSwallow.mem_of_le_of_forall_lt (isClosed_regOne c) (hUc ω) ?_ ?_
    · rw [hU0' ω hω]; exact haR
    · intro t ht
      have hn := notMem_of_lt_hittingBtwn ht zero_le
      simp only [exitSetOne, mem_union, mem_ofPred_eq, not_or, not_le] at hn
      exact ⟨hn.1.le, hn.2.le⟩
  have hKim : ∀ ω, B 0 ω = 0 → ∀ t ≤ τ ω, 0 < (U t ω).im := fun ω hω t ht =>
    hc.trans_le (hK ω hω t ht).2
  -- measurability
  have hτm : Measurable τ := by
    refine measurable_of_Iic fun x => ?_
    have h := 𝓕.le x _ (hτ x)
    have e : τ ⁻¹' Iic x = {ω | ((τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (x : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_preimage, mem_Iic]; exact WithTop.coe_le_coe.symm
    rw [e]; exact h
  have hUj : Measurable (Function.uncurry U) :=
    measurable_uncurry_of_continuous_of_measurable hUc fun t => (hUm t).mono (𝓕.le t) le_rfl
  have hUτm : Measurable fun ω => U (τ ω) ω := hUj.comp (hτm.prodMk measurable_id)
  have hτr : Measurable fun ω => ((τ ω : ℝ≥0) : ℝ) := measurable_coe_nnreal_real.comp hτm
  -- generator integrals along the path
  have hGint : ∀ {F : ℂ → ℝ} (hF : ContDiff ℝ 3 F) {g : ℝ} ,
      (∀ z ∈ regOne c, g ≤ dynkinGen (tamedZField c) e F z) → ∀ ω, B 0 ω = 0 →
      g * (τ ω : ℝ) ≤ ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F (U r.toNNReal ω) := by
    intro F hF g hg ω hω
    have hGc : Continuous fun r : ℝ => dynkinGen (tamedZField c) e F (U r.toNNReal ω) :=
      (Dynkin.continuous_dynkinGen hF hb.continuous e).comp ((hUc ω).comp continuous_real_toNNReal)
    have hmono := intervalIntegral.integral_mono_on (NNReal.coe_nonneg (τ ω))
      (continuous_const.intervalIntegrable (μ := volume) (u := fun _ => g) _ _)
      (hGc.intervalIntegrable (μ := volume) _ _)
      (fun r hr => hg _ (hK ω hω _ (Real.toNNReal_le_iff_le_coe.2 hr.2)))
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    linarith
  have hGint' : ∀ {F : ℂ → ℝ} (hF : ContDiff ℝ 3 F) {g : ℝ},
      (∀ z ∈ regOne c, dynkinGen (tamedZField c) e F z ≤ g) → ∀ ω, B 0 ω = 0 →
      ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F (U r.toNNReal ω) ≤ g * (τ ω : ℝ) := by
    intro F hF g hg ω hω
    have hGc : Continuous fun r : ℝ => dynkinGen (tamedZField c) e F (U r.toNNReal ω) :=
      (Dynkin.continuous_dynkinGen hF hb.continuous e).comp ((hUc ω).comp continuous_real_toNNReal)
    have hmono := intervalIntegral.integral_mono_on (NNReal.coe_nonneg (τ ω))
      (hGc.intervalIntegrable (μ := volume) _ _)
      (continuous_const.intervalIntegrable (μ := volume) (u := fun _ => g) _ _)
      (fun r hr => hg _ (hK ω hω _ (Real.toNNReal_le_iff_le_coe.2 hr.2)))
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    linarith
  have hτint : Integrable (fun ω => ((τ ω : ℝ≥0) : ℝ)) P :=
    Integrable.of_bound hτr.aestronglyMeasurable T (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]; exact_mod_cast hτT ω)
  have hT0 : (0 : ℝ) < T := hT
  -- Dynkin for `(Re z)²`: `κ E τ ≤ 1`
  obtain ⟨F₁, C₁, hF₁, hF₁C, hF₁V⟩ := exists_cutoff_eq hc (G := Collision.sqRe)
    (fun z _ => Collision.contDiff_sqRe.contDiffAt)
  obtain ⟨hint1, hzero1⟩ := NonSwallow.dynkin_stopped hB hBc 𝓕 (NonSwallow.bmFilt_adapted hBm)
    (NonSwallow.bmFilt_le_past hBm) hb hbM hU hF₁ (fun x => (hF₁C x).2) (fun x => (hF₁C x).1)
    hU0 hτ T hτT
  have hF₁val : ∀ z ∈ regOne c, F₁ z = z.re ^ 2 := fun z hz => (hF₁V z hz.1 hz.2).eq_of_nhds
  have hgen1 : ∀ z ∈ regOne c, κ ≤ dynkinGen (tamedZField c) e F₁ z := by
    intro z hz
    have hz0 : 0 < z.im := hc.trans_le hz.2
    rw [NonSwallow.dynkinGen_congr (hF₁V z hz.1 hz.2), dynkinGen_sqRe_tamed hκ0.le hz.2 hz0]
    have : 0 ≤ 4 * z.re ^ 2 / (z.re ^ 2 + z.im ^ 2) := by positivity
    linarith
  have hle1 : ∀ᵐ ω ∂P, κ * (τ ω : ℝ) ≤ 1 - (F₁ (U (τ ω) ω) - F₁ a
      - ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F₁ (U r.toNNReal ω)) := by
    filter_upwards [hB0] with ω hω
    have h1 := hGint hF₁ hgen1 ω hω
    have hmem := hK ω hω _ le_rfl
    have h2 : F₁ (U (τ ω) ω) ≤ 1 := by
      rw [hF₁val _ hmem]
      have h3 : |(U (τ ω) ω).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hmem.1
      have := sq_abs (U (τ ω) ω).re
      nlinarith [abs_nonneg (U (τ ω) ω).re]
    have h3 : 0 ≤ F₁ a := by rw [hF₁val a haR]; positivity
    linarith
  have hEτ : κ * ∫ ω, ((τ ω : ℝ≥0) : ℝ) ∂P ≤ 1 := by
    have := integral_mono_ae (hτint.const_mul κ) ((integrable_const 1).sub hint1) hle1
    simp only [Pi.sub_apply] at this
    rw [integral_const_mul, integral_sub (integrable_const 1) hint1, hzero1] at this
    simpa using this
  have hP1 : P {ω | (T : ℝ) ≤ (τ ω : ℝ)} ≤ ENNReal.ofReal (1 / (κ * T)) := by
    have hsub : {ω | (T : ℝ) ≤ (τ ω : ℝ)} ⊆
        {ω | ENNReal.ofReal T ≤ ENNReal.ofReal ((τ ω : ℝ))} := fun ω hω =>
      ENNReal.ofReal_le_ofReal hω
    refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
      (ENNReal.measurable_ofReal.comp hτr).aemeasurable (by simpa using hT.ne')
      ENNReal.ofReal_ne_top).trans ?_)
    simp only [Function.comp_apply]
    rw [← ofReal_integral_eq_lintegral_ofReal hτint (Eventually.of_forall fun ω =>
      NNReal.coe_nonneg _), ← ENNReal.ofReal_div_of_pos hT0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff₀ hT0 (by positivity)]
    nlinarith [hEτ, hT0]
  -- Dynkin for `h`: `E h(Z_τ) = h(a)`
  obtain ⟨F₂, C₂, hF₂, hF₂C, hF₂V⟩ := exists_cutoff_eq hc (G := hPos κ)
    (fun z hz => contDiffAt_hPos κ (mem_slitPlane_of_im_pos' hz) 3)
  obtain ⟨hint2, hzero2⟩ := NonSwallow.dynkin_stopped hB hBc 𝓕 (NonSwallow.bmFilt_adapted hBm)
    (NonSwallow.bmFilt_le_past hBm) hb hbM hU hF₂ (fun x => (hF₂C x).2) (fun x => (hF₂C x).1)
    hU0 hτ T hτT
  have hF₂val : ∀ z ∈ regOne c, F₂ z = hPos κ z := fun z hz => (hF₂V z hz.1 hz.2).eq_of_nhds
  have hgen2 : ∀ z ∈ regOne c, dynkinGen (tamedZField c) e F₂ z = 0 := fun z hz => by
    rw [NonSwallow.dynkinGen_congr (hF₂V z hz.1 hz.2), dynkinGen_hPos hκ0 hz.2 (hc.trans_le hz.2)]
  have hint0 : ∀ ω, B 0 ω = 0 →
      ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F₂ (U r.toNNReal ω) = 0 := fun ω hω =>
    le_antisymm (by simpa using hGint' hF₂ (g := 0) (fun z hz => (hgen2 z hz).le) ω hω)
      (by simpa using hGint hF₂ (g := 0) (fun z hz => (hgen2 z hz).ge) ω hω)
  have hF₂Ui : Integrable (fun ω => F₂ (U (τ ω) ω)) P :=
    ItoLite.integrable_of_bound_abs (hF₂.continuous.measurable.comp hUτm).stronglyMeasurable
      fun ω => (hF₂C _).1
  have hEF2 : ∫ ω, F₂ (U (τ ω) ω) ∂P = F₂ a := by
    have hae : (fun ω => F₂ (U (τ ω) ω) - F₂ a
        - ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F₂ (U r.toNNReal ω)) =ᵐ[P]
        fun ω => F₂ (U (τ ω) ω) - F₂ a := by
      filter_upwards [hB0] with ω hω
      rw [hint0 ω hω, sub_zero]
    rw [integral_congr_ae hae, integral_sub hF₂Ui (integrable_const _), integral_const] at hzero2
    simp at hzero2
    linarith
  have ha0 : a ≠ 0 := fun h => by simp [h] at hca; linarith
  have hsin : 0 < Real.sin (2 * π / κ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ hκ0]; nlinarith [Real.pi_pos]
  have hF₂nn : 0 ≤ᵐ[P] fun ω => F₂ (U (τ ω) ω) := by
    filter_upwards [hB0] with ω hω
    have hmem := hK ω hω _ le_rfl
    have hne : U (τ ω) ω ≠ 0 := fun h => by have := hKim ω hω _ le_rfl; simp [h] at this
    rw [Pi.zero_apply, hF₂val _ hmem]
    exact le_trans (by positivity) (hPos_bounds hκ hne (hKim ω hω _ le_rfl).le).1
  have hP2 : P {ω | B 0 ω = 0 ∧ 1 ≤ ‖U (τ ω) ω‖} ≤
      ENNReal.ofReal (‖a‖ ^ (1 - 4 / κ) / Real.sin (2 * π / κ)) := by
    have hsub : {ω | B 0 ω = 0 ∧ 1 ≤ ‖U (τ ω) ω‖} ⊆
        {ω | ENNReal.ofReal (Real.sin (2 * π / κ)) ≤ ENNReal.ofReal (F₂ (U (τ ω) ω))} := by
      rintro ω ⟨hω, h1⟩
      refine ENNReal.ofReal_le_ofReal ?_
      have hmem := hK ω hω _ le_rfl
      have hne : U (τ ω) ω ≠ 0 := fun h => by
        rw [h, norm_zero] at h1; linarith
      rw [hF₂val _ hmem]
      refine le_trans ?_ (hPos_bounds hκ hne (hKim ω hω _ le_rfl).le).1
      have hb0 : 0 ≤ 1 - 4 / κ := by rw [sub_nonneg, div_le_one hκ0]; linarith
      exact le_mul_of_one_le_right hsin.le (Real.one_le_rpow h1 hb0)
    refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
      (ENNReal.measurable_ofReal.comp (hF₂.continuous.measurable.comp hUτm)).aemeasurable
      (by simpa using hsin) ENNReal.ofReal_ne_top).trans ?_)
    simp only [Function.comp_apply]
    rw [← ofReal_integral_eq_lintegral_ofReal hF₂Ui hF₂nn, hEF2,
      ← ENNReal.ofReal_div_of_pos hsin]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hsin.le)
    rw [hF₂val a haR]
    exact (hPos_bounds hκ ha0 (hc.le.trans hca.le)).2
  -- the high exits are slow or far
  have hsub : {ω | B 0 ω = 0 ∧ c < (tamedZ (drive κ B ω) c a (exitTimeOne κ c a B T ω)).im} ⊆
      {ω | (T : ℝ) ≤ (τ ω : ℝ)} ∪ {ω | B 0 ω = 0 ∧ 1 ≤ ‖U (τ ω) ω‖} := by
    rintro ω ⟨hω, hhigh⟩
    by_cases hτlt : τ ω < T
    · right
      refine ⟨hω, ?_⟩
      obtain ⟨j, hj, hjE⟩ := (hittingBtwn_lt_iff T le_rfl).1 hτlt
      have hmem := NonSwallow.hittingBtwn_mem_of_isClosed (isClosed_exitSetOne c) (hUc ω)
        ⟨j, Ico_subset_Icc_self hj, hjE⟩
      rcases hmem with h | h
      · exact h
      · exact absurd h (not_le.2 hhigh)
    · left
      exact_mod_cast not_lt.1 hτlt
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  exact add_le_add hP1 hP2

/-- Measurability of the tamed flow at its exit time. -/
theorem measurable_tamedZ_exitTimeOne (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {c : ℝ} (hc : 0 < c) (a : ℂ) (T : ℝ≥0) :
    Measurable fun ω => tamedZ (drive κ B ω) c a (exitTimeOne κ c a B T ω) := by
  set e : ℂ := -((Real.sqrt κ : ℝ) : ℂ) with he
  set 𝓕 := NonSwallow.bmFilt hBm with h𝓕
  set U : ℝ≥0 → Ω → ℂ := fun t ω => tamedZ (drive κ B ω) c a t with hUdef
  have hU : ∀ ω (t : ℝ≥0),
      U t ω = a + (∫ r in (0 : ℝ)..t, tamedZField c (U r.toNNReal ω)) + B t ω • e :=
    fun ω t => NonSwallow.tamedZ_integralEq hBc hc κ a ω t
  have hbM : ∀ x, ‖tamedZField c x‖ ≤ 2 / c := norm_tamedZField_le hc
  have hb := NonSwallow.lipschitz_tamedZField hc
  have hUc : ∀ ω, Continuous (U · ω) :=
    Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  have hUm : ∀ t, Measurable[𝓕 t] (U t) :=
    Dynkin.measurable_of_integralEq 𝓕 (NonSwallow.bmFilt_adapted hBm) hBc hb hbM hU hUc
  have hτ : IsStoppingTime 𝓕 (fun ω => (exitTimeOne κ c a B T ω : WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUm hUc (isClosed_exitSetOne c) T
  have hτm : Measurable (exitTimeOne κ c a B T) := by
    refine measurable_of_Iic fun x => ?_
    have h := 𝓕.le x _ (hτ x)
    have e : exitTimeOne κ c a B T ⁻¹' Iic x =
        {ω | ((exitTimeOne κ c a B T ω : ℝ≥0) : WithTop ℝ≥0) ≤ (x : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_preimage, mem_Iic]; exact WithTop.coe_le_coe.symm
    rw [e]; exact h
  have hUj : Measurable (Function.uncurry U) :=
    measurable_uncurry_of_continuous_of_measurable hUc fun t => (hUm t).mono (𝓕.le t) le_rfl
  exact hUj.comp (hτm.prodMk measurable_id)

/-- **Alive points stay high.** If `a ∉ K_T`, there is `m > 0` such that for every taming level
`0 < c ≤ m` the `c`-tamed flow coincides with the true flow on `[0,T]` and stays at height `≥ m`. -/
theorem exists_le_im_tamedZ_of_notMem {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {a : ℂ} (ha : a ∈ H) (haK : a ∉ fwdHull W T) :
    ∃ m > (0 : ℝ), ∀ c, 0 < c → c ≤ m → ∀ t ∈ Icc (0 : ℝ) T, m ≤ (tamedZ W c a t).im := by
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT ha haK
  obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT)
    (Complex.continuous_im.comp_continuousOn hu.1)
  have hm : 0 < (u s0).im := FwdClock.sol_im_pos hW ha hu hs0
  have hmin' : ∀ t ∈ Icc (0 : ℝ) T, (u s0).im ≤ (u t).im := fun t ht => by
    simpa using isMinOn_iff.1 hmin t ht
  refine ⟨(u s0).im, hm, fun c hc hcm t ht => ?_⟩
  have heq := tamedZ_eq_of_isForwardSol hW hc hT hu (fun t ht => hcm.trans (hmin' t ht))
  rw [heq t ht]
  exact hmin' t ht

/-- **[RS05, Lemma 6.5], quantitative positive half**: for `κ > 4`, `a ∈ ℍ`, `|a| < 1`, `T > 0`,
`P(a ∉ K_T) ≤ 1/(κT) + |a|^b / sin(2π/κ)`, `b = 1 − 4/κ` (for a version of `B` with continuous
paths). -/
theorem prob_notMem_fwdHull_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 4 < κ) {a : ℂ} (ha : a ∈ H)
    (ha1 : ‖a‖ < 1) (T : ℝ≥0) (hT : 0 < T) :
    P {ω | B 0 ω = 0 ∧ a ∉ fwdHull (drive κ B ω) T}
      ≤ ENNReal.ofReal (1 / (κ * T)) +
        ENNReal.ofReal (‖a‖ ^ (1 - 4 / κ) / Real.sin (2 * π / κ)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have ha0 : 0 < a.im := ha
  set c : ℕ → ℝ := fun n => a.im / ((n : ℝ) + 2) with hcdef
  have hc : ∀ n, 0 < c n := fun n => by positivity
  have hca : ∀ n, c n < a.im := fun n => by
    rw [hcdef, div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set X : Set Ω := {ω | B 0 ω = 0 ∧ a ∉ fwdHull (drive κ B ω) T} with hX
  set D : ℕ → Set Ω := fun n => X ∩
    {ω | (tamedZ (drive κ B ω) (c n) a (exitTimeOne κ (c n) a B T ω)).im ≤ c n} with hD
  have hDm : ∀ n, MeasurableSet (D n) := fun n =>
    (((hBm 0) (measurableSet_singleton 0)).inter
      (measurableSet_mem_fwdHull_drive hBc κ T.2 (fun r _ => hBm r) a).compl).inter
      (measurableSet_le (Complex.measurable_im.comp
        (measurable_tamedZ_exitTimeOne hBm hBc κ (hc n) a T)) measurable_const)
  set S : ℕ → Set Ω := fun n => ⋃ k ≥ n, D k with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hDm k
  have hSanti : Antitone S := fun n m hnm ω hω => by
    simp only [hS, mem_iUnion] at hω ⊢
    obtain ⟨k, hk, hkω⟩ := hω
    exact ⟨k, hnm.trans hk, hkω⟩
  have hSempty : (⋂ n, S n) = ∅ := by
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    simp only [hS, mem_iInter, mem_iUnion] at hω
    obtain ⟨k0, hk0, hDk0⟩ := hω 0
    obtain ⟨hB0ω, haK⟩ := hDk0.1
    have hW : Continuous (drive κ B ω) := drive_continuous (hBc ω)
    obtain ⟨m, hm, hmc⟩ := exists_le_im_tamedZ_of_notMem hW T.2 ha haK
    -- `c n → 0`, so eventually `c n < m`
    obtain ⟨N, hN⟩ : ∃ N : ℕ, c N < m := by
      obtain ⟨N, hN⟩ := exists_nat_gt (a.im / m)
      refine ⟨N, ?_⟩
      rw [hcdef, div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hm] at hN
      nlinarith
    obtain ⟨k, hk, hDk⟩ := hω N
    have hck : c k < m := lt_of_le_of_lt (by
      rw [hcdef]; exact div_le_div_of_nonneg_left ha0.le (by positivity) (by
        have : (N : ℝ) ≤ k := by exact_mod_cast hk
        linarith)) hN
    have hτT : (exitTimeOne κ (c k) a B T ω : ℝ) ∈ Icc (0 : ℝ) T :=
      ⟨NNReal.coe_nonneg _, by
        have h : exitTimeOne κ (c k) a B T ω ≤ T := hittingBtwn_le (n := (0 : ℝ≥0)) ω
        exact_mod_cast h⟩
    have := hmc (c k) (hc k) hck.le _ hτT
    exact absurd hDk.2 (not_le.2 (hck.trans_le this))
  have htend : Tendsto (fun n => P (S n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) (fun n => (hSm n).nullMeasurableSet) hSanti
      ⟨0, measure_ne_top P _⟩
    rwa [hSempty, measure_empty] at h
  have hle : ∀ n, P X ≤ (ENNReal.ofReal (1 / (κ * T)) +
      ENNReal.ofReal (‖a‖ ^ (1 - 4 / κ) / Real.sin (2 * π / κ))) + P (S n) := by
    intro n
    have hsub : X ⊆ {ω | B 0 ω = 0 ∧
        c n < (tamedZ (drive κ B ω) (c n) a (exitTimeOne κ (c n) a B T ω)).im} ∪ S n := by
      intro ω hω
      by_cases hhigh : c n < (tamedZ (drive κ B ω) (c n) a (exitTimeOne κ (c n) a B T ω)).im
      · exact Or.inl ⟨hω.1, hhigh⟩
      · exact Or.inr (mem_iUnion₂.2 ⟨n, le_rfl, hω, not_lt.1 hhigh⟩)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    gcongr
    exact prob_exit_high_le hB hBm hBc hκ (hc n) (hca n) ha1 T hT
  have hlim : Tendsto (fun n => (ENNReal.ofReal (1 / (κ * T)) +
      ENNReal.ofReal (‖a‖ ^ (1 - 4 / κ) / Real.sin (2 * π / κ))) + P (S n)) atTop
      (𝓝 ((ENNReal.ofReal (1 / (κ * T)) +
        ENNReal.ofReal (‖a‖ ^ (1 - 4 / κ) / Real.sin (2 * π / κ))) + 0)) :=
    tendsto_const_nhds.add htend
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hle

/-- **Points near the origin are swallowed with probability `≥ 1/2`** (`κ > 4`): if `a ∈ ℍ`,
`|a| < 1` and `|a|^{1−4/κ} ≤ sin(2π/κ)/4`, then `P(a ∈ K_{4/κ}) ≥ 1/2`. -/
theorem half_le_measure_mem_fwdHull (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 4 < κ) {a : ℂ}
    (ha : a ∈ H) (ha1 : ‖a‖ < 1) (hsmall : ‖a‖ ^ (1 - 4 / κ) ≤ Real.sin (2 * π / κ) / 4) :
    1 / 2 ≤ P {ω | a ∈ fwdHull (drive κ B ω) (4 / κ)} := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ0 : 0 < κ := by linarith
  obtain ⟨B'', hB''m, hB''c, hB''0, hB''br, hB''eq⟩ := exists_good_version0 hB
  set T : ℝ≥0 := (4 / κ).toNNReal with hTdef
  have hTr : (T : ℝ) = 4 / κ := Real.coe_toNNReal _ (by positivity)
  have hT : 0 < T := by rw [← NNReal.coe_pos, hTr]; positivity
  have hsin : 0 < Real.sin (2 * π / κ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ hκ0]; nlinarith [Real.pi_pos]
  have hbound := prob_notMem_fwdHull_le hB''br.toIsPreBrownianReal hB''m hB''c hκ ha ha1 T hT
  rw [hTr] at hbound
  have h1 : ENNReal.ofReal (1 / (κ * (4 / κ))) = 1 / 4 := by
    rw [show κ * (4 / κ) = 4 by field_simp, ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  have h2 : ENNReal.ofReal (‖a‖ ^ (1 - 4 / κ) / Real.sin (2 * π / κ)) ≤ 1 / 4 := by
    rw [show (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hsin]; linarith
  have hnot : P {ω | a ∉ fwdHull (drive κ B'' ω) (4 / κ)} ≤ 1 / 2 := by
    have e : {ω | a ∉ fwdHull (drive κ B'' ω) (4 / κ)} =
        {ω | B'' 0 ω = 0 ∧ a ∉ fwdHull (drive κ B'' ω) (4 / κ)} := by
      ext ω; simp [hB''0 ω]
    rw [e]
    refine hbound.trans ?_
    rw [h1]
    calc (1 / 4 : ℝ≥0∞) + ENNReal.ofReal (‖a‖ ^ (1 - 4 / κ) / Real.sin (2 * π / κ))
        ≤ 1 / 4 + 1 / 4 := by gcongr
      _ = 1 / 2 := by rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 1 = 2 by norm_num,
            ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
  have hm : MeasurableSet {ω | a ∈ fwdHull (drive κ B'' ω) (4 / κ)} :=
    measurableSet_mem_fwdHull_drive hB''c κ (by positivity) (fun r _ => hB''m r) a
  have hcompl : P {ω | a ∈ fwdHull (drive κ B'' ω) (4 / κ)} =
      1 - P {ω | a ∉ fwdHull (drive κ B'' ω) (4 / κ)} := by
    have e : {ω | a ∉ fwdHull (drive κ B'' ω) (4 / κ)} =
        {ω | a ∈ fwdHull (drive κ B'' ω) (4 / κ)}ᶜ := by ext ω; simp
    rw [e, prob_compl_eq_one_sub hm, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  have hcongr : P {ω | a ∈ fwdHull (drive κ B ω) (4 / κ)} =
      P {ω | a ∈ fwdHull (drive κ B'' ω) (4 / κ)} := by
    refine measure_congr (hB''eq.mono fun ω h => ?_)
    have hdr : drive κ B ω = drive κ B'' ω := funext fun s => by simp [drive, h]
    change (a ∈ fwdHull (drive κ B ω) (4 / κ)) = (a ∈ fwdHull (drive κ B'' ω) (4 / κ))
    rw [hdr]
  rw [hcongr, hcompl]
  calc (1 / 2 : ℝ≥0∞) = 1 - 1 / 2 := by
        rw [one_div, ENNReal.one_sub_inv_two]
    _ ≤ 1 - P {ω | a ∉ fwdHull (drive κ B'' ω) (4 / κ)} := tsub_le_tsub_left hnot 1

end Prob

end InteractingSLE
