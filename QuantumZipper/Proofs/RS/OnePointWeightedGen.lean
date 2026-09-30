import QuantumZipper.Proofs.RS.OnePointMart
import QuantumZipper.Proofs.RS.OnePointBarrier
import QuantumZipper.Proofs.Thm11.NonSwallowing
import QuantumZipper.Proofs.Thm11.FrozenMartingales

/-!
# RS S1-3P, part 1: the one-point state as an additive-noise SDE, and its test functions

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §5, nodes S1-Q / S1-3P (the Girsanov-free fallback,
see the module docstring of `OnePointWeighted.lean` for the choice of route).

This file collects the analytic inputs of the stopping argument:
* `lipschitzWith_opDrift`, `norm_opDrift_le`: the tamed one-point drift `opDrift c` (S1-0) is
  bounded and Lipschitz (the `L`-component is `−(Im (2/proj c Z))²`);
* `opProc` and `opProc_integralEq`: the tamed one-point state
  `U_t = (tamedZ, tamedLogCR)` solves `U_t = (z, log Im z) + ∫₀ᵗ opDrift c (U) + B_t (−√κ, 0)`;
* `dynkinGen_opDrift_angle_at`: the generator identity of S1-0 under a pointwise (`ContDiffAt`)
  hypothesis (the proof is the one of `dynkinGen_opDrift_angle`, which assumes smoothness on all
  of `ℝ × (0,π)`; the barrier is only smooth where the remaining radial time is positive);
* `contDiffAt_barF`, `dynkinGen_barF_le`: the S1-W barrier on the state space is `C³` and has
  nonpositive generator where `Im Z ≥ c` and the remaining radial time is positive;
* `contDiffOn_phiMF`: the S1-M profile on the state space is `C³` on `{Im Z > 0}`.

Own elementary proofs (standard calculus), as allowed by the cost rule of `AGENT_GUIDE.md`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace RS

open FrozenMart FwdHolo

/-! ### The tamed drift is bounded and Lipschitz -/

theorem tamedLField_eq_neg_sq {c : ℝ} (hc : 0 < c) (w : ℂ) :
    tamedLField c w = -((2 / proj c w).im) ^ 2 := by
  have hp : proj c w ≠ 0 := proj_ne_zero_tamed hc w
  have hn : Complex.normSq (proj c w) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have h4 : ‖proj c w‖ ^ 4 = Complex.normSq (proj c w) ^ 2 := by
    rw [← Complex.sq_norm]; ring
  have him : (2 / proj c w).im = -2 * (proj c w).im / Complex.normSq (proj c w) := by
    simp only [Complex.div_im]
    norm_num
    ring
  rw [tamedLField, h4, him]
  field_simp
  ring

theorem abs_im_two_div_proj_le {c : ℝ} (hc : 0 < c) (w : ℂ) : |(2 / proj c w).im| ≤ 2 / c := by
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  exact div_le_div_of_nonneg_left (by norm_num) hc (norm_proj_ge_tamed c w)

theorem lipschitzWith_tamedLField {c : ℝ} (hc : 0 < c) :
    LipschitzWith (Real.toNNReal (16 / c ^ 3)) (tamedLField c) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, dist_eq_norm,
    tamedLField_eq_neg_sq hc, tamedLField_eq_neg_sq hc]
  set a := (2 / proj c x).im
  set b := (2 / proj c y).im
  have ha := abs_im_two_div_proj_le hc x
  have hb := abs_im_two_div_proj_le hc y
  have hab : |a - b| ≤ 4 / c ^ 2 * ‖x - y‖ := by
    have h1 : |a - b| ≤ ‖2 / proj c x - 2 / proj c y‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h2 := norm_two_div_sub_le_tamed hc (norm_proj_ge_tamed c x) (norm_proj_ge_tamed c y)
    have hp : ‖proj c x - proj c y‖ ≤ 2 * ‖x - y‖ := by
      simpa [dist_eq_norm] using (proj_lipschitz c).dist_le_mul x y
    calc |a - b| ≤ 2 * ‖proj c x - proj c y‖ / c ^ 2 := h1.trans h2
      _ ≤ 2 * (2 * ‖x - y‖) / c ^ 2 := by gcongr
      _ = 4 / c ^ 2 * ‖x - y‖ := by ring
  have hsum : |a + b| ≤ 4 / c := by
    calc |a + b| ≤ |a| + |b| := abs_add_le _ _
      _ ≤ 2 / c + 2 / c := add_le_add ha hb
      _ = 4 / c := by ring
  calc |-a ^ 2 - -b ^ 2| = |a - b| * |a + b| := by
        rw [show -a ^ 2 - -b ^ 2 = -((a - b) * (a + b)) by ring, abs_neg, abs_mul]
    _ ≤ (4 / c ^ 2 * ‖x - y‖) * (4 / c) :=
        mul_le_mul hab hsum (abs_nonneg _) (by positivity)
    _ = 16 / c ^ 3 * ‖x - y‖ := by field_simp; ring

theorem norm_opDrift_le {c : ℝ} (hc : 0 < c) (x : ℂ × ℝ) : ‖opDrift c x‖ ≤ 2 / c + 4 / c ^ 2 := by
  have h1 : ‖(2 : ℂ) / proj c x.1‖ ≤ 2 / c := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) hc (norm_proj_ge_tamed c x.1)
  have h2 : ‖tamedLField c x.1‖ ≤ 4 / c ^ 2 := by
    rw [tamedLField_eq_neg_sq hc, Real.norm_eq_abs, abs_neg, abs_pow]
    have := abs_im_two_div_proj_le hc x.1
    calc |(2 / proj c x.1).im| ^ 2 ≤ (2 / c) ^ 2 := by gcongr
      _ = 4 / c ^ 2 := by ring
  have hx : opDrift c x = (2 / proj c x.1, tamedLField c x.1) := rfl
  rw [hx, Prod.norm_def]
  refine max_le (h1.trans ?_) (h2.trans ?_) <;> [exact le_add_of_nonneg_right (by positivity);
    exact le_add_of_nonneg_left (by positivity)]

theorem lipschitzWith_opDrift {c : ℝ} (hc : 0 < c) :
    LipschitzWith (max (Real.toNNReal (4 / c ^ 2)) (Real.toNNReal (16 / c ^ 3))) (opDrift c) := by
  have h1 : LipschitzWith (Real.toNNReal (4 / c ^ 2)) (fun x : ℂ × ℝ => 2 / proj c x.1) := by
    have := (NonSwallow.lipschitz_tamedZField hc).comp (LipschitzWith.prod_fst (α := ℂ) (β := ℝ))
    rw [mul_one] at this
    exact this
  have h2 : LipschitzWith (Real.toNNReal (16 / c ^ 3)) (fun x : ℂ × ℝ => tamedLField c x.1) := by
    have := (lipschitzWith_tamedLField hc).comp (LipschitzWith.prod_fst (α := ℂ) (β := ℝ))
    rw [mul_one] at this
    exact this
  exact h1.prodMk h2

/-! ### The tamed one-point state as an additive-noise SDE -/

/-- The tamed one-point state `(Z̃_t, L̃_t) = (tamedZ, tamedLogCR)` for the SLE driver. -/
def opProc {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (c : ℝ) (z : ℂ) (t : ℝ≥0) (ω : Ω) : ℂ × ℝ :=
  (tamedZ (drive κ B ω) c z t, tamedLogCR (drive κ B ω) c z t)

theorem opProc_integralEq {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω))
    {c : ℝ} (hc : 0 < c) (κ : ℝ) (z : ℂ) (ω : Ω) (t : ℝ≥0) :
    opProc κ B c z t ω = (z, Real.log z.im)
      + (∫ r in (0 : ℝ)..t, opDrift c (opProc κ B c z r.toNNReal ω)) + B t ω • opNoise κ := by
  set W := drive κ B ω with hWdef
  have hW : Continuous W := NonSwallow.continuous_drive_ns hBc κ ω
  have ht : (0 : ℝ) ≤ t := t.coe_nonneg
  have hZc : Continuous fun r : ℝ => tamedZ W c z (r.toNNReal : ℝ) :=
    (FrozenMart.continuous_tamedZ_nnreal hW hc z).comp continuous_real_toNNReal
  set g : ℝ → ℂ × ℝ := fun r => opDrift c (opProc κ B c z r.toNNReal ω) with hg
  have hgc : Continuous g := by
    have : g = fun r => opDrift c (tamedZ W c z (r.toNNReal : ℝ), 0) := rfl
    rw [this]
    exact (continuous_opDrift hc).comp (hZc.prodMk continuous_const)
  have hint : IntervalIntegrable g MeasureTheory.volume 0 t := hgc.intervalIntegrable _ _
  have h1 : (∫ r in (0 : ℝ)..t, g r).1 = ∫ r in (0 : ℝ)..t, (g r).1 := by
    have := (ContinuousLinearMap.fst ℝ ℂ ℝ).intervalIntegral_comp_comm hint
    simp only [ContinuousLinearMap.coe_fst'] at this
    exact this.symm
  have h2 : (∫ r in (0 : ℝ)..t, g r).2 = ∫ r in (0 : ℝ)..t, (g r).2 := by
    have := (ContinuousLinearMap.snd ℝ ℂ ℝ).intervalIntegral_comp_comm hint
    simp only [ContinuousLinearMap.coe_snd'] at this
    exact this.symm
  refine Prod.ext ?_ ?_
  · simp only [opProc, Prod.fst_add, Prod.smul_fst, opNoise, h1]
    rw [NonSwallow.tamedZ_integralEq hBc hc κ z ω t]
    simp only [hg, opDrift, opProc]
    simp [Complex.real_smul]
    rfl
  · simp only [opProc, Prod.snd_add, Prod.smul_snd, opNoise, h2, smul_zero, add_zero]
    rw [tamedLogCR]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    simp only [hg, opDrift, opProc, Real.coe_toNNReal s hs.1, tamedLField]

/-! ### The generator identity of S1-0 at a single point -/

/-- **S1-0, pointwise form.** The identity `dynkinGen_opDrift_angle`, assuming only that `φ` is
`C³` near `(L, arg Z)`. The proof is the one of `dynkinGen_opDrift_angle`. -/
theorem dynkinGen_opDrift_angle_at {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) {φ : ℝ → ℝ → ℝ}
    {Z : ℂ} {L : ℝ} (hΦ : ContDiffAt ℝ 3 (Function.uncurry φ) (L, Complex.arg Z))
    (hZ : c ≤ Z.im) :
    dynkinGen (opDrift c) (opNoise κ) (fun x : ℂ × ℝ => φ x.2 (Complex.arg x.1)) (Z, L)
      = κ * Z.im ^ 2 / ‖Z‖ ^ 4 * radGen κ φ L (Complex.arg Z) := by
  have hZi : 0 < Z.im := hc.trans_le hZ
  have hZ0 : Z ≠ 0 := fun h => by rw [h] at hZi; simp at hZi
  have hF : ContDiffAt ℝ 2 (fun x : ℂ × ℝ => φ x.2 (Complex.arg x.1)) (Z, L) := by
    have hΨ : ContDiffAt ℝ 2 (fun x : ℂ × ℝ => (x.2, Complex.arg x.1)) (Z, L) :=
      contDiffAt_snd.prodMk ((contDiffAt_arg hZi).comp (Z, L) contDiffAt_fst)
    have h := (hΦ.of_le (m := 2) (by norm_num)).comp (Z, L) hΨ
    simpa [Function.comp_def, Function.uncurry] using h
  have hψ : ContDiffAt ℝ 2 (φ L) (Complex.arg Z) := by
    have hsec : ContDiffAt ℝ 3 (fun θ' : ℝ => (L, θ')) (Complex.arg Z) :=
      contDiffAt_const.prodMk contDiffAt_id
    have h := (hΦ.comp (Complex.arg Z) hsec).of_le (m := 2) (by norm_num)
    simpa [Function.comp_def, Function.uncurry] using h
  have hproj : proj c Z = Z := proj_of_le hZ
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line hF]
  have e1 : (fun s : ℝ => (fun x : ℂ × ℝ => φ x.2 (Complex.arg x.1))
        ((Z, L) + s • opDrift c (Z, L)))
      = fun s : ℝ =>
          φ (L + s * (-4 * Z.im ^ 2 / ‖Z‖ ^ 4)) (Complex.arg (Z + s • (2 / Z))) := by
    funext s
    simp only [opDrift, hproj, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul]
  have e2 : (fun s : ℝ => (fun x : ℂ × ℝ => φ x.2 (Complex.arg x.1))
        ((Z, L) + s • opNoise κ))
      = fun s : ℝ => φ L (Complex.arg (Z + s • (((-Real.sqrt κ : ℝ) : ℂ)))) := by
    funext s
    simp only [opNoise, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_zero, add_zero]
  rw [e1, e2, (hasDerivAt_opAngle_line (φ := φ) hZi (hΦ.differentiableAt (by norm_num))).deriv,
    deriv_deriv_opAngle_noise (ψ := φ L) (((-Real.sqrt κ : ℝ) : ℂ)) hZi hψ]
  rw [radGen, im_two_div_div hZ0, im_neg_sqrt_div_sq hZ0 hκ.le, neg_im_sq_neg_sqrt_div hZ0 hκ.le,
    cos_arg_div_sin_arg hZi]
  have hZim : Z.im ≠ 0 := hZi.ne'
  have hn : ‖Z‖ ≠ 0 := norm_ne_zero_iff.mpr hZ0
  have hκ0 : κ ≠ 0 := hκ.ne'
  field_simp
  ring

/-! ### The barrier and the martingale profile on the state space -/

theorem contDiffOn_barW_three {p : ℝ} (hp : 0 < p) : ContDiffOn ℝ 3 (barW p) (Ioi 0) := by
  have hinf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (barW p) (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun ξ hξ => (hasDerivAt_barW hp hξ).differentiableAt.differentiableWithinAt, ?_⟩
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : ℝ => ξ ^ (p - 1)) (Set.Ioi 0) :=
      contDiffOn_id.rpow_const_of_ne fun ξ hξ => hξ.ne'
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : ℝ => Real.exp (-ξ ^ 2 / 2))
        (Set.Ioi 0) := by
      fun_prop
    refine ((h1.mul h2).div_const (barDen p)).congr fun ξ hξ => ?_
    exact (hasDerivAt_barW hp hξ).deriv
  exact hinf.of_le (by simp)

theorem contDiffAt_uncurry_barrier {κ K t₀ L₀ L θ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hσ : 0 < t₀ + κ / 4 * (L - L₀)) (hθ : 0 < Real.sin θ) :
    ContDiffAt ℝ 3 (Function.uncurry (barrier κ K t₀ L₀)) (L, θ) := by
  have hp : 0 < 8 / κ - 1 := by
    rw [sub_pos, lt_div_iff₀ hκ]; linarith
  have hfun : Function.uncurry (barrier κ K t₀ L₀) = fun q : ℝ × ℝ =>
      Real.exp (K * (t₀ + κ / 4 * (q.1 - L₀))) *
        barW (8 / κ - 1) (Real.sin q.2 / Real.sqrt (t₀ + κ / 4 * (q.1 - L₀))) := by
    funext q; rfl
  rw [hfun]
  have hσf : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => t₀ + κ / 4 * (q.1 - L₀)) (L, θ) := by fun_prop
  have hsq : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Real.sqrt (t₀ + κ / 4 * (q.1 - L₀))) (L, θ) :=
    hσf.sqrt hσ.ne'
  have hsin : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Real.sin q.2) (L, θ) := by fun_prop
  have hξ : ContDiffAt ℝ 3
      (fun q : ℝ × ℝ => Real.sin q.2 / Real.sqrt (t₀ + κ / 4 * (q.1 - L₀))) (L, θ) :=
    hsin.div hsq (Real.sqrt_pos.2 hσ).ne'
  have hξpos : 0 < Real.sin θ / Real.sqrt (t₀ + κ / 4 * (L - L₀)) :=
    div_pos hθ (Real.sqrt_pos.2 hσ)
  have hW : ContDiffAt ℝ 3 (barW (8 / κ - 1)) (Real.sin θ / Real.sqrt (t₀ + κ / 4 * (L - L₀))) :=
    (contDiffOn_barW_three hp).contDiffAt (Ioi_mem_nhds hξpos)
  have hexp : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Real.exp (K * (t₀ + κ / 4 * (q.1 - L₀)))) (L, θ) :=
    by fun_prop
  exact hexp.mul (ContDiffAt.comp (g := barW (8 / κ - 1)) (L, θ) hW hξ)

/-- The S1-W barrier as a function of the one-point state `(Z, L)`. -/
def barF (κ K t₀ L₀ : ℝ) (x : ℂ × ℝ) : ℝ := barrier κ K t₀ L₀ x.2 (Complex.arg x.1)

/-- The S1-M profile as a function of the one-point state `(Z, L)`. -/
def phiMF (κ : ℝ) (x : ℂ × ℝ) : ℝ := phiM κ x.2 (Complex.arg x.1)

theorem sin_arg_pos {Z : ℂ} (hZ : 0 < Z.im) : 0 < Real.sin (Complex.arg Z) :=
  Real.sin_pos_of_mem_Ioo (arg_mem_Ioo_of_im_pos hZ)

theorem contDiffAt_barF {κ K t₀ L₀ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {x : ℂ × ℝ}
    (hx : 0 < x.1.im) (hσ : 0 < t₀ + κ / 4 * (x.2 - L₀)) :
    ContDiffAt ℝ 3 (barF κ K t₀ L₀) x := by
  have hΦ := contDiffAt_uncurry_barrier (K := K) (θ := Complex.arg x.1) hκ hκ8 hσ (sin_arg_pos hx)
  have hΨ : ContDiffAt ℝ 3 (fun y : ℂ × ℝ => (y.2, Complex.arg y.1)) x :=
    contDiffAt_snd.prodMk ((contDiffAt_arg hx).comp x contDiffAt_fst)
  have h := hΦ.comp x hΨ
  show ContDiffAt ℝ 3 (fun y : ℂ × ℝ => barrier κ K t₀ L₀ y.2 (Complex.arg y.1)) x
  simpa [Function.comp_def, Function.uncurry] using h

theorem contDiffOn_barF {κ K t₀ L₀ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    ContDiffOn ℝ 3 (barF κ K t₀ L₀) {x | 0 < x.1.im ∧ 0 < t₀ + κ / 4 * (x.2 - L₀)} :=
  fun _ hx => (contDiffAt_barF hκ hκ8 hx.1 hx.2).contDiffWithinAt

theorem contDiffOn_phiMF (κ : ℝ) : ContDiffOn ℝ 3 (phiMF κ) {x | 0 < x.1.im} := by
  intro x hx
  have hmem : (x.2, Complex.arg x.1) ∈ univ ×ˢ Ioo 0 Real.pi :=
    ⟨trivial, arg_mem_Ioo_of_im_pos hx⟩
  have hΦ : ContDiffAt ℝ 3 (Function.uncurry (phiM κ)) (x.2, Complex.arg x.1) :=
    (contDiffOn_uncurry_phiM κ).contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hmem)
  have hΨ : ContDiffAt ℝ 3 (fun y : ℂ × ℝ => (y.2, Complex.arg y.1)) x :=
    contDiffAt_snd.prodMk ((contDiffAt_arg (show 0 < x.1.im from hx)).comp x contDiffAt_fst)
  have h := hΦ.comp x hΨ
  have h' : ContDiffAt ℝ 3 (fun y : ℂ × ℝ => phiM κ y.2 (Complex.arg y.1)) x := by
    simpa [Function.comp_def, Function.uncurry] using h
  exact h'.contDiffWithinAt

/-- **The barrier is a supersolution** of the one-point generator where `Im Z ≥ c` and the
remaining radial time `σ = t₀ + (κ/4)(L − L₀)` is positive (S1-0 and S1-W). -/
theorem dynkinGen_barF_le {κ c K t₀ L₀ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hc : 0 < c)
    (hK : ∀ ξ > 0, -K * barW (8 / κ - 1) ξ + ξ * deriv (barW (8 / κ - 1)) ξ * (ξ ^ 2 - 1) / 2 ≤ 0)
    {x : ℂ × ℝ} (hx : c ≤ x.1.im) (hσ : 0 < t₀ + κ / 4 * (x.2 - L₀)) :
    dynkinGen (opDrift c) (opNoise κ) (barF κ K t₀ L₀) x ≤ 0 := by
  obtain ⟨Z, L⟩ := x
  have hZ : 0 < Z.im := hc.trans_le hx
  have hΦ := contDiffAt_uncurry_barrier (K := K) (θ := Complex.arg Z) hκ hκ8 hσ (sin_arg_pos hZ)
  have h := dynkinGen_opDrift_angle_at hκ hc hΦ hx
  show dynkinGen (opDrift c) (opNoise κ)
    (fun x : ℂ × ℝ => barrier κ K t₀ L₀ x.2 (Complex.arg x.1)) (Z, L) ≤ 0
  rw [h]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (radGen_barrier_le hκ hκ8 hK hσ (arg_mem_Ioo_of_im_pos hZ))

theorem dynkinGen_phiMF {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) {x : ℂ × ℝ} (hx : c ≤ x.1.im) :
    dynkinGen (opDrift c) (opNoise κ) (phiMF κ) x = 0 := by
  obtain ⟨Z, L⟩ := x
  exact dynkinGen_opDrift_phiM hκ hc hx

end RS
end QuantumZipper
