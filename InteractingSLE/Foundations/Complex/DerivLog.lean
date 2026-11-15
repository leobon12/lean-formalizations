import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import QuantumZipper.Proofs.Loewner.ForwardHolo
import QuantumZipper.Proofs.Complex.KoebeBasic
import SupercriticalConformalCovariance.Frozen.IsConformalBijection

/-!
# Derivative lifts `L_ψ` and the coordinate rule (1.4)

Packet GEO-DLOG of `planning/INFRA-GEO.md` (§3 "Complex analysis", §4 phase G1). Specification
`source/ig1-specification.pdf`, p. 2 (the coordinate rule (1.4) and "the chosen analytic logarithm
of `ψ'`") and the frame dictionary FD11.2–FD12.4, pp. 12–17 (Aux. lemma 1).

## Carriers

* `IsDerivLog ψ L D`: `L` is holomorphic on `D` and `exp ∘ L = ψ'` on `D`. The lift is data, as in
  the source ("the chosen analytic logarithm"); the library never chooses it.
* `coordChange χ ψ L h = h ∘ ψ − χ Im L`: the coordinate rule (1.4) on functions.
* The strip `𝒮 = {0 < Im z < 1}` appears literally as `{z : ℂ | 0 < z.im ∧ z.im < 1}`; this is
  definitionally `InteractingSLE.strip` of `Foundations/Harmonic/Strip.lean` (not imported here).
* The explicit strip charts of the frame dictionary: `stripToH q` (`P` of (FD11.5)) with lift
  `derivLogStripToH q`, and `stripQ q` (`Q` of (FD12.3)) with lift `derivLogStripQ q`. These are
  literal formulas, total on `ℂ`; every statement restricts to the strip.

## Main results

* `exists_isDerivLog`: existence on a simply connected domain;
* `IsDerivLog.exists_int_eqOn`: two lifts on a connected domain differ by one `2πin`;
* `IsDerivLog.comp`, `IsDerivLog.invFunOn`: the chain-rule lift and the inverse lift `−L_ψ ∘ ψ⁻¹`;
* `coordChange_coordChange`: coordinate changes compose along the chain-rule lift;
* `isDerivLog_neg_inv` (FD12.1), `neg_derivLog_neg_inv_eq` (FD12.2);
* `isDerivLog_fwdMap`: QuantumZipper's `logDerivFwd W t` is a lift of the Loewner map `f_t` on
  `ℍ \ K_t` (the branch of `log f_t'` vanishing at `t = 0`);
* `isDerivLog_stripToH` (FD11.5), `isDerivLog_stripQ` (FD12.3), `derivLog_comp_stripQ` (FD12.4),
  `neg_inv_comp_stripQ` (`R ∘ Q = P`), `isDerivLog_rotation`, `isDerivLog_rotation_inv` and
  `coordChange_rotation` (FD11.8).

## Proof notes

A continuous logarithm of a holomorphic function is holomorphic
(`differentiableAt_of_continuousAt_of_exp_eq`: locally `L = L(z) + Log(G/G(z))`). Existence then
follows from Mathlib's continuous logarithm on simply connected sets
(`Complex.exists_continuousOn_eqOn_exp_comp`), and `isDerivLog_fwdMap` from QuantumZipper's
`FwdHolo.hasDerivAt_fwdMap` plus a local Lipschitz bound for `logDerivFwd` in `z`
(`norm_logDerivFwd_sub_le`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H)

namespace InteractingSLE

/-! ## Derivative lifts -/

/-- `L` is an analytic logarithm of `ψ'` on `D`: the derivative lift `L_ψ` of the coordinate
rule (1.4), Specification p. 2 ("let `L_ψ` be the chosen analytic logarithm of `ψ'`"). The
choice of `L` is part of the data, as in the source. -/
def IsDerivLog (ψ L : ℂ → ℂ) (D : Set ℂ) : Prop :=
  DifferentiableOn ℂ L D ∧ ∀ z ∈ D, exp (L z) = deriv ψ z

/-- A lift on `D` is a lift on every subset. -/
theorem IsDerivLog.mono {ψ L : ℂ → ℂ} {D E : Set ℂ} (h : IsDerivLog ψ L D) (hED : E ⊆ D) :
    IsDerivLog ψ L E :=
  ⟨h.1.mono hED, fun z hz => h.2 z (hED hz)⟩

/-- A logarithm of a function holomorphic at `z` that is continuous at `z` is holomorphic at `z`:
near `z` it equals `L z + Log (G w / G z)`. -/
theorem differentiableAt_of_continuousAt_of_exp_eq {L G : ℂ → ℂ} {z : ℂ}
    (hL : ContinuousAt L z) (hG : DifferentiableAt ℂ G z)
    (hLG : ∀ᶠ w in 𝓝 z, exp (L w) = G w) : DifferentiableAt ℂ L z := by
  have hGz : G z = exp (L z) := hLG.self_of_nhds.symm
  have hev : L =ᶠ[𝓝 z] fun w => L z + log (G w / G z) := by
    filter_upwards [hL.eventually (Metric.ball_mem_nhds (L z) Real.pi_pos), hLG] with w hw hwG
    have hq : G w / G z = exp (L w - L z) := by rw [exp_sub, hwG, hGz]
    rw [Complex.dist_eq] at hw
    have him := abs_lt.1 (lt_of_le_of_lt (Complex.abs_im_le_norm (L w - L z)) hw)
    rw [hq, log_exp (by linarith [him.1]) (by linarith [him.2])]
    ring
  have hdiff : DifferentiableAt ℂ (fun w => L z + log (G w / G z)) z := by
    refine DifferentiableAt.const_add _ ((hG.div_const _).clog ?_)
    rw [div_self (hGz ▸ exp_ne_zero _)]
    exact one_mem_slitPlane
  exact hdiff.congr_of_eventuallyEq hev

/-- A continuous logarithm, on an open set, of a holomorphic function is holomorphic. -/
theorem differentiableOn_of_continuousOn_of_exp_eq {L G : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hL : ContinuousOn L D) (hG : DifferentiableOn ℂ G D) (hLG : ∀ z ∈ D, exp (L z) = G z) :
    DifferentiableOn ℂ L D := fun _ hz =>
  (differentiableAt_of_continuousAt_of_exp_eq (hL.continuousAt (hD.mem_nhds hz))
    (hG.differentiableAt (hD.mem_nhds hz))
    (eventually_of_mem (hD.mem_nhds hz) hLG)).differentiableWithinAt

/-- Existence of a derivative lift on a simply connected domain (Specification p. 2). -/
theorem exists_isDerivLog {ψ : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D) (hDc : IsSimplyConnected D)
    (hψ : DifferentiableOn ℂ ψ D) (hne : ∀ z ∈ D, deriv ψ z ≠ 0) :
    ∃ L, IsDerivLog ψ L D := by
  have hd : DifferentiableOn ℂ (deriv ψ) D := hψ.deriv hDo
  obtain ⟨L, hLc, hL⟩ := exists_continuousOn_eqOn_exp_comp hDc hDo hd.continuousOn
    (fun ⟨z, hz, hz0⟩ => hne z hz hz0)
  exact ⟨L, differentiableOn_of_continuousOn_of_exp_eq hDo hLc hd (fun z hz => hL hz),
    fun z hz => hL hz⟩

/-- Two lifts on a connected domain differ by one constant `2πin` (Specification p. 2: "a change
by `2πin` changes the actual lifted heights"). -/
theorem IsDerivLog.exists_int_eqOn {ψ L₁ L₂ : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsPreconnected D) (h₁ : IsDerivLog ψ L₁ D) (h₂ : IsDerivLog ψ L₂ D) :
    ∃ n : ℤ, EqOn L₁ (fun z => L₂ z + 2 * π * I * n) D := by
  have hn : ∀ z ∈ D, ∃ n : ℤ, L₁ z = L₂ z + n * (2 * π * I) := fun z hz =>
    exp_eq_exp_iff_exists_int.1 ((h₁.2 z hz).trans (h₂.2 z hz).symm)
  rcases D.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨0, fun z hz => hz.elim⟩
  set f : ℂ → ℝ := fun z => (L₁ z - L₂ z).im / (2 * π) with hf_def
  have hfn : ∀ z ∈ D, ∀ n : ℤ, L₁ z = L₂ z + n * (2 * π * I) → f z = n := by
    intro z _ n hzn
    simp only [hf_def, hzn, add_sub_cancel_left, mul_im, intCast_re, intCast_im, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
    field_simp
    ring
  have hfc : ContinuousOn f D :=
    ((continuous_im.comp_continuousOn (h₁.1.continuousOn.sub h₂.1.continuousOn)).div_const _)
  have hmaps : MapsTo f D (range ((↑) : ℤ → ℝ)) := by
    intro z hz
    obtain ⟨n, hzn⟩ := hn z hz
    exact ⟨n, (hfn z hz n hzn).symm⟩
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  obtain ⟨n₀, hn₀⟩ := hn z₀ hz₀
  refine ⟨n₀, fun z hz => ?_⟩
  obtain ⟨n, hzn⟩ := hn z hz
  have hconst := hDc.constant_of_mapsTo hdisc hfc hmaps hz hz₀
  rw [hfn z hz n hzn, hfn z₀ hz₀ n₀ hn₀, Int.cast_inj] at hconst
  rw [hzn, hconst]
  ring

/-- The **analytic chain-rule lift** (Specification p. 2): `L_{ψ∘φ} = L_ψ ∘ φ + L_φ`. -/
theorem IsDerivLog.comp {ψ φ Lψ Lφ : ℂ → ℂ} {D E : Set ℂ} (hDo : IsOpen D) (hEo : IsOpen E)
    (hψ : DifferentiableOn ℂ ψ E) (hφ : DifferentiableOn ℂ φ D) (hmaps : MapsTo φ D E)
    (hLψ : IsDerivLog ψ Lψ E) (hLφ : IsDerivLog φ Lφ D) :
    IsDerivLog (ψ ∘ φ) (fun z => Lψ (φ z) + Lφ z) D := by
  refine ⟨?_, fun z hz => ?_⟩
  · exact (hLψ.1.comp hφ hmaps).add hLφ.1
  · have hφz : DifferentiableAt ℂ φ z := hφ.differentiableAt (hDo.mem_nhds hz)
    have hψz : DifferentiableAt ℂ ψ (φ z) := hψ.differentiableAt (hEo.mem_nhds (hmaps hz))
    rw [exp_add, hLψ.2 _ (hmaps hz), hLφ.2 z hz, deriv_comp z hψz hφz]

/-- The **inverse lift** (Specification p. 2): `L_{ψ⁻¹} = −L_ψ ∘ ψ⁻¹`. -/
theorem IsDerivLog.invFunOn {ψ L : ℂ → ℂ} {D E : Set ℂ} (hDo : IsOpen D)
    (hψ : IsConformalBijection ψ D E) (hL : IsDerivLog ψ L D) :
    IsDerivLog (Function.invFunOn ψ D) (fun w => -L (Function.invFunOn ψ D w)) E := by
  have key : ∀ w ∈ E, ∃ z ∈ D, Function.invFunOn ψ D w = z ∧
      HasDerivAt (Function.invFunOn ψ D) (deriv ψ z)⁻¹ w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hψ.2.surjOn hw
    exact ⟨z, hz, hψ.2.injOn.leftInvOn_invFunOn hz,
      QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn hDo hψ.1 hψ.2.injOn hz⟩
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨z, hz, hinv, hder⟩ := key w hw
    have hLz : DifferentiableAt ℂ L (Function.invFunOn ψ D w) := by
      rw [hinv]; exact hL.1.differentiableAt (hDo.mem_nhds hz)
    exact (hLz.comp w hder.differentiableAt).neg.differentiableWithinAt
  · obtain ⟨z, hz, hinv, hder⟩ := key w hw
    show exp (-L (Function.invFunOn ψ D w)) = _
    rw [hder.deriv, hinv, exp_neg, hL.2 z hz]

/-! ## The coordinate rule (1.4) -/

/-- The **coordinate rule (1.4)** on functions (harmonic means and boundary data; the
distribution-valued field version belongs to the GFF foundation):
`(D, h) ↦ (D̃, h ∘ ψ − χ Im L_ψ)`, Specification p. 2. -/
def coordChange (χ : ℝ) (ψ L : ℂ → ℂ) (h : ℂ → ℝ) : ℂ → ℝ :=
  fun z => h (ψ z) - χ * (L z).im

/-- Coordinate changes compose along the chain-rule lift (pure algebra). -/
theorem coordChange_coordChange (χ : ℝ) (ψ φ Lψ Lφ : ℂ → ℂ) (h : ℂ → ℝ) :
    coordChange χ φ Lφ (coordChange χ ψ Lψ h) =
      coordChange χ (ψ ∘ φ) (fun z => Lψ (φ z) + Lφ z) h := by
  funext z
  simp only [coordChange, Function.comp_apply, add_im]
  ring

/-! ## Elementary facts about `ℍ` used by the explicit lifts -/

namespace DerivLog

theorem ne_zero_of_mem_H {w : ℂ} (hw : w ∈ H) : w ≠ 0 := fun h => by
  have h' : (0 : ℝ) < w.im := hw
  rw [h, zero_im] at h'
  exact lt_irrefl _ h'

theorem mem_slitPlane_of_mem_H {w : ℂ} (hw : w ∈ H) : w ∈ slitPlane := Or.inr (ne_of_gt hw)

/-- On `ℍ` the principal argument (the imaginary part of `Log`) lies in `(0, π)`. -/
theorem arg_mem_Ioo_of_mem_H {w : ℂ} (hw : w ∈ H) : arg w ∈ Ioo 0 π :=
  ⟨(arg_nonneg_iff.2 (le_of_lt hw)).lt_of_ne fun h => (ne_of_gt hw) (arg_eq_zero_iff.1 h.symm).2,
    arg_lt_pi_iff.2 (Or.inr (ne_of_gt hw))⟩

theorem add_ofReal_mem_H {w : ℂ} (hw : w ∈ H) (c : ℝ) : w + c ∈ H := by
  show 0 < (w + c).im
  rw [add_im, ofReal_im, add_zero]; exact hw

theorem sub_one_mem_H {w : ℂ} (hw : w ∈ H) : w - 1 ∈ H := by
  show 0 < (w - 1).im
  rw [sub_im, one_im, sub_zero]; exact hw

/-- `Log (a / b) = Log a − Log b` for `a, b ∈ ℍ`. -/
theorem log_div_eq_sub_of_mem_H {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) :
    log (a / b) = log a - log b := by
  have h1 := arg_mem_Ioo_of_mem_H ha
  have h2 := arg_mem_Ioo_of_mem_H hb
  have hexp : exp (log a - log b) = a / b := by
    rw [exp_sub, exp_log (ne_zero_of_mem_H ha), exp_log (ne_zero_of_mem_H hb)]
  rw [← hexp, log_exp] <;> simp only [sub_im, log_im] <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `exp(πz) ∈ ℍ` on the strip `{0 < Im z < 1}`. -/
theorem exp_pi_mul_mem_H {z : ℂ} (hz : z ∈ {z : ℂ | 0 < z.im ∧ z.im < 1}) :
    exp (π * z) ∈ H := by
  show 0 < (exp (π * z)).im
  rw [exp_im]
  refine mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]; exact mul_pos Real.pi_pos hz.1
  · simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [Real.pi_pos, hz.2]

theorem hasDerivAt_exp_pi_mul (z : ℂ) :
    HasDerivAt (fun z : ℂ => exp (π * z)) (π * exp (π * z)) z := by
  have := ((hasDerivAt_id z).const_mul (π : ℂ)).cexp
  simpa [mul_comm] using this

theorem exp_log_pi_mul {q : ℝ} (hq : 0 < q) :
    exp (Real.log (π * (q + 1)) : ℂ) = π * (q + 1) := by
  rw [← ofReal_exp, Real.exp_log (by positivity)]; push_cast; ring

/-- The exponential of the strip lifts of (FD11.5) and (FD12.3). -/
theorem exp_lift_strip {q : ℝ} (hq : 0 < q) (z w : ℂ) (hw : w ≠ 0) :
    exp ((Real.log (π * (q + 1)) : ℂ) + π * z - 2 * log w) =
      π * (q + 1) * exp (π * z) / w ^ 2 := by
  rw [exp_sub, exp_add, exp_log_pi_mul hq, show (2 : ℂ) * log w = (2 : ℕ) * log w by norm_num,
    exp_nat_mul, exp_log hw]

/-- Holomorphy of the strip lifts of (FD11.5) and (FD12.3). -/
theorem differentiableAt_lift_strip (q : ℝ) {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z)
    (hs : g z ∈ slitPlane) :
    DifferentiableAt ℂ (fun z : ℂ => (Real.log (π * (q + 1)) : ℂ) + π * z - 2 * log (g z)) z :=
  ((differentiableAt_const _).add (differentiableAt_id.const_mul _)).sub ((hg.clog hs).const_mul 2)

end DerivLog

open DerivLog

/-! ## The infinity-source lift in the half-plane (FD12.1–FD12.2) -/

/-- **(FD12.1)**: `R(z) = −1/z` has the lift `L_R(z) = −2 Log z` on `ℍ`. -/
theorem isDerivLog_neg_inv : IsDerivLog (fun z => -z⁻¹) (fun z => -2 * log z) H := by
  refine ⟨fun z hz =>
    ((differentiableAt_log (mem_slitPlane_of_mem_H hz)).const_mul _).differentiableWithinAt,
    fun z hz => ?_⟩
  have hz0 : z ≠ 0 := ne_zero_of_mem_H hz
  have hder : deriv (fun z : ℂ => -z⁻¹) z = (z ^ 2)⁻¹ := by
    rw [deriv.fun_neg, deriv_inv]; ring
  show exp (-2 * log z) = _
  rw [hder, show -2 * log z = -((2 : ℕ) * log z) by push_cast; ring, exp_neg, exp_nat_mul,
    exp_log hz0]

/-- **(FD12.2)**: the compatible inverse lift of `R` is `2πi − 2 Log w` on `ℍ`. -/
theorem neg_derivLog_neg_inv_eq {w : ℂ} (hw : w ∈ H) :
    -(-2 * log (-w⁻¹)) = 2 * π * I - 2 * log w := by
  have hw0 : w ≠ 0 := ne_zero_of_mem_H hw
  have harg := arg_mem_Ioo_of_mem_H hw
  have hlog : log (-w⁻¹) = π * I - log w := by
    have hexp : exp (π * I - log w) = -w⁻¹ := by
      rw [exp_sub, exp_pi_mul_I, exp_log hw0]; ring
    rw [← hexp, log_exp]
    · simp only [sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, log_im]
      linarith [harg.1, harg.2]
    · simp only [sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, log_im]
      linarith [harg.1, harg.2]
  rw [hlog]; ring

/-! ## The Loewner maps carry the canonical lift -/

open QuantumZipper in
/-- Local Lipschitz bound for `z ↦ logDerivFwd W T z = −∫₀ᵀ 2/f_s(z)² ds` on `ℍ \ K_T`. -/
theorem norm_logDerivFwd_sub_le {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H \ fwdHull W T) :
    ∃ ε > 0, ∃ K : ℝ, ∀ w : ℂ, ‖w - z‖ < ε →
      ‖logDerivFwd W T w - logDerivFwd W T z‖ ≤ ‖w - z‖ * K := by
  obtain ⟨m, hm, C, hC, ε, hε, hloc⟩ := FwdHolo.fwdMap_local hW hT hz
  set K : ℝ := 2 * C / (m / 2 * m ^ 2) + 2 * C / ((m / 2) ^ 2 * m) with hK_def
  have hint : ∀ w, ‖w - z‖ < ε →
      IntervalIntegrable (fun s => 2 / (fwdMap W s w) ^ 2) MeasureTheory.volume 0 T := by
    intro w hw
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    refine continuousOn_const.div
      ((FwdHolo.continuousOn_fwdMap_time hW hT (hloc w hw).1).pow 2)
      (fun s hs => pow_ne_zero 2 fun h => ?_)
    have h1 := ((hloc w hw).2 s hs).2.1
    rw [h, zero_im] at h1; linarith
  have hz' : ‖z - z‖ < ε := by simpa using hε
  refine ⟨ε, hε, K * T, fun w hw => ?_⟩
  have hpt : ∀ s ∈ Set.uIoc (0 : ℝ) T,
      ‖2 / (fwdMap W s w) ^ 2 - 2 / (fwdMap W s z) ^ 2‖ ≤ ‖w - z‖ * K := by
    intro s hs
    rw [uIoc_of_le hT] at hs
    obtain ⟨hd, ha, hb⟩ := (hloc w hw).2 s (Ioc_subset_Icc_self hs)
    set A := fwdMap W s w
    set B := fwdMap W s z
    have hA : m / 2 ≤ ‖A‖ := ha.trans (Complex.im_le_norm A)
    have hB : m ≤ ‖B‖ := hb.trans (Complex.im_le_norm B)
    have hA0 : A ≠ 0 := by intro h; rw [h, norm_zero] at hA; linarith
    have hB0 : B ≠ 0 := by intro h; rw [h, norm_zero] at hB; linarith
    have e : 2 / A ^ 2 - 2 / B ^ 2 =
        2 * (B - A) / (A * B ^ 2) + 2 * (B - A) / (A ^ 2 * B) := by
      field_simp; ring
    have hBA : ‖B - A‖ ≤ ‖w - z‖ * C := by rw [norm_sub_rev]; exact hd
    rw [e]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_two]
    rw [hK_def, mul_add]
    have hm2 : 0 < m / 2 := by linarith
    gcongr ?_ + ?_
    · rw [mul_div_assoc', mul_comm (‖w - z‖) (2 * C), mul_assoc]
      apply div_le_div₀ (by positivity) (by nlinarith [norm_nonneg (w - z)]) (by positivity)
      exact mul_le_mul hA (pow_le_pow_left₀ hm.le hB 2) (by positivity) (by positivity)
    · rw [mul_div_assoc', mul_comm (‖w - z‖) (2 * C), mul_assoc]
      apply div_le_div₀ (by positivity) (by nlinarith [norm_nonneg (w - z)]) (by positivity)
      exact mul_le_mul (pow_le_pow_left₀ hm2.le hA 2) hB hm.le (by positivity)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub (hint w hw) (hint z hz'), sub_zero, abs_of_nonneg hT]
    at hbound
  simp only [logDerivFwd]
  rw [neg_sub_neg, norm_sub_rev, ← mul_assoc]
  exact hbound

open QuantumZipper in
/-- `z ↦ logDerivFwd W T z` is continuous on `ℍ \ K_T`. -/
theorem continuousAt_logDerivFwd {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H \ fwdHull W T) : ContinuousAt (logDerivFwd W T) z := by
  obtain ⟨ε, hε, K, hK⟩ := norm_logDerivFwd_sub_le hW hT hz
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (g := fun w => ‖w - z‖ * K) ?_
  · filter_upwards [Metric.ball_mem_nhds z hε] with w hw
    exact hK w (by rwa [mem_ball, Complex.dist_eq] at hw)
  · have hc : Continuous fun w : ℂ => ‖w - z‖ * K := by fun_prop
    simpa using hc.tendsto z

/-- The Loewner maps carry the canonical lift: `logDerivFwd` (the branch of `log f_t'` vanishing
at `t = 0`, Theorem 1.1's "continuous branch of `log f_t'` initialized at zero") is a derivative
lift of `f_t` on `ℍ \ K_t`. -/
theorem isDerivLog_fwdMap {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsDerivLog (QuantumZipper.fwdMap W t) (QuantumZipper.logDerivFwd W t)
      (H \ QuantumZipper.fwdHull W t) := by
  have hU : IsOpen (H \ QuantumZipper.fwdHull W t) :=
    QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht
  have hexp : ∀ z ∈ H \ QuantumZipper.fwdHull W t,
      exp (QuantumZipper.logDerivFwd W t z) = deriv (QuantumZipper.fwdMap W t) z := fun z hz =>
    (QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW ht hz).deriv.symm
  exact ⟨differentiableOn_of_continuousOn_of_exp_eq hU
    (fun z hz => (continuousAt_logDerivFwd hW ht hz).continuousWithinAt)
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).deriv hU) hexp, hexp⟩

/-! ## The strip charts of Aux. lemma 1 (FD11.5, FD12.3, FD12.4, FD11.8)

Throughout, `q > 0` and the strip is `𝒮 = {0 < Im z < 1}` (Specification p. 13). On `𝒮`,
`e^{πz} ∈ ℍ`, so `e^{πz} − 1` and `e^{πz} + q` lie in `ℍ` and their principal logarithms have
imaginary part in `(0, π)` (`DerivLog.arg_mem_Ioo_of_mem_H`): these are the branches the source
prescribes ("the inner logarithm has imaginary part in `(0, π)`"). -/

/-- The strip-to-half-plane chart `P(z) = −(e^{πz} + q)/(e^{πz} − 1)` of (FD11.5). -/
def stripToH (q : ℝ) (z : ℂ) : ℂ := -(exp (π * z) + q) / (exp (π * z) - 1)

/-- The derivative lift `L_P(z) = log(π(q+1)) + πz − 2 Log(e^{πz} − 1)` of (FD11.5). -/
def derivLogStripToH (q : ℝ) (z : ℂ) : ℂ :=
  (Real.log (π * (q + 1)) : ℂ) + π * z - 2 * log (exp (π * z) - 1)

/-- The chart `Q(z) = (e^{πz} − 1)/(e^{πz} + q)` of (FD12.3). -/
def stripQ (q : ℝ) (z : ℂ) : ℂ := (exp (π * z) - 1) / (exp (π * z) + q)

/-- The derivative lift `L_Q(z) = log(π(q+1)) + πz − 2 Log(e^{πz} + q)` of (FD12.3). -/
def derivLogStripQ (q : ℝ) (z : ℂ) : ℂ :=
  (Real.log (π * (q + 1)) : ℂ) + π * z - 2 * log (exp (π * z) + q)

/-- **(FD11.5)**: `L_P` is a derivative lift of `P` on the strip. -/
theorem isDerivLog_stripToH {q : ℝ} (hq : 0 < q) :
    IsDerivLog (stripToH q) (derivLogStripToH q) {z : ℂ | 0 < z.im ∧ z.im < 1} := by
  have hE := hasDerivAt_exp_pi_mul
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact (differentiableAt_lift_strip q ((hE z).differentiableAt.sub_const 1)
      (mem_slitPlane_of_mem_H (sub_one_mem_H (exp_pi_mul_mem_H hz)))).differentiableWithinAt
  · have hne := ne_zero_of_mem_H (sub_one_mem_H (exp_pi_mul_mem_H hz))
    have hP : HasDerivAt (stripToH q) _ z :=
      ((hE z).add_const (q : ℂ)).neg.div ((hE z).sub_const 1) hne
    rw [hP.deriv, derivLogStripToH, exp_lift_strip hq z _ hne]
    simp only [Pi.neg_apply]
    field_simp
    ring

/-- **(FD12.3)**: `L_Q` is a derivative lift of `Q` on the strip. -/
theorem isDerivLog_stripQ {q : ℝ} (hq : 0 < q) :
    IsDerivLog (stripQ q) (derivLogStripQ q) {z : ℂ | 0 < z.im ∧ z.im < 1} := by
  have hE := hasDerivAt_exp_pi_mul
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact (differentiableAt_lift_strip q ((hE z).differentiableAt.add_const (q : ℂ))
      (mem_slitPlane_of_mem_H (add_ofReal_mem_H (exp_pi_mul_mem_H hz) q))).differentiableWithinAt
  · have hne := ne_zero_of_mem_H (add_ofReal_mem_H (exp_pi_mul_mem_H hz) q)
    have hQ : HasDerivAt (stripQ q) _ z := ((hE z).sub_const 1).div ((hE z).add_const (q : ℂ)) hne
    rw [hQ.deriv, derivLogStripQ, exp_lift_strip hq z _ hne]
    field_simp
    ring

/-- `R ∘ Q = P` with `R(w) = −1/w` (Specification p. 17, "Direct algebra gives `R ∘ Q = P`"). -/
theorem neg_inv_comp_stripQ (q : ℝ) : (fun w => -w⁻¹) ∘ stripQ q = stripToH q := by
  funext z
  simp only [Function.comp_apply, stripQ, stripToH, inv_div, neg_div]

/-- `Log Q = Log(e^{πz} − 1) − Log(e^{πz} + q)` on the strip. -/
theorem log_stripQ {q : ℝ} {z : ℂ} (hz : z ∈ {z : ℂ | 0 < z.im ∧ z.im < 1}) :
    log (stripQ q z) = log (exp (π * z) - 1) - log (exp (π * z) + q) :=
  log_div_eq_sub_of_mem_H (sub_one_mem_H (exp_pi_mul_mem_H hz))
    (add_ofReal_mem_H (exp_pi_mul_mem_H hz) q)

/-- **(FD12.4)**: `L_R ∘ Q + L_Q = L_P` on the strip, with `L_R(w) = −2 Log w` of (FD12.1)
(no integer constant: the identity holds with the displayed branches). -/
theorem derivLog_comp_stripQ (q : ℝ) :
    EqOn (fun z => -2 * log (stripQ q z) + derivLogStripQ q z) (derivLogStripToH q)
      {z : ℂ | 0 < z.im ∧ z.im < 1} := by
  intro z hz
  simp only [log_stripQ hz, derivLogStripQ, derivLogStripToH]
  ring

/-- `Q` maps the strip into `ℍ`. -/
theorem mapsTo_stripQ {q : ℝ} (hq : 0 < q) :
    MapsTo (stripQ q) {z : ℂ | 0 < z.im ∧ z.im < 1} H := by
  intro z hz
  have hE : 0 < (exp (π * z)).im := exp_pi_mul_mem_H hz
  have hb := ne_zero_of_mem_H (add_ofReal_mem_H (exp_pi_mul_mem_H hz) q)
  show 0 < (stripQ q z).im
  rw [stripQ, div_im, ← sub_div]
  refine div_pos ?_ (normSq_pos.2 hb)
  simp only [sub_im, sub_re, add_im, add_re, one_im, one_re, ofReal_im, ofReal_re]
  nlinarith

/-- `P` maps the strip into `ℍ`. -/
theorem mapsTo_stripToH {q : ℝ} (hq : 0 < q) :
    MapsTo (stripToH q) {z : ℂ | 0 < z.im ∧ z.im < 1} H := by
  intro z hz
  have hE : 0 < (exp (π * z)).im := exp_pi_mul_mem_H hz
  have hb := ne_zero_of_mem_H (sub_one_mem_H (exp_pi_mul_mem_H hz))
  show 0 < (stripToH q z).im
  rw [stripToH, div_im, ← sub_div]
  refine div_pos ?_ (normSq_pos.2 hb)
  simp only [neg_im, neg_re, sub_im, sub_re, add_im, add_re, one_im, one_re, ofReal_im, ofReal_re]
  nlinarith

/-- The rotation `J(z) = −z + i` maps the strip to itself (Aux. lemma 1). -/
theorem mapsTo_rotation_strip :
    MapsTo (fun z : ℂ => -z + I) {z : ℂ | 0 < z.im ∧ z.im < 1} {z : ℂ | 0 < z.im ∧ z.im < 1} := by
  intro z hz
  have h1 : 0 < z.im := hz.1
  have h2 : z.im < 1 := hz.2
  show 0 < (-z + I).im ∧ (-z + I).im < 1
  rw [add_im, neg_im, I_im]
  constructor <;> linarith

theorem deriv_rotation (z : ℂ) : deriv (fun z : ℂ => -z + I) z = -1 :=
  ((hasDerivAt_id' z).neg.add_const I).deriv

/-- (FD11.8) the chosen lift `L_J = −iπ` of the rotation `J(z) = −z + i`. -/
theorem isDerivLog_rotation : IsDerivLog (fun z : ℂ => -z + I) (fun _ => -(π * I)) univ := by
  refine ⟨fun _ _ => differentiableWithinAt_const _, fun z _ => ?_⟩
  show exp (-(π * I)) = _
  rw [deriv_rotation, exp_neg, exp_pi_mul_I]
  norm_num

/-- (FD11.8) the compatible inverse lift `L_{J⁻¹} = −L_J ∘ J⁻¹ = +iπ` of `J⁻¹ = J`. -/
theorem isDerivLog_rotation_inv : IsDerivLog (fun z : ℂ => -z + I) (fun _ => π * I) univ := by
  refine ⟨fun _ _ => differentiableWithinAt_const _, fun z _ => ?_⟩
  show exp (π * I) = _
  rw [deriv_rotation, exp_pi_mul_I]

/-- **(FD11.8)**: with parameter `χ(κ') = −χ`, the centered counterflow field `F_d(u) = −u − πχ`
transported by `J⁻¹ = J` with its compatible inverse lift `+iπ` is `−u ∘ J`. -/
theorem coordChange_rotation (χ : ℝ) (u : ℂ → ℝ) :
    coordChange (-χ) (fun z => -z + I) (fun _ => (π : ℂ) * I) (fun z => -u z - π * χ) =
      fun z => -u (-z + I) := by
  funext z
  simp only [coordChange, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

end InteractingSLE
