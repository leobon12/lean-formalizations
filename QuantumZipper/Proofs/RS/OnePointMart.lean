import QuantumZipper.Proofs.RS.OnePointState
import QuantumZipper.Proofs.Probability.Girsanov.Generator
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# RS S1-M: the one-point local martingale `M = Υ^{d−2} S^β` has zero radial generator

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §5, node S1-M (see also
`blueprint/GIRSANOV_BLUEPRINT.md` §1).

For the sharp one-point estimate S1 the paper uses the one-point local martingale

`M_t = Υ_t^{d−2} S_t^β`,  `S_t = sin (arg Z_t)`,  `d = 1 + κ/8`,  `β = 8/κ − 1 = 4a − 1`,

where `(Z_t, L_t) = (fwdMap W t z, fwdLogCR W t z)` is the one-point state of S1-0 and
`Υ_t = exp L_t` (`a = 2/κ` is the radial time constant). In the state variables `(L, θ)` its
profile is the function

`φ_M L θ = exp ((κ/8 − 1) L) · sin θ ^ (8/κ − 1)`  (`RS.phiM`),

which is `Υ^{d−2} S^β` for `Υ = e^L`, `S = sin θ` (`phiM_log_eq_rpow`), and the content of the node
is that this profile has **zero radial generator**:

`radGen κ φ_M L θ = 0` for every `L ∈ ℝ` and `θ ∈ (0,π)` (and every `κ > 0`).

Consequently, through the factorization of the one-point generator (node S1-0,
`dynkinGen_opDrift_angle`), the function `x ↦ φ_M x.2 (arg x.1)` has zero Dynkin generator at
every one-point state with `Im Z ≥ c > 0` (`dynkinGen_opDrift_phiM`). This is the generator form
of LZ (4): `dM_t = (1 − 4a) (X_t/|Z_t|²) M_t dB_t`, i.e. `M` is a local martingale with no drift
term; the local Dynkin/optional stopping step at `ρ_r` that turns this into
`E[M_{ρ_r}; ρ_r ≤ T] ≤ M_0 = (Im z)^{d−2} sin^β (arg z)` is carried out on the Girsanov side
(blueprint nodes S1-Q and S1-3).

Proof: the three derivatives `∂_L φ_M = (κ/8 − 1) φ_M`,
`∂_θ φ_M = β cot θ · φ_M` and `∂²_θ φ_M = (β(β−1) cot²θ − β) φ_M` are computed with mathlib's
`HasDerivAt` calculus (via the log form `φ_M = exp ((κ/8−1) L + β log sin θ)` on `(0,π)`,
`Real.rpow_def_of_pos`), and then

`radGen κ φ_M = φ_M · [ −(4/κ)(κ/8 − 1) − β/2 + (β(β−1)/2 + (1 − 4/κ) β) cot²θ ] = 0`,

because both coefficients vanish for `β = 8/κ − 1`. This is exactly LZ's computation `(1−4a)` in
`dM = (1 − 4a)(X/|Z|²) M dB`; see also Lawler's Park City notes, proof of Thm 3.41, p. 30, where
the same `X²`, `Y²` coefficients cancel.

Literature: G. F. Lawler and W. Zhou, arXiv:1006.4936 (§2, (3)–(4), pp. 3–4: the Green function
`G(z) = y^{d−2} [sin arg z]^{4a−1}` and the local martingale `M_t(z) = Υ_t(z)^{d−2} S_t(z)^{4a−1}`);
G. Lawler, Park City notes (arXiv:0712.3256), Example 3.33 (p. 28) and the proof of Thm 3.41
(p. 30); G. Lawler and B. Werness, arXiv:1011.3551, §2.2–2.3; G. Lawler, *Conformally Invariant
Processes in the Plane*, Example 3.33 (p. 28), Thm 3.41. The derivative lemmas are **own
elementary proofs** (mathlib has no packaged derivation of `d/dθ sin^β θ` at a point; the log form
on `(0,π)` is used instead); the zero-generator identity is the blueprint's stated computation,
checked numerically in `audits/2026-09-27-fidelity/AUDIT6.md` §5–6 (`s1M_coefficients`).
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace RS

/-! ## The one-point martingale function -/

/-- **The one-point martingale profile.** `M = Υ^{d−2} S^β` in the state variables
`(L, θ) = (log Υ, arg Z)`: `φ_M L θ = exp ((κ/8 − 1) L) · sin θ ^ (8/κ − 1)`
(LZ arXiv:1006.4936 (4): `M_t = Υ_t^{d−2} S_t^{4a−1}`, `d = 1 + κ/8`, `4a − 1 = 8/κ − 1`). -/
def phiM (κ : ℝ) (L θ : ℝ) : ℝ :=
  Real.exp ((κ / 8 - 1) * L) * Real.sin θ ^ (8 / κ - 1)

theorem phiM_pos {κ L θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) : 0 < phiM κ L θ :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) _)

theorem phiM_nonneg {κ L θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) : 0 ≤ phiM κ L θ :=
  (phiM_pos hθ).le

/-- On the region `0 < θ < π` the power `sin^β θ` is the exponential of `β log sin θ`: the log
form of `φ_M` used to differentiate it (and, downstream, to form `barrier / φ_M`). -/
theorem phiM_eq_exp {κ L θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    phiM κ L θ = Real.exp ((κ / 8 - 1) * L + (8 / κ - 1) * Real.log (Real.sin θ)) := by
  rw [phiM, Real.rpow_def_of_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2), ← Real.exp_add]
  congr 1
  ring

/-- The log form of `φ_M(·, ·)` holds eventually on the open region `(0,π)`. -/
theorem phiM_eventuallyEq_exp {κ L θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    phiM κ L =ᶠ[𝓝 θ] fun θ' : ℝ =>
      Real.exp ((κ / 8 - 1) * L + (8 / κ - 1) * Real.log (Real.sin θ')) := by
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
  exact phiM_eq_exp hθ'

/-! ## The three derivatives of `φ_M` -/

/-- `∂_L φ_M = (κ/8 − 1) φ_M` (the exponent of `Υ^{d−2}`), for all `L`, `θ`. -/
theorem deriv_phiM_L (κ : ℝ) (L θ : ℝ) :
    deriv (fun L' : ℝ => phiM κ L' θ) L = (κ / 8 - 1) * phiM κ L θ := by
  have h1 : HasDerivAt (fun L' : ℝ => Real.exp ((κ / 8 - 1) * L'))
      (Real.exp ((κ / 8 - 1) * L) * (κ / 8 - 1)) L := by
    simpa using ((hasDerivAt_id L).const_mul (κ / 8 - 1)).exp
  have h2 : HasDerivAt (fun L' : ℝ => Real.exp ((κ / 8 - 1) * L') * Real.sin θ ^ (8 / κ - 1))
      (Real.exp ((κ / 8 - 1) * L) * (κ / 8 - 1) * Real.sin θ ^ (8 / κ - 1)) L := by
    simpa using h1.mul_const (Real.sin θ ^ (8 / κ - 1))
  rw [show (fun L' : ℝ => phiM κ L' θ)
      = fun L' : ℝ => Real.exp ((κ / 8 - 1) * L') * Real.sin θ ^ (8 / κ - 1) from rfl, h2.deriv]
  unfold phiM
  ring

/-- Derivative of the log form of `φ_M` in the angle variable:
`d/dθ exp ((κ/8−1)L + β log sin θ) = exp(…) · β cot θ` (for `θ ∈ (0,π)`, where `sin θ > 0`). -/
theorem hasDerivAt_phiM_expForm {κ L θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    HasDerivAt (fun θ' : ℝ => Real.exp ((κ / 8 - 1) * L + (8 / κ - 1) * Real.log (Real.sin θ')))
      (Real.exp ((κ / 8 - 1) * L + (8 / κ - 1) * Real.log (Real.sin θ))
        * ((8 / κ - 1) * (Real.cos θ / Real.sin θ))) θ := by
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hlog : HasDerivAt (fun θ' : ℝ => Real.log (Real.sin θ')) (Real.cos θ / Real.sin θ) θ := by
    have h := (Real.hasDerivAt_log hs).comp θ (Real.hasDerivAt_sin θ)
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using h
  exact ((hlog.const_mul (8 / κ - 1)).const_add ((κ / 8 - 1) * L)).exp

/-- `∂_θ φ_M = β cot θ · φ_M` for `θ ∈ (0,π)` (the derivative of `sin^β θ` is `β sin^{β−1} θ cos θ`
and `sin^{β−1}θ · sin θ = sin^β θ`). -/
theorem deriv_phiM_theta {κ L θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    deriv (phiM κ L) θ = (8 / κ - 1) * (Real.cos θ / Real.sin θ) * phiM κ L θ := by
  have hev := phiM_eventuallyEq_exp (κ := κ) (L := L) hθ
  rw [hev.deriv_eq, (hasDerivAt_phiM_expForm hθ).deriv, ← phiM_eq_exp hθ]
  ring

/-- `∂²_θ φ_M = (β(β−1) cot²θ − β) φ_M` for `θ ∈ (0,π)`: from `∂_θ φ_M = β cot θ φ_M` and
`d/dθ (β cot θ) = −β (1 + cot²θ)`. -/
theorem deriv_deriv_phiM_theta {κ L θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    deriv (deriv (phiM κ L)) θ
      = ((8 / κ - 1) * ((8 / κ - 1) - 1) * (Real.cos θ / Real.sin θ) ^ 2 - (8 / κ - 1))
        * phiM κ L θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  -- `deriv (φ_M (L, ·))` is eventually the derivative of the log form
  have hev : deriv (phiM κ L) =ᶠ[𝓝 θ] fun θ' : ℝ =>
      Real.exp ((κ / 8 - 1) * L + (8 / κ - 1) * Real.log (Real.sin θ'))
        * ((8 / κ - 1) * (Real.cos θ' / Real.sin θ')) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact (phiM_eventuallyEq_exp hθ').deriv_eq.trans (hasDerivAt_phiM_expForm hθ').deriv
  have hq : HasDerivAt (fun θ' : ℝ => Real.cos θ' / Real.sin θ')
      ((-Real.sin θ * Real.sin θ - Real.cos θ * Real.cos θ) / Real.sin θ ^ 2) θ :=
    (Real.hasDerivAt_cos θ).div (Real.hasDerivAt_sin θ) hs.ne'
  have h2 : HasDerivAt (fun θ' : ℝ =>
      Real.exp ((κ / 8 - 1) * L + (8 / κ - 1) * Real.log (Real.sin θ'))
        * ((8 / κ - 1) * (Real.cos θ' / Real.sin θ'))) _ θ :=
    (hasDerivAt_phiM_expForm hθ).mul (hq.const_mul (8 / κ - 1))
  rw [hev.deriv_eq, h2.deriv, ← phiM_eq_exp hθ]
  have hsne : Real.sin θ ≠ 0 := hs.ne'
  have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  field_simp
  nlinarith [hsc]

/-! ## S1-M: the zero generator -/

/-- **S1-M: the one-point martingale has zero radial generator.** For every `κ > 0`, every
`L ∈ ℝ` and every `θ ∈ (0,π)`,

`radGen κ φ_M L θ = 0`,

where `φ_M = RS.phiM` (`M = Υ^{d−2} S^β`). This is the generator form of LZ (4)
(`dM = (1 − 4a)(X/|Z|²) M dB`: no drift); note that no upper bound on `κ` is needed for this
identity. -/
theorem radGen_phiM_eq_zero (hκ : 0 < κ) {L θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    radGen κ (phiM κ) L θ = 0 := by
  have hk : κ ≠ 0 := hκ.ne'
  rw [radGen, deriv_phiM_L, deriv_phiM_theta hθ, deriv_deriv_phiM_theta hθ]
  have ha : -(4 / κ) * (κ / 8 - 1) - (8 / κ - 1) / 2 = 0 := by
    field_simp
    ring
  have hb : (8 / κ - 1) * ((8 / κ - 1) - 1) / 2 + (1 - 4 / κ) * (8 / κ - 1) = 0 := by
    field_simp
    ring
  linear_combination
    (phiM κ L θ * (Real.cos θ / Real.sin θ) ^ 2) * hb + phiM κ L θ * ha

/-- `arg Z ∈ (0,π)` for `Z` in the open upper half plane. -/
theorem arg_mem_Ioo_of_im_pos {Z : ℂ} (hZ : 0 < Z.im) : Complex.arg Z ∈ Ioo 0 Real.pi := by
  refine ⟨?_, Complex.arg_lt_pi_iff.mpr (Or.inr hZ.ne')⟩
  refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hZ.le) (fun h => ?_)
  exact hZ.ne' (Complex.arg_eq_zero_iff.mp h.symm).2

/-- The profile `φ_M` is `C³` on `univ ×ˢ (0,π)`, so that S1-0's generator identity applies. -/
theorem contDiffOn_uncurry_phiM (κ : ℝ) :
    ContDiffOn ℝ 3 (Function.uncurry (phiM κ)) (univ ×ˢ Ioo 0 Real.pi) := by
  have hfun : Function.uncurry (phiM κ) = fun p : ℝ × ℝ =>
      Real.exp ((κ / 8 - 1) * p.1) * Real.sin p.2 ^ (8 / κ - 1) := by
    funext p
    rfl
  rw [hfun]
  refine ContDiffOn.mul ?_ ?_
  · fun_prop
  · exact (by fun_prop :
        ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Real.sin p.2) (univ ×ˢ Ioo 0 Real.pi)).rpow_const_of_ne
      (fun p hp => (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2).ne')

/-- **S1-M, generator form at the one-point state.** While `Im Z ≥ c > 0`, the Dynkin generator
of `x ↦ φ_M x.2 (arg x.1)` (the one-point martingale `M` read in the state `(Z, L)`) vanishes:

`L (φ_M(·, arg ·)) (Z,L) = κ (Im Z)²/‖Z‖⁴ · radGen κ φ_M L (arg Z) = 0`

by S1-0 (`dynkinGen_opDrift_angle`) and the zero generator `radGen_phiM_eq_zero`. -/
theorem dynkinGen_opDrift_phiM (hκ : 0 < κ) (hc : 0 < c) {Z : ℂ} {L : ℝ} (hZ : c ≤ Z.im) :
    dynkinGen (opDrift c) (opNoise κ) (fun x : ℂ × ℝ => phiM κ x.2 (Complex.arg x.1))
      (Z, L) = 0 := by
  rw [dynkinGen_opDrift_angle hκ hc (φ := phiM κ) (contDiffOn_uncurry_phiM κ) hZ]
  rw [radGen_phiM_eq_zero hκ (arg_mem_Ioo_of_im_pos (hc.trans_le hZ)), mul_zero]

end RS
end QuantumZipper
