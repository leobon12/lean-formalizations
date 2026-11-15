/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SmkMarks
import InteractingSLE.Spec.Sec5.CrossRestartKernelQData
import InteractingSLE.Spec.Sec7.LocalExtHKer

/-!
# GW2's open lines: equal stage-start data stay equal along the stage

Packet PROVE-GW2-STAGEMEAN, R120 round. In the stage induction the kernel route gives the stage mean through a typing
of the KERNEL word along the kernel relative driver `Sn`, in the kernel chart `ca = λ · cs`. At the stage start the
kernel mean is identified with the β-form mean (uniqueness of conditional means), which says that the two typings'
force boundary data agree there, after the dilation by `λ`. This file shows that the agreement then holds at every
later stage time, in the form of the bounded harmonic extensions:

* `forceBoundaryData_mul_div`: the data of a typing at `λ x` is the data of the typing with marks divided by `λ`
  at `x`;
* **`eqOn_bhe_dil_of_data_eq`**: if the stage driver is the Brownian rescaling `S = Sn(λ² ·)/λ` on `[0, Q]` and the
  two typings' data agree at time `0` off a finite set (the kernel one read at `λ x`), then the kernel typing flowed
  along `Sn` to `λ² Q`, read at `λ z`, has the same bounded harmonic extension as the stage typing flowed along `S` to
  `Q` (`Sec5.CrossRestart.KernelQ.exists_finset_forceBoundaryData_flow_eq` for the flow, `GW2Smk.relMarkL_scale`,
  `GW2Smk.relMarkR_scale` for the rescaling, uniqueness of bounded harmonic extensions).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Omx

open MartChar.RealFlow

/-- The data of a typing at `λ x` is the data of the typing with marks divided by `λ` at `x`. -/
theorem forceBoundaryData_mul_div {lam : ℝ} (hlam : 0 < lam) (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (yL : Fin nL → ℝ) (yR : Fin nR → ℝ) (x : ℝ) :
    forceBoundaryData κ ρL ρR yL yR (lam * x) =
      forceBoundaryData κ ρL ρR (fun i => yL i / lam) (fun j => yR j / lam) x := by
  have eL : yL = fun i => lam * (yL i / lam) := funext fun i => (mul_div_cancel₀ _ hlam.ne').symm
  have eR : yR = fun j => lam * (yR j / lam) := funext fun j => (mul_div_cancel₀ _ hlam.ne').symm
  conv_lhs => rw [eL, eR]
  exact Sec7.Lemma725RefFull.forceBoundaryData_dil hlam κ ρL ρR _ _ x

/-- **Equal stage-start data give equal flowed bounded harmonic extensions.** -/
theorem eqOn_bhe_dil_of_data_eq {κ : ℝ} {S Sn : ℝ → ℝ} (hS : Continuous S) (hSn : Continuous Sn) {lam : ℝ}
    (hlam : 0 < lam) {Q : ℝ} (hQ : 0 ≤ Q) (hSS : EqOn S (fun s => Sn (lam ^ 2 * s) / lam) (Icc 0 Q))
    {nL nR mL mR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (σL : Fin mL → ℝ) (σR : Fin mR → ℝ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {yL : Fin mL → ℝ} {yR : Fin mR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hyL : ∀ i, yL i ≤ 0) (hyR : ∀ j, 0 ≤ yR j)
    {T₀ : Finset ℝ}
    (h0 : ∀ x ∉ T₀, forceBoundaryData κ σL σR yL yR (lam * x) = forceBoundaryData κ ρL ρR xL xR x)
    {u v : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ σL σR (fun i => -rightImg (fun s => -Sn s) (-yL i) (lam ^ 2 * Q) - Sn (lam ^ 2 * Q))
        (fun j => rightImg Sn (yR j) (lam ^ 2 * Q) - Sn (lam ^ 2 * Q)))
      (forceJumpSet (fun i => -rightImg (fun s => -Sn s) (-yL i) (lam ^ 2 * Q) - Sn (lam ^ 2 * Q))
        (fun j => rightImg Sn (yR j) (lam ^ 2 * Q) - Sn (lam ^ 2 * Q))) u)
    (hv : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -S s) (-xL i) Q - S Q)
        (fun j => rightImg S (xR j) Q - S Q))
      (forceJumpSet (fun i => -rightImg (fun s => -S s) (-xL i) Q - S Q) (fun j => rightImg S (xR j) Q - S Q)) v) :
    EqOn (fun z => u ((lam : ℂ) * z)) v H := by
  classical
  set yL' : Fin mL → ℝ := fun i => yL i / lam with hyL'
  set yR' : Fin mR → ℝ := fun j => yR j / lam with hyR'
  have hyL'0 : ∀ i, yL' i ≤ 0 := fun i => div_nonpos_of_nonpos_of_nonneg (hyL i) hlam.le
  have hyR'0 : ∀ j, 0 ≤ yR' j := fun j => div_nonneg (hyR j) hlam.le
  have h0' : ∀ x ∉ T₀, forceBoundaryData κ σL σR yL' yR' x = forceBoundaryData κ ρL ρR xL xR x := fun x hx => by
    rw [← h0 x hx, forceBoundaryData_mul_div hlam]
  obtain ⟨T, hT⟩ := Sec5.CrossRestart.KernelQ.exists_finset_forceBoundaryData_flow_eq hS hQ κ σL σR ρL ρR
    hyL'0 hyR'0 hxL hxR h0'
  -- the kernel marks flowed along `Sn` are `λ` times the scaled-down marks flowed along `S`
  have eL : (fun i => -rightImg (fun s => -Sn s) (-yL i) (lam ^ 2 * Q) - Sn (lam ^ 2 * Q)) =
      fun i => lam * (-rightImg (fun s => -S s) (-yL' i) Q - S Q) := by
    funext i
    have e : yL i = lam * yL' i := (mul_div_cancel₀ _ hlam.ne').symm
    rw [e]
    exact GW2Smk.relMarkL_scale hSn hlam hQ hSS (yL' i)
  have eR : (fun j => rightImg Sn (yR j) (lam ^ 2 * Q) - Sn (lam ^ 2 * Q)) =
      fun j => lam * (rightImg S (yR' j) Q - S Q) := by
    funext j
    have e : yR j = lam * yR' j := (mul_div_cancel₀ _ hlam.ne').symm
    rw [e]
    exact GW2Smk.relMarkR_scale hSn hlam hQ hSS (yR' j)
  rw [eL, eR] at hu
  have hu' := Sec7.Lemma725RefFull.isBoundedHarmonicExtension_force_comp_dil hlam hu
  -- both are bounded harmonic extensions of the stage data off one finite set
  set gL : Fin nL → ℝ := fun i => -rightImg (fun s => -S s) (-xL i) Q - S Q with hgL
  set gR : Fin nR → ℝ := fun j => rightImg S (xR j) Q - S Q with hgR
  set kL : Fin mL → ℝ := fun i => -rightImg (fun s => -S s) (-yL' i) Q - S Q with hkL
  set kR : Fin mR → ℝ := fun j => rightImg S (yR' j) Q - S Q with hkR
  set E : Set ℝ := (T : Set ℝ) ∪ forceJumpSet gL gR ∪ forceJumpSet kL kR with hE
  have hEf : E.Finite :=
    ((T.finite_toSet.union (GW2Sdm.finite_forceJumpSet gL gR)).union (GW2Sdm.finite_forceJumpSet kL kR))
  have hv' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR gL gR) E v :=
    LocalExt.IsBoundedHarmonicExtension.mono_set hv (fun x hx => Or.inl (Or.inr hx))
  have hu'' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR gL gR) E
      (fun z => u (Sec7.Lemma725RefFull.dil lam z)) := by
    have h1 := LocalExt.IsBoundedHarmonicExtension.mono_set hu' (S' := E) (fun x hx => Or.inr hx)
    refine (Restart.isBoundedHarmonicExtension_congr (g := forceBoundaryData κ σL σR kL kR) (fun y hy => ?_) _).2 h1
    exact (hT y fun h => hy (Or.inl (Or.inl h))).symm
  exact PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension hEf hv' hu''

end InteractingSLE.Theorem14.GW2Omx
