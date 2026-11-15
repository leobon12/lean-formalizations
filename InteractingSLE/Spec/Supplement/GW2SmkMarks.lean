/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdmWord
import InteractingSLE.Spec.Sec5.StagedRepLaterScale
import InteractingSLE.Spec.Sec7.Lemma71BStop

/-!
# GW2's stage mean, clause (G2): the kernel-route marks are the dilated stage marks

Packet PROVE-GW2-STAGEMEAN, marks round. The word clause of `GW2Sdm.StageDilationOnAt` asks that the kernel-route
harmonic function, rescaled by `λ`, be the bounded harmonic extension of the typed stage word flowed to the clock.
On the kernel route (`GW2Stl.exists_chart_mean_stop_random`) that harmonic function is the bounded harmonic extension
of a typing of the kernel word flowed along the kernel relative driver `R` to the relative clock `q`
(`kernelBhe`). This file proves the clause from the driver clause alone, once the kernel typing is the stage typing
with marks multiplied by `λ` and `q = λ² · clock`:

* **`rightImg_scale_of_eqOn`**: if `S = Sn(λ² ·)/λ` on `[0, Q]` (`Sn` continuous), then for `u ∈ [0, Q]`
  `rightImg Sn (λ x) (λ² u) = λ · rightImg S x u` (`Sec5.CrossCond.StagedRepLater.rightImg_scale` for the continuous
  rescaled path, and `Sec7.Lemma71B.rightImg_congr`: the real flow only reads the driver up to the current time);
* `relMarkR_scale`, `relMarkL_scale`: the marks relative to the driver scale by `λ` (right marks; left marks by
  reflection);
* `kernelBhe` and **`eqOn_kernelBhe_dil`** (per sample);
* **`StageInst.word_clause_of_kernel`**: the word clause of `StageDilationOnAt` for `Uca = kernelBhe` with the dilated
  stage typing.

Deterministic. Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Smk

open MartChar.RealFlow
open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24

/-! ### The real flow under Brownian scaling on an interval -/

/-- **Right images under Brownian scaling of the driver on `[0, Q]`.** -/
theorem rightImg_scale_of_eqOn {S Sn : ℝ → ℝ} (hSn : Continuous Sn) {lam : ℝ} (hlam : 0 < lam) {Q : ℝ}
    (hS : EqOn S (fun s => Sn (lam ^ 2 * s) / lam) (Icc 0 Q)) (x : ℝ) {u : ℝ} (hu : u ∈ Icc 0 Q) :
    rightImg Sn (lam * x) (lam ^ 2 * u) = lam * rightImg S x u := by
  set S' : ℝ → ℝ := fun s => Sn (lam ^ 2 * s) / lam with hS'
  have hS'c : Continuous S' := (hSn.comp (continuous_const.mul continuous_id)).div_const _
  have he : Sec5.CrossCond.StagedRepLater.scD lam S' = Sn := by
    funext s
    simp only [Sec5.CrossCond.StagedRepLater.scD, hS']
    rw [mul_div_cancel₀ s (pow_pos hlam 2).ne', mul_div_cancel₀ _ hlam.ne']
  rw [← he, Sec5.CrossCond.StagedRepLater.rightImg_scale hS'c hlam x hu.1,
    Sec7.Lemma71B.rightImg_congr hS'c hu.1 (hS.mono (Icc_subset_Icc_right hu.2)) x]

/-- **Right marks relative to the driver scale by `λ`.** -/
theorem relMarkR_scale {S Sn : ℝ → ℝ} (hSn : Continuous Sn) {lam : ℝ} (hlam : 0 < lam) {Q : ℝ} (hQ : 0 ≤ Q)
    (hS : EqOn S (fun s => Sn (lam ^ 2 * s) / lam) (Icc 0 Q)) (x : ℝ) :
    rightImg Sn (lam * x) (lam ^ 2 * Q) - Sn (lam ^ 2 * Q) = lam * (rightImg S x Q - S Q) := by
  have hQm : Q ∈ Icc 0 Q := ⟨hQ, le_rfl⟩
  have e : S Q = Sn (lam ^ 2 * Q) / lam := hS hQm
  rw [rightImg_scale_of_eqOn hSn hlam hS x hQm, e, mul_sub, mul_div_cancel₀ _ hlam.ne']

/-- **Left marks relative to the driver scale by `λ`** (reflection of `relMarkR_scale`). -/
theorem relMarkL_scale {S Sn : ℝ → ℝ} (hSn : Continuous Sn) {lam : ℝ} (hlam : 0 < lam) {Q : ℝ} (hQ : 0 ≤ Q)
    (hS : EqOn S (fun s => Sn (lam ^ 2 * s) / lam) (Icc 0 Q)) (x : ℝ) :
    -rightImg (fun v => -Sn v) (-(lam * x)) (lam ^ 2 * Q) - Sn (lam ^ 2 * Q) =
      lam * (-rightImg (fun v => -S v) (-x) Q - S Q) := by
  have hQm : Q ∈ Icc 0 Q := ⟨hQ, le_rfl⟩
  have hS' : EqOn (fun v => -S v) (fun s => (fun v => -Sn v) (lam ^ 2 * s) / lam) (Icc 0 Q) := fun s hs => by
    simp only
    rw [hS hs, neg_div]
  have e : S Q = Sn (lam ^ 2 * Q) / lam := hS hQm
  rw [← mul_neg, rightImg_scale_of_eqOn (Sn := fun v => -Sn v) hSn.neg hlam hS' (-x) hQm, e]
  field_simp

/-! ### The kernel-route harmonic function -/

/-- **The kernel-route harmonic function** of a typing with the weights of the type `w` and initial marks `xL, xR`,
flowed along the relative driver `R` to the relative clock `q` (the form of `GW2Stl.exists_chart_mean_stop_random`). -/
def kernelBhe (κ : ℝ) (w : WordType) (R : ℝ≥0 → ℝ) (xL : Fin w.1 → ℝ) (xR : Fin w.2.1 → ℝ) (q : ℝ≥0) : ℂ → ℝ :=
  bheProc κ (typedRhoL w) (typedRhoR w) (fun t (_ : Unit) => R t) (geomLW (fun t (_ : Unit) => R t) (fun _ => xL))
    (geomRW (fun t (_ : Unit) => R t) (fun _ => xR)) () q

/-- **The kernel-route harmonic function at the dilated typing is the dilated stage extension** (per sample): if the
stage driver is `S = R(λ² ·)/λ` on `[0, Q]` and `q = λ² Q`, then `kernelBhe(λ x)(λ ·)` is the bounded harmonic
extension of the same weights at the stage marks flowed along `S` to `Q`. -/
theorem eqOn_kernelBhe_dil {κ : ℝ} {w : WordType} {S : ℝ → ℝ} {R : ℝ≥0 → ℝ}
    (hR : Continuous fun s : ℝ => R s.toNNReal) {lam : ℝ} (hlam : 0 < lam) {Q : ℝ} (hQ : 0 ≤ Q) {q : ℝ≥0}
    (hq : (q : ℝ) = lam ^ 2 * Q) (hS : EqOn S (fun s => R (lam ^ 2 * s).toNNReal / lam) (Icc 0 Q))
    (xL : Fin w.1 → ℝ) (xR : Fin w.2.1 → ℝ) {v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension
      (forceBoundaryData κ (typedRhoL w) (typedRhoR w) (fun i => -rightImg (fun s => -S s) (-xL i) Q - S Q)
        (fun j => rightImg S (xR j) Q - S Q))
      (forceJumpSet (fun i => -rightImg (fun s => -S s) (-xL i) Q - S Q) (fun j => rightImg S (xR j) Q - S Q)) v) :
    EqOn (fun z => kernelBhe κ w R (fun i => lam * xL i) (fun j => lam * xR j) q ((lam : ℂ) * z)) v H := by
  have hRq : R q = R (lam ^ 2 * Q).toNNReal := by rw [← hq, Real.toNNReal_coe]
  have eL : (fun i => lam * (-rightImg (fun s => -S s) (-xL i) Q - S Q)) =
      fun i => geomLW (fun t (_ : Unit) => R t) (fun _ => fun i => lam * xL i) i q () - R q := by
    funext i
    rw [← relMarkL_scale hR hlam hQ hS (xL i), hRq, ← hq]
    rfl
  have eR : (fun j => lam * (rightImg S (xR j) Q - S Q)) =
      fun j => geomRW (fun t (_ : Unit) => R t) (fun _ => fun j => lam * xR j) j q () - R q := by
    funext j
    rw [← relMarkR_scale hR hlam hQ hS (xR j), hRq, ← hq]
    rfl
  have hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (typedRhoL w) (typedRhoR w) (fun i => lam * (-rightImg (fun s => -S s) (-xL i) Q - S Q))
        (fun j => lam * (rightImg S (xR j) Q - S Q)))
      (forceJumpSet (fun i => lam * (-rightImg (fun s => -S s) (-xL i) Q - S Q))
        (fun j => lam * (rightImg S (xR j) Q - S Q)))
      (kernelBhe κ w R (fun i => lam * xL i) (fun j => lam * xR j) q) := by
    rw [eL, eR]
    exact isBoundedHarmonicExtension_bheProc () q
  exact GW2Sdm.eqOn_bhe_dil hlam hu hv

/-! ### The word clause of a stage instance -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **The word clause of `GW2Sdm.StageDilationOnAt` on the kernel route**: for the kernel-route harmonic function of
the stage typing with marks multiplied by `λ`, flowed along the kernel relative driver `R` to `q = λ² · clock`, the
clause follows from the driver clause `S = R(λ² ·)/λ` on `[0, clock]`. -/
theorem StageInst.word_clause_of_kernel (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (w : WordType) (t : ℝ≥0) {G : Set Ω} {lam : Ω → ℝ} {R : Ω → ℝ≥0 → ℝ} {q : Ω → ℝ≥0}
    (h : ∀ᵐ ω ∂c.P, ω ∈ G → 0 < lam ω ∧ Continuous (fun s : ℝ => R ω s.toNNReal) ∧
      (q ω : ℝ) = lam ω ^ 2 * ((I.clock c t ω).toNNReal : ℝ) ∧
      EqOn (fun s : ℝ => I.drv c s.toNNReal ω) (fun s => R ω (lam ω ^ 2 * s).toNNReal / lam ω)
        (Icc 0 ((I.clock c t ω).toNNReal : ℝ))) :
    ∀ᵐ ω ∂c.P, ω ∈ G → EqOn
      (fun z => kernelBhe c.κ w (R ω) (fun i => lam ω * typedXL c.κ w (I.β (I.srec c r l ω)) i)
        (fun j => lam ω * typedXR c.κ w (I.β (I.srec c r l ω)) j) (q ω) ((lam ω : ℂ) * z))
      (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
        (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
        (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
        (I.clock c t ω).toNNReal) H := by
  filter_upwards [h] with ω hω hωG
  obtain ⟨hlam, hRc, hq, hS⟩ := hω hωG
  have hd : ∀ s, canonDrv s (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω) = I.drv c s ω := fun s =>
    relDrv_relVar (Hc := I.Hr) (R := I.drv c) (V := I.cap c) (ω := ω) (continuous_stgDrv (hv.2.1 ω) _)
      (stgDrv_zero (fun t => I.R t ω) _) s
  have hpR : Bessel.realPath Supp8.Q3Stop.canonDrv (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω) =
      fun s => I.drv c s.toNNReal ω := funext fun s => hd _
  have hpL : Bessel.realPath (fun t y => -Supp8.Q3Stop.canonDrv t y)
      (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω) =
      fun s => -I.drv c s.toNNReal ω := funext fun s => congrArg Neg.neg (hd _)
  refine eqOn_kernelBhe_dil hRc hlam (NNReal.coe_nonneg _) hq hS _ _ ?_
  convert isBoundedHarmonicExtension_bheProc ω (I.clock c t ω).toNNReal using 2 <;> funext i <;>
    simp only [geomLW, geomRW, hpL, hpR, Real.toNNReal_coe]

end InteractingSLE.Theorem14.GW2Smk
