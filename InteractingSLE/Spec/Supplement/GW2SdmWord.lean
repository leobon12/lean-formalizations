/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdmDrv
import InteractingSLE.Spec.Sec7.Lemma725RefFullDilField

/-!
# GW2's stage mean, clause (G2): the word clause from the dilation of the force data

Packet PROVE-GW2-STAGEMEAN, driver-scaling round. The last clause of `GW2Sdm.StageDilationOnAt` asks that the
kernel-route harmonic function `U_ca`, rescaled by `λ`, be the canonical bounded harmonic extension of the typed stage
word flowed to the clock (`bheProc`). Bounded harmonic extensions of force data are covariant under dilation and unique
(`Sec7.Lemma725RefFull.isBoundedHarmonicExtension_force_comp_dil`,
`PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension`), so the clause reduces to: `U_ca` is the bounded harmonic extension of the SAME weights at the DILATED marks.

* `finite_forceJumpSet`;
* **`eqOn_bhe_dil`**: if `u` extends the force data at marks `λ x` and `v` at marks `x`, then `u(λ ·) = v` on `ℍ`;
* **`StageInst.word_clause_of_bhe`**: the word clause of `StageDilationOnAt` from the extension property of `U_ca` at
  the dilated stage marks (the stage word's flowed marks, relative to the stage driver, multiplied by `λ`).

Deterministic. Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Sdm

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24

/-- The exceptional set of force data is finite. -/
theorem finite_forceJumpSet {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : (forceJumpSet xL xR).Finite :=
  ((Set.finite_range xL).union (Set.finite_range xR)).insert 0

/-- **Bounded harmonic extensions of force data under dilation of the marks.** -/
theorem eqOn_bhe_dil {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {lam : ℝ} (hlam : 0 < lam) {u v : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => lam * xL i) (fun j => lam * xR j))
      (forceJumpSet (fun i => lam * xL i) (fun j => lam * xR j)) u)
    (hv : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) v) :
    EqOn (fun w => u ((lam : ℂ) * w)) v H :=
  PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension (finite_forceJumpSet xL xR) hv
    (Sec7.Lemma725RefFull.isBoundedHarmonicExtension_force_comp_dil hlam hu)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **The word clause of `StageDilationOnAt`** from the extension property of the kernel-route harmonic function at
the dilated stage marks. -/
theorem StageInst.word_clause_of_bhe (I : StageInst Ω) (w : WordType) (t : ℝ≥0) {G : Set Ω} {lam : Ω → ℝ}
    {Uca : Ω → ℂ → ℝ}
    (hUca : ∀ᵐ ω ∂c.P, ω ∈ G → 0 < lam ω ∧ IsBoundedHarmonicExtension
      (forceBoundaryData c.κ (typedRhoL w) (typedRhoR w)
        (fun i => lam ω * (geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i (I.clock c t ω).toNNReal
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω) - I.drv c (I.clock c t ω).toNNReal ω))
        (fun j => lam ω * (geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j (I.clock c t ω).toNNReal
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω) - I.drv c (I.clock c t ω).toNNReal ω)))
      (forceJumpSet
        (fun i => lam ω * (geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i (I.clock c t ω).toNNReal
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω) - I.drv c (I.clock c t ω).toNNReal ω))
        (fun j => lam ω * (geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j (I.clock c t ω).toNNReal
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω) - I.drv c (I.clock c t ω).toNNReal ω)))
      (Uca ω)) :
    ∀ᵐ ω ∂c.P, ω ∈ G → EqOn (fun w => Uca ω (lam ω * w))
      (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
        (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
        (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
        (I.clock c t ω).toNNReal) H := by
  filter_upwards [hUca] with ω h hωG
  obtain ⟨hlam, hu⟩ := h hωG
  exact eqOn_bhe_dil hlam hu (isBoundedHarmonicExtension_bheProc ω _)

end InteractingSLE.Theorem14.GW2Sdm
