import QuantumZipper.Proofs.Probability.LengthMarkov
import QuantumZipper.Proofs.Probability.BrownianPathMeas
import QuantumZipper.Proofs.Probability.BMExistence
import QuantumZipper.Proofs.Thm18.G1PkgPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5 repair, part 1: Wiener measure on the product path space (decision D39)

`E5Final4.not_isBrownianReal_coord`: no probability measure `W` on `ℝ≥0 → ℝ` (product σ-algebra)
makes the coordinate process `IsBrownianReal`, because mathlib's `IsBrownianReal.cont` asks the
set of discontinuous paths to be `W`-null, and no measurable set of the product σ-algebra other
than `univ` contains all discontinuous paths (Karatzas–Shreve, *Brownian Motion and Stochastic
Calculus*, 2nd ed., §2.2.B, Exercise 2.7). Continuity is a property of a *version* of Brownian
motion, not of its law on the product σ-algebra; the law itself (Wiener measure on
`(ℝ^{[0,∞)}, 𝓑(ℝ)^{⊗[0,∞)})`, Karatzas–Shreve §2.2.A, Theorem 2.2 (Daniell–Kolmogorov) and the
construction of §2.2.B) is characterized by its finite-dimensional distributions.

**Decision D39**: a "Brownian coordinate measure" `W` is stated as
`IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W` (the coordinate process has the Brownian
finite-dimensional laws). This file provides the two facts that replace the (impossible)
`IsBrownianReal.cont` in the E5 proofs:

* `ae_mem_of_continuous`: every measurable set containing all continuous paths has full
  `W`-measure (the continuous paths have outer `W`-measure one; Doob's formulation, cf.
  Karatzas–Shreve §2.2.B, discussion after Exercise 2.7);
* `isTrivialSigma_iInf_bmPast_coord`: Blumenthal's 0-1 law for the coordinate process under `W`
  (transferred from `GermZeroOne.isTrivialSigma_iInf_bmPast` through the continuous regularization
  `Thm18Asm.G1Pkg.pathReg`, which preserves `W`: `map_pathReg`).

Also: `wiener_eq_map` (`W` is the path law of every Brownian motion) and the non-vacuity facts
`isPreBrownianReal_coord_map`, `exists_wiener`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

/-- The coordinate process on the path space is pre-Brownian under the path law of a Brownian
motion (**non-vacuity** of the repaired condition). -/
theorem isPreBrownianReal_coord_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) (P.map (pathOf B)) where
  hasLaw I := by
    have hIm : Measurable fun b : ℝ≥0 → ℝ => I.restrict (fun t => b t) :=
      Finset.measurable_restrict I
    refine ⟨hIm.aemeasurable, ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable hIm.aemeasurable
      (IsBrownianReal.aemeasurable_pathOf hB)]
    exact (hB.hasLaw I).map_eq

/-- **A Wiener measure on the product path space exists.** -/
theorem exists_wiener : ∃ W : Measure (ℝ≥0 → ℝ), IsProbabilityMeasure W ∧
    IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W := by
  obtain ⟨B, hB⟩ := BMExist.exists_isBrownianReal_stdP
  have hW := isPreBrownianReal_coord_map hB
  exact ⟨_, hW.isGaussianProcess.isProbabilityMeasure, hW⟩

theorem isProjectiveLimit_of_pre {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : ℝ≥0 → Ω → ℝ} (hD : IsPreBrownianReal D μ) (hDm : AEMeasurable (pathOf D) μ) :
    IsProjectiveLimit (μ.map (pathOf D)) BrownianReal.projectiveFamily := by
  intro I
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hDm]
  exact (hD.hasLaw I).map_eq

/-- **A pre-Brownian coordinate measure is the path law of every Brownian motion.** -/
theorem wiener_eq_map {W : Measure (ℝ≥0 → ℝ)}
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) : W = P.map (pathOf B) := by
  have hid : pathOf (fun t (b : ℝ≥0 → ℝ) => b t) = id := rfl
  have h2 := isProjectiveLimit_of_pre hW (by rw [hid]; exact measurable_id.aemeasurable)
  rw [hid, Measure.map_id] at h2
  exact h2.unique (isProjectiveLimit_of_pre hB.toIsPreBrownianReal
    (IsBrownianReal.aemeasurable_pathOf hB))

variable {W : Measure (ℝ≥0 → ℝ)}

/-- **The continuous paths have outer `W`-measure one**: a measurable set containing every
continuous path is `W`-a.s. (replaces `IsBrownianReal.cont` for the coordinate process). -/
theorem ae_mem_of_continuous (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) (hC : ∀ b, Continuous b → b ∈ S) :
    ∀ᵐ b ∂W, b ∈ S := by
  obtain ⟨B, hB⟩ := BMExist.exists_isBrownianReal_stdP
  rw [wiener_eq_map hW hB]
  refine (ae_map_iff (IsBrownianReal.aemeasurable_pathOf hB) (p := fun b => b ∈ S) hS).2 ?_
  filter_upwards [hB.cont] with ω hω using hC _ hω

/-- Two measurable real functionals of the path that agree on continuous paths agree `W`-a.e. -/
theorem ae_eq_of_continuous (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    {f g : (ℝ≥0 → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ b, Continuous b → f b = g b) : f =ᵐ[W] g :=
  ae_mem_of_continuous hW (measurableSet_eq_fun hf hg) hfg

/-- The regularized coordinate process `t, b ↦ pathReg b t` (as `G1ProfileRed.regCoord`). -/
def regCoordE5 (t : ℝ≥0) (b : ℝ≥0 → ℝ) : ℝ := Thm18Asm.G1Pkg.pathReg b t

theorem measurable_regCoordE5 (t : ℝ≥0) : Measurable (regCoordE5 t) :=
  (measurable_pi_apply t).comp Thm18Asm.G1Pkg.pathReg_spec.1

/-- **The regularized coordinate process is a Brownian motion under a Wiener measure `W`**
(as `G1ProfileRed.isBrownianReal_regCoord`, after `wiener_eq_map`). -/
theorem isBrownianReal_regCoordE5 (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) :
    IsBrownianReal regCoordE5 W := by
  obtain ⟨B, hB⟩ := BMExist.exists_isBrownianReal_stdP
  rw [wiener_eq_map hW hB]
  exact
  { hasLaw := fun I => by
      have hIm : Measurable fun p : ℝ≥0 → ℝ => (I.restrict p : I → ℝ) :=
        measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℝ≥0)
      have hf : Measurable fun a : ℝ≥0 → ℝ => I.restrict (regCoordE5 · a) :=
        hIm.comp Thm18Asm.G1Pkg.pathReg_spec.1
      have hmB := IsBrownianReal.aemeasurable_pathOf hB
      refine ⟨hf.aemeasurable, ?_⟩
      rw [AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hmB]
      rw [← (hB.hasLaw I).map_eq]
      refine Measure.map_congr ?_
      filter_upwards [hB.cont] with ω hω
      have hc : Continuous (pathOf B ω) := hω
      show I.restrict (Thm18Asm.G1Pkg.pathReg (pathOf B ω)) = I.restrict (B · ω)
      rw [Thm18Asm.G1Pkg.pathReg_spec.2.2 _ hc]
      rfl
    cont := ae_of_all _ fun a => Thm18Asm.G1Pkg.pathReg_spec.2.1 a }

/-- **The regularization preserves Wiener measure.** -/
theorem map_pathReg (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) :
    W.map Thm18Asm.G1Pkg.pathReg = W := by
  have hid : pathOf (fun t (b : ℝ≥0 → ℝ) => b t) = id := rfl
  have h2 := isProjectiveLimit_of_pre hW (by rw [hid]; exact measurable_id.aemeasurable)
  rw [hid, Measure.map_id] at h2
  have h1 := isProjectiveLimit_of_pre (isBrownianReal_regCoordE5 hW).toIsPreBrownianReal
    Thm18Asm.G1Pkg.pathReg_spec.1.aemeasurable
  exact h1.unique h2

/-- **Blumenthal's 0-1 law for the coordinate process under a Wiener measure `W`.** -/
theorem isTrivialSigma_iInf_bmPast_coord
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) :
    GermZeroOne.IsTrivialSigma
      (⨅ n, GermZeroOne.bmPast (fun t (b : ℝ≥0 → ℝ) => b t) (GermZeroOne.epsSeq n)) W := by
  intro s hs
  have hs' : MeasurableSet[⨅ n, GermZeroOne.bmPast regCoordE5 (GermZeroOne.epsSeq n)]
      (Thm18Asm.G1Pkg.pathReg ⁻¹' s) := by
    rw [MeasurableSpace.measurableSet_iInf] at hs ⊢
    intro n
    obtain ⟨A, hA, hAs⟩ := hs n
    exact ⟨A, hA, by rw [← hAs]; rfl⟩
  have h := GermZeroOne.isTrivialSigma_iInf_bmPast (isBrownianReal_regCoordE5 hW)
    measurable_regCoordE5 _ hs'
  have hsm : MeasurableSet s :=
    ((iInf_le (fun n => GermZeroOne.bmPast (fun t (b : ℝ≥0 → ℝ) => b t)
      (GermZeroOne.epsSeq n)) 0).trans (GermZeroOne.bmPast_le LengthMarkov.GermDensity.measurable_coord _)) s hs
  rwa [← Measure.map_apply Thm18Asm.G1Pkg.pathReg_spec.1 hsm, map_pathReg hW] at h

end E5
end QuantumZipper
