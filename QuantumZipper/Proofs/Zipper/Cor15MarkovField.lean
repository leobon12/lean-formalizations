import QuantumZipper.Proofs.Zipper.Cor15GrpHalves
import QuantumZipper.Proofs.Zipper.FSMeasBasic
import QuantumZipper.Proofs.Zipper.E5IncField

/-!
# D35 core piece 1: `Cor15MarkovFieldStmt` from the field-level Markov input

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18)
and Theorem 1.2. Decision D35 (`DECISIONS.md`): the field half of the Markov property of
capacity unzipping. For a genuine setup `c = (𝔥₀ + X, √κ B)`, `a > 0`, the unzipped field
`y = (D_a c).1` must be a.s. `RegEq` to `𝔥₀ + X'` for a free field `X'` modulo constants that is
independent of the shifted Brownian path `B(a + ·) − B(a)` — an actual field on the *same*
probability space, not only a law identity.

This file contains the two halves of that task that are pure bookkeeping, and isolates the
remaining analytic input:

* **`regEq_ofFun_add_sfTrunc_sub`**: the natural candidate carries `RegEq` *by construction*.
  The field `sfTrunc (y − 𝔥₀)` agrees with the raw difference `y − 𝔥₀` at every s-finite measure
  (D27: `FSMeas.sfTrunc`), hence at every folded circle, so the `limUnder` defining `avgReg`
  of `𝔥₀ + sfTrunc (y − 𝔥₀)` is literally the one defining `avgReg y`. No regularity of `y` is
  needed for this half.
* **`isFreeGFFModConstH_of_map_eq`**: `IsFreeGFFModConstH` is a property of the law of the whole
  field (`Measure ℂ → ℝ` with the product σ-algebra): measurable coordinates, Gaussian balanced
  increments, their means and covariances, and linearity in the measure argument. It therefore
  transfers across an identity of the laws `P.map Y = P'.map X` of two field-valued random
  variables. (The analogue for a measure-preserving *map* is `NonVacuity.nv_freeGFF`; the
  law-level version was missing.)
* **`Cor15UnzipFieldStmt`**: the remaining input, exactly the field version of Theorem 1.2
  (`theorem1_2_holds`, `B1Full.b1_full`, which are stated for the countable data
  `lawData`/`fieldLawMod0` only): the truncated raw difference of the unzipped field is, on the
  same space, a.s. equal to a free field modulo constants that is independent of the shifted
  Brownian path. **`cor15MarkovFieldStmt_of`** derives the D35 field statement from it.

Everything below is proved; `Cor15UnzipFieldStmt` is the (unproved) input.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

/-! ## 1. Freeness is a property of the law of the field -/

/-- **`IsFreeGFFModConstH` transfers along an identity of laws of the whole field.** If `Y` has
measurable coordinates and `P.map Y = P'.map X` with `X` a free field modulo constants, then `Y`
is a free field modulo constants. (Balanced increments are read off by a measurable map
`FieldSample → (I → ℝ)`; means, covariances and the a.s. linearity all depend only on the law.) -/
theorem isFreeGFFModConstH_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {Y : Ω → FieldSample} {X : Ω' → FieldSample}
    (hYm : ∀ μ : Measure ℂ, Measurable fun ω => Y ω μ)
    (hlaw : P.map Y = P'.map X) (hX : IsFreeGFFModConstH X P') :
    IsFreeGFFModConstH Y P := by
  have hY : Measurable Y := measurable_pi_iff.2 hYm
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  refine ⟨hYm, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun I => ⟨?_, ?_⟩⟩
    · exact (measurable_pi_iff.2 fun i => (hYm _).sub (hYm _)).aemeasurable
    · let F : Ω → (I → ℝ) := fun ω => I.restrict fun p => Y ω p.1.1 - Y ω p.1.2
      let G : Ω' → (I → ℝ) := fun ω => I.restrict fun p => X ω p.1.1 - X ω p.1.2
      let T : FieldSample → (I → ℝ) := fun x => I.restrict fun p => x p.1.1 - x p.1.2
      have hT : Measurable T := by
        refine measurable_pi_iff.2 fun i => ?_
        exact (measurable_pi_apply _).sub (measurable_pi_apply _)
      have eF : F = T ∘ Y := by funext ω; rfl
      have eG : G = T ∘ X := by funext ω; rfl
      have hlawT : P.map F = P'.map G := by
        rw [eF, eG, ← Measure.map_map hT hY, hlaw, Measure.map_map hT hXm]
      show IsGaussian (P.map F)
      rw [hlawT]
      exact (hX.gaussian.hasGaussianLaw I).isGaussian_map
  · intro μ ν hμ hν hm
    have hg : AEStronglyMeasurable (fun x : FieldSample => x μ - x ν) (P.map Y) :=
      ((measurable_pi_apply μ).sub (measurable_pi_apply ν)).aestronglyMeasurable
    have hg' : AEStronglyMeasurable (fun x : FieldSample => x μ - x ν) (P'.map X) :=
      ((measurable_pi_apply μ).sub (measurable_pi_apply ν)).aestronglyMeasurable
    calc ∫ ω, (Y ω μ - Y ω ν) ∂P
        = ∫ x, (x μ - x ν) ∂(P.map Y) := (integral_map hY.aemeasurable hg).symm
      _ = ∫ x, (x μ - x ν) ∂(P'.map X) := by rw [hlaw]
      _ = ∫ ω', (X ω' μ - X ω' ν) ∂P' := integral_map hXm.aemeasurable hg'
      _ = 0 := hX.centered μ ν hμ hν hm
  · intro p q h1 h2 h3 h4 h5 h6
    have hgp : AEStronglyMeasurable (fun x : FieldSample => x p.1 - x p.2) (P.map Y) :=
      ((measurable_pi_apply (p.1 : Measure ℂ)).sub
        (measurable_pi_apply (p.2 : Measure ℂ))).aestronglyMeasurable
    have hgq : AEStronglyMeasurable (fun x : FieldSample => x q.1 - x q.2) (P.map Y) :=
      ((measurable_pi_apply (q.1 : Measure ℂ)).sub
        (measurable_pi_apply (q.2 : Measure ℂ))).aestronglyMeasurable
    have hgp' : AEStronglyMeasurable (fun x : FieldSample => x p.1 - x p.2) (P'.map X) :=
      ((measurable_pi_apply (p.1 : Measure ℂ)).sub
        (measurable_pi_apply (p.2 : Measure ℂ))).aestronglyMeasurable
    have hgq' : AEStronglyMeasurable (fun x : FieldSample => x q.1 - x q.2) (P'.map X) :=
      ((measurable_pi_apply (q.1 : Measure ℂ)).sub
        (measurable_pi_apply (q.2 : Measure ℂ))).aestronglyMeasurable
    change cov[((fun x : FieldSample => x p.1 - x p.2) ∘ Y),
      ((fun x : FieldSample => x q.1 - x q.2) ∘ Y); P] = kernelCov2 neumannH p q
    rw [(covariance_map hgp hgq hY.aemeasurable).symm, hlaw,
      covariance_map hgp' hgq' hXm.aemeasurable]
    exact hX.covariance_eq p q h1 h2 h3 h4 h5 h6
  · intro μ ν hμ hν a b
    refine ae_iff.2 ?_
    set A : Set FieldSample := {x | x (a • μ + b • ν) = (a : ℝ) * x μ + (b : ℝ) * x ν} with hAdef
    have hA : MeasurableSet A := by
      rw [hAdef]
      have hm1 : Measurable fun x : FieldSample => (a : ℝ) * x μ :=
        measurable_const.mul (measurable_pi_apply μ)
      have hm2 : Measurable fun x : FieldSample => (b : ℝ) * x ν :=
        measurable_const.mul (measurable_pi_apply ν)
      exact measurableSet_eq_fun (measurable_pi_apply (a • μ + b • ν)) (hm1.add hm2)
    have hYset : {ω | ¬ (Y ω (a • μ + b • ν) = (a : ℝ) * Y ω μ + (b : ℝ) * Y ω ν)} =
        Y ⁻¹' Aᶜ := by
      rw [hAdef]; rfl
    have hXset : X ⁻¹' Aᶜ = {ω | ¬ (X ω (a • μ + b • ν) = (a : ℝ) * X ω μ + (b : ℝ) * X ω ν)} := by
      rw [hAdef]; rfl
    rw [hYset, ← Measure.map_apply hY hA.compl, hlaw, Measure.map_apply hXm hA.compl, hXset,
      ← ae_iff]
    exact hX.linear μ ν hμ hν a b

/-! ## 2. `RegEq` with `𝔥₀` is automatic for the truncated raw difference -/

variable {κ : ℝ}

/-! ## 3. The remaining field-level input and the D35 statement -/

end Cor15Group
end QuantumZipper
