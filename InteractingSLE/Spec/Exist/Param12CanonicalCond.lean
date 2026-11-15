/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12CanonicalMeas
import InteractingSLE.Spec.Coupling.ResampleProjBridge
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# The Borel conditions defining canonical coupling laws (S4)

Packet PROVE-PARAM12C. A law `π` on `XCode × 𝒟'(ℍ)` is a **canonical coupling law** of the word `θ`
(`CanonCond κ θ π`) when

* the code marginal is an evolution law of `θ` (`IsEvoLaw`, S3);
* the field marginal is `fieldLaw0` of the time-zero harmonic extension of `θ`;
* (**sampled**) for every rational ball set `F`, dyadic time `q`, event `A` of a countable π-system of observations up
  to `q` (and `A = univ`) and rational combination `j` of the generating test functions of `𝒟(⋃F)`: on the event that
  `⋃ F̄` is alive at `q`, the characteristic functional of the field at the test function `ψ_{F,j}` integrates to the
  protected characteristic function `cfAt` at `q` (`sampL = sampR`);
* (**projection independence**) with the same indices and the rational combinations `φ_j` of the generating test
  functions of `𝒟(ℍ)`: the characteristic functional of the resampling at `⋃F` of the restricted field law equals that
  of the restricted field law at `φ_j` (`projL = projR`).

All conditions are countably many identities between measurable functions of (word, law): the set of pairs satisfying
them is measurable (`measurableSet_canonCond`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly Coupling Ito Staged LQGMetric Restart

variable {nL nR : ℕ}

/-! ### Fixed data -/

/-- The open union of the balls of a rational ball set, as an open set. -/
def ballsOpens (F : RatBallSet) : TopologicalSpace.Opens ℂ := ⟨ballsU F.1, isOpen_ballsU F.1⟩

theorem ballsOpens_subset_H (F : RatBallSet) : (ballsOpens F : Set ℂ) ⊆ H :=
  (ballsU_subset_ballsK F.1).trans F.2

/-- The sampled test functions: rational combinations of the generating family of `𝒟(⋃F)`, on `ℍ`. -/
def sampTest (F : RatBallSet) (j : RatComb) : TestOn upperHalfPlaneOpens :=
  toTestH (ballsOpens F) (ratComb (ballsOpens F) j)

theorem tsupport_sampTest_subset (F : RatBallSet) (j : RatComb) :
    tsupport (sampTest F j : ℂ → ℝ) ⊆ ballsK F.1 := by
  rw [sampTest, coe_toTestH (ballsOpens_subset_H F)]
  exact (ratComb (ballsOpens F) j).tsupport_subset.trans (ballsU_subset_ballsK F.1)

/-- A countable π-system generating the observations. -/
def obsPi (nL nR : ℕ) : Set (Set (ObsY nL nR)) := (exists_countable_isPiSystem_generate (ObsY nL nR)).choose

theorem obsPi_spec : (obsPi nL nR).Countable ∧ IsPiSystem (obsPi nL nR) ∧
    (inferInstance : MeasurableSpace (ObsY nL nR)) = MeasurableSpace.generateFrom (obsPi nL nR) :=
  (exists_countable_isPiSystem_generate (ObsY nL nR)).choose_spec

/-- A Borel version of the projection onto `H(⋃F)` for the zero-boundary GFF on `ℍ`. -/
def projMap (F : RatBallSet) : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens :=
  (exists_markovMap_zbLaw (ballsOpens F) (ballsOpens_subset_H F)).choose

theorem projMap_spec (F : RatBallSet) : Measurable (projMap F) ∧
    GFF.IsMarkovDecomposition (ballsOpens F) upperHalfPlaneOpens id (projMap F) (zbLaw upperHalfPlaneOpens) :=
  (exists_markovMap_zbLaw (ballsOpens F) (ballsOpens_subset_H F)).choose_spec

/-- The field law of a word: the zero-boundary GFF plus the time-zero harmonic extension. -/
def fieldLawW (κ : ℝ) (θ : WordData nL nR) : Measure (DistOn upperHalfPlaneOpens) := fieldLaw0 (wordExt κ θ)

theorem measurable_fieldLawW (κ : ℝ) : Measurable (fieldLawW (nL := nL) (nR := nR) κ) := by
  have e : fieldLawW (nL := nL) (nR := nR) κ = mapKernel (zbLaw upperHalfPlaneOpens)
      (fun r : WordData nL nR × DistOn upperHalfPlaneOpens => r.2 + meanH (wordExt κ r.1)) (measurable_shift κ) := by
    funext θ
    rw [fieldLawW, fieldLaw0_eq_map]
    rfl
  rw [e]
  exact (mapKernel _ _ _).measurable

/-! ### The four kinds of conditions -/

/-- The event: observation up to `q` in `A`, and `⋃ F̄` alive at `q`. -/
def condEv (F : RatBallSet) (q : ℝ≥0) (A : Set (ObsY nL nR)) : Set (XCode nL nR) :=
  codeObs q ⁻¹' A ∩ codeAlive (ballsK F.1) q

/-- Sampled condition, field side. -/
def sampL (F : RatBallSet) (q : ℝ≥0) (A : Set (ObsY nL nR)) (j : RatComb)
    (π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)) : ℂ :=
  ∫ p, (if p.1 ∈ condEv F q A then Complex.exp (Complex.I * (p.2 (sampTest F j) : ℂ)) else 0) ∂π

/-- Sampled condition, driving side. -/
def sampR (κ : ℝ) (F : RatBallSet) (q : ℝ≥0) (A : Set (ObsY nL nR)) (j : RatComb) (θ : WordData nL nR)
    (π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)) : ℂ :=
  ∫ p, (if p.1 ∈ condEv F q A then cfAt κ cwP (uP κ) (sampTest F j) 1 (fun _ => q) (θ, p.1) else 0) ∂π

/-- The constant `∫ e^{i G(y)(φ_j)} d zbLaw(y)` of the resampling. -/
def projConst (F : RatBallSet) (j : RatComb) : ℂ :=
  ∫ y, Complex.exp (Complex.I * (projMap F y (ratComb upperHalfPlaneOpens j) : ℂ)) ∂zbLaw upperHalfPlaneOpens

/-- Projection-independence condition: the resampled side. -/
def projL (κ : ℝ) (F : RatBallSet) (q : ℝ≥0) (A : Set (ObsY nL nR)) (j : RatComb) (θ : WordData nL nR)
    (π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)) : ℂ :=
  (∫ p, (if p.1 ∈ condEv F q A then Complex.exp (Complex.I *
    ((p.2 (ratComb upperHalfPlaneOpens j) - projMap F (p.2 - meanH (wordExt κ θ)) (ratComb upperHalfPlaneOpens j) : ℝ) : ℂ))
    else 0) ∂π) * projConst F j

/-- Projection-independence condition: the field side. -/
def projR (F : RatBallSet) (q : ℝ≥0) (A : Set (ObsY nL nR)) (j : RatComb)
    (π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)) : ℂ :=
  ∫ p, (if p.1 ∈ condEv F q A then Complex.exp (Complex.I * (p.2 (ratComb upperHalfPlaneOpens j) : ℂ))
    else 0) ∂π

/-- **Canonical coupling laws** of the word `θ` (see the module docstring). -/
def CanonCond (κ : ℝ) (θ : WordData nL nR) (π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)) : Prop :=
  IsEvoLaw κ θ (π.map Prod.fst) ∧ π.map Prod.snd = fieldLawW κ θ ∧
    (∀ (F : RatBallSet) (n k : ℕ), ∀ A ∈ insert univ (obsPi nL nR), ∀ j : RatComb,
      sampL F (dyad n k) A j π = sampR κ F (dyad n k) A j θ π) ∧
    ∀ (F : RatBallSet) (n k : ℕ), ∀ A ∈ insert univ (obsPi nL nR), ∀ j : RatComb,
      projL κ F (dyad n k) A j θ π = projR F (dyad n k) A j π

/-! ### Measurability -/

section Meas

/-- Integrals against a law, of a jointly measurable integrand, are measurable in (parameter, law). -/
theorem measurable_integral_law {α Ω' : Type*} [MeasurableSpace α] [MeasurableSpace Ω'] {f : α × Ω' → ℂ}
    (hf : Measurable f) :
    Measurable fun r : α × ProbabilityMeasure Ω' => ∫ p, f (r.1, p) ∂(r.2 : Measure Ω') := by
  let η : Kernel (α × ProbabilityMeasure Ω') Ω' :=
    ⟨fun r => (r.2 : Measure Ω'), measurable_subtype_coe.comp measurable_snd⟩
  have : IsMarkovKernel η := ⟨fun r => (r.2 : ProbabilityMeasure Ω').prop⟩
  have hg : StronglyMeasurable fun q : (α × ProbabilityMeasure Ω') × Ω' => f (q.1.1, q.2) :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  exact (hg.integral_kernel_prod_right' (κ := η)).measurable

theorem measurableSet_condEv (F : RatBallSet) (q : ℝ≥0) {A : Set (ObsY nL nR)} (hA : MeasurableSet A) :
    MeasurableSet (condEv (nL := nL) (nR := nR) F q A) :=
  (measurable_codeObs q hA).inter (measurableSet_codeAlive (isCompact_ballsK F.1) F.2 q)

theorem measurable_unshift (κ : ℝ) :
    Measurable fun r : WordData nL nR × DistOn upperHalfPlaneOpens => r.2 - meanH (wordExt κ r.1) := by
  refine measurable_distOn_iff.2 fun φ => ?_
  have hI : Measurable fun w : WordData nL nR => ∫ z, wordExt κ w z * φ z :=
    ((measurable_wordExt κ).mul (φ.continuous.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have he : (fun r : WordData nL nR × DistOn upperHalfPlaneOpens => (r.2 - meanH (wordExt κ r.1)) φ) =
      fun r => r.2 φ - ∫ z, wordExt κ r.1 z * φ z := by
    funext r
    rw [← meanH_apply_eq (continuousOn_wordExt κ r.1) φ]
    rfl
  rw [he]
  exact ((measurable_distOn_apply φ).comp measurable_snd).sub (hI.comp measurable_fst)

variable {Ωc : Type*} [MeasurableSpace Ωc]

theorem measurable_sampL (F : RatBallSet) (q : ℝ≥0) {A : Set (ObsY nL nR)} (hA : MeasurableSet A)
    (j : RatComb) :
    Measurable fun r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) =>
      sampL F q A j (r.2 : Measure _) :=
  measurable_integral_law (f := fun r : WordData nL nR × (XCode nL nR × DistOn upperHalfPlaneOpens) =>
    if r.2.1 ∈ condEv F q A then Complex.exp (Complex.I * (r.2.2 (sampTest F j) : ℂ)) else 0)
    (Measurable.ite ((measurableSet_condEv F q hA).preimage (measurable_fst.comp measurable_snd))
      (GFF.measurable_exp_I_mul ((measurable_distOn_apply _).comp (measurable_snd.comp measurable_snd)))
      measurable_const)

theorem measurable_sampR (κ : ℝ) (F : RatBallSet) (q : ℝ≥0) {A : Set (ObsY nL nR)} (hA : MeasurableSet A)
    (j : RatComb) :
    Measurable fun r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) =>
      sampR κ F q A j r.1 (r.2 : Measure _) := by
  have hc := measurable_cfAt_indicator (nL := nL) (nR := nR) κ (isCompact_ballsK F.1) F.2 (sampTest F j)
    (tsupport_sampTest_subset F j) q
  have e : ∀ r : WordData nL nR × (XCode nL nR × DistOn upperHalfPlaneOpens),
      (if r.2.1 ∈ condEv F q A then cfAt κ cwP (uP κ) (sampTest F j) 1 (fun _ => q) (r.1, r.2.1) else 0) =
        if r.2.1 ∈ codeObs q ⁻¹' A then
          (if (r.1, r.2.1).2 ∈ codeAlive (ballsK F.1) q then
            cfAt κ cwP (uP κ) (sampTest F j) 1 (fun _ => q) (r.1, r.2.1) else 0) else 0 := by
    intro r
    by_cases h1 : r.2.1 ∈ codeObs q ⁻¹' A <;> by_cases h2 : r.2.1 ∈ codeAlive (ballsK F.1) q <;>
      simp [condEv, h1, h2]
  refine (measurable_integral_law (f := fun r : WordData nL nR × (XCode nL nR × DistOn upperHalfPlaneOpens) =>
    if r.2.1 ∈ condEv F q A then cfAt κ cwP (uP κ) (sampTest F j) 1 (fun _ => q) (r.1, r.2.1) else 0) ?_)
  simp_rw [e]
  exact Measurable.ite ((measurable_codeObs q hA).preimage (measurable_fst.comp measurable_snd))
    (hc.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))) measurable_const

theorem measurable_projL (κ : ℝ) (F : RatBallSet) (q : ℝ≥0) {A : Set (ObsY nL nR)} (hA : MeasurableSet A)
    (j : RatComb) :
    Measurable fun r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) =>
      projL κ F q A j r.1 (r.2 : Measure _) := by
  refine Measurable.mul_const ?_ _
  have hG := (projMap_spec F).1
  have hu : Measurable fun r : WordData nL nR × (XCode nL nR × DistOn upperHalfPlaneOpens) =>
      r.2.2 - meanH (wordExt κ r.1) :=
    (measurable_unshift κ).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  refine measurable_integral_law (f := fun r : WordData nL nR × (XCode nL nR × DistOn upperHalfPlaneOpens) =>
    if r.2.1 ∈ condEv F q A then Complex.exp (Complex.I *
      ((r.2.2 (ratComb upperHalfPlaneOpens j) - projMap F (r.2.2 - meanH (wordExt κ r.1))
        (ratComb upperHalfPlaneOpens j) : ℝ) : ℂ)) else 0) ?_
  exact Measurable.ite ((measurableSet_condEv F q hA).preimage (measurable_fst.comp measurable_snd))
    (GFF.measurable_exp_I_mul (((measurable_distOn_apply _).comp (measurable_snd.comp measurable_snd)).sub
      ((measurable_distOn_apply _).comp (hG.comp hu)))) measurable_const

theorem measurable_projR (F : RatBallSet) (q : ℝ≥0) {A : Set (ObsY nL nR)} (hA : MeasurableSet A)
    (j : RatComb) :
    Measurable fun r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) =>
      projR F q A j (r.2 : Measure _) :=
  measurable_integral_law (f := fun r : WordData nL nR × (XCode nL nR × DistOn upperHalfPlaneOpens) =>
    if r.2.1 ∈ condEv F q A then Complex.exp (Complex.I * (r.2.2 (ratComb upperHalfPlaneOpens j) : ℂ)) else 0)
    (Measurable.ite ((measurableSet_condEv F q hA).preimage (measurable_fst.comp measurable_snd))
      (GFF.measurable_exp_I_mul ((measurable_distOn_apply _).comp (measurable_snd.comp measurable_snd)))
      measurable_const)

theorem measurableSet_obsPi {A : Set (ObsY nL nR)} (hA : A ∈ insert univ (obsPi nL nR)) : MeasurableSet A := by
  rcases hA with rfl | hA
  · exact MeasurableSet.univ
  · have h : MeasurableSet[MeasurableSpace.generateFrom (obsPi nL nR)] A :=
      MeasurableSpace.measurableSet_generateFrom hA
    rwa [← obsPi_spec.2.2] at h

/-- **Canonical coupling laws form a measurable set** of (word data, law). -/
theorem measurableSet_canonCond (κ : ℝ) :
    MeasurableSet {r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) |
      CanonCond κ r.1 (r.2 : Measure _)} := by
  have hc : (insert univ (obsPi nL nR)).Countable := obsPi_spec.1.insert univ
  have h3 : MeasurableSet {r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) |
      ∀ (F : RatBallSet) (n k : ℕ), ∀ A ∈ insert univ (obsPi nL nR), ∀ j : RatComb,
        sampL F (dyad n k) A j (r.2 : Measure _) = sampR κ F (dyad n k) A j r.1 (r.2 : Measure _)} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun F => MeasurableSet.iInter fun n => MeasurableSet.iInter fun k =>
      MeasurableSet.biInter hc fun A hA => MeasurableSet.iInter fun j =>
        measurableSet_eq_fun (measurable_sampL F _ (measurableSet_obsPi hA) j)
          (measurable_sampR κ F _ (measurableSet_obsPi hA) j)
  have h4 : MeasurableSet {r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) |
      ∀ (F : RatBallSet) (n k : ℕ), ∀ A ∈ insert univ (obsPi nL nR), ∀ j : RatComb,
        projL κ F (dyad n k) A j r.1 (r.2 : Measure _) = projR F (dyad n k) A j (r.2 : Measure _)} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun F => MeasurableSet.iInter fun n => MeasurableSet.iInter fun k =>
      MeasurableSet.biInter hc fun A hA => MeasurableSet.iInter fun j =>
        measurableSet_eq_fun (measurable_projL κ F _ (measurableSet_obsPi hA) j)
          (measurable_projR F _ (measurableSet_obsPi hA) j)
  have h1 := measurableSet_isEvoLaw (nL := nL) (nR := nR) κ
    (g := (Prod.fst : XCode nL nR × DistOn upperHalfPlaneOpens → XCode nL nR)) measurable_fst
  have hF : Measurable fun r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) =>
      ((r.2 : ProbabilityMeasure _) : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)).map Prod.snd :=
    (measurable_coe_map measurable_snd).comp measurable_snd
  have hG : Measurable fun r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) =>
      fieldLawW κ r.1 := (measurable_fieldLawW κ).comp measurable_fst
  have h2 := measurableSet_eq_measure hF hG fun _ => inferInstance
  convert ((h1.inter h2).inter h3).inter h4 using 1
  ext r
  simp only [CanonCond, mem_ofPred_eq, mem_inter_iff, and_assoc]

end Meas

end Param12

end Exist

end InteractingSLE
