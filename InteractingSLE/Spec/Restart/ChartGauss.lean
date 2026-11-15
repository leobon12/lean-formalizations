/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Datum
import InteractingSLE.Spec.Coupling.ProtectedKernel
import InteractingSLE.Foundations.Harmonic.StepData
import InteractingSLE.Impl.PiecewiseConstant
import Mathlib.Probability.Kernel.CondDistrib

/-!
# (R1) of the first-contact restart: the conditional chart field given the datum is a GFF

Packet PROVE-RESTART-CPL2. The restart carrier `FirstContactRestartStatement` (`Carrier.lean`) asks, for almost
every chart datum `c`, that under the regular conditional law `K c` of the restart variable given the datum the chart
field is a GFF on `ℍ` with boundary datum `c` (the first conjunct of `IsConditionalFlowPair`). The specification
proves the conditional law **given the retained marked first-contact history** `𝒢` (Lemma 7.8, p. 290: "the
conditional Gaussian law is the retained marked law given the local-set germ and the two selected histories", with
mean `𝔤 ∘ φ − χ arg φ'`; Theorem W8, p. 539: "it has the canonical surviving finite-word mean in its joint unbounded
component"); in the chart this is the GFF on `ℍ` with the mean `𝔤`, the bounded harmonic extension of the chart datum.
Since that law depends on `𝒢` only through the datum, the conditional law given the datum alone is the same
(PROVE-RESTART-CPL handoff, "Truth check").

This file proves that step in general (`ae_isGFFWithBoundaryData_of_condExp`): if, on a `𝒢`-measurable event `M`,
the characteristic functional of the chart field given `𝒢` is the Gaussian one of the datum `β` (a `𝒢`-measurable
sorted word), then for **every** Markov kernel `K` disintegrating the joint law of `(β, X)` on `M`, almost every
`K c` makes the field a GFF with datum `c`.

Two points need care, and are the reason for the structure of the proof:
* the transfer from `𝒢` to the datum needs the Gaussian characteristic value to be a **measurable** function of the
  datum (an almost-sure identity `f ∘ β = g` with `g` `𝒢`-measurable does not make `f` measurable, and the
  conditional law given `σ(β)` can then differ); this is why the mean is the explicit word mean
  `BoundaryWord.mean` (jointly measurable, `measurable_mean`), the bounded harmonic extension of a sorted word
  (`isBoundedHarmonicExtension_mean`, unique: `eqOn_mean`);
* "for every test function" is uncountable, so the identity is used only on the countable family of rational
  combinations of the generating test functions (`ratComb`), which determine a law on `𝒟'(ℍ)`
  (`ext_of_integral_cexp_ratComb`); the GFF property for all test functions then comes from the reference law
  `BoundaryWord.gffLaw` (`isGFFWithBoundaryData_gffLaw`).

## Main results

* `BoundaryWord.mean`, `BoundaryWord.isBoundedHarmonicExtension_mean`, `BoundaryWord.eqOn_mean`,
  `BoundaryWord.measurable_mean`: the explicit bounded harmonic extension of a sorted word;
* `BoundaryWord.gffLaw`, `BoundaryWord.integral_cexp_gffLaw`, `BoundaryWord.isGFFWithBoundaryData_gffLaw`: the GFF law
  on `𝒟'(ℍ)` with the word as boundary datum;
* `isZBGFFProcess_comp`, `isZBGFFProcess_map`: transport of the zero-boundary GFF process along measurable maps;
* `ext_of_integral_cexp_ratComb`: finite measures on `𝒟'(V)` agreeing on countably many characteristic values are
  equal;
* **`ae_isGFFWithBoundaryData_of_condExp`** (and the frozen-style form `ae_isGFFWithBoundaryData_of_condExp'`): (R1)
  of the carrier from the conditional Gaussian identity in the chart;
* `exists_isMarkovKernel_map_eq_compProd`: the disintegrating kernel exists on a standard Borel canonical space.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace BoundaryWord

/-- The jump positions of the word are weakly increasing (`p i ≤ p j` for `i ≤ j < n`). -/
def IsSorted (c : BoundaryWord) : Prop := ∀ i j : ℕ, i ≤ j → j < c.1 → c.2.1 i ≤ c.2.1 j

/-- The step data of a sorted word. -/
def stepData (c : BoundaryWord) (hc : c.IsSorted) : StepData where
  n := c.1
  x := fun j => c.2.1 j
  monotone_x := fun i j hij => hc i j hij j.2
  v := fun k => c.2.2 k

/-- The explicit bounded harmonic extension of a word's boundary function:
`q n + ∑_{j < n} (q j − q (j+1)) arg(z − p j)/π`. -/
def mean (c : BoundaryWord) (z : ℂ) : ℝ :=
  c.2.2 c.1 + ∑ j ∈ Finset.range c.1, (c.2.2 j - c.2.2 (j + 1)) * (Complex.arg (z - c.2.1 j) / Real.pi)

theorem mean_eq_harmonicExtH (c : BoundaryWord) (hc : c.IsSorted) :
    c.mean = (c.stepData hc).harmonicExtH := by
  funext z
  simp only [mean, StepData.harmonicExtH, stepHarmonicH, stepData, Fin.val_last, Fin.val_castSucc,
    Fin.val_succ]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j => (c.2.2 j - c.2.2 (j + 1)) *
    (Complex.arg (z - c.2.1 j) / Real.pi)) c.1).symm

theorem measurable_mean : Measurable fun p : BoundaryWord × ℂ => p.1.mean p.2 := by
  have h : ∀ n : ℕ, Measurable fun p : BoundaryWord × ℂ =>
      p.1.2.2 n + ∑ j ∈ Finset.range n, (p.1.2.2 j - p.1.2.2 (j + 1)) *
        (Complex.arg (p.2 - p.1.2.1 j) / Real.pi) := by
    intro n
    refine Measurable.add ((measurable_pi_apply n).comp (measurable_snd.comp (measurable_snd.comp
      measurable_fst))) (Finset.measurable_sum _ fun j _ => ?_)
    refine Measurable.mul (((measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp
      measurable_fst))).sub ((measurable_pi_apply (j + 1)).comp (measurable_snd.comp
      (measurable_snd.comp measurable_fst)))) ?_
    refine (Complex.measurable_arg.comp (measurable_snd.sub ?_)).div_const _
    exact Complex.measurable_ofReal.comp ((measurable_pi_apply j).comp (measurable_fst.comp
      (measurable_snd.comp measurable_fst)))
  have hn : Measurable fun p : BoundaryWord × ℂ => p.1.1 := measurable_fst.comp measurable_fst
  have hF : Measurable fun q : (BoundaryWord × ℂ) × ℕ =>
      q.1.1.2.2 q.2 + ∑ j ∈ Finset.range q.2, (q.1.1.2.2 j - q.1.1.2.2 (j + 1)) *
        (Complex.arg (q.1.2 - q.1.1.2.1 j) / Real.pi) :=
    measurable_from_prod_countable_left fun n => h n
  exact hF.comp (measurable_id.prodMk hn)


theorem card_le_eq_index (c : BoundaryWord) {t : ℝ} (ht : t ∉ c.jumps) :
    (Finset.univ.filter fun j : Fin c.1 => c.2.1 j ≤ t).card = c.index t := by
  have hne : ∀ i < c.1, c.2.1 i ≠ t := fun i hi he => ht (mem_jumps.2 ⟨i, hi, he⟩)
  rw [index, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if c.2.1 i ≤ t then 1 else 0) c.1]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := hne i (Finset.mem_range.1 hi)
  by_cases h : c.2.1 i < t
  · simp [h, h.le]
  · have : ¬ c.2.1 i ≤ t := fun h' => h (lt_of_le_of_ne h' hi')
    simp [h, this]

theorem stepData_bdry (c : BoundaryWord) (hc : c.IsSorted) {t : ℝ} (ht : t ∉ c.jumps) :
    (c.stepData hc).bdry t = c.fn t := by
  show c.2.2 (Finset.univ.filter fun j : Fin c.1 => c.2.1 j ≤ t).card = c.2.2 (c.index t)
  rw [c.card_le_eq_index ht]

/-- **The word mean is the bounded harmonic extension** of a sorted word's boundary function. -/
theorem isBoundedHarmonicExtension_mean (c : BoundaryWord) (hc : c.IsSorted) :
    IsBoundedHarmonicExtension c.fn c.jumps c.mean := by
  rw [mean_eq_harmonicExtH c hc]
  refine ⟨(c.stepData hc).harmonicOnNhd_harmonicExtH, ?_, fun x hx => ?_⟩
  · obtain ⟨C, hC⟩ := (c.stepData hc).isBounded_image_harmonicExtH.exists_norm_le
    exact ⟨C, fun z hz => by simpa using hC _ (mem_image_of_mem _ hz)⟩
  · have hx' : ∀ j, (c.stepData hc).x j ≠ x := fun j hj =>
      hx (Finset.mem_coe.2 (mem_jumps.2 ⟨j, j.2, hj⟩))
    rw [← c.stepData_bdry hc (fun h => hx (Finset.mem_coe.2 h))]
    exact (c.stepData hc).tendsto_harmonicExtH hx'

/-- **Uniqueness**: every bounded harmonic extension of a sorted word's boundary function is the word mean on `ℍ`. -/
theorem eqOn_mean (c : BoundaryWord) (hc : c.IsSorted) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension c.fn c.jumps u) : EqOn u c.mean QuantumZipper.H := by
  rw [mean_eq_harmonicExtH c hc]
  obtain ⟨hh, ⟨C, hC⟩, hlim⟩ := hu
  refine (c.stepData hc).eqOn_harmonicExtH hh ?_ fun t ht => ?_
  · refine (Metric.isBounded_Icc (-C) C).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact abs_le.1 (hC z hz)
  · have htj : t ∉ c.jumps := fun h => by
      obtain ⟨i, hi, he⟩ := mem_jumps.1 h
      exact ht ⟨i, hi⟩ he
    rw [c.stepData_bdry hc htj]
    exact hlim t (fun h => htj (Finset.mem_coe.1 h))

end BoundaryWord

open LQGMetric

/-! ### Transport of the zero-boundary GFF process along a measurable map -/

section Transport

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {U : TopologicalSpace.Opens ℂ}

/-- A process read through a measurable map `Y` is a zero-boundary GFF process under `P` iff the process is one
under the law `P.map Y` (here: `P.map Y → P`). -/
theorem isZBGFFProcess_comp {P : Measure Ω} {Y : Ω → Ω'} (hY : Measurable Y)
    {X : TestOn U → Ω' → ℝ} (hX : IsZBGFFProcess U X (P.map Y)) :
    IsZBGFFProcess U (fun φ ω => X φ (Y ω)) P := by
  obtain ⟨hm, hg, hc, hcov⟩ := hX
  refine ⟨fun φ => (hm φ).comp hY, ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · have h := hg.hasGaussianLaw I
    refine ⟨h.aemeasurable.comp_aemeasurable hY.aemeasurable, ?_⟩
    have e := AEMeasurable.map_map_of_aemeasurable h.aemeasurable hY.aemeasurable
    rw [show (fun ω => I.restrict fun t => X t (Y ω)) = (fun x => I.restrict fun t => X t x) ∘ Y from rfl,
      ← e]
    exact h.isGaussian_map
  · rw [← hc φ, integral_map hY.aemeasurable ((hm φ).aestronglyMeasurable)]
  · rw [← hcov φ ψ, covariance_map ((hm φ).aestronglyMeasurable) ((hm ψ).aestronglyMeasurable)
      hY.aemeasurable]
    rfl

/-- The converse transport: a process of the form `X ∘ Y` that is a zero-boundary GFF process under `P` gives one
under `P.map Y`. -/
theorem isZBGFFProcess_map {P : Measure Ω} {Y : Ω → Ω'} (hY : Measurable Y)
    {X : TestOn U → Ω' → ℝ} (hXm : ∀ φ, Measurable (X φ))
    (hX : IsZBGFFProcess U (fun φ ω => X φ (Y ω)) P) : IsZBGFFProcess U X (P.map Y) := by
  obtain ⟨-, hg, hc, hcov⟩ := hX
  refine ⟨hXm, ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · have h := hg.hasGaussianLaw I
    have hm : Measurable fun x => I.restrict fun t => X t x :=
      measurable_pi_iff.2 fun t => hXm t.1
    refine ⟨hm.aemeasurable, ?_⟩
    rw [Measure.map_map hm hY]
    exact h.isGaussian_map
  · rw [← hc φ, integral_map hY.aemeasurable ((hXm φ).aestronglyMeasurable)]
  · rw [← hcov φ ψ, covariance_map ((hXm φ).aestronglyMeasurable) ((hXm ψ).aestronglyMeasurable)
      hY.aemeasurable]
    rfl

end Transport


/-! ### The Gaussian law with a word datum -/

namespace BoundaryWord

theorem continuousOn_mean (c : BoundaryWord) : ContinuousOn c.mean QuantumZipper.H := by
  have harg : ∀ p : ℝ, ContinuousOn (fun z : ℂ => Complex.arg (z - p)) QuantumZipper.H := by
    intro p z hz
    refine ((Complex.continuousAt_arg ?_).comp (continuousAt_id.sub continuousAt_const)).continuousWithinAt
    refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    have hz' : (0 : ℝ) < z.im := hz
    show (id z - (p : ℂ)).im ≠ 0
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact hz'.ne'
  exact continuousOn_const.add (continuousOn_finsetSum _ fun j _ =>
    continuousOn_const.mul ((harg _).div_const _))

theorem locallyIntegrableOn_mean (c : BoundaryWord) :
    LocallyIntegrableOn c.mean (upperHalfPlaneOpens : Set ℂ) volume :=
  c.continuousOn_mean.locallyIntegrableOn QuantumZipper.isOpen_H.measurableSet

/-- The mean of the word as a distribution on `ℍ`: `φ ↦ ∫ mean · φ`. -/
def meanDist (c : BoundaryWord) : DistOn upperHalfPlaneOpens :=
  Distribution.ofFun upperHalfPlaneOpens c.mean volume ⊤

theorem meanDist_apply (c : BoundaryWord) (φ : TestOn upperHalfPlaneOpens) :
    c.meanDist φ = ∫ z, c.mean z * φ z := by
  rw [meanDist, Distribution.ofFun_apply c.locallyIntegrableOn_mean]
  simp only [smul_eq_mul, mul_comm]

/-- **The GFF law with the boundary datum of the word**: the law of `h⁰ + 𝔥_c` on `𝒟'(ℍ)`, `h⁰` a zero-boundary GFF on
`ℍ` and `𝔥_c` the word mean. -/
def gffLaw (c : BoundaryWord) : Measure (DistOn upperHalfPlaneOpens) :=
  Coupling.gaussLaw upperHalfPlaneOpens upperHalfPlaneOpens c.meanDist

instance (c : BoundaryWord) : IsProbabilityMeasure c.gffLaw := by
  rw [gffLaw]; infer_instance

/-- The characteristic functional of the word GFF law. -/
theorem integral_cexp_gffLaw (c : BoundaryWord) (φ : TestOn upperHalfPlaneOpens) :
    ∫ g, Complex.exp (Complex.I * (g φ : ℂ)) ∂c.gffLaw =
      Complex.exp (Complex.I * ((∫ z, c.mean z * φ z : ℝ) : ℂ) -
        (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ : ℂ) / 2) := by
  rw [gffLaw, Coupling.integral_cexp_gaussLaw le_rfl subset_rfl, meanDist_apply]

theorem integral_mul_eq_of_eqOn {u v : ℂ → ℝ} (huv : EqOn u v QuantumZipper.H)
    (φ : TestOn upperHalfPlaneOpens) : ∫ z, u z * φ z = ∫ z, v z * φ z := by
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ QuantumZipper.H
  · simp only [huv hz]
  · have : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (φ.tsupport_subset h)
    simp only [this, mul_zero]

/-- **The word GFF law has the word as boundary datum.** -/
theorem isGFFWithBoundaryData_gffLaw (c : BoundaryWord) (hc : c.IsSorted) :
    IsGFFWithBoundaryData c.gffLaw id c.fn c.jumps := by
  refine ⟨measurable_id, fun u₀ hu₀ => ?_⟩
  have hZ := Coupling.isZeroBoundaryGFF_zbLaw (D := upperHalfPlaneOpens) subset_rfl
  have hF := Coupling.measurable_add_const_restrictDist upperHalfPlaneOpens
    (D := upperHalfPlaneOpens) c.meanDist
  have hmean : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, u₀ z * φ z = c.meanDist φ := fun φ => by
    rw [meanDist_apply]
    exact integral_mul_eq_of_eqOn (c.eqOn_mean hc hu₀) φ
  refine isZBGFFProcess_map hF (fun φ => (measurable_distOn_apply φ).sub_const _) ?_
  have hincl : ∀ φ : TestOn upperHalfPlaneOpens, GFF.testIncl upperHalfPlaneOpens upperHalfPlaneOpens φ = φ :=
    fun φ => TestFunction.ext fun z => by rw [GFF.coe_testIncl le_rfl]
  convert hZ.process using 2 with φ g
  simp only [add_apply, GFF.restrictDist_apply, hincl, hmean, id, add_sub_cancel_right]

end BoundaryWord

/-! ### Laws on `𝒟'(V)` are determined by countably many characteristic values -/

section RatComb

variable {V : TopologicalSpace.Opens ℂ}

/-- Indices of the rational linear combinations of the generating family `distGen V`: a finite set of generators
and rational coefficients. A countable type. -/
abbrev RatComb : Type := Σ s : Finset (ℕ × ℕ), (s → ℚ)

/-- The rational linear combination `∑ᵢ qᵢ φᵢ` of generators `φᵢ = distGen V i`. -/
def ratComb (V : TopologicalSpace.Opens ℂ) (k : RatComb) : TestOn V :=
  ∑ i : k.1, ((k.2 i : ℚ) : ℝ) • distGen V i

/-- **Two finite measures on `𝒟'(V)` whose characteristic functionals agree on the countably many rational
combinations of the generating family are equal.** (The finite-dimensional characteristic functions of the
generating cylinders agree on rational points, hence everywhere by continuity.) -/
theorem ext_of_integral_cexp_ratComb {μ ν : Measure (DistOn V)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ k : RatComb, ∫ g, Complex.exp (Complex.I * (g (ratComb V k) : ℂ)) ∂μ =
      ∫ g, Complex.exp (Complex.I * (g (ratComb V k) : ℂ)) ∂ν) : μ = ν := by
  classical
  have huniv : μ univ = ν univ := by
    have h0 := h ⟨∅, fun i => absurd i.2 (Finset.notMem_empty _)⟩
    simp only [ratComb, Finset.univ_eq_empty, Finset.sum_empty, map_zero, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, integral_const, Complex.real_smul, mul_one] at h0
    have h0' : μ.real univ = ν.real univ := by exact_mod_cast h0
    rw [Measure.real, Measure.real] at h0'
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h0'
  refine ext_of_generate_finite (Coupling.genCylinders V) (Coupling.distOn_eq_generateFrom_genCylinders V)
    (Coupling.isPiSystem_genCylinders V) ?_ huniv
  rintro _ ⟨C, hC, rfl⟩
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, Sx, hSx, rfl⟩ := hC
  set pr : DistOn V → EuclideanSpace ℝ s := fun T => WithLp.toLp 2 (fun i : s => T (distGen V i))
    with hprdef
  have hpr : Measurable pr := (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.2 fun i => measurable_distOn_apply _)
  have hmS : MeasurableSet {y : EuclideanSpace ℝ s | y.ofLp ∈ Sx} :=
    (WithLp.measurable_ofLp 2 _) hSx
  have hset : Coupling.genPairs V ⁻¹' cylinder s Sx = pr ⁻¹' {y | y.ofLp ∈ Sx} := by
    ext T
    simp only [pr, cylinder, mem_preimage, mem_ofPred_eq]
    rfl
  have hdense : DenseRange fun q : s → ℚ => WithLp.toLp 2 (fun i : s => ((q i : ℚ) : ℝ)) := by
    have h1 : DenseRange fun q : s → ℚ => fun i : s => ((q i : ℚ) : ℝ) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    have h2 : DenseRange (WithLp.toLp 2 : (s → ℝ) → EuclideanSpace ℝ s) :=
      (WithLp.toLp_surjective 2).denseRange
    exact h2.comp h1 (PiLp.continuous_toLp 2 _)
  have hchar : charFun (μ.map pr) = charFun (ν.map pr) := by
    refine Continuous.ext_on hdense continuous_charFun continuous_charFun ?_
    rintro _ ⟨q, rfl⟩
    rw [charFun_apply, charFun_apply, integral_map hpr.aemeasurable (by fun_prop),
      integral_map hpr.aemeasurable (by fun_prop)]
    simp_rw [hprdef, Coupling.inner_toLp_pairings, mul_comm _ Complex.I]
    exact h ⟨s, q⟩
  rw [hset, ← Measure.map_apply hpr hmS, ← Measure.map_apply hpr hmS, Measure.ext_of_charFun hchar]

end RatComb

/-! ### The conditional Gaussian law given the datum -/

namespace BoundaryWord

theorem measurableSet_isSorted : MeasurableSet {c : BoundaryWord | c.IsSorted} := by
  have : {c : BoundaryWord | c.IsSorted} =
      ⋂ i : ℕ, ⋂ j : ℕ, {c : BoundaryWord | i ≤ j → j < c.1 → c.2.1 i ≤ c.2.1 j} := by
    ext c; simp [IsSorted]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i ≤ j
  · have : {c : BoundaryWord | i ≤ j → j < c.1 → c.2.1 i ≤ c.2.1 j} =
        {c : BoundaryWord | c.1 ≤ j} ∪ {c : BoundaryWord | c.2.1 i ≤ c.2.1 j} := by
      ext c
      simp only [mem_ofPred_eq, mem_union]
      constructor
      · intro h
        by_cases hj : j < c.1
        · exact Or.inr (h hij hj)
        · exact Or.inl (not_lt.1 hj)
      · rintro (h | h) _ hj
        · exact absurd hj (not_lt.2 h)
        · exact h
    rw [this]
    exact (measurableSet_le measurable_fst measurable_const).union
      (measurableSet_le ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
        ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)))
  · have : {c : BoundaryWord | i ≤ j → j < c.1 → c.2.1 i ≤ c.2.1 j} = univ := by
      ext c; simp [hij]
    rw [this]
    exact MeasurableSet.univ

/-- The tested word mean `c ↦ ∫ mean_c · φ` is measurable. -/
theorem measurable_integral_mean_mul (φ : TestOn upperHalfPlaneOpens) :
    Measurable fun c : BoundaryWord => ∫ z, c.mean z * φ z := by
  have h : StronglyMeasurable fun p : BoundaryWord × ℂ => p.1.mean p.2 * φ p.2 :=
    (measurable_mean.mul (φ.continuous.measurable.comp measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume)).measurable

end BoundaryWord

/-- The Gaussian characteristic value `exp(i ∫ 𝔥_c φ − ‖φ‖²_{H⁻¹(ℍ)}/2)` of the word GFF law. -/
def gaussCF (c : BoundaryWord) (φ : TestOn upperHalfPlaneOpens) : ℂ :=
  Complex.exp (Complex.I * ((∫ z, c.mean z * φ z : ℝ) : ℂ) -
    (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ : ℂ) / 2)

theorem measurable_gaussCF (φ : TestOn upperHalfPlaneOpens) : Measurable fun c => gaussCF c φ := by
  unfold gaussCF
  exact Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp
    (BoundaryWord.measurable_integral_mean_mul φ))).sub measurable_const)

theorem gaussCF_eq_integral (c : BoundaryWord) (φ : TestOn upperHalfPlaneOpens) :
    gaussCF c φ = ∫ g, Complex.exp (Complex.I * (g φ : ℂ)) ∂c.gffLaw :=
  (BoundaryWord.integral_cexp_gffLaw c φ).symm

theorem norm_gaussCF_le (c : BoundaryWord) (φ : TestOn upperHalfPlaneOpens) : ‖gaussCF c φ‖ ≤ 1 := by
  rw [gaussCF_eq_integral]
  refine (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun g => ?_)).trans ?_
  · exact (Complex.norm_exp_I_mul_ofReal _).le
  · simp

/-- **(R1) of the restart carrier from the conditional Gaussian identity in the chart.** Let `𝒢` be a sub-σ-algebra
(the retained marked first-contact history), `M ∈ 𝒢` (the meeting branch), `β` a `𝒢`-measurable sorted word (the
chart datum) and `X` a random element of `S` whose coordinate `H ∘ X` is the chart field. Suppose that, conditionally
on `𝒢`, on `M` the chart field has the Gaussian characteristic functional of the GFF on `ℍ` with datum `β`:
`E[exp(i (H X, φ)) | 𝒢] = exp(i ∫ 𝔥_β φ − ‖φ‖²_{H⁻¹(ℍ)}/2)` for every test function `φ` (Lemma 7.8, p. 290, and
Theorem W8, p. 539, transported to the chart). Then for every Markov kernel `K` disintegrating the joint law of
`(β, X)` on `M`, for almost every datum `c`, under `K c` the field `H` is a GFF with boundary datum `c`: the first
conjunct of `IsConditionalFlowPair`. -/
theorem ae_isGFFWithBoundaryData_of_condExp {Ω S : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace S] {P : Measure Ω} [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω}
    (hM : MeasurableSet[𝒢] M) {β : Ω → BoundaryWord} (hβ : Measurable[𝒢] β)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) {X : Ω → S} (hX : Measurable X)
    {H : S → DistOn upperHalfPlaneOpens} (hH : Measurable H) {K : Kernel BoundaryWord S}
    [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    (hG : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ) :
    ∀ᵐ c ∂(P.restrict M).map β, IsGFFWithBoundaryData (K c) H c.fn c.jumps := by
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hMm : MeasurableSet M := h𝒢 _ hM
  have hfm : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable fun s => Complex.exp (Complex.I * (H s φ : ℂ)) := fun φ =>
    GFF.measurable_exp_I_mul ((measurable_distOn_apply φ).comp hH)
  have hnorm : ∀ (φ : TestOn upperHalfPlaneOpens) (s : S),
      ‖Complex.exp (Complex.I * (H s φ : ℂ))‖ ≤ 1 := fun φ s =>
    (Complex.norm_exp_I_mul_ofReal _).le
  -- Step 1: for each test function, the kernel characteristic value is the Gaussian one for a.e. datum.
  have hstep : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun c => ∫ s, Complex.exp (Complex.I * (H s φ : ℂ)) ∂(K c)) =ᵐ[(P.restrict M).map β]
        fun c => gaussCF c φ := by
    intro φ
    have hFm : Measurable fun c => ∫ s, Complex.exp (Complex.I * (H s φ : ℂ)) ∂(K c) :=
      ((hfm φ).stronglyMeasurable.integral_kernel (κ := K)).measurable
    have hFb : ∀ c, ‖∫ s, Complex.exp (Complex.I * (H s φ : ℂ)) ∂(K c)‖ ≤ 1 := fun c =>
      (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall (hnorm φ))).trans
        (by simp)
    have hint_f : Integrable (fun ω => Complex.exp (Complex.I * (H (X ω) φ : ℂ))) P :=
      Integrable.of_bound ((hfm φ).comp hX).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => hnorm φ (X ω))
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun A _ _ => ?_) (fun A _ _ => ?_)
      fun A hA _ => ?_
    · exact (Integrable.of_bound hFm.aestronglyMeasurable 1 (Eventually.of_forall hFb)).integrableOn
    · exact (Integrable.of_bound (measurable_gaussCF φ).aestronglyMeasurable 1
        (Eventually.of_forall fun c => norm_gaussCF_le c φ)).integrableOn
    have hpre : (fun ω => (β ω, X ω)) ⁻¹' (A ×ˢ univ) = β ⁻¹' A := by
      ext ω; simp
    have hGA : MeasurableSet[𝒢] (β ⁻¹' A ∩ M) := (hβ hA).inter hM
    have hgm : Measurable fun p : BoundaryWord × S => Complex.exp (Complex.I * (H p.2 φ : ℂ)) :=
      (hfm φ).comp measurable_snd
    calc ∫ c in A, ∫ s, Complex.exp (Complex.I * (H s φ : ℂ)) ∂(K c) ∂((P.restrict M).map β)
        = ∫ p in A ×ˢ univ, Complex.exp (Complex.I * (H p.2 φ : ℂ))
            ∂((P.restrict M).map β ⊗ₘ K) := by
          rw [Measure.setIntegral_compProd hA MeasurableSet.univ]
          · simp only [Measure.restrict_univ]
          · exact (Integrable.of_bound hgm.aestronglyMeasurable 1
              (Eventually.of_forall fun p => hnorm φ p.2)).integrableOn
      _ = ∫ ω in β ⁻¹' A ∩ M, Complex.exp (Complex.I * (H (X ω) φ : ℂ)) ∂P := by
          rw [← hlaw, setIntegral_map (hA.prod MeasurableSet.univ) hgm.aestronglyMeasurable
            (hβm.prodMk hX).aemeasurable, hpre, Measure.restrict_restrict (hβm hA)]
      _ = ∫ ω in β ⁻¹' A ∩ M, P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω ∂P :=
          (setIntegral_condExp h𝒢 hint_f hGA).symm
      _ = ∫ ω in β ⁻¹' A ∩ M, gaussCF (β ω) φ ∂P := by
          refine setIntegral_congr_ae (h𝒢 _ hGA) ?_
          filter_upwards [hG φ] with ω hω hωA
          exact hω hωA.2
      _ = ∫ c in A, gaussCF c φ ∂((P.restrict M).map β) := by
          rw [setIntegral_map hA (measurable_gaussCF φ).aestronglyMeasurable hβm.aemeasurable,
            Measure.restrict_restrict (hβm hA)]
  -- Step 2: simultaneously for the countable family of rational combinations, and sorted data.
  have hall := ae_all_iff.2 fun k : RatComb => hstep (ratComb upperHalfPlaneOpens k)
  have hsorted : ∀ᵐ c ∂(P.restrict M).map β, c.IsSorted := by
    rw [ae_map_iff hβm.aemeasurable BoundaryWord.measurableSet_isSorted, ae_restrict_iff' hMm]
    exact hsort
  filter_upwards [hall, hsorted] with c hc hcs
  -- Step 3: the law of `H` under `K c` is the word GFF law.
  have hmap : (K c).map H = c.gffLaw := by
    refine ext_of_integral_cexp_ratComb fun k => ?_
    rw [integral_map hH.aemeasurable (GFF.measurable_exp_I_mul
      (measurable_distOn_apply _)).aestronglyMeasurable, hc k, gaussCF_eq_integral]
  refine ⟨hH, fun u₀ hu₀ => ?_⟩
  have h := (c.isGFFWithBoundaryData_gffLaw hcs).2 u₀ hu₀
  rw [← hmap] at h
  exact isZBGFFProcess_comp hH h

/-- The same reduction with the conditional mean written, as in the frozen `IsOptionalHullCoupling`, through every
choice `u` of the bounded harmonic extensions of the data (they agree on `ℍ`, `BoundaryWord.eqOn_mean`). -/
theorem ae_isGFFWithBoundaryData_of_condExp' {Ω S : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace S] {P : Measure Ω} [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω}
    (hM : MeasurableSet[𝒢] M) {β : Ω → BoundaryWord} (hβ : Measurable[𝒢] β)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) {X : Ω → S} (hX : Measurable X)
    {H : S → DistOn upperHalfPlaneOpens} (hH : Measurable H) {K : Kernel BoundaryWord S}
    [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    (hG : ∀ u : Ω → ℂ → ℝ, (∀ ω, IsBoundedHarmonicExtension (β ω).fn (β ω).jumps (u ω)) →
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω =
          Complex.exp (Complex.I * ((∫ z, u ω z * φ z : ℝ) : ℂ) -
            (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ : ℂ) / 2)) :
    ∀ᵐ c ∂(P.restrict M).map β, IsGFFWithBoundaryData (K c) H c.fn c.jumps := by
  have hex : ∀ c : BoundaryWord, ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension c.fn c.jumps u := fun c =>
    (PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData).imp
      fun _ h => h.1
  refine ae_isGFFWithBoundaryData_of_condExp h𝒢 hM hβ hsort hX hH hlaw fun φ => ?_
  filter_upwards [hG (fun ω => (hex (β ω)).choose) (fun ω => (hex (β ω)).choose_spec) φ, hsort]
    with ω hω hωs hωM
  rw [hω hωM, gaussCF, BoundaryWord.integral_mul_eq_of_eqOn
    ((β ω).eqOn_mean (hωs hωM) (hex (β ω)).choose_spec) φ]

/-- **The regular conditional law of the restart variable given the datum** exists when the canonical space is
standard Borel: `(P|M).map (β, X) = (P|M).map β ⊗ₘ K` for `K` the conditional distribution of `X` given `β`. -/
theorem exists_isMarkovKernel_map_eq_compProd {Ω C S : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S] (P : Measure Ω) [IsFiniteMeasure P]
    (M : Set Ω) {β : Ω → C} (hβ : Measurable β) {X : Ω → S} (hX : Measurable X) :
    ∃ K : Kernel C S, IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K :=
  ⟨condDistrib X β (P.restrict M), inferInstance,
    (compProd_map_condDistrib hβ.aemeasurable hX.aemeasurable).symm⟩

end Restart

end InteractingSLE
