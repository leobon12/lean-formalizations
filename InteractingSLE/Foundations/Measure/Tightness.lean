import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Tightness, Prokhorov and the portmanteau theorem on Polish product spaces

Packet PROVE-EXT (graph node `EXT.MEAS.prokhorov`: "laws with tight coordinate marginals are tight
on finite products; tight sequences have weakly convergent subsequences; closed relations
(equality of coordinates) and factorizations against bounded continuous functions pass to weak
limits"). Infrastructure, not a frozen source-facing file.

Mathlib (`a4c8ef0a`) has tightness (`MeasureTheory.IsTightMeasureSet`, binary products
`IsTightMeasureSet.prodMk`), Prokhorov's theorem (`isCompact_closure_of_isTightMeasureSet`), the
portmanteau theorem (`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`), the continuous
mapping theorem (`ProbabilityMeasure.continuous_map`), continuity of products of laws
(`ProbabilityMeasure.continuous_prod`) and metrizability of the weak topology (Lévy–Prokhorov).
This file adds the glue the specification uses:

* `isTightMeasureSet_pi`: tight coordinate marginals give tightness on a countable product;
* `exists_subseq_tendsto_of_isTightMeasureSet`: sequential Prokhorov theorem;
* `exists_subseq_tendsto_pi`: a sequence of laws on a countable product of Polish spaces with
  tight coordinate marginals has a weakly convergent subsequence (the "diagonal subsequence and
  Kolmogorov extension" step, done in one stroke on the Polish product);
* `measure_eq_one_of_tendsto_of_isClosed`, `ae_eq_of_tendsto_of_ae_eq`: closed events of full mass
  and equalities of continuous coordinates pass to weak limits;
* `map_eq_of_tendsto_of_map_eq`: a fixed law of a continuous coordinate passes to weak limits;
* `toMeasure_eq_prod_of_tendsto`: independence of two components (a product law) passes to weak
  limits.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace InteractingSLE.Prokhorov

/-! ### Tightness on countable products -/

/-- A set of measures on a countable product is tight if each family of coordinate marginals is
tight. -/
theorem isTightMeasureSet_pi {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)] {S : Set (Measure (∀ i, X i))}
    (hS : ∀ i, IsTightMeasureSet ((fun μ : Measure (∀ i, X i) => μ.map (fun x => x i)) '' S)) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ι
  have hK : ∀ i, ∃ K : Set (X i), IsCompact K ∧
      ∀ ν ∈ (fun μ : Measure (∀ i, X i) => μ.map (fun x => x i)) '' S, ν Kᶜ ≤ δ i := fun i =>
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 (hS i)) (δ i)
      (ENNReal.coe_pos.2 (hδpos i))
  choose K hKc hKle using hK
  refine ⟨univ.pi K, isCompact_univ_pi hKc, fun μ hμ => ?_⟩
  have hcompl : (univ.pi K)ᶜ = ⋃ i, (fun x : ∀ i, X i => x i) ⁻¹' (K i)ᶜ := by
    ext x
    simp
  calc μ (univ.pi K)ᶜ = μ (⋃ i, (fun x : ∀ i, X i => x i) ⁻¹' (K i)ᶜ) := by rw [hcompl]
    _ ≤ ∑' i, μ ((fun x : ∀ i, X i => x i) ⁻¹' (K i)ᶜ) := measure_iUnion_le _
    _ ≤ ∑' i, (δ i : ℝ≥0∞) := by
      refine ENNReal.tsum_le_tsum fun i => ?_
      exact (Measure.le_map_apply (measurable_pi_apply i).aemeasurable _).trans
        (hKle i _ ⟨μ, hμ, rfl⟩)
    _ ≤ ε := hδsum.le

/-! ### Sequential Prokhorov theorem -/

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

/-- **Prokhorov's theorem, sequential form.** In a separable metrizable space, a tight sequence of
probability measures has a weakly convergent subsequence. -/
theorem exists_subseq_tendsto_of_isTightMeasureSet [TopologicalSpace.PseudoMetrizableSpace E]
    [TopologicalSpace.SeparableSpace E] [T2Space E] [BorelSpace E] (μ : ℕ → ProbabilityMeasure E)
    (hμ : IsTightMeasureSet (range fun n => (μ n : Measure E))) :
    ∃ ν : ProbabilityMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have hS : IsTightMeasureSet
      {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ range μ} := by
    refine hμ.subset ?_
    rintro _ ⟨ν, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  have hc := isCompact_closure_of_isTightMeasureSet hS
  obtain ⟨ν, -, φ, hφ, hlim⟩ := hc.tendsto_subseq fun n => subset_closure (mem_range_self n)
  exact ⟨ν, φ, hφ, hlim⟩

/-- **Tight coordinate marginals on a countable Polish product.** A sequence of laws on a countable
product of Polish spaces whose coordinate marginals are tight has a weakly convergent
subsequence. -/
theorem exists_subseq_tendsto_pi {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, PolishSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] (μ : ℕ → ProbabilityMeasure (∀ i, X i))
    (hμ : ∀ i, IsTightMeasureSet (range fun n => ((μ n : Measure (∀ i, X i))).map (fun x => x i))) :
    ∃ ν : ProbabilityMeasure (∀ i, X i), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  refine exists_subseq_tendsto_of_isTightMeasureSet μ (isTightMeasureSet_pi fun i => ?_)
  refine (hμ i).subset ?_
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  exact ⟨n, rfl⟩

/-! ### What passes to weak limits -/

section Limits

variable [OpensMeasurableSpace E] [HasOuterApproxClosed E] {ι : Type*} {L : Filter ι}
  [L.NeBot] {μs : ι → ProbabilityMeasure E} {μ : ProbabilityMeasure E}

/-- **Portmanteau, closed events of full mass.** If `μ i F = 1` eventually and `μ i → μ` weakly,
with `F` closed, then `μ F = 1`. -/
theorem measure_eq_one_of_tendsto_of_isClosed (hlim : Tendsto μs L (𝓝 μ)) {F : Set E}
    (hF : IsClosed F) (h1 : ∀ᶠ i in L, (μs i : Measure E) F = 1) : (μ : Measure E) F = 1 := by
  refine le_antisymm prob_le_one ?_
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  have hls : L.limsup (fun i => (μs i : Measure E) F) = 1 := by
    rw [limsup_congr h1, limsup_const]
  rwa [hls] at h

/-- **Closed relations pass to weak limits.** If two continuous maps into a Hausdorff space agree
almost surely under every `μ i` (eventually in `L`) and `μ i → μ`, they agree `μ`-almost surely. -/
theorem ae_eq_of_tendsto_of_ae_eq {F : Type*} [TopologicalSpace F] [T2Space F]
    (hlim : Tendsto μs L (𝓝 μ)) {f g : E → F} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ᶠ i in L, f =ᵐ[(μs i : Measure E)] g) : f =ᵐ[(μ : Measure E)] g := by
  have hF : IsClosed {x | f x = g x} := isClosed_eq hf hg
  have hFm : MeasurableSet {x | f x = g x} := hF.measurableSet
  have h1 := measure_eq_one_of_tendsto_of_isClosed hlim hF (h.mono fun i hi => by
    rw [← prob_compl_eq_zero_iff hFm]
    exact measure_mono_null (fun x hx => hx) (ae_iff.1 hi))
  rw [← prob_compl_eq_zero_iff hFm] at h1
  exact ae_iff.2 (measure_mono_null (fun x hx => hx) h1)

end Limits

section MapLimits

variable [OpensMeasurableSpace E] {ι : Type*} {L : Filter ι} [L.NeBot]
  {μs : ι → ProbabilityMeasure E} {μ : ProbabilityMeasure E}

/-- **Fixed laws of continuous coordinates pass to weak limits.** If `f` is continuous, the law of
`f` is `ν` under every `μ i` (eventually in `L`) and `μ i → μ`, then the law of `f` under `μ` is
`ν`. -/
theorem map_eq_of_tendsto_of_map_eq {F : Type*} [TopologicalSpace F] [MeasurableSpace F]
    [BorelSpace F] [T2Space (ProbabilityMeasure F)] (hlim : Tendsto μs L (𝓝 μ)) {f : E → F}
    (hf : Continuous f) {ν : ProbabilityMeasure F} (h : ∀ᶠ i in L, (μs i).map f = ν) :
    μ.map f = ν := by
  have h1 : Tendsto (fun i => (μs i).map f) L (𝓝 (μ.map f)) :=
    ((ProbabilityMeasure.continuous_map hf).tendsto μ).comp hlim
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (h.mono fun i hi => hi.symm))

end MapLimits

section ProdLimits

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace α]
  [TopologicalSpace β] [SecondCountableTopology α] [SecondCountableTopology β]
  [TopologicalSpace.PseudoMetrizableSpace α] [TopologicalSpace.PseudoMetrizableSpace β]
  [BorelSpace α] [BorelSpace β] [T2Space (ProbabilityMeasure (α × β))]
  {ι : Type*} {L : Filter ι} [L.NeBot]

/-- **Independence passes to weak limits.** If under every `μ i` (eventually in `L`) the two
components are independent (the law is the product of its marginals) and `μ i → μ` weakly, then
the components are independent under `μ`. -/
theorem toMeasure_eq_prod_of_tendsto {μs : ι → ProbabilityMeasure (α × β)}
    {μ : ProbabilityMeasure (α × β)} (hlim : Tendsto μs L (𝓝 μ))
    (h : ∀ᶠ i in L, (μs i : Measure (α × β)) =
      ((μs i : Measure (α × β)).map Prod.fst).prod ((μs i : Measure (α × β)).map Prod.snd)) :
    (μ : Measure (α × β)) =
      ((μ : Measure (α × β)).map Prod.fst).prod ((μ : Measure (α × β)).map Prod.snd) := by
  set p : ProbabilityMeasure (α × β) → ProbabilityMeasure (α × β) := fun ν =>
    (ν.map Prod.fst).prod (ν.map Prod.snd) with hp
  have hpc : Continuous p :=
    ProbabilityMeasure.continuous_prod.comp
      ((ProbabilityMeasure.continuous_map continuous_fst).prodMk
        (ProbabilityMeasure.continuous_map continuous_snd))
  have h1 : Tendsto (fun i => p (μs i)) L (𝓝 (p μ)) := (hpc.tendsto μ).comp hlim
  have h2 : ∀ᶠ i in L, p (μs i) = μs i := h.mono fun i hi => by
    apply Subtype.ext
    exact hi.symm
  have h3 : p μ = μ := tendsto_nhds_unique h1 (hlim.congr' (h2.mono fun i hi => hi.symm))
  have h4 : ((μ : Measure (α × β)).map Prod.fst).prod ((μ : Measure (α × β)).map Prod.snd) =
      (μ : Measure (α × β)) :=
    congrArg (fun ν : ProbabilityMeasure (α × β) => (ν : Measure (α × β))) h3
  exact h4.symm

end ProdLimits

end InteractingSLE.Prokhorov
