import InteractingSLE.Spec.Dimension.Ordinary
import InteractingSLE.Foundations.SLE.Transience

/-!
# Transfer of the interior dimension bound (inputs of Aux. lemma 15)

Specification, proof of Aux. lemma 15 (`source/spec/p049-096.md`, lines 865–872, p. 89): a
localized future of a finite-force trace is absolutely continuous with respect to ordinary SLE_κ,
so "the preceding almost-sure dimension bound applies to its whole trace", and "a conformal map and
its inverse are Lipschitz on compact interior subsets", so pullbacks preserve the bound.

* `HasInteriorDimBound d W`: the conclusion of Aux. lemma 14 for the trace driven by `W`
  (`dim_H(γ ∩ ℍ) ≤ d` and the dyadic box-counting bound on every compact `K ⊆ ℍ`).
* `ae_hasInteriorDimBound`: Aux. lemma 14 on probability spaces in every universe (from the
  `Type` version through the canonical path space, `InteractingSLE.ae_drive_of_forall_canon`).
* `ae_hasInteriorDimBound_of_absolutelyContinuous`: if the law on `CPath` of a random path is
  absolutely continuous with respect to a Brownian law, the trace driven by `√κ` times that path
  satisfies the bound almost surely (no measurability of the event is needed).
* `dimH_image_le_of_differentiableOn`: a holomorphic map on an open set does not increase the
  Hausdorff dimension of subsets (it is locally Lipschitz).
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Dimension

open QuantumZipper QuantumZipper.RS

/-- The conclusion of Aux. lemma 14 for the chordal Loewner trace driven by `W`: the trace has
interior Hausdorff dimension at most `d`, and on every compact `K ⊆ ℍ`, for all large `n`, only
finitely many dyadic squares of side `2^{-n}` meet `γ ∩ K`, at most `(2^n)^d` of them. -/
def HasInteriorDimBound (d : ℝ) (W : ℝ → ℝ) : Prop :=
  dimH (trace W '' Ici 0 ∩ H) ≤ ENNReal.ofReal d ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∀ᶠ n in atTop,
      (dyadicHits n (trace W '' Ici 0 ∩ K)).Finite ∧
      (dyadicCount n (trace W '' Ici 0 ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ d

/-- **Aux. lemma 14, every universe.** For `0 < κ < 8` and every Brownian motion `B` on a
probability space in any universe, almost surely the SLE_κ trace driven by `√κ B` satisfies
`HasInteriorDimBound d_κ`. -/
theorem ae_hasInteriorDimBound {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, HasInteriorDimBound (interiorDimBound κ) (drive κ B ω) :=
  InteractingSLE.ae_drive_of_forall_canon hB κ fun μ _ hμ =>
    ae_dimH_sleTrace_inter_H_le hκ hκ8 μ canonBM hμ

/-- **Transfer through absolute continuity.** If the law on `CPath` of a random path `X` is
absolutely continuous with respect to a Brownian law `μ`, then almost surely the trace driven by
`√κ X` satisfies the interior dimension bound of Aux. lemma 14 (`0 < κ < 8`). -/
theorem ae_hasInteriorDimBound_of_absolutelyContinuous {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → CPath} (hX : AEMeasurable X P)
    {μ : Measure CPath} [IsProbabilityMeasure μ] (hμ : IsBrownianReal canonBM μ)
    (hac : P.map X ≪ μ) :
    ∀ᵐ ω ∂P, HasInteriorDimBound (interiorDimBound κ) (drive κ canonBM (X ω)) :=
  ae_of_ae_map hX (hac.ae_le (ae_dimH_sleTrace_inter_H_le hκ hκ8 μ canonBM hμ))

/-- A holomorphic map on an open set is locally Lipschitz there, so it does not increase the
Hausdorff dimension of subsets ("a conformal map and its inverse are Lipschitz on compact interior
subsets", proof of Aux. lemma 15). -/
theorem dimH_image_le_of_differentiableOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {E : Set ℂ} (hE : E ⊆ U) : dimH (f '' E) ≤ dimH E := by
  apply dimH_image_le_of_locally_lipschitzOn
  intro x hx
  have hcd : ContDiffAt ℂ 1 f x := (hf.contDiffOn hU).contDiffAt (hU.mem_nhds (hE hx))
  obtain ⟨K, t, ht, hL⟩ := hcd.exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩

/-- **A localized future absolutely continuous with respect to ordinary SLE_κ** (proof of Aux.
lemma 15: "the preceding almost-sure dimension bound applies to its whole trace"; the trace is
continuous in its own coordinate). If the law on `CPath` of a random path `X` is absolutely
continuous with respect to a Brownian law, then almost surely the Loewner chain driven by `√κ X`
(`0 < κ < 8`) has, at every time, the radial limit `trace`, this trace is continuous, and it
satisfies the interior dimension bound of Aux. lemma 14. -/
theorem ae_trace_good_of_absolutelyContinuous {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → CPath} (hX : AEMeasurable X P)
    {μ : Measure CPath} [IsProbabilityMeasure μ] (hμ : IsBrownianReal canonBM μ)
    (hac : P.map X ≪ μ) :
    ∀ᵐ ω ∂P, (∀ u : ℝ, 0 ≤ u → Tendsto
        (fun y : ℝ => fwdMapInv (drive κ canonBM (X ω)) u (y * Complex.I)) (𝓝[>] 0)
        (𝓝 (trace (drive κ canonBM (X ω)) u))) ∧
      ContinuousOn (trace (drive κ canonBM (X ω))) (Ici 0) ∧
      HasInteriorDimBound (interiorDimBound κ) (drive κ canonBM (X ω)) := by
  obtain ⟨δ, hδ, hgood⟩ := ae_sleTrace_good hμ hκ hκ8
  have hμgood : ∀ᵐ f ∂μ, (∀ u : ℝ, 0 ≤ u → Tendsto
        (fun y : ℝ => fwdMapInv (drive κ canonBM f) u (y * Complex.I)) (𝓝[>] 0)
        (𝓝 (trace (drive κ canonBM f) u))) ∧
      ContinuousOn (trace (drive κ canonBM f)) (Ici 0) ∧
      HasInteriorDimBound (interiorDimBound κ) (drive κ canonBM f) := by
    filter_upwards [hgood, ae_dimH_sleTrace_inter_H_le hκ hκ8 μ canonBM hμ] with f hf hdim
    refine ⟨fun u hu => ?_, hf.2.1, hdim⟩
    obtain ⟨C, hC⟩ := hf.2.2 ⌈u⌉₊
    exact tendsto_fwdMapInv_of_rpow_bound hδ (hC u ⟨hu, Nat.le_ceil u⟩)
  exact ae_of_ae_map hX (hac.ae_le hμgood)

end InteractingSLE.Dimension
