/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71CMart
import InteractingSLE.Spec.Sec7.Lemma71CMeas

/-!
# Lemma 7.1's killed mapped segment from the pocket coupling in chart form

Packet PROVE-LEMMA71C. Specification, proof of Lemma 7.1 (`source/spec/p193-240.md` L576–L606, pp. 223–225).

`Lemma71B.Lemma71KilledSegmentStatement` asks for the mapped pocket segment `γ = ψ(η_C)`, its driver `W` up to its
terminal capacity time `T`, a filtration with the usual conditions, and the **martingale clause**: the two-seed
coupling means with the seed weights (CPF2) are local martingales before `min (swallowTime z) T`. The proof of
Lemma 7.1 obtains the martingale clause from the **coupling clause in the pocket chart** (p. 225: "For each bounded
stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies to the revealed outer curves
and the middle prefix … The means in all the remaining components are those of the three-curve result in Remark 6.7.
In particular, in the active component they have the two seed heights (CPF2), with the inherited
logarithmic-derivative branch. Their time continuity is Proposition 6.5. The martingale characterization, Theorem
2.4, …"): conditionally on the history at a stopping time `τ < T`, the field `h` on the remaining part of the pocket
is the coupling mean of the mapped driver, read back through the pocket chart `ψ⁻¹` with the inherited branch, plus a
zero-boundary GFF there. In Lean this is `Coupling.MartMeans2.IsChartCouplingCharFun` with lifetime `T`.

This file proves the step "coupling clause in the pocket chart ⇒ martingale clause" for the killed driver
(`Lemma71C.hasMartingaleMeansBefore_of_isChartTransport`), with the driver's unboundedness at a finite `T` taken from
the geometry (`Lemma71B.unbounded_of_fwdHull_eq`), and so reduces `Lemma71KilledSegmentStatement` to the three-curve
pocket coupling in chart form.

## Main results

* `Lemma71PocketChartStatement` (**named input**): the three-curve construction of §7.1 delivers, on one probability
  space with a filtration with the usual conditions, the mapped segment `γ` (geometric clause), its driver `W` up to
  its terminal capacity time (continuous, adapted before `T`, hull clause), the measurable field `h`, the
  `𝓖₀`-measurable pocket chart `c` (conformal, continuous lift), and the killed coupling clause
  `IsChartCouplingCharFun` with the (CPF2) weights;
* **`lemma71KilledSegmentStatement_of_pocketChart`**: `Lemma71B.Lemma71KilledSegmentStatement` from it;
* `lemma71MappedSegmentStatement_of_pocketChart`, `lemma71TraceReferenceStatement_of_pocketChart`: the compositions
  with PROVE-LEMMA71B and PROVE-LEMMA71;
* `Lemma71PocketCurveStatement` (**named input, curve form**): as above, but the driver is the canonical driver
  `segDriver` of the mapped segment and the terminal capacity time is `capLife` (`Lemma71CClock.lean`), and instead of
  the driver's continuity, hull clause and adaptedness only the **adaptedness of the filled prefixes** at capacity
  times (`IsPrefixAdapted`) is required;
* **`lemma71PocketChartStatement_of_pocketCurve`** (the driver of the mapped segment up to its terminal capacity
  time: `IsSegCurve.segDriver_spec`, `adaptedBefore_segDriver`) and **`lemma71KilledSegmentStatement_of_pocketCurve`**.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe v

namespace InteractingSLE.Sec7.Lemma71C

open MartChar Coupling Lemma71B

/-- **Named input: the three-curve pocket coupling in chart form** (Specification §7.1, the setup, pp. 221–222; proof
of Lemma 7.1, pp. 223–225). Fix `0 < κ < 4` and angles `θ₁ < 0 < θ₂`. On the probability space of the three-curve
construction (a GFF `h` with its flow lines `η_{θ₁}`, `η`, `η_{θ₂}`, Proposition 5.5 and Theorem 1.2 in the
non-boundary regime) there are:
* a filtration `𝓖` with the usual conditions (right-continuous; the time-zero σ-algebra contains the null sets): the
  filtration retaining the complete outer curves and the mapped middle prefix;
* the mapped pocket segment `γ = ψ(η_C)` (the geometric clause of `Lemma71KilledSegmentStatement`);
* its driver `W` up to its terminal capacity time `T` (`W₀ = 0`, continuous and adapted before `T`, hull clause);
* the measurable field `h` and the pocket chart `c ω` (`c.1 = ψ`, `c.2.1 = ψ⁻¹`, `c.2.2` the inherited branch of
  `arg (ψ⁻¹)′`), conformal, `𝓖₀`-measurable, with a continuous lift;
* the **killed coupling clause in the pocket chart** (`IsChartCouplingCharFun` with lifetime `T`, the two-seed word
  and the (CPF2) weights `ρᴸ = θ₂χ/λ − 2`, `ρᴿ = −θ₁χ/λ − 2`), for constants `a`, `k` of the coordinate change
  (`h_ψ = h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′`, Lemma 7.1's setup).
The last item is p. 225's "history-locality statement of Lemma 6.2 … means … of the three-curve result in Remark 6.7
… two seed heights (CPF2), with the inherited logarithmic-derivative branch … time continuity … Proposition 6.5". -/
def Lemma71PocketChartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ : ℝ, θ₁ < 0 → 0 < θ₂ →
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓖 : Filtration ℝ≥0 mΩ) (_ : 𝓖.IsRightContinuous) (γ : Ω → ℝ → ℂ) (W : ℝ≥0 → Ω → ℝ)
      (T : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens) (c : Ω → Chart) (a k : ℝ),
      (∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) ∧
      (∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) Hbar ∧
        γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
        interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅) ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω}) ∧
      AdaptedBefore 𝓖 T W ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
        QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t)) ∧
      Measurable h ∧ (∀ ω, (c ω).IsConformal) ∧
      (∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P 𝓖 W
        (geomL W LP.twoSeedXL) (geomR W LP.twoSeedXR) T c a k h

/-- **`Lemma71KilledSegmentStatement` from the pocket coupling in chart form** (proof of Lemma 7.1, p. 225: the coupling
clause of the transported field gives the martingale clause of Theorem 2.4). The driver is unbounded at a finite
terminal capacity time by the elementary hull bound (`Lemma71B.unbounded_of_fwdHull_eq`), so its capped exit times
announce `T` and `hasMartingaleMeansBefore_of_isChartTransport` applies to the chart transport `h_ψ` of `h`.
Conditional helper: it replaces no source theorem. -/
theorem lemma71KilledSegmentStatement_of_pocketChart (hpc : Lemma71PocketChartStatement.{v}) :
    Lemma71KilledSegmentStatement.{v} := by
  intro κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  obtain ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, γ, W, T, h, c, a, k, hnull, hγ, hW0, hc, hWa, hK, hh, hcc, hdom, hfwd,
    hliftm, hliftc, hcf⟩ := hpc κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  refine ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, γ, W, T, hnull, hγ, hW0, hc, hWa, hK, ?_⟩
  have hunb : ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω| := by
    filter_upwards [hγ, hK] with ω hγω hKω
    obtain ⟨hγc, -, hγH, hγ0, hγinf, hγR⟩ := hγω
    exact unbounded_of_fwdHull_eq (hc ω) hγc hγH hγ0 hγinf hγR hKω
  exact hasMartingaleMeansBefore_of_isChartTransport (h' := fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω))
    hcc hdom hfwd hliftm hliftc hh hnull hW0 hc hWa hunb hcf fun ω =>
      Chart.isChartTransport_chartTransport (hcc ω)
        (Chart.locallyIntegrableOn_of_continuousOn ((hcc ω).continuousOn_lift_inv (hliftc ω))) 1 a k (h ω)

/-- `Lemma71.Lemma71MappedSegmentStatement` (the mapped segment with a global driver) from the pocket coupling in chart
form, through PROVE-LEMMA71B's `lemma71MappedSegmentStatement_of_killed` (the terminal capacity is infinite).
Conditional helper. -/
theorem lemma71MappedSegmentStatement_of_pocketChart (hpc : Lemma71PocketChartStatement.{v}) :
    Lemma71.Lemma71MappedSegmentStatement.{v} :=
  lemma71MappedSegmentStatement_of_killed (lemma71KilledSegmentStatement_of_pocketChart hpc)

/-- `Sec7.Lemma71TraceReferenceStatement` (the transient two-seed reference evolution of Lemma 7.1, consumed by
Proposition 7.3) from the pocket coupling in chart form. Conditional helper. -/
theorem lemma71TraceReferenceStatement_of_pocketChart (hpc : Lemma71PocketChartStatement.{v}) :
    Lemma71TraceReferenceStatement.{v} :=
  lemma71TraceReferenceStatement_of_killed (lemma71KilledSegmentStatement_of_pocketChart hpc)

/-! ### The curve form: the driver of the mapped segment is constructed -/

/-- **Named input, curve form: the three-curve pocket coupling** (Specification §7.1, pp. 221–222; proof of Lemma 7.1,
pp. 223–225; Remark 6.14, p. 218). As `Lemma71PocketChartStatement`, except that the driver and the terminal capacity
time are not data: they are the canonical driver `segDriver (γ ω)` of the mapped segment and its terminal capacity
time `capLife (γ ω)` (`Lemma71CClock.lean`). The requirements on them are replaced by:
* the geometric clause for every sample (`IsSegCurve`; modify `γ` on a null event of `𝓖₀` if needed);
* the filled prefixes of `γ` adapted at capacity times (`IsPrefixAdapted 𝓖 γ`: "the filtration retaining the complete
  outer curves" and the mapped middle prefix).
The remaining clauses (usual conditions, measurable field, `𝓖₀`-measurable pocket chart with a continuous lift, and the
killed coupling clause in the pocket chart with the (CPF2) weights) are those of `Lemma71PocketChartStatement`. -/
def Lemma71PocketCurveStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ : ℝ, θ₁ < 0 → 0 < θ₂ →
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓖 : Filtration ℝ≥0 mΩ) (_ : 𝓖.IsRightContinuous) (γ : Ω → ℝ → ℂ)
      (h : Ω → DistOn upperHalfPlaneOpens) (c : Ω → Chart) (a k : ℝ),
      (∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) ∧
      (∀ ω, IsSegCurve (γ ω)) ∧ IsPrefixAdapted 𝓖 γ ∧
      Measurable h ∧ (∀ ω, (c ω).IsConformal) ∧
      (∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P 𝓖
        (fun s ω => segDriver (γ ω) s) (geomL (fun s ω => segDriver (γ ω) s) LP.twoSeedXL)
        (geomR (fun s ω => segDriver (γ ω) s) LP.twoSeedXR) (fun ω => capLife (γ ω)) c a k h

/-- **The pocket coupling in chart form from its curve form**: the canonical driver of the mapped segment vanishes at
`0`, is continuous up to the terminal capacity time, has the filled prefixes as hulls (`IsSegCurve.segDriver_spec`) and
is adapted before the terminal capacity time (`adaptedBefore_segDriver`). Conditional helper. -/
theorem lemma71PocketChartStatement_of_pocketCurve (hpc : Lemma71PocketCurveStatement.{v}) :
    Lemma71PocketChartStatement.{v} := by
  intro κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  obtain ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, γ, h, c, a, k, hnull, hγ, hpre, hh, hcc, hdom, hfwd, hliftm, hliftc,
    hcf⟩ := hpc κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  refine ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, γ, fun s ω => segDriver (γ ω) s, fun ω => capLife (γ ω), h, c, a, k, hnull,
    Eventually.of_forall fun ω => hγ ω, fun ω => (hγ ω).segDriver_spec.1,
    fun ω => (hγ ω).segDriver_spec.2.1, adaptedBefore_segDriver hγ hpre,
    Eventually.of_forall fun ω => (hγ ω).segDriver_spec.2.2, hh, hcc, hdom, hfwd, hliftm, hliftc, hcf⟩

/-- **`Lemma71KilledSegmentStatement` from the curve form of the pocket coupling.** Conditional helper. -/
theorem lemma71KilledSegmentStatement_of_pocketCurve (hpc : Lemma71PocketCurveStatement.{v}) :
    Lemma71KilledSegmentStatement.{v} :=
  lemma71KilledSegmentStatement_of_pocketChart (lemma71PocketChartStatement_of_pocketCurve hpc)

/-- `Sec7.Lemma71TraceReferenceStatement` from the curve form of the pocket coupling. Conditional helper. -/
theorem lemma71TraceReferenceStatement_of_pocketCurve (hpc : Lemma71PocketCurveStatement.{v}) :
    Lemma71TraceReferenceStatement.{v} :=
  lemma71TraceReferenceStatement_of_pocketChart (lemma71PocketChartStatement_of_pocketCurve hpc)

end InteractingSLE.Sec7.Lemma71C
