/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Provider.exists_isOptionalHullCoupling
import InteractingSLE.Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData
import InteractingSLE.Spec.Theorem15Inputs
import InteractingSLE.Frozen.Spec.IsFlowLine

/-!
# Existence of flow lines (`exists_isFlowLine`, Theorem 1.5's companion) from Theorems 1.1–1.3

Packet PROVE-FLOWEXIST, goal 1. The frozen `exists_isFlowLine` (R26) asks, for a GFF `h` on `ℍ` with finite
piecewise-constant data `b` on **any** probability space, for its angle-`θ` flow line from `x` on that same space.
Route (packet; AUD-3c N1; ARCH-3b §7.2):

1. the chart `z ↦ z − x` and the angle: `h' = h(· + x) + θχ` (`Exist.flowField`); it is a GFF with the force-word
   data of the flow-line word (`Exist.isGFFWithBoundaryData_flowField`);
2. a reference coupling of the flow-line word (Theorem 1.1, sealed provider); its field has the law of `h'`
   (`Exist.map_eq_of_isGFFWithBoundaryData`);
3. the reference driving history is a Borel function `Ψ` of the field, with a closed generating trace at every point
   of a Borel full-measure set of fields (`Exist.exists_fieldDetermination`, from Theorems 1.2 and 1.3);
4. **realization** on the given space: the processes `Ψ(h')` with a filtration and a Brownian motion are an integrated
   evolution (`BrownianRealizationStatement`, **named input (ii)**) and then an optional hull coupling with `h'`
   (`HullClauseTransferStatement`, **named input (i)**);
5. the trace: `h'` lies in the Borel set almost surely (same law), so `η = x + ηf(h')` is the flow line.

**`exists_isFlowLine_of_thm12_thm13`** (provider shape, conditional helper): the frozen statement of
`exists_isFlowLine` from Theorem 1.2, Theorem 1.3 (exactly their frozen types) and the two named inputs.

## The remaining named inputs (AUD-3c N1)

Both assume a *realization datum* (`IsFieldRealizationDatum`): a reference optional hull coupling whose killed driving
history is a Borel function `Ψ` of its field, and a field `h` with the reference field law on the target space.

* (i) `HullClauseTransferStatement`: given any integrated evolution `(𝓕, Ψ(h), B)` on the target space, the field
  clauses (GFF clause and the conditional law at every stopping time `τ < ζ` of the usual augmentation of the
  killed-history filtration) hold there. Pure law transfer; its proof needs Doob–Dynkin for stopping times of the
  augmented filtration of `Ψ(h)` (every such `τ` is almost surely `τ₀(h)`, as `Coupling.CompactTransfer` does for
  `Prod.fst`) and Borel measurability of the right-hand side of the conditional-law clause (Loewner energy, coupling
  mean, hull disjointness) as a function of the history code, so that the almost-sure identity moves between spaces.
* (ii) `BrownianRealizationStatement`: some `(𝓕, B)` makes `(Ψ(h), B)` an integrated evolution. Before the lifetime
  `B` is read off the driving equation (its law is the reference one); after a finite lifetime it is continued by a
  Brownian motion built from the field and independent of the killed history (conditional atomlessness of a test
  pairing of the field given the history: the conditional Gaussian law at an announcing sequence `τₙ ↑ ζ`,
  `Coupling.AnnounceLifetime`, and Lévy upward convergence), concatenated by the strong Markov restart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

open Sec2.Assembly

/-- The hypotheses shared by the two realization inputs: an optional hull coupling `(h₀, W₀, V₀, B₀, ζ₀)` of an
ordered force word whose killed driving history is a Borel function `Ψ` of its field (`Ψ(h₀) = (ζ₀, W₀, V₀)` before
`ζ₀`, almost surely), and a measurable field `h` on a probability space `(Ω, P)` with the law of `h₀`. -/
def IsFieldRealizationDatum (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (Ψ : LQGMetric.DistOn upperHalfPlaneOpens →
      ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  0 < κ ∧ IsOrderedForceWord xL xR ∧ Measurable Ψ ∧ Measurable h ∧
    ∃ (Ω₀ : Type u) (mΩ₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ)
      (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞)
      (h₀ : Ω₀ → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ ∧
      (∀ᵐ ω ∂P₀, (Ψ (h₀ ω)).1 = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
        (Ψ (h₀ ω)).2.1 t = W₀ t ω ∧ (∀ i, (Ψ (h₀ ω)).2.2.1 i t = VL₀ i t ω) ∧
          ∀ j, (Ψ (h₀ ω)).2.2.2 j t = VR₀ j t ω) ∧
      P.map h = P₀.map h₀

/-- **Named input (i): the field clauses of the optional hull specification transfer along the field law.** For a
realization datum (`IsFieldRealizationDatum`), whenever the processes `Ψ(h)` together with some filtration `𝓕` and some
`B` form an integrated `SLE_κ(ρ)` evolution on `(Ω, P)`, they form an optional hull coupling with `h`. (Pure law
transfer: the field clauses involve only the joint law of `h` and the killed history `Ψ(h)`, which is the reference
one.) -/
def HullClauseTransferStatement : Prop :=
  ∀ (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (Ψ : LQGMetric.DistOn upperHalfPlaneOpens →
      ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ))
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsFieldRealizationDatum κ xL xR ρL ρR Ψ P h →
    ∀ (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 (fun t ω => (Ψ (h ω)).2.1 t)
        (fun i t ω => (Ψ (h ω)).2.2.1 i t) (fun i t ω => (Ψ (h ω)).2.2.2 i t) B (fun ω => (Ψ (h ω)).1) →
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 (fun t ω => (Ψ (h ω)).2.1 t)
        (fun i t ω => (Ψ (h ω)).2.2.1 i t) (fun i t ω => (Ψ (h ω)).2.2.2 i t) B (fun ω => (Ψ (h ω)).1) h

/-- **Named input (ii): the driving evolution is realized on any space carrying the field** (AUD-3c N1). For a
realization datum, there are a filtration `𝓕` and a Brownian motion `B` on `(Ω, P)` such that the processes `Ψ(h)` and
`B` form an integrated `SLE_κ(ρ)` evolution. Before the lifetime `B` is read off the driving equation; after a finite
lifetime it continues as a Brownian motion built from the field's own randomness, independent of the killed history. -/
def BrownianRealizationStatement : Prop :=
  ∀ (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (Ψ : LQGMetric.DistOn upperHalfPlaneOpens →
      ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ))
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsFieldRealizationDatum κ xL xR ρL ρR Ψ P h →
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 (fun t ω => (Ψ (h ω)).2.1 t)
        (fun i t ω => (Ψ (h ω)).2.2.1 i t) (fun i t ω => (Ψ (h ω)).2.2.2 i t) B (fun ω => (Ψ (h ω)).1)

/-- The history paths of a code: lifetime, driver, left and right force points. -/
def pathsOfCode {nL nR : ℕ} (x : XCode nL nR) :
    ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ) :=
  (cζ x, cw x, cvL x, cvR x)

theorem measurable_pathsOfCode {nL nR : ℕ} : Measurable (pathsOfCode (nL := nL) (nR := nR)) :=
  measurable_cζ.prodMk (measurable_cw.prodMk
    ((measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun t => measurable_cvL_at i t).prodMk
      (measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun t => measurable_cvR_at j t)))

/-- **Existence of flow lines** (the frozen `exists_isFlowLine`, Theorem 1.5's non-vacuity companion), in the provider
shape (all of the anchor's arguments implicit, its hypotheses auto-parameters), from Theorem 1.2 and Theorem 1.3
(exactly their frozen types) and the named inputs `HullClauseTransferStatement` and `BrownianRealizationStatement`
(conditional helper; it is not the provider). Theorem 1.1 enters through its sealed provider. -/
theorem exists_isFlowLine_of_thm12_thm13 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (hHull : HullClauseTransferStatement.{u}) (hBM : BrownianRealizationStatement.{u}) {κ : ℝ}
    (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ := by
  have _ := hκ4
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps x
  -- the reference coupling of the flow-line word (Theorem 1.1)
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup⟩ :=
    Spec.Provider.exists_isOptionalHullCoupling.{u} (κ := κ) (xL := flowLineXL b jumps x)
      (xR := flowLineXR b jumps x) (ρL := flowLineRhoL κ b jumps x θ) (ρR := flowLineRhoR κ b jumps x θ) hκ hF
  -- the history is a Borel function of the field (Theorems 1.2 and 1.3)
  obtain ⟨Ψ, S, ηf, hΨm, hSm, hae, htr⟩ := exists_fieldDetermination h12 h13 hκ hF hcoup
  -- the flow-line field and its law
  set h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens :=
    fun ω => flowField x (θ * QuantumZipper.chiC κ) (h ω) with hh'def
  have hh' := isGFFWithBoundaryData_flowField hκ hb x θ hh
  obtain ⟨u, hu, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := flowLineRhoL κ b jumps x θ) (ρR := flowLineRhoR κ b jumps x θ) (vL := flowLineXL b jumps x)
    (vR := flowLineXR b jumps x)
  have hh₀ : IsGFFWithBoundaryData P₀ h₀
      (forceBoundaryData κ (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) (flowLineXL b jumps x)
        (flowLineXR b jumps x)) (forceJumpSet (flowLineXL b jumps x) (flowLineXR b jumps x)) :=
    ⟨hcoup.2.1, hcoup.2.2.1⟩
  have hlaw : P.map h' = P₀.map h₀ := map_eq_of_isGFFWithBoundaryData hh' hh₀ hu
  -- realization on the given space
  have hdet : ∀ᵐ ω ∂P₀, (pathsOfCode (Ψ (h₀ ω))).1 = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
      (pathsOfCode (Ψ (h₀ ω))).2.1 t = W₀ t ω ∧ (∀ i, (pathsOfCode (Ψ (h₀ ω))).2.2.1 i t = VL₀ i t ω) ∧
        ∀ j, (pathsOfCode (Ψ (h₀ ω))).2.2.2 j t = VR₀ j t ω := by
    filter_upwards [hae] with ω hω
    exact ⟨hω.2.1, hω.2.2⟩
  have hdatum : IsFieldRealizationDatum κ (flowLineXL b jumps x) (flowLineXR b jumps x)
      (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) (pathsOfCode ∘ Ψ) P h' :=
    ⟨hκ, hF, measurable_pathsOfCode.comp hΨm, hh'.1, Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup,
      hdet, hlaw⟩
  obtain ⟨𝓕, B, hE⟩ := hBM κ _ _ _ _ (pathsOfCode ∘ Ψ) P h' hdatum
  have hcoupΩ := hHull κ _ _ _ _ (pathsOfCode ∘ Ψ) P h' hdatum 𝓕 B hE
  -- the field lies in the good set almost surely
  have hS₀ : ∀ᵐ f ∂(P₀.map h₀), f ∈ S :=
    (ae_map_iff hcoup.2.1.aemeasurable hSm).2 (hae.mono fun ω hω => hω.1)
  rw [← hlaw] at hS₀
  have hSΩ : ∀ᵐ ω ∂P, h' ω ∈ S := (ae_map_iff hh'.1.aemeasurable hSm).1 hS₀
  refine ⟨fun ω t => ηf (h' ω) t + x, fun ω => cζ (Ψ (h' ω)), h', 𝓕, _, _, _, B,
    fun ω => isTranslateAddConst_flowField x _ (h ω), hcoupΩ, ?_⟩
  filter_upwards [hSΩ] with ω hω
  have e : (fun t => ηf (h' ω) t + (x : ℂ) - x) = ηf (h' ω) := by
    funext t; ring
  rw [e]
  exact htr _ hω

end Exist

end InteractingSLE
