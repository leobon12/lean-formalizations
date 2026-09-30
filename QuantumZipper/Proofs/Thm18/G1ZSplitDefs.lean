import QuantumZipper.Proofs.Thm18.G1ZoomPalmCov
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Thm18.G1G0Stmt
import QuantumZipper.Proofs.Thm18.G1Rescale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-SPLIT: the split of the zoom nodes A1, A, B2 of G1 (Theorem 1.8), decision D48

Plan: `handoff/G1-ZSPLIT.md`. Consumers: `G1RerootPathStmt` (A1), `G1RerootStmt` (A),
`G1PalmModelStmt` (B2) of `G1ZoomNodes.lean`.

## Sources

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71: "the configuration must be invariant under unzipping by a fixed quantity of
quantum length", the side surfaces are wedges "from Proposition 1.6"), and the proof of
Proposition 1.7 (pp. 25–26: rerooting at a point sampled from quantum length, zooming in by adding a
constant). Palm formula: Duplantier–Sheffield, arXiv:0808.1560, §3.3. Loewner flow cocycle:
Lawler, *Conformally invariant processes in the plane*, §4.

## A1 (pathwise rerooting) = A1a + A1b + A1c (+ the proved lemma `g1SidePt_eq_of_len`)

With `c = (Y, W)`, `t' = unzipTime γ ℓ c`, `a = unzipScale γ ℓ c`, `W' = (zipLenDown γ ℓ c).2 =
g1zNewDrv W t' a`, `ψ = g1zSideMap left W`, `ψ' = g1zSideMap left W'`:
* **A1a** `G1RerootAffineStmt` (deterministic Loewner/Carathéodory geometry): the composite
  `u ↦ f_{t'}⁻¹(a ψ'(u + β))` is `u ↦ ψ(u/λ)` on `ℍ` (a conformal self-map of `ℍ` fixing `∞` is
  affine), where `β` is the boundary preimage under `a ψ'` of the side image `O^∓_{t'}` of the old
  root; and `W'` again has a simple trace generating its hulls.
* **A1b** `G1RerootRegStmt` (a.s. field cocycle): given the map identity of A1a, the canonical
  data of the old side field equal those of the new side field translated to `β`.
* **A1c** `G1RerootLenStmt` (a.s. lengths): `t' > 0`, `a > 0`, and the new side boundary measure gives
  `[β, 0]` (resp. `[0, β]`) length `ℓ` and charges open intervals (so `g1SidePt ℓ = β`,
  `g1SidePt_eq_of_len`). Uses `LenEqStmt` on the right side.

## A (rerooting invariance) = E6 + A1 + A2

* **A2** `G1RerootFactorStmt`: the rerooted and the plain canonical side data factor measurably
  through the configuration data `g1zCfgData c = (dataFull h, W|[0,∞))` read by `configLawFull`, on a
  measurable set of full measure, for every configuration with a continuous, simple, hull-generating
  driver (the form of `G1RegGood`/`G1BdryGood`; a condition on continuity cannot be a measurable set
  of paths, `G1PathNoGo.lean`).

## B2 (Palm zoom model) = B2-C + B2-R + B2-Z, B2-Z = Z1 + Z2

* **B2-C** `G1SideConstInvStmt`: the canonical side data have the same law after adding a constant
  (wedge and SLE scale invariance, independence).
* **B2-R** `G1PalmConstStmt`: A + B1 for the functionals `Γ(loc(canonical(· + C)))`.
* **Z1** `G1PalmToWedgeStmt`: change of variables to the wedge boundary: the Palm-window integral of
  the side field is the Palm-window integral of `Y` of the zooms through the local maps `g1zLocMap`.
* **Z2** `G1WedgePalmZoomStmt`: the weighted ε-approximate D3⁺ model mixture for the latter,
  uniformly in the level `L` (`G1WApproxSeq`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus

/-! ## Objects -/

/-- The inverse side uniformizer `ψ = (uniformizer D)⁻¹ : ℍ → D` of the driver `W`. -/
def g1zSideMap (left : Bool) (W : ℝ → ℝ) : ℂ → ℂ :=
  invFunOn (uniformizer (sideDom (trace W) left)) (sideDom (trace W) left)

/-- The driver after unzipping by capacity time `t` and Brownian rescaling by `a`. -/
def g1zNewDrv (W : ℝ → ℝ) (t a : ℝ) : ℝ → ℝ :=
  fun s => (W (t + a ^ 2 * max s 0) - W t) / a

/-- The side image `O⁻_t` (left) / `O⁺_t` (right) of the root. -/
def g1zSideImage (left : Bool) (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  if left then (sideImages W t).1 else (sideImages W t).2

/-- The configuration data read by `configLawFull` (`lawData` of the field is `dataFull H`). -/
def g1zCfgData (c : FieldSample × (ℝ → ℝ)) : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) :=
  (WedgeMeas.dataFull H c.1, fun t : ℝ≥0 => c.2 t)

/-- The rerooted local canonical side functional of a configuration. -/
def g1zRerootF (γ : ℝ) (left : Bool) (ℓ : ℝ) (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) (c : FieldSample × (ℝ → ℝ)) : ℝ≥0∞ :=
  Γ (locFieldFull R (canonical γ (translate (g1CfgSideField γ left c)
    (g1SidePt γ left (g1CfgSideField γ left c) ℓ : ℂ))))

/-- The deterministic driver conditions (continuity, normalization, simple trace generating
the hulls). -/
def G1zDrvGood (W : ℝ → ℝ) : Prop :=
  Continuous W ∧ W 0 = 0 ∧ (∀ s, W s = W (max s 0)) ∧ IsSimpleChord (trace W) ∧
    ∀ t : ℝ, 0 ≤ t → fwdHull W t = trace W '' Ioc 0 t

/-! ## A1: the pathwise rerooting identity -/

/-- **A1a (deterministic geometry).** For a good driver, `t > 0`, `a > 0`: the unzipped and
rescaled driver is good, and there are `λ > 0` and `β` in the side half-line with
`f_t⁻¹(a ψ'(u + β)) = ψ(u/λ)` on `ℍ` and `a ψ'(u) → O^∓_t` as `u → β` in `ℍ`. -/
def G1RerootAffineStmt : Prop :=
  ∀ W : ℝ → ℝ, G1zDrvGood W → ∀ t a : ℝ, 0 < t → 0 < a → ∀ left : Bool,
    G1zDrvGood (g1zNewDrv W t a) ∧
    ∃ lam β : ℝ, 0 < lam ∧ β ∈ g1SideHalf left ∧
      EqOn (fun u => fwdMapInv W t ((a : ℂ) * g1zSideMap left (g1zNewDrv W t a) (u + β)))
        (fun u => g1zSideMap left W (u / lam)) H ∧
      Tendsto (fun u => (a : ℂ) * g1zSideMap left (g1zNewDrv W t a) u) (𝓝[H] (β : ℂ))
        (𝓝 (g1zSideImage left W t : ℂ))

/-! ## A2: measurable factorization through the configuration law -/

/-- **A2 (measurable factorization).** For `ℓ > 0` and measurable `Γ ∈ [0,1]`: measurable maps
`G` (rerooted functional) and `G₀` (plain canonical side data) on the configuration-data space,
and a measurable set `E` of full measure for the wedge configuration, such that for every
configuration with data in `E` and a good driver the functionals are given by `G`, `G₀`. -/
def G1RerootFactorStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ ℓ : ℝ, 0 < ℓ → ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ →
      (∀ y, Γ y ≤ 1) →
      ∃ (G : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ≥0∞)
        (G₀ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → (ℕ → ℝ) × (TestFun H → ℝ))
        (E : Set (((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ))),
        Measurable G ∧ Measurable G₀ ∧ MeasurableSet E ∧
        (∀ c : FieldSample × (ℝ → ℝ), g1zCfgData c ∈ E → G1zDrvGood c.2 →
          g1zRerootF γ left ℓ R Γ c = G (g1zCfgData c) ∧
          WedgeMeas.dataFull H (canonical γ (g1CfgSideField γ left c)) = G₀ (g1zCfgData c)) ∧
        ∀ᵐ ω ∂P, g1zCfgData (wedgeConfig γ B Y ω) ∈ E

/-! ## B2: the Palm zoom model -/

/-- The Palm-window integral with the constant `C` added after rerooting. -/
def g1PalmIntC (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → FieldSample)
    (left : Bool) (U C : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ b in g1Win γ left (Z ω) U,
    Γ (locFieldFull R (canonical γ (addConst (translate (Z ω) (b : ℂ)) C)))
      ∂(g1SideNu γ left (Z ω)) ∂P

/-- `G1WApproxAt` with a level-dependent target `a L` (the target is compared at the same level
`L` as the models). -/
def G1WApproxSeq (γ : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) (ε : ℝ≥0∞)
    (a : ℝ → ℝ≥0∞) : Prop :=
  ∃ (T : Type) (_ : MeasurableSpace T) (ρ : Measure T) (r : T → ℝ) (ρ₀ : T → Measure ℂ)
    (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (X : T → Ω₀ → FieldSample)
    (E' : Type) (_ : MeasurableSpace E') (Ξ : T → Ω₀ → E') (g : T → Ω₀ → ℂ → ℝ)
    (w : T → Ω₀ → ℝ≥0∞) (M : ℝ≥0),
    IsFiniteMeasure ρ ∧ IsProbabilityMeasure P₀ ∧
    (∀ x, Setup γ γ (r x) (ρ₀ x) P₀ (X x) (Ξ x) (g x)) ∧
    (∀ x, Measurable[condSigma (Ξ x) (X x) (r x)] (w x)) ∧ (∀ x ω, w x ω ≤ M) ∧
    (∀ L, AEMeasurable (fun x => g1zWMdl γ (r x) L R (ρ₀ x) P₀ (X x) (g x) (w x) Γ) ρ) ∧
    AEMeasurable (fun x => ∫⁻ ω, w x ω ∂P₀) ρ ∧
    ∫⁻ x, ∫⁻ ω, w x ω ∂P₀ ∂ρ ≤ 1 + ε ∧ 1 ≤ ∫⁻ x, ∫⁻ ω, w x ω ∂P₀ ∂ρ + ε ∧
    ∀ᶠ L in atTop,
      ∫⁻ x, g1zWMdl γ (r x) L R (ρ₀ x) P₀ (X x) (g x) (w x) Γ ∂ρ ≤ a L + ε ∧
        a L ≤ ∫⁻ x, g1zWMdl γ (r x) L R (ρ₀ x) P₀ (X x) (g x) (w x) Γ ∂ρ + ε

/-- A constant target: `G1WApproxSeq` is `G1WApproxAt`. -/
theorem g1WApproxAt_of_seq_const {γ : ℝ} {R : ℕ} {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞}
    {ε a : ℝ≥0∞} (h : G1WApproxSeq γ R Γ ε fun _ => a) : G1WApproxAt γ R Γ ε a := h

/-- **B2-C (additive constants).** The law of the canonical side data does not change when a
constant is added to the side field (the `(γ−2/γ)`-wedge is invariant in law under adding
constants modulo rescaling, the SLE is scale invariant and independent of it). -/
def G1SideConstInvStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ C : ℝ,
    ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      ∫⁻ ω, Γ (locFieldFull R (canonical γ (addConst (g1SideField γ B Y left ω) C))) ∂P =
        ∫⁻ ω, Γ (locFieldFull R (canonical γ (g1SideField γ B Y left ω))) ∂P

/-- **B2-R (Palm rerooting with a constant).** The normalized Palm-window integral of the
functional `Γ(loc(canonical(· + C)))` is its plain expectation (A and B1 for this functional). -/
def G1PalmConstStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ U : ℝ, 0 < U → ∀ C : ℝ,
    ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      (ENNReal.ofReal U)⁻¹ * g1PalmIntC γ P (g1SideField γ B Y left) left U C R Γ =
        ∫⁻ ω, Γ (locFieldFull R (canonical γ (addConst (g1SideField γ B Y left ω) C))) ∂P

open Classical in
/-- The boundary preimage under `ψ = g1zSideMap left W` of a real point `x` of the side
half-line (junk `0` if there is none). -/
noncomputable def g1zBdryPre (left : Bool) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  if h : ∃ b ∈ g1SideHalf left, Tendsto (g1zSideMap left W) (𝓝[H] (b : ℂ)) (𝓝 (x : ℂ)) then
    h.choose else 0

/-- The local conformal map at the wedge boundary point `x`: `w ↦ ψ(ψ⁻¹(x) + w) − x`. -/
def g1zLocMap (left : Bool) (W : ℝ → ℝ) (x : ℝ) : ℂ → ℂ :=
  fun w => g1zSideMap left W (w + (g1zBdryPre left W x : ℂ)) - (x : ℂ)

/-- The Palm window of the wedge field on the side half-line. -/
def g1zWedgeWin (γ : ℝ) (left : Bool) (y : FieldSample) (U : ℝ) : Set ℝ :=
  {x | x ∈ g1SideHalf left ∧ qBoundaryMeasure γ y (g1SideSeg left x) ≤ ENNReal.ofReal U}

/-- The Palm-window integral of the wedge `Y` of the zooms at level `L` through the local maps. -/
def g1zWedgePalmInt (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) (left : Bool) (U L : ℝ) (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ x in g1zWedgeWin γ left (Y ω) U,
    Γ (locFieldFull R (canonical γ
      (zoomFieldVia γ L (Y ω) x (g1zLocMap left (drive (γ ^ 2) B ω) x))))
      ∂((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf left)) ∂P

/-- **Z1 (change of variables to the wedge boundary).** The Palm-window integral of the side
field with constant `C` equals the Palm-window integral of `Y` of the zooms at level `γ C` through
the local maps (identified boundary transport of B0, `ν_side = ν_Y ∘ ψ`, and the field identity
`translate (Y ∘ ψ) b ≈ Y(x + g1zLocMap x (·))`, `x = ψ(b)`). -/
def G1PalmToWedgeStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ U : ℝ, 0 < U → ∀ C : ℝ,
    ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      g1PalmIntC γ P (g1SideField γ B Y left) left U C R Γ =
        g1zWedgePalmInt γ P B Y left U (γ * C) R Γ

/-- **Z2 (Palm zoom of the wedge through the local maps).** For every `ε > 0` some window `U`
has a weighted `ε`-approximate D3⁺ model mixture of the normalized wedge Palm-window
integrals, level by level (Palm formula DS11 §3.3 for the wedge boundary measure; fixed-point
zoom of Prop. 1.6 through the local maps, as G0; weights conditioned at a small radius). -/
def G1WedgePalmZoomStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ U : ℝ, 0 < U ∧
      G1WApproxSeq γ R Γ ε fun L => (ENNReal.ofReal U)⁻¹ * g1zWedgePalmInt γ P B Y left U L R Γ

end Thm18Asm
end QuantumZipper
