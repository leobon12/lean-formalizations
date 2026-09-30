import QuantumZipper.Proofs.Thm18.G1ZoomWeighted
import QuantumZipper.Statements.Prop17
import QuantumZipper.Proofs.Thm18.G3ConcreteMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-ZOOM: the nodes of the zoom half of G1 and the top-level reduction

Theorem 1.8, node G1, part (a) (`G1ZoomPartStmt`): each side surface of the SLE-decorated
`(γ − 2/γ)`-quantum wedge is a `γ`-quantum wedge. Plan and task list: `handoff/G1-ZOOM.md`.

## Route (sources)

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, pp. 69–71): the side surfaces are
`γ`-wedges "for the left side from Proposition 1.6 and for the right side by symmetry"; the
configuration "must be invariant under unzipping by a fixed quantity of quantum length as
measured along the left of the two γ quantum wedges" because the collision point "was sampled
uniformly from quantum measure" (p. 70, cf. the proof of Prop. 1.7, pp. 25–26). In this project
the length-unzip invariance is E6 (`Thm13Asm.E6Stmt`, `configLawFull (zipLenDown γ ℓ ∘ c) =
configLawFull c` for `P_*` samples, Thm 1.3 chain), and the Prop. 1.6 zoom is D3⁺(i). The steps:

* **(A) rerooting invariance** (`G1RerootStmt`). Unzipping by left length `ℓ` sends the old root
  `0` to the boundary point `x₋` with `ν[x₋,0] = ℓ` (`0⁺` to `x₊` with `ν[0,x₊] = ℓ`, using F1
  for the right side), and the old side component is the new one re-rooted there: pathwise
  (`G1RerootPathStmt`), the canonical side field equals the canonical side field of
  `zipLenDown γ ℓ c` translated to `g1SidePt`. With E6 (and F1) this gives law invariance of the
  canonical side surface under rerooting by `ℓ` along its real boundary (the analogue of Prop 1.7
  for the side surface).
* **(B1) Palm average** (`G1PalmAvgStmt`): `ℓ ↦ g1SidePt ℓ` pushes Lebesgue measure on `(0,U]`
  to the side boundary measure on the window `{ν[b,0] ≤ U}`; Fubini.
* **(B2) Palm zoom model** (`G1PalmModelStmt`): for each `ε`, for a small window `U`, the
  Palm-weighted rerooted integral is `ε`-approximated by a weighted mixture of D3⁺ models (Palm formula for the free field,
  Duplantier–Sheffield arXiv:0808.1560 §3.3; local absolute continuity of the wedge w.r.t. the
  free field away from `0`; conformal invariance and Markov property of the free boundary GFF;
  locality of `canonical` at large level).
* **(Z) wedge law**: `isQuantumWedge_of_wapprox` (G1ZoomWeighted.lean) from D3⁺(i).

`g1ZoomPartStmt_of_nodes : D3PlusIStmtRich → G1RerootStmt → G1PalmAvgStmt → G1PalmModelStmt →
G1ZoomPartStmt` is proved here (own bookkeeping: `∫_{(0,U]}` of a constant, then (Z)).
`G1SideBdryRegStmt` and `G1RerootPathStmt` are stated for the owners of (A) and (B1).

Why not `G1ZoomModelStmt` (G1ZoomModel.lean): its mixture is exact and unweighted, but the Palm
average has the window weight `1{ν[b,0] ≤ U}` and the local density of the `(γ − 2/γ)`-wedge
w.r.t. the free field near `b ≠ 0`, neither `condSigma`-measurable; hence the weighted,
`ε`-approximate interface `G1WApproxAt` / `G1ZoomWApproxT`.

Boundary measures are taken with `qBoundaryMeasureOn` on the open real half-line of the side
(`g1SideHalf`), because on the curve side `(0,∞)` (left) the global `qBoundaryMeasure` of the
pulled-back field is not known to exist before G1 is proved (it would be junk `0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus

/-! ## The objects -/

/-- The side field of a configuration `c = (h, W)`: `h ∘ ψ + Q log|ψ'|` with
`ψ = (uniformizer D)⁻¹`, `D` the side component of `ℍ \ trace W`. -/
def g1CfgSideField (γ : ℝ) (left : Bool) (c : FieldSample × (ℝ → ℝ)) : FieldSample :=
  coordChange c.1 (invFunOn (uniformizer (sideDom (trace c.2) left)) (sideDom (trace c.2) left))
    (Qc γ)

/-- The side field of the Theorem 1.8 configuration. -/
def g1SideField (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) (left : Bool) (ω : Ω) : FieldSample :=
  g1CfgSideField γ left (wedgeConfig γ B Y ω)

/-- The open real half-line bounding the side surface next to its root: `(−∞,0)` for the left
side, `(0,∞)` for the right side. -/
def g1SideHalf (left : Bool) : Set ℝ := if left then Iio 0 else Ioi 0

/-- The boundary segment between the root `0` and `b`. -/
def g1SideSeg (left : Bool) (b : ℝ) : Set ℝ := if left then Icc b 0 else Icc 0 b

/-- The side boundary measure: the local quantum boundary measure on `g1SideHalf left`. -/
def g1SideNu (γ : ℝ) (left : Bool) (x : FieldSample) : Measure ℝ :=
  qBoundaryMeasureOn γ x (g1SideHalf left)

/-- The new root after rerooting by quantum length `ℓ` along the real boundary, with
`ν = g1SideNu`: `lenLeft ν ℓ = −inf {y > 0 : ℓ ≤ ν[−y,0]}` (left),
`lenRight ν ℓ = inf {y > 0 : ℓ ≤ ν[0,y]}` (right) (the quantile maps of G3ConcreteMaps.lean;
`map_lenLeft_restrict_Ioc` in G2FullMixCampbell.lean is the quantile transform for B1). -/
def g1SidePt (γ : ℝ) (left : Bool) (x : FieldSample) (ℓ : ℝ) : ℝ :=
  if left then lenLeft (g1SideNu γ left x) ℓ else lenRight (g1SideNu γ left x) ℓ

/-- The Palm window: boundary points of the side half-line within quantum length `U` of the
root. -/
def g1Win (γ : ℝ) (left : Bool) (x : FieldSample) (U : ℝ) : Set ℝ :=
  {b | b ∈ g1SideHalf left ∧ g1SideNu γ left x (g1SideSeg left b) ≤ ENNReal.ofReal U}

/-- `E Γ(local data of the canonical field rerooted by quantum length ℓ)`. -/
def g1RerootInt (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → FieldSample)
    (left : Bool) (ℓ : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, Γ (locFieldFull R (canonical γ (translate (Z ω) (g1SidePt γ left (Z ω) ℓ : ℂ)))) ∂P

/-- The Palm-window integral `E ∫_{window} Γ(local data of canonical (Z(· + b))) ν(db)`. -/
def g1PalmInt (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → FieldSample)
    (left : Bool) (U : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ b in g1Win γ left (Z ω) U,
    Γ (locFieldFull R (canonical γ (translate (Z ω) (b : ℂ)))) ∂(g1SideNu γ left (Z ω)) ∂P

/-! ## The nodes -/

/-- **Node B0 (boundary regularity of the side field)**, input of (A) and (B1): a.s. the side
boundary measure has no atoms, charges every nondegenerate interval of the side half-line,
is finite on every segment from the root, and has infinite total mass. -/
def G1SideBdryRegStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ᵐ ω ∂P, (∀ t : ℝ, g1SideNu γ left (g1SideField γ B Y left ω) {t} = 0) ∧
      (∀ u v : ℝ, u < v → Ioo u v ⊆ g1SideHalf left →
        0 < g1SideNu γ left (g1SideField γ B Y left ω) (Ioo u v)) ∧
      (∀ b ∈ g1SideHalf left, g1SideNu γ left (g1SideField γ B Y left ω) (g1SideSeg left b) < ⊤) ∧
      g1SideNu γ left (g1SideField γ B Y left ω) (g1SideHalf left) = ⊤

/-- **Node A (rerooting invariance of the side surface)**: the canonical side data are
a.e.-measurable, and for every `ℓ > 0` rerooting by quantum length `ℓ` along the real boundary
does not change the integrals of the local canonical data. (To be proved from E6, F1,
`G1RerootPathStmt` and a measurable factorization through `configLawFull`; see the handoff.) -/
def G1RerootStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    AEMeasurable (fun ω => WedgeMeas.dataFull H (canonical γ (g1SideField γ B Y left ω))) P ∧
    ∀ ℓ : ℝ, 0 < ℓ → ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ →
      (∀ y, Γ y ≤ 1) →
      g1RerootInt γ P (g1SideField γ B Y left) left ℓ R Γ =
        ∫⁻ ω, Γ (locFieldFull R (canonical γ (g1SideField γ B Y left ω))) ∂P

/-- **Node B1 (Palm average, change of variables)**: averaging the rerooted integrals over
`ℓ ∈ (0,U]` is the Palm-window integral against the side boundary measure. -/
def G1PalmAvgStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ U : ℝ, 0 < U → ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ →
      (∀ y, Γ y ≤ 1) →
      ∫⁻ ℓ in Ioc 0 U, g1RerootInt γ P (g1SideField γ B Y left) left ℓ R Γ =
        g1PalmInt γ P (g1SideField γ B Y left) left U R Γ

/-- **Node B2 (Palm zoom model)**: for every `R`, measurable `Γ ∈ [0,1]` and `ε > 0` there is a
window `U > 0` (small windows keep the Palm points inside the unit half-disc, where the
`(γ − 2/γ)`-wedge is exactly a free field plus `(γ − 2/γ)(−log|·|)`) such that the normalized
Palm-window integral `U⁻¹ · g1PalmInt` is `ε`-approximated by a weighted mixture of D3⁺ models
(`G1WApproxAt`). -/
def G1PalmModelStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ U : ℝ, 0 < U ∧
      G1WApproxAt γ R Γ ε ((ENNReal.ofReal U)⁻¹ * g1PalmInt γ P (g1SideField γ B Y left) left U R Γ)

/-! ## The reduction -/

/-- A constant integrand on `(0,U]`, normalized. -/
theorem g1z_inv_mul_setLIntegral_const {U : ℝ} (hU : 0 < U) (a : ℝ≥0∞) :
    (ENNReal.ofReal U)⁻¹ * ∫⁻ _ℓ in Ioc (0 : ℝ) U, a = a := by
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm a, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hU).ne' ENNReal.ofReal_ne_top, one_mul]

/-- **One side**: (A), (B1), (B2) and D3⁺(i) give the wedge law of the side surface, for the
uniformizer chosen in `componentSurface`. -/
theorem g1ZoomPartSide_of_nodes (hD3 : D3PlusIStmtRich) (hA : G1RerootStmt)
    (hB1 : G1PalmAvgStmt) (hB2 : G1PalmModelStmt) {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (left : Bool) :
    G1ZoomPartSide γ P B Y left := by
  obtain ⟨hmeas, hrr⟩ := hA γ P B Y hS hIn left
  have happ : G1ZoomWApprox γ P (g1SideField γ B Y left) := by
    intro R Γ hΓ hΓ1 ε hε
    obtain ⟨U, hU, hap⟩ := hB2 γ P B Y hS hIn left R Γ hΓ hΓ1 ε hε
    have hkey : (ENNReal.ofReal U)⁻¹ * g1PalmInt γ P (g1SideField γ B Y left) left U R Γ =
        ∫⁻ ω, Γ (locFieldFull R (canonical γ (g1SideField γ B Y left ω))) ∂P := by
      rw [← hB1 γ P B Y hS hIn left U hU R Γ hΓ hΓ1,
        setLIntegral_congr_fun measurableSet_Ioc (fun ℓ hℓ => hrr ℓ hℓ.1 R Γ hΓ hΓ1)]
      exact g1z_inv_mul_setLIntegral_const hU _
    show G1WApproxAt γ R Γ ε
      (∫⁻ ω, Γ (locFieldFull R (canonical γ (g1SideField γ B Y left ω))) ∂P)
    rw [← hkey]
    exact hap
  have hW := isQuantumWedge_of_wapprox hD3 hS.1 hS.2.1 hmeas happ
  refine ⟨fun ω => invFunOn (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left))
    (sideDom (sleTrace (γ ^ 2) B ω) left), ?_, hW⟩
  filter_upwards [hIn.2.2] with ω hω
  refine ⟨_, ?_, rfl⟩
  cases left
  · exact hω.2.2.2
  · exact hω.2.2.1

/-- **G1 zoom half from its nodes**: D3⁺(i), rerooting invariance (A), Palm average (B1) and
the Palm zoom model (B2). -/
theorem g1ZoomPartStmt_of_nodes (hD3 : D3PlusIStmtRich) (hA : G1RerootStmt)
    (hB1 : G1PalmAvgStmt) (hB2 : G1PalmModelStmt) : G1ZoomPartStmt := by
  intro γ Ω _ P _ B Y hS hIn
  exact ⟨g1ZoomPartSide_of_nodes hD3 hA hB1 hB2 hS hIn true,
    g1ZoomPartSide_of_nodes hD3 hA hB1 hB2 hS hIn false⟩

/-- **G1 from D3⁺(i), the zoom nodes and the regularity half.** -/
theorem g1Stmt_of_zoomNodes_regRep (hD3 : D3PlusIStmtRich) (hA : G1RerootStmt)
    (hB1 : G1PalmAvgStmt) (hB2 : G1PalmModelStmt) (hR : G1RegRepStmt) : G1Stmt :=
  g1Stmt_of_zoom_regRep (g1ZoomPartStmt_of_nodes hD3 hA hB1 hB2) hR

end Thm18Asm
end QuantumZipper
