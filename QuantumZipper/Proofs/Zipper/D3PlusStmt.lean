import QuantumZipper.Proofs.GFF.K3.MixedM7Stmt
import QuantumZipper.Proofs.Section5.TVLocal
import QuantumZipper.LQG.Local
import QuantumZipper.LQG.Wedge

/-!
# D3⁺ (zoom lemma, corrected form) and the local data map `locData`: statements

Decision **D23** (`DECISIONS.md`). Blueprint: `blueprint/E_BRANCH_BLUEPRINT.md` §2 (TV-local),
§3 (D3⁺), §4 E5; `blueprint/SECTION5_BLUEPRINT.md` D3 (corrected), D4. Paper: Sheffield,
arXiv:1012.4797, §1.6 and the proof of Prop. 1.6 (p. 25, "the argument in Proposition 1.6"),
§5.4 (pp. 66–72).

## The local data map

`locData R c = (TV.locField R c.1, s ↦ c.2 (min s R))`: the raw values of the field at the dyadic
folded circles inside `closedBall 0 R`, and the driver on the **deterministic capacity window**
`[0, R]` (held constant afterwards). It is `Measurable` for the product σ-algebras
(`measurable_locData`), so it can be used with `Measure.map` and in `∫⁻`.

The blueprint's first proposal stopped the driver at the exit time of the hull from `B_R`. That
time is not measurable for the product σ-algebra on `ℝ → ℝ` (it depends on uncountably many
coordinates), and it is bounded by `R²/2` (half-plane capacity: a hull inside `closedBall 0 R`
has `hcap ≤ R²`, and `hcap K_t = 2t`), so the hull-stopped driver is a function of the window
data at any `R' ≥ R²/2`. TV-local convergence for the window form therefore implies it for the
hull form (TV distance decreases under measurable maps). See D23.

## The model field of D3⁺

`zoomModel γ α L ρ₀ x g = x + ofFun (z ↦ α(−log‖z‖) + g z + (L/γ − x ρ₀))`: the free field
normalized by the reference measure `ρ₀` (which gives no mass to `ball 0 r`), a log singularity of
strength `α` at `0`, a correction `g`, and the level `L/γ`. For a probability measure `μ` it is
`X μ − X ρ₀ + ∫ (α(−log) + g) dμ + L/γ`, i.e. the D22 coupling `X − μ(ℂ) X(ρ₀) + ∫ g dμ` plus the
log singularity (E5: `α = α₀ = γ − 2/γ`; Prop 1.6 D4: `α = γ`).

The zoom is read **locally**, on the half-disc `halfDisc r = ball 0 r ∩ ℍ`, through
`scaleParamOn`/`canonicalOn` (as in Prop 1.6's `AreaConvergesInLawOn`): the model field is only
meaningful near `0`. The global `canonical` of E5's `canonConfig` agrees with `canonicalOn` on
the event that the local scale is small (locality of the area measure); that conversion is E5's.

## The three statements (common hypotheses `Setup`)

`X` free (`IsFreeGFFModConstH`), `Ξ` independent of the balanced increments of `X` (as in D22),
`g ω ∘ foldH` harmonic on `ball 0 r` (Neumann on `ℝ`), `g z` measurable for
`𝒢 := σ(Ξ) ⊔ outsideSigma X 0 r` (the free field outside the half-disc), `α < Q`, `0 < γ < 2`.
Conditional statements "`E ‖law(F | 𝒢) − μ‖_TV → 0`" are written without conditional laws, in
the two-sided `ℝ≥0∞` form of `E5.E5Stmt`: uniformly over `𝒢 ⊗ Borel`-measurable test functions
`Φ(ω, y) ∈ [0,1]`.

* `D3PlusIStmt` (field-level zoom convergence): `locField R (canonicalOn γ Y_L (halfDisc r))`
  given `𝒢` converges in TV to the local data of the `α`-quantum wedge, uniformly in `Φ`.
* `D3PlusIIStmt` (level-shift continuity, LSC): replacing `g` by `g'` with `|g − g'| ≤ K` on
  `ball 0 r ∩ Hbar` changes the joint conditional law of
  `(locField R (canonicalOn …), log (scaleParamOn …))` by a TV amount `→ 0`.
* `D3PlusIIIStmt` (scale → 0): almost surely, for every `ε > 0`, eventually in `L`,
  `0 < scaleParamOn γ Y_L (halfDisc r) < ε` (the almost-sure form; it implies convergence in
  probability, and the positivity clause rules out the junk value `0` of `sInf ∅`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The local data map -/

/-! ## The model field of D3⁺ -/

/-- The half-disc `ball 0 r ∩ ℍ` on which the zoom is read. -/
def halfDisc (r : ℝ) : Set ℂ := Metric.ball 0 r ∩ H

theorem isOpen_halfDisc (r : ℝ) : IsOpen (halfDisc r) := Metric.isOpen_ball.inter isOpen_H

theorem halfDisc_subset_H (r : ℝ) : halfDisc r ⊆ H := inter_subset_right

/-- **The model field of D3⁺** at level `L`: `x` normalized by `ρ₀`, plus `α(−log‖·‖) + g`, plus
the constant `L/γ`. -/
def zoomModel (γ α L : ℝ) (ρ₀ : Measure ℂ) (x : FieldSample) (g : ℂ → ℝ) : FieldSample :=
  x + ofFun (fun z => α * -Real.log ‖z‖ + g z + (L / γ - x ρ₀))

/-- The conditioning σ-algebra `σ(Ξ) ⊔ outsideSigma X 0 r` of D3⁺. -/
abbrev condSigma {Ω E' : Type*} [MeasurableSpace E'] (Ξ : Ω → E') (X : Ω → FieldSample) (r : ℝ) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap Ξ inferInstance ⊔ K3.outsideSigma X 0 r

/-- **Common hypotheses of D3⁺** (`E_BRANCH_BLUEPRINT.md` §3, with the D22 interface):
`0 < γ < 2`, `α < Q`, `0 < r`; `X` a free field; `Ξ` measurable and independent of the balanced
increments of `X`; `ρ₀` an admissible probability measure giving no mass to `ball 0 r`;
`g ω ∘ foldH` harmonic on `ball 0 r` for every `ω`; `g z` measurable for `condSigma Ξ X r`. -/
structure Setup (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → FieldSample) {E' : Type*} [MeasurableSpace E'] (Ξ : Ω → E') (g : Ω → ℂ → ℝ) :
    Prop where
  hγ : 0 < γ
  hγ2 : γ < 2
  hα : α < Qc γ
  hr : 0 < r
  hX : IsFreeGFFModConstH X P
  hΞ : Measurable Ξ
  hind : Indep (MeasurableSpace.comap Ξ inferInstance) (K3.freeIncrSigma X) P
  hρ : IsAdmissibleH ρ₀
  hρ1 : ρ₀ Set.univ = 1
  hρB : ρ₀ (Metric.ball (0 : ℂ) r) = 0
  harm : ∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (Metric.ball (0 : ℂ) r)
  gmeas : ∀ z, Measurable[condSigma Ξ X r] fun ω => g ω z

/-! ## The statements -/

/-- **D3⁺(i): field-level zoom convergence.** Under `Setup`, for an `α`-quantum wedge `Y'`: for
every `R` and `η > 0`, eventually in `L`, uniformly over `condSigma ⊗ Borel`-measurable
`Φ ∈ [0,1]`,
`|E Φ(ω, locField R (canonicalOn γ Y_L (halfDisc r))) − E ∫ Φ(ω, locField R Y') dP'| ≤ η`.
(This is `E ‖law(canonical Y_L | Ξ, 𝒪_r) − 𝒲_α‖_{TV, R} → 0`.) -/
def D3PlusIStmt : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g : Ω → ℂ → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Y' : Ω' → FieldSample),
    Setup γ α r ρ₀ P X Ξ g → IsQuantumWedge γ α Y' P' →
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ L in atTop,
      ∀ Φ : Ω × (ℕ → ℝ) → ℝ≥0∞, Measurable[(condSigma Ξ X r).prod inferInstance] Φ →
        (∀ p, Φ p ≤ 1) →
        let lhs := ∫⁻ ω, Φ (ω, TV.locField R
          (canonicalOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r))) ∂P
        let rhs := ∫⁻ ω, ∫⁻ ω', Φ (ω, TV.locField R (Y' ω')) ∂P' ∂P
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

/-- **D3⁺(iii): the local scale tends to `0`.** Under `Setup`, almost surely, for every `ε > 0`,
eventually in `L`, `0 < scaleParamOn γ Y_L (halfDisc r) < ε`. -/
def D3PlusIIIStmt : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g : Ω → ℂ → ℝ),
    Setup γ α r ρ₀ P X Ξ g →
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ L in atTop,
      0 < scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) ∧
        scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) < ε

end D3Plus
end QuantumZipper
