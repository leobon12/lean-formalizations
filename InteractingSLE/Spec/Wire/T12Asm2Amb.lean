/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm2Outer
import InteractingSLE.Spec.Sec7.R5SameClause

/-!
# Theorem 1.2's R.5 binders: the cover clause from the pathwise ambient cover

PROVE-T12-ASSEMBLE2. Ruling R85's R.5 binders `R5Enl.R7R5RemainingOn` (extremal pockets) and
`OuterContOn.R7OuterR5RemainingOn` (outer pockets) ask on every test for `R5Enl.R5ClausesOn`. PROVE-R5-SAMETIME
proved the reference heights of its fifth clause (the cover) at the hull (`R5Same.ae_tendsto_harmRep_refHull`), so with
the ambient lifts `R5Same.ambLift` the cover follows from the purely pathwise `R5Same.R7AmbientCover`
(`R5Same.r5Clauses_of_ambient`, unconditioned form). Here:

* `R5PreOn` (def): clauses 1–4 of `R5ClausesOn` (finite exceptional sets, lattice phase, reference charts, the
  conditioned increment laws `HasOldChartIncrementLawOn`);
* **`r5ClausesOn_of_ambient`**: `R5PreOn` and `R7AmbientCover` give `R5ClausesOn` with `liftB = ambLift W'`;
* `TwoSeedR5AmbInputOn(Inf)` (test level), `R7R5AmbRemainingOn`, `R7OuterR5AmbRemainingOn` (named inputs: the premises
  of `R7R5RemainingOn` / `R7OuterR5MRemainingOn` verbatim, conclusion `R5PreOn` and `R7AmbientCover` on every test);
* **`r7R5RemainingOn_of_amb`**, **`r7OuterR5MRemainingOn_of_amb`**: the reductions (the walls' data of
  `r5Clauses_of_ambient` are derived from the configuration as in `R5Enl.r7PhaseWordRemaining_of_r5On`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5AmbOn

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont R7Outer R7Leaves StripPocketConfig RefWire R5Phase R5Enl R5Same PocketStopWalls PocketStopSide
  Aux119Heights PhaseSel

universe u

section Defs

variable {Ω : Type*}

/-- **Clauses 1–4 of `R5ClausesOn`**: finite exceptional sets, the lattice phase, the reference charts on the pair
events, and the conditioned old-chart increment laws (everything except the cover). -/
def R5PreOn [MeasurableSpace Ω] (κ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (c : Ω → Chart) (h₀ : Ω → DistOn upperHalfPlaneOpens) (C : Ω → Set ℂ) (F : ℕ → Ω → Set ℂ) (δ : Ω → ℝ)
    (X : Ω → Set ℂ) (M : ℕ → Set Ω) (old : ℕ → Ω → Chart) (q : ℝ≥0) : Prop :=
  (∀ ω, (X ω).Finite) ∧
  (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ) ∧
  (∀ i, ∀ ω ∈ M i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ (old i ω).IsConformal ∧
    ((relChart c γ q ω).dom : Set ℂ) ⊆ (old i ω).dom ∧
    ((old i ω).dom : Set ℂ) = H \ liveExt A γ C (F i) 0 ω) ∧
  (∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt A γ C (F i) 0) h₀ P (gB i)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
    ∀ i, HasOldChartIncrementLawOn P (M i) (old i) (relChart c γ q) (gB i) g)

/-- **R.5's clauses on every test of a walls' event, cover in pathwise ambient form** (bounded change pocket):
clauses 1–4 (`R5PreOn`) and the pathwise cover `R7AmbientCover` against the counterflow's force processes. -/
def TwoSeedR5AmbInputOn (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ)
    (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ)
        (M : ℝ≥0 → ℕ → Set Ω) (old : ℝ≥0 → ℕ → Ω → Chart),
        ∀ q : ℝ≥0, R5PreOn κ P A (travAll R L r η ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) h₀
            (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') (δ q) (X q) (M q) (old q) q ∧
          R7AmbientCover κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A (travAll R L r η ψ)
            (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a
            (fun ω => cfPocket (R ω) (L ω) r) W' ζ' VL VR (δ q) (X q) (M q) (old q) q

/-- **R.5's clauses on every test of a walls' event, cover in pathwise ambient form** (pocket opening at the flow
seed). -/
def TwoSeedR5AmbInputInfOn (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ)
    (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ)
        (M : ℝ≥0 → ℕ → Set Ω) (old : ℝ≥0 → ℕ → Ω → Chart),
        ∀ q : ℝ≥0, R5PreOn κ P A (travAllInf R L r η ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) h₀
            (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') (δ q) (X q) (M q) (old q) q ∧
          R7AmbientCover κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A (travAllInf R L r η ψ)
            (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a
            (fun ω => cfPocket (R ω) (L ω) r) W' ζ' VL VR (δ q) (X q) (M q) (old q) q

end Defs

section Clause

variable {Ω : Type*}

/-- **`R5ClausesOn` on an R.7 test with the ambient lifts**: clauses 1–4 (`R5PreOn`) and the pathwise cover
`R7AmbientCover` give `R5ClausesOn` with `liftB = ambLift W'`; the reference heights are
`R5Same.ae_tendsto_harmRep_refHull` (PROVE-R5-SAMETIME's `r5Clauses_of_ambient`, conditioned form). -/
theorem r5ClausesOn_of_ambient {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ}
    {ρR' : Fin mR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
    {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {M : ℕ → Set Ω}
    {old : ℕ → Ω → Chart} {q : ℝ≥0}
    (hpre : R5PreOn κ P A γ c (centredField h'' u₀') (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ X M
      old q)
    (hCov : R7AmbientCover κ ρL ρR ρL' ρR' P A γ xL xR c a (fun ω => cfPocket (R ω) (L ω) r) W' ζ' VL VR δ X M
      old q) :
    R5ClausesOn κ ρL ρR P A γ xL xR c a (centredField h'' u₀') u₀' (fun ω => cfPocket (R ω) (L ω) r)
      (refHull W' ζ') δ X (ambLift W') M old q := by
  obtain ⟨hXf, hLattice, hOld, hLaw⟩ := hpre
  refine ⟨hXf, hLattice, hOld, hLaw, fun gB hgB => ?_⟩
  have hH := ae_tendsto_harmRep_refHull hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ hgB
  filter_upwards [hH, hCov] with ω hHω hcovω hωA hlive ξ hξ hXξ
  obtain ⟨i, x, r', x', d, z₀, hM, hr, hcol, htr, hz₀, hinv, hev, hx', hfx, hd, hword⟩ :=
    hcovω hωA hlive ξ hξ hXξ
  exact ⟨i, x, r', _, d, hM, hr, hcol, htr, hHω hωA i z₀ hz₀ _ (ξ : ℂ) x' hx' hinv hev hfx, hd, hword⟩

end Clause

section Test

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The conditioned per-test clauses from the ambient form** (bounded change pocket), for any configuration whose
traversals are driven curves. -/
theorem twoSeedR5InputOn_of_amb [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
    {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hγ : ∀ ψ : Ω → ℂ → ℂ, ∀ ω ∈ G, IsCfJordan (R ω) (L ω) r (ψ ω) →
      IsDrivenCurve (travAll R L r η ψ ω))
    (hin : TwoSeedR5AmbInputOn κ rL rR P R L r η G (centredField h'' u₀') W' ζ' ρL' ρR' VL VR) :
    TwoSeedR5InputOn κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ') := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, δ, X, M, old, hcl⟩ := hin A hA hAG hPA ψ hψ hψm
  exact ⟨n, hn, a, δ, X, fun _ => ambLift W', M, old, fun q => r5ClausesOn_of_ambient hT' hTr hu₀ hh hC hκ hu₀'
    hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG
    (fun ω hω => hγ ψ ω (hAG hω) (hψ ω hω)) (hcl q).1 (hcl q).2⟩

/-- **The conditioned per-test clauses from the ambient form** (pocket opening at the flow seed). -/
theorem twoSeedR5InputInfOn_of_amb [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
    {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hγ : ∀ ψ : Ω → ℂ → ℂ, ∀ ω ∈ G, IsCfJordanInf (R ω) (L ω) r (ψ ω) →
      IsDrivenCurve (travAllInf R L r η ψ ω))
    (hin : TwoSeedR5AmbInputInfOn κ rL rR P R L r η G (centredField h'' u₀') W' ζ' ρL' ρR' VL VR) :
    TwoSeedR5InputInfOn κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ') := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, δ, X, M, old, hcl⟩ := hin A hA hAG hPA ψ hψ hψm
  exact ⟨n, hn, a, δ, X, fun _ => ambLift W', M, old, fun q => r5ClausesOn_of_ambient hT' hTr hu₀ hh hC hκ hu₀'
    hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG
    (fun ω hω => hγ ψ ω (hAG hω) (hψ ω hω)) (hcl q).1 (hcl q).2⟩

end Test

/-! ### Every R.7 configuration -/

section Remaining

open HOuter OuterContOn

/-- **Lemma R.5's conditioned clauses, cover in pathwise ambient form, on every R.7 configuration** (named input;
margins `c`, `c′`): the premises are exactly those of `R5Enl.R7R5RemainingOn`; the conclusion is `R5PreOn` and
`R5Same.R7AmbientCover` on every test, against the old references at the rational original times. -/
def R7R5AmbRemainingOn (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedR5AmbInputOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') W' ζ'
          (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) VL VR ∧
        TwoSeedR5AmbInputInfOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') W' ζ'
          (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) VL VR

/-- **Lemma R.5's conditioned clauses, cover in pathwise ambient form, on every outer R.7 configuration** (named
input): the premises are exactly those of `OuterContOn.R7OuterR5MRemainingOn`; conclusion as in
`R7R5AmbRemainingOn`. -/
def R7OuterR5AmbRemainingOn (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedR5AmbInputOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') W' ζ'
          (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) VL VR ∧
        TwoSeedR5AmbInputInfOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') W' ζ'
          (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) VL VR

/-- **`R5Enl.R7R5RemainingOn` from the ambient form**: the walls' data are derived from the configuration exactly as
in `R5Enl.r7PhaseWordRemaining_of_r5On`, then `twoSeedR5Input(Inf)On_of_amb` on the two kinds of change pockets. -/
theorem r7R5RemainingOn_of_amb {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hr5 : R7R5AmbRemainingOn.{u} k rL rR c c') : R7R5RemainingOn.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hr5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have hreg := hcfg.regular
  have hdetR := fun t => hdet_of_borel hΦαR (fun ω => (hΦ ω).1) hV.R_ae u₀ t
  have hdetL := fun t => hdet_of_borel hΦαL (fun ω => (hΦ ω).2.2.2) hV.L_ae u₀ t
  have hlocR := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αR
    (hreg.mono fun ω hω => hω.2.2.2.2.1) hu₀ hV.R_cont hV.R_zero hV.R_meas hV.R_ae
  have hlocL := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αL
    (hreg.mono fun ω hω => hω.2.2.2.2.2.2.2) hu₀ hV.L_cont hV.L_zero hV.L_meas hV.L_ae
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  exact ⟨twoSeedR5InputOn_of_amb hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hGp (fun ω hω => hconf ω hω.1)
      (fun ψ ω hω hψ => ((hcfgP ω hω.1 hω.2).isDrivenCurve hψ).1) hs,
    twoSeedR5InputInfOn_of_amb hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hG0 (fun ω hω => hconf ω hω.1)
      (fun ψ ω hω hψ => ((hcfgI' ω hω).isDrivenCurve hψ).1) hsI⟩

/-- **`OuterContOn.R7OuterR5MRemainingOn` from the ambient form** (outer configurations; as
`r7R5RemainingOn_of_amb`, with `IsOuterCfg(Inf).props` for the driven traversals). -/
theorem r7OuterR5MRemainingOn_of_amb {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hr5 : R7OuterR5AmbRemainingOn.{u} k rL rR c c') : R7OuterR5MRemainingOn.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hr5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have hreg := hcfg.regular
  have hdetR := fun t => hdet_of_borel hΦαR (fun ω => (hΦ ω).1) hV.R_ae u₀ t
  have hdetL := fun t => hdet_of_borel hΦαL (fun ω => (hΦ ω).2.2.2) hV.L_ae u₀ t
  have hlocR := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αR
    (hreg.mono fun ω hω => hω.2.2.2.2.1) hu₀ hV.R_cont hV.R_zero hV.R_meas hV.R_ae
  have hlocL := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αL
    (hreg.mono fun ω hω => hω.2.2.2.2.2.2.2) hu₀ hV.L_cont hV.L_zero hV.L_meas hV.L_ae
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  exact ⟨twoSeedR5InputOn_of_amb hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hGp (fun ω hω => hconf ω hω.1)
      (fun ψ ω hω hψ => ((hcfgP ω hω.1 hω.2).props hψ).1) hs,
    twoSeedR5InputInfOn_of_amb hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hG0 (fun ω hω => hconf ω hω.1)
      (fun ψ ω hω hψ => ((hcfgI' ω hω).props hψ).1) hsI⟩

end Remaining

end InteractingSLE.Sec7.R5AmbOn
