/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallOuterCoverInf
import InteractingSLE.Spec.Sec7.R5EnlFwdR7Inf
import InteractingSLE.Spec.Sec7.R5EnlR7
import InteractingSLE.Spec.Sec7.R5LiftHull2

/-!
# Lemma R.5 on the extremal R.7 pockets from the split cover: `R5Enl.R7R5RemainingOn`

Packet PROVE-R5-WALL (second round). The R.5 assembly for the extremal (reverse-contained) change pockets of R.7
(rulings R85, R86, R86a, R88): on every test, `R5ClausesOn` for R5-REFCHART's reference family with the references'
own lifts — clause 1 (finite exceptional sets), clause 2 (the lattice phase of R5-LIFT's common integer), clause 3
(`R5Ref.refEvent_spec`), clause 4 (R5-ENLARGED's conditioned increment law `R5Enl.r5ClausesOn_clause4_ref`, proved
outright) and clause 5 (the gap-free split cover `R5Wall.r5Cover_ref_of_liftWord_split'`).

* `TwoSeedSplitInput(Inf)` (defs, **named input**): the initial heights, R5-LIFT's pathwise `R7LiftGeom'(Inf)` and the
  outer lift input `R7OuterLiftWord(Inf)` at every integer field at which the hull lift input holds;
* **`twoSeedR5InputOn_of_split`**, **`twoSeedR5InputInfOn_of_split`**: `TwoSeedR5Input(Inf)On` from them;
* `R7SplitRemaining` (def, **named input**; premises verbatim those of `R5Enl.R7R5RemainingOn`) and
  **`r7R5RemainingOn_of_split`**: `R5Enl.R7R5RemainingOn` at all margins (walls' data derived from the configuration as
  in `R5Enl.r7PhaseWordRemaining_of_r5On`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Wall

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont R7Outer R7Leaves StripPocketConfig RefWire R5Phase R5Ref R5Enl PhaseSel

universe u

section Defs

variable {Ω : Type*}

/-- **Lemma R.5's split-cover inputs on every test of a walls' event** (bounded change pocket; named input): in a
walls-measurable
chart branch `n` with a lattice offset `a`, the initial heights (exceptional set `X₀`), and at every relative capacity
a finite exceptional set `X_q ⊇ X₀ ∪ outerExc`, R5-LIFT's pathwise geometry `R5Lift.R7LiftGeom'` with reflecting sets
`J_q`,
and the lift input at the exposed landings on the walls at every integer field at which the hull lift input holds. -/
def TwoSeedSplitInput (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ a : ℝ, (∃ m : ℤ, a = m * phaseStep κ) ∧
        ∃ (X₀ : Ω → Set ℂ) (X : ℝ≥0 → Ω → Set ℂ) (J : ℝ≥0 → ℕ → Ω → Set ℝ),
          R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAll R L r η ψ)
            (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u X₀ ∧
          ∀ q : ℝ≥0, (∀ ω, (X q ω).Finite) ∧ (∀ ω, X₀ ω ⊆ X q ω) ∧ (∀ ω, outerExc R L r η ψ q ω ⊆ X q ω) ∧
            R5Lift.R7LiftGeom' P A R L r η ψ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' ζ' VL VR (X q) (J q) q ∧
            ∀ N : Ω → ℤ, R7AmbientLiftWord κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
                (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
                (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a W' ζ' VL VR
                (fun ω => chiC κ * (2 * Real.pi * N ω) + a) (X q) q →
              R7OuterLiftWord κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
                (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
                (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a W' ζ' VL VR
                (fun ω => chiC κ * (2 * Real.pi * N ω) + a) (X q) q

/-- **Lemma R.5's split-cover inputs on every test of a walls' event** (pocket opening at the flow seed; named input):
in a walls-measurable
chart branch `n` with a lattice offset `a`, the initial heights (exceptional set `X₀`), and at every relative capacity
a finite exceptional set `X_q ⊇ X₀ ∪ outerExcInf`, R5-LIFT's pathwise geometry `R5Lift.R7LiftGeomInf'` with reflecting
sets `J_q`,
and the lift input at the exposed landings on the walls at every integer field at which the hull lift input holds. -/
def TwoSeedSplitInputInf (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ a : ℝ, (∃ m : ℤ, a = m * phaseStep κ) ∧
        ∃ (X₀ : Ω → Set ℂ) (X : ℝ≥0 → Ω → Set ℂ) (J : ℝ≥0 → ℕ → Ω → Set ℝ),
          R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAllInf R L r η ψ)
            (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u X₀ ∧
          ∀ q : ℝ≥0, (∀ ω, (X q ω).Finite) ∧ (∀ ω, X₀ ω ⊆ X q ω) ∧ (∀ ω, outerExcInf R L r η ψ q ω ⊆ X q ω) ∧
            R5Lift.R7LiftGeomInf' P A R L r η ψ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' ζ' VL VR (X q) (J q) q ∧
            ∀ N : Ω → ℤ, R7AmbientLiftWordInf κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
                (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
                (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a W' ζ' VL VR
                (fun ω => chiC κ * (2 * Real.pi * N ω) + a) (X q) q →
              R7OuterLiftWordInf κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
                (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
                (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a W' ζ' VL VR
                (fun ω => chiC κ * (2 * Real.pi * N ω) + a) (X q) q

end Defs

section Tests

variable {Ω : Type*} {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ}
  {ρR' : Fin mR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **`R5Enl.TwoSeedR5InputOn` from the split-cover inputs** (bounded change pocket): per test, the phase integer of
R5-LIFT's
`R5Lift.exists_r7AmbientLiftWord'`, clause 1 (`refExc ∪ X_q` finite), clause 2 (`R5Lift.phase_mem_lattice`), clause 3
(`R5Ref.refEvent_spec`), clause 4 (R5-ENLARGED's `R5Enl.r5ClausesOn_clause4_ref`) and clause 5
(`r5Cover_ref_of_liftWord_split'`). -/
theorem twoSeedR5InputOn_of_split
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
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {G : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j) {rL rR : ℝ}
    (hin : TwoSeedSplitInput κ rL rR P R L r η G (centredField h'' u₀') u₀' ρL' ρR' W' ζ' VL VR) :
    TwoSeedR5InputOn κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ') := by
  classical
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, X, J, hInit, hq⟩ := hin A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hcfgA : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  have hζA : ∀ ω ∈ A, ζ' ω = ⊤ := fun ω hω => hζG ω (hAG hω)
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hJ : ∀ ω ∈ A, IsJordanCases (cfPocket (R ω) (L ω) r) (ψ ω) := fun ω hω => by
    have hcf := hcfg ω (hAG hω)
    have hp := hcf.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded)
    exact Or.inl ⟨cfPt (openPt (R ω) (L ω) r), cfPt (closePt (R ω) (L ω) r), hp.isBounded,
      hcf.conf.cfPt_openPt_notMem, hψ ω hω⟩
  obtain ⟨hcA, hcExt, -⟩ := shiftChart_aux29Facts hCo hCH hJ n
  have hfacts := shiftChart_cfPocket_facts hcfgA hψ n
  have hc : ∀ ω ∈ A, (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).IsConformal :=
    fun ω hω => (hfacts ω hω).1
  have hdom : ∀ ω ∈ A, ((shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r := fun ω hω => (hfacts ω hω).2.1
  have heq : ∀ ω ∈ A, EqOn (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).1 (ψ ω)
      (cfPocket (R ω) (L ω) r) := fun ω hω => (hfacts ω hω).2.2
  have hℓ := fun ω hω => (hcA ω hω).2
  have hex := fun q : ℝ≥0 =>
    R5Lift.exists_r7AmbientLiftWord' (κ := κ) (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) (ρL' := ρL')
      (ρR' := ρR')
      hcfgA hψ hc hdom heq hℓ hcExt (fun _ => rfl) (fun _ => rfl) hC.1.2.2.2.2 hζA hxL' hxR' (hq q).2.2.2.1 a
  choose N hN using hex
  refine ⟨n, hn, a, fun q ω => chiC κ * (2 * Real.pi * N q ω) + a, fun q ω => refExc R L r η ψ q ω ∪ X q ω,
    fun _ i ω => (refChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ
      i ω).2.2,
    fun q => refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q,
    fun _ => refChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ,
    fun q => ?_⟩
  obtain ⟨hXf, hX₀, hOX, -, hOuter⟩ := hq q
  refine r5ClausesOn_of_refCover hcfgA hψ hc hdom heq hXf
    (Eventually.of_forall fun ω _ _ => R5Lift.phase_mem_lattice (N q ω) ha)
    (R5Enl.r5ClausesOn_clause4_ref hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
      hGm hG hA hAG hcfgA hζA hψ hψm hηm hc hdom heq q) ?_
  exact r5Cover_ref_of_liftWord_split' hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
    hlocL hGm hG hA hAG hcfgA hψ hc hdom heq hcExt hζA (fun _ _ => rfl) (fun _ _ => rfl) (hN q)
    hInit hX₀ hOX (hOuter (N q) (hN q))

/-- **`R5Enl.TwoSeedR5InputInfOn` from the split-cover inputs** (pocket opening at the flow seed): per test, the phase
integer of R5-LIFT's
`R5Lift.exists_r7AmbientLiftWordInf'`, clause 1 (`refExcInf ∪ X_q` finite), clause 2 (`R5Lift.phase_mem_lattice`),
clause 3
(`R5Ref.refEventInf_spec`), clause 4 (R5-ENLARGED's `R5Enl.r5ClausesOn_clause4_refInf`) and clause 5
(`r5Cover_refInf_of_liftWord_split'`). -/
theorem twoSeedR5InputInfOn_of_split
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
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {G : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j) {rL rR : ℝ}
    (hin : TwoSeedSplitInputInf κ rL rR P R L r η G (centredField h'' u₀') u₀' ρL' ρR' W' ζ' VL VR) :
    TwoSeedR5InputInfOn κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ') := by
  classical
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, X, J, hInit, hq⟩ := hin A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hcfgA : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  have hζA : ∀ ω ∈ A, ζ' ω = ⊤ := fun ω hω => hζG ω (hAG hω)
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hJ : ∀ ω ∈ A, IsJordanCases (cfPocket (R ω) (L ω) r) (ψ ω) := fun ω hω => by
    exact Or.inr ⟨cfPt (closePt (R ω) (L ω) r), hψ ω hω⟩

  obtain ⟨hcA, hcExt, -⟩ := shiftChart_aux29Facts hCo hCH hJ n
  have hfacts := shiftChart_cfPocketInf_facts hcfgA hψ n
  have hc : ∀ ω ∈ A, (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).IsConformal :=
    fun ω hω => (hfacts ω hω).1
  have hdom : ∀ ω ∈ A, ((shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r := fun ω hω => (hfacts ω hω).2.1
  have heq : ∀ ω ∈ A, EqOn (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).1 (ψ ω)
      (cfPocket (R ω) (L ω) r) := fun ω hω => (hfacts ω hω).2.2
  have hℓ := fun ω hω => (hcA ω hω).2
  have hex := fun q : ℝ≥0 =>
    R5Lift.exists_r7AmbientLiftWordInf' (κ := κ) (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR)
      (ρL' := ρL') (ρR' := ρR')
      hcfgA hψ hc hdom heq hℓ hcExt (fun _ => rfl) (fun _ => rfl) hC.1.2.2.2.2 hζA hxL' hxR' (hq q).2.2.2.1 a
  choose N hN using hex
  refine ⟨n, hn, a, fun q ω => chiC κ * (2 * Real.pi * N q ω) + a, fun q ω => refExcInf R L r η ψ q ω ∪ X q ω,
    fun _ i ω => (refChartInf (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ
      i ω).2.2,
    fun q => refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q,
    fun _ => refChartInf (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ,
    fun q => ?_⟩
  obtain ⟨hXf, hX₀, hOX, -, hOuter⟩ := hq q
  refine r5ClausesOn_of_refInfCover hcfgA hψ hc hdom heq hXf
    (Eventually.of_forall fun ω _ _ => R5Lift.phase_mem_lattice (N q ω) ha)
    (R5Enl.r5ClausesOn_clause4_refInf hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
      hGm hG hA hAG hcfgA hζA hψ hψm hηm hc hdom heq q) ?_
  exact r5Cover_refInf_of_liftWord_split' hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
    hlocL hGm hG hA hAG hcfgA hψ hc hdom heq hcExt hζA (fun _ _ => rfl) (fun _ _ => rfl) (hN q)
    hInit hX₀ hOX (hOuter (N q) (hN q))

end Tests

/-- **Lemma R.5's split-cover inputs on every R.7 configuration** (named input; margins `c`, `c′`): the premises are
exactly those of `R5Enl.R7R5RemainingOn`; the conclusion is `TwoSeedSplitInput(Inf)` against the counterflow's
coupling (force processes `VL`, `VR`, weights `flowLineRho(L/R) k b' J' 0 0`). -/
def R7SplitRemaining (k rL rR c c' : ℝ) : Prop :=
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
      TwoSeedSplitInput k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'
          (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) W' ζ' VL VR ∧
        TwoSeedSplitInputInf k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'
          (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) W' ζ' VL VR

/-- **`R5Enl.R7R5RemainingOn` at all margins from the split-cover inputs**: the walls' data are derived from the
configuration exactly as in `R5Enl.r7PhaseWordRemaining_of_r5On`, then `twoSeedR5Input(Inf)On_of_split` on the two
kinds of change pockets (the counterflow's left marks are `≤ 0`, its right marks `≥ 0`). -/
theorem r7R5RemainingOn_of_split {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hs5 : R7SplitRemaining.{u} k rL rR c c') : R7R5RemainingOn.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hs5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
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
  have hxL' := Theorem14.GW3Word.flowLineXL_nonpos b' J'
  have hxR' := Theorem14.GW3Word.flowLineXR_nonneg b' J'
  exact ⟨twoSeedR5InputOn_of_split hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hGp (fun ω hω => hcfgP ω hω.1 hω.2)
      (fun ω hω => hζG ω hω.1) hxL' hxR' hs,
    twoSeedR5InputInfOn_of_split hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hG0 hcfgI' (fun ω hω => hζG ω hω.1)
      hxL' hxR' hsI⟩

/-- **R.5 up to phase on every R.7 pocket test (`PhaseCont.R7PhaseWordRemaining`) from the split-cover inputs**:
`R5Enl.r7PhaseWordRemaining_of_r5On` after `r7R5RemainingOn_of_split`. -/
theorem r7PhaseWordRemaining_of_split {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hs5 : R7SplitRemaining.{u} k rL rR c c') : PhaseCont.R7PhaseWordRemaining.{u} k rL rR c c' :=
  r7PhaseWordRemaining_of_r5On hk4 hc hc' (r7R5RemainingOn_of_split hk4 hc hc' hs5)

end InteractingSLE.Sec7.R5Wall
