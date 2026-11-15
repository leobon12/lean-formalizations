/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallOuterCover
import InteractingSLE.Spec.Sec7.R5WallOuterGeomInf

/-!
# R.5's split cover without the gap: exposed coordinates landing on the walls (pocket opening at the flow seed)

Packet PROVE-R5-WALL (second round; ruling R86a). The twin of `R5WallOuterCover` for the change pocket opening at the
flow seed: `R7OuterLiftWordInf` (named pathwise input), **`r5Cover_exposedOuterInf`**, and the gap-free full clause 5
**`r5Cover_refInf_of_split'`**, **`r5Cover_refInf_of_liftWord_split'`**.

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Wall

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide
  PhaseSel Aux119Heights PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same PocketStopField
  PocketStopWalls PocketStopWallsFin PocketWordPerQ R5Ref
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*}

/-- **The lift-difference limit and the word identity at the exposed landings on the walls** (pocket opening at the
flow seed;
named pathwise input): `R5Ref.R7AmbientLiftWordInf` at exposed current coordinates whose landing lies outside the
pocket. -/
def R7OuterLiftWordInf [MeasurableSpace Ω] (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ)
    (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (c : Ω → Chart) (a : ℝ) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ)
    (VR : Fin mR → ℝ≥0 → Ω → ℝ) (δ : Ω → ℝ) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω - segDriver
        (travAllInf R L r η ψ ω) q)
      (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
        segDriver (travAllInf R L r η ψ ω) q) →
    extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ X ω →
    exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ →
    ∀ (i : ℕ) (x ε x' : ℝ), let s := rationalOriginalTime i;
      ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      η ω s ∈ cfPocket (R ω) (L ω) r →
      IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε →
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω →
      x' ∉ forceJumpSet (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) →
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) →
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s ((refChartInf c R L r η ψ i ω).2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) →
      ∃ d : ℝ,
        Tendsto (fun y => (relChart c (travAllInf R L r η ψ) q ω).2.2 ((relChart c (travAllInf R L r η ψ) q ω).2.1 y) -
          ambLift W' i ω ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
        forceBoundaryData κ ρL' ρR' (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) x' + chiC κ * d =
          phaseData κ ρL ρR
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
              segDriver (travAllInf R L r η ψ ω) q)
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
              segDriver (travAllInf R L r η ψ ω) q)
            (δ ω) ξ - a

section Cover

variable {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **The cover at the exposed landings on the walls** (pocket opening at the flow seed, seeds at `0`; ruling R86a):
with the
attachments and `0` in the exceptional set, the counterflow heights by the per-prime-end Proposition 3.8, and the
lift input `R7OuterLiftWord`, R.5's cover holds on `exposedOuterSel` with the references' own lifts. -/
theorem r5Cover_exposedOuterInf
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
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) {a : ℝ} {δ : Ω → ℝ}
    {X : Ω → Set ℂ} {q : ℝ≥0} (hOX : ∀ ω, outerExcInf R L r η ψ q ω ⊆ X ω)
    (hLW : R7OuterLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q) := by
  intro gB hgB
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω => ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
  have hH := ae_tendsto_harmRep_refHull_comp hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ hgB
  filter_upwards [hH, hLW, hC.1.2.2.2.2] with ω hHω hlw hp hωA hlive ξ hξ hXξ hS
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h1 := (hcfg ω hωA).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h1
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp (hζA ω hωA) hV fun _ => rfl
  obtain ⟨i, x, ε, x', ρ, hM, hv, hcol, hpK, hland, hρ, hfree, hjump, hcur, hold⟩ :=
    exists_outer_coverInf (ζ' := ζ') hωA (hcfg ω hωA) (hψ ω hωA) (hc ω hωA) (hdom ω hωA) (heq ω hωA) (hcExt ω hωA)
      (hζA ω hωA) (fun i t => hL i t) (fun j t => hR j t) (hxL ω) (hxR ω) hlive ξ (fun h => hXξ (Or.inl h))
      (fun h => hXξ (Or.inr (hOX ω h))) hS
  obtain ⟨d, hd, hword⟩ := hlw hωA hlive ξ hξ (fun h => hXξ (Or.inr h)) hS i x ε x' hM hv hcol hpK hjump hcur hold
  have hb := hHω hωA i _ hpK ρ hρ _ (ξ : ℂ) x' hjump hland hfree hcur
  obtain ⟨hb', hd'⟩ := tendsto_refLift_of_lift_sub (c := c) (γ := travAllInf R L r η ψ)
    (p := (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal) (q := q) (hc ω hωA) (hγ ω hωA) hlive
    hM.2.2.2.1 hcol.1 hcol.2.1 hcol.2.2.1
    (f := harmRep (gB i ω) (H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (refHull W' ζ' i) 0 ω)) (g := u₀') (ℓ := ambLift W' i ω) hb hd
  exact ⟨i, x, ε, _, 0, hM, hcol.1, hcol.2.1, hcol.2.2.1, hb', hd', by rw [mul_zero, add_zero, hword]⟩

/-- **R.5's full clause 5 for the reference family, with no gap** (pocket opening at the flow seed, marks at `0`;
rulings R86,
R86a): the hull cover at landings in the pocket, the initial heights at the wall coordinates, and the outer lift input
at the exposed landings on the walls (attachments and `0` in the exceptional set). -/
theorem r5Cover_refInf_of_split'
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
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : ∀ ω i, xL ω i = 0) (hxR : ∀ ω j, xR ω j = 0) {a : ℝ} {δ : Ω → ℝ}
    {X X₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hCov : R7AmbientCoverHull κ ρL ρR ρL' ρR' P A (travAllInf R L r η ψ) xL xR c a (fun ω => cfPocket (R ω) (L ω) r)
      W' ζ' VL VR δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q)
    (hInit : R7InitialHeights κ ρL ρR P A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR c a
      (centredField h'' u₀') u₀' X₀) (hX₀ : ∀ ω, X₀ ω ⊆ X ω) (hOX : ∀ ω, outerExcInf R L r η ψ q ω ⊆ X ω)
    (hOuter : R7OuterLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (fun _ _ => True) :=
  r5Cover_refInf_of_split hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA
    hAG hcfg hψ hc hcExt hxL hxR hCov hInit hX₀
    (r5Cover_exposedOuterInf hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG
      hA hAG hcfg hψ hc hdom heq hcExt hζA (fun ω => hxL ω 0)
      (fun ω => hxR ω 0) hOX hOuter)

/-- **R.5's full clause 5 for the reference family from the lift inputs, with no gap** (pocket opening at the flow
seed):
`r5Cover_refInf_of_split'` with the hull cover from R5-LIFT's `R5Ref.R7AmbientLiftWordInf`. -/
theorem r5Cover_refInf_of_liftWord_split'
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
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : ∀ ω i, xL ω i = 0) (hxR : ∀ ω j, xR ω j = 0) {a : ℝ} {δ : Ω → ℝ}
    {X X₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hLW : R7AmbientLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q)
    (hInit : R7InitialHeights κ ρL ρR P A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR c a
      (centredField h'' u₀') u₀' X₀) (hX₀ : ∀ ω, X₀ ω ⊆ X ω) (hOX : ∀ ω, outerExcInf R L r η ψ q ω ⊆ X ω)
    (hOuter : R7OuterLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (fun _ _ => True) :=
  r5Cover_refInf_of_split' hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA
    hAG hcfg hψ hc hdom heq hcExt hζA hxL hxR
    (r7AmbientCoverHull_of_liftWordInf hC.1.2.2.2.2 hcfg hψ hc hdom heq hζA hLW) hInit hX₀ hOX hOuter

end Cover

end InteractingSLE.Sec7.R5Wall
