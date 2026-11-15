/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71QCurve
import InteractingSLE.Spec.Sec7.Lemma71MMain
import InteractingSLE.Spec.Sec7.Lemma72EMain

/-!
# Lemma 7.1's fixed-time pocket clause from the geometric half of the middle-curve side limits

Packet PROVE-LEMMA71Q. The wiring of the main theorems takes Lemma 7.1 through its fixed-time chart clause
(`Lemma72E.PocketClauseStatement`, from which PROVE-LEMMA72E assembles `Lemma72C.PocketCondStatement`,
`Lemma72B.PocketJointStatement` and `Lemma72.Lemma71JointStatement`). This file derives that clause from the named
geometric input `MiddleLandingStatement` (CS-a and CS-branch) and the §4.2 reference:

* `primeEnd_of_sideLimit`: the prime-end premise of `Lemma71M.isPocketChartData_of_pocketPrimeEnd` from the side limits
  of the active component (the argument of `Lemma71M.isPocketChartData_of_sideLimit`, with its intermediate premise
  exposed);
* `sideLimit_of_curveSide`: those side limits from the inherited branch and the side limits along the middle curve (the
  argument of `Lemma71N.isPocketChartData_of_curveSide`, with its intermediate statement exposed);
* **`pocketClauseStatement_of_middleLanding`**: the fixed-time chart clause
  (`Lemma71M.isChartCouplingCharFunConst_of_primeEnd_ind`, B4 = `Lemma71M.measurable_chartAvoid_pocket`) on the pocket
  construction of PROVE-LEMMA71K; **`lemma71JointStatement_of_middleLanding`** (Lemma 7.1's joint law).

Conditional helpers (on `MiddleLandingStatement` and the named inputs of the three-curve space); they replace no
source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71Q

/-! ### The prime-end premise from the side limits (Lemma71M's argument, intermediate exposed) -/

section PrimeEnd

open Complex
open QuantumZipper (H Hbar)
open MartChar Coupling Lemma71C Lemma71D Lemma71E Lemma71K Sec6 LocalSets Lemma71G Lemma71L Lemma71M

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
  {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

/-- **The prime-end premise of the pocket chart from the side limits of the active component** (the argument of
`Lemma71M.isPocketChartData_of_sideLimit`, whose intermediate premise is exposed here for the fixed-time clause). -/
theorem primeEnd_of_sideLimit [IsProbabilityMeasure P]
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    {n : Ω → ℤ} {a' : ℝ}
    (hside : ∀ (t : ℝ≥0) (gL gT : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
        (WholeField.centredField h u₀) P gT →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL vT : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        InnerProductSpace.HarmonicOnNhd vT
          (H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω →
            gT ω ψ = ∫ x, vT x * ψ x) →
        ∃ Ex : Set ℝ, Ex.Finite ∧
          PocketSideLimit (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
            (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
            (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) vL vT u₀
            (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t)
            (pocketGl κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
              (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s)
              (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
              (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t a') Ex) :
    ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∃ gS gL gT : Ω → DistOn upperHalfPlaneOpens,
    IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)))
      (WholeField.centredField h u₀) P gS ∧
    IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL ∧
    IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
      (WholeField.centredField h u₀) P gT ∧
    ∀ᵐ ω ∂P, IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t →
      PocketPrimeEnd (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
        (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
        (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀
        (QuantumZipper.chiC κ) φ
        ((c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t))
        (chartMean κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
          (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (shiftLift (c ω) (n ω)) a'
          (QuantumZipper.chiC κ) φ t) := by
  intro t φ
  have hS' := hS
  obtain ⟨-, -, hh0, -, -, -, hβ62, hα62, hγ62, -⟩ := hS'
  have hpc' := hpc
  obtain ⟨-, -, hconf, hdom, -, -, -, hlift, -, -, hseg, -, -⟩ := hpc'
  obtain ⟨hc, h0, -, hηm, hdet, hloc, htr⟩ := IsLemma62Curve.three hβ62 hα62 hγ62
  -- the stopped union
  have hSm := measurable_capStop hG hM hY t
  have hSg := capStop_galmarino (G := G) (M := M) (Y := Y) t
  have hτ : ∀ ω, capTime G M Y β α γ t ω = capStop G M Y t (histOf (pathCoord (β ω)) ⊤)
      (histOf (pathCoord (α ω)) ⊤) (pathCoord (γ ω)) := fun _ => rfl
  have hstopsS : ∀ i, Measurable (Three.threeStops (capTime G M Y β α γ t) i) :=
    measurable_of_galmarino hηm (Three.measurable_threeRule hSm) (Three.isGalmarino_threeRule hSg)
      (Three.threeStops_eq_threeRule hτ)
  have hlocS := isLocalSet_explored_of_tendsto hh0 hc h0 hηm hdet hloc htr (Three.measurable_threeRule hSm)
    (Three.isGalmarino_threeRule hSg) (Three.threeStops_eq_threeRule hτ)
  obtain ⟨gS, hgS⟩ := IsLocalSet.exists_isLocalSetMean hh0 (measurable_explored hc hηm hstopsS) hlocS
  -- the complete three curves
  have hlocL := isLocalSet_explored_of_tendsto (τ := fun _ _ => ⊤) (S := fun _ _ _ => ⊤) hh0 hc h0 hηm hdet hloc
    htr (fun _ => measurable_const) (fun _ => isGalmarino_const ⊤) (fun _ _ => rfl)
  obtain ⟨gL, hgL⟩ := IsLocalSet.exists_isLocalSetMean hh0
    (measurable_explored hc hηm fun _ => measurable_const) hlocL
  -- the complete outer curves
  have hlocT := isLocalSet_explored_of_tendsto (τ := fun i _ => Three.outerStops i)
    (S := fun j _ _ => Three.outerStops j) hh0 hc h0 hηm hdet hloc htr (fun _ => measurable_const)
    (fun j => isGalmarino_const (Three.outerStops j)) (fun _ _ => rfl)
  obtain ⟨gT, hgT⟩ := IsLocalSet.exists_isLocalSetMean hh0
    (measurable_explored hc hηm fun _ => measurable_const) hlocT
  refine ⟨gS, gL, gT, hgS, hgL, hgT, ?_⟩
  filter_upwards [hgS.2.1, hgL.2.1, hgT.2.1, hside t gL gT hgL hgT] with ω ⟨v, hv, hgv⟩ ⟨vL, hvL, hgvL⟩
    ⟨vT, hvT, hgvT⟩ hsd hE
  obtain ⟨Ex, hEx, hsl⟩ := hsd hE.1 vL vT hvL hgvL hvT hgvT
  have hWc : ∀ ω', ContinuousOn (fun s => segDriver (γ' ω') s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ' ω')} :=
    fun ω' => (hseg ω').segDriver_spec.2.1
  obtain ⟨hvLt, hvRt⟩ := geomL_le_le_geomR (W := fun s ω => segDriver (γ' ω) s) (T := fun ω => capLife (γ' ω))
    hWc LP.twoSeedXL LP.twoSeedXR hE.1
  obtain ⟨Lg, hLg, hLe⟩ := exists_isDerivLog_shiftLift (hdom ω) (hlift ω) (n ω)
  exact pocketPrimeEnd_of_sideLimit φ (isConformal_shiftLift (hconf ω) (n ω)) hLg hLe (hWc ω)
    (hseg ω).segDriver_spec.1 hE.1 κ _ _ hvLt hvRt a' hv hgv hvL hgvL hvT hgvT hEx hsl

end PrimeEnd

/-! ### The side limits of the active component from the middle-curve side limits (Lemma71N's argument) -/

section SideLimit

open QuantumZipper (H Hbar chiC)
open QuantumZipper.CA (cayley cayleyInv)
open MartChar Lemma71M Lemma71E Lemma71D Coupling Lemma71G Lemma71C Lemma71K Lemma71L Sec6 LocalSets Lemma71N

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
  {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

/-- **The side limits of the active component** (`Lemma71M.PocketSideLimit`, `a' = 0`) **from the inherited branch and
the side limits along the middle curve** (the argument of `Lemma71N.isPocketChartData_of_curveSide`, whose intermediate
statement is exposed here): the outer arcs are `Lemma71N.ae_outerSideLimit`, the curve sides the hypothesis. -/
theorem sideLimit_of_curveSide [IsProbabilityMeasure P] (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ')
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {n : Ω → ℤ}
    (hN : ∀ᵐ ω ∂P, IsPocketBranch (β ω) (α ω) (c ω) (n ω))
    (hcurve : ∀ (t : ℝ≥0) (gL : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        PocketCurveSide (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) vL u₀
          (pocketInv (Lemma71E.shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t)
          (pocketGl κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
            (Lemma71E.shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t 0)
          (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t)
          (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t)) :
    ∀ (t : ℝ≥0) (gL gT : Ω → DistOn upperHalfPlaneOpens),
    IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
    IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
      (WholeField.centredField h u₀) P gT →
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL vT : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens,
        tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
      InnerProductSpace.HarmonicOnNhd vT
        (H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens,
        tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω →
          gT ω ψ = ∫ x, vT x * ψ x) →
      ∃ Ex : Set ℝ, Ex.Finite ∧
        PocketSideLimit (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
          (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) vL vT u₀
          (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t)
          (pocketGl κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
            (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t 0) Ex := by
  intro t gL gT hgL hgT
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, hγ62, hae⟩ := hS'
  obtain ⟨hc3, -, him3, -, -, -, -⟩ := Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, hbetw, hfr, hsegc, -, hmark⟩ := hpc'
  obtain ⟨hhL, hhR⟩ := cpf2_heights hκ θ₁ θ₂
  filter_upwards [ae_outerSideLimit href hκ hκ4 hθ₁ hθ₂ ha hb hS hpc hN hgT, hcurve t gL hgL, hae, hbetw, hfr,
    hmark] with ω hOSω hcv hω hbω hfrω hmω htl vL vT hvL hgvL hvT hgvT
  obtain ⟨-, -, -, -, -, -, hβα, hsβ, hsα, hsγ, hord, hγα, hγβ⟩ := hω
  obtain ⟨a', b', Ψ, hMk, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hseg, hrange⟩ := hmω
  have hg : PocketGood β α γ C c γ' ω :=
    ⟨hord, hγα, hγβ, hbω, hfrω, a', b', Ψ, hMk, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hseg⟩
  have hF : IsPocketFrame (β ω) (α ω) (C ω) (c ω) Ψ a' b' :=
    ⟨hsβ, hsα, hβα, hbω, hMk, hconf ω, hdom ω, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hfrω⟩
  have hCo : IsOpen (C ω) := (hC ω).1
  have hCH : C ω ⊆ H := (hC ω).2.2.2
  have hγc : Continuous (γ ω) := hc3 2 ω
  have hγH : ∀ t, γ ω t ∈ Hbar := fun t => him3 2 ω t
  -- the sets
  set τ := capTime G M Y β α γ t ω with hτdef
  have hAT : explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω =
      (range (β ω) ∪ range (α ω)) ∩ H := Three.explored_threeOuter β α γ ω (by rw [hsγ.2.2.1]; simp)
  have hA := Three.explored_threeStops β α γ (capTime G M Y β α γ t) ω
  set Γ : Set ℂ := γ ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ τ} with hΓdef
  have hτle := capTime_le_visit hg hCo hCH (hconf ω) (hdom ω) hγH hγc (hsegc ω) (hMiff ω) (hGeq ω) (hYeq ω) htl
  have hΓc : IsCompact Γ := by
    refine (Metric.isCompact_of_isClosed_isBounded (isClosed_le ENNReal.continuous_coe continuous_const)
      ((Metric.isBounded_Icc (0 : ℝ≥0)
        (visitClock (γ ω) (closure (cayley '' C ω)) (capInv (γ' ω) t)).toNNReal).subset fun s hs => ?_)).image hγc
    refine ⟨zero_le (a := s), ?_⟩
    have h3 := (show (s : ℝ≥0∞) ≤ τ from hs).trans hτle
    rw [ENNReal.ofReal] at h3
    exact_mod_cast h3
  have hAsub : explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω ⊆
      explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω ∪ Γ := by
    rw [hA, hAT]
    rintro z ⟨(hz | hz) | hz, hzH⟩
    · exact Or.inl ⟨Or.inl hz, hzH⟩
    · exact Or.inl ⟨Or.inr hz, hzH⟩
    · exact Or.inr hz
  have hfr' : frontier (C ω) ∩ H ⊆ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω := by
    rw [hAT]; exact fun z hz => ⟨hfrω hz, hz.2⟩
  have hΓK : ∀ z ∈ closure (cayley '' C ω) \ {wallPt (α ω) b'}, cayleyInv z ∈ Γ →
      Ψ z ∈ γ' ω '' Icc 0 (capInv (γ' ω) t) := fun z hzK hzΓ =>
    mem_image_of_mem_prefix hg hCo hCH (hconf ω) (hdom ω) hγH hγc hsγ.2.1 (hsegc ω) (hMiff ω) (hGeq ω) (hYeq ω) htl
      hΨi hseg hrange hzK (fun h1 => hF.one_notMem (h1 ▸ hzK)) hzΓ
  have hOS : OuterSideLimit (Lemma71E.shiftLift (c ω) (n ω)) vT u₀ (chiC κ)
      (sleLambda κ * (-1 - (fun _ : Fin 1 => cpf2RhoL κ θ₂) 0) - 0)
      (sleLambda κ * (1 + (fun _ : Fin 1 => cpf2RhoR κ θ₁) 0) - 0) := by
    simp only
    rw [hhL, hhR]
    exact hOSω vT hvT hgvT
  have hvL' : (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω) 0 t =
      -RealFlow.rightImg (fun s => -Ito.rpath (fun s => segDriver (γ' ω) s) s) 0 t := by
    simp only [geomL, LP.twoSeedXL, neg_zero]
    rfl
  have hvR' : (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) 0 t =
      RealFlow.rightImg (Ito.rpath fun s => segDriver (γ' ω) s) 0 t := by
    simp only [geomR, LP.twoSeedXR]
    rfl
  exact pocketSideLimit_of_curveSide (isConformal_shiftLift (hconf ω) (n ω)) (hdom ω) hCH hF.closePt_notMem hΨc hΨi
    hΨtop hΨe hF.one_notMem (hsegc ω) htl hΓc hAsub hfr' hΓK κ _ _ hvL' hvR' 0 hOS (hcv htl vL hvL hgvL)

end SideLimit

/-! ### The fixed-time pocket clause and Lemma 7.1's joint law -/

section Clause

open QuantumZipper (H chiC)
open MartChar Coupling Lemma71C Lemma71D Lemma71E Lemma71K Sec6 LocalSets Lemma71G Lemma71L Lemma71M Lemma71N

/-- **Lemma 7.1's fixed-time pocket clause (`Lemma72E.PocketClauseStatement`) from the geometric half of the
middle-curve side limits.** On every three-curve space: the pocket construction of PROVE-LEMMA71K
(`Lemma71K.exists_isPocketConstruction`), the inherited branch `n` (`Lemma71O.pocketBranchStatement`, proved), the
capacity data (`Lemma71L.exists_capData`); the side limits along the middle curve are
`pocketCurveSideStatement_of_middleLanding`,
those of the active component `sideLimit_of_curveSide`, the prime-end premise `primeEnd_of_sideLimit`, and the clause
`Lemma71M.isChartCouplingCharFunConst_of_primeEnd_ind` with B4 = `Lemma71M.measurable_chartAvoid_pocket` (`a' = 0`,
`k = χ`). Conditional helper (on `MiddleLandingStatement` and the §4.2 reference). -/
theorem pocketClauseStatement_of_middleLanding (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hL : MiddleLandingStatement.{u}) : Lemma72E.PocketClauseStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb Ω mΩ P hP h u₀ β α γ ζβ ζα ζγ hS
  obtain ⟨C, c, γ', hpc⟩ := exists_isPocketConstruction hS
  obtain ⟨n, hn, hN⟩ := Lemma71O.pocketBranchStatement κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀ β α γ ζβ ζα ζγ hS
    C c γ' hpc
  obtain ⟨G, M, Y, hG, hM, hY, hMiff, hGeq, hYeq⟩ := exists_capData hS hpc
  have hcurve := pocketCurveSideStatement_of_middleLanding href hL κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀ β α γ
    ζβ ζα ζγ hS C c γ' hpc G M Y hG hM hY hMiff hGeq hYeq n hn hN
  exact ⟨C, c, γ', n, 0, chiC κ, hpc, hn,
    isChartCouplingCharFunConst_of_primeEnd_ind hS hpc hG hM hY hMiff hGeq hYeq
      (c' := fun ω => shiftLift (c ω) (n ω)) (fun _ => rfl) (fun _ => rfl)
      (measurable_chartAvoid_pocket hS hpc hn _ _ 0)
      (primeEnd_of_sideLimit hS hpc hG hM hY
        (sideLimit_of_curveSide href hκ hκ4 hθ₁ hθ₂ ha hb hS hpc hMiff hGeq hYeq hN hcurve))⟩

/-- **Lemma 7.1's joint law (`Lemma72.Lemma71JointStatement`) from the geometric half of the middle-curve side
limits** and the three named inputs of the three-curve space (`Lemma72E.lemma71JointStatement_of_clause`). Conditional
helper. -/
theorem lemma71JointStatement_of_middleLanding (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hMD : Lemma71I.Lemma613ContactStatement.{u})
    (hL : MiddleLandingStatement.{u}) : Lemma72.Lemma71JointStatement.{u} :=
  Lemma72E.lemma71JointStatement_of_clause href h55 hMD (pocketClauseStatement_of_middleLanding href hL)

end Clause

end InteractingSLE.Sec7.Lemma71Q
