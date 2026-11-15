/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71MChart

/-!
# Lemma 7.1: `IsPocketChartData` from the side limits of the active pocket component

Packet PROVE-LEMMA71M. Combines

* the local-set means of the stopped union `A(τ_t)`, of the complete three curves and of the complete outer curves
  (Lemma 6.2 for transient curves, `Sec6.isLocalSet_explored_of_tendsto`, with the path-form capacity stop of
  PROVE-LEMMA71L and constant stops), and their harmonic representatives (almost surely, `IsLocalSetMean`);
* the explicit chart of the active component and the disc transfer (`Lemma71M.pocketPrimeEnd_of_sideLimit`);
* the prime-end form of the coupling clause with B4 discharged (`Lemma71M.isPocketChartData_of_pocketPrimeEnd`),

into **`isPocketChartData_of_sideLimit`**: on every three-curve space with the pocket construction of PROVE-LEMMA71K and
a `σ(β, α)`-measurable branch shift `n`, `Lemma72B.IsPocketChartData` follows from the side limits
(`Lemma71M.PocketSideLimit`) of the active component at every fixed capacity time, for every version of the two
complete-curve means and all their harmonic representatives. The side limits are the content of Proposition 6.1 for
the pocket (Remark 6.7: Proposition 3.8 comparisons on each side, the two-curve side heights, the inherited branch);
the hypothesis `hside` states exactly that.

Conditional helper (on the side limits); it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71M

open QuantumZipper (H Hbar)
open MartChar Coupling Lemma71C Lemma71D Lemma71E Lemma71K Sec6 LocalSets Lemma71G Lemma71L

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
  {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

/-- The lift of a shifted chart is the imaginary part of a logarithm of `ψ′` on the chart domain. -/
theorem exists_isDerivLog_shiftLift {c₀ : Chart} {C₀ : Set ℂ} (hdom : (c₀.dom : Set ℂ) = C₀)
    (hl : ∃ L : ℂ → ℂ, IsDerivLog c₀.1 L C₀ ∧ ∀ z ∈ C₀, c₀.2.2 z = (L z).im) (n : ℤ) :
    ∃ L : ℂ → ℂ, IsDerivLog (shiftLift c₀ n).1 L (shiftLift c₀ n).dom ∧
      ∀ z ∈ (shiftLift c₀ n).dom, (shiftLift c₀ n).2.2 z = (L z).im := by
  obtain ⟨L, hL, hLe⟩ := hl
  have hd : ((shiftLift c₀ n).dom : Set ℂ) = C₀ := hdom
  refine ⟨fun z => L z + 2 * Real.pi * n * Complex.I, ?_, fun z hz => ?_⟩
  · rw [hd]
    refine ⟨hL.1.add_const _, fun z hz => ?_⟩
    rw [Complex.exp_add, hL.2 z hz]
    have : Complex.exp (2 * Real.pi * n * Complex.I) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I n
      rw [← this]; ring_nf
    rw [this, mul_one]
    rfl
  · have hz' : z ∈ C₀ := by rw [← hd]; exact hz
    show c₀.2.2 z + 2 * Real.pi * n = (L z + 2 * Real.pi * n * Complex.I).im
    rw [hLe z hz', Complex.add_im]
    simp

/-- **`IsPocketChartData` from the side limits of the active component.** On every three-curve space with the
pocket construction of PROVE-LEMMA71K (`G`, `M`, `Y` from `Lemma71L.exists_capData`) and a `σ(β, α)`-measurable
branch shift `n`: if, at every fixed capacity time `t`, for every version `gL`, `gT` of the local-set means of the
complete three curves and of the complete outer curves, almost surely on `{t < capLife}` and for all their harmonic
representatives `vL`, `vT`, the active component has side limits (`PocketSideLimit`) outside a finite set with the
chart-side function `pocketGl` of the shifted chart, then `Lemma72B.IsPocketChartData` holds (chart
`shiftLift (c ω) (n ω)`, `k = χ`). Conditional helper (on the side limits). -/
theorem isPocketChartData_of_sideLimit [IsProbabilityMeasure P]
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' : ℝ}
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
    Lemma72B.IsPocketChartData κ θ₁ θ₂ P β α γ h
      (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
      γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) a'
      (QuantumZipper.chiC κ) := by
  refine isPocketChartData_of_pocketPrimeEnd hS hpc hG hM hY hMiff hGeq hYeq hn fun t φ => ?_
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

end Main

end InteractingSLE.Sec7.Lemma71M
