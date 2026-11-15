/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71MMeas

/-!
# Lemma 7.1: `IsPocketChartData` from the prime-end premise alone (B4 measurability discharged)

Packet PROVE-LEMMA71M. PROVE-LEMMA71L reduced the fixed-time chart coupling clause of Lemma 7.1 to two named inputs:
the prime-end premise P (`Lemma71L.PocketPrimeEnd`) and the measurability B4 of the avoidance event, the chart mean
and the chart variance for the prefix filtration. Only the values on the avoidance event enter the three-curve law, so
here the chart mean and variance are required to be measurable **on the avoidance event**
(`isChartCouplingCharFunConst_of_premise_ind`, `isChartCouplingCharFunConst_of_primeEnd_ind`: the proofs of
PROVE-LEMMA71L with the indicator forms), and these indicator forms are proved for the pocket construction
(`measurable_chartAvoid_pocket`, from `Lemma71M.measurable_chartAvoid`).

* **`isPocketChartData_of_pocketPrimeEnd`**: on every three-curve space with the pocket construction of PROVE-LEMMA71K
  and a `σ(β, α)`-measurable branch shift `n`, the prime-end premise P alone gives `Lemma72B.IsPocketChartData`.

Conditional helpers (on P); they replace no source theorem.
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

/-- **The fixed-time chart coupling clause from the three-curve law, with the chart mean and variance measurable on
the avoidance event** (`Lemma71L.isChartCouplingCharFunConst_of_premise` with the indicator forms of B4). -/
theorem isChartCouplingCharFunConst_of_premise_ind [IsProbabilityMeasure P]
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {c' : Ω → Chart} (hc' : ∀ ω, (c' ω).IsConformal)
    {ρL ρR : Fin 1 → ℝ} {a' : ℝ}
    (hmeas : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens),
      MeasurableSet[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          fun ω => chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
          (QuantumZipper.chiC κ) φ t) ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          fun ω => chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t))
    (hprem : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∃ gS gL gT : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)))
        (WholeField.centredField h u₀) P gS ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
        (WholeField.centredField h u₀) P gT ∧
      ∀ᵐ ω ∂P, IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t →
        IsThreeChartPremise (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
          (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀
          (QuantumZipper.chiC κ) φ
          (chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
            (QuantumZipper.chiC κ) φ t)
          (chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t)) :
    IsChartCouplingCharFunConst κ ρL ρR P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω)) c' a'
      (QuantumZipper.chiC κ) h := by
  intro t u hu φ
  have hS' := hS
  obtain ⟨-, hu₀, hh0, -, -, -, hβ62, hα62, hγ62, -⟩ := hS'
  have hpc' := hpc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hseg, -, -⟩ := hpc'
  obtain ⟨gS, gL, gT, hgS, hgL, hgT, hpr⟩ := hprem t φ
  obtain ⟨hEm, hMm, hVm⟩ := hmeas t φ
  have hpr' : ∀ᵐ ω ∂P, ω ∈ {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} →
      IsThreeChartPremise (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
        (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
        (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀
        (QuantumZipper.chiC κ) φ
        ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          (fun ω => chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
            (QuantumZipper.chiC κ) φ t) ω)
        ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          (fun ω => chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t) ω) := by
    filter_upwards [hpr] with ω hω hE
    have hE' : ω ∈ {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} := hE
    rw [indicator_of_mem hE', indicator_of_mem hE']
    exact hω hE
  have hlaw := ae_condExp_exp_eq_three_of_le_aeSigma
    (𝒢 := prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t)
    hh0 hβ62 hα62 hγ62 (measurable_capStop hG hM hY t) (capStop_galmarino t) (fun _ => rfl) hgS hgL hgT hu₀.1
    hu₀.2.1 (QuantumZipper.chiC κ) φ
    ((prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ').le t)
    ((prefixFiltrationOf_le_aeSigma hS hpc hG hM hY hMiff hGeq hYeq t).trans (aeSigma_mono P le_sup_right))
    hEm hMm hVm hpr'
  filter_upwards [hlaw] with ω hω hlt hsupp
  have hE : IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t := ⟨hlt, hsupp⟩
  have h1 := hω hE
  have hE' : ω ∈ {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} := hE
  rw [indicator_of_mem hE', indicator_of_mem hE'] at h1
  have hfield : (fun ω' => cexp (I * ((WholeField.centredField h u₀ ω' φ + ∫ x, u₀ x * φ x : ℝ) : ℂ))) =
      fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) := by
    funext ω'
    rw [WholeField.centredField_apply h hu₀.1 ω' φ, sub_add_cancel]
  rw [hfield] at h1
  rw [h1]
  have hWc : ∀ ω'', ContinuousOn (fun s => segDriver (γ' ω'') s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ' ω'')} :=
    fun ω'' => (hseg ω'').segDriver_spec.2.1
  obtain ⟨hvL, hvR⟩ := geomL_le_le_geomR (W := fun s ω => segDriver (γ' ω) s) (T := fun ω => capLife (γ' ω))
    hWc LP.twoSeedXL LP.twoSeedXR hlt
  have hkey := integral_couplingMean_eq_chartMean (κ := κ) (ρL := ρL) (ρR := ρR) (a := a')
    (k := QuantumZipper.chiC κ) (vL := fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
    (vR := fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (hc' ω) (hWc ω) hE hvL hvR (hu ω)
  have hkey' : (∫ z, (couplingMean κ (fun s : ℝ => segDriver (γ' ω) s.toNNReal) (t : ℝ) (u ω) ((c' ω).1 z) - a' -
      QuantumZipper.chiC κ * (c' ω).2.2 z) * φ z) =
      chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
        (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
        (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
        (QuantumZipper.chiC κ) φ t := hkey
  rw [hkey', Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have hr : Ito.rpath (fun s => segDriver (γ' ω) s) = fun s : ℝ => segDriver (γ' ω) s.toNNReal := rfl
  simp only [chartVar, hr]
  push_cast
  ring

/-- **The fixed-time chart coupling clause from the prime-end premise**, B4 in indicator form
(`Lemma71L.isChartCouplingCharFunConst_of_primeEnd` with the indicator forms). -/
theorem isChartCouplingCharFunConst_of_primeEnd_ind [IsProbabilityMeasure P]
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {c' : Ω → Chart} (hc'1 : ∀ ω, (c' ω).1 = (c ω).1)
    (hc'2 : ∀ ω, (c' ω).2.1 = (c ω).2.1) {ρL ρR : Fin 1 → ℝ} {a' : ℝ}
    (hmeas : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens),
      MeasurableSet[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          fun ω => chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
          (QuantumZipper.chiC κ) φ t) ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          fun ω => chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t))
    (hP : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∃ gS gL gT : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)))
        (WholeField.centredField h u₀) P gS ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
        (WholeField.centredField h u₀) P gT ∧
      ∀ᵐ ω ∂P, IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t →
        PocketPrimeEnd (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
          (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀
          (QuantumZipper.chiC κ) φ
          ((c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t))
          (chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
            (QuantumZipper.chiC κ) φ t)) :
    IsChartCouplingCharFunConst κ ρL ρR P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω)) c' a'
      (QuantumZipper.chiC κ) h := by
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, -, -, hseg, -, -⟩ := hpc'
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, -, -, hγ62, -⟩ := hS'
  have hc' : ∀ ω, (c' ω).IsConformal := fun ω => by
    have := hconf ω
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · rw [hc'2]; exact this.1
    · rw [hc'2]; exact this.2.1
    · rw [hc'1, hc'2]; exact this.2.2 w hw
  refine isChartCouplingCharFunConst_of_premise_ind hS hpc hG hM hY hMiff hGeq hYeq hc' hmeas fun t φ => ?_
  obtain ⟨gS, gL, gT, hgS, hgL, hgT, hpr⟩ := hP t φ
  refine ⟨gS, gL, gT, hgS, hgL, hgT, ?_⟩
  filter_upwards [hpr, ae_pocketGood hS hpc] with ω hω hg hE
  have hΓ := hseg ω
  have hD := IsSegCurve.fwdHull_segDriver_eq hΓ (NNReal.coe_nonneg t)
    (by rw [ENNReal.ofReal_coe_nnreal]; exact hE.1)
  -- a point of the chart domain
  obtain ⟨R, hR, hKR⟩ := hD.2.exists_subset_ball
  set w₀ : ℂ := ((R + 1 : ℝ) : ℂ) * I with hw₀
  have hw₀H : w₀ ∈ H := by
    show (0 : ℝ) < (((R + 1 : ℝ) : ℂ) * I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_zero,
      add_zero, mul_one]
    linarith
  have hw₀K : w₀ ∉ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t := by
    rw [hD.1]
    intro hw
    have := mem_ball_zero_iff.1 (hKR hw)
    rw [hw₀, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      at this
    linarith
  have hz₀ : (c ω).2.1 w₀ ∈ (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t) :=
    ⟨w₀, ⟨hw₀H, hw₀K⟩, rfl⟩
  obtain ⟨hz₀A, hcomp⟩ := connectedComponentIn_eq_image hg (hC ω).1 (hC ω).2.2.2 (hconf ω) (hdom ω)
    (fun s => hγ62.2.2.1 ω s) (hγ62.1 ω) (hγ62.2.1 ω) hΓ (hMiff ω) (hGeq ω) (hYeq ω) hE.1 hz₀
  have hφ : tsupport φ ⊆ (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t) := by
    have := hE.2
    rw [hc'2] at this
    exact this
  have hV : chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t = QuantumZipper.zeroGFFTestCov
      ((c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t)) φ φ := by
    simp only [chartVar, hc'2]
    rfl
  rw [hV]
  exact isThreeChartPremise_of_pocketPrimeEnd hz₀A hcomp hφ (hω hE)

/-- **B4 for the pocket construction**: the avoidance event at `t` is in the prefix filtration at `t`, and the chart
mean and the chart variance on it are measurable for it (charts `shiftLift (c ω) (n ω)`, `n` `σ(β, α)`-measurable). -/
theorem measurable_chartAvoid_pocket (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) (ρL ρR : Fin 1 → ℝ)
    (a' : ℝ) (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t} ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t}.indicator
          fun ω => chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (shiftLift (c ω) (n ω)) a'
          (QuantumZipper.chiC κ) φ t) ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t}.indicator
          fun ω => chartVar (fun s => segDriver (γ' ω) s) (shiftLift (c ω) (n ω)) φ t) := by
  obtain ⟨hC, hCm, hconf, hdom, hfm, hlm, hlc, -, -, -, hseg, hγ'm, -⟩ := hpc
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, hγ62, -⟩ := hS
  have hβm : Measurable β := measurable_pi_iff.2 hβ62.2.2.2.1
  have hαm : Measurable α := measurable_pi_iff.2 hα62.2.2.2.1
  have hγm : Measurable γ := measurable_pi_iff.2 hγ62.2.2.2.1
  have h₀ : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ mΩ := (hβm.prodMk hαm).comap_le
  have h𝓑 : MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
      MeasurableSpace.comap γ MeasurableSpace.pi ⊔ Ito.nullSets P ≤ mΩ :=
    sup_le (sup_le (sup_le hβm.comap_le hαm.comap_le) hγm.comap_le) (Ito.nullSets_le P)
  have hγ'mΩ : ∀ u, Measurable fun ω => γ' ω u := fun u => (hγ'm u).mono h𝓑 le_rfl
  have hpm : ∀ r n k, MeasurableSet (prefixEvent γ' r n k) := fun r n k =>
    measurableSet_prefixEvent hseg (fun u _ => hγ'mΩ u) r n k
  have hpre : IsPrefixAdapted (prefixFiltrationOf (mΩ := mΩ)
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') γ' :=
    isPrefixAdapted_prefixFiltrationOf _ γ' hpm
  have hWa := adaptedBefore_segDriver hseg hpre
  have hc : ∀ ω, ContinuousOn (fun s => segDriver (γ' ω) s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ' ω)} :=
    fun ω => (hseg ω).segDriver_spec.2.1
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hdomm : ∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ (c ω).dom} := fun z => by
    have e : {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := by
      ext ω
      show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
      rw [hdom ω]
    rw [e]
    exact @Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) C hCo hCm z
  exact measurable_chartAvoid (c := fun ω => shiftLift (c ω) (n ω)) κ ρL ρR a' (QuantumZipper.chiC κ) hWa hc
    (fun i => adaptedBefore_geomL hc hWa LP.twoSeedXL i) (fun i => adaptedBefore_geomR hc hWa LP.twoSeedXR i) t
    (le_prefixFiltrationOf h₀ γ' t) hCo hCm (fun ω => isConformal_shiftLift (hconf ω) (n ω)) hdom hfm
    (fun z => @measurable_indicator_shiftLift Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) c n hn
      z (hdomm z) (hlm z))
    (fun ω => continuousOn_shiftLift (hlc ω) (n ω)) φ

/-- **`IsPocketChartData` from the prime-end premise P alone.** On every three-curve space with the pocket
construction of PROVE-LEMMA71K (`G`, `M`, `Y` from `Lemma71L.exists_capData`) and a `σ(β, α)`-measurable branch
shift `n`, the prime-end premise P for the charts `shiftLift (c ω) (n ω)` gives `Lemma72B.IsPocketChartData` (chart
`shiftLift (c ω) (n ω)`, `k = χ`): B4 is `measurable_chartAvoid_pocket`. Conditional helper (on P). -/
theorem isPocketChartData_of_pocketPrimeEnd [IsProbabilityMeasure P]
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' : ℝ}
    (hP : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∃ gS gL gT : Ω → DistOn upperHalfPlaneOpens,
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
            (QuantumZipper.chiC κ) φ t)) :
    Lemma72B.IsPocketChartData κ θ₁ θ₂ P β α γ h
      (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
      γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) a'
      (QuantumZipper.chiC κ) :=
  isPocketChartData_of_isPocketConstruction hS hpc hn
    (isChartCouplingCharFunConst_of_primeEnd_ind hS hpc hG hM hY hMiff hGeq hYeq
      (c' := fun ω => shiftLift (c ω) (n ω)) (fun _ => rfl) (fun _ => rfl)
      (measurable_chartAvoid_pocket hS hpc hn _ _ a') hP)

end Main

end InteractingSLE.Sec7.Lemma71M
