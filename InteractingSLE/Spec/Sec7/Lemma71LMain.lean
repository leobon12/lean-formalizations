/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71LComp
import InteractingSLE.Spec.Sec7.Lemma71LLaw

/-!
# Lemma 7.1: the fixed-time chart coupling clause from the three-curve law

Packet PROVE-LEMMA71L. Specification §7.1 (`source/spec/p193-240.md` L590–L595, pp. 224–225): "For each bounded
stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies to the revealed outer curves
and the middle prefix. […] The means in all the remaining components are those of the three-curve result in Remark 6.7.
In particular, in the active component they have the two seed heights (CPF2), with the inherited
logarithmic-derivative branch."

**`isChartCouplingCharFunConst_of_premise`**: on a three-curve space with the pocket construction of PROVE-LEMMA71K, the
fixed-time chart coupling clause `hcf` of `Lemma71K.isPocketChartData_of_isPocketConstruction`
(`Lemma71D.IsChartCouplingCharFunConst` for the prefix filtration of the mapped segment, `k = χ`) follows from

* `hmeas`: the avoidance event, the chart mean and the chart variance at time `t` are measurable for the prefix
  filtration at `t` (B4, measurability);
* `hprem`: versions of the local-set means of `A(τ_t)`, of the complete three curves and of the complete outer curves
  for which, almost surely on the avoidance event, the premise of the three-curve law of Remark 6.7
  (`Lemma71G.IsThreeChartPremise`) holds with the chart mean and the chart variance as its values (P).

The proof applies the three-curve law at the capacity time `τ_t = capTime … t` (a path-form stopping time of the
labelled histories, `capStop`) to `𝒢 = prefixFiltrationOf σ(β, α) γ' t`, which lies in the completed labelled histories
(R3/G7, `prefixFiltrationOf_le_aeSigma`; law `ae_condExp_exp_eq_three_of_le_aeSigma`), to the centred field with the
harmonic shift `u₀`, and identifies the chart mean with the clause's mean
(`Lemma71D.integral_couplingMean_eq_chartMean`).

Conditional helper; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71L

open QuantumZipper (H Hbar)
open MartChar Coupling Lemma71C Lemma71D Lemma71E Lemma71K Sec6 LocalSets Lemma71G

theorem aeSigma_mono {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω} [MeasurableSpace Ω] (P : Measure Ω) (h : m₁ ≤ m₂) :
    aeSigma m₁ P ≤ aeSigma m₂ P := fun _ ⟨G', hG', he⟩ => ⟨G', h _ hG', he⟩

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
  {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

/-- **The fixed-time chart coupling clause of Lemma 7.1 from the three-curve law** (see the module docstring).
`G`, `M`, `Y` are the chart, its domain and the closing point as functions of the outer histories
(`exists_capData`); `c'` is any family of conformal charts (e.g. `shiftLift (c ω) (n ω)`). -/
theorem isChartCouplingCharFunConst_of_premise [IsProbabilityMeasure P]
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
        γ' t] (fun ω => chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
          (QuantumZipper.chiC κ) φ t) ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] (fun ω => chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t))
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
  have hlaw := ae_condExp_exp_eq_three_of_le_aeSigma
    (𝒢 := prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t)
    hh0 hβ62 hα62 hγ62 (measurable_capStop hG hM hY t) (capStop_galmarino t) (fun _ => rfl) hgS hgL hgT hu₀.1
    hu₀.2.1 (QuantumZipper.chiC κ) φ
    ((prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ').le t)
    ((prefixFiltrationOf_le_aeSigma hS hpc hG hM hY hMiff hGeq hYeq t).trans (aeSigma_mono P le_sup_right))
    hEm hMm hVm hpr
  filter_upwards [hlaw] with ω hω hlt hsupp
  have hE : IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t := ⟨hlt, hsupp⟩
  have h1 := hω hE
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

/-! ### The premise on the explicit chart domain -/

/-- **The prime-end premise of the three-curve law on a given domain `D`** (P): `IsThreeChartPremise` with the
component replaced by `D` and without the variance value — harmonic representatives `v`, `vL`, `vT` of the local-set
means of `A`, of the full union `AL` and of the outer union `AT`, and a chart `(f, φc, G, Lc, E)` of `D` (`f` from the
disc, `φc` onto `ℍ`, `G` bounded harmonic, `Lc` a continuous argument of `φc′`, `E` finite) such that every prime end
outside `E` has an impression `p` on `A ∪ ℝ` with the full union inside `A` near `p` and the full-union mean there
with the boundary values of `G ∘ φc − χ Lc`, or on `AT ∪ ℝ` with `A` inside the outer union near `p` and the
outer-union mean there with those boundary values; and `M` is the pairing of `G ∘ φc − χ Lc` with `φ`. -/
def PocketPrimeEnd (A AL AT : Set ℂ) (gS gL gT : DistOn upperHalfPlaneOpens) (F : ℂ → ℝ) (χ : ℝ)
    (φ : TestOn upperHalfPlaneOpens) (D : Set ℂ) (M : ℝ) : Prop :=
  ∃ v vL vT : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A) ∧
    (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ A → gS ψ = ∫ x, v x * ψ x) ∧
    InnerProductSpace.HarmonicOnNhd vL (H \ AL) ∧
    (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ AL → gL ψ = ∫ x, vL x * ψ x) ∧
    InnerProductSpace.HarmonicOnNhd vT (H \ AT) ∧
    (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ AT → gT ψ = ∫ x, vT x * ψ x) ∧
    ∃ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      SupercriticalConformalCovariance.IsConformalBijection f (ball 0 1) D ∧
      SupercriticalConformalCovariance.IsConformalBijection φc D {w : ℂ | 0 < w.im} ∧
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} ∧ (∃ M', ∀ w : ℂ, 0 < w.im → |G w| ≤ M') ∧
      ContinuousOn Lc D ∧ (∀ z ∈ D, deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) ∧ E.Finite ∧
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ A ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, AL ∩ ball p r ⊆ A) ∧
            Tendsto (fun ζ => (vL (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ AT ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A ∩ ball p r ⊆ AT) ∧
            Tendsto (fun ζ => (vT (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ))) (𝓝[ball 0 1] q)
              (𝓝 0)))) ∧
      (∫ x, (G (φc x) - χ * Lc x) * φ x) = M

/-- **The three-curve premise from the prime-end premise on a domain equal to the component.** -/
theorem isThreeChartPremise_of_pocketPrimeEnd {A AL AT : Set ℂ} {gS gL gT : DistOn upperHalfPlaneOpens}
    {F : ℂ → ℝ} {χ : ℝ} {φ : TestOn upperHalfPlaneOpens} {D : Set ℂ} {M : ℝ} {z₀ : ℂ} (hz₀ : z₀ ∈ H \ A)
    (hD : connectedComponentIn (H \ A) z₀ = D) (hφ : tsupport φ ⊆ D)
    (hP : PocketPrimeEnd A AL AT gS gL gT F χ φ D M) :
    IsThreeChartPremise A AL AT gS gL gT F χ φ M (QuantumZipper.zeroGFFTestCov D φ φ) := by
  obtain ⟨v, vL, vT, hv, hgv, hvL, hgvL, hvT, hgvT, f, φc, G, Lc, E, hf, hφc, hG, hGb, hLc, hder, hE, hpe, hM⟩ :=
    hP
  rw [← hD] at hφ hf hφc hLc hder ⊢
  exact ⟨z₀, hz₀, hφ, v, vL, vT, hv, hgv, hvL, hgvL, hvT, hgvT, f, φc, G, Lc, E, hf, hφc, hG, hGb, hLc, hder, hE,
    hpe, hM, rfl⟩

/-- **The fixed-time chart coupling clause of Lemma 7.1 from the prime-end premise on the chart domain** (P) and the
measurability of the chart mean and variance (B4): `isChartCouplingCharFunConst_of_premise` with the component and
the variance identified (`connectedComponentIn_eq_image`). The charts `c'` share the forward and inverse maps of the
pocket chart `c` (e.g. `shiftLift (c ω) (n ω)`). -/
theorem isChartCouplingCharFunConst_of_primeEnd [IsProbabilityMeasure P]
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
        γ' t] (fun ω => chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
          (QuantumZipper.chiC κ) φ t) ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] (fun ω => chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t))
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
  refine isChartCouplingCharFunConst_of_premise hS hpc hG hM hY hMiff hGeq hYeq hc' hmeas fun t φ => ?_
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

/-- **`IsPocketChartData` on every three-curve space from the prime-end premise and the measurability of the chart
mean** (`Lemma71K.isPocketChartData_of_isPocketConstruction` with `hcf` from `isChartCouplingCharFunConst_of_primeEnd`;
chart `shiftLift (c ω) (n ω)`, `k = χ`). Conditional helper. -/
theorem isPocketChartData_of_primeEnd [IsProbabilityMeasure P]
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' : ℝ}
    (hmeas : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens),
      MeasurableSet[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t} ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] (fun ω => chartMean κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
          (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (shiftLift (c ω) (n ω)) a'
          (QuantumZipper.chiC κ) φ t) ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] (fun ω => chartVar (fun s => segDriver (γ' ω) s) (shiftLift (c ω) (n ω)) φ t))
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
    (isChartCouplingCharFunConst_of_primeEnd hS hpc hG hM hY hMiff hGeq hYeq (c' := fun ω => shiftLift (c ω) (n ω))
      (fun _ => rfl) (fun _ => rfl) hmeas hP)

end Main

end InteractingSLE.Sec7.Lemma71L
