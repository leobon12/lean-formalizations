/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseStop
import InteractingSLE.Spec.Sec7.PocketCoupling

/-!
# The phase law of a field read through a retained chart, from the retained Gaussian kernel

Packet PROVE-PHASECLAUSE. Specification Aux. lemma 124 and Aux. lemma 125's proof (`source/spec/p385-432.md`
L171–L250, pp. 393–396: "Aux. lemma 124 preserves the actual canonical active mean at `T(S)`. The marked local-set law
gives its active Dirichlet covariance") and Aux. lemma 122 (pp. 389–391, the phase `d`); Astra's follow-up 5 §3.2 (R73:
"Right continuity of the retained filtration makes this constant measurable at time zero").

The landed `PocketCoupling.isCouplingCharFun_chartTransport` derives the zero-phase conditional-law clause from the
physical kernel at fixed times (given σ-algebras `𝓜_q ⊇ 𝓗_q`) and the zero-phase mean identification. For the phase
word the retained filtration `𝓗` must know the phase at time `0`, while the kernel σ-algebras `𝓜_q` know it only on
the live event at positive times. This file proves the phase law from

* the kernel at fixed times given `𝓜_q`;
* the mean identification with the phase `d_q` (`chartTransport c 1 a k M_q` is the coupling mean of `phaseProc (d q)`);
* `d_q = c₀` almost surely on the live event at positive times (the phase is constant);
* a **transfer hypothesis**: at positive times every event of `𝓗_q` inside the live event is almost surely an event of
  `𝓜_q` (for `𝓗_q = 𝓦 ∨ prefix events ∨ σ(c₀)` this is the measurability of the phase for `𝓜_q`, `PhaseClauseRead`).

## Main results

* `ae_condExp_cexp_chartTransport_eq_energy`: the conditional characteristic function of the transported field given
  `𝒢` from the physical kernel, with mean `chartTransport c 1 a k M` and the Loewner–Green energy (the mean-free part of
  `Restart.DomainMarkov.Mean.ae_condExp_cexp_chartTransport_eq_cfAt`);
* **`hasPhaseSafeLaw_chartTransport`**: `PhaseClause.HasPhaseSafeLaw` for the transported field;
* **`isPhaseCouplingCharFun_chartTransport`**: the phase clause `PhaseMart.IsPhaseCouplingCharFun` with the constant
  phase `c₀` for a driven curve and its geometric force coordinates.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseClause

open Restart.DomainMarkov Restart.DomainMarkov.Mean Restart.DomainMarkov.Aux79 Coupling Ito PhaseSel PhaseMart
  PocketTraversal Lemma71C

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-! ### The conditional characteristic function of the transported field -/

/-- **The transported field is Gaussian given `𝒢` with mean `chartTransport c 1 a k M` and the Loewner–Green energy of
the hull**, almost surely on an event `E ∈ 𝒢` inside the avoidance event (the mean-free part of
`Mean.ae_condExp_cexp_chartTransport_eq_cfAt`: the physical kernel on the chart preimage of the active domain,
conformal invariance and `WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov`). -/
theorem ae_condExp_cexp_chartTransport_eq_energy [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ) (q : ℝ≥0) {Mset : Set Ω}
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → (q : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q)) φ φ : ℝ) :
            ℂ)))
    (ψ : TestOn upperHalfPlaneOpens) {E : Set Ω} (hE : MeasurableSet[𝒢] E)
    (hEM : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ Mset ∧ ω ∈ Restart.DomainMarkov.avoidSet W ζ ψ q ∧ IsDrvReg W ζ ω) :
    ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k (h ω) ψ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k (M ω) ψ : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) q ψ : ℝ) : ℂ)) := by
  set Mset' : Set Ω := Mset ∩ {ω | IsDrvReg W ζ ω ∧ ω ∈ Restart.DomainMarkov.avoidSet W ζ ψ q} with hMset'
  have hcond' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset' →
      tsupport φ ⊆ (c ω).2.1 '' activeOr W ζ ψ q ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' activeOr W ζ ψ q ω) φ φ : ℝ) : ℂ)) := by
    intro φ
    filter_upwards [hcond φ] with ω hω hωM hsupp
    rw [activeOr_eq hωM.2.1 hωM.2.2] at hsupp ⊢
    exact hω hωM.1 hωM.2.2.1 hsupp
  have hEM' : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ Mset' := by
    filter_upwards [hEM] with ω hω hωE
    exact ⟨(hω hωE).1, (hω hωE).2.2, (hω hωE).2.1⟩
  have hkey := ae_condExp_cexp_chartTransport_sub h𝒢 hc hdom hfwd hliftm hliftc hh a k
    (isOpen_activeOr (W := W) (ζ := ζ) ψ q) (activeOr_subset ψ q) hcond' ψ hE hEM'
    (fun ω _ => tsupport_subset_activeOr ψ q ω)
  filter_upwards [hkey, hEM] with ω hk hω hωE
  obtain ⟨-, hav, hreg⟩ := hω hωE
  rw [hk hωE, activeOr_eq hreg hav]
  have hG := WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hreg.1 hreg.2 hav.1 ψ hav.2
  rw [hG]

/-! ### The phase law at positive times -/

/-- **(S) of the phase word for a field read through a retained chart, at positive times.** Let the chart be measurable
for `𝒢 ≤ 𝓜_q`, the physical field Gaussian given `𝓜_q` on the chart preimage of the active domain with mean `M_q`
(`hcond`), the chart transport of `M_q` the coupling mean of the phase-`d_q` word (`hmean`), `d_q = c₀` almost surely
on the live event at positive times, and every event of `𝓗_q` inside the live event almost surely an event of `𝓜_q`
at positive times (`h𝓗𝓜`). Then the transported field satisfies `HasPhaseSafeLaw` for `𝓗` with the phase `c₀`
(tower property for `𝓜_q`, `ae_condExp_cexp_chartTransport_eq_energy`). -/
theorem hasPhaseSafeLaw_chartTransport [IsProbabilityMeasure P] {𝓗 : Filtration ℝ≥0 mΩ} {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓜 : ∀ q, 𝓜 q ≤ mΩ) (h𝒢𝓜 : ∀ q, 𝒢 ≤ 𝓜 q)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ)
    (h𝓗𝓜 : ∀ q : ℝ≥0, 0 < q → ∀ D : Set Ω, MeasurableSet[𝓗 q] D →
      (∀ᵐ ω ∂P, ω ∈ D → (q : ℝ≥0∞) < ζ ω) → ∃ D' : Set Ω, MeasurableSet[𝓜 q] D' ∧ D =ᵐ[P] D')
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q)) φ φ : ℝ) :
            ℂ)))
    {d : ℝ≥0 → Ω → ℝ}
    (hmean : ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      ω ∈ Restart.DomainMarkov.avoidSet W ζ ψ q → Chart.chartTransport (hc ω) 1 a k (M q ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (phaseProc κ ρL ρR W VL VR (d q) ω q) z * ψ z)
    {c₀ : Ω → ℝ} (hdc : ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → d q ω = c₀ ω)
    (hreg : ∀ᵐ ω ∂P, IsDrvReg W ζ ω) :
    HasPhaseSafeLaw κ ρL ρR P 𝓗 ζ W VL VR c₀ fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  intro ψ q hq D hD hDa
  have h𝒢 : 𝒢 ≤ mΩ := (h𝒢𝓜 0).trans (h𝓜 0)
  have hlive : ∀ᵐ ω ∂P, ω ∈ D → (q : ℝ≥0∞) < ζ ω := by
    filter_upwards [hDa] with ω h hω using (h hω).1
  obtain ⟨D', hD'm, hDD'⟩ := h𝓗𝓜 q hq D hD hlive
  have hD'a : ∀ᵐ ω ∂P, ω ∈ D' → ω ∈ Restart.DomainMarkov.avoidSet W ζ ψ q := by
    filter_upwards [hDa, hDD'] with ω h1 h2 hω
    have e : (ω ∈ D) = (ω ∈ D') := h2
    exact h1 (e ▸ hω)
  have hX : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z))
      (fun z => (hfwd z).mono h𝒢 le_rfl) (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hh 1 a k
  have hint : Integrable (fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k (h ω) ψ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply ψ).comp hX)
  rw [setIntegral_congr_set hDD', setIntegral_congr_set hDD', ← setIntegral_condExp (h𝓜 q) hint hD'm]
  refine setIntegral_congr_ae ((h𝓜 q) _ hD'm) ?_
  have hkey := ae_condExp_cexp_chartTransport_eq_energy (𝒢 := 𝓜 q) (h𝓜 q) hc (fun z => h𝒢𝓜 q _ (hdom z))
    (fun z => (hfwd z).mono (h𝒢𝓜 q) le_rfl) (fun z => (hliftm z).mono (h𝒢𝓜 q) le_rfl) hliftc hh a k q
    (Mset := univ) (fun φ => by filter_upwards [hcond q φ] with ω hω _ using hω) ψ hD'm
    (by filter_upwards [hD'a, hreg] with ω h1 h2 hω using ⟨trivial, h1 hω, h2⟩)
  filter_upwards [hkey, hD'a, hmean q ψ, hdc q hq] with ω hk hav hm hd hωD
  have hav' := hav hωD
  have e : phaseProc κ ρL ρR W VL VR (d q) ω = phaseProc κ ρL ρR W VL VR c₀ ω := by
    funext s ξ
    show bheProc κ (shiftL κ ρL (d q ω)) (shiftR κ ρR (d q ω)) W VL VR ω s ξ + d q ω =
      bheProc κ (shiftL κ ρL (c₀ ω)) (shiftR κ ρR (c₀ ω)) W VL VR ω s ξ + c₀ ω
    rw [hd hav'.1]
  rw [hk hωD, hm hav', e]
  simp only [cfAt]
  congr 1
  push_cast
  ring

/-! ### The phase clause for a driven curve -/

/-- **The phase conditional-law clause of a field read through a retained chart, along a driven curve** (the phase
version of `PocketCoupling.isCouplingCharFun_chartTransport`): `hasPhaseSafeLaw_chartTransport` and
`isPhaseCouplingCharFun_of_hasPhaseSafeLaw` for the canonical driver of `γ` and its geometric force coordinates, with
the constant phase `c₀` measurable at time `0` of the usual augmentation of `𝓗`. -/
theorem isPhaseCouplingCharFun_chartTransport [IsProbabilityMeasure P] (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ}
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hpre : IsPrefixAdapted 𝓗 γ)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxL : Measurable[𝓗 0] xL)
    (hxR : Measurable[𝓗 0] xR) {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓜 : ∀ q, 𝓜 q ≤ mΩ) (h𝒢𝓜 : ∀ q, 𝒢 ≤ 𝓜 q)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ)
    (h𝓗𝓜 : ∀ q : ℝ≥0, 0 < q → ∀ D : Set Ω, MeasurableSet[𝓗 q] D →
      (∀ᵐ ω ∂P, ω ∈ D → (q : ℝ≥0∞) < capLife (γ ω)) → ∃ D' : Set Ω, MeasurableSet[𝓜 q] D' ∧ D =ᵐ[P] D')
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, (q : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q))
            φ φ : ℝ) : ℂ)))
    {d : ℝ≥0 → Ω → ℝ}
    (hmean : ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      ω ∈ Restart.DomainMarkov.avoidSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) ψ q →
      Chart.chartTransport (hc ω) 1 a k (M q ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
            (geomRW (fun t ω => segDriver (γ ω) t) xR) (d q) ω q) z * ψ z)
    {c₀ : Ω → ℝ} (hc₀ : Measurable[usualAugmentation 𝓗 P 0] c₀)
    (hdc : ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < capLife (γ ω) → d q ω = c₀ ω) :
    IsPhaseCouplingCharFun κ ρL ρR P (usualAugmentation 𝓗 P) (fun t ω => segDriver (γ ω) t)
      (geomLW (fun t ω => segDriver (γ ω) t) xL) (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun _ ω => c₀ ω)
      (fun ω => capLife (γ ω)) (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) := by
  have hWa := adaptedBefore_segDriver_of_isDrivenCurve hγ hpre
  have h𝒢 : 𝒢 ≤ mΩ := (h𝒢𝓜 0).trans (h𝓜 0)
  have hlaw := hasPhaseSafeLaw_chartTransport (𝓗 := 𝓗) (κ := κ) (ρL := ρL) (ρR := ρR)
    (W := fun t ω => segDriver (γ ω) t) (VL := geomLW (fun t ω => segDriver (γ ω) t) xL)
    (VR := geomRW (fun t ω => segDriver (γ ω) t) xR) (ζ := fun ω => capLife (γ ω)) hc 𝓜 h𝓜 h𝒢𝓜 hdom hfwd
    hliftm hliftc hh a k h𝓗𝓜 M hcond hmean hdc
    (ae_of_all _ fun ω => ⟨(hγ ω).segDriver_spec.2.1, (hγ ω).segDriver_spec.1⟩)
  have hX : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z))
      (fun z => (hfwd z).mono h𝒢 le_rfl) (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hh 1 a k
  exact isPhaseCouplingCharFun_of_hasPhaseSafeLaw hκ hc₀ _
    (fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp hX) hlaw
    (ae_of_all _ (PocketCoupling.isForceReg_segDriver hγ xL xR)) hWa
    (fun i => PocketPhaseMeans.adaptedBefore_geomLW (fun ω => (hγ ω).segDriver_spec.2.1) hWa hxL i)
    (fun j => PocketPhaseMeans.adaptedBefore_geomRW (fun ω => (hγ ω).segDriver_spec.2.1) hWa hxR j)

end InteractingSLE.Sec7.PhaseClause
