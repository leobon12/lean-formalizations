/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovAux79
import InteractingSLE.Spec.Restart.DomainMarkovMeanLoc

/-!
# (S) for a chart field from the kernels and the mean identifications on deterministic later lines

Packet PROVE-DOMAINMARKOV8 (specification Aux. lemmas 77 and 79, pp. 287–290). In a retained setting the field is read
through a chart `c` fixed at time `0` (`X = chartTransport c 1 a k h`), and the continuation is a curve in that chart
with capacity clock `Qc` (the chart capacity reached at physical time `t`). This file combines

* `Aux79.hasSafeLaw_of_lineLaw` (the discretization in physical time), with
* the chart law on a random sub-domain (`Mean.ae_condExp_cexp_chartTransport_sub`, PROVE-DOMAINMARKOV6), here at the
  **random** capacity time `Qc t` (`ae_condExp_cexp_chartTransport_eq_cfAt_rand`),

so that K2's input (S) reduces to two statements on **deterministic** physical later lines `t`:

* **(Aux. 77 at the line `t`)** given a σ-algebra `𝒢L t` containing the physical filtration at `t`, the physical field
  paired with test functions supported in the chart preimage `inv(ℍ ∖ K̃_{Qc t})` of the continuation's active domain
  is Gaussian with a mean `M t` and the zero-boundary covariance of that domain;
* **(Aux. 79 at the line `t`)** the chart transport of `M t` is the canonical finite-force mean `𝔥_{Qc t}` of the
  continuation at the capacity time `Qc t`.

## Main results

* `ae_condExp_cexp_chartTransport_eq_cfAt_rand`;
* **`hasSafeLaw_of_lineKernel`**: (S) for the chart field from the two line statements;
* `setIntegral_lapTest_of_lineLocal`, **`hasSafeMembers_of_lineLocal`**: (L) for the chart field from the
  history-marked locality of the physical later-line sets `B t` with `ℍ ∖ B t = inv(ℍ ∖ K̃_{Qc t})` (the locality
  half of Aux. lemma 77 at deterministic lines; `Mean.hasSafeMembers_chartTransport` at the random capacity time).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H zeroGFFTestCov fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.DomainMarkov.Aux79

open Coupling K2 Mean

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The transported field has the coupling characteristic functional at a random capacity time `r`**
(`Mean.ae_condExp_cexp_chartTransport_eq_cfAt` with the deterministic time replaced by `r ω`; same proof). -/
theorem ae_condExp_cexp_chartTransport_eq_cfAt_rand (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ) (r : Ω → ℝ≥0) {Mset : Set Ω}
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → (r ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r ω))) φ φ :
            ℝ) : ℂ)))
    (ψ : TestOn upperHalfPlaneOpens) {E : Set Ω} (hE : MeasurableSet[𝒢] E)
    (hEM : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ Mset ∧ ω ∈ DomainMarkov.avoidSet W ζ ψ (r ω) ∧ IsDrvReg W ζ ω)
    (hmean : ∀ᵐ ω ∂P, ω ∈ E → Chart.chartTransport (hc ω) 1 a k (M ω) ψ =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (r ω) (bheProc κ ρL ρR W VL VR ω (r ω)) z * ψ z) :
    ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k (h ω) ψ : ℂ)) | 𝒢] ω =
        cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 r ω := by
  set V : Ω → Set ℂ := fun ω => activeOr W ζ ψ (r ω) ω with hV
  set Mset' : Set Ω := Mset ∩ {ω | IsDrvReg W ζ ω ∧ ω ∈ DomainMarkov.avoidSet W ζ ψ (r ω)} with hMset'
  have hcond' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset' →
      tsupport φ ⊆ (c ω).2.1 '' V ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' V ω) φ φ : ℝ) : ℂ)) := by
    intro φ
    filter_upwards [hcond φ] with ω hω hωM hsupp
    simp only [hV] at hsupp ⊢
    rw [activeOr_eq hωM.2.1 hωM.2.2] at hsupp ⊢
    exact hω hωM.1 hωM.2.2.1 hsupp
  have hEM' : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ Mset' := by
    filter_upwards [hEM] with ω hω hωE
    exact ⟨(hω hωE).1, (hω hωE).2.2, (hω hωE).2.1⟩
  have hkey := ae_condExp_cexp_chartTransport_sub h𝒢 hc hdom hfwd hliftm hliftc hh a k (V := V)
    (fun ω => isOpen_activeOr ψ (r ω) ω) (fun ω => activeOr_subset ψ (r ω) ω) hcond' ψ hE hEM'
    (fun ω _ => tsupport_subset_activeOr ψ (r ω) ω)
  filter_upwards [hkey, hEM, hmean] with ω hk hω hm hωE
  obtain ⟨-, hav, hreg⟩ := hω hωE
  rw [hk hωE]
  simp only [hV]
  rw [activeOr_eq hreg hav, hm hωE, cfAt]
  have hG := WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hreg.1 hreg.2 hav.1 ψ hav.2
  rw [hG]
  congr 1
  push_cast
  ring

/-- **(S) for a chart field from the kernels and the mean identifications on deterministic later lines.** Let the
conformal chart `c` (continuous harmonic lifts) be measurable for the physical filtration at time `0`, the live event
`F` an event of it, and the clock `Qc`, filtrations `𝓖`, `𝓗'`, regularity and line safe events as in
`hasSafeLaw_of_lineLaw`. Suppose that at every deterministic physical time `t`, given a σ-algebra `𝒢L t ⊇ 𝓖_t`,
almost surely on `F`:

* (Aux. 77 at the line) before the lifetime, the physical field paired with test functions supported in
  `inv(ℍ ∖ K̃_{Qc t})` is Gaussian with mean `M t` and the zero-boundary covariance of `inv(ℍ ∖ K̃_{Qc t})`;
* (Aux. 79 at the line) on the line safe event of `ψ`, the chart transport of `M t` tested against `ψ` is the
  canonical finite-force mean `𝔥_{Qc t}` of the continuation tested against `ψ`.

Then the transported field `chartTransport c 1 a k h` has K2's input (S) for `𝓗'`. -/
theorem hasSafeLaw_of_lineKernel {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω} (hF : MeasurableSet[𝓖 0] F)
    {Qc : ℝ≥0 → Ω → ℝ≥0} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω) (hQ0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t] (lineSafe Qc W ζ (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) φ φ :
            ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ lineSafe Qc W ζ (tsupport ψ) t → Chart.chartTransport (hc ω) 1 a k (M t ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (Qc t ω) (bheProc κ ρL ρR W VL VR ω (Qc t ω)) z * ψ z) :
    HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) ψ :=
    fun ψ => ((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp
      (Chart.measurable_chartTransport_random' hc (fun z => 𝓖.le 0 _ (hdom z))
        (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hliftc hh 1 a k)
  refine hasSafeLaw_of_lineLaw hXψ hQc hQm hQ0 hQa h𝓗' hreach hreg hS 𝒢L h𝒢L h𝒢Lm fun ψ t => ?_
  have h0t : 𝓖 0 ≤ 𝒢L t := (𝓖.mono (zero_le (a := t))).trans (h𝒢L t)
  have hE : MeasurableSet[𝒢L t] (F ∩ lineSafe Qc W ζ (tsupport ψ) t) :=
    (h0t _ hF).inter (h𝒢L t _ (hS ψ t))
  have hkey := ae_condExp_cexp_chartTransport_eq_cfAt_rand (P := P) (ρL := ρL) (ρR := ρR) (VL := VL) (VR := VR)
    (h𝒢Lm t) hc (fun z => h0t _ (hdom z)) (fun z => (hfwd z).mono h0t le_rfl)
    (fun z => (hliftm z).mono h0t le_rfl) hliftc hh a k (Qc t) (Mset := F) (fun φ => by
      filter_upwards [hker t φ] with ω hω hωF hlt hsupp using hω hωF hlt hsupp) ψ hE
    (by
      filter_upwards [hreg] with ω hω hωE
      exact ⟨hωE.1, hωE.2, (hω hωE.1).2.1, (hω hωE.1).1⟩)
    (by
      filter_upwards [hmean t ψ] with ω hω hωE using hω hωE.1 hωE.2)
  filter_upwards [hkey] with ω hω hωF hωS
  exact hω ⟨hωF, hωS⟩

open LocalSets WholeField LQGMetric.MarkovZB in
/-- **The member identities at the random capacity time `r`** (`Mean.hasSafeMembers_chartTransport`'s proof, for one
event `D` and the random time `r`): if a hitting-measurable relatively closed random set `B` is a history-marked local
set of `h − u₀` for marks `𝒢`, with `ℍ ∖ B = inv(ℍ ∖ K̃_r)` almost surely on `F ∩ {r < ζ}`, then on every
`𝒢`-event `D` inside `F` on which the balls avoid `K̃_r` before the lifetime, the chart field has the member
identities of the balls. -/
theorem setIntegral_lapTest_of_lineLocal {F : Set Ω} {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (h𝒢 : 𝒢 ≤ mΩ)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ) (r : Ω → ℝ≥0)
    (B : Ω → Set ℂ) (hBm : Measurable[mΩ, hittingSigma] B) (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hloc : IsHistoryAvoidanceLocal 𝒢 B (centredField h u₀) P)
    (hBK : ∀ᵐ ω ∂P, ω ∈ F → (r ω : ℝ≥0∞) < ζ ω →
      H \ B ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r ω)))
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsDrvReg W ζ ω) (Fb : Finset (ℚ × ℚ × ℚ)) (hFH : ballsK Fb ⊆ H) {D : Set Ω}
    (hD𝒢 : MeasurableSet[𝒢] D)
    (hDs : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ (r ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (r ω)))
    (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in D, Complex.exp (Complex.I *
        (Chart.chartTransport (hc ω) 1 a k (h ω) (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂P =
      projFactor (ballsOpen Fb) f Ξ *
        ∫ ω in D, Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k (h ω) Ξ : ℂ)) ∂P := by
  have hDm : MeasurableSet D := h𝒢 _ hD𝒢
  by_cases hPD : P D = 0
  · rw [setIntegral_measure_zero _ hPD, setIntegral_measure_zero _ hPD, mul_zero]
  have : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hDac : P[|D] ≪ P := cond_absolutelyContinuous
  have hDae : ∀ᵐ ω ∂(P[|D]), ω ∈ D := ae_cond_mem hDm
  set K : Ω → Set ℂ := fun ω => relHull W ζ (r ω) ω with hK
  have hBK' : ∀ᵐ ω ∂(P[|D]), H \ B ω = (c ω).2.1 '' (H \ K ω) := by
    filter_upwards [hDae, hDac.ae_le hDs, hDac.ae_le hBK, hDac.ae_le hreg] with ω hωD h1 h2 h3
    obtain ⟨hωF, hsζ, -⟩ := h1 hωD
    simp only [hK]
    rw [relHull_eq (h3 hωF) hsζ]
    exact h2 hωF hsζ
  obtain ⟨M, hMm, hMharm, hMcond⟩ := LocalExt.exists_condDecomp_chart (P := P) hhm hu₀ hh0 hc
    hdom hfwd hliftm hliftc hlift h𝒢 hBm hBc hloc (fun ω => relHull_relClosed (W := W) (ζ := ζ) (r ω) ω) hD𝒢 hPD
    hBK' a k
  have h𝒦 : germSigma B (centredField h u₀) ⊔ 𝒢 ≤ mΩ :=
    sup_le (germSigma_le hBm (measurable_centredField hhm u₀)) h𝒢
  have hXm : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z))
      (fun z => (hfwd z).mono h𝒢 le_rfl) (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hhm 1 a k
  have hker := fun χ => condExp_cexp_eq_rangeKerCF (Q := P[|D]) h𝒦 hXm hMm hMcond χ
  have hUH : ballsOpen Fb ≤ upperHalfPlaneOpens := fun z hz => hFH (ballsU_subset_ballsK Fb hz)
  have hD𝒦 : MeasurableSet[germSigma B (centredField h u₀) ⊔ 𝒢] D := (le_sup_right : 𝒢 ≤ _) _ hD𝒢
  have hDV : ∀ᵐ ω ∂(P[|D]), ω ∈ D → IsOpen (H \ K ω) ∧ H \ K ω ⊆ H ∧
      ((ballsOpen Fb : Set ℂ) ⊆ H \ K ω) ∧ IsHarmonicDistOn (M ω) (H \ K ω) := by
    filter_upwards [hMharm, hDac.ae_le hDs, hDac.ae_le hreg] with ω hM h1 h3 hωD
    obtain ⟨hωF, hsζ, hdisj⟩ := h1 hωD
    refine ⟨(relHull_relClosed (r ω) ω).2, sdiff_subset, fun z hz => ⟨hFH (ballsU_subset_ballsK Fb hz), fun hzK => ?_⟩,
      hM⟩
    simp only [hK] at hzK
    rw [relHull_eq (h3 hωF) hsζ] at hzK
    exact Set.disjoint_left.1 hdisj (ballsU_subset_ballsK Fb hz) hzK
  have key := Sec7.Lemma72D.setIntegral_lapTest_of_kernel (P := P[|D]) h𝒦 hXm hker hUH hD𝒦 hDV f Ξ
  rw [setIntegral_cond_of_subset' hDm subset_rfl, setIntegral_cond_of_subset' hDm subset_rfl,
    mul_smul_comm] at key
  have hne : (P D)⁻¹.toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 (measure_ne_top _ _), ENNReal.inv_ne_top.2 hPD⟩
  exact smul_right_injective ℂ hne key

open LocalSets WholeField in
/-- **(L) for a chart field from the history-marked locality of the physical later-line sets** (the locality half of
Aux. lemma 77 at deterministic physical lines). Chart, clock, filtrations and regularity as in
`hasSafeLaw_of_lineKernel`; at every deterministic physical time `t` a hitting-measurable relatively closed random set
`B t` (the physical later-line union, or the complement of the active component) is a history-marked local set of the
centred field for marks `ℋ t ⊇ 𝓖_t`, with `ℍ ∖ B t = inv(ℍ ∖ K̃_{Qc t})` almost surely on `F` before the lifetime.
Then the transported field has K2's input (L) for `𝓗'`. -/
theorem hasSafeMembers_of_lineLocal {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω) (hQ0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t] (lineSafe Qc W ζ (ballsK Fb) t))
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (B t) (centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) :
    HasSafeMembers P 𝓗' F ζ W fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) ψ :=
    fun ψ => ((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp
      (Chart.measurable_chartTransport_random' hc (fun z => 𝓖.le 0 _ (hdom z))
        (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hliftc hhm 1 a k)
  have hreg' : ∀ᵐ ω ∂P, ω ∈ F → IsDrvReg W ζ ω := by
    filter_upwards [hreg] with ω hω hωF using ⟨(hω hωF).2.1, (hω hωF).1⟩
  refine hasSafeMembers_of_lineMembers (VL := VL) (VR := VR) hXψ hQc hQm hQ0 hQa h𝓗' hreach hreg hS
    fun t Fb hFH E hE hEs f Ξ => ?_
  have h0t : 𝓖 0 ≤ ℋ t := (𝓖.mono (zero_le (a := t))).trans (h𝓖ℋ t)
  exact setIntegral_lapTest_of_lineLocal hhm hu₀ hh0 hc (hℋ t) (fun z => h0t _ (hdom z))
    (fun z => (hfwd z).mono h0t le_rfl) (fun z => (hliftm z).mono h0t le_rfl) hliftc hlift a k (Qc t) (B t)
    (hBm t) (hBc t) (hloc t) (hBK t) hreg' Fb hFH (h𝓖ℋ t _ hE) (by
      filter_upwards [hEs] with ω hω hωE using ⟨(hω hωE).1, (hω hωE).2.1, (hω hωE).2.2⟩) f Ξ

end InteractingSLE.Restart.DomainMarkov.Aux79
