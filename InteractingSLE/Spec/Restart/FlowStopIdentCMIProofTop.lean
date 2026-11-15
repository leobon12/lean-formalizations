/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIProofKernel
import InteractingSLE.Spec.Restart.FlowStopIdentCMIProofLife
import InteractingSLE.Spec.Restart.FlowStopIdentCMIG3

/-!
# The explicit-shift (L1): reduction to the pathwise data and the converse assembly

Packet PROVE-L1-CMI (continuation). `FlowLineStopIdentCMIStatement` (the input of `RLC.g3SourceStatement_of_CMI`) is
reduced to two named statements, neither of which is new mathematics:

* `StopPathData`: the pathwise facts at a stop `τ` that `ae_condExp_shift_eq_ref` consumes (a continuous driver `W₁`
  agreeing with the `b`-driver past `τ`, the `b`-marks at its geometric images, the hull closure in the chart buffer and
  the trace filling the hulls);
* **`CMIStopDataStatement`** (named input, pathwise): a driver `W₁` (the `b`-driver frozen at the exit time) with these
  facts at every driving stop before the exit time;
* **`CMIConverseStatement`** (named input, the converse assembly (d)–(h)): a field with the reference word's kernel at
  every driving stop before the exit time (and the pathwise facts) is, on an enlargement, a stopped flow line of the
  reference data through the exit time — Theorem 2.4's converse before a stop
  (`StoppedK2.isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun`), the clauses at stops of the reference driving
  filtration (from below at the exit time, `StoppedK2.condExp_cexp_eq_of_le_stop`), locality of the hulls under the
  tilt (`LocalExt.IsLocalSet.withDensity_exp_neg`), the GFF clause (`isGFFWithBoundaryData_shift`) and the trace;
* **`cmiStoppedStatement_of_inputs`**: the reduction, through the **proved** per-stop identification
  `ae_condExp_shift_eq_ref` (steps (b)–(c));
* **`flowLineStopIdentCMIStatement_of_inputs`**, **`RLC.g3SourceStatement_of_CMIInputs`**: Lemma G3 (source form)
  from the two named inputs, the WFS kernel target and Theorems 1.2–1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open StoppedExtend

/-- **The pathwise data at a stop** consumed by `ae_condExp_shift_eq_ref`: `W₁` is continuous with `W₁ 0 = 0`, agrees
with `W₀` on `[0, t₂]` for some `t₂ > τ`, the `b`-marks sit at its geometric images at `τ`, the hull of `W₁` at `τ` has
closure in the chart buffer `N − y`, and for `τ > 0` a trace fills the hulls up to `τ`. -/
def StopPathData {S : Type*} (b : ℝ → ℝ) (J : Finset ℝ) (y : ℝ) (N : Set ℂ) (W₀ W₁ : ℝ≥0 → S → ℝ)
    (VL₀ : Fin (flowLineNL b J y) → ℝ≥0 → S → ℝ) (VR₀ : Fin (flowLineNR b J y) → ℝ≥0 → S → ℝ)
    (τ : S → WithTop ℝ≥0) (ω : S) : Prop :=
  Continuous (W₁ · ω) ∧ W₁ 0 ω = 0 ∧
    (∃ t₂ : ℝ, (((τ ω).untopD 0 : ℝ≥0) : ℝ) < t₂ ∧
      ∀ r ∈ Icc (0 : ℝ) t₂, Ito.rpath (W₁ · ω) r = Ito.rpath (W₀ · ω) r) ∧
    (∀ i, VL₀ i ((τ ω).untopD 0) ω - W₀ ((τ ω).untopD 0) ω =
      geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL b J y i)) ∧
    (∀ j, VR₀ j ((τ ω).untopD 0) ω - W₀ ((τ ω).untopD 0) ω =
      geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR b J y j)) ∧
    closure (fwdHull (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)) ⊆ (fun z => z + y) ⁻¹' N ∧
    (0 < (τ ω).untopD 0 → ∃ η : ℝ → ℂ, ContinuousOn η (Icc 0 (((τ ω).untopD 0 : ℝ≥0) : ℝ)) ∧
      ∀ r ∈ Ioc (0 : ℝ) (((τ ω).untopD 0 : ℝ≥0) : ℝ), fwdHull (Ito.rpath (W₁ · ω)) r = fillH (η '' Icc 0 r))

/-- **Named input (pathwise): the frozen driver.** For the `b`-coupling of a flow line `Γ` from `y` whose buffer `V`
has its real points in `[a, c]` and whose shift hull set lies in the buffer `N`, there is a driver `W₁` (the `b`-driver
frozen at the exit time `e = RLC.exitTime V Γ U`) with `StopPathData` at every stopping time of the driving filtration
before `e`. -/
def CMIStopDataStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ (b : ℝ → ℝ) (J : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    ∀ N : Set ℂ, IsOpen N → ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N →
    ∀ a c : ℝ, (∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) → FlowStopIdentCM.shiftHullSet V a c ⊆ N →
    ∀ y θ : ℝ, ∀ {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
      (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (h' : S → DistOn upperHalfPlaneOpens) (𝓕₀ : Filtration ℝ≥0 ‹_›)
      (W₀ : ℝ≥0 → S → ℝ) (VL₀ : Fin (flowLineNL b J y) → ℝ≥0 → S → ℝ)
      (VR₀ : Fin (flowLineNR b J y) → ℝ≥0 → S → ℝ) (B₀ : ℝ≥0 → S → ℝ),
      IsOptionalHullCoupling κ (flowLineXL b J y) (flowLineXR b J y) (flowLineRhoL κ b J y θ)
        (flowLineRhoR κ b J y θ) Q₀ 𝓕₀ W₀ VL₀ VR₀ B₀ U h' →
      (∀ᵐ x ∂Q₀, IsGeneratingTrace (fun t => W₀ t x) (U x) (fun t => Γ x t - y)) →
      ∀ hX : IsMeasurableKilledDriving W₀ VL₀ VR₀ U, ∃ W₁ : ℝ≥0 → S → ℝ,
        ∀ τ : S → WithTop ℝ≥0, IsStoppingTime (drivingFiltration Q₀ hX) τ →
          (∀ᵐ ω ∂Q₀, (τ ω : ℝ≥0∞) < RLC.exitTime V (Γ ω) (U ω)) →
          ∀ᵐ ω ∂Q₀, StopPathData b J y N W₀ W₁ VL₀ VR₀ τ ω

/-- **Named input (the converse assembly (d)–(h)).** In the explicit-shift setting, with the `b`-coupling of `Γ` in the
chart of `y` and a driver `W₁` with `StopPathData` at every driving stop before the exit time `e`: if, under
`Q* = k e^{−Λ} · Q₀`, the shifted chart field `h' + T_y` has the reference word's kernel (at the geometric images of
`W₁`) at every driving stop before `e`, then `Γ` stopped at `e` is, on an enlargement `Q* ⊗ ν`, a stopped flow line of
`H₀ + (q − F.f)` for the data `bR`. -/
def CMIConverseStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N →
    ∀ a c : ℝ, Icc a c ⊆ O → (∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) →
      FlowStopIdentCM.shiftHullSet V a c ⊆ N →
    ∀ (F : CMCut) (q : ℂ → ℝ),
      IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q →
      (∀ z ∈ N, z ∈ H → F.f z = q z) → (∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) →
    ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
      (H₀ : S → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
    ∀ s : ℕ → TestOn upperHalfPlaneOpens, (∀ n z, |s n z| ≤ |F.src z|) →
      (∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) →
    ∀ Λ : S → ℝ, Measurable Λ → (∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))) →
    ∀ k : ℝ, 0 < k → IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (h' : S → DistOn upperHalfPlaneOpens) (𝓕₀ : Filtration ℝ≥0 ‹_›)
      (W₀ : ℝ≥0 → S → ℝ) (VL₀ : Fin (flowLineNL b J y) → ℝ≥0 → S → ℝ)
      (VR₀ : Fin (flowLineNR b J y) → ℝ≥0 → S → ℝ) (B₀ : ℝ≥0 → S → ℝ),
      (∀ x, IsTranslateAddConst y (θ * QuantumZipper.chiC κ) (H₀ x) (h' x)) →
      IsOptionalHullCoupling κ (flowLineXL b J y) (flowLineXR b J y) (flowLineRhoL κ b J y θ)
        (flowLineRhoR κ b J y θ) Q₀ 𝓕₀ W₀ VL₀ VR₀ B₀ U h' →
      (∀ᵐ x ∂Q₀, IsGeneratingTrace (fun t => W₀ t x) (U x) (fun t => Γ x t - y)) →
      ∀ (hX : IsMeasurableKilledDriving W₀ VL₀ VR₀ U) (W₁ : ℝ≥0 → S → ℝ),
      (∀ τ : S → WithTop ℝ≥0, IsStoppingTime (drivingFiltration Q₀ hX) τ →
        (∀ᵐ ω ∂Q₀, (τ ω : ℝ≥0∞) < RLC.exitTime V (Γ ω) (U ω)) →
        ∀ᵐ ω ∂Q₀, StopPathData b J y N W₀ W₁ VL₀ VR₀ τ ω) →
      (∀ (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration Q₀ hX) τ),
        (∀ᵐ ω ∂Q₀, (τ ω : ℝ≥0∞) < RLC.exitTime V (Γ ω) (U ω)) →
        ∀ uR : S → ℂ → ℝ, (∀ ω, IsBoundedHarmonicExtension
          (forceBoundaryData κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
            (fun i => geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL bR Ĵ y i))
            (fun j => geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR bR Ĵ y j)))
          (forceJumpSet
            (fun i => geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL bR Ĵ y i))
            (fun j => geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR bR Ĵ y j)))
          (uR ω)) →
        ∀ φ : TestOn upperHalfPlaneOpens,
          ∀ᵐ ω ∂(Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))),
            Disjoint (tsupport φ) (fwdHull (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)) →
            (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)))[fun ω' =>
                Complex.exp (Complex.I * ((h' ω' + chartShift F q y) φ : ℂ)) | hτ.measurableSpace] ω =
              LocalExt.cfVal (∫ z, couplingMean κ (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
                  (uR ω) z * φ z)
                (loewnerGreenEnergy (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) φ)) →
      ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
        IsStoppedFlowLine κ bR Ĵ y θ ((Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))).prod ν)
          (fun p => H₀ p.1 + smoothDist upperHalfPlaneOpens fun z => q z - F.f z) (fun p => Γ p.1)
          fun p => RLC.exitTime V (Γ p.1) (U p.1)

/-- **The explicit-shift (L1) without the lifetime clause, from the two named inputs**, through the proved per-stop
Cameron–Martin identification `ae_condExp_shift_eq_ref` (steps (b)–(c)). -/
theorem cmiStoppedStatement_of_inputs (h1 : CMIStopDataStatement.{u}) (h2 : CMIConverseStatement.{u}) :
    CMIStoppedStatement.{u} := by
  classical
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN a c haO hVa hsN F q hq hFq hFΔ y θ S _ Q₀ _ H₀ hH
    s hsle hslim Λ hΛm hΛ k hk hprob Γ U hΓ
  obtain ⟨h', 𝓕₀, W₀, VL₀, VR₀, B₀, htr, hC, hgen⟩ := hΓ
  obtain ⟨hX, -⟩ := hC.2.2.2
  obtain ⟨W₁, hW₁⟩ := h1 κ hκ b J hb N hN V hV hVb hVN a c hVa hsN y θ Q₀ Γ U h' 𝓕₀ W₀ VL₀ VR₀ B₀ hC hgen hX
  refine h2 κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN a c haO hVa hsN F q hq hFq hFΔ y θ Q₀ H₀ hH s
    hsle hslim Λ hΛm hΛ k hk hprob Γ U h' 𝓕₀ W₀ VL₀ VR₀ B₀ htr hC hgen hX W₁ hW₁ ?_
  intro τ hτ hτe uR huR φ
  by_cases hyN : (y : ℂ) ∈ N
  · have hyO : y ∈ O := by simpa using hNO _ hyN (by simp)
    have hτU : ∀ᵐ ω ∂Q₀, (τ ω : ℝ≥0∞) < U ω := hτe.mono fun ω h => h.trans_le (min_le_left _ _)
    exact ae_condExp_shift_eq_ref hκ hb hbR hO hbO hyO θ hq hN hNO hFq hFΔ hyN hsle hslim hΛm hΛ hk hprob htr hC hX
      hτ hτU (hW₁ τ hτ hτe) huR φ
  · -- the seed is outside the buffer: the exit time is `0`, so there is no stop before it
    have hfalse : ∀ᵐ ω ∂Q₀, False := by
      filter_upwards [hτe, hgen] with ω h1' h2'
      have h0 : Γ ω 0 = y := sub_eq_zero.1 h2'.1
      have hnV : Γ ω 0 ∉ V := by
        rw [h0]; exact fun hy => hyN (hVN (subset_closure hy))
      rw [RLC.exitTime_eq_zero (U ω) hnV] at h1'
      exact absurd h1' (not_lt.2 bot_le)
    obtain ⟨_, hω⟩ := hfalse.exists
    exact hω.elim

/-- **The explicit-shift (L1) with its lifetime clause from the two named inputs.** -/
theorem flowLineStopIdentCMIStatement_of_inputs (h1 : CMIStopDataStatement.{u}) (h2 : CMIConverseStatement.{u}) :
    FlowLineStopIdentCMIStatement.{u} :=
  flowLineStopIdentCMIStatement_of_stopped (cmiStoppedStatement_of_inputs h1 h2)

end FlowStopIdentCMI

end Restart

/-- **Lemma G3 in the source's form from the two named inputs of the explicit-shift (L1)**, the WFS kernel target for
`0 < κ < 4` and Theorems 1.2 (param) / 1.3. -/
theorem RLC.g3SourceStatement_of_CMIInputs (h1 : Restart.FlowStopIdentCMI.CMIStopDataStatement.{0})
    (h2 : Restart.FlowStopIdentCMI.CMIConverseStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    RLC.G3SourceStatement.{0} :=
  RLC.g3SourceStatement_of_CMI (Restart.FlowStopIdentCMI.flowLineStopIdentCMIStatement_of_inputs h1 h2) hT h12p h13

end InteractingSLE
