/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12DawnFibreOn
import InteractingSLE.Spec.Sec5.Aux61UnionKPC1

/-!
# The fibre-kernel leaves bundled with their cover (the provable form of Dawn's fibre interface)

Packet PROVE-AUX61-FIBK.

**Finding (the Dawn interface cannot be discharged by a construction).** `Wire.Dawn.GluedChartOn hGeo K`,
`GluedPC1On hGeo K`, `GluedLocalOn hGeo` and `GluedKernelDataOn hGeo` speak about the records
`Classical.choose (hGeo …)`. By proof irrelevance this is ONE unspecified witness of `∃ D, Night.FibreGeometry μ E D`;
nothing beyond `FibreGeometry` is known about it. `FibreGeometry` constrains only the paths, lifetimes, history events
and data of the codes `Y i`, never their FIELD component: replacing the field part of `Y i` by a constant
distribution keeps `FibreGeometry` (`PathGood`, the visit sets and the cutoffs do not read the field), while the chart
law `FibreChart` then fails (a constant has a unit-modulus characteristic functional, `cfVal` has modulus
`exp(−E/2) < 1`). So no proof of `GluedChartOn hGeo K` can use the actual construction of the records (FIBDATA's
`exitCode`). The fix is to bundle the records with their kernel facts in ONE existential:

* **`HasFibreKernelCover μ E`**: `∃ D K, FibreGeometry ∧ FibreDataMeas ∧ FibreSigma ∧ FibreChart ∧ FibrePC1 ∧
  FibreLocal`; **`hasDyActFibreCover_of_kernelCover`**: it gives FIB2's `HasDyActFibreCover … RefWin`;
* **`HasFibreChartCover μ E`**: the same with the canonical candidate means (`Aux61UnionK.canonKernelData`) and WITHOUT
  the (PC1) leaf; **`hasFibreKernelCover_iff_chartCover`**: the two are equivalent (PC1 is deterministic for the
  canonical means, `fibrePC1_canon`; a (PC1) chart law is the canonical chart law, `fibreChart_canon_of_pc1`);
* **`GluedKernelCoverOn`**, **`GluedChartCoverOn`**: the setting-quantified forms (exactly the binders of
  `Aux61Act.DyActFibreCoverOn` for the small-gap window, as in `Wire.Night.GluedFibreGeometryOn`);
  **`dyCover_of_kernelCoverOn`**, **`dyCover_of_chartCoverOn`**: they give `DyActFibreCoverOn (¬ IsLargeGap) RefWin`;
* **`kernelCoverOn_of_dawn`**, **`chartCoverOn_of_dawn`**: Dawn's seven fibre leaves imply the bundled forms, so the
  rewiring `hFibGeometry, fibKernel, hFibDataMeas, hFibSigma, hFibChart, hFibPC1, hFibLocal ↦ hFibCover` never
  strengthens a hypothesis of Theorems 1.2/1.3.

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Aux61UnionK

open Sec4 Sec5.Aux61Fib Sec5.Aux61FibK Sec5.Aux61R2 Sec5.Aux61Cov
open Sec5.Prop51G Sec5.Aux61Kernel Sec5.Cond44Ref Sec5.Aux61Act
open WangWu WholeField LocalSets Restart Exist.StagedLaw LocalExt Coupling LawUnique

universe u

/-! ### One glued setting -/

section Setting

variable {X : Type u} [MeasurableSpace X]

/-- **The fibre-kernel cover, bundled**: countable records covering the event, with fixed reference words,
conditioning σ-algebras and candidate means, such that the chart law, (PC1) and glued projection independence hold
for THESE records. -/
def HasFibreKernelCover (μ : Measure X) (E : X → Prop) : Prop :=
  ∃ (D : Wire.Night.FibreRecords X) (K : Wire.Dawn.FibreKernelData D), Wire.Night.FibreGeometry μ E D ∧
    Wire.Dawn.FibreDataMeas D K ∧ Wire.Dawn.FibreSigma D K ∧ Wire.Dawn.FibreChart μ D K ∧
      Wire.Dawn.FibrePC1 μ D K ∧ Wire.Dawn.FibreLocal μ D

/-- **The fibre-chart cover**: the bundled cover with the canonical candidate means and no (PC1) leaf. -/
def HasFibreChartCover (μ : Measure X) (E : X → Prop) : Prop :=
  ∃ (D : Wire.Night.FibreRecords X) (kappa : D.ι → ℝ) (boundary : D.ι → ℝ → ℝ) (jumps : D.ι → Finset ℝ)
    (sigma : D.ι → ℕ → ℕ → MeasurableSpace X), Wire.Night.FibreGeometry μ E D ∧
    Wire.Dawn.FibreDataMeas D (canonKernelData D kappa boundary jumps sigma) ∧
      Wire.Dawn.FibreSigma D (canonKernelData D kappa boundary jumps sigma) ∧
        Wire.Dawn.FibreChart μ D (canonKernelData D kappa boundary jumps sigma) ∧ Wire.Dawn.FibreLocal μ D

/-- **The bundled cover gives FIB2's dyadic fibre cover** (GlueK's reductions, as wired in `Wire.Dawn`). -/
theorem hasDyActFibreCover_of_kernelCover {μ : Measure X} [IsFiniteMeasure μ] {E : X → Prop}
    (h : HasFibreKernelCover μ E) : HasDyActFibreCover μ E RefWin := by
  obtain ⟨D, K, hg, hm, hs, hc, hp, hl⟩ := h
  have hmeas := Wire.Dawn.fibreMeas_of_data D K hm
  have hint := Wire.Dawn.fibreIntegral_of_chart D K hg hm hs hc hp
  exact Wire.Night.hasDyCover_of_glued D hg hmeas hint (Wire.Dawn.fibreMembers_of_local D hg hmeas hint hl)

/-- **The two bundled forms are equivalent**: (PC1) is deterministic for the canonical means, and a chart law with
(PC1) means is the canonical chart law. -/
theorem hasFibreKernelCover_iff_chartCover {μ : Measure X} {E : X → Prop} :
    HasFibreKernelCover μ E ↔ HasFibreChartCover μ E := by
  constructor
  · rintro ⟨D, K, hg, hm, hs, hc, hp, hl⟩
    exact ⟨D, K.kappa, K.boundary, K.jumps, K.sigma, hg, hm, hs, fibreChart_canon_of_pc1 D hg K hc hp, hl⟩
  · rintro ⟨D, kappa, boundary, jumps, sigma, hg, hm, hs, hc, hl⟩
    exact ⟨D, canonKernelData D kappa boundary jumps sigma, hg, hm, hs, hc,
      fibrePC1_canon D hg kappa boundary jumps sigma, hl⟩

/-- **The fibre-chart cover gives FIB2's dyadic fibre cover.** -/
theorem hasDyActFibreCover_of_chartCover {μ : Measure X} [IsFiniteMeasure μ] {E : X → Prop}
    (h : HasFibreChartCover μ E) : HasDyActFibreCover μ E RefWin :=
  hasDyActFibreCover_of_kernelCover (hasFibreKernelCover_iff_chartCover.2 h)

end Setting

/-! ### The small-gap window settings -/

/-- **The bundled fibre-kernel cover in every small-gap window setting** (the binders of `DyActFibreCoverOn` and of
`Wire.Night.GluedFibreGeometryOn`). -/
def GluedKernelCoverOn : Prop :=
  ∀ (t : ℚ) (c : WinCode), 0 < t →
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ → ¬ IsLargeGap κ θ₁ θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ s : ℚ, 0 < s →
            HasFibreKernelCover.{u}
              (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun u : ℝ => η p.1 u.toNNReal) t c)

/-- **The fibre-chart cover in every small-gap window setting** (canonical candidate means, no (PC1) leaf). -/
def GluedChartCoverOn : Prop :=
  ∀ (t : ℚ) (c : WinCode), 0 < t →
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ → ¬ IsLargeGap κ θ₁ θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ s : ℚ, 0 < s →
            HasFibreChartCover.{u}
              (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun u : ℝ => η p.1 u.toNNReal) t c)

/-- The two setting-quantified bundled forms are equivalent. -/
theorem gluedKernelCoverOn_iff_chartCoverOn : GluedKernelCoverOn.{u} ↔ GluedChartCoverOn.{u} := by
  constructor
  · intro H t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
    exact hasFibreKernelCover_iff_chartCover.1
      (H t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
  · intro H t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
    exact hasFibreKernelCover_iff_chartCover.2
      (H t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- **The bundled cover gives the corrected dyadic fibre cover** consumed by `Aux61Act.fwdNoEastCrosscutTgtQOn_of_
dyCover_refWin`. -/
theorem dyCover_of_kernelCoverOn (H : GluedKernelCoverOn.{u}) :
    DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) RefWin := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact hasDyActFibreCover_of_kernelCover
    (H t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- **The fibre-chart cover gives the corrected dyadic fibre cover.** -/
theorem dyCover_of_chartCoverOn (H : GluedChartCoverOn.{u}) :
    DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) RefWin :=
  dyCover_of_kernelCoverOn (gluedKernelCoverOn_iff_chartCoverOn.2 H)

/-- **Dawn's seven fibre leaves imply the bundled cover** (so replacing them by `GluedKernelCoverOn` strengthens no
hypothesis). -/
theorem kernelCoverOn_of_dawn (hGeo : Wire.Night.GluedFibreGeometryOn.{u}) (K : Wire.Dawn.GluedKernelDataOn hGeo)
    (hm : Wire.Dawn.GluedDataMeasOn hGeo K) (hs : Wire.Dawn.GluedSigmaOn hGeo K) (hc : Wire.Dawn.GluedChartOn hGeo K)
    (hp : Wire.Dawn.GluedPC1On hGeo K) (hl : Wire.Dawn.GluedLocalOn hGeo) : GluedKernelCoverOn.{u} := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs'
  exact ⟨_, K t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs',
    Classical.choose_spec (hGeo t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs'),
    hm t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs',
    hs t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs',
    hc t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs',
    hp t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs',
    hl t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs'⟩

/-- **Dawn's seven fibre leaves imply the fibre-chart cover.** -/
theorem chartCoverOn_of_dawn (hGeo : Wire.Night.GluedFibreGeometryOn.{u}) (K : Wire.Dawn.GluedKernelDataOn hGeo)
    (hm : Wire.Dawn.GluedDataMeasOn hGeo K) (hs : Wire.Dawn.GluedSigmaOn hGeo K) (hc : Wire.Dawn.GluedChartOn hGeo K)
    (hp : Wire.Dawn.GluedPC1On hGeo K) (hl : Wire.Dawn.GluedLocalOn hGeo) : GluedChartCoverOn.{u} :=
  gluedKernelCoverOn_iff_chartCoverOn.1 (kernelCoverOn_of_dawn hGeo K hm hs hc hp hl)

end InteractingSLE.Sec5.Aux61UnionK
