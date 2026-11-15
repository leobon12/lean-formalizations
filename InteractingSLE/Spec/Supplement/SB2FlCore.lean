/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxFlow

/-!
# The step of SB2(2)'s retained-law induction: kernel bookkeeping and the masked canonical driver

Worker PROVE-SB2-F3LAW (target 1: the induction step from B's stage `ℓ` to `ℓ + 2`). The landed step core
`Qw.ae_isGFF_stepField` asks the record of the piece's driver to be measurable for the finer marks at every sample. For
the canonical driver `driverOf (c, Z)` of a stage, the record is matched with a marks-measurable driver only almost
surely on the stage's live event; off it the canonical driver is arbitrary. So the step uses the canonical driver
**masked** off an event `L` of the coarse marks (`maskDrv`): on `L` it is the canonical driver, elsewhere the zero
driver. Under the conditional law at a point of `L` the mask is invisible, so the masked driver is still the
conditional flow-line driver (Theorem 1.3, as in `Qx.ae_isFlowLineDriver_driverOf`).

* `ae_isGFF_congr_on`, `ae_isGFF_word_congr_on`, `ae_isGFF_of_kernel_eq`: moving a conditional GFF law along almost
  sure equalities of the field, of the word, and of the kernels;
* `measurable_inf_aeSigma_of_ae_eq`: a measurable function almost surely equal to an `𝒢`-measurable one is
  measurable for the completed `mΩ ⊓ aeSigma 𝒢 P`;
* `maskDrv` and **`ae_isFlowLineDriver_maskDrv`**.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fl

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField Qw

section Kernel

variable {Ω : Type*} {𝓜 𝓜' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **A conditional GFF law moves to an almost surely equal field** on an event of the marks. -/
theorem ae_isGFF_congr_on (h𝓜 : 𝓜 ≤ mΩ) {G : Set Ω} (hG : MeasurableSet[𝓜] G)
    {Y Y' : Ω → DistOn upperHalfPlaneOpens} (hY' : Measurable Y') {β : Ω → BoundaryWord}
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Y (β ω₀).fn (β ω₀).jumps)
    (he : ∀ᵐ ω ∂P, ω ∈ G → Y ω = Y' ω) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Y' (β ω₀).fn (β ω₀).jumps := by
  filter_upwards [hlaw, KernelTower.ae_ae_condExpKernel_of_ae h𝓜 he, Sec7.Aux122Disint.ae_ae_condExpKernel_mem
    (P := P) h𝓜 hG] with ω₀ hl hek hmem hω₀
  refine isGFFWithBoundaryData_congr_ae (hl hω₀) hY' ?_
  filter_upwards [hek, hmem hω₀] with ω h1 h2
  exact h1 h2

/-- **A conditional GFF law moves to an almost surely equal word** on an event. -/
theorem ae_isGFF_word_congr_on {G : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β β' : Ω → BoundaryWord}
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Y (β ω₀).fn (β ω₀).jumps)
    (he : ∀ᵐ ω ∂P, ω ∈ G → β ω = β' ω) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Y (β' ω₀).fn (β' ω₀).jumps := by
  filter_upwards [hlaw, he] with ω₀ hl he hω₀
  rw [← he hω₀]
  exact hl hω₀

/-- **A conditional GFF law moves to null-equivalent marks.** -/
theorem ae_isGFF_of_kernel_eq {G : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens}
    {β : Ω → BoundaryWord} (hk : ∀ᵐ ω ∂P, condExpKernel P 𝓜 ω = condExpKernel P 𝓜' ω)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Y (β ω₀).fn (β ω₀).jumps) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜' ω₀) Y (β ω₀).fn (β ω₀).jumps := by
  filter_upwards [hlaw, hk] with ω₀ hl hk hω₀
  rw [← hk]
  exact hl hω₀

end Kernel

/-- **Completed measurability from an almost sure version.** -/
theorem measurable_inf_aeSigma_of_ae_eq {Ω β : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace β] {P : Measure Ω} {Y Z : Ω → β} (hY : Measurable Y) (hZ : Measurable[𝒢] Z) (hYZ : Y =ᵐ[P] Z) :
    Measurable[mΩ ⊓ aeSigma 𝒢 P] Y := fun _ hB =>
  MeasurableSpace.measurableSet_inf.2 ⟨hY hB, WholeField.measurable_aeSigma_of_ae_eq' (P := P) hZ hYZ hB⟩

/-! ### The masked canonical driver -/

open Classical in
/-- **The canonical driver masked off an event**: the driver `e` on `L`, the zero driver (lifetime `0`) elsewhere. -/
def maskDrv {Ω : Type*} (L : Set Ω) (e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  if ω ∈ L then e ω else Mz.zeroDrv

theorem maskDrv_of_mem {Ω : Type*} {L : Set Ω} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω} (hω : ω ∈ L) :
    maskDrv L e ω = e ω := by
  simp only [maskDrv, hω, ↓reduceIte]

theorem maskDrv_of_notMem {Ω : Type*} {L : Set Ω} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω} (hω : ω ∉ L) :
    maskDrv L e ω = Mz.zeroDrv := by
  simp only [maskDrv, hω, ↓reduceIte]

theorem isRegularDriver_maskDrv {Ω : Type*} {L : Set Ω} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : ∀ ω, IsRegularDriver (e ω)) (ω : Ω) : IsRegularDriver (maskDrv L e ω) := by
  by_cases hω : ω ∈ L
  · rw [maskDrv_of_mem hω]; exact he ω
  · rw [maskDrv_of_notMem hω]; exact Mz.isRegularDriver_zeroDrv

theorem measurable_maskDrv {Ω : Type*} {m : MeasurableSpace Ω} {L : Set Ω} (hL : MeasurableSet[m] L)
    {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (he : Measurable[m] e) : Measurable[m] (maskDrv L e) := by
  classical
  exact Measurable.ite hL he measurable_const

/-- **The masked canonical driver is the conditional flow-line driver** on the masking event (Theorem 1.3): if, given
`𝓜`, the field `Z` is almost surely on `L ∈ 𝓜` a GFF with the data of the `𝓜`-measurable word `c`, then
`maskDrv L (driverOf (c, Z))` is there the angle-`θ` flow-line driver of `Z`. -/
theorem ae_isFlowLineDriver_maskDrv (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝓜 : 𝓜 ≤ mΩ) {c : Ω → BoundaryWord}
    (hc : Measurable[𝓜] c) {Z : Ω → DistOn upperHalfPlaneOpens} (hZ : Measurable Z) {L : Set Ω}
    (hL : MeasurableSet[𝓜] L)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Z (c ω₀).fn (c ω₀).jumps) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ L → IsFlowLineDriver κ (c ω₀).fn (c ω₀).jumps θ (condExpKernel P 𝓜 ω₀) Z
      (fun t ω => (maskDrv L (fun ω => driverOf h12p hκ θ (c ω, Z ω)) ω).1 t)
      (fun ω => (maskDrv L (fun ω => driverOf h12p hκ θ (c ω, Z ω)) ω).2) := by
  have hcm : Measurable c := hc.mono h𝓜 le_rfl
  have hD : Measurable fun ω => driverOf h12p hκ θ (c ω, Z ω) :=
    (measurable_driverOf h12p hκ θ).comp (hcm.prodMk hZ)
  have hM : Measurable (maskDrv L fun ω => driverOf h12p hκ θ (c ω, Z ω)) := measurable_maskDrv (h𝓜 _ hL) hD
  filter_upwards [hlaw, Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝓜 hc,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝓜 hL] with ω₀ hl hceq hmem hω₀
  refine Cond.isFlowLineDriver_of_driverCodeMatch_univ h12p hκ θ h13 (c ω₀) (hl hω₀)
    (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hM)) (measurable_snd.comp hM) (fun ω => ?_) ?_
  · by_cases hω : ω ∈ L
    · simp only [maskDrv_of_mem hω]
      exact Mu.continuousOn_driverOf h12p hκ θ (c ω, Z ω)
    · simp only [maskDrv_of_notMem hω]
      exact continuousOn_const
  · filter_upwards [hceq, hmem hω₀] with ω hω hωL
    simp only [maskDrv_of_mem hωL]
    rw [← hω]
    exact Mu.isDriverCodeMatch_driverOf h12p hκ θ (c ω, Z ω)

end InteractingSLE.Theorem14.SB.Fl
