/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Kern

/-!
# The conditional law at the stop given the announced history

Packet PROVE-STAGEDLAW3. For a frozen optional hull coupling driven by everywhere regular drivers `E` (`W = E.1`,
`ζ = E.2`) with an admissible seed, take an announcing sequence `σₙ` of the lifetime and the stops
`ρₙ = min t σₙ` (`stopSeq`). They increase to the stop `T = min t ζ` (reached when `t < ζ`, announced when `ζ ≤ t`).
Given `𝓗 = ⋁ₙ 𝓓_{ρₙ}` (`WholeField.exists_announced_kernel_history`), every test function supported off the hull at
the stop has the Gaussian conditional law whose mean is the tested coupling mean **at the stop** with the record
driver and the stop word, and whose variance is the Green energy of the remaining domain at the stop
(`IsGoodStopPath.tendsto_integral_couplingMean`, `IsGoodStopPath.tendsto_zeroGFFTestCov`):

* `stopSeq`, `isStoppingTime_stopSeq`, `monotone_stopSeq`;
* `ae_isGoodStopPath`: almost every path is good at a finite stop;
* **`ae_condExp_cexp_stop`**: the conditional characteristic functional at a fixed test function.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged Restart LQGMetric

/-! ### The stops -/

/-- The stops `ρₙ = min t σₙ`. -/
def stopSeq {Ω : Type*} (t : ℝ≥0∞) (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 := (min t (σ n ω : ℝ≥0∞)).toNNReal

theorem stopSeq_le {Ω : Type*} (t : ℝ≥0∞) (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) : stopSeq t σ n ω ≤ σ n ω := by
  unfold stopSeq
  have h : min t (σ n ω : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h]
  exact min_le_right _ _

theorem monotone_stopSeq {Ω : Type*} (t : ℝ≥0∞) {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ ω, Monotone fun n => σ n ω)
    (ω : Ω) : Monotone fun n => stopSeq t σ n ω := fun m n hmn => by
  unfold stopSeq
  refine ENNReal.toNNReal_mono (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
    (min_le_min le_rfl (ENNReal.coe_le_coe.2 (hσ ω hmn)))

theorem isStoppingTime_stopSeq {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} (t : ℝ≥0∞)
    {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) (n : ℕ) :
    IsStoppingTime 𝓖 fun ω => (stopSeq t σ n ω : WithTop ℝ≥0) := by
  induction t using ENNReal.recTopCoe with
  | top =>
    have e : (fun ω => (stopSeq ⊤ σ n ω : WithTop ℝ≥0)) = fun ω => (σ n ω : WithTop ℝ≥0) := by
      funext ω
      simp only [stopSeq, min_eq_right le_top, ENNReal.toNNReal_coe]
    rw [e]
    exact hσ n
  | coe T =>
    have e : (fun ω => (stopSeq (T : ℝ≥0∞) σ n ω : WithTop ℝ≥0)) =
        fun ω => min (σ n ω : WithTop ℝ≥0) (T : WithTop ℝ≥0) := by
      funext ω
      rw [stopSeq, ← ENNReal.coe_min, ENNReal.toNNReal_coe, min_comm]
      rfl
    rw [e]
    exact (hσ n).min_const T

/-! ### Good paths -/

section Good

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
  {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}

/-- **Almost every path is good at a finite stop.** -/
theorem ae_isGoodStopPath (hκ : 0 < κ) (hreg : ∀ ω, IsRegularDriver (E ω))
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓕 (fun s ω => (E ω).1 s) VL VR B fun ω => (E ω).2)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (t : ℝ≥0∞) :
    ∀ᵐ ω ∂Q, min t (E ω).2 ≠ ⊤ →
      IsGoodStopPath κ xL xR ρL ρR t (E ω) (fun i s => VL i s ω) (fun j s => VR j s ω) (fun s => B s ω) := by
  filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ] with ω hp hthr hfin
  have hgood : LocalExt.IsDrvGood (recHist (recOf t (E ω))) := by
    refine isDrvGood_recOf_of_leftLim (hreg ω) hfin fun T hT hζ => ?_
    obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthr T hT hζ
    exact ⟨w₀, (continuous_fst.tendsto _).comp hlim⟩
  have hpos : 0 < (E ω).2 := by
    refine pos_iff_ne_zero.2 fun h0 => hseed ?_
    exact hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0
  refine ⟨hp, fun T hT hζ => ?_, hreg ω, hgood, hfin, hpos⟩
  obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthr T hT hζ
  exact ⟨w₀, vL₀, vR₀, hlim⟩

end Good

/-! ### The kernel at the stop -/

/-- The mean at the stop read from the record: the coupling mean of the record driver at the record time, with the
force word at the positions read from the record. -/
def stopMean (κ : ℝ) (nL nR : ℕ) (xLp xRp ρLp ρRp : ℕ → ℝ) (θc : ℝ) (r : RecData) : ℂ → ℝ :=
  couplingMean κ (rdrv r) (rtime r)
    (fun y => (forceWord κ nL nR (fun i => markPosL (rdrv r) (rtime r) (xLp i))
      (fun j => markPos (rdrv r) (rtime r) (xRp j)) ρLp ρRp θc).mean y + θc)

/-- The hull at the stop read from the record. -/
def stopHull (r : RecData) : Set ℂ := fwdHull (rdrv r) (rtime r)

section Kernel

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
  {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {h' : Ω → DistOn upperHalfPlaneOpens}

/-- **The conditional law at the stop, at a fixed test function.** Given the announced history `⋁ₙ 𝓓_{ρₙ}`, on
`{min t ζ < ∞}` every test function supported off the hull at the stop has the Gaussian characteristic functional with
the tested mean at the stop and the Green energy of the remaining domain. -/
theorem ae_condExp_cexp_stop (hκ : 0 < κ) (hreg : ∀ ω, IsRegularDriver (E ω))
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 (fun s ω => (E ω).1 s) VL VR B (fun ω => (E ω).2) h')
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hX : IsMeasurableKilledDriving (fun s ω => (E ω).1 s) VL VR fun ω => (E ω).2)
    {σ : ℕ → Ω → ℝ≥0} (hσ : Coupling.IsAnnouncingSeq (drivingFiltration Q hX) Q (fun ω => (E ω).2) σ) (t : ℝ≥0∞)
    {ρLp ρRp xLp xRp : ℕ → ℝ} (hρL : ∀ i : Fin nL, ρLp i = ρL i) (hρR : ∀ j : Fin nR, ρRp j = ρR j)
    (hxL : ∀ i : Fin nL, xLp i = xL i) (hxR : ∀ j : Fin nR, xRp j = xR j) (θc : ℝ)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q, min t (E ω).2 ≠ ⊤ → tsupport ψ ⊆ H \ stopHull (recOf t (E ω)) →
      Q[fun ω' => Complex.exp (Complex.I * (h' ω' ψ : ℂ)) |
          ⨆ n, (isStoppingTime_stopSeq t hσ.1 n).measurableSpace] ω =
        Complex.exp (Complex.I * ((∫ z, stopMean κ nL nR xLp xRp ρLp ρRp θc (recOf t (E ω)) z * ψ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (H \ stopHull (recOf t (E ω))) ψ ψ : ℝ) : ℂ)) := by
  obtain ⟨u₀, hu₀⟩ := WholeField.exists_bhe κ ρL ρR xL xR
  have hρ := isStoppingTime_stopSeq t hσ.1
  have hρm : ∀ ω, Monotone fun n => stopSeq t σ n ω := monotone_stopSeq t hσ.2.1
  have hρζ : ∀ n, ∀ᵐ ω ∂Q, (stopSeq t σ n ω : ℝ≥0∞) < (E ω).2 := fun n =>
    (hσ.2.2.1 n).mono fun ω hω => lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le t σ n ω)) hω
  obtain ⟨A, 𝒢, -, hAK, -, hker⟩ := WholeField.exists_announced_kernel_history hC hκ hu₀ hX hρ hρm hρζ
  filter_upwards [hker ψ, ae_all_iff.2 hAK, ae_isGoodStopPath hκ hreg hC.1 hseed t, hσ.2.2.2,
    ae_all_iff.2 hσ.2.2.1] with ω hk hA hgood hann hlt hfin hsupp
  have hg := hgood hfin
  obtain ⟨hle, hlim⟩ := tendsto_stopSeq (σ := fun n => σ n ω) (hσ.2.1 ω) hlt hann hfin
  have hsζ : ∀ n, (stopSeq t σ n ω : ℝ≥0∞) < (E ω).2 := fun n =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le t σ n ω)) (hlt n)
  have hdisjK : Disjoint (tsupport ψ) (stopHull (recOf t (E ω))) :=
    Set.disjoint_left.2 fun z hz hK => (hsupp hz).2 hK
  have hdisj : ∀ n, Disjoint (tsupport ψ) (A n ω) := by
    intro n
    rw [hA n, hg.fwdHull_eq (s := stopSeq t σ n ω) (hle n) (hsζ n)]
    refine hdisjK.mono_right (fwdHull_subset_of_le ?_)
    rw [rtime_recOf_coe]
    exact_mod_cast hle n
  obtain ⟨h1, h2, -, h4⟩ := hk hdisj
  have hmean := hg.tendsto_integral_couplingMean (s := fun n => stopSeq t σ n ω) hρL hρR hxL hxR θc hsζ hle hlim
    ψ hsupp
  have hm : (Q[fun ω' => WholeField.centredField h' u₀ ω' ψ | ⨆ n, 𝒢 n]) ω + ∫ z, u₀ z * ψ z =
      ∫ z, stopMean κ nL nR xLp xRp ρLp ρRp θc (recOf t (E ω)) z * ψ z := by
    refine tendsto_nhds_unique ((h1.add_const (∫ z, u₀ z * ψ z)).congr fun n => ?_) hmean
    simp only [WholeField.testedFrozenMean, sub_add_cancel]
  have hvar := hg.tendsto_zeroGFFTestCov (s := fun n => stopSeq t σ n ω) hsζ hle hlim ψ hdisjK
  have hv : (⨅ n, zeroGFFTestCov (H \ A n ω) ψ ψ) = zeroGFFTestCov (H \ stopHull (recOf t (E ω))) ψ ψ := by
    refine tendsto_nhds_unique h2 (hvar.congr fun n => ?_)
    rw [hA n]
  rw [h4, hm, hv]

end Kernel

end StagedLaw

end Exist

end InteractingSLE
