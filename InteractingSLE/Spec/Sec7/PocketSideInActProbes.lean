/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInActPoisson
import InteractingSLE.Spec.Sec7.PhaseSelAdapt
import InteractingSLE.Spec.Sec7.PocketPhaseMeans

/-!
# Constructing the R73 probes from the full Poisson word

PROVE-POCKET-SIDEIN. On a protected capacity horizon choose a surviving far
point, construct the canonical mean and interval harmonic measure there, and
read the common phase from their quotient. The actual mean's continuity is
the only mean-continuity input; canonical-mean continuity, positivity and the
exact difference identity are derived from the coordinates and full word.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open Aux117 MartChar PhaseSel

/-- The actual full phase word and continuous actual coupling mean give a
continuous common phase on each protected bounded capacity horizon. No
abstract positive probe, canonical-mean continuity or quotient identity is
an additional hypothesis. The driver may be a continuous stopped extension. -/
theorem continuousOn_phase_of_poisson_word {nL nR : ℕ} {κ : ℝ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ≥0}
    {VL : Fin (nL + 1) → ℝ → ℝ} {VR : Fin (nR + 1) → ℝ → ℝ}
    (hVL : ∀ i, ContinuousOn (VL i) (Icc 0 (T : ℝ)))
    (hVR : ∀ i, ContinuousOn (VR i) (Icc 0 (T : ℝ)))
    (hord : ∀ t ∈ Icc 0 (T : ℝ), (∀ i, VL i t ≤ W t) ∧ ∀ j, W t ≤ VR j t)
    (hsep : ∀ t ∈ Ioo 0 (T : ℝ), VL 0 t < VR 0 t)
    {U : ℝ → ℂ → ℝ} {d : ℝ → ℝ}
    (hPoisson : ∀ t ∈ Ioo 0 (T : ℝ), IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => VL i t - W t) (fun j => VR j t - W t) (d t))
      (forceJumpSet (fun i => VL i t - W t) (fun j => VR j t - W t)) (U t))
    (hMeanContinuous : ∀ z ∈ H \ QuantumZipper.fwdHull W T,
      ContinuousOn (fun t => couplingMean κ W t (U t) z) (Ioo 0 (T : ℝ))) :
    ContinuousOn d (Ioo 0 (T : ℝ)) := by
  obtain ⟨m, hm⟩ := PhaseSelAdapt.exists_zpt_alive hW T
  let z := PhaseSelAdapt.zpt m
  have hz : z ∈ H \ QuantumZipper.fwdHull W T := hm
  let M : ℝ → ℝ := fun t => couplingMean κ W t (U t) z
  let M₀ : ℝ → ℝ := fun t => couplingMean κ W t
    (meanExt κ ρL ρR (W t) (fun i => VL i t) (fun j => VR j t)) z
  let w : ℝ → ℝ := fun t => phaseWindow (VL 0 t - W t) (VR 0 t - W t)
    (QuantumZipper.fwdMap W t z)
  have hM : ContinuousOn M (Ioo 0 (T : ℝ)) := hMeanContinuous z hz
  have hM₀ : ContinuousOn M₀ (Icc 0 (T : ℝ)) :=
    PocketPhaseMeans.continuousOn_couplingMean_of_ext T.coe_nonneg hW.continuousOn
      hVL hVR hord (fun t _ => isBoundedHarmonicExtension_meanExt κ ρL ρR (W t)
        (fun i => VL i t) (fun j => VR j t)) hz
  have hw : ContinuousOn w (Icc 0 (T : ℝ)) := continuousOn_phaseWindow hW T.coe_nonneg hz
    ((hVL 0).sub hW.continuousOn) ((hVR 0).sub hW.continuousOn)
  have hpos : ∀ t ∈ Ioo 0 (T : ℝ), 0 < w t := by
    intro t ht
    exact (phaseWindow_mem_Ioo (by linarith only [hsep t ht])
      (Ito.im_fwdMap_pos hW T.coe_nonneg hz (Ioo_subset_Icc_self ht))).1
  have heq : ∀ t ∈ Ioo 0 (T : ℝ), M t - M₀ t = d t * w t := by
    intro t ht
    exact couplingMean_sub_couplingMean_eq (hsep t ht) (hPoisson t ht)
      (Ito.im_fwdMap_pos hW T.coe_nonneg hz (Ioo_subset_Icc_self ht))
  refine ((hM.sub (hM₀.mono Ioo_subset_Icc_self)).div
    (hw.mono Ioo_subset_Icc_self) (fun t ht => (hpos t ht).ne')).congr ?_
  intro t ht
  exact (eq_div_iff (hpos t ht).ne').2 (heq t ht).symm

end InteractingSLE.Sec7.PocketStopSide
