/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.OneForceBand

/-!
# One-force transience for `κ > 4` (Part B.2)

Packet PROVE-ZHAN-GT4-B3. Source: Astra, *Follow-up proofs and dependency audit*, §B.2 L1159–L1188 (ruling R38): "Now
start
the one force at `0+` … It reaches gap one at a finite stopping time. The mapped future is the separated law just
treated.
If the original trace accumulated at zero, the future trace would accumulate on the compact real inverse fibre of zero
under that finite prefix. This is impossible. … Scaling of the seed law gives `Z =d rZ` … Thus `Z = ∞` almost surely. …
Restart the seed law when its gap is one, then scale, to obtain transience for every separated one-force law. Reflection
gives the other side." (Additional note, Proposition 3.3, L1453–L1471, ruling R39.)

* The seed is not a terminal cluster point: restart the seed one-force law at time `1`; the future is a separated
  one-force law, which has no real terminal cluster point (`ae_noRealCluster_oneForce`), and the inverse-fibre step
  (`eventually_le_norm_of_shift_noRealCluster`, GT4-B) applies (`ae_noCluster_zero_oneSeed`).
* Seed transience by scaling (`ae_tendsto_norm_trace_seed_of_noCluster`, GT4-B's two-seed argument for every seed word,
  with the uniqueness in law of Theorem 2.2, `measure_killedState_eq_assembled`, in place of the two-seed one).
* Separated transience: restart the seed law at time `1`; the future word is a positive multiple of the target word, the
  canonical non-transience probability is dilation invariant, and the future of a transient trace is transient
  (`codeLaw_nt_eq_zero_oneForce`, `ae_tendsto_norm_trace_oneForce`). The right side by reflection
  (`ae_tendsto_norm_trace_oneForce_right`).

All results take (G5) for ordinary `SLE_κ` at positive stopping times (`StoppingInverseBoundaryStatement κ`, Part A) as
the only input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper

/-! ### The seed is not a terminal cluster point -/

/-- **No real terminal cluster at a realized separated one-force word**: the canonical probability of the complement of
the no-real-cluster event is zero (given (G5)). -/
theorem codeLaw_compl_noClusterCodeSet_eq_zero_oneForce {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} (hρ : κ / 2 - 2 ≤ ρL 0)
    {s : (Fin 1 → ℝ) × (Fin 0 → ℝ)} (hs : s.1 0 < 0)
    (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR) :
    codeLaw κ ρL ρR (noClusterCodeSet (nL := 1) (nR := 0))ᶜ s = 0 := by
  have hκ : 0 < κ := by linarith
  have hsep : ∀ (i : Fin 1) (j : Fin 0), s.1 i < s.2 j := fun _ j => j.elim0
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{0} hsep hsolv
  have hev : ∀ᵐ ω ∂P, NoClusterEvent (fun t => W t ω) (ζ ω) := by
    filter_upwards [IsIntegratedSLEEvolution.ae_noRealCluster_oneForce hκ4 hG5 hs hρ hE,
      hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ (isOrderedForceWord_oneLeft hs.le)
        (hasAdmissiblePartialSums_oneLeft hρ) (fun i => by rw [Fin.fin_one_eq_zero i]; exact hs) (fun j => j.elim0),
      IsIntegratedSLEEvolution.ae_good_oneForce hκ hs hρ hE] with ω hnoω ⟨hζ, η, hη⟩ ⟨_, hwc, hw0, _⟩
    rw [hζ]
    exact NoClusterEvent.of_noRealCluster hwc hw0 hη (hnoω η hη)
  have e := measure_eventOf_eq_codeLaw hκ hsep hE (Φ := fun w τ => ¬ NoClusterEvent w τ)
    measurableSet_noClusterCodeSet.compl (fun _ _ _ => Iff.rfl) not_noClusterEvent_congr
  rw [← e]
  exact ae_iff.1 hev

section Seed

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL : Fin 1 → ℝ} {xR ρR : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The seed is not a terminal cluster point of the seed one-force law** (B.2 L1180–L1188), `κ > 4`, given (G5). -/
theorem IsIntegratedSLEEvolution.ae_noCluster_zero_oneSeed (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hρ : κ / 2 - 2 ≤ ρL 0)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖η t‖ := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ : 0 < κ := by linarith
  have hF : IsOrderedForceWord (fun _ : Fin 1 => (0 : ℝ)) xR := isOrderedForceWord_oneLeft le_rfl
  have hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ : Fin 1 => (0 : ℝ)) xR :=
    hasAdmissiblePartialSums_oneLeft hρ
  have hT := isStoppingTime_const 𝓕 (1 : ℝ≥0)
  have hA : MeasurableSet[hT.measurableSpace] (restartEventTies 1 (fun _ => 0) xR W VL VR ζ) := by
    rw [IsStoppingTime.measurableSpace_const]
    exact measurableSet_restartEventTies 1 hE
  have hAT : ∀ ω ∈ restartEventTies 1 (fun _ => 0) xR W VL VR ζ,
      (((fun _ => (1 : ℝ≥0)) ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ (0 < (fun _ => (1 : ℝ≥0)) ω ∨
        ∀ i j, (fun _ : Fin 1 => (0 : ℝ)) i < xR j) :=
    fun ω hω => ⟨hω.1, Or.inl one_pos⟩
  have hlaw := measure_restart_codeEvent hκ hE hT hA hAT (Φ := fun w τ => ¬ NoClusterEvent w τ)
    measurableSet_noClusterCodeSet.compl (fun _ _ _ => Iff.rfl) not_noClusterEvent_congr
  have hAm : MeasurableSet (restartEventTies 1 (fun _ => 0) xR W VL VR ζ) := hT.measurableSpace_le _ hA
  have hzero : ∫⁻ ω in restartEventTies 1 (fun _ => 0) xR W VL VR ζ,
      codeLaw κ ρL ρR (noClusterCodeSet (nL := 1) (nR := 0))ᶜ (wordAt W VL VR (fun _ => 1) ω) ∂P = 0 := by
    refine (setLIntegral_congr_fun_ae hAm ?_).trans (setLIntegral_const _ 0 |>.trans (zero_mul _))
    filter_upwards [ae_solvable_restart hκ hE hT hA hAT] with ω h hω
    obtain ⟨-, -, hxL', -⟩ := word_of_mem_restartEventTies hF hadm hω
    exact codeLaw_compl_noClusterCodeSet_eq_zero_oneForce hκ4 hG5 hρ (hxL' 0) (h hω).2
  rw [hzero] at hlaw
  have h1 : ∀ᵐ ω ∂P, ω ∈ restartEventTies 1 (fun _ => 0) xR W VL VR ζ →
      NoClusterEvent (fun t => W (1 + t) ω - W 1 ω) (ζ ω - 1) := by
    rw [ae_iff]
    refine le_antisymm (le_of_eq_of_le ?_ hlaw.le) bot_le
    congr 1
    ext ω
    simp only [mem_ofPred_eq, Classical.not_imp, mem_inter_iff, ENNReal.coe_one]
  filter_upwards [h1, Zhan.IsIntegratedSLEEvolution.ae_mem_restartEventTies hκ hF hadm hE, hE.2.2.2.2]
    with ω hev ⟨hζ, hmem⟩ hp η hη
  obtain ⟨-, hTop, hRat⟩ := hev (hmem 1 one_pos)
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  have hw0 : (fun t => W t ω) 0 = 0 := hp.1
  have hwc₂ : Continuous (Sec7.shiftNN (fun t => W t ω) 1) :=
    (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
  obtain ⟨η₂, hη₂⟩ := (ratVals_mem_topSet_iff hwc₂ (Sec7.shiftNN_zero _ _)).1 hTop
  have hno₂ := (ratVals_mem_ratNoClusterSet_iff hwc₂ (Sec7.shiftNN_zero _ _) hη₂).1 hRat
  exact eventually_le_norm_of_shift_noRealCluster hwc hw0 hη hη₂ hno₂

end Seed

end InteractingSLE.ZhanGT4
