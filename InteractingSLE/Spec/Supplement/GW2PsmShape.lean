/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzShape
import InteractingSLE.Spec.Supplement.GW2RvInst
import InteractingSLE.Spec.Supplement.GW2SdpRoot
import InteractingSLE.Spec.Supplement.GW2FbDual
import InteractingSLE.Spec.Supplement.GW2OmxDil6

/-!
# GW2's open lines: the root-`x` shape at every stage time on one event, and the instance at root `0`

Packet PROVE-GW2-STAGEMEAN, R121 round.

* **`ae_compl_union_eq_relChartX_all`**: ROOTX's `GW2Rz.ae_compl_union_eq_relChartX` with the stage time quantified
  inside the almost-sure event (the same proof: the event is the version's, independent of the time);
* `relChartX_of_baseRead_zero`, **`baseRead_zero_cfRec`**: at the root `0`, ROOTX's re-centred chart is GB6's relative
  chart (the retained hull stays off the target `0`);
* **`schedUnionSX_eq_schedUnionS`**: at the root `0` the corrected root-`x` union is the root-`0` union.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Psm

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.ReadD GW2TipSystem GW2Rz
open Supp8.RelSafe (supBelow)

section Shape

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)

include hGT hs₀ hx₀ in
/-- **ROOTX's shape at every stage time on one almost-sure event.** -/
theorem ae_compl_union_eq_relChartX_all (hver : IsRelVersionX x₀ s P Wα ζα W γ α R V) :
    ∀ᵐ ω ∂P, ω ∈ GT → ∀ t : ℝ≥0, min (physClockX x₀ s Wα ζα W GT t ω) (V ω) < V ω →
      H \ (Supp8.Q3Rel.invHull (rdrv (cfRec s Wα ζα ω)) s ∪
          (fun z : ℂ => z + x₀) '' fwdHull (fun r : ℝ => W r.toNNReal ω) t) =
        (relChartX x₀ s (cfRec s Wα ζα ω)).2.1 ''
          (H \ fwdHull (Ito.rpath fun u => R u ω) (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal) := by
  filter_upwards [hver.2.2.2.2.2.2] with ω hω hωG t hlt
  have hg := hGT ω hωG
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hWc, hW0, hζ⟩, harc, -, hgx⟩ := hg
  obtain ⟨-, hreachV, hhull⟩ := hω hgx
  obtain ⟨hfc, hfm, hf0⟩ := clockX_props hGT hs₀ hx₀ hωG
  -- `t` is before the root-`x` contact
  have htc : (t : ℝ≥0∞) < contactX x₀ s γ α ω := by
    by_contra hcon
    have hle : contactX x₀ s γ α ω ≤ t := le_of_not_gt hcon
    have hV : V ω ≤ physClockX x₀ s Wα ζα W GT t ω := by
      rw [physClockX_eq_iSup hGT hs₀ hx₀ hωG]
      refine ENNReal.le_of_forall_nnreal_lt fun u hu => ?_
      obtain ⟨t', ht', hut'⟩ := hreachV u hu
      have ht't : t' < t := by
        have := lt_of_lt_of_le ht' hle
        exact_mod_cast this
      refine le_trans ?_ (le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < contactX x₀ s γ α ω) =>
        ENNReal.ofReal (clockX x₀ s Wα ζα W t' ω)) t' ⟨ht't, ht'⟩)
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hut'.le
    rw [min_eq_right hV] at hlt
    exact lt_irrefl _ hlt
  have hphys := physClockX_eq_clockX hGT hs₀ hx₀ hωG htc
  have h0 := (clock_props Wα ζα ω hα hWc hW0 hζ hs₀ hx₀ harc hwc hw0 hγ).1
  have hm := (clock_props Wα ζα ω hα hWc hW0 hζ hs₀ hx₀ harc hwc hw0 hγ).2.1
  have hnn : 0 ≤ clockX x₀ s Wα ζα W t ω := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h]; exact h0.ge
    · have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < contactX x₀ s γ α ω := lt_of_le_of_lt bot_le htc
      exact le_of_lt (lt_of_eq_of_lt h0.symm (hm h0T htc h))
  have hlt' : ENNReal.ofReal (clockX x₀ s Wα ζα W t ω) < V ω := by
    rw [hphys] at hlt
    exact lt_of_not_ge fun h => lt_irrefl _ (by rwa [min_eq_right h] at hlt)
  have hmin : min (physClockX x₀ s Wα ζα W GT t ω) (V ω) = ENNReal.ofReal (clockX x₀ s Wα ζα W t ω) := by
    rw [hphys]
    exact min_eq_left hlt'.le
  have hreal : (((ENNReal.ofReal (clockX x₀ s Wα ζα W t ω)).toNNReal : ℝ≥0) : ℝ) = clockX x₀ s Wα ζα W t ω := by
    rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hnn]
  have hH' : fwdHull (fun r : ℝ => R r.toNNReal ω)
        (RootH29.forwardCapacity x₀ s t (cfRec s Wα ζα ω, recOf (t : ℝ≥0∞) ((fun t => W t ω), ⊤))) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x₀ s (cfRec s Wα ζα ω, recOf (t : ℝ≥0∞) ((fun t => W t ω), ⊤)) : ℝ) :
        ℂ)) '' RootH29.forwardHull x₀ s t (cfRec s Wα ζα ω, recOf (t : ℝ≥0∞) ((fun t => W t ω), ⊤)) :=
    hhull t htc hlt'.le
  have key := compl_union_eq_relChartX Wα ζα ω (α := α ω) (s := s) (x := x₀) (w := fun t => W t ω)
    (γ := γ ω) hα hWc hW0 hζ hx₀ harc hwc hw0 hγ (t := t) htc (R := fun u => R u ω) hH'
  rw [hmin, hreal]
  exact key

end Shape

section Root0

/-- **At a vanishing reading, ROOTX's re-centred chart is GB6's relative chart.** -/
theorem relChartX_of_baseRead_zero {x : ℝ} {s : ℝ≥0} {r : RecData} (h : baseRead x s r = 0) :
    relChartX x s r = Supp8.RelSafeS.relChart r := by
  unfold relChartX Chart.recenter
  rw [h]
  refine Prod.ext (funext fun z => ?_) (Prod.ext (funext fun z => ?_) rfl)
  · simp
  · simp

/-- **At the root `0` the reading of the counterflow record is `0`** (the retained hull stays off the target). -/
theorem baseRead_zero_cfRec {Ω : Type*} (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (ω : Ω) (hζ : ζ' ω = ⊤) :
    baseRead 0 s (cfRec s W' ζ' ω) = 0 := by
  have hrt : rtime (cfRec s W' ζ' ω) = s := by
    unfold cfRec
    rw [rtime_recOf_coe, GW2JointKernel.cfE_snd, hζ, min_top_right, ENNReal.toNNReal_coe]
  refine GW2Sdp.baseRead_zero s _ hrt fun h0 => ?_
  obtain ⟨ρ, hρ, hρw⟩ := GW2Omx.exists_ball_disjoint_invHull (continuous_rdrv (cfRec s W' ζ' ω)) s.coe_nonneg
  have hcl : closure (Supp8.Q3Rel.invHull (rdrv (cfRec s W' ζ' ω)) s) ⊆ {w : ℂ | ρ ≤ ‖w‖} :=
    closure_minimal (fun w hw => hρw w hw) (isClosed_le continuous_const continuous_norm)
  have := hcl h0
  simp only [mem_ofPred_eq, Complex.ofReal_zero, norm_zero] at this
  linarith

/-- **At the root `0` the corrected root-`x` union is the root-`0` union.** -/
theorem schedUnionSX_eq_schedUnionS {Ω : Type*} [MeasurableSpace Ω] (c : GW2TipSystem.RootC24.SourceData Ω)
    (r : GW2TipSystem.ScaledRootIdx c.Θ c.Q) (l : List (GW2TipSystem.EntryIdx c.Θ c.Q))
    (a : ℕ) (hr0 : GW2TipSystem.rootPt r.1 = 0) (t : ℝ≥0) (ω : Ω) :
    GW2Rv.schedUnionSX c r l a t ω = GW2Sdi.schedUnionS c r l a t ω := by
  unfold GW2Rv.schedUnionSX GW2Sdi.schedUnionS GW2Rz.schedPhysUnionX GW2Sdh.schedPhysUnion
  rw [hr0]
  have hid : (fun z : ℂ => z + ((0 : ℝ) : ℂ)) = id := funext fun z => by simp
  rw [hid, image_id]
  rfl

end Root0

end InteractingSLE.Theorem14.GW2Psm
