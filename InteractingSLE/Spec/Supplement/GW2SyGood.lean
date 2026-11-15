/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SyJoin
import InteractingSLE.Spec.Supplement.GW2RdSafeGood

/-!
# GW2's stage identity: GB6's good set at the schedule instance

Packet PROVE-GW2-RELDET, ruling R106, open item 4 of the handoff (the good set).

* `exists_goodSet_explored`: GB6's physical good set `PhysGood` for ANY explored curve with a generating trace on
  `[0, ∞)`, with the counterflow retained (`GW2RdSafeGood.exists_goodSet_gw2`'s proof, whose explored curve was the
  extended flow line).
* **`exists_goodSet_sched`**: the good set at the schedule instance, for the explored curve `GW2SyJoin.schedW` and
  its trace `schedTr`. These are the targets `physGood`, `measurableSet_GT`, `GT_ae` of PROVE-GW2-SDE's
  `StageInst.Good` (with `measurable_W` = `GW2SyJoin.measurable_schedW`). Only Theorem 1.3 is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Supp8 Supp8.GB6 Supp8.RelSafe Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24

/-- **GB6's good set for any explored curve**, with the retained curve a flow line of infinite lifetime. -/
theorem exists_goodSet_explored {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ}
    {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsFlowLineDriver κ b J θ P h W ζ)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {X : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ≥0 → ℂ}
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω) ∧ X 0 ω = 0 ∧ IsGeneratingTrace (fun t => X t ω) ⊤ (η ω))
    (s : ℝ≥0) :
    ∃ GT : Set Ω, (∀ ω ∈ GT, PhysGood s X W ζ η γ ω) ∧ MeasurableSet GT ∧
      (∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s W ζ ω ∈ gb6TS s) := by
  have hall : ∀ᵐ ω ∂P,
      (Continuous (fun t => X t ω) ∧ X 0 ω = 0 ∧ IsGeneratingTrace (fun t => X t ω) ⊤ (η ω)) ∧
      (W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
        IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) ∧
      ((s : ℝ≥0∞) < ζ ω → GB6RecGood s W ζ γ ω) ∧
      ((s : ℝ≥0∞) < ζ ω → γ ω s ∈ H →
        Tendsto (QuantumZipper.fwdMapInv (rdrv (gb6Rec s W ζ ω)) s) (𝓝[H] 0) (𝓝 (γ ω s))) := by
    filter_upwards [hX, ae_driver_zero_continuousOn hcf, hγ, ae_gb6RecGood hcf hγ s,
      ae_tendsto_record_tip_top hcf hγ hζ s] with ω hXω hd hγω hg htip
    exact ⟨hXω, ⟨hd.1, hd.2, hγω⟩, hg, fun _ _ => htip⟩
  obtain ⟨G, hGm, hGae, hG⟩ := SourceC.exists_measurable_good hall
  have hrec : Measurable (gb6Rec s W ζ) := (measurable_recOf_cfE hcf s).2
  refine ⟨G ∩ gb6Rec s W ζ ⁻¹' gb6TS s, fun ω hω => ?_, hGm.inter (hrec (measurableSet_gb6TS s)), ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hG ω hω.1
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff h3).2 hω.2
    exact ⟨h1, h2, hs, hsH, h3 hs, h4 hs hsH⟩
  · filter_upwards [hGae] with ω hω
    exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩

/-- The counterflow of a source is a flow line of infinite lifetime with its trace. -/
theorem source_counterflow {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) :
    ∃ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
      IsFlowLineDriver (16 / c.κ) b' J' 0 c.P h' c.W c.ζ ∧
      ∀ᵐ ω ∂c.P, IsGeneratingTrace (fun t => c.W t ω) (c.ζ ω) (c.α ω) := by
  obtain ⟨b', J', h', -, -, hfl⟩ := c.hcf
  refine ⟨b', J', h', hfl, ?_⟩
  filter_upwards [c.hα, c.hζ] with ω h1 h2
  rw [h2]
  exact h1

/-- **GB6's good set at the schedule instance.** -/
theorem exists_goodSet_sched {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∃ GT : Set Ω, (∀ ω ∈ GT, PhysGood c.s (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s) := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  refine exists_goodSet_explored hfl hα c.hζ ?_ c.s
  filter_upwards [ae_schedW_trace c r l a h13] with ω hω
  exact ⟨continuous_schedW c r l a ω, schedW_zero c r l a ω, hω.1⟩

end InteractingSLE.Theorem14.GW2Rd
