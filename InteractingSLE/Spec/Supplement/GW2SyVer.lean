/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SyFin
import InteractingSLE.Spec.Supplement.GW2SyGood
import InteractingSLE.Spec.Supplement.GW2RdVer

/-!
# GW2's stage identity: GB6 at the schedule instance (explored curve, good set, versions)

Packet PROVE-GW2-RELDET, ruling R106. Open items 1 and 4 of the handoff, at the actual source `c`, root `r`, retained
history `l` and candidate `a`. Explored curve: ROOT2's joined future driver (`GW2SyJoin.schedW`, trace `schedTr`).
Retained curve: the counterflow `(c.W, c.ζ, c.α)` at `c.s`. From Theorem 1.3 only:

* `ae_source_noReturn`: the counterflow does not return to its root (`GW2RdVer.counterflowNoReturn_of_thm13`);
* `ae_schedW_regular`: GB6's explored input `hW` for `schedW`;
* **`exists_schedVersionsA`**: exhausting announced GB6 versions with finite stops;
* **`exists_schedVersionsA_timeCap`**: the same, stopped at the physical time `Δ > 0` (stops `≤ capClock Δ`,
  exhaustion below `Δ`);
* **`exists_schedGB6`**: one bundle with the inputs of PROVE-GW2-SDE's `StageInst.Good`. It gives:
  - GB6's good set (`physGood`, `measurableSet_GT`, `GT_ae`) and `measurable_W`;
  - the versions with `ρ`, `ρs` and the announcement (`IsGB6RelVersionA` is their conjunction);
  - finite stops, so `stgStartM ≤ V < ⊤`;
  - the `c.sigma r l`-measurability of the explored curve up to the history time, which is the input of
    `StageInst.prefix_retained_of_path`, i.e. part (II).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId Supp8.RelSafe GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The counterflow of a source does not return to its root. -/
theorem ae_source_noReturn (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) :
    ∀ᵐ ω ∂c.P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => c.W t ω) (c.ζ ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < c.ζ ω → α' v ≠ 0 := by
  have h1 := counterflowNoReturn_of_thm13 h13 c.κ c.hκ c.hκ4 c.b c.jumps c.hb c.P c.h c.hh c.W c.ζ c.hcf c.hζ
  filter_upwards [h1, c.hζ] with ω hω hz α' hα' v hv _
  rw [hz] at hα'
  exact hω α' hα' v hv

variable [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
theorem ae_schedW_regular : ∀ᵐ ω ∂c.P, Continuous (schedW c r l a · ω) ∧ schedW c r l a 0 ω = 0 ∧
    IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) ∧
    Tendsto (fun t => ‖schedTr c r l a ω t‖) atTop atTop := by
  filter_upwards [ae_schedW_trace c r l a h13] with ω hω
  exact ⟨continuous_schedW c r l a ω, schedW_zero c r l a ω, hω.1, hω.2⟩

include h13 in
/-- **Exhausting announced GB6 versions with finite stops at the schedule instance.** -/
theorem exists_schedVersionsA :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ∃ n, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  exact exists_versionsA_fin_all hfl hα (ae_source_noReturn h13 c) (measurable_schedW c r l a)
    (ae_schedW_regular h13 c r l a) c.s

include h13 in
/-- **Exhausting announced GB6 versions with finite stops at the schedule instance, stopped at the physical time
`Δ`.** -/
theorem exists_schedVersionsA_timeCap {Δ : ℝ≥0} (hΔ : 0 < Δ) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ n,
        V n ω ≤ capClock (gb6Tc c.s (schedTr c r l a) c.α ω) (gb6Clock c.s (schedW c r l a) c.W ω) Δ) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        t < Δ → ∃ n, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  exact exists_versionsA_fin_timeCap hfl hα (ae_source_noReturn h13 c) (measurable_schedW c r l a)
    (ae_schedW_regular h13 c r l a) c.s hΔ

include h13 in
/-- **GB6 at the schedule instance, bundled** for PROVE-GW2-SDE's `StageInst.Good` (explored `schedW`, trace
`schedTr`; any good set `GT`, any version `(R n, V n)`). -/
theorem exists_schedGB6 :
    (∀ t, Measurable (schedW c r l a t)) ∧
    (∀ t ≤ historyTime c r l, MeasurableSpace.comap (schedW c r l a t) inferInstance ≤ c.sigma r l) ∧
    (∃ GT : Set Ω, (∀ ω ∈ GT, PhysGood c.s (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s)) ∧
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ∃ n, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω :=
  ⟨measurable_schedW c r l a, fun _ ht => comap_schedW_le_sigma c r l a ht, exists_goodSet_sched h13 c r l a,
    exists_schedVersionsA h13 c r l a⟩

end InteractingSLE.Theorem14.GW2Rd
