/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TgMono
import InteractingSLE.Spec.Supplement.GW2BhRule
import InteractingSLE.Spec.Supplement.GB6ReadDTrace

/-!
# Review defect N4: versions of the schedule instance capped strictly before a cap gauge's life

Packet PROVE-GW2-SDE (round 12; DECISIONS-FABLE-3, second pass: N4 with SDE). `OpenLinesS.noThreshold` is false once
the instance's cap passes the candidate piece's lifetime. The fix caps instance `n` before that lifetime. RELDET's
`GW2Rd.exists_versionsA_of_capGauge_mono` already builds monotone announced versions strictly below the life `Lζ` of
ANY cap gauge `Gζ` (causal, Borel, nonnegative; along every relative-driver coordinate continuous, positive before
`Lζ` and zero at `Lζ`), exhausting every clock below `Lζ` before contact. RELDET's schedule family uses the trivial
gauge (`Gζ = 1`, `Lζ = ⊤`). This file:

* **`exists_schedVersionsA_mono_gauge`**: the schedule instance's finite, monotone, exhausting family capped strictly
  below the life of any cap gauge (`V n < Lζ` on the record event; every clock below `Lζ` before contact is eventually
  below `V n`);
* the life gauge of a closed real set `F` read after a path-rule time `A` (the stage start):
  `lifeGauge s F A = afterRead (dist (physicalTrace s t ·) F) A (· / 2)` (BUF's normalized readout of GB6's causal
  physical-trace reader), **`isCausal_lifeGauge`**, **`measurable_lifeGauge`**, **`lifeGauge_nonneg`**: the three
  pathwise conditions of the cap-gauge theorem.

With `F` the closed bad real set of the candidate's angle (D10's set) and `A` the stage start, the remaining condition
along relative coordinates is the continuity of the physical trace there, its first entrance into `F` after `A` being
the life (see the handoff, round 12).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Sdz

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC GW2Rd
  GW2TipSystem GW2TipSystem.RootC24

/-! ### The schedule family capped before a cap gauge's life -/

section Sched

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **The schedule instance's finite monotone exhausting versions, capped strictly below a cap gauge's life**
(RELDET's `exists_schedVersionsA_mono` with any cap gauge in place of the trivial one). -/
theorem exists_schedVersionsA_mono_gauge (hs : 0 < c.s) {Gζ : GaugeReadout} (hGζm : ∀ t, Measurable (Gζ t))
    (hGζc : IsCausal Gζ) (hGζ0 : ∀ t p, 0 ≤ Gζ t p) {Lζ : Ω → ℝ≥0∞}
    (hζ : ∀ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞),
      RelativeDriverCoordinates c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α D L →
      ∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → 0 < Lζ ω ∧
        ContinuousOn (fun t => Gζ t (gb6Rec c.s c.W c.ζ ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < Lζ ω → 0 < Gζ t (gb6Rec c.s c.W c.ζ ω, fun u => D u ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = Lζ ω → Gζ t (gb6Rec c.s c.W c.ζ ω, fun u => D u ω) = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < Lζ ω) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < Lζ ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  obtain ⟨R₀, V₀, hRV₀, hmono₀, hlt₀, hex₀⟩ := exists_versionsA_of_capGauge_mono hfl hα (ae_source_noReturn h13 c)
    (measurable_schedW c r l a) (ae_schedW_regular h13 c r l a) c.s hs hGζm hGζc hGζ0 hζ
  obtain ⟨R, V, hRV, hmono, hle, hfin, hex⟩ := exists_finite_family_mono hRV₀ hmono₀ (measurable_recOf_cfE hfl c.s).2
  refine ⟨R, V, hRV, fun n ω => hmono ω (Nat.le_succ n), hfin, ?_, ?_⟩
  · filter_upwards [hlt₀] with ω hω hrec n using (hle n ω).trans_lt (hω hrec n)
  · filter_upwards [hex₀] with ω hω hs' hsH t ht hlt
    obtain ⟨m, hm⟩ := hω hs' hsH t ht hlt
    exact hex ω _ ENNReal.ofReal_ne_top m hm

end Sched

/-! ### The life gauge of a closed set, read after a path-rule time -/

section Gauge

/-- The distance of GB6's physical trace reader to a set. -/
def traceDist (s : ℝ≥0) (F : Set ℂ) : GaugeReadout :=
  fun t p => Metric.infDist (ReadD.physicalTrace s t p) F

/-- **The life gauge**: BUF's normalized readout of `traceDist` after the path-rule time `A`, at half the distance read
at `A` (`2` before `A`; `min 2 (dist / (ℓ_A / 2))` from `A` on). -/
def lifeGauge (s : ℝ≥0) (F : Set ℂ) (A : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) : GaugeReadout :=
  GW2Bh.afterRead (traceDist s F) A fun ℓ => ℓ / 2

theorem isCausal_traceDist (s : ℝ≥0) (F : Set ℂ) : IsCausal (traceDist s F) := by
  intro t r w w' h
  simp only [traceDist]
  rw [ReadD.physicalTrace_congr s t r h]

theorem measurable_traceDist (s : ℝ≥0) (F : Set ℂ) (t : ℝ≥0) : Measurable (traceDist s F t) :=
  (Metric.continuous_infDist_pt F).measurable.comp (ReadD.measurable_physicalTrace s t)

/-- **The life gauge is causal.** -/
theorem isCausal_lifeGauge (s : ℝ≥0) (F : Set ℂ) {A : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hA : IsPathRule A) :
    IsCausal (lifeGauge s F A) :=
  GW2Bh.isCausal_afterRead (isCausal_traceDist s F) hA

/-- **The life gauge is Borel.** -/
theorem measurable_lifeGauge (s : ℝ≥0) (F : Set ℂ) {A : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hAm : Measurable A)
    (t : ℝ≥0) : Measurable (lifeGauge s F A t) :=
  GW2Bh.measurable_afterRead (measurable_traceDist s F) hAm (measurable_id.div_const 2) t

/-- **The life gauge is nonnegative.** -/
theorem lifeGauge_nonneg (s : ℝ≥0) (F : Set ℂ) (A : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) (t : ℝ≥0)
    (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ lifeGauge s F A t p := by
  simp only [lifeGauge, GW2Bh.afterRead]
  split_ifs
  · refine le_min zero_le_two (div_nonneg Metric.infDist_nonneg ?_)
    refine div_nonneg ?_ zero_le_two
    simp only [GW2Bh.levelAt]
    refine le_ciInf fun q => ?_
    split_ifs
    · exact le_min zero_le_one Metric.infDist_nonneg
    · exact zero_le_one
  · exact zero_le_two

end Gauge

end InteractingSLE.Theorem14.GW2Sdz
