/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TlDeath
import InteractingSLE.Spec.Supplement.GW2TkStrict

/-!
# N4 item 1 in launch coordinates, part 8: the capped family strictly below the candidate's death

Packet PROVE-GW2-RELDET (decision D20, option (A); review defect N4, item 1). The schedule instance's announced GB6
versions, capped by the death gauge of the candidate's LAUNCH coordinates (`launchGauge`: the distance of the launch
trace to the bad set of the canonical launch word, both read off (counterflow record, relative path)):

* **`exists_schedVersionsA_strict_launch`**: finite versions, monotone at every sample, strictly increasing on the
  record event, with caps strictly below the launch gauge's life `schedLaunchLife` on the record event, and exhausting
  every relative clock value before the first contact and below that life (RELDET's
  `exists_schedVersionsA_strict_gauge` with `ae_launchGauge_coord`);
* `deathClock`: the relative clock of the candidate's death `T + ζ` (`ζ` the candidate's lifetime) when the death is
  before the cap and before the first contact, `⊤` otherwise;
* **`ae_schedLaunchLife_eq`**: on the history's success (time-ordered history) at a positive lifetime, the launch
  gauge's life IS the death clock, almost surely (`ae_candDist`);
* **`exists_schedVersionsA_strict_death`**: the family above, with "cap strictly below the death" and "exhaustion below
  the death" stated for the death clock.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC
open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Sec5.Prop513Schedule

section Fam

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The death gauge of the candidate's launch coordinates** at the schedule instance. -/
abbrev schedLaunchGauge : GaugeReadout :=
  launchGauge c.κ (candAngle c r l a) (launchWordOf c r l a) (historyTime c r l) (candidateCap c r a) c.s

/-- The life of the schedule instance's launch gauge. -/
abbrev schedLaunchLife (ω : Ω) : ℝ≥0∞ :=
  launchLife c.κ (candAngle c r l a) (launchWordOf c r l a) (historyTime c r l) (candidateCap c r a)
    (fun t => schedW c r l a t ω) (gb6Clock c.s (schedW c r l a) c.W ω) (gb6Tc c.s (schedTr c r l a) c.α ω)

open scoped Classical in
/-- **The relative clock of the candidate's death** `T + ζ`, when the death is before the cap and before the first
contact; `⊤` otherwise. -/
def deathClock (ω : Ω) : ℝ≥0∞ :=
  if candLife c r l a ω ≤ candidateCap c r a ∧
      ((historyTime c r l + (candLife c r l a ω).toNNReal : ℝ≥0) : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω then
    ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω (historyTime c r l + (candLife c r l a ω).toNNReal))
  else ⊤

end Fam

section Sched

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **The schedule instance's versions capped strictly before the life of the launch-coordinate death gauge**
(review defect N4, item 1, decision D20 (A)): finite, monotone, strictly increasing on the record event, below the
life of `schedLaunchGauge` on the record event, and exhausting every relative clock value below that life before the
first contact. -/
theorem exists_schedVersionsA_strict_launch (hs : 0 < c.s) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < schedLaunchLife c r l a ω) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < schedLaunchLife c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hW' : ∀ᵐ ω ∂c.P, Continuous (schedW c r l a · ω) ∧ schedW c r l a 0 ω = 0 ∧
      IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) :=
    (ae_schedW_regular h13 c r l a).mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  exact exists_schedVersionsA_strict_gauge h13 c r l a hs
    (measurable_launchGauge (measurable_launchWordOf c r l a) c.s) (isCausal_launchGauge c.s)
    (launchGauge_nonneg c.s)
    (fun D L hC => ae_launchGauge_coord hfl hα (ae_source_noReturn h13 c) hW' c.s hs hC
      fun w w' h => launchWordOf_congr c r l a h)

include h13 in
/-- **The launch gauge's life is the candidate's death clock**, almost surely, on the history's success (time-ordered
history) at a positive lifetime. -/
theorem ae_schedLaunchLife_eq (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < candLife c r l a ω →
      schedLaunchLife c r l a ω = deathClock c r l a ω := by
  classical
  filter_upwards [ae_candDist h13 c r l a hord] with ω hω hold hζ0
  obtain ⟨hpos, hzero⟩ := hω hold hζ0
  set f := launchDist c.κ (candAngle c r l a) (launchWordOf c r l a) (historyTime c r l)
    (fun t => schedW c r l a t ω) with hfdef
  set cap := candidateCap c r a with hcap
  set T := historyTime c r l with hT
  set Tc := gb6Tc c.s (schedTr c r l a) c.α ω with hTc
  set Z : Set ℝ≥0 := {σ | σ ≤ cap ∧ f σ = 0} with hZ
  have hd0 : launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 := by
    rw [← launchDist_zero (T := T)]
    exact (hpos 0 zero_le (by simpa using hζ0)).ne'
  have hlife : schedLaunchLife c r l a ω =
      if launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 ∧
        ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc then
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω (T + sInf Z)) else ⊤ := rfl
  rw [hlife, deathClock]
  by_cases hζc : candLife c r l a ω ≤ cap
  · have hne : candLife c r l a ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hζc
    set ζ := (candLife c r l a ω).toNNReal with hζ
    have hζe : (ζ : ℝ≥0∞) = candLife c r l a ω := ENNReal.coe_toNNReal hne
    have hζcap : ζ ≤ cap := by rw [← ENNReal.coe_le_coe, hζe]; exact hζc
    have hmem : ζ ∈ Z := ⟨hζcap, hzero hζc⟩
    have hmin : ∀ σ ∈ Z, ζ ≤ σ := by
      intro σ hσ
      by_contra hlt
      have hσζ : (σ : ℝ≥0∞) < candLife c r l a ω := by rw [← hζe]; exact ENNReal.coe_lt_coe.2 (not_le.1 hlt)
      exact (hpos σ hσ.1 hσζ).ne' hσ.2
    have hinf : sInf Z = ζ :=
      le_antisymm (csInf_le (OrderBot.bddBelow Z) hmem) (le_csInf ⟨ζ, hmem⟩ hmin)
    have hiff : (∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc) ↔ ((T + ζ : ℝ≥0) : ℝ≥0∞) < Tc := by
      constructor
      · rintro ⟨σ, hσc, hσf, hσT⟩
        exact (ENNReal.coe_le_coe.2 (add_le_add_right (hmin σ ⟨hσc, hσf⟩) T)).trans_lt hσT
      · intro h
        exact ⟨ζ, hζcap, hmem.2, h⟩
    by_cases hTζ : ((T + ζ : ℝ≥0) : ℝ≥0∞) < Tc
    · have hc1 : launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 ∧
          ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc := ⟨hd0, hiff.2 hTζ⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc1), ite_eq_left_of_eq_true _ _ (eq_true ⟨hζc, hTζ⟩), hinf]
    · have hc1 : ¬ (launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 ∧
          ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc) := fun h => hTζ (hiff.1 h.2)
      have hc2 : ¬ (candLife c r l a ω ≤ cap ∧ ((T + ζ : ℝ≥0) : ℝ≥0∞) < Tc) := fun h => hTζ h.2
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_right_of_eq_false _ _ (eq_false hc2)]
  · have hc1 : ¬ (launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 ∧
        ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc) := by
      rintro ⟨-, σ, hσc, hσf, -⟩
      have hσζ : (σ : ℝ≥0∞) < candLife c r l a ω :=
        (ENNReal.coe_le_coe.2 hσc).trans_lt (lt_of_not_ge hζc)
      exact (hpos σ hσc hσζ).ne' hσf
    have hc2 : ¬ (candLife c r l a ω ≤ cap ∧
        ((T + (candLife c r l a ω).toNNReal : ℝ≥0) : ℝ≥0∞) < Tc) := fun h => hζc h.1
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_right_of_eq_false _ _ (eq_false hc2)]

include h13 in
/-- **N4 item 1 in launch coordinates**: the schedule instance's versions, finite, monotone and strictly increasing on
the record event, capped strictly below the candidate's death and exhausting every relative clock value below it
before the first contact — on the history's success (time-ordered history) at a positive lifetime. -/
theorem exists_schedVersionsA_strict_death (hs : 0 < c.s) (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → oldSuccess c r l ω → 0 < candLife c r l a ω →
        ∀ n, V n ω < deathClock c r l a ω) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → oldSuccess c r l ω → 0 < candLife c r l a ω →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < deathClock c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨R, V, hRV, hmono, hstrict, hfin, hlt, hex⟩ := exists_schedVersionsA_strict_launch h13 c r l a hs
  refine ⟨R, V, hRV, hmono, hstrict, hfin, ?_, ?_⟩
  · filter_upwards [hlt, ae_schedLaunchLife_eq h13 c r l a hord] with ω h1 h2 hrec hold hζ0 n
    rw [← h2 hold hζ0]
    exact h1 hrec n
  · filter_upwards [hex, ae_schedLaunchLife_eq h13 c r l a hord] with ω h1 h2 hs' hsH hold hζ0 t ht htl
    rw [← h2 hold hζ0] at htl
    exact h1 hs' hsH t ht htl

end Sched

end InteractingSLE.Theorem14.GW2Rd
