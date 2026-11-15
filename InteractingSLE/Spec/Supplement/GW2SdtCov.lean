/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdtSlow
import InteractingSLE.Spec.Supplement.GW2TpRoot

/-!
# The version families cover the history's clock on the alive events

Packet PROVE-GW2-SDE (round 19, D45 (3)). The coverage premise of `frameNSlowWordN_slowShellOf` (the candidate's stops
eventually pass the root-`x` clock at the history time, on the alive event) for the two version families in use:

* **`hcov_canon`**: ROOTX's canonical family `GW2Rv.schedVerXCanonFamily` (it exhausts every clock before the
  contact);
* **`hcov_death`**: RELDET's death-capped family `GW2Rd.schedVerXDeathFamily` (decision D27). It exhausts the clock
  below the candidate's death clock, and at an alive history the death clock is past the history's clock because the
  candidate's lifetime is positive (`ae_candLife_pos`, D45 (2)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdt

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

/-- **ROOTX's canonical version family covers the history's clock.** -/
theorem hcov_canon (h13 : Theorem13Statement.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
        cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (GW2Rv.schedVerXCanonFamily h13 Ω c r l a).V n ω := by
  intro Ω _ _ c r l a hg
  have hspec := (GW2Rv.exists_schedVersionsXA_strict h13 c r l a hg.1).choose_spec.choose_spec
  filter_upwards [hspec.2.2.2.2] with ω hω _ hcf hTc
  have e : (GW2Rv.schedVerXCanonFamily h13 Ω c r l a).V =
      (GW2Rv.exists_schedVersionsXA_strict h13 c r l a hg.1).choose_spec.choose := by
    show (GW2Rv.schedVerXCanon h13 c r l a).V = _
    unfold GW2Rv.schedVerXCanon
    simp only [hg.1, ↓reduceDIte]
  rw [e]
  exact hω hcf _ hTc

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **At an alive history the death clock is past the history's clock.** -/
theorem ae_clock_lt_deathClockX (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hg : GW2Rv.GoodRoot c r) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
        deathClockX c r l a ω := by
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  filter_upwards [ae_candLife_pos h13 c r l a, hGTae] with ω hpos hGTω halive hcf hTc
  have hω := hGTω.2 hcf
  have hlife := hpos halive
  unfold deathClockX
  split_ifs with h
  · obtain ⟨hcap, hc⟩ := h
    have hfin : candLife c r l a ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hcap
    have hpos' : 0 < (candLife c r l a ω).toNNReal := ENNReal.toNNReal_pos hlife.ne' hfin
    have hlt : historyTime c r l < historyTime c r l + (candLife c r l a ω).toNNReal :=
      lt_add_of_pos_right _ hpos'
    obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hω
    obtain ⟨-, hmono, -⟩ := clock_props c.W c.ζ ω hα hW hW0 hζ hg.2 hg.1 harc hwc hw0 hγ
    have hclt : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω <
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l + (candLife c r l a ω).toNNReal) ω :=
      hmono hTc hc hlt
    have h0 : 0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω :=
      RootH29.forwardCapacity_nonneg _ _ _ _
    exact (ENNReal.ofReal_lt_ofReal_iff (h0.trans_lt hclt)).2 hclt
  · exact ENNReal.ofReal_lt_top

/-- **RELDET's death-capped version family covers the history's clock** on the alive event. -/
theorem hcov_death (h13 : Theorem13Statement.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
        cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (schedVerXDeathFamily h13 Ω c r l a).V n ω := by
  intro Ω _ _ c r l a hg
  by_cases hord : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l)
  swap
  · exact Eventually.of_forall fun ω halive =>
      absurd (RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive) hord
  filter_upwards [schedVerXDeath_exhausts_death h13 c r l a hg.1 hg.2 hord, ae_clock_lt_deathClockX h13 c r l a hg]
    with ω hex hdeath halive hcf hTc
  exact hex hcf (RootJ32.oldSuccess_of_alive c r l ω halive) _ hTc (hdeath halive hcf hTc)

/-- **Coverage survives a re-indexing** `ψ n ≥ n` (BUF's re-indexed version families). -/
theorem eventually_lt_reindex {V : ℕ → ℝ≥0∞} {ψ : ℕ → ℕ} (hψ : ∀ n, n ≤ ψ n) {x : ℝ≥0∞}
    (h : ∀ᶠ n in atTop, x < V n) : ∀ᶠ n in atTop, x < V (ψ n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact eventually_atTop.2 ⟨N, fun n hn => hN _ (hn.trans (hψ n))⟩

end InteractingSLE.Theorem14.GW2Sdt
