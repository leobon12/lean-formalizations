/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdsN3
import InteractingSLE.Spec.Supplement.GW2SdoShape
import InteractingSLE.Spec.Supplement.GW2RootH29Cover

/-!
# The near structure (N3) in the form of `vwordsX_withNearS`'s `hstruct`

Packet PROVE-GW2-SDE (round 18). `GW2Sdo.vwordsX_withNearS` asks (N3) for the near base-word reader `base` of the pinned
selection, at every root and history, almost surely on the alive event. Here:

* `ae_goodRoot_of_alive`: on J32's alive event the root is good almost surely (the cover event's root is admissible and
  its counterflow tip is interior; as in `GW2Rv.ae_goodRoot_of_gate`);
* **`hstruct_span`**, **`hstruct_junction`**: (N3) for any reader that, almost surely on the alive event, is the base
  word of SOME root-`x` version (of a version family `ver`) of SOME candidate whose stop passes the history's clock
  (the reader of round 14's `GW2Sdo.exists_reindex_nearWords` is such a reader); for J32S over the span gap
  `GW2Sdr.gapFam2` (ASSEMBLE7's current top) and over the junction gap `GW2Sdq.gapFam`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Wm

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **On J32's alive event the root is good**, almost surely. -/
theorem ae_goodRoot_of_alive (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l → GW2Rv.GoodRoot c r := by
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα] with ω hcover hα halive
  obtain ⟨hcov, -, -⟩ := RootJ32.alive_spec c r l ω halive
  obtain ⟨hseed, hsH, -⟩ := hcover hcov
  refine ⟨RootH29.rootPt_nonneg_of_seedOK c hseed, ?_⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ c.s) with h | h
  · exfalso
    rw [← h, hα.1] at hsH
    exact (lt_irrefl (0 : ℝ)) hsH
  · exact h

/-- **(N3) as `hstruct` on the span-gap cover**: for a version family `ver` and any near base-word reader that is,
almost surely on the alive event, the base word of some version of some candidate passing the history's clock. -/
theorem hstruct_span (ver : GW2Rv.SchedVerXFamily.{u})
    (nb : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
      List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
    (heq : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdr.gapFam2 Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdr.gapFam2 Ω c).G r) l → ∃ a n : ℕ,
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V n ω ∧
        nb Ω c r l ω = GW2Wm.baseWordX c.κ (cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
            (schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((ver Ω c r l a).V n)
            (historyTime c r l) ((ver Ω c r l a).R n)) ω)) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdr.gapFam2 Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdr.gapFam2 Ω c).G r) l →
        GW2Sdy.NearStruct c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
          (nb Ω c r l ω) := by
  intro Ω _ _ c r l
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  by_cases hg : GW2Rv.GoodRoot c r
  · have hall : ∀ᵐ ω ∂c.P, ∀ a n : ℕ, ω ∈ ((GW2Sdz.J32S GW2Sdr.gapFam2 Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdr.gapFam2 Ω c).G r) l →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V n ω →
        ∀ flip : Bool, GW2Sdy.NearStruct c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) flip
          (GW2Wm.baseWordX c.κ (cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
            (GW2Ru.length_historyProgram c r l)
            (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
              (schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((ver Ω c r l a).V n)
              (historyTime c r l) ((ver Ω c r l a).R n)) ω)) :=
      ae_all_iff.2 fun a => ae_all_iff.2 fun n =>
        ae_nearStruct_span c r l a hg.1 hg.2 ((ver Ω c r l a).isA hg.1 n).1.1 ((ver Ω c r l a).fin n)
    filter_upwards [heq Ω c r l hg, hall] with ω he hall' halive
    obtain ⟨a, n, hV, hnb⟩ := he halive
    rw [hnb]
    exact hall' a n halive hV _
  · filter_upwards [ae_goodRoot_of_alive h13 c r l] with ω hgood halive
    exact absurd (hgood (GW2Sdz.alive_scaled_subset GW2Sdr.gapFam2 Ω c r l halive)) hg

/-- **(N3) as `hstruct` on the junction-gap cover**: for a version family `ver` and any near base-word reader that is,
almost surely on the alive event, the base word of some version of some candidate passing the history's clock. -/
theorem hstruct_junction (ver : GW2Rv.SchedVerXFamily.{u})
    (nb : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
      List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
    (heq : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l → ∃ a n : ℕ,
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V n ω ∧
        nb Ω c r l ω = GW2Wm.baseWordX c.κ (cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
            (schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((ver Ω c r l a).V n)
            (historyTime c r l) ((ver Ω c r l a).R n)) ω)) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
        GW2Sdy.NearStruct c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
          (nb Ω c r l ω) := by
  intro Ω _ _ c r l
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  by_cases hg : GW2Rv.GoodRoot c r
  · have hall : ∀ᵐ ω ∂c.P, ∀ a n : ℕ, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V n ω →
        ∀ flip : Bool, GW2Sdy.NearStruct c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) flip
          (GW2Wm.baseWordX c.κ (cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
            (GW2Ru.length_historyProgram c r l)
            (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
              (schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((ver Ω c r l a).V n)
              (historyTime c r l) ((ver Ω c r l a).R n)) ω)) :=
      ae_all_iff.2 fun a => ae_all_iff.2 fun n =>
        ae_nearStruct_junction c r l a hg.1 hg.2 ((ver Ω c r l a).isA hg.1 n).1.1 ((ver Ω c r l a).fin n)
    filter_upwards [heq Ω c r l hg, hall] with ω he hall' halive
    obtain ⟨a, n, hV, hnb⟩ := he halive
    rw [hnb]
    exact hall' a n halive hV _
  · filter_upwards [ae_goodRoot_of_alive h13 c r l] with ω hgood halive
    exact absurd (hgood (GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive)) hg

end InteractingSLE.Theorem14.GW2Sds
