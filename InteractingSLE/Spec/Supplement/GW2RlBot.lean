/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RlTop
import InteractingSLE.Spec.Supplement.GW2TuBot

/-!
# The rightward `hstruct` for the reference near base (D37 (A) route)

PROVE-GW2-ROOTX round 11. D37 (A) reads the near base through the rightward selection (`withNearSB`), whose
`hstruct` premise is RELDET's `NearStructBot` rather than SDE's `NearStruct`. Here:

* **`GW2Rl.hstructBot_junction`**: for ANY version family and ANY near base that is, a.s. on the alive event, the base
  word of some version of some candidate passing the history's clock (the `heq` of `vwordsX_pkgRj_junction`), the near
  base has `NearStructBot` at the near scale in the orientation `flipOf |l|` (RELDET's `ae_nearStructBot_junction`
  for every version, a countable intersection);
* **`Wire.T14Rl.hstructBot_rl`**: the same for the top's data (`rlVer ψx`, `rlNb ψx`), with no open input.

So the near data `hword` (`nearSlotWords_rl`), `heq` (`heq_rl`) and both `hstruct` forms are available for the
reference near base, whichever near selection (`withNearS` or `withNearSB`) the final package uses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rl

open Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

/-- **The rightward structure of a near base on the junction-gap cover** (mirror of SDE's `hstruct_junction`). -/
theorem hstructBot_junction (ver : GW2Rv.SchedVerXFamily.{u})
    (nb : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
      List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
    (heq : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l → ∃ a n : ℕ,
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V n ω ∧
        nb Ω c r l ω = GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
            (schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((ver Ω c r l a).V n)
            (historyTime c r l) ((ver Ω c r l a).R n)) ω)) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
        GW2Sdy.NearStructBot c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
          (nb Ω c r l ω) := by
  intro Ω _ _ c r l
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  by_cases hg : GW2Rv.GoodRoot c r
  · have hall : ∀ᵐ ω ∂c.P, ∀ a n : ℕ, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (ver Ω c r l a).V n ω →
        GW2Sdy.NearStructBot c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
          (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l)
            ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
            (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
              (schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((ver Ω c r l a).V n)
              (historyTime c r l) ((ver Ω c r l a).R n)) ω)) :=
      ae_all_iff.2 fun a => ae_all_iff.2 fun n =>
        ae_nearStructBot_junction c r l a hg.1 hg.2 ((ver Ω c r l a).isA hg.1 n).1.1 ((ver Ω c r l a).fin n)
    filter_upwards [heq Ω c r l hg, hall] with ω he hall' halive
    obtain ⟨a, n, hV, hnb⟩ := he halive
    rw [hnb]
    exact hall' a n halive hV
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hgood halive
    exact absurd (hgood (GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive)) hg

end InteractingSLE.Theorem14.GW2Rl

namespace InteractingSLE.Wire.T14Rl

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.RootC24

/-- **The rightward `hstruct` for the top's near base**, closed. -/
theorem hstructBot_rl (ψx : GW2Rl.PsiFamR.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
          ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
        GW2Sdy.NearStructBot c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
          (rlNb ψx Ω c r l ω) :=
  GW2Rl.hstructBot_junction (rlVer ψx) (rlNb ψx) (heq_rl ψx)

end InteractingSLE.Wire.T14Rl
