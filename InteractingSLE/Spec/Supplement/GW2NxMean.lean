/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NxFam
import InteractingSLE.Spec.Supplement.GW2NwMean
import InteractingSLE.Spec.Supplement.GW2SdzPair
import InteractingSLE.Spec.Supplement.GW2GmJ32Data

/-!
# Decision D54: alive histories are strictly ordered; the `mean` statement at the stop family

Packet PROVE-GW2-NOTHR (round 6, decision D54 (A)). The `mean` part of the top's `hmeanF` is guarded by STRICT
history order: only alive histories are read, and they are strictly ordered.

* `AliveStrict`: alive histories of a construction family are strictly time-ordered (almost surely);
  **`aliveStrict_rootJ32`** (`RootJ32.pairwise_lt_historyProgram_of_alive`), **`aliveStrict_scaled`** (the top's
  scaled cover `GW2Sdz.J32S gap`), **`aliveS_pairwise_lt`** (pointwise, on the top's `T14Cur.aliveS gap`), and
  `aliveOrdered_of_aliveStrict` (strict ⇒ D1's weak guard);
* **`hVd_stop`**: the stop-capped family `GW2Nx.schedVerXStopFamily` (D49 (A)) is stopped at the candidate's stop on
  the live event of the top's instances `T14Cur.instC _ (T14Cur.baseWm cw)` — the `hVd` binder of
  `GW2Nw.hmeanF_root0`, at strictly ordered histories and good roots;
* **`hmeanF_root0_stop`**, **`hmeanF_root0_stop_canon`**: the top's `hmeanF` form at roots `0` and strictly ordered
  histories, for the stop family, modulo only RELDET's R1–R4 statements (`GW2Psm.PrefixLifeStatement`,
  `GW2Psm.PrefixContactStatement`, `GW2Nw.PrefixLiveCoverStatement`, `GW2Nw.PrefixIdentStatement`,
  `GW2Nw.BetaConsStatement`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Nx

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd
  Sec5.Prop513Schedule Supp8 Supp8.Q3Stop GW2Psm GW2Sde ZhanGT4.UpMark

/-! ### Alive histories are strictly ordered -/

/-- **Alive histories of `D` are strictly time-ordered** (almost surely; the strict guard of decision D54). -/
def AliveStrict (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)

/-- **J32's alive histories are strictly time-ordered** (`RootJ32.pairwise_lt_historyProgram_of_alive`). -/
theorem aliveStrict_rootJ32 : AliveStrict RootJ32.constructionFamily.{u} :=
  fun _ _ _ c r l => Eventually.of_forall fun ω h => RootJ32.pairwise_lt_historyProgram_of_alive c r l ω h

/-- **The top's alive histories are strictly time-ordered**, pointwise: on J32's alive event over the scaled cover
(`T14Cur.aliveS gap`). -/
theorem aliveS_pairwise_lt (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) {ω : Ω}
    (h : ω ∈ Wire.T14Cur.aliveS gap Ω c r l) : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) :=
  RootJ32.pairwise_lt_historyProgram_of_alive c r l ω (GW2Sdz.alive_scaled_subset gap Ω c r l h)

/-- **The scaled family's alive histories are strictly time-ordered** (the top's `GW2Sdz.J32S gap`). -/
theorem aliveStrict_scaled (gap : RootCv.GapFamily.{u}) : AliveStrict (GW2Sdz.J32S gap) :=
  fun Ω _ _ c r l => Eventually.of_forall fun _ h => aliveS_pairwise_lt gap Ω c r l h

/-- Strictly ordered alive histories are (weakly) time-ordered: D1's guard `GW2Sdx.AliveOrdered`. -/
theorem aliveOrdered_of_aliveStrict {D : ConstructionFamily.{u}} (hD : AliveStrict D) : GW2Sdx.AliveOrdered D :=
  fun Ω _ _ c r l => (hD Ω c r l).mono fun _ h ha => Gm.timeOrdered_of_pairwise_lt (h ha)

/-! ### The stop family at the top's instances -/

/-- **The stop-capped family is stopped at the candidate's stop on the live event of the top's instances**
(decision D49 (A); the `hVd` binder of `GW2Nw.hmeanF_root0`). On the live event the records are good
(`StageInst.E_good_of_recordX`), the history succeeded (`augRec_mem_succRec_iff`) and the record is off
`launchBadRec` (the base family's record event), so the lifetime is positive (`ae_life_pos_of_srecX_notMem`). -/
theorem hVd_stop (cw : Wire.T14Cur.CfWord.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) → (h : GW2Rv.GoodRoot c r) → ∀ (a n : ℕ)
      (w : WordType), ∀ᵐ ω ∂c.P,
        ω ∈ liveEvRec c.κ w
          (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n h).β
          (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n h).E
          ((Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n
            h).srecX c r l (rootPt r.1)) →
        (schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).V n ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ
          (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a) (historyTime c r l + candStop c r l a ω) ω := by
  intro Ω _ _ c r l hord h a n w
  have hTO : TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  set I := Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n h
    with hI
  have hA := (schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).isA h.1 n
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ =>
      ne_top_of_le_ne_top ((schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).fin n ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hA.1.1 hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hGT := schedGTX_spec Wire.T14Asm7.h13 c r l a
  filter_upwards [hEgood, hGT.2.2, ae_life_pos_of_srecX_notMem Wire.T14Asm7.h13 c r l a I (rootPt r.1),
    ae_schedVerXStop_le_physClockX Wire.T14Asm7.h13 c r l a h.1 h.2 hTO hGT.1 n] with ω hE hGTω hpos hle hlive
  have hgood := (hE hlive.1).1
  have hold : oldSuccess c r l ω := (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).1 hlive.1.1.2
  have hE₀ : I.srecX c r l (rootPt r.1) ω ∈ (Wire.T14Cur.baseWm cw Ω c r l a).E₀ := by
    have h1 := hlive.1.1.1
    rwa [GW2Rd.schedChoiceLinesX_E₀] at h1
  exact hle (hGTω.2 hgood) hgood hold (hpos hold hE₀)

/-- **The top's `hmeanF` at roots `0` and strictly ordered histories, for the stop-capped family** (decision D54):
modulo only RELDET's R1–R4 statements, for every word `cw` of the source's counterflow. -/
theorem hmeanF_root0_stop (hR1 : PrefixLifeStatement.{u}) (hR2 : PrefixContactStatement.{u})
    (hR3 : GW2Nw.PrefixLiveCoverStatement.{u}) (hId : GW2Nw.PrefixIdentStatement.{u})
    (hR4 : GW2Nw.BetaConsStatement.{u}) (cw : Wire.T14Cur.CfWord.{u})
    (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r)) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GW2Rv.GoodRoot c r) → rootPt r.1 = 0 → ∀ (a n : ℕ) (w : WordType) (t : ℝ≥0)
      (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      LocalSets.IsLocalSetMean
        ((Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n h).B t)
        (WholeField.centredField c.h
          (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n h).u₀)
        c.P g →
      ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        stageMeanAtX (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm cw) Ω c r l a n h)
          c r l (rootPt r.1) w t ψ ω (g ω) :=
  GW2Nw.hmeanF_root0 hR1 hR2 hR3 hId hR4 (schedVerXStopFamily Wire.T14Asm7.h13) cw hcw (hVd_stop cw)

/-- **`hmeanF_root0_stop` at GEOM2's canonical counterflow word** (`GW2Nw.cfWordCanon`). -/
theorem hmeanF_root0_stop_canon (hR1 : PrefixLifeStatement.{u}) (hR2 : PrefixContactStatement.{u})
    (hR3 : GW2Nw.PrefixLiveCoverStatement.{u}) (hId : GW2Nw.PrefixIdentStatement.{u})
    (hR4 : GW2Nw.BetaConsStatement.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GW2Rv.GoodRoot c r) → rootPt r.1 = 0 → ∀ (a n : ℕ) (w : WordType) (t : ℝ≥0)
      (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      LocalSets.IsLocalSetMean
        ((Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm GW2Nw.cfWordCanon) Ω c r l
          a n h).B t)
        (WholeField.centredField c.h
          (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm GW2Nw.cfWordCanon) Ω c r l
            a n h).u₀) c.P g →
      ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        stageMeanAtX (Wire.T14Cur.instC (schedVerXStopFamily Wire.T14Asm7.h13)
          (Wire.T14Cur.baseWm GW2Nw.cfWordCanon) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω) :=
  hmeanF_root0_stop hR1 hR2 hR3 hId hR4 GW2Nw.cfWordCanon GW2Nw.isCfWordOf_cfWordCanon

end InteractingSLE.Theorem14.GW2Nx
