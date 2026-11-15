/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RlNear
import InteractingSLE.Spec.Supplement.GW2SdsGap
import InteractingSLE.Spec.Supplement.GW2SdqGap

/-!
# `hwords` closed (decision D58, item 1)

PROVE-GW2-ROOTX round 11. The data of the top's word package:
* the version family **`rlVer ψx`** = RELDET's death family `schedVerXDeathFamily` re-indexed uniformly
  (`GW2Rl.verU`), for any extra re-indexing `ψx` (BUF's kernel-loss re-indexing for nearImg);
* the counterflow word `rlCw` = SDE's `cfWordSrc`;
* the near base **`rlNb ψx`** = `GW2Rl.refNb` (GEOM2's base word of the first version beyond the clock);
* the gap family `GW2Sdq.gapFam`; any base packages `Kb` and candidate selectors `kSel`.

Then:
* **`nearSlotWords_rl`**: SDE's `hword` (`Wire.T14Rk.NearSlotWords`) for these data;
* **`heq_rl`**: the near base's identity;
* **`vwordsX_rl`**: `hwords` for `pkgRj (rlVer ψx) rlCw Kb (rlNb ψx) kSel`, with NO open input (only the top's own
  instance binders `hmeanF`, `hno`, which define the instance inputs);
* **`Wire.theorem14Statement_assembled7Wm_rlc`**: the current top with `V := pkgRj …`, `hs`, `C`, `hshell`,
  `hwords`, `hgap`, `hpos` discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Wire.T14Rl

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj T14Rk

/-- The top's counterflow word: SDE's source counterflow word. -/
abbrev rlCw : CfWord.{u} := fun _ _ _ c _ => GW2Sds.cfWordSrc c

/-- **The top's version family**: RELDET's death family, re-indexed uniformly. -/
abbrev rlVer (ψx : GW2Rl.PsiFamR.{u}) : GW2Rv.SchedVerXFamily.{u} :=
  GW2Rl.verU (GW2Rd.schedVerXDeathFamily T14Asm7.h13) ψx

/-- **The top's near base**: the base word of the first version beyond the clock. -/
abbrev rlNb (ψx : GW2Rl.PsiFamR.{u}) : NearBase.{u} := GW2Rl.refNb T14Asm7.h13 (rlVer ψx) rlCw

theorem verCovers_death : VerCovers (GW2Rd.schedVerXDeathFamily T14Asm7.h13) :=
  GW2Sdt.hcov_death T14Asm7.h13

/-- **The near slots' words** for the top's data. -/
theorem nearSlotWords_rl (ψx : GW2Rl.PsiFamR.{u}) (Kb : ℕ → GW2Sde.PkgFamily.{u}) (k : ℕ) :
    NearSlotWords GW2Sdq.gapFam (rlVer ψx) rlCw Kb (rlNb ψx) k := by
  intro Ω _ _ c r l
  filter_upwards [GW2Rl.ae_nearSlotWords (h13 := T14Asm7.h13) (rlVer ψx) rlCw (hβ_baseWm rlCw) (hE₀eq_baseWm rlCw)
    (GW2Rl.unifCover_verU T14Asm7.h13 verCovers_death ψx) (Kb k) GW2Sdq.gapFam Ω c r l] with ω hω halive n
  filter_upwards [hω halive n] with m hm i j
  obtain ⟨h1, h2⟩ := hm (Nat.pair i j)
  exact ⟨h1, by rw [h2, GW2Sdy.candidateAngle_pair]⟩

/-- **The near base's identity** (the `heq` of `vwordsX_pkgRj_junction`) for the top's data. -/
theorem heq_rl (ψx : GW2Rl.PsiFamR.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ aliveS GW2Sdq.gapFam Ω c r l → ∃ a n : ℕ,
        ENNReal.ofReal (GW2Rz.clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
          (rlVer ψx Ω c r l a).V n ω ∧
        rlNb ψx Ω c r l ω = GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          (GW2Rd.augRec (GW2Rd.stageEncRec c r l) (GW2Rz.stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
            (GW2Rz.schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((rlVer ψx Ω c r l a).V n)
            (RootJ31.historyTime c r l) ((rlVer ψx Ω c r l a).R n)) ω) :=
  fun Ω _ _ c r l hg => GW2Rl.heq_refNb T14Asm7.h13 (rlVer ψx) GW2Sdq.gapFam rlCw
    (GW2Rl.verCovers_verU verCovers_death ψx) Ω c r l hg

/-- **`hwords` for the top's package, closed.** -/
theorem vwordsX_rl (ψx : GW2Rl.PsiFamR.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC (rlVer ψx) (baseWm rlCw) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC (rlVer ψx) (baseWm rlCw) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC (rlVer ψx) (baseWm rlCw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC (rlVer ψx) (baseWm rlCw) Ω c r l a n h) c r l (rootPt r.1))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (kSel : NearSel.{u}) :
    ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (pkgRj (rlVer ψx) rlCw Kb (rlNb ψx) kSel k)
      GW2Sdh.nearLam :=
  vwordsX_pkgRj_junction (rlVer ψx) hmeanF hno Kb (rlNb ψx) kSel (GW2Rl.verCovers_verU verCovers_death ψx)
    (nearSlotWords_rl ψx Kb) (heq_rl ψx)

end InteractingSLE.Wire.T14Rl

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj T14Rk
  T14Rl

/-- **Theorem 1.4, the current top with the word package closed**: SDE's junction-gap cover, the source counterflow
word, the uniformly re-indexed death family (any `ψx`), the reference near base, ROOTX's shells; `hgap`, `hpos`,
`hs`, `C`, `hshell` and `hwords` discharged. -/
theorem theorem14Statement_assembled7Wm_rlc (ψx : GW2Rl.PsiFamR.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC (rlVer ψx) (baseWm rlCw) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC (rlVer ψx) (baseWm rlCw) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC (rlVer ψx) (baseWm rlCw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC (rlVer ψx) (baseWm rlCw) Ω c r l a n h) c r l (rootPt r.1))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (kSel : NearSel.{u})
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 (rlVer ψx) (chL (baseWm rlCw)) (Kb k))
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((pkgRj (rlVer ψx) rlCw Kb (rlNb ψx) kSel k).at 0) GW2Sdh.nearLam Ω c r l
        ((k : ℝ≥0∞) + 1)⁻¹ (aliveS GW2Sdq.gapFam Ω c r l))
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_assembled7Wm_rj GW2Sdq.gapFam GW2Sdq.measurable_gapFam
    (fun _ _ _ c x => GW2Sds.ae_gapFam_pos c x) (rlVer ψx) rlCw hmeanF hno Kb (rlNb ψx) kSel hnear
    (vwordsX_rl ψx hmeanF hno Kb kSel) hnearImg hTL

end InteractingSLE.Wire
