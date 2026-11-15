/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NzDth
import InteractingSLE.Spec.Supplement.GW2PuDthF
import InteractingSLE.Spec.Supplement.GW2RpPkg
import InteractingSLE.Spec.Wire.T14GdBase

/-!
# BUF's death threshold at the top's family, every admissible root (D72, D75)

Packet PROVE-GW2-NOTHR (round 10). STAGEMEAN's positive-lifetime death clause is landed at every admissible root for
the stop-capped family and GEOM2's word map (`GW2Pu.deathExportFamilyDP_stop`). The top's family is a strictly
increasing re-indexing of the stop family (ROOTX's `T14Rp.oneVerS ψx`, ASSEMBLE7's `GW2Kt.stopPkgVer ψx`, D68/D75) on
ASSEMBLE7's guarded base `T14Gd.guardBase (baseWm cw)`:

* `stageDeathExportXDP_comp`: the death clause of an instance passes to every sub-family of its versions (only the
  agreement clause `∀ n q, q < Vf n → Rf n q = Wd q` reads the family);
* **`deathExportFamilyDP_reindex`**, **`deathExportFamilyDP_reindex_guard`**: the clause at a re-indexed stop family,
  on the word-map base and on its guarded base (the re-indexed instance is the stop instance at the re-indexed
  version, `GW2Bh.instX_reindex`; on guarded histories the guarded base is the base, `T14Gd.chL_guardBase_of_guard`);
* **`deathThrX_stopReindex`**, **`deathThrX_stopReindex_guard`**: `GW2Ny.DeathThrXStatementS` (BUF's death threshold,
  admissible roots, strictly ordered histories) for every strictly increasing re-indexing of the stop family, with NO
  open input (`GW2Nz.deathThrX_of_exportDP_fin`; `hD27`/`hcaps` of the stop family pass to re-indexings);
* **`deathThrX_oneVerS`** (`T14Rp.oneVerS ψx`, `chL (guardBase (baseWm cwSrc))`), **`deathThrX_stopPkgVer`**
  (`GW2Kt.stopPkgVer ψx`, same base): the forms BUF consumes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Ow

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  GW2Sde GW2Sdh Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop MartChar.RealFlow GW2Nu GW2Nv
  Sec5.Prop513Schedule Sec5.CrossCond.StagedRepLater

section Clause

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The death clause passes to every sub-family of the versions.** -/
theorem stageDeathExportXDP_comp {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}
    {a : ℕ} {I : StageInst Ω} {Rf : ℕ → ℝ≥0 → Ω → ℝ} {Vf : ℕ → Ω → ℝ≥0∞} {x₀ : ℝ} (φ : ℕ → ℕ)
    (hexp : GW2Pv.StageDeathExportXDP c r l a I Rf Vf x₀) :
    GW2Pv.StageDeathExportXDP c r l a I (fun n => Rf (φ n)) (fun n => Vf (φ n)) x₀ := by
  filter_upwards [hexp] with ω₀ hω hdat cL θ hl
  obtain ⟨b, J, hh, Wα, ζα, α, b', J', h', cw, W, ζ, γ, t₀, lam, F, h1, h2, h3, h4, h5, h6, h7, h8, h9, hlast⟩ :=
    hω hdat cL θ hl
  refine ⟨b, J, hh, Wα, ζα, α, b', J', h', cw, W, ζ, γ, t₀, lam, F, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
  filter_upwards [hlast] with ξ hξ hGT hold hSV hd hpos
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hξ hGT hold hSV hd hpos
  refine ⟨a1, a2, a3, a4, a5, fun hp => ?_⟩
  obtain ⟨b1, b2, Wd, hWc, hW0, hag, hhull⟩ := a6 hp
  exact ⟨b1, b2, Wd, hWc, hW0, fun n q hq => hag (φ n) q hq, hhull⟩

end Clause

section Family

variable (cw : Wire.T14Cur.CfWord.{u})
  (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r))
  (φ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ)
  (hφ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), StrictMono (φ Ω c r l a))

include hcw in
/-- **The death clause at a re-indexed stop family, GEOM2's word-map base.** -/
theorem deathExportFamilyDP_reindex :
    GW2Nz.DeathExportFamilyDP Wire.T14Asm7.h13
      (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ)
      (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw)) := by
  intro Ω _ _ c r l hord h hroot a j
  rw [GW2Bh.instX_reindex]
  exact stageDeathExportXDP_comp (φ Ω c r l a)
    (GW2Pu.deathExportFamilyDP_stop cw hcw Ω c r l hord h hroot a (φ Ω c r l a j))

include hcw in
/-- **The death clause at a re-indexed stop family, ASSEMBLE7's guarded base.** -/
theorem deathExportFamilyDP_reindex_guard :
    GW2Nz.DeathExportFamilyDP Wire.T14Asm7.h13
      (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw))) := by
  intro Ω _ _ c r l hord h hroot a j
  have hg : Wire.T14Gd.Guard c r l := ⟨hord, hroot⟩
  have e := Wire.T14Gd.instC_guardBase_of_guard (Wire.T14Cur.baseWm cw) a
    (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ) j h hg
  change GW2Pv.StageDeathExportXDP c r l a
    (Wire.T14Cur.instC (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ)
      (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw)) Ω c r l a j h) _ _ _
  rw [e]
  exact deathExportFamilyDP_reindex cw hcw φ hφ Ω c r l hord h hroot a j

/-- `hD27` passes to a re-indexing of the stop family. -/
theorem hD27_reindex :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        deathClockX c r l a ω < ⊤ → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
          (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ Ω c r l a).V n ω := by
  intro Ω _ _ c r l a h hord
  filter_upwards [GW2Nx.hD27_stop Wire.T14Asm7.h13 Ω c r l a h hord] with ω hω hgood hold hd t ht htl
  exact GW2Sdt.eventually_lt_reindex (fun n => (hφ Ω c r l a).id_le n) (hω hgood hold hd t ht htl)

/-- `hcaps` passes to a re-indexing of the stop family. -/
theorem hcaps_reindex :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        0 < candLife c r l a ω →
        ∀ n, (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ Ω c r l a).V n ω <
          deathClockX c r l a ω := by
  intro Ω _ _ c r l a h hord
  filter_upwards [GW2Nx.hcaps_stop Wire.T14Asm7.h13 Ω c r l a h hord] with ω hω hgood hold hpos n
  exact hω hgood hold hpos (φ Ω c r l a n)

/-- `hword` for the word-map base read through RELDET's lines choice. -/
theorem hword_chL :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β ∧
        (range fun y => wordType c.κ ((Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β y)).Countable ∧
        ∀ y, ((Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β y).IsSorted := by
  intro Ω _ _ c r l hTO h a
  have hβ := Wire.T14Cur.hword_baseWm cw Ω c r l hTO h a
  rw [← GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a] at hβ
  exact hβ

/-- `hword` for the guarded word-map base read through RELDET's lines choice. -/
theorem hword_chL_guard :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw)) Ω c r l a).β ∧
        (range fun y => wordType c.κ
          ((Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw)) Ω c r l a).β y)).Countable ∧
        ∀ y, ((Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw)) Ω c r l a).β y).IsSorted := by
  intro Ω _ _ c r l hTO h a
  have hβ := Wire.T14Gd.hword_guardBase cw Ω c r l hTO h a
  rw [← GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13
    (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw)) c r l a] at hβ
  exact hβ

include hcw in
/-- **BUF's death threshold at every re-indexing of the stop family, GEOM2's word-map base**, every admissible root,
strictly ordered histories, with no open input. -/
theorem deathThrX_stopReindex :
    GW2Ny.DeathThrXStatementS Wire.T14Asm7.h13
      (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ)
      (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw)) :=
  GW2Nz.deathThrX_of_exportDP_fin Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ _ _
    (hword_chL cw) (hD27_reindex φ hφ) (hcaps_reindex φ hφ) (deathExportFamilyDP_reindex cw hcw φ hφ)

include hcw in
/-- **BUF's death threshold at every re-indexing of the stop family, ASSEMBLE7's guarded base**, every admissible
root, strictly ordered histories, with no open input. -/
theorem deathThrX_stopReindex_guard :
    GW2Ny.DeathThrXStatementS Wire.T14Asm7.h13
      (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm cw))) :=
  GW2Nz.deathThrX_of_exportDP_fin Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ _ _
    (hword_chL_guard cw) (hD27_reindex φ hφ) (hcaps_reindex φ hφ) (deathExportFamilyDP_reindex_guard cw hcw φ hφ)

end Family

/-- **BUF's death threshold at the top's family (D68/D75)**: ROOTX's `T14Rp.oneVerS ψx` on ASSEMBLE7's guarded base
at BUF's word `cwSrc`, every admissible root, strictly ordered histories, with NO open input. -/
theorem deathThrX_oneVerS (ψx : GW2Bh.PsiFam.{u}) :
    GW2Ny.DeathThrXStatementS Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) := by
  unfold Wire.T14Rp.oneVerS GW2Rl.verU
  exact deathThrX_stopReindex_guard GW2Bh.cwSrc GW2Kt.isCfWordOf_cwSrc _ _

/-- **BUF's death threshold at ASSEMBLE7's `GW2Kt.stopPkgVer ψx`** on the guarded base at `cwSrc`, every admissible
root, strictly ordered histories, with NO open input. -/
theorem deathThrX_stopPkgVer (ψx : GW2Bh.PsiFam.{u}) :
    GW2Ny.DeathThrXStatementS Wire.T14Asm7.h13 (GW2Kt.stopPkgVer ψx)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) := by
  unfold GW2Kt.stopPkgVer
  exact deathThrX_stopReindex_guard GW2Bh.cwSrc GW2Kt.isCfWordOf_cwSrc _ _

end InteractingSLE.Theorem14.GW2Ow
