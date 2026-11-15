/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjCertA
import InteractingSLE.Spec.Supplement.GW2SgDec

/-!
# Good samples: the almost sure facts behind the window certificates (decision D33)

PROVE-GW2-ROOTX round 9. **`GoodSample`** bundles, at one sample, the facts the window certificates use for EVERY
history, candidate and version at once; **`ae_goodSample`**: almost every sample is good (countable intersections).

* `life`: D42 at alive histories (`ae_alive_drop_notMem_launchBadRec`);
* `cons`: the explored drivers of a history and of the passed test's candidate agree (`GW2Ru.ae_cons_schedW_eq`);
* `good`, `gt`: alive histories are good and before every candidate's contact (`GW2Ru.ae_alive_goodEvent`); the good
  sets are the good event (`schedGTX_spec`);
* `vat`, `rho`, `exh`: the versions of `ver` are versions at the sample, read their path rules, and exhaust the live
  samples' capacity;
* `cap`, `read`, `pair`: J32's capacity reader is the clock, its driver reader the versions (`ae_rootCapAt_eq_clockX`,
  `ae_j32Read_eq_versionX`), and the live buffer is before the contact (`GW2Rz.ae_exactPair_rootX`);
* `safe`: the slow stage variables never visit their avoided sets nor return (`ae_slowVarG_noBad_noReturn`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rq GW2Rv GW2Rz GW2Sde GW2Sdh GW2Sdx

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **A good sample** for the window certificates. -/
structure GoodSample (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (h : GoodRoot c r) (ω : Ω) : Prop where
  life : ∀ l : List (EntryIdx c.Θ c.Q),
    ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
    ∀ (k : ℕ) (x : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q)), l.drop k = x :: l' →
      ∃ a : ℕ, RootJ31.candidateAngle c r a = x.1 ∧ ω ∈ (RootJ32.experiment c r).data.tests l' a x.2 ∧
        ∀ y : Ω → RecData, GW2Rd.augRec (GW2Rd.stageEncRec c r l') y ω ∉ GW2Rd.launchBadRec c r l' a
  cons : ∀ (l : List (EntryIdx c.Θ c.Q)) (a₀ : ℕ) (q : c.Q) (a : ℕ),
    ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
    ω ∈ (RootJ32.experiment c r).data.tests l a₀ q → ∀ t ≤ (q : ℝ≥0),
      GW2Rd.schedW c r ((RootJ31.candidateAngle c r a₀, q) :: l) a t ω = GW2Rd.schedW c r l a₀ t ω
  good : ∀ l : List (EntryIdx c.Θ c.Q),
    ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
    cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s ∧
      ∀ a : ℕ, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω
  gt : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
    (ω ∈ schedGTX h13 c r l a ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s)
  vat : ∀ (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ), cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
    VersionAtX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (GW2Rd.schedTr c r l a) c.α
      ((ver Ω c r l a).R n) ((ver Ω c r l a).V n) ω
  rho : ∀ (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ),
    (ver Ω c r l a).V n ω = ((ver Ω c r l a).isA h.1 n).1.2.choose
      (cfRec c.s c.W c.ζ ω, fun u => (ver Ω c r l a).R n u ω)
  exh : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (u : ℝ≥0), u < GW2Sdg.rootGain c r l a ω →
    ∀ᶠ n in atTop, ((GW2Sdg.rootHistCap c r l a ω + u : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l a).V n ω
  cap : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), 0 < (RootJ31.sourceSample c r l a ω).1 →
    ∀ t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω,
      GW2Sdg.rootCapAt c r l a t ω = clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) t ω
  read : ∀ (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ), 0 < (RootJ31.sourceSample c r l a ω).1 → ∀ c' : ℝ≥0,
    (c' : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s
      (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω) (GW2Bf.exactPair c r l a ω) →
    (c' : ℝ≥0∞) < (ver Ω c r l a).V n ω → GW2Bf.j32Read c r l a c' ω = (ver Ω c r l a).R n c' ω
  pair : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), 0 < (RootJ31.sourceSample c r l a ω).1 →
    ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω
  safe : ∀ (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ), HistOrdered c r l →
    (slowVarG h13 ver ch c r l a h.1 n).record ω ∈ (slowVarG h13 ver ch c r l a h.1 n).E →
      ¬ BadQ c.κ 0 ((slowVarG h13 ver ch c r l a h.1 n).β ((slowVarG h13 ver ch c r l a h.1 n).record ω))
          (fun q => LP.traceAt q (fun u => (slowVarG h13 ver ch c r l a h.1 n).R u ω))
          ((slowVarG h13 ver ch c r l a h.1 n).V ω) ∧
        ¬ ReturnQ (fun q => LP.traceAt q (fun u => (slowVarG h13 ver ch c r l a h.1 n).R u ω))
          ((slowVarG h13 ver ch c r l a h.1 n).V ω)

/-- **Almost every sample is good.** -/
theorem ae_goodSample (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}}
    (hI : InstInputsX h13 ver ch) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (h : GoodRoot c r) :
    ∀ᵐ ω ∂c.P, GoodSample h13 ver ch c r h ω := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hgt : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      (ω ∈ schedGTX h13 c r l a ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s) :=
    ae_all_iff.2 fun l => ae_all_iff.2 fun a => (schedGTX_spec h13 c r l a).2.2
  have hver : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ),
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      VersionAtX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (GW2Rd.schedTr c r l a) c.α
        ((ver Ω c r l a).R n) ((ver Ω c r l a).V n) ω :=
    ae_all_iff.2 fun l => ae_all_iff.2 fun a => ae_all_iff.2 fun n =>
      GW2Ru.versionAtX_of_isRelVersionX ((ver Ω c r l a).isA h.1 n).1.1
  have hrho : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ),
      (ver Ω c r l a).V n ω = ((ver Ω c r l a).isA h.1 n).1.2.choose
        (cfRec c.s c.W c.ζ ω, fun u => (ver Ω c r l a).R n u ω) :=
    ae_all_iff.2 fun l => ae_all_iff.2 fun a => ae_all_iff.2 fun n =>
      ((ver Ω c r l a).isA h.1 n).1.2.choose_spec.2.2
  have hexh : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (u : ℝ≥0), u < GW2Sdg.rootGain c r l a ω →
      ∀ᶠ n in atTop, ((GW2Sdg.rootHistCap c r l a ω + u : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l a).V n ω :=
    ae_all_iff.2 fun l => ae_all_iff.2 fun a => (ver Ω c r l a).exhausts h.1
  have hcap : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), 0 < (RootJ31.sourceSample c r l a ω).1 →
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω,
        GW2Sdg.rootCapAt c r l a t ω = clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) t ω :=
    ae_all_iff.2 fun l => ae_all_iff.2 fun a => ae_rootCapAt_eq_clockX h13 c r l a
  have hread : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ), 0 < (RootJ31.sourceSample c r l a ω).1 →
      ∀ c' : ℝ≥0, (c' : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s
        (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω) (GW2Bf.exactPair c r l a ω) →
      (c' : ℝ≥0∞) < (ver Ω c r l a).V n ω → GW2Bf.j32Read c r l a c' ω = (ver Ω c r l a).R n c' ω :=
    ae_all_iff.2 fun l => ae_all_iff.2 fun a => ae_all_iff.2 fun n =>
      ae_j32Read_eq_versionX h13 c r l a h.1 ((ver Ω c r l a).isA h.1 n).1.1
  have hpair : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), 0 < (RootJ31.sourceSample c r l a ω).1 →
      ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω : ℝ≥0) : ℝ≥0∞) <
        contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω :=
    ae_all_iff.2 fun l => ae_all_iff.2 fun a =>
      (ae_exactPair_rootX h13 c r l a).mono fun _ hω hl => (hω hl).2.1
  filter_upwards [ae_alive_drop_notMem_launchBadRec h13 c r, GW2Ru.ae_cons_schedW_eq h13 c r,
    GW2Ru.ae_alive_goodEvent h13 c r, hgt, hver, hrho, hexh, hcap, hread, hpair,
    ae_slowVarG_noBad_noReturn h12p h12p₀ h13₀ hI c r h] with ω h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end InteractingSLE.Theorem14.GW2Rj
