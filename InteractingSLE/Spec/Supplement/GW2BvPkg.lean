/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvSel
import InteractingSLE.Spec.Supplement.GW2BuReidx
import InteractingSLE.Spec.Supplement.GW2BoPkg
import InteractingSLE.Spec.Supplement.GW2SdtSlow
import InteractingSLE.Spec.Supplement.GW2SdtCov
import InteractingSLE.Spec.Supplement.GW2SdoNear

/-!
# The re-indexed package (D45 (1): the package SDE's `hwords` consumes)

Packet PROVE-GW2-BUF (round 19). The near slot `(l, n, m, a)` of ROOTX's `pkgX` reads version `m` of candidate `a`.
The near words ask for every candidate at once, eventually in `m`. So the versions are re-indexed per candidate.
The data, fixed as SDE's handoff (round 19) and D45 ask:

* versions: RELDET's death family `GW2Rd.schedVerXDeathFamily h13` (D27, D49), re-indexed by `m ↦ ψ a m + m` with
  `ψ = max (psiCov, monoHull ψx)`:
  * `psiCov` is the cover re-indexing (`GW2Sdo.exists_reindex_eventually_all`): eventually every candidate's slot
    passes the history's clock;
  * `ψx` is any extra re-indexing; the version loss of nearImg chooses it (round 18's `exists_reindex_goodFrom`).
    Every word fact below holds for every `ψx`.
* choices: RELDET's lines on SDE's `GW2Sdt.baseWmS cw` (`pkgCh`; the top's `chL (baseWm cw)`).
* the base package `pkgKb`: BUF's near stops (`nearStopPkgX`) for any exit rules, on a base package whose slow shells
  are SDE's `GW2Sdt.slowShellOf`.
* the near base reader `pkgNb`: GEOM2's base word of the prefix record of the first slot passing the clock.
* the package **`pkgB … k`** = `withNearSB (pkgX h13 ver ch Kb) nearLam pkgNb (kSel k)` (the rightward selection).

Exported:
* `pkgVer`, `pkgCh`, `pkgKb`, `pkgNb`, **`pkgB`**;
* `sameSlots_pkgB`, `slowShell_pkgB`, `slowVar_pkgB`, **`nearStopsX_pkgKb`**;
* the coverage of the re-indexed family: **`hcov_pkgVer`**, and **`ae_eventually_cov_all`** (eventually, every
  candidate's slot passes the clock);
* `pkgVer_V`, `pkgVer_R`, `le_pkgPsi`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

/-! ### The monotone hull of a re-indexing -/

/-- The monotone hull `m ↦ max_{j ≤ m} f j`. -/
def monoHull (f : ℕ → ℕ) (m : ℕ) : ℕ := (Finset.range (m + 1)).sup f

theorem monotone_monoHull (f : ℕ → ℕ) : Monotone (monoHull f) := fun _ _ h =>
  Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ h))

theorem le_monoHull (f : ℕ → ℕ) (m : ℕ) : f m ≤ monoHull f m :=
  Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_self m))

/-- A re-indexing per source setup, root, history and candidate. -/
abbrev PsiFam : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
    List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ

/-- A near base reader per source setup, root and history (SDE's `T14Cur.NearBase`). -/
abbrev NearBaseB : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
    List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord

/-- A candidate selector per buffer index (SDE's `T14Cur.NearSel`). -/
abbrev NearSelB : Type (u + 1) :=
  ℕ → ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
    List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ

/-- Exit rules per source setup, root, history, buffer index and candidate (the argument of `nearStopPkgX`). -/
abbrev ExitFam : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
    List (EntryIdx c.Θ c.Q) → ℕ → ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞

/-- A counterflow word per source setup and root (the word `c'` of GEOM2's word map; the top's `CfWord`). -/
abbrev CfWordB : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω), ScaledRootIdx c.Θ c.Q →
    BoundaryWord

section Cov

variable (h13 : Exist.Theorem13Statement.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))

/-- **The cover events of the death family**: version `k` of candidate `a` passes the history's clock. -/
def covEv (a k : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) <
    (schedVerXDeathFamily h13 Ω c r l a).V k ω}

theorem measurableSet_covEv (hx : 0 ≤ rootPt r.1) (a k : ℕ) : MeasurableSet (covEv h13 c r l a k) := by
  have hclk : Measurable fun ω => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω :=
    RootH29.measurable_forwardCapacity_random (rootPt r.1) c.s
      (measurable_recPair (measurable_gb6Rec_src c) (measurable_schedW c r l a)
        (fun ω => (GW2Sdo.continuous_schedW c r l a ω).1) (fun ω => (GW2Sdo.continuous_schedW c r l a ω).2)
        (RootJ31.historyTime c r l)) measurable_const
  exact measurableSet_lt (ENNReal.measurable_ofReal.comp hclk)
    ((schedVerXDeathFamily h13 Ω c r l a).isA hx k).1.1.2.2.2.2.1

theorem monotone_covEv (a : ℕ) : Monotone (covEv h13 c r l a) := fun k k' hkk' ω hω => by
  have hm : Monotone fun j => (schedVerXDeathFamily h13 Ω c r l a).V j ω :=
    monotone_nat_of_le_succ fun j => (schedVerXDeathFamily h13 Ω c r l a).mono j ω
  exact lt_of_lt_of_le hω (hm hkk')

/-- **The cover re-indexing** (SDE's `exists_reindex_eventually_all` on the cover events; the identity off the
nonnegative roots). -/
def psiCov : ℕ → ℕ → ℕ :=
  if hx : 0 ≤ rootPt r.1 then
    (GW2Sdo.exists_reindex_eventually_all (μ := c.P) (covEv h13 c r l) (measurableSet_covEv h13 c r l hx)
      (monotone_covEv h13 c r l)).choose
  else fun _ m => m

theorem psiCov_mono (a : ℕ) : Monotone (psiCov h13 c r l a) := by
  unfold psiCov
  split_ifs with hx
  · exact (GW2Sdo.exists_reindex_eventually_all (μ := c.P) (covEv h13 c r l) (measurableSet_covEv h13 c r l hx)
      (monotone_covEv h13 c r l)).choose_spec.1 a
  · exact monotone_id

theorem le_psiCov (a m : ℕ) : m ≤ psiCov h13 c r l a m := by
  unfold psiCov
  split_ifs with hx
  · exact (GW2Sdo.exists_reindex_eventually_all (μ := c.P) (covEv h13 c r l) (measurableSet_covEv h13 c r l hx)
      (monotone_covEv h13 c r l)).choose_spec.2.1 a m
  · exact le_rfl

theorem ae_psiCov (hx : 0 ≤ rootPt r.1) :
    ∀ᵐ ω ∂c.P, ∀ᶠ m in atTop, ∀ a, (∃ k, ω ∈ covEv h13 c r l a k) → ω ∈ covEv h13 c r l a (psiCov h13 c r l a m) := by
  simp only [psiCov, hx, ↓reduceDIte]
  exact (GW2Sdo.exists_reindex_eventually_all (μ := c.P) (covEv h13 c r l) (measurableSet_covEv h13 c r l hx)
    (monotone_covEv h13 c r l)).choose_spec.2.2

end Cov

/-! ### The package -/

section Pkg

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u}) (ψx : PsiFam.{u})

/-- **The package's re-indexing**: the cover re-indexing and the monotone hull of the extra one. -/
def pkgPsi (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) : ℕ :=
  max (psiCov h13 c r l a m) (monoHull (ψx Ω c r l a) m)

theorem monotone_pkgPsi (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Monotone (pkgPsi h13 ψx Ω c r l a) :=
  fun _ _ h => max_le_max (psiCov_mono h13 c r l a h) (monotone_monoHull _ h)

theorem le_pkgPsi (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) :
    psiCov h13 c r l a m ≤ pkgPsi h13 ψx Ω c r l a m ∧ ψx Ω c r l a m ≤ pkgPsi h13 ψx Ω c r l a m :=
  ⟨le_max_left _ _, (le_monoHull _ m).trans (le_max_right _ _)⟩

/-- **The package's version family**: RELDET's death family re-indexed by `m ↦ pkgPsi a m + m`. -/
def pkgVer : SchedVerXFamily.{u} :=
  verReindex (schedVerXDeathFamily h13) (fun Ω _ _ c r l a => reindexPlus (pkgPsi h13 ψx Ω c r l a))
    (fun Ω _ _ c r l a => strictMono_reindexPlus (monotone_pkgPsi h13 ψx Ω c r l a))

theorem pkgVer_V (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) :
    (pkgVer h13 ψx Ω c r l a).V m = (schedVerXDeathFamily h13 Ω c r l a).V (pkgPsi h13 ψx Ω c r l a m + m) := rfl

theorem pkgVer_R (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) :
    (pkgVer h13 ψx Ω c r l a).R m = (schedVerXDeathFamily h13 Ω c r l a).R (pkgPsi h13 ψx Ω c r l a m + m) := rfl

/-- **The package's choice family**: RELDET's lines on SDE's base family `baseWmS cw` (the top's `chL (baseWm cw)`). -/
abbrev pkgCh (cw : CfWordB.{u}) : SchedChoiceFamily.{u} := schedChoiceLinesX h12 h13 (GW2Sdt.baseWmS cw)

/-- A base package with SDE's slow shells `slowShellOf h13 ver cw`. -/
def withShellOf (K₀ : PkgFamily.{u}) (ver : SchedVerXFamily.{u}) (cw : CfWordB.{u}) : PkgFamily.{u} :=
  fun Ω _ _ c r => { K₀ Ω c r with slowShell := fun l a ω => GW2Sdt.slowShellOf h13 ver cw Ω c r l a ω }

/-- **The base package**: BUF's near stops for the exit rules `Ex` on the shelled base package. -/
def pkgKb (cw : CfWordB.{u}) (Ex : ExitFam.{u}) (K₀ : PkgFamily.{u}) : PkgFamily.{u} :=
  nearStopPkgX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) Ex (withShellOf h13 K₀ (pkgVer h13 ψx) cw)

open Classical in
/-- **The reference prefix record**: the prefix record of the first slot (of RELDET's death family) passing the
history's clock. -/
def refPre (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) : RecData :=
  if h : ∃ p : ℕ, ω ∈ covEv h13 c r l (Nat.unpair p).1 (Nat.unpair p).2 then
    stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair (Nat.find h)).1)
      (schedGTX h13 c r l (Nat.unpair (Nat.find h)).1)
      ((schedVerXDeathFamily h13 Ω c r l (Nat.unpair (Nat.find h)).1).V (Nat.unpair (Nat.find h)).2)
      (RootJ31.historyTime c r l)
      ((schedVerXDeathFamily h13 Ω c r l (Nat.unpair (Nat.find h)).1).R (Nat.unpair (Nat.find h)).2) ω
  else default

/-- **The near base reader**: GEOM2's base word of the reference prefix record. -/
def pkgNb (cw : CfWordB.{u}) : NearBaseB.{u} := fun Ω _ _ c r l ω =>
  GW2Wm.baseWordX c.κ (cw Ω c r) (rootPt r.1) c.s (RootJ31.historyProgram c r l) ((entryList l).length + 1)
    (GW2Ru.length_historyProgram c r l) (augRec (stageEncRec c r l) (fun ω' => refPre h13 Ω c r l ω') ω)

/-- **The re-indexed package at buffer index `k`** (D45 (1)): ROOTX's `pkgX` on the re-indexed death family, the
lines on `baseWmS cw`, BUF's near stops and SDE's slow shells, with the rightward selection on `pkgNb`. -/
def pkgB (cw : CfWordB.{u}) (Ex : ExitFam.{u}) (K₀ : PkgFamily.{u}) (kSel : NearSelB.{u}) (k : ℕ) :
    VPkgXFamily.{u} :=
  withNearSB (pkgX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) (pkgKb h13 h12 ψx cw Ex K₀)) nearLam (pkgNb h13 cw)
    (kSel k)

variable (cw : CfWordB.{u}) (Ex : ExitFam.{u}) (K₀ : PkgFamily.{u}) (kSel : NearSelB.{u})

/-- **The package has the slots of ROOTX's package** (the `hs` of the top). -/
theorem sameSlots_pkgB (k : ℕ) :
    SameSlots (pkgX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) (pkgKb h13 h12 ψx cw Ex K₀))
      (pkgB h13 h12 ψx cw Ex K₀ kSel k) :=
  sameSlots_withNearSB _ _ _ _

/-- The package's slow shells are SDE's. -/
theorem slowShell_pkgB (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (pkgB h13 h12 ψx cw Ex K₀ kSel k Ω c r).slowShell l a ω =
      GW2Sdt.slowShellOf h13 (pkgVer h13 ψx) cw Ω c r l a ω := rfl

/-- The package's slow variables are ROOTX's slow slots. -/
theorem slowVar_pkgB (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) :
    (pkgB h13 h12 ψx cw Ex K₀ kSel k Ω c r).slowVar l a n =
      slowSlotX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) Ω c r l a n := rfl

/-- **The near stops are good** (the `hnear` of the top), given the owners' instance inputs and measurable exit path
rules. -/
theorem nearStopsX_pkgKb (hI : InstInputsX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw))
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ),
      Supp8.GB6.HullId.IsPathRule (Ex Ω c r l n a) ∧ Measurable (Ex Ω c r l n a)) :
    NearStopsX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) (pkgKb h13 h12 ψx cw Ex K₀) :=
  nearStopsX_nearStopPkgX hI hE _

/-- **The coverage of the re-indexed family** (SDE's `hcov` premise): its stops eventually pass the history's
clock on J32's alive events (`GW2Sdt.hcov_death` and `GW2Sdt.eventually_lt_reindex`). -/
theorem hcov_pkgVer : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r →
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      (RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) <
        (pkgVer h13 ψx Ω c r l a).V n ω := by
  intro Ω _ _ c r l a hg
  filter_upwards [GW2Sdt.hcov_death h13 Ω c r l a hg] with ω h halive hcf hTc
  exact GW2Sdt.eventually_lt_reindex (fun n => Nat.le_add_left n _) (h halive hcf hTc)

/-- **Eventually every candidate's slot passes the clock** (the cover re-indexing), wherever every candidate's
family eventually passes it. -/
theorem ae_eventually_cov_all (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) :
    ∀ᵐ ω ∂c.P, ∀ᶠ m in atTop, ∀ a, (∃ k, ω ∈ covEv h13 c r l a k) →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) <
        (pkgVer h13 ψx Ω c r l a).V m ω := by
  filter_upwards [ae_psiCov h13 c r l hx] with ω hω
  filter_upwards [hω] with m hm a ha
  have h1 := hm a ha
  have hle : psiCov h13 c r l a m ≤ pkgPsi h13 ψx Ω c r l a m + m :=
    (le_pkgPsi h13 ψx Ω c r l a m).1.trans (Nat.le_add_right _ _)
  exact monotone_covEv h13 c r l a hle h1

end Pkg

end InteractingSLE.Theorem14.GW2Bh
