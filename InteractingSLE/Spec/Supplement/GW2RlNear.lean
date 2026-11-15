/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RkTop
import InteractingSLE.Spec.Supplement.GW2SdoReidx
import InteractingSLE.Spec.Supplement.GW2BuReidx
import InteractingSLE.Spec.Supplement.GW2SdyFam
import InteractingSLE.Spec.Supplement.GW2SdtCov

/-!
# The near slots' words for a uniformly covering version family (decision D58, item 1)

PROVE-GW2-ROOTX round 11. SDE's `hword` (`Wire.T14Rk.NearSlotWords`) asks, at every alive history and every `n`,
eventually in `m`, that EVERY candidate's near slot `(l, n, m, a)` of ROOTX's package (`pkgX`, version `m` of
candidate `a`) has its record in its record event and reads `upW (θ_a χ) (nb ω)`. Two inputs make it hold:

* a version family that eventually passes the history clock **uniformly in the candidates** (`UnifCover`);
* a near base reader equal to GEOM2's base word of SOME version beyond the clock (all candidates' prefix records
  beyond the clock agree, SDE's `GW2Sdo.ae_stgPreRecX_sched_eq`).

Here:
* **`refPreV`**, **`refNb`**: the prefix record of the first (candidate, version) of `ver` passing the clock, and
  its base word (the near base);
* **`heq_refNb`**: `refNb` is such a base word (the `heq` of `vwordsX_pkgRj_junction`), for any covering family;
* **`ae_nearSlotWords`**: the near slots' words, for any choice family with GEOM2's word map and D42's `E₀`;
* `monoHull`, `covEvV`, `psiU` (SDE's `exists_reindex_eventually_all` on the cover events), **`verU ver ψx`** (the
  family re-indexed by `m ↦ max (psiU a m, monoHull ψx a m) + m`, any extra re-indexing `ψx`), **`unifCover_verU`**,
  **`verCovers_verU`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rl

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

/-! ### The reference near base -/

section Ref

variable (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})

open Classical in
/-- **The reference prefix record**: the prefix record of the first pair (candidate, version) of `ver` whose stop
passes the history's clock. -/
def refPreV (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) : RecData :=
  if h : ∃ p : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair p).1)
      (RootJ31.historyTime c r l) ω) < (ver Ω c r l (Nat.unpair p).1).V (Nat.unpair p).2 ω then
    stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair (Nat.find h)).1)
      (schedGTX h13 c r l (Nat.unpair (Nat.find h)).1)
      ((ver Ω c r l (Nat.unpair (Nat.find h)).1).V (Nat.unpair (Nat.find h)).2) (RootJ31.historyTime c r l)
      ((ver Ω c r l (Nat.unpair (Nat.find h)).1).R (Nat.unpair (Nat.find h)).2) ω
  else default

/-- **The reference near base**: GEOM2's base word of the reference prefix record. -/
def refNb (cw : GW2Rj.CfWordFam.{u}) : Wire.T14Cur.NearBase.{u} := fun Ω _ _ c r l ω =>
  GW2Wm.baseWordX c.κ (cw Ω c r) (rootPt r.1) c.s (RootJ31.historyProgram c r l) ((entryList l).length + 1)
    (GW2Ru.length_historyProgram c r l) (augRec (stageEncRec c r l) (fun ω' => refPreV h13 ver Ω c r l ω') ω)

theorem refNb_eq {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (cw : GW2Rj.CfWordFam.{u})
    {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {ω : Ω}
    (h : ∃ p : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair p).1)
      (RootJ31.historyTime c r l) ω) < (ver Ω c r l (Nat.unpair p).1).V (Nat.unpair p).2 ω) :
    refNb h13 ver cw Ω c r l ω = GW2Wm.baseWordX c.κ (cw Ω c r) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
      ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
      (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair (Nat.find h)).1)
        (schedGTX h13 c r l (Nat.unpair (Nat.find h)).1)
        ((ver Ω c r l (Nat.unpair (Nat.find h)).1).V (Nat.unpair (Nat.find h)).2) (RootJ31.historyTime c r l)
        ((ver Ω c r l (Nat.unpair (Nat.find h)).1).R (Nat.unpair (Nat.find h)).2)) ω) := by
  unfold refNb
  congr 1
  simp only [augRec, refPreV, h, ↓reduceDIte]

/-- **The reference near base is GEOM2's base word of a version beyond the clock** (the `heq` of
`Wire.T14Rk.vwordsX_pkgRj_junction`), for any version family covering the clock. -/
theorem heq_refNb (gap : RootCv.GapFamily.{u}) (cw : GW2Rj.CfWordFam.{u}) (hcov : Wire.T14Rk.VerCovers ver)
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (hg : GoodRoot c r) :
    ∀ᵐ ω ∂c.P, ω ∈ Wire.T14Cur.aliveS gap Ω c r l → ∃ a n : ℕ,
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) <
        (ver Ω c r l a).V n ω ∧
      refNb h13 ver cw Ω c r l ω = GW2Wm.baseWordX c.κ (cw Ω c r) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
        ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
        (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver Ω c r l a).V n) (RootJ31.historyTime c r l) ((ver Ω c r l a).R n)) ω) := by
  filter_upwards [hcov Ω c r l 0 hg, GW2Ru.ae_alive_goodEvent_scaled h13 gap c r] with ω hcovω hgood halive
  obtain ⟨hcf, hcon⟩ := hgood l halive
  obtain ⟨k, hk⟩ := (hcovω (GW2Sdz.alive_scaled_subset gap Ω c r l halive) hcf (hcon 0)).exists
  have h : ∃ p : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair p).1)
      (RootJ31.historyTime c r l) ω) < (ver Ω c r l (Nat.unpair p).1).V (Nat.unpair p).2 ω :=
    ⟨Nat.pair 0 k, by rw [Nat.unpair_pair]; exact hk⟩
  exact ⟨(Nat.unpair (Nat.find h)).1, (Nat.unpair (Nat.find h)).2, Nat.find_spec h, refNb_eq h13 ver cw h⟩

end Ref

/-! ### The near slots' words -/

/-- **Uniform cover**: on the alive events, eventually in `m`, version `m` of EVERY candidate passes the clock. -/
abbrev UnifCover (ver : SchedVerXFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GoodRoot c r →
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ∀ᶠ m in atTop, ∀ a : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
        (RootJ31.historyTime c r l) ω) < (ver Ω c r l a).V m ω

variable {h13 : Exist.Theorem13Statement.{u}}

/-- At a good root the near slot is the root-`x` instance of version `m` with the package's near stop. -/
theorem pkgX_nearVar_eq {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}} (K : PkgFamily.{u})
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hg : GoodRoot c r) (l : List (EntryIdx c.Θ c.Q)) (n m a : ℕ) :
    (pkgX h13 ver ch K Ω c r).nearVar l n m a =
      (instX h13 ver ch Ω c r l a m hg.1).varX c r l (rootPt r.1) ((K Ω c r).nearStop l n m a) := by
  change nearSlotX h13 ver ch K Ω c r l n m a = _
  unfold nearSlotX
  simp only [hg, ↓reduceDIte]

/-- **The near slots' words** of ROOTX's package for a uniformly covering version family and the reference near
base (any choice family with GEOM2's word map and D42's `E₀`, any base package). -/
theorem ae_nearSlotWords (ver : SchedVerXFamily.{u}) {ch : SchedChoiceFamily.{u}} (cw : GW2Rj.CfWordFam.{u})
    (hβ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = GW2Wm.schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s
        (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
        (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    (hU : UnifCover ver) (K : PkgFamily.{u}) (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω ∂c.P, ω ∈ Wire.T14Cur.aliveS gap Ω c r l → ∀ n : ℕ, ∀ᶠ m in atTop, ∀ a : ℕ,
      ((pkgX h13 ver ch K Ω c r).nearVar l n m a).record ω ∈ ((pkgX h13 ver ch K Ω c r).nearVar l n m a).E ∧
      ((pkgX h13 ver ch K Ω c r).nearVar l n m a).β (((pkgX h13 ver ch K Ω c r).nearVar l n m a).record ω) =
        GW2Rd.upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ) (refNb h13 ver cw Ω c r l ω) := by
  classical
  by_cases hg : GoodRoot c r
  swap
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hω halive
    exact absurd (hω (GW2Sdz.alive_scaled_subset gap Ω c r l halive)) hg
  obtain ⟨hx, hs⟩ := hg
  have hpair : ∀ᵐ ω ∂c.P, ∀ p q : ℕ × ℕ, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      (((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l p.1) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1) (RootJ31.historyTime c r l) ω) <
          (ver Ω c r l p.1).V p.2 ω) →
      (((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l q.1) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l q.1) (RootJ31.historyTime c r l) ω) <
          (ver Ω c r l q.1).V q.2 ω) →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1) (schedGTX h13 c r l p.1) ((ver Ω c r l p.1).V p.2)
          (RootJ31.historyTime c r l) ((ver Ω c r l p.1).R p.2) ω =
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l q.1) (schedGTX h13 c r l q.1) ((ver Ω c r l q.1).V q.2)
          (RootJ31.historyTime c r l) ((ver Ω c r l q.1).R q.2) ω :=
    ae_all_iff.2 fun p => ae_all_iff.2 fun q =>
      GW2Sdo.ae_stgPreRecX_sched_eq h13 c r l p.1 q.1 hs hx ((ver Ω c r l p.1).isA hx p.2).1.1
        ((ver Ω c r l q.1).isA hx q.2).1.1
  have hρ : ∀ᵐ ω ∂c.P, ∀ p : ℕ × ℕ, (ver Ω c r l p.1).V p.2 ω =
      ((ver Ω c r l p.1).isA hx p.2).1.2.choose (cfRec c.s c.W c.ζ ω, fun u => (ver Ω c r l p.1).R p.2 u ω) :=
    ae_all_iff.2 fun p => ((ver Ω c r l p.1).isA hx p.2).1.2.choose_spec.2.2
  have hGTall : ∀ᵐ ω ∂c.P, ∀ a, ω ∈ schedGTX h13 c r l a ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s :=
    ae_all_iff.2 fun a => (schedGTX_spec h13 c r l a).2.2
  filter_upwards [hpair, hρ, hGTall, GW2Sdt.ae_notMem_launchBadRec h13 c r l,
    GW2Ru.ae_alive_goodEvent_scaled h13 gap c r, hU Ω c r l ⟨hx, hs⟩]
    with ω hpω hρω hGTω hlaunch hgoodEv hUω halive n
  have halive32 := GW2Sdz.alive_scaled_subset gap Ω c r l halive
  obtain ⟨hcf, hcon⟩ := hgoodEv l halive
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive32
  filter_upwards [hUω halive32] with m hm a
  have hslot := hm a
  have hex0 : ∃ p : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair p).1)
      (RootJ31.historyTime c r l) ω) < (ver Ω c r l (Nat.unpair p).1).V (Nat.unpair p).2 ω :=
    ⟨Nat.pair a m, by rw [Nat.unpair_pair]; exact hslot⟩
  have hpre : stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V m)
      (RootJ31.historyTime c r l) ((ver Ω c r l a).R m) ω = refPreV h13 ver Ω c r l ω := by
    simp only [refPreV, hex0, ↓reduceDIte]
    exact hpω (a, m) ((Nat.unpair (Nat.find hex0)).1, (Nat.unpair (Nat.find hex0)).2) hcf ⟨hcon a, hslot⟩
      ⟨hcon _, Nat.find_spec hex0⟩
  rw [pkgX_nearVar_eq K c r ⟨hx, hs⟩ l n m a]
  have hA := (ver Ω c r l a).isA hx m
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · show augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((ver Ω c r l a).V m) (RootJ31.historyTime c r l) ((ver Ω c r l a).R m)) ω ∈ (ch Ω c r l a).E₀
    rw [hE₀]
    exact hlaunch halive32 a _
  · exact (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).2 hold
  · have hstart : (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V m)
        (RootJ31.historyTime c r l) ω : ℝ≥0∞) < (ver Ω c r l a).V m ω := by
      rw [GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx ((hGTω a).2 hcf) (hcon a) hslot]
      exact hslot
    exact GW2Sdo.mem_aliveRecX hA.1.2.choose_spec.2.1 (stgRecDec_stageEncRec c r l ω) (hA.1.1.2.1 ω)
      (hA.1.1.2.2.1 ω) hcf (hρω (a, m)) hstart
  · show (ch Ω c r l a).β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (schedGTX h13 c r l a) ((ver Ω c r l a).V m) (RootJ31.historyTime c r l) ((ver Ω c r l a).R m)) ω) = _
    rw [hβ]
    unfold GW2Wm.schedWordMapX refNb
    rw [GW2Rj.candAngle_eq]
    congr 2
    simp only [augRec, hpre]

/-! ### A uniformly covering re-indexing -/

/-- The monotone hull `m ↦ max_{j ≤ m} f j`. -/
def monoHull (f : ℕ → ℕ) (m : ℕ) : ℕ := (Finset.range (m + 1)).sup f

theorem monotone_monoHull (f : ℕ → ℕ) : Monotone (monoHull f) := fun _ _ h =>
  Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ h))

section Cover

variable (ver : SchedVerXFamily.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))

/-- **The cover events of a family**: version `k` of candidate `a` passes the history's clock. -/
def covEvV (a k : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) <
    (ver Ω c r l a).V k ω}

theorem measurableSet_covEvV (hx : 0 ≤ rootPt r.1) (a k : ℕ) : MeasurableSet (covEvV ver c r l a k) := by
  have hclk : Measurable fun ω => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω :=
    RootH29.measurable_forwardCapacity_random (rootPt r.1) c.s
      (measurable_recPair (measurable_gb6Rec_src c) (measurable_schedW c r l a)
        (fun ω => (GW2Sdo.continuous_schedW c r l a ω).1) (fun ω => (GW2Sdo.continuous_schedW c r l a ω).2)
        (RootJ31.historyTime c r l)) measurable_const
  exact measurableSet_lt (ENNReal.measurable_ofReal.comp hclk) ((ver Ω c r l a).isA hx k).1.1.2.2.2.2.1

theorem monotone_covEvV (a : ℕ) : Monotone (covEvV ver c r l a) := fun k k' hkk' ω hω => by
  have hm : Monotone fun j => (ver Ω c r l a).V j ω :=
    monotone_nat_of_le_succ fun j => (ver Ω c r l a).mono j ω
  exact lt_of_lt_of_le hω (hm hkk')

/-- **The uniform cover re-indexing** (SDE's `exists_reindex_eventually_all` on the cover events; the identity off
the nonnegative roots). -/
def psiU : ℕ → ℕ → ℕ :=
  if hx : 0 ≤ rootPt r.1 then
    (GW2Sdo.exists_reindex_eventually_all (μ := c.P) (covEvV ver c r l) (measurableSet_covEvV ver c r l hx)
      (monotone_covEvV ver c r l)).choose
  else fun _ m => m

theorem psiU_mono (a : ℕ) : Monotone (psiU ver c r l a) := by
  unfold psiU
  split_ifs with hx
  · exact (GW2Sdo.exists_reindex_eventually_all (μ := c.P) (covEvV ver c r l) (measurableSet_covEvV ver c r l hx)
      (monotone_covEvV ver c r l)).choose_spec.1 a
  · exact monotone_id

theorem ae_psiU (hx : 0 ≤ rootPt r.1) :
    ∀ᵐ ω ∂c.P, ∀ᶠ m in atTop, ∀ a, (∃ k, ω ∈ covEvV ver c r l a k) → ω ∈ covEvV ver c r l a (psiU ver c r l a m) := by
  simp only [psiU, hx, ↓reduceDIte]
  exact (GW2Sdo.exists_reindex_eventually_all (μ := c.P) (covEvV ver c r l) (measurableSet_covEvV ver c r l hx)
    (monotone_covEvV ver c r l)).choose_spec.2.2

end Cover

/-- An extra re-indexing per source setup, root, history and candidate (BUF's `ψx`). -/
abbrev PsiFamR : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
    List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ

/-- The combined re-indexing `max (psiU a m, monoHull ψx a m)`. -/
def psiAll (ver : SchedVerXFamily.{u}) (ψx : PsiFamR.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) : ℕ :=
  max (psiU ver c r l a m) (monoHull (ψx Ω c r l a) m)

theorem monotone_psiAll (ver : SchedVerXFamily.{u}) (ψx : PsiFamR.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    Monotone (psiAll ver ψx Ω c r l a) :=
  fun _ _ h => max_le_max (psiU_mono ver c r l a h) (monotone_monoHull _ h)

/-- **The uniformly covering re-indexed family** `m ↦ ver (psiAll a m + m)`. -/
def verU (ver : SchedVerXFamily.{u}) (ψx : PsiFamR.{u}) : SchedVerXFamily.{u} :=
  GW2Bh.verReindex ver (fun Ω _ _ c r l a => GW2Bh.reindexPlus (psiAll ver ψx Ω c r l a))
    (fun Ω _ _ c r l a => GW2Bh.strictMono_reindexPlus (monotone_psiAll ver ψx Ω c r l a))

theorem verU_V (ver : SchedVerXFamily.{u}) (ψx : PsiFamR.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) :
    (verU ver ψx Ω c r l a).V m = (ver Ω c r l a).V (psiAll ver ψx Ω c r l a m + m) := rfl

/-- **The re-indexed family covers the clock** (from the coverage of the original family). -/
theorem verCovers_verU {ver : SchedVerXFamily.{u}} (hcov : Wire.T14Rk.VerCovers ver) (ψx : PsiFamR.{u}) :
    Wire.T14Rk.VerCovers (verU ver ψx) := by
  intro Ω _ _ c r l a hg
  filter_upwards [hcov Ω c r l a hg] with ω h halive hcf hTc
  exact GW2Sdt.eventually_lt_reindex (fun n => Nat.le_add_left n _) (h halive hcf hTc)

/-- **The re-indexed family covers the clock uniformly in the candidates.** -/
theorem unifCover_verU {ver : SchedVerXFamily.{u}} (h13 : Exist.Theorem13Statement.{u})
    (hcov : Wire.T14Rk.VerCovers ver) (ψx : PsiFamR.{u}) : UnifCover (verU ver ψx) := by
  intro Ω _ _ c r l hg
  have hcovAll : ∀ᵐ ω ∂c.P, ∀ a : ℕ, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ∀ᶠ k in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) <
        (ver Ω c r l a).V k ω :=
    ae_all_iff.2 fun a => hcov Ω c r l a hg
  filter_upwards [ae_psiU ver c r l hg.1, hcovAll, GW2Ru.ae_alive_goodEvent h13 c r] with ω hψ hcovω hgood halive
  obtain ⟨hcf, hcon⟩ := hgood l halive
  filter_upwards [hψ] with m hm a
  have h1 := hm a ((hcovω a halive hcf (hcon a)).exists)
  have hle : psiU ver c r l a m ≤ psiAll ver ψx Ω c r l a m + m := (le_max_left _ _).trans (Nat.le_add_right _ _)
  exact monotone_covEvV ver c r l a hle h1

end InteractingSLE.Theorem14.GW2Rl
