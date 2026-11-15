/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuStmt
import InteractingSLE.Spec.Supplement.GW2TrCap

/-!
# The uncapped joined driver of an angle: definitions and the statements BUF consumes

Packet PROVE-GW2-NEARIMG2, decision D50 (BUF's D-e). Clause (iii) of `VNearImgOn` is closed by sending the J31
candidate's cap to `∞` against the UNCAPPED joined driver of its angle. This file fixes the objects and the
statements; their proofs are in the later `GW2NiUnc*` files.

**The objects** (angle index `i`, history `l`; `T = historyTime`):
* `capIdx c r t`: a cap index whose cap value is at least `t` (`Q` is dense, hence unbounded);
* `angCand i k = Nat.pair i (Nat.pair k 0)`: the candidate of angle index `i`, cap index `k`, buffer `0`;
* **`uncW c r l i`**: at time `t`, the explored driver `schedW` of the candidate of angle `i` whose cap is above `t`.
  By RELDET's D-b (`GW2Rd.ae_schedW_eq_of_angle`) it is almost surely the explored driver of EVERY candidate of that
  angle before its cap: the history followed by the whole (uncapped) piece of the angle;
* **`uncTr`**: a generating trace of `uncW` on `[0, ∞)` where one exists (the slit otherwise), as `GW2Rd.schedTr`;
* `uncLife`: the piece's lifetime (common to the angle, `GW2Rd.candLife_eq_of_angle`);
* **`uncDeathX`**: the root-`x` clock of the death `T + ζ` when the piece dies before the root-`x` contact, `⊤`
  otherwise (the uncapped `GW2Rd.deathClockX`).

**The statements** (BUF consumes them; section "For BUF" of `planning/handoffs/PROVE-GW2-NEARIMG2.md`):
* **`UncRegStatement`**: almost surely `uncW` is continuous from `0`, `uncTr` is a generating trace on `[0, ∞)`, and it
  is transient (Theorem 1.3's `ζ = ⊤ → ‖η‖ → ∞` on `{uncLife = ⊤}`, the frozen tail otherwise);
* **`UncAgreeStatement`**: almost surely every candidate of the angle explores `uncW` and traces `uncTr` up to
  `T + cap` (D-b against the uncapped driver);
* **`IsCanonUX`** / **`StageLawUXStatement`**: the stage law of the uncapped driver in `GW2Bh.IsCanonX` form, written
  with the hull identity (the form `GW2Bh.gapVanishes_contactX` consumes) instead of a version family: a continuous
  canonical relative driver from `0` generating the re-centred relative hulls of `uncW` before the root-`x` contact and
  the death, with a generating trace living to the root-`x` relative life and the clock bounded before the contact;
* **`UncEndStatement`**: the same law restricted to `{uncLife = ⊤} ∩ {no root-`x` contact}` — the one part that is
  not a consequence of the capped law `GW2Bh.StageLawXStatement` (there no capped candidate sees the end of the
  uncapped curve). It is the input asked from STAGEMEAN (D50).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

section Defs

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (i : ℕ)

/-- Some cap value is at least `t` (`Q` is dense in `ℝ≥0`). -/
theorem exists_capIdx_ge (t : ℝ≥0) : ∃ k : ℕ, t ≤ (timeEnumeration c r k : ℝ≥0) := by
  obtain ⟨q, hqQ, hq⟩ := c.hQd.exists_between (lt_add_one t)
  obtain ⟨k, hk⟩ := timeEnumeration_surjective c r ⟨q, hqQ⟩
  exact ⟨k, by rw [hk]; exact hq.1.le⟩

/-- **A cap index whose cap value is at least `t`.** -/
def capIdx (t : ℝ≥0) : ℕ := (exists_capIdx_ge c r t).choose

theorem le_capIdx (t : ℝ≥0) : t ≤ (timeEnumeration c r (capIdx c r t) : ℝ≥0) :=
  (exists_capIdx_ge c r t).choose_spec

/-- **The candidate of angle index `i` and cap index `k`** (buffer `0`). -/
def angCand (i k : ℕ) : ℕ := Nat.pair i (Nat.pair k 0)

theorem candidateAngle_angCand (i k : ℕ) : candidateAngle c r (angCand i k) = angleEnumeration c r i := by
  simp only [candidateAngle, angCand, Nat.unpair_pair]

theorem candidateCap_angCand (i k : ℕ) :
    candidateCap c r (angCand i k) = (timeEnumeration c r k : ℝ≥0) := by
  simp only [candidateCap, angCand, Nat.unpair_pair]

/-- **The uncapped joined driver of angle index `i`**: at time `t`, the explored driver of the candidate of that
angle whose cap is above `t`. -/
def uncW : ℝ≥0 → Ω → ℝ := fun t ω => schedW c r l (angCand i (capIdx c r t)) t ω

open scoped Classical in
/-- **A generating trace of the uncapped joined driver on `[0, ∞)`** where one exists (the slit otherwise). -/
def uncTr : Ω → ℝ≥0 → ℂ :=
  fun ω => if h : ∃ η, IsGeneratingTrace (fun t => uncW c r l i t ω) ⊤ η then h.choose else Gm.slitTrace

/-- **The piece's lifetime** (common to all candidates of the angle). -/
abbrev uncLife (ω : Ω) : ℝ≥0∞ := candLife c r l (angCand i 0) ω

open scoped Classical in
/-- **The uncapped death clock**: the root-`x` clock of `T + ζ` when the piece dies before the root-`x` contact,
`⊤` otherwise. -/
def uncDeathX (ω : Ω) : ℝ≥0∞ :=
  if uncLife c r l i ω ≠ ⊤ ∧ ((historyTime c r l + (uncLife c r l i ω).toNNReal : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (uncTr c r l i) c.α ω then
    ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i)
      (historyTime c r l + (uncLife c r l i ω).toNNReal) ω)
  else ⊤

/-- **The stage law of the uncapped driver at one sample** (`GW2Bh.IsCanonX` with the hull identity): a continuous
relative driver from `0` generating the re-centred relative hulls of `uncW` before the root-`x` contact and the
death, with a generating trace living to the root-`x` relative life, the clock bounded before the contact. -/
def IsCanonUX (ξ : Ω) (Wc : ℝ≥0 → ℝ) : Prop :=
  Continuous Wc ∧ Wc 0 = 0 ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ) < uncDeathX c r l i ξ →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ) ∧
    (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
      ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (uncW c r l i · ξ)
        (uncTr c r l i ξ) (c.α ξ)) ≤ ζc) ∧
    ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ →
      clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ ≤ M

end Defs

/-! ### The statements -/

/-- **Regularity and transience of the uncapped joined driver** (time-ordered histories). -/
def UncRegStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (i : ℕ), GW2Sdx.HistOrdered c r l → ∀ᵐ ω ∂c.P,
      Continuous (uncW c r l i · ω) ∧ uncW c r l i 0 ω = 0 ∧
      IsGeneratingTrace (uncW c r l i · ω) ⊤ (uncTr c r l i ω) ∧
      Tendsto (fun t => ‖uncTr c r l i ω t‖) atTop atTop

/-- **D-b against the uncapped driver**: every candidate of the angle explores `uncW` and traces `uncTr` up to
`T + cap`. -/
def UncAgreeStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (i : ℕ), ∀ᵐ ω ∂c.P, ∀ a : ℕ, candidateAngle c r a = angleEnumeration c r i →
      ∀ t ≤ historyTime c r l + candidateCap c r a,
        schedW c r l a t ω = uncW c r l i t ω ∧ schedTr c r l a ω t = uncTr c r l i ω t

/-- **The stage law of the uncapped driver** (on the good counterflow records and the history's success). -/
def StageLawUXStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (i : ℕ), GW2Rv.GoodRoot c r → GW2Sdx.HistOrdered c r l →
    ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ξ →
      ∃ Wc : ℝ≥0 → ℝ, IsCanonUX c r l i ξ Wc

/-- **The input asked from STAGEMEAN (D50)**: the uncapped stage law where the piece lives forever and never meets
the counterflow prefix (the only case no capped candidate sees). -/
def UncEndStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (i : ℕ), GW2Rv.GoodRoot c r → GW2Sdx.HistOrdered c r l →
    ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ξ →
      uncLife c r l i ξ = ⊤ → contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ = ⊤ →
      ∃ Wc : ℝ≥0 → ℝ, IsCanonUX c r l i ξ Wc

end InteractingSLE.Theorem14.GW2Ni
