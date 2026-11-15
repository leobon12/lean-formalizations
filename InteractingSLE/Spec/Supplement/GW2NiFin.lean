/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NiUncLaw
import InteractingSLE.Spec.Supplement.GW2BuReidx

/-!
# The version families satisfy the exhaustion property; the cap and buffer hypothesis of `exists_kSel`

Packet PROVE-GW2-NEARIMG2 (D50).

* **`exhStopStatement_deathFamily`**: RELDET's death family `GW2Rd.schedVerXDeathFamily` satisfies
  `ExhStopStatement` (its exhaustion below the death, `GW2Rd.schedVerXDeath_exhausts_death`);
* **`ExhStopStatement.reindex`**: so does every strictly increasing re-indexing (`GW2Bh.verReindex`, BUF's final
  family);
* **`exists_capBuf_of_unc`** (one sample): from an uncapped exit `e` before the end (`e + clock(T) < clock(T + t₀)`,
  `t₀` before the life, `T + t₀` before the uncapped contact), every cap past `t₀` has, eventually in the buffer, J32's
  gain above `e` — the hypothesis `hgood` of `exists_kSel` once BUF identifies the selected exits with `e`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

/-- **RELDET's death family exhausts below the stop.** -/
theorem exhStopStatement_deathFamily (h13 : Exist.Theorem13Statement.{u}) :
    ExhStopStatement (schedVerXDeathFamily h13) := by
  intro Ω _ _ c r l a hg hord
  filter_upwards [schedVerXDeath_exhausts_death h13 c r l a hg.1 hg.2 hord] with ω h hgx hold t ht _ hd
  exact h hgx hold t ht hd

/-- **A strictly increasing re-indexing keeps the exhaustion.** -/
theorem ExhStopStatement.reindex {ver : GW2Rv.SchedVerXFamily.{u}} (h : ExhStopStatement ver)
    (φ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω),
      ScaledRootIdx c.Θ c.Q → List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ)
    (hφ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), StrictMono (φ Ω c r l a)) :
    ExhStopStatement (GW2Bh.verReindex ver φ hφ) := by
  intro Ω _ _ c r l a hg hord
  filter_upwards [h Ω c r l a hg hord] with ω hω hgx hold t ht htc hd
  have hev := hω hgx hold t ht htc hd
  have htend : Tendsto (φ Ω c r l a) atTop atTop := (hφ Ω c r l a).tendsto_atTop
  filter_upwards [htend.eventually hev] with n hn
  rw [show ((GW2Bh.verReindex ver φ hφ) Ω c r l a).V n ω = (ver Ω c r l a).V (φ Ω c r l a n) ω from by
    rw [GW2Bh.verReindex, GW2Bh.reindex_V _ (hφ Ω c r l a)]]
  exact hn

theorem candidateWithBuffer_angCand (i k b : ℕ) :
    RootK32.candidateWithBuffer (angCand i k) b = Nat.pair i (Nat.pair k b) := by
  simp only [RootK32.candidateWithBuffer, angCand, Nat.unpair_pair]

/-- **The cap and buffer step of the kSel bound against the uncapped driver** (one sample). On the good sets of the
capped candidates of angle `i`, with the cover event and the history's success, where every candidate of the angle
explores and traces the uncapped curve up to `T + cap` (`UncAgreeStatement`): an exit `e` of the uncapped stage path
with `e + clock(T) < clock(T + t₀)`, `t₀` before the life and `T + t₀` before the uncapped contact, is eventually (in
the buffer) below J32's gain of every candidate `Nat.pair i (Nat.pair k b)` whose cap passes `t₀ + 1`. -/
theorem exists_capBuf_of_unc {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (i : ℕ) (hx : 0 ≤ rootPt r.1) {ξ : Ω}
    (hGT : ∀ k, ξ ∈ schedGTX h13 c r l (angCand i k)) (hcov : ξ ∈ RootCv.coverEvent c r)
    (hold : oldSuccess c r l ξ)
    (hUA : ∀ a : ℕ, candidateAngle c r a = angleEnumeration c r i →
      ∀ t ≤ historyTime c r l + candidateCap c r a,
        schedW c r l a t ξ = uncW c r l i t ξ ∧ schedTr c r l a ξ t = uncTr c r l i ξ t)
    (hUc : Continuous (uncTr c r l i ξ)) {e : ℝ≥0∞} {t₀ : ℝ≥0} (ht₀ζ : (t₀ : ℝ≥0∞) < uncLife c r l i ξ)
    (ht₀T : ((historyTime c r l + t₀ : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ)
    (he : e + ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) (historyTime c r l) ξ) <
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) (historyTime c r l + t₀) ξ)) :
    ∃ Q : ℝ≥0, ∀ k : ℕ, Q ≤ (timeEnumeration c r k : ℝ≥0) →
      ∀ᶠ b in atTop, e < (GW2Sdg.rootGain c r l (Nat.pair i (Nat.pair k b)) ξ : ℝ≥0∞) := by
  refine ⟨t₀ + 1, fun k hk => ?_⟩
  have ht₀c : t₀ < (timeEnumeration c r k : ℝ≥0) := (lt_add_one t₀).trans_le hk
  have hang : candidateAngle c r (angCand i k) = angleEnumeration c r i := candidateAngle_angCand c r i k
  have hcapk : ∀ t, t ≤ historyTime c r l + (timeEnumeration c r k : ℝ≥0) →
      t ≤ historyTime c r l + candidateCap c r (angCand i k) := fun t ht => by
    rw [candidateCap_angCand]; exact ht
  have h := eventually_lt_rootGain_of_unc h13 c r l i hx k (hGT k) hcov hold
    (fun t ht => (hUA _ hang t (hcapk t ht)).1) (fun t ht => (hUA _ hang t (hcapk t ht)).2) hUc ht₀c ht₀ζ ht₀T he
  filter_upwards [h] with b hb
  rwa [candidateWithBuffer_angCand] at hb

end InteractingSLE.Theorem14.GW2Ni
