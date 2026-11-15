/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmCons

/-!
# GW2's open lines: the stage union of a history is its prefix's union at the entry's end

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic; the union side of the Claim(k) step):

* `oldSuccess_of_cons`: a successful history has a successful prefix;
* **`schedUnionS_cons_eq`**: on the history's success, the corrected stage union of `(r, e :: l', a)` at stage time
  `0` IS the corrected union of the prefix `(r, l', a')` at the entry's duration `δ`, for a prefix candidate `a'` of
  the entry's angle whose cap reaches past the entry's end;
* **`schedUnionS_cons_subset`**: at every sample (given the identity on success), the prefix's union at `δ` lies in
  the history's union at `0` (off the history's success the latter is `ℍ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Psm

open Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec5.Prop513Schedule GW2TipSystem.Swc

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A successful history has a successful prefix.** -/
theorem oldSuccess_of_cons (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) (ω : Ω) (h : oldSuccess c r (e :: l') ω) : oldSuccess c r l' ω := by
  rintro ⟨j, hj⟩
  have hj' : j < (historyProgram c r (e :: l')).length := by
    rw [historyProgram_cons, List.length_append, List.length_singleton]
    omega
  have h1 := h ⟨j, hj'⟩
  change (stopRec c.hκ c.h12p c.βA c.c₀ c.h
    (schedSpec (rootPt r.1) (historyProgram c r (e :: l'))) j ω).2.2 = false at h1
  change (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (historyProgram c r l')) j ω).2.2 = false
  rw [historyProgram_cons, GW2TipSystem.stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hj ω] at h1
  exact h1

/-- **The stage union of a history at its start is the prefix's union at the entry's end** (on the history's
success). -/
theorem schedUnionS_cons_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ) (ω : Ω)
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2))
    (hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2))
    (hold : oldSuccess c r (e :: l') ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r (e :: l') a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r (e :: l') a) ω ⟨j, hj⟩)))
    (hgood' : ∀ (j : ℕ) (hj : j < (futureProgram c r l' a').length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l' a') ω ⟨j, hj⟩)))
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (δ : ℝ≥0) (hδ : historyTime c r l' + δ = historyTime c r (e :: l')) :
    GW2Sdi.schedUnionS c r (e :: l') a 0 ω = GW2Sdi.schedUnionS c r l' a' δ ω := by
  have hold' := oldSuccess_of_cons c r e l' ω hold
  unfold GW2Sdi.schedUnionS
  rw [ite_eq_left_of_eq_true _ _ (eq_true hold), ite_eq_left_of_eq_true _ _ (eq_true hold')]
  unfold GW2Sdh.schedPhysUnion
  rw [add_zero, hδ]
  congr 1
  set T : ℝ≥0 := historyTime c r (e :: l') with hT
  have hc1 : Continuous fun s : ℝ => GW2Rd.schedW c r (e :: l') a s.toNNReal ω :=
    (GW2Rd.continuous_schedW c r (e :: l') a ω).comp continuous_real_toNNReal
  have hc2 : Continuous fun s : ℝ => GW2Rd.schedW c r l' a' s.toNNReal ω :=
    (GW2Rd.continuous_schedW c r l' a' ω).comp continuous_real_toNNReal
  refine LocalExt.fwdHull_congr_of_continuousOn (t' := (T : ℝ) + 1) hc1.continuousOn hc2.continuousOn
    T.coe_nonneg (by linarith) fun s hs => ?_
  have hsT : s.toNNReal ≤ T := by
    rw [Real.toNNReal_le_iff_le_coe]
    exact hs.2
  show GW2Rd.schedW c r (e :: l') a s.toNNReal ω = GW2Rd.schedW c r l' a' s.toNNReal ω
  rw [congrFun (GW2Rd.schedW_of_oldSuccess c r (e :: l') a hold) s.toNNReal,
    congrFun (GW2Rd.schedW_of_oldSuccess c r l' a' hold') s.toNNReal]
  exact futureJoined_cons_eq c r e l' a a' ω hord hord' hold hold' hgood hgood' hθ hcap _ hsT

/-- **The prefix's union at the entry's end lies in the history's union at its start.** -/
theorem schedUnionS_cons_subset (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ) (δ : ℝ≥0) (ω : Ω)
    (heq : oldSuccess c r (e :: l') ω → GW2Sdi.schedUnionS c r (e :: l') a 0 ω = GW2Sdi.schedUnionS c r l' a' δ ω) :
    GW2Sdi.schedUnionS c r l' a' δ ω ⊆ GW2Sdi.schedUnionS c r (e :: l') a 0 ω := by
  by_cases hs : oldSuccess c r (e :: l') ω
  · rw [heq hs]
  · have h1 : GW2Sdi.schedUnionS c r (e :: l') a 0 ω = H := by
      unfold GW2Sdi.schedUnionS
      simp only [hs, ↓reduceIte]
    rw [h1]
    exact (GW2Sdi.schedUnionS_subset_isOpen c r l' a' δ ω).1

end InteractingSLE.Theorem14.GW2Psm
