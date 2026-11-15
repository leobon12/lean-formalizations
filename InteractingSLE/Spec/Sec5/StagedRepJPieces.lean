/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJTree

/-!
# Prop 5.9's later root stages: PIECES' canonical objects are read on `Gam`

Packet PROVE-STAGED-REPJ. The target side of the transfer of a later stage's comparison clause: PIECES' root
candidates (`rootCand … q`) agree, at almost every sample `ω'`, with REP2's candidates `gamCand r` on `Gam` at the pair
`Z ω' = (qField ω'.1, cfHistory ω'.1)` (`pieceZ`): the two tree data agree there (`agreeAt_rootData_gamData`), except on
the null set where PIECES' good set `rootGood` (read through `toMeasurable`) and `Z⁻¹ gamGood` differ. Hence:

* `aeComap P Z 𝓜`: the events almost surely equal to `Z`-preimages of `𝓜`-events (a σ-algebra);
* **`canonQ_le_aeComap`**: the canonical pasts of a family agreeing almost surely with a family on `Γ` at `Z` lie in
  `aeComap` of the canonical pasts on `Γ`; `canonR_ae_eq`: the reached events agree almost surely;
* **`rootPast_ae`**, **`rootObs_ae`**: the past and the observable conditions of `compClauseK_transfer` for PIECES'
  candidate `(ℓ, t)` against `Gam`'s.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open Prop59System Prop59Stage Prop59Pieces StagedCand StagedAdapt StagedKill StagedKCand StagedRepLater
open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart Sec4

/-! ### Events almost surely equal to preimages -/

section AeComap

variable {Ω Γ : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → Γ)

/-- **The events almost surely equal to `Z`-preimages of `𝓜`-events.** -/
@[instance_reducible]
def aeComap (𝓜 : MeasurableSpace Γ) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ M, MeasurableSet[𝓜] M ∧ A =ᵐ[P] Z ⁻¹' M
  measurableSet_empty := ⟨∅, @MeasurableSet.empty Γ 𝓜, by rw [preimage_empty]⟩
  measurableSet_compl A := fun ⟨M, hM, h⟩ => ⟨Mᶜ, hM.compl, by rw [preimage_compl]; exact h.compl⟩
  measurableSet_iUnion f hf := by
    choose M hM h using hf
    exact ⟨⋃ i, M i, MeasurableSet.iUnion hM, by rw [preimage_iUnion]; exact EventuallyEqSet.countable_iUnion h⟩

variable {P Z}

theorem aeComap_mono {𝓜 𝓜' : MeasurableSpace Γ} (h : 𝓜 ≤ 𝓜') : aeComap P Z 𝓜 ≤ aeComap P Z 𝓜' :=
  fun _ ⟨M, hM, hA⟩ => ⟨M, h _ hM, hA⟩

end AeComap

/-! ### Canonical pasts and reached events of almost surely agreeing families -/

section Canon

variable {Ω Γ : Type*} {𝓑 : MeasurableSpace Ω} {𝓑' : MeasurableSpace Γ} [MeasurableSpace Ω] [MeasurableSpace Γ]
  {P : Measure Ω} {Z : Ω → Γ} {nL₀ nR₀ : ℕ}
  {cand : CandFam Ω nL₀ nR₀} {cand' : CandFam Γ nL₀ nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)}
  {y₀' : Γ → Start (nL₀ + 0) (nR₀ + 0)} (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀)

/-- **The canonical pasts of almost surely agreeing families.** -/
theorem canonQ_le_aeComap (hfam : IsRegFam cand)
    (hfam' : IsRegFam cand') (hy₀ : Measurable y₀) (hy₀' : Measurable y₀')
    (hag : ∀ᵐ ω ∂P, (∀ j t, PieceAt (cand j t) (cand' j t) ω (Z ω)) ∧ y₀ ω = y₀' (Z ω))
    (hbase : 𝓑 ≤ aeComap P Z 𝓑') :
    ∀ j t, canonQ 𝓑 cand G hnL hnR y₀ j t ≤ aeComap P Z (canonQ 𝓑' cand' G hnL hnR y₀' j t)
  | 0, _ => hbase
  | j + 1, t => by
    refine sup_le ((canonQ_le_aeComap hfam hfam' hy₀ hy₀' hag hbase j (Fin.init t)).trans
      (aeComap_mono le_sup_left)) (MeasurableSpace.generateFrom_le ?_)
    rintro B ⟨n, m, S, hnm, hS, rfl⟩
    refine ⟨swEv G hnL hnR j (candStage cand' (canonY cand' y₀') j (Fin.init t)) n m ∩
      {γ | (swT G hnL hnR j (candStage cand' (canonY cand' y₀') j (Fin.init t)) n γ,
        nextStart G hnL hnR j (candStage cand' (canonY cand' y₀') j (Fin.init t)) n γ) ∈ S}, ?_, ?_⟩
    · refine le_sup_right (a := canonQ 𝓑' cand' G hnL hnR y₀' j (Fin.init t)) _ ?_
      exact MeasurableSpace.measurableSet_generateFrom ⟨n, m, S, hnm, hS, rfl⟩
    · filter_upwards [hag] with ω hω
      exact propext (mem_swGen_congr G hnL hnR hω.1 hω.2 hfam hfam' hy₀ hy₀' j (Fin.init t) n m S)

omit [MeasurableSpace Γ] in
/-- **The canonical reached events of almost surely agreeing families agree almost surely.** -/
theorem canonR_ae_eq {R₀ : Set Ω} {R₀' : Set Γ}
    (hag : ∀ᵐ ω ∂P, (∀ j t, PieceAt (cand j t) (cand' j t) ω (Z ω)) ∧ y₀ ω = y₀' (Z ω))
    (hR : ∀ᵐ ω ∂P, (ω ∈ R₀ ↔ Z ω ∈ R₀')) (j : ℕ) (t : Fin j → ℝ≥0) :
    canonR cand G hnL hnR y₀ R₀ j t =ᵐ[P] Z ⁻¹' canonR cand' G hnL hnR y₀' R₀' j t := by
  filter_upwards [hag, hR] with ω hω hωR
  exact propext (mem_canonR_congr G hnL hnR hω.1 hω.2 hωR j t)

end Canon

end InteractingSLE.Sec5.CrossCond.StagedRepJ
