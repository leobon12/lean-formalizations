/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermInputs

/-!
# The clock clauses of the path statement at a good sample

Packet PROVE-RC-TERM, second run (ruling R124). Pathwise, at a good sample (`IsTermGood`) whose capacity lifetime and
chart path match a code value `p` (the conclusion of `ae_codeMatch_term`):

* **`IsTermGood.conclusion`**: the inverse clock `c₁ = invClock (chartClock pPath) pStop` and `σ = aLife` satisfy the
  clauses of `TerminalRetainedPathStatement`: `σ ≤ p.2`; `c₁` strictly increasing on `[0, σ]`; `c₁ [0, σ]` is the set
  of physical times `t ≤ ζ₁` with no contact with `η₂[0, T]` strictly between `0` and `t`; and
  `η₁ (c₁ s) = termInv x₂ r (decPath p s)` on `[0, σ]`.

Proof: `IsClockOn.strictMonoOn_invClock`, `IsClockOn.image_invClock` (the image is `[0, pStop]`), `pStop` is the first
contact with `{x₁} ∪ ηb₂[0, N] = {x₁} ∪ η₂[0, T]` (`IsTermGood.pStop_eq`, injectivity of the first path), and the chart
identities `termInv_eq_kInv`, `IsKSample.kInv_kPath_of_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Restart Supp7 Sec7 Sec7.Lemma76F Exist.Staged Exist.StagedLaw Sec2.Assembly RLC.AStopProc

section Conclude

variable {Ω : Type*} {N : ℝ≥0} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ηb₂ η₁' η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
  {x₁ x₂ : ℝ} {ω : Ω}

/-- **The clock clauses at a good sample** (see the module docstring). -/
theorem IsTermGood.conclusion (g : IsTermGood N E ηb₂ η₁' ζ₁ x₁ x₂ ω) (hE2 : (E ω).2 = ζ₂ ω) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) = ζ₂ ω) (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (hag₂ : ∀ s, ηb₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s)) {p : (PCode × PCode) × ℝ≥0∞}
    (hV : aLife (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂) ω ≤ p.2)
    (hγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ aLife (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂) ω →
      aPath (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂) ω t + (pSeed N E x₁ x₂ ω : ℂ) =
        decPath p t) :
    ∃ (c₁ : ℝ≥0 → ℝ≥0) (σ : ℝ≥0∞), σ ≤ p.2 ∧ StrictMonoOn c₁ {s | (s : ℝ≥0∞) ≤ σ} ∧
      c₁ '' {s | (s : ℝ≥0∞) ≤ σ} =
        {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₁ ω ∧ ∀ t' : ℝ≥0, 0 < t' → t' < t → η₁ ω t' ∉ η₂ ω '' Icc 0 T} ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η₁ ω (c₁ s) = termInv x₂ (pRec N E ω) (decPath p s) := by
  obtain ⟨q, w, hq, hs⟩ := g.sample
  have hc := g.isAGood.clock
  have hLζ : pStop N E ηb₂ η₁' ζ₁ x₁ x₂ ω ≤ ζ₁ ω := physStop_le _ _ _ _ _
  have hTN : T ≤ N := by
    have h1 := g.life
    rw [hE2, ← hT] at h1
    exact_mod_cast h1
  -- the retained image is the completed second path
  have hcap : ∀ s, capTime (capR 0 N) (ζ₂ ω) s = min s T := fun s => by
    have h1 : min (ζ₂ ω) ((capR 0 N : ℝ≥0) : ℝ≥0∞) = (T : ℝ≥0∞) := by
      rw [← hT]
      exact min_eq_left (ENNReal.coe_le_coe.2 (hTN.trans (lt_capR_right 0 N).le))
    simp only [capTime, h1, ENNReal.toNNReal_coe]
  have himg2 : ηb₂ ω '' Icc 0 N = η₂ ω '' Icc 0 T := by
    ext z
    constructor
    · rintro ⟨s, -, rfl⟩
      exact ⟨min s T, ⟨zero_le, min_le_right _ _⟩, by rw [hag₂, hcap]⟩
    · rintro ⟨s, hs', rfl⟩
      exact ⟨s, ⟨hs'.1, hs'.2.trans hTN⟩, by rw [hag₂, hcap, min_eq_left hs'.2]⟩
  -- contacts of the first version with the retained union are contacts of the first path with `η₂[0, T]`
  have hK : ∀ t' : ℝ≥0, 0 < t' → (t' : ℝ≥0∞) ≤ ζ₁ ω →
      (η₁' ω t' ∈ η₁' ω '' Icc 0 0 ∪ ηb₂ ω '' Icc 0 N ↔ η₁ ω t' ∈ η₂ ω '' Icc 0 T) := by
    intro t' ht0 htζ
    rw [Icc_self, image_singleton, himg2, ← ha₁ t' htζ]
    constructor
    · rintro (h1 | h1)
      · exfalso
        have h2 : t' = 0 := g.path.1 (show ((t' : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ ω from htζ)
          (show (((0 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ ω by rw [ENNReal.coe_zero]; exact zero_le) h1
        exact absurd h2 ht0.ne'
      · exact h1
    · exact fun h1 => Or.inr h1
  refine ⟨invClock (chartClock (pPath N E ηb₂ η₁' ζ₁ x₁ x₂ ω)) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂ ω),
    aLife (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂) ω, hV, hc.strictMonoOn_invClock, ?_,
    fun s hs' => ?_⟩
  · have hi := hc.image_invClock
    refine hi.trans ?_
    ext t
    simp only [mem_ofPred_eq]
    rw [g.pStop_eq]
    constructor
    · intro ht
      obtain ⟨-, htζ, hno⟩ := mem_contSet_of_le (zero_le) ht
      refine ⟨htζ, fun t' ht0 htt hmem => hno t' ht0 htt ?_⟩
      have ht'ζ : (t' : ℝ≥0∞) ≤ ζ₁ ω := (ENNReal.coe_le_coe.2 htt.le).trans htζ
      exact (hK t' ht0 ht'ζ).2 hmem
    · rintro ⟨htζ, hno⟩
      refine le_contStop ⟨zero_le, htζ, fun t' ht0 htt hmem => hno t' ht0 htt ?_⟩
      have ht'ζ : (t' : ℝ≥0∞) ≤ ζ₁ ω := (ENNReal.coe_le_coe.2 htt.le).trans htζ
      exact (hK t' ht0 ht'ζ).1 hmem
  · have hle := (hc.invClock_spec hs').1
    rw [← hγ s hs']
    have e1 : aPath (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂) ω s =
        kPath (pU N E ω) (pRho₂ ηb₂ x₂ ω) (pT N E ω) (x₁ - x₂) (pRho₁ η₁' x₁ ω) (ζ₁ ω)
          (invClock (chartClock (pPath N E ηb₂ η₁' ζ₁ x₁ x₂ ω)) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂ ω) s) := rfl
    have e2 : (pSeed N E x₁ x₂ ω : ℂ) = (markPos (pU N E ω) (pT N E ω : ℝ) (x₁ - x₂) : ℂ) := rfl
    rw [e1, e2, termInv_eq_kInv hs rfl (rtime_pRec N E ω) rfl (hs.kPath_mem_Hbar _), hs.kInv_kPath_of_le hle]
    simp only [pRho₁, sub_add_cancel]
    exact (ha₁ _ (hle.trans hLζ)).symm

end Conclude

end Term

end InteractingSLE.RealContact
