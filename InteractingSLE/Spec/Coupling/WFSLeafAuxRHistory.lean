/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafKernel

/-!
# Reading a Galmarino prefix from a continuation

This pointwise adapter retains the field when an Aux. 54 extension is used.
The earlier driving-law argument already uses this identity internally; here
the identity is exposed for comparing the joint field--history laws.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF

/-- Restricting a continuous killed record to an earlier lifetime preserves
its continuous-record property. -/
theorem isKilledContHist_killAt {nL nR : ℕ} {γ : HistorySpace nL nR}
    (hγ : IsKilledContHist γ) {t : ℝ≥0∞} (ht : t ≤ γ.1) :
    IsKilledContHist (killAt γ t) := by
  obtain ⟨f, hc, hf⟩ := hγ
  refine ⟨f, hc.mono (fun s hs => hs.trans_le ht), fun p hp => ?_⟩
  change (dyadicTime p : ℝ≥0∞) < t at hp
  change (if (dyadicTime p : ℝ≥0∞) < t then γ.2 p else 0) = f (dyadicTime p)
  simpa only [hp, ↓reduceIte] using hf p (hp.trans_le ht)

/-- The rule keeps its value when the history is killed at that value. -/
theorem rule_apply_ruleKill {nL nR : ℕ}
    {Q : HistorySpace nL nR → ℝ≥0∞} (hQ : IsHistGalmarino Q)
    {γ : HistorySpace nL nR} (hγ : IsKilledContHist γ) (hle : Q γ ≤ γ.1) :
    Q (ruleKill Q γ) = Q γ := by
  have hδ : IsKilledContHist (ruleKill Q γ) := isKilledContHist_killAt hγ (min_le_right _ _)
  apply hQ γ (ruleKill Q γ) hγ hδ hle
  · change Q γ ≤ min (Q γ) γ.1
    rw [min_eq_left hle]
  · intro p hp
    change γ.2 p = if (dyadicTime p : ℝ≥0∞) < min (Q γ) γ.1 then γ.2 p else 0
    simp only [min_eq_left hle, hp, ↓reduceIte]

/-- A rule whose value is before the first recorded cutoff reads the same
prefix from that cutoff record and from its longer continuation. -/
theorem ruleKill_eq_ruleKill_of_prefix {nL nR : ℕ}
    {Q : HistorySpace nL nR → ℝ≥0∞} (hQ : IsHistGalmarino Q)
    {γ δ : HistorySpace nL nR} (hγ : IsKilledContHist γ) (hδ : IsKilledContHist δ)
    (hQγ : Q γ ≤ γ.1) (hle : γ.1 ≤ δ.1)
    (hs : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < γ.1 → γ.2 p = δ.2 p) :
    ruleKill Q δ = ruleKill Q γ := by
  have he := hQ γ δ hγ hδ hQγ (hQγ.trans hle) (fun p hp => hs p (hp.trans_le hQγ))
  apply Prod.ext
  · change min (Q δ) δ.1 = min (Q γ) γ.1
    rw [he, min_eq_left (hQγ.trans hle), min_eq_left hQγ]
  · funext p
    change (if (dyadicTime p : ℝ≥0∞) < min (Q δ) δ.1 then δ.2 p else 0) =
      if (dyadicTime p : ℝ≥0∞) < min (Q γ) γ.1 then γ.2 p else 0
    rw [he, min_eq_left (hQγ.trans hle), min_eq_left hQγ]
    split_ifs with hp
    · exact (hs p (hp.trans_le hQγ)).symm
    · rfl

/-- A normalized stopped record is read from any continuous extension by its
own Galmarino rule. No terminal value of the extended path is used. -/
theorem ruleKill_eq_of_prefix {nL nR : ℕ}
    {R : HistorySpace nL nR → ℝ≥0∞} (hR : IsHistGalmarino R)
    {γ δ : HistorySpace nL nR} (hγ : IsKilledContHist γ) (hδ : IsKilledContHist δ)
    (hn : historyNormalize γ = γ) (hr : R γ = γ.1) (hle : γ.1 ≤ δ.1)
    (hs : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < γ.1 → γ.2 p = δ.2 p) :
    ruleKill R δ = γ := by
  have hrδ : R δ = γ.1 := (hR γ δ hγ hδ (hr ▸ le_rfl) (hr ▸ hle)
    (fun p hp => hs p (hr ▸ hp))).trans hr
  apply Prod.ext
  · exact (min_eq_left (hrδ ▸ hle)).trans hrδ
  · funext p
    change (if (dyadicTime p : ℝ≥0∞) < min (R δ) δ.1 then δ.2 p else 0) = γ.2 p
    rw [hrδ, min_eq_left hle]
    by_cases hp : (dyadicTime p : ℝ≥0∞) < γ.1
    · simp only [hp, ↓reduceIte, hs p hp]
    · have hnp := congrFun (congrArg Prod.snd hn) p
      simpa only [historyNormalize, hp, ↓reduceIte] using hnp

end InteractingSLE.WFS
