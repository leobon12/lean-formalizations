/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPreCAssembly
import InteractingSLE.Spec.Restart.FlowStopIdentGRule

/-!
# First-level rules on a longer killed history

The existing first-hit reader is evaluated on a prefix and transferred to its
longer continuation by its strong Galmarino property. Capping its successive
level hits at deterministic times preserves that property and measurability.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF Restart.FlowStopIdentG

variable {nL nR : ℕ}

/-- The existing first-hit theorem also reads a hit strictly before the recorded
lifetime. Its proof is an application to the truncated history and Galmarino. -/
theorem hitRule_eq_of_hit_before {E : Type*} [PseudoEMetricSpace E]
    {ψ : HistorySpace nL nR → ℝ≥0 → E} (hψ : IsNonAnticipating ψ)
    {F : Set E} (hF : IsClosed F) {γ : HistorySpace nL nR} (hγ : IsKilledContHist γ)
    {g : ℝ≥0 → E} {T : ℝ≥0} (hT : 0 < T) (hTγ : (T : ℝ≥0∞) ≤ γ.1)
    (hg : ContinuousOn g (Iic T)) (hoff : ∀ s < T, g s ∉ F) (hgt : g T ∈ F)
    (hread : ∀ p, (dyadicTime p : ℝ≥0∞) < T → ψ γ (dyadicTime p) = g (dyadicTime p)) :
    hitRule ψ F γ = T := by
  let δ := killAt γ (T : ℝ≥0∞)
  have hδ : IsKilledContHist δ := isKilledContHist_killAt hγ hTγ
  have he : ∀ p, (dyadicTime p : ℝ≥0∞) < T → ψ δ (dyadicTime p) = ψ γ (dyadicTime p) := by
    intro p hp
    apply hψ δ γ p
    intro q hq
    have hqt : (dyadicTime q : ℝ≥0∞) < T :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hq) hp
    change (if (dyadicTime q : ℝ≥0∞) < T then γ.2 q else 0) = γ.2 q
    simp only [hqt, ↓reduceIte]
  have hhit : hitRule ψ F δ = T := hitRule_eq_of_hit hF hT rfl hg hoff hgt
    (fun p hp => (he p hp).trans (hread p hp))
  have hgal := isStrongGalmarino_hitRule hψ F
  exact (hgal δ γ hδ hγ T le_rfl hTγ (fun p hp => by
    change (if (dyadicTime p : ℝ≥0∞) < T then γ.2 p else 0) = γ.2 p
    simp only [hp, ↓reduceIte]) hhit.le).trans hhit

/-- A continuous real path starting below a level has a positive first level
contact before any specified time where it reaches the level. -/
theorem exists_first_level_contact {g : ℝ≥0 → ℝ} {U : ℝ≥0} {c : ℝ}
    (hg : ContinuousOn g (Iic U)) (h0 : g 0 < c) (hU : c ≤ g U) :
    ∃ T : ℝ≥0, 0 < T ∧ T ≤ U ∧ c ≤ g T ∧ ∀ s < T, g s < c := by
  let G : ℝ≥0 → ℝ := fun t => g (min t U)
  have hG : Continuous G := hg.comp_continuous (continuous_id.min continuous_const)
    (fun t => min_le_right t U)
  have hK : IsCompact (Icc (0 : ℝ≥0) U ∩ G ⁻¹' Ici c) :=
    isCompact_Icc.inter_right (isClosed_Ici.preimage hG)
  obtain ⟨T, hT⟩ := hK.exists_isLeast ⟨U, ⟨by simp, by simpa only [mem_preimage, mem_Ici, G, min_self] using hU⟩⟩
  have hTU : T ≤ U := hT.1.1.2
  have hcT : c ≤ g T := by simpa only [mem_preimage, mem_Ici, G, min_eq_left hTU] using hT.1.2
  have hT0 : 0 < T := pos_iff_ne_zero.2 fun he => by
    rw [he] at hcT
    exact (not_le_of_gt h0) hcT
  refine ⟨T, hT0, hTU, hcT, fun s hs => ?_⟩
  by_contra hsc
  have hsU : s ≤ U := hs.le.trans hTU
  have hsK : s ∈ Icc (0 : ℝ≥0) U ∩ G ⁻¹' Ici c :=
    ⟨⟨zero_le, hsU⟩, by simpa only [mem_preimage, mem_Ici, G, min_eq_left hsU] using (le_of_not_gt hsc)⟩
  exact (not_le_of_gt hs) (hT.2 hsK)

/-- The first hit of level `n+1`, capped at deterministic time `n+1`. -/
def levelPrefixRule (ψ : HistorySpace nL nR → ℝ≥0 → ℝ) (n : ℕ)
    (γ : HistorySpace nL nR) : ℝ≥0∞ :=
  min (hitRule ψ (Ici ((n : ℝ) + 1)) γ) ((n : ℝ≥0∞) + 1)

/-- Level-prefix rules are Borel on the whole history carrier. -/
theorem measurable_levelPrefixRule {ψ : HistorySpace nL nR → ℝ≥0 → ℝ}
    (hm : ∀ p, Measurable fun γ => ψ γ (dyadicTime p)) (n : ℕ) :
    Measurable (levelPrefixRule ψ n) :=
  (measurable_hitRule hm _).min measurable_const

/-- Level-prefix rules are strong Galmarino, and hence ordinary Galmarino. -/
theorem isStrongGalmarino_levelPrefixRule {ψ : HistorySpace nL nR → ℝ≥0 → ℝ}
    (hψ : IsNonAnticipating ψ) (n : ℕ) : IsStrongGalmarino (levelPrefixRule ψ n) :=
  (isStrongGalmarino_hitRule hψ _).min (isStrongGalmarino_const _)

end InteractingSLE.WFS
