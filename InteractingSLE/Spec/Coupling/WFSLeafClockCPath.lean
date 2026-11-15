/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafClockCHit
import InteractingSLE.Spec.Sec7.RelClockAnnounce

/-!
# Cofinal Galmarino prefixes from a continuous observable

For a scalar history reader starting at zero, continuous before the cutoff,
and unbounded before every finite cutoff, the capped level-hit rules are
strictly earlier and cofinal. Cofinality reuses the existing relative-clock
announcement by comparison, rather than reproving compact-time boundedness.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF Restart.FlowStopIdentG

variable {nL nR : ℕ} {ψ : HistorySpace nL nR → ℝ≥0 → ℝ} {γ : HistorySpace nL nR}

/-- A continuous observable reaching level `c` before the recorded lifetime
makes its first-hit rule no later than that time. -/
theorem hitRule_le_of_level_contact (hψ : IsNonAnticipating ψ) (hγ : IsKilledContHist γ)
    {U : ℝ≥0} {c : ℝ} (hU : (U : ℝ≥0∞) < γ.1)
    (hc : ContinuousOn (ψ γ) (Iic U)) (h0 : ψ γ 0 < c) (hu : c ≤ ψ γ U) :
    hitRule ψ (Ici c) γ ≤ U := by
  obtain ⟨T, hT0, hTU, hTc, hoff⟩ := exists_first_level_contact hc h0 hu
  have he := hitRule_eq_of_hit_before hψ isClosed_Ici hγ hT0
    ((ENNReal.coe_le_coe.2 hTU).trans hU.le) (hc.mono (Iic_subset_Iic.2 hTU))
    (fun s hs => not_le.2 (hoff s hs)) hTc (fun _ _ => rfl)
  rw [he]
  exact ENNReal.coe_le_coe.2 hTU

/-- Each capped level rule is strictly before a cutoff at which the observable
is unbounded; infinite cutoffs are handled by the deterministic cap. -/
theorem levelPrefixRule_lt (hψ : IsNonAnticipating ψ) (hγ : IsKilledContHist γ)
    (hc : ContinuousOn (ψ γ) {t | (t : ℝ≥0∞) < γ.1}) (h0 : ψ γ 0 = 0)
    (hunb : γ.1 ≠ ⊤ → ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < γ.1 ∧ M < ψ γ t)
    (n : ℕ) : levelPrefixRule ψ n γ < γ.1 := by
  by_cases htop : γ.1 = ⊤
  · rw [htop]
    have hfin : ((((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
    exact lt_of_le_of_lt (min_le_right _ _) (by exact_mod_cast hfin)
  · obtain ⟨U, hU, hu⟩ := hunb htop ((n : ℝ) + 1)
    have hcont := hc.mono (fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hU)
    have hstart : ψ γ 0 < (n : ℝ) + 1 := by rw [h0]; positivity
    exact (min_le_left _ _).trans_lt ((hitRule_le_of_level_contact hψ hγ hU hcont hstart hu.le).trans_lt hU)

/-- The existing open-entrance announcement is bounded by the Galmarino
closed-level rule. This transfers its cofinality to the history rule. -/
theorem relClock_announce_le_levelPrefixRule
    (hc : ContinuousOn (ψ γ) {t | (t : ℝ≥0∞) < γ.1})
    (hunb : γ.1 ≠ ⊤ → ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < γ.1 ∧ M < ψ γ t)
    (n : ℕ) :
    ((Sec7.RelClock.announce (fun t (_ : Unit) => ψ γ t) (fun _ => (γ.1 : WithTop ℝ≥0)) n () :
      ℝ≥0) : ℝ≥0∞) ≤ levelPrefixRule ψ n γ := by
  let X : ℝ≥0 → Unit → ℝ := fun t _ => ψ γ t
  let ζ : Unit → WithTop ℝ≥0 := fun _ => γ.1
  let a := Sec7.RelClock.announce X ζ n ()
  have ha : (a : ℝ≥0∞) < γ.1 := Sec7.RelClock.announce_lt (ω := ()) hunb n
  have hat : (a : ℝ≥0∞) ≤ hitRule ψ (Ici ((n : ℝ) + 1)) γ := by
    apply le_hitRule_of_off isClosed_Ici (hc.mono fun t ht => show (t : ℝ≥0∞) < γ.1 from ht.trans ha)
    · intro t ht hmem
      have htζ : (t : WithTop ℝ≥0) < ζ () := ht.trans ha
      have hentr : Sec7.RelClock.entrance X ζ (n : ℝ) () ≤ t :=
        Sec7.RelClock.entrance_le htζ (by exact (lt_add_one (n : ℝ)).trans_le hmem)
      have hate : (a : WithTop ℝ≥0) ≤ Sec7.RelClock.entrance X ζ (n : ℝ) () := by
        change ((Sec7.RelClock.announce X ζ n () : ℝ≥0) : WithTop ℝ≥0) ≤ _
        rw [Sec7.RelClock.coe_announce]
        exact min_le_right _ _
      exact (not_le_of_gt ht) (hate.trans hentr)
    · intro p _ _
      rfl
  refine le_min hat ?_
  have han : a ≤ (n : ℝ≥0) := min_le_left _ _
  exact (ENNReal.coe_le_coe.2 han).trans (le_add_right le_rfl)

/-- The level-prefix rules converge to the recorded lifetime. -/
theorem tendsto_levelPrefixRule (hψ : IsNonAnticipating ψ) (hγ : IsKilledContHist γ)
    (hc : ContinuousOn (ψ γ) {t | (t : ℝ≥0∞) < γ.1}) (h0 : ψ γ 0 = 0)
    (hunb : γ.1 ≠ ⊤ → ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < γ.1 ∧ M < ψ γ t) :
    Tendsto (fun n => levelPrefixRule ψ n γ) atTop (𝓝 γ.1) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    obtain ⟨t, hbt, htγ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb
    obtain ⟨N, hN⟩ := Sec7.RelClock.exists_le_announce
      (X := fun t (_ : Unit) => ψ γ t) (ζ := fun _ => (γ.1 : WithTop ℝ≥0))
      (fun _ => hc) (ω := ()) htγ
    filter_upwards [eventually_ge_atTop N] with n hn
    have hmono := Sec7.RelClock.monotone_announce
      (X := fun t (_ : Unit) => ψ γ t) (ζ := fun _ => (γ.1 : WithTop ℝ≥0)) () hn
    exact hbt.trans_le ((ENNReal.coe_le_coe.2 (hN.trans hmono)).trans
      (relClock_announce_le_levelPrefixRule hc hunb n))
  · intro b hb
    exact Eventually.of_forall fun n => (levelPrefixRule_lt hψ hγ hc h0 hunb n).trans hb

end InteractingSLE.WFS
