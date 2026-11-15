/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqTail

/-!
# Mixed-pocket gap equality when the target is at infinity

Packet PROVE-R7-GAPEQ. The last-visit counterpart of `pocketGapEq_of_collars`, with the same
explicit remaining local geometric inputs. Properness is included where the last-visit
supremum needs a bounded parameter set. No determination theorem is used (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace InteractingSLE.Sec7.R7GapEq

open Sec6 R7StopIn

/-- **Mixed pocket with target at infinity, conditional reduction.** Old contacts have parameter
strictly below the last-visit attachment, because the proper barrier is parametrized from the
entrance towards infinity. The geometric hypotheses remain explicit unproved inputs for the
actual mixed pockets. -/
theorem pocketGapEqInf_of_collars
    {W : ℝ → ℝ} {η B : ℝ → ℂ} {C F K O : Set ℂ} {τ : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hCo : IsOpen C)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (hfr : frontier C ⊆ B '' Ici 0 ∪ O)
    (houter : ∀ p ∈ O, HasExteriorCollar C F K p)
    (hBc : ContinuousOn B (Ici 0)) (hBi : InjOn B (Ici 0))
    (hBt : Tendsto (fun v => ‖B v‖) atTop atTop)
    (hrev : IsReverseVisitOrderInf B fun t => η '' Icc 0 t)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 0) (hτf : η τ ∉ η '' Ico 0 τ)
    (hAC : BarrierAttachConstInf η C B τ)
    (hOld : ∀ t ∈ Ioi τ, ∀ v ∈ Ici (0 : ℝ),
      v < lastVisit (fun s => η '' Icc 0 s) B t → η t = B v →
        HasOldAllowedCover η C F K (η t) t) :
    PocketGapEqInf η C τ := by
  have hfirst : lastVisit (fun s => η '' Icc 0 s) B τ = 0 :=
    lastVisit_eq_of_fresh hBc hBi hBt hη.2.1 hrev hτ0 (mem_Ici.2 le_rfl) hτ hτf
  intro a b hτa hab hgap hb ha
  have ha0 : 0 ≤ a := hτ0.trans hτa
  have endpoint : ∀ t ∈ Icc a b,
      (t = τ ∨ t ∈ closure {u | τ < u ∧ η u ∈ C}) →
        η t = B (lastVisit (fun s => η '' Icc 0 s) B t) := by
    intro t ht hvis
    rcases hvis with htτ | hvis
    · rw [htτ, hfirst, hτ]
    have htfr : η t ∈ frontier C := by
      refine ⟨mem_closure_of_visits hη.2.1 hτ0 hvis, ?_⟩
      rw [hCo.interior_eq]
      exact hgap t ht
    obtain ⟨v, hv, hvt⟩ := mem_barrier_at_gap hη.2.1 h42 havoid hfr houter
      ha0 hab hgap ht htfr
    have hRt : IsCompact (η '' Icc 0 t) :=
      isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun _ hs => hs.1)
    have hvu : v ≤ lastVisit (fun s => η '' Icc 0 s) B t :=
      le_lastVisit hBt hRt.isBounded hv ⟨t, ⟨ha0.trans ht.1, le_rfl⟩, hvt.symm⟩
    rcases hvu.eq_or_lt with he | he
    · rw [← he, hvt]
    have htτ : τ < t := by
      refine lt_of_le_of_ne (hτa.trans ht.1) ?_
      intro heq
      have hv0 := hBi hv (mem_Ici.2 le_rfl) (hvt.trans (heq ▸ hτ))
      rw [heq.symm, hfirst, hv0] at he
      exact lt_irrefl _ he
    exact False.elim (not_hasOldAllowedCover_at_gap hη hW hW0 h42 havoid
      ha0 hab hgap ht hvis (hOld t htτ v hv he hvt.symm))
  have haeq := endpoint a ⟨le_rfl, hab.le⟩ ha
  have hbvis : b ∈ closure {u | τ < u ∧ η u ∈ C} :=
    closure_mono (s := {u | a < u ∧ η u ∈ C}) (t := {u | τ < u ∧ η u ∈ C})
      (fun u hu => ⟨hτa.trans_lt hu.1, hu.2⟩) hb
  have hbeq := endpoint b ⟨hab.le, le_rfl⟩ (Or.inr hbvis)
  rw [haeq, hbeq, hAC a b hτa hab.le hgap]

end InteractingSLE.Sec7.R7GapEq
