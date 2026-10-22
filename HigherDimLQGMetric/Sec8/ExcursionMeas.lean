import HigherDimLQGMetric.Sec8.ConfigBorel
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Borel stopping times of a continuous excursion

The first step is the closed hitting-event theorem on a compact time set.
It supplies the measurability of the boundary and collector hitting times
used to index excursions by rational times.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Topology unitInterval
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Hitting a closed spatial set during a fixed closed set of times is a
closed condition on a continuous path. -/
theorem isClosed_sec8_path_hits_closed (F : Set (Rd d)) (hF : IsClosed F)
    (K : Set unitInterval) (hK : IsClosed K) :
    IsClosed {η : C(unitInterval, Rd d) | ∃ t ∈ K, η t ∈ F} := by
  let S : Set (C(unitInterval, Rd d) × unitInterval) :=
    {p | p.2 ∈ K ∧ p.1 p.2 ∈ F}
  have hS : IsClosed S :=
    (hK.preimage continuous_snd).inter (hF.preimage continuous_eval)
  have heq : {η : C(unitInterval, Rd d) | ∃ t ∈ K, η t ∈ F} = Prod.fst '' S := by
    ext η
    constructor
    · rintro ⟨t, ht, hη⟩
      exact ⟨(η, t), ⟨ht, hη⟩, rfl⟩
    · rintro ⟨⟨η', t⟩, ⟨ht, hη⟩, rfl⟩
      exact ⟨t, ht, hη⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace S hS

/-- A closed spatial hit between two variable time bounds is still closed:
the time witness lives in the compact unit interval. -/
theorem isClosed_sec8_path_hits_between (F : Set (Rd d)) (hF : IsClosed F) :
    IsClosed {p : C(unitInterval, Rd d) × (unitInterval × unitInterval) |
      ∃ t : unitInterval, p.2.1 ≤ t ∧ t ≤ p.2.2 ∧ p.1 t ∈ F} := by
  let S : Set ((C(unitInterval, Rd d) × (unitInterval × unitInterval)) × unitInterval) :=
    {p | p.1.2.1 ≤ p.2 ∧ p.2 ≤ p.1.2.2 ∧ p.1.1 p.2 ∈ F}
  have hS : IsClosed S :=
    (isClosed_le (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (by fun_prop) (by fun_prop)).inter
        (hF.preimage (by fun_prop)))
  have heq : {p : C(unitInterval, Rd d) × (unitInterval × unitInterval) |
        ∃ t : unitInterval, p.2.1 ≤ t ∧ t ≤ p.2.2 ∧ p.1 t ∈ F} =
      Prod.fst '' S := by
    ext p
    constructor
    · rintro ⟨t, h₁, h₂, hF⟩
      exact ⟨(p, t), ⟨h₁, h₂, hF⟩, rfl⟩
    · rintro ⟨⟨p', t⟩, ⟨h₁, h₂, hF⟩, rfl⟩
      exact ⟨t, h₁, h₂, hF⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace S hS

/-- Times at or before `τ` when a path hits `F`, with time zero added so the
set is always nonempty. -/
def sec8PriorHit (η : C(unitInterval, Rd d)) (F : Set (Rd d))
    (τ : unitInterval) : Set unitInterval :=
  {0} ∪ (Iic τ ∩ η ⁻¹' F)

theorem isClosed_sec8PriorHit (η : C(unitInterval, Rd d))
    (F : Set (Rd d)) (hF : IsClosed F) (τ : unitInterval) :
    IsClosed (sec8PriorHit η F τ) :=
  isClosed_singleton.union (isClosed_Iic.inter (hF.preimage η.continuous))

theorem sec8PriorHit_nonempty (η : C(unitInterval, Rd d))
    (F : Set (Rd d)) (τ : unitInterval) :
    (sec8PriorHit η F τ).Nonempty :=
  ⟨0, Or.inl rfl⟩

/-- The last hit of a closed set before `τ`, defaulting to zero. -/
def sec8LastHit (η : C(unitInterval, Rd d)) (F : Set (Rd d))
    (τ : unitInterval) : unitInterval :=
  sSup (sec8PriorHit η F τ)

theorem sec8LastHit_mem (η : C(unitInterval, Rd d))
    (F : Set (Rd d)) (hF : IsClosed F) (τ : unitInterval) :
    sec8LastHit η F τ ∈ sec8PriorHit η F τ :=
  (isClosed_sec8PriorHit η F hF τ).sSup_mem (sec8PriorHit_nonempty η F τ)

theorem measurable_sec8LastHit (F : Set (Rd d)) (hF : IsClosed F)
    (τ : unitInterval) :
    Measurable fun η : C(unitInterval, Rd d) => sec8LastHit η F τ := by
  apply measurable_of_Ici
  intro a
  by_cases ha : a = 0
  · subst a
    have hpre : (fun η : C(unitInterval, Rd d) => sec8LastHit η F τ) ⁻¹' Ici 0 = univ := by
      ext η
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact bot_le
    rw [hpre]
    exact MeasurableSet.univ
  · have hpre : (fun η : C(unitInterval, Rd d) => sec8LastHit η F τ) ⁻¹' Ici a =
        {η | ∃ t ∈ Icc a τ, η t ∈ F} := by
      ext η
      simp only [mem_preimage, mem_Ici, mem_ofPred_eq]
      constructor
      · intro hlast
        have hm := sec8LastHit_mem η F hF τ
        rcases hm with hzero | ⟨htτ, htF⟩
        · have ha0 : a ≤ (0 : unitInterval) := hzero ▸ hlast
          exact False.elim (ha (le_antisymm ha0 bot_le))
        · exact ⟨sec8LastHit η F τ, ⟨hlast, htτ⟩, htF⟩
      · rintro ⟨t, ⟨hat, htτ⟩, htF⟩
        exact hat.trans (le_sSup (show t ∈ sec8PriorHit η F τ from Or.inr ⟨htτ, htF⟩))
    rw [hpre]
    exact (isClosed_sec8_path_hits_closed F hF (Icc a τ) isClosed_Icc).measurableSet

/-- Joint Borel measurability in the path and the cutoff time. -/
theorem measurable_sec8LastHit_joint (F : Set (Rd d)) (hF : IsClosed F) :
    Measurable fun p : C(unitInterval, Rd d) × unitInterval => sec8LastHit p.1 F p.2 := by
  apply measurable_of_Ici
  intro a
  by_cases ha : a = 0
  · subst a
    have hpre : (fun p : C(unitInterval, Rd d) × unitInterval =>
        sec8LastHit p.1 F p.2) ⁻¹' Ici 0 = univ := by
      ext p
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact bot_le
    rw [hpre]
    exact MeasurableSet.univ
  · have hpre : (fun p : C(unitInterval, Rd d) × unitInterval =>
        sec8LastHit p.1 F p.2) ⁻¹' Ici a =
        {p | ∃ t : unitInterval, a ≤ t ∧ t ≤ p.2 ∧ p.1 t ∈ F} := by
      ext p
      simp only [mem_preimage, mem_Ici, mem_ofPred_eq]
      constructor
      · intro hlast
        have hm := sec8LastHit_mem p.1 F hF p.2
        rcases hm with hzero | ⟨htτ, htF⟩
        · have ha0 : a ≤ (0 : unitInterval) := hzero ▸ hlast
          exact False.elim (ha (le_antisymm ha0 bot_le))
        · exact ⟨sec8LastHit p.1 F p.2, hlast, htτ, htF⟩
      · rintro ⟨t, hat, htτ, htF⟩
        exact hat.trans (le_sSup (show t ∈ sec8PriorHit p.1 F p.2 from Or.inr ⟨htτ, htF⟩))
    rw [hpre]
    have hcont : Continuous fun p : C(unitInterval, Rd d) × unitInterval =>
        (p.1, (a, p.2)) := by fun_prop
    have hclosed := (isClosed_sec8_path_hits_between F hF).preimage hcont
    exact hclosed.measurableSet

/-- Times at or after `τ` when a path hits `F`, with time one added. -/
def sec8FollowingHit (η : C(unitInterval, Rd d)) (F : Set (Rd d))
    (τ : unitInterval) : Set unitInterval :=
  {1} ∪ (Ici τ ∩ η ⁻¹' F)

theorem isClosed_sec8FollowingHit (η : C(unitInterval, Rd d))
    (F : Set (Rd d)) (hF : IsClosed F) (τ : unitInterval) :
    IsClosed (sec8FollowingHit η F τ) :=
  isClosed_singleton.union (isClosed_Ici.inter (hF.preimage η.continuous))

theorem sec8FollowingHit_nonempty (η : C(unitInterval, Rd d))
    (F : Set (Rd d)) (τ : unitInterval) :
    (sec8FollowingHit η F τ).Nonempty :=
  ⟨1, Or.inl rfl⟩

/-- The first hit of a closed set after `τ`, defaulting to one. -/
def sec8FirstHit (η : C(unitInterval, Rd d)) (F : Set (Rd d))
    (τ : unitInterval) : unitInterval :=
  sInf (sec8FollowingHit η F τ)

theorem sec8FirstHit_mem (η : C(unitInterval, Rd d))
    (F : Set (Rd d)) (hF : IsClosed F) (τ : unitInterval) :
    sec8FirstHit η F τ ∈ sec8FollowingHit η F τ :=
  (isClosed_sec8FollowingHit η F hF τ).sInf_mem (sec8FollowingHit_nonempty η F τ)

theorem measurable_sec8FirstHit (F : Set (Rd d)) (hF : IsClosed F)
    (τ : unitInterval) :
    Measurable fun η : C(unitInterval, Rd d) => sec8FirstHit η F τ := by
  apply measurable_of_Iic
  intro a
  by_cases ha : a = 1
  · subst a
    have hpre : (fun η : C(unitInterval, Rd d) => sec8FirstHit η F τ) ⁻¹' Iic 1 = univ := by
      ext η
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact le_top
    rw [hpre]
    exact MeasurableSet.univ
  · have hpre : (fun η : C(unitInterval, Rd d) => sec8FirstHit η F τ) ⁻¹' Iic a =
        {η | ∃ t ∈ Icc τ a, η t ∈ F} := by
      ext η
      simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
      constructor
      · intro hfirst
        have hm := sec8FirstHit_mem η F hF τ
        rcases hm with hone | ⟨hτt, htF⟩
        · have h1a : (1 : unitInterval) ≤ a := hone ▸ hfirst
          exact False.elim (ha (le_antisymm le_top h1a))
        · exact ⟨sec8FirstHit η F τ, ⟨hτt, hfirst⟩, htF⟩
      · rintro ⟨t, ⟨hτt, hta⟩, htF⟩
        exact (sInf_le (show t ∈ sec8FollowingHit η F τ from Or.inr ⟨hτt, htF⟩)).trans hta
    rw [hpre]
    exact (isClosed_sec8_path_hits_closed F hF (Icc τ a) isClosed_Icc).measurableSet

/-- Joint Borel measurability of the first hit after a variable cutoff. -/
theorem measurable_sec8FirstHit_joint (F : Set (Rd d)) (hF : IsClosed F) :
    Measurable fun p : C(unitInterval, Rd d) × unitInterval => sec8FirstHit p.1 F p.2 := by
  apply measurable_of_Iic
  intro a
  by_cases ha : a = 1
  · subst a
    have hpre : (fun p : C(unitInterval, Rd d) × unitInterval =>
        sec8FirstHit p.1 F p.2) ⁻¹' Iic 1 = univ := by
      ext p
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact le_top
    rw [hpre]
    exact MeasurableSet.univ
  · have hpre : (fun p : C(unitInterval, Rd d) × unitInterval =>
        sec8FirstHit p.1 F p.2) ⁻¹' Iic a =
        {p | ∃ t : unitInterval, p.2 ≤ t ∧ t ≤ a ∧ p.1 t ∈ F} := by
      ext p
      simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
      constructor
      · intro hfirst
        have hm := sec8FirstHit_mem p.1 F hF p.2
        rcases hm with hone | ⟨hτt, htF⟩
        · have h1a : (1 : unitInterval) ≤ a := hone ▸ hfirst
          exact False.elim (ha (le_antisymm le_top h1a))
        · exact ⟨sec8FirstHit p.1 F p.2, hτt, hfirst, htF⟩
      · rintro ⟨t, hτt, hta, htF⟩
        exact (sInf_le (show t ∈ sec8FollowingHit p.1 F p.2 from Or.inr ⟨hτt, htF⟩)).trans hta
    rw [hpre]
    have hcont : Continuous fun p : C(unitInterval, Rd d) × unitInterval =>
        (p.1, (p.2, a)) := by fun_prop
    have hclosed := (isClosed_sec8_path_hits_between F hF).preimage hcont
    exact hclosed.measurableSet

end HigherDimLQGMetric
