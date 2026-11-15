/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkVersion6Paths
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianGood

/-!
# Announcing target separation for a local solution

Cap the original announcing times at the first gap below `1/(n+1)`.
The construction uses continuity and the positive initial target gap, without
maximality of the evolution or a restriction on the target's index.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Version6

open Zhan.Retarget

/-- The original announcing time capped before a small target gap. -/
def sepAnnounce {Ω : Type*} (W V : ℝ≥0 → Ω → ℝ) (e : Ω → ℝ≥0∞)
    (A : ℕ → Ω → ℝ≥0) (n : ℕ) : Ω → ℝ≥0 :=
  Sec2.TwoSeed.capTime (A n)
    (fun ω => Coupling.hitBelow (fun s => V s ω - W s ω) (e ω) (1 / ((n : ℝ) + 1)))

variable {Ω : Type*} {W V : ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0}

/-- The capped time is at most the given original stop. -/
theorem sepAnnounce_le (n : ℕ) (ω : Ω) : sepAnnounce W V e A n ω ≤ A n ω :=
  Sec2.TwoSeed.capTime_le _ _ _

/-- The capped time as a minimum in extended nonnegative time. -/
theorem coe_sepAnnounce (n : ℕ) (ω : Ω) :
    (sepAnnounce W V e A n ω : WithTop ℝ≥0) = min (A n ω : WithTop ℝ≥0)
      (Coupling.hitBelow (fun s => V s ω - W s ω) (e ω) (1 / ((n : ℝ) + 1))) :=
  Sec2.TwoSeed.coe_capTime _ _ _

/-- The capped stops increase everywhere when the original stops do. -/
theorem monotone_sepAnnounce (hA : ∀ ω, Monotone (A · ω)) (ω : Ω) :
    Monotone (sepAnnounce W V e A · ω) := by
  intro m n hmn
  apply WithTop.coe_le_coe.1
  rw [coe_sepAnnounce, coe_sepAnnounce]
  refine min_le_min (WithTop.coe_le_coe.2 (hA ω hmn)) (Coupling.hitBelow_anti ?_)
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

/-- Every capped stop lies strictly before target separation. -/
theorem sepAnnounce_lt_sepTime {ω : Ω}
    (hc : ContinuousOn (fun s => V s ω - W s ω) {s | (s : ℝ≥0∞) < e ω})
    (h0 : W 0 ω < V 0 ω) {n : ℕ} (hA : (A n ω : ℝ≥0∞) < e ω) :
    (sepAnnounce W V e A n ω : ℝ≥0∞) < sepTime (W · ω) (V · ω) (e ω) := by
  set q := sepAnnounce W V e A n ω
  have hq : (q : ℝ≥0∞) < e ω := (ENNReal.coe_le_coe.2 (sepAnnounce_le n ω)).trans_lt hA
  have hhit : (q : WithTop ℝ≥0) ≤
      Coupling.hitBelow (fun s => V s ω - W s ω) (e ω) (1 / ((n : ℝ) + 1)) :=
    (coe_sepAnnounce n ω).symm ▸ min_le_right _ _
  have hbefore : ∀ s : ℝ≥0, s < q → 1 / ((n : ℝ) + 1) ≤ V s ω - W s ω := by
    intro s hs
    by_contra hlt
    have hsζ := (ENNReal.coe_le_coe.2 hs.le).trans_lt hq
    have hle := hhit.trans (Coupling.hitBelow_le hsζ (not_le.1 hlt))
    exact (not_le.2 hs) (WithTop.coe_le_coe.1 hle)
  refine lt_sepTime_of_forall hc hq fun s hs => ?_
  rcases hs.lt_or_eq with hs | rfl
  · have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith only [hbefore s hs, hδ]
  · rcases eq_zero_or_pos q with hq0 | hq0
    · simpa only [hq0] using h0
    · have : NeBot (𝓝[<] q) := nhdsLT_neBot_of_exists_lt ⟨0, hq0⟩
      have hcont := hc.continuousAt ((Coupling.isOpen_setOf_coe_lt (e ω)).mem_nhds hq)
      have hlim : Tendsto (fun s => V s ω - W s ω) (𝓝[<] q) (𝓝 (V q ω - W q ω)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have hge : 1 / ((n : ℝ) + 1) ≤ V q ω - W q ω :=
        ge_of_tendsto hlim
          (by filter_upwards [self_mem_nhdsWithin] with s hs; exact hbefore s hs)
      have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith only [hge, hδ]

/-- The capped stops exhaust the entire interval before target separation. -/
theorem exists_le_sepAnnounce {ω : Ω}
    (hc : ContinuousOn (fun s => V s ω - W s ω) {s | (s : ℝ≥0∞) < e ω})
    (hAm : Monotone (A · ω))
    (hA : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → ∃ n, t ≤ A n ω)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < sepTime (W · ω) (V · ω) (e ω)) :
    ∃ n, t ≤ sepAnnounce W V e A n ω := by
  have htζ := ht.trans_le (sepTime_le _ _ _)
  have hcont : ContinuousOn (fun s => V s ω - W s ω) (Icc 0 t) :=
    hc.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans_lt htζ
  obtain ⟨δ, hδ, hbound⟩ := isCompact_Icc.exists_forall_le' hcont (fun s hs =>
    sub_pos.2 (lt_of_lt_sepTime ((ENNReal.coe_le_coe.2 hs.2).trans_lt ht)))
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  obtain ⟨k, hk⟩ := hA t htζ
  refine ⟨max N k, WithTop.coe_le_coe.1 ?_⟩
  rw [coe_sepAnnounce]
  refine le_min (WithTop.coe_le_coe.2 (hk.trans (hAm (le_max_right _ _))))
    (Coupling.le_hitBelow fun s _ hsmall => ?_)
  by_contra hst
  have hst' : s < t := not_le.1 hst
  have hNs : 1 / (((max N k : ℕ) : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_left N k) 1)
  linarith only [hsmall, hbound s ⟨zero_le, hst'.le⟩, hNs, hN]

end InteractingSLE.Sec5.TwoMark.Version6
