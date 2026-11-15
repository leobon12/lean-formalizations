/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallOuterGeomInf

/-! # Visited neighborhoods from the order on the actual pocket walls

These adapters use the two-arc topology and clipped wall order only. No global
reverse-pocket configuration or ambient domain equality is assumed.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace InteractingSLE.Sec7.R5Out
open Sec6 PocketJordan

theorem exists_ball_frontier_subset_range_of_wallOrder {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ}
    (hP : PocketJordan.IsCfPocket C α₁ α₂)
    (hrev₁ : R16.IsReverseVisitOrder α₁ (fun t => η '' Icc 0 t))
    (hrev₂ : R16.IsReverseVisitOrder α₂ (fun t => η '' Icc 0 t))
    {T : ℝ} (hyR : α₁ 1 ∈ η '' Icc 0 T) {p : ℂ} (hpR : p ∈ η '' Icc 0 T)
    (h₁ : p ≠ α₁ (firstVisit (fun t => η '' Icc 0 t) α₁ T))
    (h₂ : p ≠ α₂ (firstVisit (fun t => η '' Icc 0 t) α₂ T)) :
    ∃ r > 0, frontier C ∩ ball p r ⊆ η '' Icc 0 T := by
  -- one wall at a time
  have key : ∀ (α : ℝ → ℂ), ContinuousOn α (Icc 0 1) → InjOn α (Icc 0 1) →
      R16.IsReverseVisitOrder α (fun t => η '' Icc 0 t) → α 1 ∈ η '' Icc 0 T →
      p ≠ α (firstVisit (fun t => η '' Icc 0 t) α T) →
      IsCompact (α '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α T)) ∧
        p ∉ α '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α T) ∧
        ∀ w ∈ Icc (0 : ℝ) 1, α w ∉ α '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α T) →
          α w ∈ η '' Icc 0 T := by
    intro α hαc hαi hrev h1 hp
    set V := {v ∈ Icc (0 : ℝ) 1 | α v ∈ η '' Icc 0 T} with hV
    have h1V : (1 : ℝ) ∈ V := ⟨⟨zero_le_one, le_rfl⟩, h1⟩
    have hne : V.Nonempty := ⟨1, h1V⟩
    have hbdd : BddBelow V := ⟨0, fun v hv => hv.1.1⟩
    have hu1 : sInf V ≤ 1 := csInf_le hbdd h1V
    have hu0 : 0 ≤ sInf V := le_csInf hne fun v hv => hv.1.1
    have hfv : firstVisit (fun t => η '' Icc 0 t) α T = sInf V := rfl
    rw [hfv] at hp ⊢
    refine ⟨isCompact_Icc.image_of_continuousOn (hαc.mono (Icc_subset_Icc_right hu1)), ?_, ?_⟩
    · rintro ⟨w, hw, hpw⟩
      have hwV : w ∈ V := ⟨⟨hw.1, hw.2.trans hu1⟩, hpw ▸ hpR⟩
      have hwu : w = sInf V := le_antisymm hw.2 (csInf_le hbdd hwV)
      exact hp (by rw [← hpw, hwu])
    · intro w hw hnot
      have hlt : sInf V < w := by
        by_contra hle
        exact hnot ⟨w, ⟨hw.1, not_lt.1 hle⟩, rfl⟩
      obtain ⟨v₀, hv₀, hv₀w⟩ := exists_lt_of_csInf_lt hne hlt
      exact hrev T v₀ hv₀.1 w hw hv₀w.le hv₀.2
  obtain ⟨hK₁, hp₁, hv₁⟩ := key α₁ hP.cont₁ hP.inj₁ hrev₁ hyR h₁
  obtain ⟨hK₂, hp₂, hv₂⟩ := key α₂ hP.cont₂ hP.inj₂ hrev₂ (hP.seed ▸ hyR) h₂
  have hKc : IsClosed ((α₁ '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α₁ T)) ∪
      α₂ '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α₂ T)) := (hK₁.union hK₂).isClosed
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl p (by
    rintro (h | h)
    · exact hp₁ h
    · exact hp₂ h)
  refine ⟨r, hr, fun z ⟨hzF, hzb⟩ => ?_⟩
  have hzK := hball hzb
  rw [hP.frontier_eq] at hzF
  rcases hzF with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact hv₁ w hw fun h => hzK (Or.inl h)
  · exact hv₂ w hw fun h => hzK (Or.inr h)


theorem exists_ball_frontier_subset_rangeInf_of_wallOrder {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ}
    (hP : PocketJordan.IsCfPocketInf C α₁ α₂) (hη : ContinuousOn η (Ici 0))
    (hrev₁ : IsReverseVisitOrderInf α₁ (fun t => η '' Icc 0 t))
    (hrev₂ : IsReverseVisitOrderInf α₂ (fun t => η '' Icc 0 t))
    {T : ℝ} (hyR : α₁ 0 ∈ η '' Icc 0 T) {p : ℂ} (hpR : p ∈ η '' Icc 0 T)
    (h₁ : p ≠ α₁ (lastVisit (fun t => η '' Icc 0 t) α₁ T))
    (h₂ : p ≠ α₂ (lastVisit (fun t => η '' Icc 0 t) α₂ T)) :
    ∃ r > 0, frontier C ∩ ball p r ⊆ η '' Icc 0 T := by
  have hRb : Bornology.IsBounded (η '' Icc 0 T) :=
    (isCompact_Icc.image_of_continuousOn (hη.mono fun t ht => ht.1)).isBounded
  obtain ⟨M, hM⟩ := hRb.exists_norm_le
  have key : ∀ (α : ℝ → ℂ), ContinuousOn α (Ici 0) → Tendsto (fun v => ‖α v‖) atTop atTop →
      IsReverseVisitOrderInf α (fun t => η '' Icc 0 t) → α 0 ∈ η '' Icc 0 T →
      p ≠ α (lastVisit (fun t => η '' Icc 0 t) α T) →
      ∃ Vp : ℝ, IsCompact (α '' Icc (lastVisit (fun t => η '' Icc 0 t) α T) Vp) ∧
        p ∉ α '' Icc (lastVisit (fun t => η '' Icc 0 t) α T) Vp ∧
        ∀ w ∈ Ici (0 : ℝ), ‖α w‖ < ‖p‖ + 1 →
          α w ∉ α '' Icc (lastVisit (fun t => η '' Icc 0 t) α T) Vp → α w ∈ η '' Icc 0 T := by
    intro α hαc hαt hrev h0 hp
    set V := {v ∈ Ici (0 : ℝ) | α v ∈ η '' Icc 0 T} with hV
    have h0V : (0 : ℝ) ∈ V := ⟨show (0 : ℝ) ≤ 0 from le_rfl, h0⟩
    have hne : V.Nonempty := ⟨0, h0V⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hαt.eventually_gt_atTop M)
    have hbdd : BddAbove V := ⟨N, fun v hv => by
      by_contra hlt
      exact absurd (hM _ hv.2) (not_le.2 (hN v (not_le.1 hlt).le))⟩
    have hu0 : 0 ≤ sSup V := le_csSup hbdd h0V
    obtain ⟨N', hN'⟩ := eventually_atTop.1 (hαt.eventually_gt_atTop (‖p‖ + 1))
    have hlv : lastVisit (fun t => η '' Icc 0 t) α T = sSup V := rfl
    rw [hlv] at hp ⊢
    refine ⟨max (sSup V) N', isCompact_Icc.image_of_continuousOn (hαc.mono fun v hv => hu0.trans hv.1), ?_, ?_⟩
    · rintro ⟨w, hw, hpw⟩
      have hwV : w ∈ V := ⟨hu0.trans hw.1, hpw ▸ hpR⟩
      have hwu : w = sSup V := le_antisymm (le_csSup hbdd hwV) hw.1
      exact hp (by rw [← hpw, hwu])
    · intro w hw hwn hnot
      have hwN : w < N' := by
        by_contra hle
        exact absurd hwn (not_lt.2 (hN' w (not_lt.1 hle)).le)
      have hlt : w < sSup V := by
        by_contra hle
        exact hnot ⟨w, ⟨not_lt.1 hle, hwN.le.trans (le_max_right _ _)⟩, rfl⟩
      obtain ⟨v₀, hv₀, hwv₀⟩ := exists_lt_of_lt_csSup hne hlt
      exact hrev T w hw v₀ hv₀.1 hwv₀.le hv₀.2
  obtain ⟨V₁, hK₁, hp₁, hv₁⟩ := key α₁ hP.cont₁ hP.tendsto₁ hrev₁ hyR h₁
  obtain ⟨V₂, hK₂, hp₂, hv₂⟩ := key α₂ hP.cont₂ hP.tendsto₂ hrev₂ (hP.seed ▸ hyR) h₂
  have hKc : IsClosed ((α₁ '' Icc (lastVisit (fun t => η '' Icc 0 t) α₁ T) V₁) ∪
      α₂ '' Icc (lastVisit (fun t => η '' Icc 0 t) α₂ T) V₂) := (hK₁.union hK₂).isClosed
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl p (by
    rintro (h | h)
    · exact hp₁ h
    · exact hp₂ h)
  refine ⟨min r₀ 1, lt_min hr₀ one_pos, fun z ⟨hzF, hzb⟩ => ?_⟩
  have hzK := hball (ball_subset_ball (min_le_left _ _) hzb)
  have hzn : ‖z‖ < ‖p‖ + 1 := by
    have h1 : dist z p < 1 := lt_of_lt_of_le hzb (min_le_right _ _)
    have h2 := norm_le_norm_add_norm_sub' z p
    rw [dist_eq_norm] at h1
    linarith [norm_sub_rev z p]
  rw [hP.frontier_eq] at hzF
  rcases hzF with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact hv₁ w hw hzn fun h => hzK (Or.inl h)
  · exact hv₂ w hw hzn fun h => hzK (Or.inr h)

end InteractingSLE.Sec7.R5Out
