/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.WallOrdBasic
import InteractingSLE.Spec.Sec7.R5WallOuterGeom
import InteractingSLE.Spec.Sec7.R5OutWallOrder

/-!
# Consumer adapters for the corrected wall order of an outer pocket

Packet PROVE-WALL-ORDER. `R5Out.exists_ball_frontier_subset_range_of_wallOrder(Inf)` (PROVE-R5-OUTER) turns the clipped
orders of the two walls into "near a visited non-attachment point `p`, the pocket frontier is visited", and
`R5Wall.eventually_mem_freeNear` turns that into the protected access `freeNear`. On an outer wall only the corrected
order off the forbidden side `S` holds (`WallOrdRefute.lean`), and the frontier near `p` may contain never-visited
outer-bulge points. The corrected forms:

* **`exists_ball_frontier_subset_of_wallOrderOff`**, **`exists_ball_frontier_subset_of_wallOrderInfOff`**: near `p`
  every frontier point is visited **or on the forbidden side** (`negInv z ∈ S`);
* **`eventually_mem_freeNear_off`**: the protected access from "frontier near `p` in `K ∪ F`" for an open forbidden set
  `F` whose frontier near `p` lies in `K`, along an approach that eventually avoids `F`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open InteractingSLE.WangWu (negInv)
open InteractingSLE.Theorem14.SB.FinRel (freeNear)

namespace InteractingSLE.Sec7.WallOrd

open Sec6 PocketJordan

/-- **Near a visited non-attachment point the pocket frontier is visited or forbidden** (bounded pocket; the corrected
form of `R5Out.exists_ball_frontier_subset_range_of_wallOrder`). -/
theorem exists_ball_frontier_subset_of_wallOrderOff {η : ℝ → ℂ} {C S : Set ℂ} {α₁ α₂ : ℝ → ℂ}
    (hP : PocketJordan.IsCfPocket C α₁ α₂)
    (hrev₁ : IsReverseVisitOrderOff S α₁ (fun t => η '' Icc 0 t))
    (hrev₂ : IsReverseVisitOrderOff S α₂ (fun t => η '' Icc 0 t))
    {T : ℝ} (hyR : α₁ 1 ∈ η '' Icc 0 T) {p : ℂ} (hpR : p ∈ η '' Icc 0 T)
    (h₁ : p ≠ α₁ (firstVisit (fun t => η '' Icc 0 t) α₁ T))
    (h₂ : p ≠ α₂ (firstVisit (fun t => η '' Icc 0 t) α₂ T)) :
    ∃ r > 0, ∀ z ∈ frontier C ∩ ball p r, z ∈ η '' Icc 0 T ∨ negInv z ∈ S := by
  have key : ∀ (α : ℝ → ℂ), ContinuousOn α (Icc 0 1) →
      IsReverseVisitOrderOff S α (fun t => η '' Icc 0 t) → α 1 ∈ η '' Icc 0 T →
      p ≠ α (firstVisit (fun t => η '' Icc 0 t) α T) →
      IsCompact (α '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α T)) ∧
        p ∉ α '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α T) ∧
        ∀ w ∈ Icc (0 : ℝ) 1, α w ∉ α '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α T) →
          negInv (α w) ∉ S → α w ∈ η '' Icc 0 T := by
    intro α hαc hrev h1 hp
    set V := {v ∈ Icc (0 : ℝ) 1 | α v ∈ η '' Icc 0 T} with hV
    have h1V : (1 : ℝ) ∈ V := ⟨⟨zero_le_one, le_rfl⟩, h1⟩
    have hne : V.Nonempty := ⟨1, h1V⟩
    have hbdd : BddBelow V := ⟨0, fun v hv => hv.1.1⟩
    have hu1 : sInf V ≤ 1 := csInf_le hbdd h1V
    have hfv : firstVisit (fun t => η '' Icc 0 t) α T = sInf V := rfl
    rw [hfv] at hp ⊢
    refine ⟨isCompact_Icc.image_of_continuousOn (hαc.mono (Icc_subset_Icc_right hu1)), ?_, ?_⟩
    · rintro ⟨w, hw, hpw⟩
      have hwV : w ∈ V := ⟨⟨hw.1, hw.2.trans hu1⟩, hpw ▸ hpR⟩
      have hwu : w = sInf V := le_antisymm hw.2 (csInf_le hbdd hwV)
      exact hp (by rw [← hpw, hwu])
    · intro w hw hnot hS
      have hlt : sInf V < w := by
        by_contra hle
        exact hnot ⟨w, ⟨hw.1, not_lt.1 hle⟩, rfl⟩
      obtain ⟨v₀, hv₀, hv₀w⟩ := exists_lt_of_csInf_lt hne hlt
      exact hrev T v₀ hv₀.1 w hw hv₀w.le hv₀.2 hS
  obtain ⟨hK₁, hp₁, hv₁⟩ := key α₁ hP.cont₁ hrev₁ hyR h₁
  obtain ⟨hK₂, hp₂, hv₂⟩ := key α₂ hP.cont₂ hrev₂ (hP.seed ▸ hyR) h₂
  have hKc : IsClosed ((α₁ '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α₁ T)) ∪
      α₂ '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α₂ T)) := (hK₁.union hK₂).isClosed
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl p (by
    rintro (h | h)
    · exact hp₁ h
    · exact hp₂ h)
  refine ⟨r, hr, fun z ⟨hzF, hzb⟩ => ?_⟩
  have hzK := hball hzb
  by_cases hzS : negInv z ∈ S
  · exact Or.inr hzS
  refine Or.inl ?_
  rw [hP.frontier_eq] at hzF
  rcases hzF with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact hv₁ w hw (fun h => hzK (Or.inl h)) hzS
  · exact hv₂ w hw (fun h => hzK (Or.inr h)) hzS

/-- **Near a visited non-attachment point the pocket frontier is visited or forbidden** (pocket opening at the flow
seed; the corrected form of `R5Out.exists_ball_frontier_subset_rangeInf_of_wallOrder`). -/
theorem exists_ball_frontier_subset_of_wallOrderInfOff {η : ℝ → ℂ} {C S : Set ℂ} {α₁ α₂ : ℝ → ℂ}
    (hP : PocketJordan.IsCfPocketInf C α₁ α₂) (hη : ContinuousOn η (Ici 0))
    (hrev₁ : IsReverseVisitOrderInfOff S α₁ (fun t => η '' Icc 0 t))
    (hrev₂ : IsReverseVisitOrderInfOff S α₂ (fun t => η '' Icc 0 t))
    {T : ℝ} (hyR : α₁ 0 ∈ η '' Icc 0 T) {p : ℂ} (hpR : p ∈ η '' Icc 0 T)
    (h₁ : p ≠ α₁ (lastVisit (fun t => η '' Icc 0 t) α₁ T))
    (h₂ : p ≠ α₂ (lastVisit (fun t => η '' Icc 0 t) α₂ T)) :
    ∃ r > 0, ∀ z ∈ frontier C ∩ ball p r, z ∈ η '' Icc 0 T ∨ negInv z ∈ S := by
  have hRb : Bornology.IsBounded (η '' Icc 0 T) :=
    (isCompact_Icc.image_of_continuousOn (hη.mono fun t ht => ht.1)).isBounded
  obtain ⟨M, hM⟩ := hRb.exists_norm_le
  have key : ∀ (α : ℝ → ℂ), ContinuousOn α (Ici 0) → Tendsto (fun v => ‖α v‖) atTop atTop →
      IsReverseVisitOrderInfOff S α (fun t => η '' Icc 0 t) → α 0 ∈ η '' Icc 0 T →
      p ≠ α (lastVisit (fun t => η '' Icc 0 t) α T) →
      ∃ Vp : ℝ, IsCompact (α '' Icc (lastVisit (fun t => η '' Icc 0 t) α T) Vp) ∧
        p ∉ α '' Icc (lastVisit (fun t => η '' Icc 0 t) α T) Vp ∧
        ∀ w ∈ Ici (0 : ℝ), ‖α w‖ < ‖p‖ + 1 →
          α w ∉ α '' Icc (lastVisit (fun t => η '' Icc 0 t) α T) Vp → negInv (α w) ∉ S →
            α w ∈ η '' Icc 0 T := by
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
    · intro w hw hwn hnot hS
      have hwN : w < N' := by
        by_contra hle
        exact absurd hwn (not_lt.2 (hN' w (not_lt.1 hle)).le)
      have hlt : w < sSup V := by
        by_contra hle
        exact hnot ⟨w, ⟨not_lt.1 hle, hwN.le.trans (le_max_right _ _)⟩, rfl⟩
      obtain ⟨v₀, hv₀, hwv₀⟩ := exists_lt_of_lt_csSup hne hlt
      exact hrev T w hw v₀ hv₀.1 hwv₀.le hv₀.2 hS
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
  by_cases hzS : negInv z ∈ S
  · exact Or.inr hzS
  refine Or.inl ?_
  rw [hP.frontier_eq] at hzF
  rcases hzF with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact hv₁ w hw hzn (fun h => hzK (Or.inl h)) hzS
  · exact hv₂ w hw hzn (fun h => hzK (Or.inr h)) hzS

/-- **The protected access with a forbidden side** (corrected form of `R5Wall.eventually_mem_freeNear`): if near `p`
the frontier of the open pocket `C` lies in `K ∪ F`, the open forbidden set `F` has its frontier near `p` in `K`, and
the approach `f` eventually lies in `ℍ ∩ (C ∖ K)` off `F`, then it eventually lies in `freeNear E K p r` for every set
`E` missing `C`. -/
theorem eventually_mem_freeNear_off {C K E F : Set ℂ} (hCo : IsOpen C) (hE : ∀ z ∈ C, z ∉ E) (hFo : IsOpen F)
    {p : ℂ} {r : ℝ} (hfr : frontier C ∩ ball p r ∩ H ⊆ K ∪ F) (hFfr : frontier F ∩ ball p r ∩ H ⊆ K)
    {α : Type*} {l : Filter α} {f : α → ℂ} (hf : Tendsto f l (𝓝 p))
    (hfC : ∀ᶠ y in l, f y ∈ H ∩ (C \ K) ∧ f y ∉ F) (hr : 0 < r) : ∀ᶠ y in l, f y ∈ freeNear E K p r := by
  filter_upwards [hfC, hf (ball_mem_nhds p hr)] with y hy hyb
  have hmem : f y ∈ (H \ K) ∩ ball p r := ⟨⟨hy.1.1, hy.1.2.2⟩, hyb⟩
  refine ⟨hmem, ?_⟩
  set S := connectedComponentIn ((H \ K) ∩ ball p r) (f y) with hS
  have hSsub : S ⊆ (H \ K) ∩ ball p r := connectedComponentIn_subset _ _
  have hSpc : IsPreconnected S := isPreconnected_connectedComponentIn
  have hfyS : f y ∈ S := mem_connectedComponentIn hmem
  -- the component misses the forbidden side
  have hSF : ∀ z ∈ S, z ∉ F := by
    intro z hzS hzF
    have hSsubF : S ⊆ F := Sec6.subset_of_isPreconnected_of_disjoint_frontier hSpc hFo ⟨z, hzS, hzF⟩
      (Set.disjoint_left.2 fun w hwS hwF => by
        have hw := hSsub hwS
        exact hw.1.2 (hFfr ⟨⟨hwF, hw.2⟩, hw.1.1⟩))
    exact hy.2 (hSsubF hfyS)
  have hSC : S ⊆ C := by
    refine Sec6.subset_of_isPreconnected_of_disjoint_frontier hSpc hCo ⟨f y, hfyS, hy.1.2.1⟩ ?_
    refine Set.disjoint_left.2 fun z hzS hzF => ?_
    have hz := hSsub hzS
    rcases hfr ⟨⟨hzF, hz.2⟩, hz.1.1⟩ with h | h
    · exact hz.1.2 h
    · exact hSF z hzS h
  exact Set.disjoint_left.2 fun z hzS hzE => hE z (hSC hzS) hzE

end InteractingSLE.Sec7.WallOrd
