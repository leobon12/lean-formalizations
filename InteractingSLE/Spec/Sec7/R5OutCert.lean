/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.WallOrdCover
import InteractingSLE.Spec.Sec7.R7StopInMixedInf

/-! # The certified frontier's attachment and visited neighborhoods -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric
open QuantumZipper (H)
open InteractingSLE.WangWu (negInv)
open scoped NNReal
namespace InteractingSLE.Sec7.R5Out
open Sec6 PocketJordan WangWu Lemma71I R7StopIn PocketCoord

/-- The entire certified wall in the counterflow chart, parametrized from the seed to infinity. -/
def certWall (M : ℝ≥0 → ℂ) (v : ℝ) : ℂ :=
  cfPt (toDisc (Lemma71I.realPath M) (1 / (1 + v)))

/-- The full certified wall is proper, continuous, and starts at zero. -/
theorem certWall_props {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M) :
    ContinuousOn (certWall M) (Ici 0) ∧
      Tendsto (fun v => ‖certWall M v‖) atTop atTop ∧ certWall M 0 = 0 := by
  obtain ⟨hc, -, ht, -, -⟩ := crosscut_arcInf_props hM.isProperArc.isDiscCrosscut_toDisc
    (show (0 : ℝ) < 1 from zero_lt_one) le_rfl
  refine ⟨hc, ht, ?_⟩
  simp only [certWall, add_zero, div_one, hM.isProperArc.isDiscCrosscut_toDisc.one, cfPt_one]

/-- A physical point of the certified frontier in the half-plane is on the full certified wall. -/
theorem mem_certWall_of_negInv_mem {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M) {z : ℂ}
    (hzH : z ∈ H) (hz : negInv z ∈ range M) : z ∈ certWall M '' Ici 0 := by
  obtain ⟨t, ht⟩ := hz
  have ht0 : 0 < t := by
    refine lt_of_le_of_ne (show 0 ≤ t from zero_le) fun h => ?_
    have h0 : negInv z = 0 := by rw [← ht, ← h, hM.2.2.1]
    exact (WangWu.ne_zero_of_mem_H (negInv_mem_H hzH)) h0
  obtain ⟨-, -, -, him, -⟩ := crosscut_arcInf_props hM.isProperArc.isDiscCrosscut_toDisc
    (show (0 : ℝ) < 1 from zero_lt_one) le_rfl
  change z ∈ (fun v : ℝ => cfPt (toDisc (Lemma71I.realPath M) (1 / (1 + v)))) '' Ici 0
  rw [him]
  refine ⟨toDisc (Lemma71I.realPath M) (discTime t), ⟨_, ⟨?_, (discTime_mem_Icc t).2⟩, rfl⟩, ?_⟩
  · exact div_pos (by exact_mod_cast ht0) (by positivity)
  · rw [toDisc_realPath_discTime, cfPt_cayley (H_subset_Hbar' (hM.2.2.2.1 t ht0))
      (WangWu.ne_zero_of_mem_H (hM.2.2.2.1 t ht0)), ht, negInv_negInv]

/-- Reverse visitation of the certified flow line gives the order on its full physical wall. -/
theorem certWall_rev {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M) {η : ℝ → ℂ}
    (hη0 : η 0 = 0) (hrev : IsWallReverseVisit M η) :
    IsReverseVisitOrderInf (certWall M) (fun t => η '' Icc 0 t) := by
  intro t v₁ hv₁ v₂ hv₂ h12 hvis
  have h1 : (0 : ℝ) < 1 + v₁ := by linarith [mem_Ici.1 hv₁]
  have hd : ∀ v ∈ Ici (0 : ℝ), 1 / (1 + v) ∈ Ioc (0 : ℝ) 1 :=
    fun v hv => div_one_add_mem zero_lt_one hv
  exact wall_rev hM hη0 hrev (hd v₂ hv₂) (hd v₁ hv₁)
    (div_le_div_of_nonneg_left zero_le_one h1 (by linarith)) hvis

/-- Near a visited point off its attachment, a proper reverse-visited wall is visited. -/
theorem exists_ball_wall_subset_trace {α η : ℝ → ℂ}
    (hαc : ContinuousOn α (Ici 0)) (hαt : Tendsto (fun v => ‖α v‖) atTop atTop)
    (hηc : ContinuousOn η (Ici 0))
    (hrev : IsReverseVisitOrderInf α (fun t => η '' Icc 0 t))
    {T : ℝ} (h0 : α 0 ∈ η '' Icc 0 T) {p : ℂ} (hpR : p ∈ η '' Icc 0 T)
    (hp : p ≠ α (lastVisit (fun t => η '' Icc 0 t) α T)) :
    ∃ r > 0, α '' Ici 0 ∩ ball p r ⊆ η '' Icc 0 T := by
  have hRb : Bornology.IsBounded (η '' Icc 0 T) :=
    (isCompact_Icc.image_of_continuousOn (hηc.mono fun t ht => ht.1)).isBounded
  obtain ⟨M, hM⟩ := hRb.exists_norm_le
  set V := {v ∈ Ici (0 : ℝ) | α v ∈ η '' Icc 0 T}
  have h0V : (0 : ℝ) ∈ V := ⟨show (0 : ℝ) ≤ 0 from le_rfl, h0⟩
  have hne : V.Nonempty := ⟨0, h0V⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hαt.eventually_gt_atTop M)
  have hbdd : BddAbove V := ⟨N, fun v hv => by
    by_contra hlt
    exact absurd (hM _ hv.2) (not_le.2 (hN v (not_le.1 hlt).le))⟩
  have hu0 : 0 ≤ sSup V := le_csSup hbdd h0V
  obtain ⟨N', hN'⟩ := eventually_atTop.1 (hαt.eventually_gt_atTop (‖p‖ + 1))
  change p ≠ α (sSup V) at hp
  have hK : IsCompact (α '' Icc (sSup V) (max (sSup V) N')) :=
    isCompact_Icc.image_of_continuousOn (hαc.mono fun v hv => hu0.trans hv.1)
  have hpK : p ∉ α '' Icc (sSup V) (max (sSup V) N') := by
    rintro ⟨w, hw, hpw⟩
    have hwV : w ∈ V := ⟨hu0.trans hw.1, hpw ▸ hpR⟩
    have hwu : w = sSup V := le_antisymm (le_csSup hbdd hwV) hw.1
    exact hp (by rw [← hpw, hwu])
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl p hpK
  refine ⟨min r₀ 1, lt_min hr₀ one_pos, ?_⟩
  rintro _ ⟨⟨w, hw, rfl⟩, hwb⟩
  have hwK := hball (ball_subset_ball (min_le_left _ _) hwb)
  have hwn : ‖α w‖ < ‖p‖ + 1 := by
    have h1 : dist (α w) p < 1 := lt_of_lt_of_le hwb (min_le_right _ _)
    have h2 := norm_le_norm_add_norm_sub' (α w) p
    rw [dist_eq_norm] at h1
    linarith [norm_sub_rev (α w) p]
  have hwN : w < N' := by
    by_contra hle
    exact absurd hwn (not_lt.2 (hN' w (not_lt.1 hle)).le)
  have hlt : w < sSup V := by
    by_contra hle
    exact hwK ⟨w, ⟨not_lt.1 hle, hwN.le.trans (le_max_right _ _)⟩, rfl⟩
  obtain ⟨v₀, hv₀, hwv₀⟩ := exists_lt_of_lt_csSup hne hlt
  exact hrev T w hw v₀ hv₀.1 hwv₀.le hv₀.2

/-- The certified frontier, off its own attachment, is visited near every visited landing. -/
theorem exists_ball_cert_frontier_subset_trace {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M)
    {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit M η) {T : ℝ} (hT : 0 ≤ T) {p : ℂ}
    (hpR : p ∈ η '' Icc 0 T)
    (hp : p ≠ certWall M (lastVisit (fun t => η '' Icc 0 t) (certWall M) T)) :
    ∃ r > 0, ∀ z ∈ ball p r, z ∈ H → negInv z ∈ range M → z ∈ η '' Icc 0 T := by
  obtain ⟨hc, ht, hzero⟩ := certWall_props hM
  obtain ⟨r, hr, hball⟩ := exists_ball_wall_subset_trace hc ht hηc (certWall_rev hM hη0 hrev)
    ⟨0, ⟨le_rfl, hT⟩, hη0.trans hzero.symm⟩ hpR hp
  exact ⟨r, hr, fun z hz hzH hzM => hball ⟨mem_certWall_of_negInv_mem hM hzH hzM, hz⟩⟩

/-- R97(a) on the forbidden right side: its frontier is visited near the landing. -/
theorem exists_ball_forbidden_right_frontier_subset_trace {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M)
    {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit M η) {T : ℝ} (hT : 0 ≤ T) {p : ℂ}
    (hpR : p ∈ η '' Icc 0 T)
    (hp : p ≠ certWall M (lastVisit (fun t => η '' Icc 0 t) (certWall M) T)) :
    ∃ r > 0, frontier (negInv '' rightSideOf (range M)) ∩ ball p r ∩ H ⊆ η '' Icc 0 T := by
  obtain ⟨r, hr, hball⟩ := exists_ball_cert_frontier_subset_trace hM hηc hη0 hrev hT hpR hp
  exact ⟨r, hr, fun z hz => hball z hz.1.2 hz.2 ((forbidden_right hM).2 z hz.1.1 hz.2)⟩

/-- R97(a) on the forbidden left side. -/
theorem exists_ball_forbidden_left_frontier_subset_trace {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M)
    {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit M η) {T : ℝ} (hT : 0 ≤ T) {p : ℂ}
    (hpR : p ∈ η '' Icc 0 T)
    (hp : p ≠ certWall M (lastVisit (fun t => η '' Icc 0 t) (certWall M) T)) :
    ∃ r > 0, frontier (negInv '' leftSideOf (range M)) ∩ ball p r ∩ H ⊆ η '' Icc 0 T := by
  obtain ⟨r, hr, hball⟩ := exists_ball_cert_frontier_subset_trace hM hηc hη0 hrev hT hpR hp
  exact ⟨r, hr, fun z hz => hball z hz.1.2 hz.2 ((forbidden_left hM).2 z hz.1.1 hz.2)⟩

end InteractingSLE.Sec7.R5Out
