/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS2

/-!
# Lemma S2's lift: two topological tools

Packet PROVE-T14-SB5. Two generic facts used by the one-sided lift of Lemma S2 (supplement pp. 578–579,
`source/spec/p577-624.md` L49: "These local limits give the continuous lift"):

* **`exists_tendsto_of_cluster`** — a map `F`, continuous on `Y`, bounded near `z ∈ closure Y`, all of whose cluster
  values at `z` (along `Y`) lie in a finite set `Φ`, has a limit at `z` along `Y`, provided `Y` is locally connected
  at `z` (arbitrarily small preconnected pieces of `Y` contain a whole trace `Y ∩ ball z δ`). This is the source's
  "two distinct fiber points would separate those germs": a connected set of values near a finite set stays near one
  of its points.
* **`leftSide_locallyConnected`** — the left side of a proper curve is locally connected at every point of the closed
  curve ("straighten a small subarc of the simple witness by the Jordan-arc collar theorem"): through the inversion
  of `Supp9B` the closed curve is a Jordan curve, and the Schoenflies theorem carries the open unit disc onto the
  inverted left side.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### Limits from finitely many cluster values -/

section Cluster

/-- The points of a finite set are uniformly separated. -/
theorem exists_sep_of_finite {Φ : Set ℂ} (hΦ : Φ.Finite) :
    ∃ ρ > 0, ∀ y ∈ Φ, ∀ y' ∈ Φ, y ≠ y' → 2 * ρ < dist y y' := by
  set P : Set (ℂ × ℂ) := {q | q.1 ∈ Φ ∧ q.2 ∈ Φ ∧ q.1 ≠ q.2} with hPdef
  have hP : P.Finite := (hΦ.prod hΦ).subset fun q hq => ⟨hq.1, hq.2.1⟩
  rcases P.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun y hy y' hy' hyy => ?_⟩
    have hmem : (y, y') ∈ P := ⟨hy, hy', hyy⟩
    rw [he] at hmem
    exact absurd hmem (notMem_empty _)
  · obtain ⟨q, hq, hmin⟩ := exists_min_image P (fun q => dist q.1 q.2) hP hne
    have hpos : 0 < dist q.1 q.2 := dist_pos.2 hq.2.2
    refine ⟨dist q.1 q.2 / 3, by positivity, fun y hy y' hy' hyy => ?_⟩
    have := hmin (y, y') ⟨hy, hy', hyy⟩
    simp only at this
    linarith

/-- **A limit from finitely many cluster values and local connectedness.** -/
theorem exists_tendsto_of_cluster {F : ℂ → ℂ} {Y Φ : Set ℂ} {z : ℂ} (hΦ : Φ.Finite) (hz : z ∈ closure Y)
    (hF : ContinuousOn F Y) {ε₀ M : ℝ} (hε₀ : 0 < ε₀) (hM : ∀ w ∈ Y ∩ ball z ε₀, ‖F w‖ ≤ M)
    (hcl : ∀ y, MapClusterPt y (𝓝[Y] z) F → y ∈ Φ)
    (hlc : ∀ ε > 0, ∃ δ > 0, ∃ V ⊆ Y ∩ ball z ε, IsPreconnected V ∧ Y ∩ ball z δ ⊆ V) :
    ∃ y, Tendsto F (𝓝[Y] z) (𝓝 y) := by
  have : (𝓝[Y] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
  have hYb : Y ∩ ball z ε₀ ∈ 𝓝[Y] z := inter_mem_nhdsWithin Y (ball_mem_nhds z hε₀)
  have key : ∀ G : Filter ℂ, G.NeBot → G ≤ 𝓝[Y] z → ∃ y ∈ Φ, MapClusterPt y G F := by
    intro G hG hGle
    have hmap : map F G ≤ 𝓟 (closedBall 0 M) := by
      rw [le_principal_iff, mem_map]
      filter_upwards [hGle hYb] with w hw
      exact mem_closedBall_zero_iff.2 (hM w hw)
    obtain ⟨y, -, hy⟩ := (isCompact_closedBall (0 : ℂ) M) hmap
    exact ⟨y, hcl y (ClusterPt.mono hy (map_mono hGle)), hy⟩
  obtain ⟨y₀, hy₀Φ, hy₀⟩ := key _ inferInstance le_rfl
  obtain ⟨ρ₀, hρ₀, hsep⟩ := exists_sep_of_finite hΦ
  refine ⟨y₀, Metric.tendsto_nhds.2 fun r hr => ?_⟩
  set ρ := min r ρ₀ with hρdef
  have hρ : 0 < ρ := lt_min hr hρ₀
  have hρr : ρ ≤ r := min_le_left _ _
  have hρρ₀ : ρ ≤ ρ₀ := min_le_right _ _
  -- eventually the values are near `Φ`
  have hU : ∀ᶠ w in 𝓝[Y] z, ∃ y ∈ Φ, F w ∈ ball y ρ := by
    by_contra hne
    rw [Filter.not_eventually, Filter.frequently_iff_neBot] at hne
    obtain ⟨y, hyΦ, hy⟩ := key _ hne inf_le_left
    have hC : IsClosed {v : ℂ | ∀ y ∈ Φ, v ∉ ball y ρ} := by
      have : {v : ℂ | ∀ y ∈ Φ, v ∉ ball y ρ} = ⋂ y ∈ Φ, (ball y ρ)ᶜ := by ext v; simp
      rw [this]
      exact isClosed_biInter fun y _ => isOpen_ball.isClosed_compl
    have hmem : {v : ℂ | ∀ y ∈ Φ, v ∉ ball y ρ} ∈ map F (𝓝[Y] z ⊓ 𝓟 {w | ¬∃ y ∈ Φ, F w ∈ ball y ρ}) := by
      rw [mem_map]
      exact mem_inf_of_right (mem_principal.2 fun w hw y' hy' h' => hw ⟨y', hy', h'⟩)
    have hcl' := hC.closure_eq ▸ ClusterPt.mem_closure_of_mem hy _ hmem
    exact hcl' y hyΦ (mem_ball_self hρ)
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ := Metric.mem_nhdsWithin_iff.1 hU
  obtain ⟨δ, hδ, V, hVs, hVc, hVδ⟩ := hlc δ₁ hδ₁
  have hFV : IsPreconnected (F '' V) := hVc.image F (hF.mono fun w hw => (hVs hw).1)
  set u := ball y₀ ρ with hu
  set v := ⋃ y ∈ Φ \ {y₀}, ball y ρ with hv
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    intro x hxu hxv
    rw [hv, mem_iUnion₂] at hxv
    obtain ⟨y, ⟨hyΦ, hyne⟩, hxy⟩ := hxv
    have h1 := hsep y₀ hy₀Φ y hyΦ (Ne.symm hyne)
    have h2 := dist_triangle y₀ x y
    have h3 : dist x y₀ < ρ := hxu
    have h4 : dist x y < ρ := hxy
    rw [dist_comm] at h3
    linarith
  have hsub : F '' V ⊆ u ∪ v := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hyΦ, hy⟩ := hδ₁s ⟨(hVs hw).2, (hVs hw).1⟩
    by_cases hyy : y = y₀
    · exact Or.inl (by rw [hu, ← hyy]; exact hy)
    · exact Or.inr (mem_iUnion₂.2 ⟨y, ⟨hyΦ, hyy⟩, hy⟩)
  rcases hFV.subset_or_subset isOpen_ball (isOpen_biUnion fun _ _ => isOpen_ball) huv hsub with h | h
  · filter_upwards [inter_mem_nhdsWithin Y (ball_mem_nhds z hδ)] with w hw
    have hwV : w ∈ V := hVδ ⟨hw.1, hw.2⟩
    exact lt_of_lt_of_le (h ⟨w, hwV, rfl⟩) hρr
  · exfalso
    have hmem : v ∈ map F (𝓝[Y] z) := by
      rw [mem_map]
      filter_upwards [inter_mem_nhdsWithin Y (ball_mem_nhds z hδ)] with w hw
      exact h ⟨w, hVδ ⟨hw.1, hw.2⟩, rfl⟩
    have hy₀v := ClusterPt.mem_closure_of_mem hy₀ _ hmem
    have hvc : closure v ⊆ ⋃ y ∈ Φ \ {y₀}, closedBall y ρ :=
      closure_minimal (iUnion₂_mono fun _ _ => ball_subset_closedBall)
        (((hΦ.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closedBall))
    obtain ⟨y, ⟨hyΦ, hyne⟩, hy⟩ := mem_iUnion₂.1 (hvc hy₀v)
    have h1 := hsep y₀ hy₀Φ y hyΦ (Ne.symm hyne)
    have h2 : dist y₀ y ≤ ρ := hy
    linarith

end Cluster

/-! ### Local connectedness of the left side -/

section LocalConn

variable {γ : ℝ≥0 → ℂ}

/-- **The left side of a proper curve is locally connected along the closed curve**: near every point `z` of the
closed curve, small preconnected pieces of the left side contain all its points near `z`. -/
theorem leftSide_locallyConnected (hγ : Supp9B.IsProperCurve γ) (h0 : (γ 0).im = 0) {z : ℂ}
    (hz : z ∈ seedRayClosure γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ V ⊆ Supp9B.leftSide γ ∩ ball z ε, IsPreconnected V ∧ Supp9B.leftSide γ ∩ ball z δ ⊆ V := by
  obtain ⟨U, V', hUo, hVo, hUb, hUc, -, hdisj, hun, -, -, hLU, -, hUL, -, hpL⟩ :=
    Supp9B.exists_jordan_sides' hγ h0
  set p := Supp9B.rightRef γ with hp
  have hJ := Supp9B.isJordanCurve_invCurve hγ h0
  have hx₁ : Supp9B.inv p (γ 0 - 1 - I) ∈ U := hLU ⟨_, Supp9B.leftRef_mem_leftSide hγ.2.2.1 h0, rfl⟩
  have hUJ : U ⊆ (Supp9B.invCurve γ)ᶜ := hun ▸ subset_union_left
  have hUeq : connectedComponentIn (Supp9B.invCurve γ)ᶜ (Supp9B.inv p (γ 0 - 1 - I)) = U := by
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hUo hVo hdisj
        (hun ▸ connectedComponentIn_subset _ _) ⟨_, mem_connectedComponentIn (hUJ hx₁), hx₁⟩
    · exact hUc.subset_connectedComponentIn hx₁ hUJ
  obtain ⟨h, -, hhb, -, -⟩ := InteractingSLE.schoenflies_plane hJ (hUJ hx₁) (hUeq ▸ hUb)
  rw [hUeq] at hhb
  have hzp : z ≠ p := fun e => Supp9B.rightRef_notMem hγ.2.2.1 h0 (by rw [hp] at e; rw [← e]; exact hz)
  set q := Supp9B.inv p z with hq
  have hq0 : q ≠ 0 := Supp9B.inv_apply_ne_zero hzp
  -- `uninv` near `q`
  obtain ⟨ε₁, hε₁, hε₁s⟩ : ∃ ε₁ > 0, ∀ w ∈ ball q ε₁, w ≠ 0 ∧ Supp9B.uninv p w ∈ ball z ε := by
    have hc := Supp9B.continuousAt_uninv (p := p) hq0
    have hz' : Supp9B.uninv p q = z := Supp9B.uninv_inv p z
    rw [ContinuousAt, hz'] at hc
    obtain ⟨ε₂, hε₂, hs⟩ := Metric.mem_nhds_iff.1 (hc (ball_mem_nhds z hε))
    refine ⟨min ε₂ ‖q‖, lt_min hε₂ (norm_pos_iff.2 hq0), fun w hw => ⟨fun hw0 => ?_, hs (ball_subset_ball
      (min_le_left _ _) hw)⟩⟩
    have : dist w q < ‖q‖ := lt_of_lt_of_le hw (min_le_right _ _)
    rw [hw0, dist_comm, dist_zero_right] at this
    exact lt_irrefl _ this
  -- `h` near `h⁻¹ q`
  set q₀ := h.symm q with hq₀
  obtain ⟨η, hη, hηs⟩ : ∃ η > 0, ∀ u ∈ ball q₀ η, h u ∈ ball q ε₁ := by
    have hc := h.continuous.continuousAt (x := q₀)
    rw [ContinuousAt, hq₀, h.apply_symm_apply] at hc
    obtain ⟨η, hη, hs⟩ := Metric.mem_nhds_iff.1 (hc (ball_mem_nhds q hε₁))
    exact ⟨η, hη, fun u hu => hs hu⟩
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ : ∃ δ₁ > 0, ∀ w ∈ ball q δ₁, h.symm w ∈ ball q₀ η := by
    have hc := h.symm.continuous.continuousAt (x := q)
    rw [ContinuousAt] at hc
    obtain ⟨δ₁, hδ₁, hs⟩ := Metric.mem_nhds_iff.1 (hc (ball_mem_nhds q₀ hη))
    exact ⟨δ₁, hδ₁, fun w hw => hs hw⟩
  obtain ⟨δ, hδ, hδs⟩ : ∃ δ > 0, ∀ w ∈ ball z δ, Supp9B.inv p w ∈ ball q δ₁ := by
    have hc := Supp9B.continuousAt_inv (p := p) hzp
    rw [ContinuousAt] at hc
    obtain ⟨δ, hδ, hs⟩ := Metric.mem_nhds_iff.1 (hc (ball_mem_nhds q hδ₁))
    exact ⟨δ, hδ, fun w hw => hs hw⟩
  set W := h '' (ball 0 1 ∩ ball q₀ η) with hW
  have hWq : W ⊆ ball q ε₁ := by
    rintro _ ⟨u, hu, rfl⟩
    exact hηs u hu.2
  have hWU : W ⊆ U := by
    rw [← hhb]
    exact image_mono inter_subset_left
  refine ⟨δ, hδ, Supp9B.uninv p '' W, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨hUL ⟨w, hWU hw, rfl⟩, (hε₁s w (hWq hw)).2⟩
  · have hWc : IsPreconnected W :=
      ((convex_ball (0 : ℂ) 1).inter (convex_ball q₀ η)).isPreconnected.image _ h.continuous.continuousOn
    exact hWc.image _ fun w hw => (Supp9B.continuousAt_uninv (hε₁s w (hWq hw)).1).continuousWithinAt
  · rintro w ⟨hwL, hwz⟩
    have hwp : w ≠ p := fun e => hpL (e ▸ hwL)
    have huU : Supp9B.inv p w ∈ U := hLU ⟨w, hwL, rfl⟩
    have hub : h.symm (Supp9B.inv p w) ∈ ball (0 : ℂ) 1 := by
      rw [← hhb] at huU
      obtain ⟨u, hu, hue⟩ := huU
      rw [← hue, h.symm_apply_apply]
      exact hu
    refine ⟨Supp9B.inv p w, ⟨h.symm (Supp9B.inv p w), ⟨hub, hδ₁s _ (hδs w hwz)⟩, h.apply_symm_apply _⟩,
      Supp9B.uninv_inv p w⟩

end LocalConn

end SB

end Theorem14

end InteractingSLE
