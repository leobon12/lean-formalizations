/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkNormPair
import InteractingSLE.Spec.Supplement.WalkSideDom

/-!
# Prefix domains and continuous identifications of incident sides

The domain-disjointness lemma is bookkeeping for the already proved capped
program theorem. `SideIdentification` is the precise remaining boundary
geometry: the two inverses agree through a continuous real-boundary map on
the designated incident collars. Such an identification supplies all local
transition conjuncts, with no derivative-log hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntBridge

open WalkBdry Exist.StagedLaw

/-- The prefix chart of a recorded walk piece avoids its prefix set. -/
theorem prefixChart_disjoint_prefixSet {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1
        (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k))
    {pre post : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ pc :: post)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < pc.2.2) :
    Disjoint ((prefixChart pc τ).dom : Set ℂ) (prefixSet pre pc τ) := by
  let w := boundaryWalkSpec b jumps θ right
  obtain ⟨ℓ, hℓ, θ', hl, hpre, hpc⟩ :=
    WalkSide.exists_launch_of_pieces_eq (κ := κ) (b := b) (jumps := jumps)
      w D w.2.2.length hs
  have hins := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) w D hl).1
  obtain ⟨hθ, ht⟩ := WalkLeaf.boundaryWalkSpec_inl hins
  have hins' : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤)) := by
    simpa only [hθ, ht] using hins
  rw [ht] at hpc
  have hτ' : (τ : ℝ≥0∞) < min ⊤ (D ℓ).2 := by
    rw [hpc] at hτ
    exact hτ
  have hne : (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [hl]
    exact Option.some_ne_none _
  have hd := WalkSide.prefixChartDomStatement κ b jumps w D ℓ θ τ hℓ hins' hne
    (hτ'.trans_le (min_le_right _ _)) hreg
  let E : ℕ → Unit → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun k _ => D k
  have hset := WalkSide.prefixSet_eq_stageSet (κ := κ) (b := b) (jumps := jumps)
    E () hℓ.le hins' hl (hD ℓ) hτ'
  have hchart := WalkSide.prefixChart_eq_chart (κ := κ) (b := b) (jumps := jumps)
    E () hℓ.le hins' hl (hD ℓ) hτ'
  rw [hpc, ← hpre, hset, hchart]
  exact hd.mono_right inter_subset_left

/-- Continuous identification of the two designated incident boundary
collars. Constructing this data is the new prime-end/planar-side input. -/
structure SideIdentification (cR cL : Chart) (yR yL : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  map : ℂ → ℂ
  continuous : ContinuousOn map (Hbar ∩ ball (yR : ℂ) radius)
  real : ∀ z ∈ ball (yR : ℂ) radius, z.im = 0 → (map z).im = 0
  at_base : map (yR : ℂ) = (yL : ℂ)
  inv_agree : ∀ z ∈ H ∩ ball (yR : ℂ) radius,
    map z ∈ H ∧ cR.2.1 z = cL.2.1 (map z)

/-- An incident-side identification implies the entire local transition
conclusion, including the designated landing coordinate. -/
theorem SideIdentification.local_transition {cR cL : Chart} {yR yL : ℝ}
    (G : SideIdentification cR cL yR yL) (hcL : cL.IsConformal) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ z ∈ H ∩ ball (yR : ℂ) δ, cR.2.1 z ∈ cL.dom) ∧
      (∀ z ∈ ball (yR : ℂ) δ, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
        Tendsto (fun w => cL.1 (cR.2.1 w)) (𝓝[H] z) (𝓝 v)) ∧
      Tendsto (fun w => cL.1 (cR.2.1 w))
        (𝓝[H] (yR : ℂ)) (𝓝 (yL : ℂ)) := by
  have he : ∀ z ∈ H ∩ ball (yR : ℂ) G.radius,
      cL.1 (cR.2.1 z) = G.map z := by
    intro z hz
    rw [(G.inv_agree z hz).2, hcL.2.2 _ (G.inv_agree z hz).1]
  have hlim : ∀ z ∈ ball (yR : ℂ) G.radius, z.im = 0 →
      Tendsto (fun w => cL.1 (cR.2.1 w)) (𝓝[H] z) (𝓝 (G.map z)) := by
    intro z hz hz0
    have hid : Tendsto (fun w : ℂ => w) (𝓝[H] z)
        (𝓝[Hbar ∩ ball (yR : ℂ) G.radius] z) := by
      refine tendsto_nhdsWithin_iff.2 ⟨nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with w hw hwb
      exact ⟨le_of_lt (show 0 < w.im from hw), hwb⟩
    have hm := (G.continuous z ⟨show 0 ≤ z.im from hz0.ge, hz⟩).tendsto.comp hid
    refine hm.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with w hw hwb
    exact (he w ⟨hw, hwb⟩).symm
  refine ⟨G.radius, G.radius_pos, fun z hz => ?_,
    fun z hz hz0 => ⟨G.map z, G.real z hz hz0, hlim z hz hz0⟩, ?_⟩
  · rw [(G.inv_agree z hz).2]
    exact hcL.inv_mem_dom (G.inv_agree z hz).1
  · have h := hlim (yR : ℂ) (mem_ball_self G.radius_pos) (Complex.ofReal_im yR)
    rwa [G.at_base] at h

end InteractingSLE.Theorem14.WalkIntBridge
