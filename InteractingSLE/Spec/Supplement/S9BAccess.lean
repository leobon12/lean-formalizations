/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BOrder
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc

/-!
# Supplement §7.10 / §9: accessibility from the unbounded complementary domain

Packet PROVE-SUPP9-C.

Let `A = fill(ζ([0, s]))` be the filling of a path in the closed upper half-plane started on the real line, and
`U = ℍ \ A` its unbounded complementary domain. The inverse of the mapping-out function `g_A` extends continuously
to `ℍ̄` (`YuanCharacterisation.exists_extension_symm`, from Pommerenke's continuity theorem). Hence every point `p` of
the closure of `U` is the starting point of a continuous injective proper curve whose later points lie in `U`: the
image of a vertical ray from a preimage of `p` (`exists_tail_of_mem_closure`). This is the "injective proper
extension from an active final prime end … the inverse image of a vertical ray in the half-plane chart" of the proof
of Lemma G13 (supplement p. 506), for any compact union of arcs that can be traversed by one path started on `ℝ`.

`exists_path_union` produces such a path for two arcs from real seeds, `γ₁([0, T₁])` and `γ₂([0, T₂])`, joined
along the real segment between their seeds.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp9B

/-! ### Tails from the closure of the unbounded domain -/

section Access

variable {ζ : ℝ → ℂ} {s : ℝ}

/-- **Accessibility.** For the filling `A` of a path in `ℍ̄` started on `ℝ`, every point `p` of the closure of
`ℍ \ A` starts a continuous injective curve, tending to `∞`, whose points after time `0` lie in `ℍ \ A`. -/
theorem exists_tail_of_mem_closure (hs : 0 ≤ s) (hc : ContinuousOn ζ (Icc 0 s))
    (hζH : MapsTo ζ (Icc 0 s) Hbar) (h0 : (ζ 0).im = 0) {p : ℂ}
    (hp : p ∈ closure (H \ fillH (ζ '' Icc 0 s))) :
    ∃ T : ℝ≥0 → ℂ, Continuous T ∧ Function.Injective T ∧ T 0 = p ∧
      (∀ t, 0 < t → T t ∈ H \ fillH (ζ '' Icc 0 s)) ∧ Tendsto (fun t => ‖T t‖) atTop atTop := by
  obtain ⟨F, hF1, hF2, -, hFc, hFi, hFr, -, -, M, hM⟩ :=
    YuanCharacterisation.exists_extension_symm hs hc hζH h0
  set U := H \ fillH (ζ '' Icc 0 s) with hU
  have hA := YuanCharacterisation.isHPHull_fillH_image_of_im hc hs h0
  have hg := ConformalImage.isMapOut_mapOut hA
  have hUF : U ⊆ F '' H := fun z hz => ⟨_, hg.1.2.mapsTo hz, hF2 z hz⟩
  -- the image of `ℍ̄` under `F` is closed
  have hclosed : IsClosed (F '' Hbar) := by
    refine isClosed_of_closure_subset fun z hz => ?_
    set R := ‖z‖ + 1 + M with hR
    set K := Hbar ∩ closedBall (0 : ℂ) R with hK
    have hKc : IsCompact K := (isCompact_closedBall 0 R).inter_left QuantumZipper.isClosed_Hbar
    have hFK : IsCompact (F '' K) := hKc.image_of_continuousOn (hFc.mono inter_subset_left)
    have hzK : z ∈ closure (F '' K) := by
      rw [Metric.mem_closure_iff] at hz ⊢
      intro ε hε
      obtain ⟨_, ⟨w, hw, rfl⟩, hd⟩ := hz (min ε 1) (lt_min hε one_pos)
      refine ⟨F w, ⟨w, ⟨hw, ?_⟩, rfl⟩, hd.trans_le (min_le_left _ _)⟩
      have h1 := hM w hw
      have h2 : dist z (F w) < 1 := hd.trans_le (min_le_right _ _)
      rw [dist_eq_norm] at h2
      have h3 : ‖w‖ ≤ ‖F w‖ + ‖F w - w‖ := by
        calc ‖w‖ = ‖F w - (F w - w)‖ := by ring_nf
          _ ≤ ‖F w‖ + ‖F w - w‖ := norm_sub_le _ _
      have h4 : ‖F w‖ ≤ ‖z‖ + 1 := by
        have := norm_sub_norm_le (F w) z
        rw [norm_sub_rev] at this
        linarith
      rw [mem_closedBall, dist_zero_right]
      linarith
    exact image_mono inter_subset_left (hFK.isClosed.closure_subset hzK)
  have hpF : p ∈ F '' Hbar :=
    hclosed.closure_subset (closure_mono ((hUF.trans (image_mono QuantumZipper.H_subset_Hbar))) hp)
  obtain ⟨w, hw, rfl⟩ := hpF
  -- the vertical ray from `w`
  set ray : ℝ≥0 → ℂ := fun t => w + ((t : ℝ) : ℂ) * I with hray
  have hrayc : Continuous ray := by rw [hray]; fun_prop
  have hrayH : ∀ t, ray t ∈ Hbar := fun t => by
    show 0 ≤ (w + ((t : ℝ) : ℂ) * I).im
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero]
    exact add_nonneg hw t.2
  have hrayH' : ∀ t, 0 < t → ray t ∈ H := fun t ht => by
    show 0 < (w + ((t : ℝ) : ℂ) * I).im
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero]
    exact add_pos_of_nonneg_of_pos hw (by exact_mod_cast ht)
  refine ⟨fun t => F (ray t), hFc.comp_continuous hrayc hrayH, fun t t' htt' => ?_, by simp [hray],
    fun t ht => (hF1 _ (hrayH' t ht)).1, ?_⟩
  · -- injectivity
    have hray_inj : Function.Injective ray := fun t t' h => by
      have := congrArg Complex.im h
      simp only [hray, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero,
        add_zero, add_right_inj] at this
      exact NNReal.coe_injective this
    by_cases ht : 0 < t <;> by_cases ht' : 0 < t'
    · exact hray_inj (hFi (hrayH' t ht) (hrayH' t' ht') htt')
    · have ht'0 : t' = 0 := le_antisymm (not_lt.1 ht') zero_le
      subst ht'0
      by_cases hwH : w ∈ H
      · exact hray_inj (hFi (hrayH' t ht) (by simpa [hray] using hwH) htt')
      · have hw0 : w.im = 0 := le_antisymm (not_lt.1 hwH) hw
        have hr0 : ray 0 = w := by simp [hray]
        exact absurd ⟨ray t, hrayH' t ht, htt'.trans (by show F (ray 0) = F w; rw [hr0])⟩ (hFr w hw0)
    · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) zero_le
      subst ht0
      by_cases hwH : w ∈ H
      · exact hray_inj (hFi (by simpa [hray] using hwH) (hrayH' t' ht') htt')
      · have hw0 : w.im = 0 := le_antisymm (not_lt.1 hwH) hw
        have hr0 : ray 0 = w := by simp [hray]
        exact absurd ⟨ray t', hrayH' t' ht', htt'.symm.trans (by show F (ray 0) = F w; rw [hr0])⟩ (hFr w hw0)
    · rw [le_antisymm (not_lt.1 ht) zero_le, le_antisymm (not_lt.1 ht') zero_le]
  · -- properness
    refine tendsto_atTop_atTop.2 fun b => ⟨(b + ‖w‖ + M).toNNReal, fun t ht => ?_⟩
    have ht' : b + ‖w‖ + M ≤ (t : ℝ) := by
      have := Real.le_coe_toNNReal (b + ‖w‖ + M)
      exact this.trans (by exact_mod_cast ht)
    have h1 := hM _ (hrayH t)
    have h2 : (t : ℝ) ≤ ‖ray t‖ + ‖w‖ := by
      have : ‖((t : ℝ) : ℂ) * I‖ = t := by simp
      calc (t : ℝ) = ‖((t : ℝ) : ℂ) * I‖ := this.symm
        _ = ‖ray t - w‖ := by simp [hray]
        _ ≤ ‖ray t‖ + ‖w‖ := norm_sub_le _ _
    have h3 : ‖ray t‖ ≤ ‖F (ray t)‖ + ‖F (ray t) - ray t‖ := by
      calc ‖ray t‖ = ‖F (ray t) - (F (ray t) - ray t)‖ := by ring_nf
        _ ≤ ‖F (ray t)‖ + ‖F (ray t) - ray t‖ := norm_sub_le _ _
    linarith

end Access

end Supp9B

end InteractingSLE
