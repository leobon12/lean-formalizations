/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLwStage
import InteractingSLE.Spec.Supplement.WalkIntClosedRun
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun
import InteractingSLE.Spec.Supplement.WalkIntFiberCollar

/-!
# The walk's launch chart as a left entry chart: the domain, infinity and lift clauses

Packet PROVE-T14-SBLEAVES2, item (b) of the orchestrator's second order (`planning/handoffs/PROVE-T14-SBLEAVES2.md`
§4.1). `IsLeftEntryChart A L c` has four clauses. For the chart of a regular, not finished run (every launch chart of
the lower walk), this module proves three of them, from the walk's physical hull models
(`WalkIntCanon.exists_hullModel_runChart`, `WalkIntClosed.hull_eq_fillH_wsetOf_run`,
`WalkIntCanon.isNormalized_runChart`):

* `isDomainChart_runChart`: the run chart is a chart of `ℍ \ fill(prefixPhysSet n)` (clause 1);
* `tendsto_runChart_cobounded`: it sends `∞` to `∞` (clause 3);
* `tendsto_runChart_lift_zero`: its lift tends to `0` at every real point left of `min(A ∩ ℝ)` (clause 4), for any
  compact `A` with the same fill, e.g. the retained prefix `lowerPrefix` (`fillH_union_real`);
* `exists_tendsto_runChart_real`: real boundary values at those points (the first half of clause 2).

The planar input is `exists_ball_disjoint_fillH`: a real point left of every real point of a compact set has a ball
missing its fill.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Lw

open Exist.Staged Exist.StagedLaw WalkIntCanon WalkBdry

/-- **A real point left of every real point of a compact set has a ball missing its fill.** The points of `ℍ` near
`x` lie in a thin unbounded half-strip to the left, which misses the set. -/
theorem exists_ball_disjoint_fillH {A : Set ℂ} (hA : IsCompact A) {x : ℝ}
    (hx : ∀ y : ℝ, (y : ℂ) ∈ A → x < y) : ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (fillH A) := by
  -- a margin to the right of `x` free of real points of `A`
  obtain ⟨x', hxx', hx'⟩ : ∃ x' : ℝ, x < x' ∧ ∀ y : ℝ, (y : ℂ) ∈ A → x' < y := by
    by_cases hR : ∃ y : ℝ, (y : ℂ) ∈ A
    · have hRc : IsCompact {y : ℝ | (y : ℂ) ∈ A} :=
        (Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage hA)
      obtain ⟨y₀, hy₀, hmin⟩ := hRc.exists_isLeast hR
      refine ⟨(x + y₀) / 2, by linarith [hx y₀ hy₀], fun y hy => ?_⟩
      linarith [hmin hy, hx y₀ hy₀]
    · push Not at hR
      exact ⟨x + 1, by linarith, fun y hy => absurd hy (hR y)⟩
  -- a height below which `A` has no point left of `x'`
  obtain ⟨h₀, hh₀, hh₀A⟩ : ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ z ∈ A, z.re ≤ x' → h₀ ≤ |z.im| := by
    set K := A ∩ {z : ℂ | z.re ≤ x'}
    have hK : IsCompact K := hA.inter_right (isClosed_le Complex.continuous_re continuous_const)
    by_cases hKe : K.Nonempty
    · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKe (Complex.continuous_im.abs.continuousOn)
      refine ⟨|z₀.im|, abs_pos.2 fun h0 => ?_, fun z hz hzr => hmin ⟨hz, hzr⟩⟩
      have hz₀r : ((z₀.re : ℝ) : ℂ) = z₀ := Complex.ext (by simp) (by simp [h0])
      have h1 := hx' z₀.re (hz₀r ▸ hz₀.1)
      have h2 : z₀.re ≤ x' := hz₀.2
      linarith
    · exact ⟨1, one_pos, fun z hz hzr => absurd ⟨z, hz, hzr⟩ hKe⟩
  set S : Set ℂ := {z | z.re < x' ∧ 0 < z.im ∧ z.im < h₀} with hS
  have hSA : Disjoint S (closure A) := by
    rw [hA.isClosed.closure_eq]
    refine Set.disjoint_left.2 fun z hzS hzA => ?_
    have := hh₀A z hzA hzS.1.le
    rw [abs_of_pos hzS.2.1] at this
    linarith [hzS.2.2]
  have hSc : IsPreconnected S := by
    have hSeq : S = {c : ℂ | c.re < x'} ∩ {c | 0 < c.im} ∩ {c | c.im < h₀} := by
      ext z; simp only [hS, mem_ofPred_eq, mem_inter_iff, and_assoc]
    rw [hSeq]
    exact (((convex_halfSpace_re_lt x').inter (convex_halfSpace_im_gt 0)).inter
      (convex_halfSpace_im_lt h₀)).isPreconnected
  have hSub : ¬ Bornology.IsBounded S := by
    intro hb
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    set r : ℝ := min (x' - 1) (-(|R| + 1))
    have hr1 : r < x' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hr2 : r ≤ -(|R| + 1) := min_le_right _ _
    have hmem : (r : ℂ) + ((h₀ / 2 : ℝ) : ℂ) * Complex.I ∈ S := by
      refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith
    have h1 := hR _ hmem
    have h2 := Complex.abs_re_le_norm ((r : ℂ) + ((h₀ / 2 : ℝ) : ℂ) * Complex.I)
    have h3 : ((r : ℂ) + ((h₀ / 2 : ℝ) : ℂ) * Complex.I).re = r := by simp
    rw [h3, abs_of_neg (by linarith [abs_nonneg R])] at h2
    linarith [le_abs_self R]
  refine ⟨min (x' - x) h₀, lt_min (by linarith) hh₀, Set.disjoint_left.2 fun z hzb hzF => ?_⟩
  have hzd : dist z x < min (x' - x) h₀ := hzb
  have hre : |z.re - x| < x' - x := by
    have := Complex.abs_re_le_norm (z - x)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    rw [← dist_eq_norm] at this
    linarith [min_le_left (x' - x) h₀]
  have him : |z.im| < h₀ := by
    have := Complex.abs_im_le_norm (z - x)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    rw [← dist_eq_norm] at this
    linarith [min_le_right (x' - x) h₀]
  have hzS : z ∈ S :=
    ⟨by linarith [(abs_lt.1 hre).2], hzF.1, by linarith [le_abs_self z.im]⟩
  rcases hzF.2 with hcl | hbd
  · exact Set.disjoint_left.1 hSA hzS hcl
  · have hsub : S ⊆ connectedComponentIn (H \ closure A) z :=
      hSc.subset_connectedComponentIn hzS fun w hw => ⟨hw.2.1, Set.disjoint_left.1 hSA hw⟩
    exact hSub (hbd.subset hsub)

/-- The fill sees only the points in `ℍ`. -/
theorem fillH_inter_H' (S : Set ℂ) : fillH (S ∩ H) = fillH S := by
  have hsplit : S = (S ∩ H) ∪ (S \ H) := (inter_union_sdiff S H).symm
  conv_rhs => rw [hsplit]
  exact (Restart.fillH_union_of_forall_notMem_H (fun z hz => hz.2)).symm

/-- Adding real points does not change the fill (e.g. `lowerPrefix = prefixPhysSet ∪ [u, 0]`). -/
theorem fillH_union_real (S : Set ℂ) (T : Set ℝ) : fillH (S ∪ ((↑) : ℝ → ℂ) '' T) = fillH S :=
  Restart.fillH_union_of_forall_notMem_H fun _ ⟨y, _, hy⟩ hH =>
    absurd (show (0 : ℝ) < ((y : ℂ)).im from hy ▸ hH) (by simp)

/-- A hull-model chart sends `∞` to `∞`: `c.1 + shift` is the normalized map out of the hull. -/
theorem tendsto_fwd_cobounded_of_hullModel {c : Chart} (M : HullModel c) :
    Tendsto c.1 (Bornology.cobounded ℂ ⊓ 𝓟 (H \ M.hull)) (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h1 := M.mapOut.2
  have h2 : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ M.hull)) atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-(1 + ‖(M.shift : ℂ)‖)) h2)
  filter_upwards [h1.eventually (Metric.ball_mem_nhds 0 one_pos)] with z hz
  have hz' : ‖c.1 z + M.shift - z‖ < 1 := by simpa using hz
  have e : z = c.1 z - (c.1 z + M.shift - z) + M.shift := by ring
  have h3 : ‖z‖ ≤ ‖c.1 z‖ + ‖c.1 z + M.shift - z‖ + ‖(M.shift : ℂ)‖ := by
    calc ‖z‖ = ‖c.1 z - (c.1 z + M.shift - z) + M.shift‖ := by rw [← e]
      _ ≤ ‖c.1 z - (c.1 z + M.shift - z)‖ + ‖(M.shift : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖c.1 z‖ + ‖c.1 z + M.shift - z‖ + ‖(M.shift : ℂ)‖ := by gcongr; exact norm_sub_le _ _
  show ‖z‖ + -(1 + ‖(M.shift : ℂ)‖) ≤ ‖c.1 z‖
  linarith

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem fillH_prefixPhysSet (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    fillH (SB.prefixPhysSet κ b jumps spec D n) = fillH (wsetOf (ExplState.run κ b jumps spec D n)) := by
  rw [← WalkIntFiber.physOf_inter_H spec, fillH_inter_H']
  rfl

/-- The hull model of a regular, not finished run chart has the hull `fill(prefixPhysSet n)`. -/
theorem exists_hullModel_fill (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) :
    ∃ M : HullModel (stChart (ExplState.run κ b jumps spec D n)),
      M.hull = fillH (SB.prefixPhysSet κ b jumps spec D n) := by
  obtain ⟨M⟩ := exists_hullModel_runChart (κ := κ) (b := b) (jumps := jumps) spec D n (fun j _ => hreg j)
  exact ⟨M, (WalkIntClosed.hull_eq_fillH_wsetOf_run spec D hreg n hnot M).trans
    (fillH_prefixPhysSet spec D n).symm⟩

/-- **Clause 1 of `IsLeftEntryChart`**: the chart of a regular, not finished run is a chart of
`ℍ \ fill(prefixPhysSet n)`. -/
theorem isDomainChart_runChart (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) :
    IsDomainChart (H \ fillH (SB.prefixPhysSet κ b jumps spec D n)) (stChart (ExplState.run κ b jumps spec D n)) := by
  obtain ⟨M, hK⟩ := exists_hullModel_fill spec D hreg n hnot
  have hN := isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) spec D n (fun j _ => hreg j)
  have hdom : ((stChart (ExplState.run κ b jumps spec D n)).dom : Set ℂ) =
      H \ fillH (SB.prefixPhysSet κ b jumps spec D n) := by
    rw [← hK]; exact M.dom_eq
  obtain ⟨L, hL, hlift⟩ := hN.derivLift
  refine ⟨hN.conformal, ?_, L, ?_, fun z hz => hlift z ?_⟩
  · rw [← hN.conformal.coe_dom]; exact hdom
  · rw [← hdom]; exact hL
  · rw [hdom]; exact hz

/-- **Clause 3 of `IsLeftEntryChart`**: the run chart sends `∞` to `∞`. -/
theorem tendsto_runChart_cobounded (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) :
    Tendsto (stChart (ExplState.run κ b jumps spec D n)).1
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH (SB.prefixPhysSet κ b jumps spec D n))) (Bornology.cobounded ℂ) := by
  obtain ⟨M, hK⟩ := exists_hullModel_fill spec D hreg n hnot
  rw [← hK]
  exact tendsto_fwd_cobounded_of_hullModel M

/-- **Clause 4 of `IsLeftEntryChart`**: at a real point left of every real point of a compact `A` with the same fill
as the run's prefix (e.g. `lowerPrefix`), the run chart's lift tends to `0`. -/
theorem tendsto_runChart_lift_zero (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {x : ℝ} (hx : ∀ y : ℝ, (y : ℂ) ∈ A → x < y) :
    Tendsto (stChart (ExplState.run κ b jumps spec D n)).2.2 (𝓝[H] (x : ℂ)) (𝓝 0) := by
  obtain ⟨M, hK⟩ := exists_hullModel_fill spec D hreg n hnot
  have hN := isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) spec D n (fun j _ => hreg j)
  obtain ⟨ρ, hρ, hd⟩ := exists_ball_disjoint_fillH hAc hx
  rw [hAf, ← hK] at hd
  exact M.tendsto_lift_zero hN hρ hd le_rfl

/-- **Clause 2 of `IsLeftEntryChart`, first half**: real boundary values of the run chart at every real point left of
every real point of `A`. -/
theorem exists_tendsto_runChart_real (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {x : ℝ} (hx : ∀ y : ℝ, (y : ℂ) ∈ A → x < y) :
    ∃ e : ℝ, Tendsto (stChart (ExplState.run κ b jumps spec D n)).1 (𝓝[H] (x : ℂ)) (𝓝 (e : ℂ)) := by
  obtain ⟨M, hK⟩ := exists_hullModel_fill spec D hreg n hnot
  obtain ⟨ρ, hρ, hd⟩ := exists_ball_disjoint_fillH hAc hx
  rw [hAf, ← hK] at hd
  obtain ⟨L, hL0, hL⟩ := IsMapOut.exists_tendsto_of_disjoint M.isHull M.mapOut hd
    (mem_ball_self (half_pos hρ)) (by simp)
  have hnhds : 𝓝[ball (x : ℂ) (ρ / 2) ∩ H] (x : ℂ) = 𝓝[H] (x : ℂ) :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (half_pos hρ)))
  rw [hnhds] at hL
  refine ⟨L.re - M.shift, ?_⟩
  have hLre : ((L.re - M.shift : ℝ) : ℂ) = L - M.shift := by
    apply Complex.ext <;> simp [hL0]
  rw [hLre]
  have := hL.sub_const (M.shift : ℂ)
  simpa using this

end Run

end InteractingSLE.Theorem14.SB.Lw
