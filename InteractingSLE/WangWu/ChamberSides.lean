/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberTheta
import InteractingSLE.Frozen.Spec.leftSideOf
import InteractingSLE.Frozen.Spec.rightSideOf
import QuantumZipper.Proofs.Complex.BasicsCayley

/-!
# Ordered crosscuts; simple proper arcs of `ℍ` as crosscuts of the disc

Packet PROVE-WW-B4 (Wang–Wu, `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31, §4.4–4.5).

**Ordered crosscuts.** A crosscut `β` lies weakly above the crosscut `α` when it avoids the lower side of `α`
(`Disjoint (crossRange β) (crossSide α (−1))`). Then the lower side of `α` lies in the lower side of `β`
(`crossSide_neg_subset_of_disjoint`), and **`α` avoids the upper side of `β`** (`disjoint_crossRange_crossSide_swap`):
the order can be read from either curve. For three ordered crosscuts `α ≤ μ ≤ β`, **every common point of `α` and
`β` lies on `μ`** (`crossRange_inter_subset_of_between`) — the specification's "Every common point of the two outer
curves belongs to `γ`. In the open half-plane it belongs to both opposite closed Jordan sides of `γ`, whose
intersection is precisely `γ`" (proof of Lemma 7.1, p. 224), and the first step of the proof of Wang–Wu Lemma 4.22.

**Proper arcs.** A simple proper curve `γ : [0, ∞) → ℍ̄` from `0` to `∞` with `γ(t) ∈ ℍ` for `t > 0`
(`IsProperArc`; Wang–Wu's seed lines, Proposition 4.18) becomes the crosscut `toDisc γ` of the disc under the Cayley
map `z ↦ (z − i)/(z + i)` (`0 ↦ −1`, `∞ ↦ 1`, negative reals to the upper and positive reals to the lower
semicircle), after the time change `s ↦ s/(1 − s)`. The frozen sides `leftSideOf`, `rightSideOf` are the upper and
lower sides of this crosscut (`mem_leftSideOf_iff`, `mem_rightSideOf_iff`), so in `ℍ` the two sides of a proper arc
partition `ℍ \ γ` (`mem_leftSideOf_or_mem_rightSideOf`), and the order relation of Wang–Wu Proposition 4.19
("`γ_{u₂}` lies to the left of `γ_{u₁}`": `γ_{u₂}` avoids the right side of `γ_{u₁}`) is the crosscut order.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.WangWu

/-! ### Ordered crosscuts -/

namespace IsDiscCrosscut

variable {α β μ : ℝ → ℂ}

/-- Two sides of crosscuts on the same side `σ` meet near `σ i`. -/
theorem crossSide_inter_nonempty (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : (crossSide α σ ∩ crossSide β σ).Nonempty := by
  have hp : ‖((σ : ℂ) * I)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  have hpσ : 0 < σ * ((σ : ℂ) * I).im := by rcases hσ with rfl | rfl <;> simp
  obtain ⟨r₁, hr₁, h₁⟩ := hα.exists_ball_inter_subset_crossSide hσ hp hpσ
  obtain ⟨r₂, hr₂, h₂⟩ := hβ.exists_ball_inter_subset_crossSide hσ hp hpσ
  set r := min (min r₁ r₂) 1 with hr
  have hr0 : 0 < r := lt_min (lt_min hr₁ hr₂) one_pos
  set w : ℂ := ((1 - r / 2 : ℝ) : ℂ) * ((σ : ℂ) * I)
  have hdist : dist w ((σ : ℂ) * I) = r / 2 := by
    rw [dist_eq_norm]
    have : w - (σ : ℂ) * I = ((-(r / 2) : ℝ) : ℂ) * ((σ : ℂ) * I) := by simp only [w]; push_cast; ring
    rw [this, norm_mul, hp, mul_one, norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have hnorm : ‖w‖ = 1 - r / 2 := by
    simp only [w, norm_mul, hp, mul_one, norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by linarith [min_le_right (min r₁ r₂) 1])
  have hwball : w ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right, hnorm]; linarith
  refine ⟨w, h₁ ⟨?_, hwball⟩, h₂ ⟨?_, hwball⟩⟩
  · rw [mem_ball, hdist]; linarith [min_le_left (min r₁ r₂) 1, min_le_left r₁ r₂]
  · rw [mem_ball, hdist]; linarith [min_le_left (min r₁ r₂) 1, min_le_right r₁ r₂]

/-- A preconnected subset of `𝔻 \ α` meeting the side `σ` of `α` lies in it. -/
theorem subset_crossSide_of_isPreconnected (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {S : Set ℂ} (hS : IsPreconnected S) (hSD : S ⊆ ball 0 1 \ crossRange α) (hne : (S ∩ crossSide α σ).Nonempty) :
    S ⊆ crossSide α σ := by
  have hcover := hα.subset_crossSide_union
  rcases IsPreconnected.subset_or_subset (hα.isOpen_crossSide (Or.inl rfl))
      (hα.isOpen_crossSide (Or.inr rfl)) hα.disjoint_crossSide (hSD.trans hcover) hS with h | h
  · rcases hσ with rfl | rfl
    · exact h
    · obtain ⟨w, hwS, hwσ⟩ := hne
      exact absurd hwσ (Set.disjoint_left.1 hα.disjoint_crossSide (h hwS))
  · rcases hσ with rfl | rfl
    · obtain ⟨w, hwS, hwσ⟩ := hne
      exact absurd (h hwS) (Set.disjoint_left.1 hα.disjoint_crossSide hwσ)
    · exact h

/-- If `β` avoids the lower side of `α`, the lower side of `α` lies in the lower side of `β`. -/
theorem crossSide_neg_subset_of_disjoint (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange β) (crossSide α (-1))) : crossSide α (-1) ⊆ crossSide β (-1) := by
  refine hβ.subset_crossSide_of_isPreconnected (Or.inr rfl) (hα.isPreconnected_crossSide (Or.inr rfl))
    (fun w hw => ⟨(hα.crossSide_subset (Or.inr rfl) hw).1, fun h => Set.disjoint_left.1 hord h hw⟩) ?_
  exact hα.crossSide_inter_nonempty hβ (Or.inr rfl)

/-- If `α` avoids the upper side of `β`, the upper side of `β` lies in the upper side of `α`. -/
theorem crossSide_pos_subset_of_disjoint (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange α) (crossSide β 1)) : crossSide β 1 ⊆ crossSide α 1 := by
  refine hα.subset_crossSide_of_isPreconnected (Or.inl rfl) (hβ.isPreconnected_crossSide (Or.inl rfl))
    (fun w hw => ⟨(hβ.crossSide_subset (Or.inl rfl) hw).1, fun h => Set.disjoint_left.1 hord h hw⟩) ?_
  obtain ⟨w, h₁, h₂⟩ := hα.crossSide_inter_nonempty hβ (Or.inl rfl)
  exact ⟨w, h₂, h₁⟩

/-- **The order of two crosscuts can be read from either one**: if `β` avoids the lower side of `α`, then `α`
avoids the upper side of `β`. -/
theorem disjoint_crossRange_crossSide_swap (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange β) (crossSide α (-1))) : Disjoint (crossRange α) (crossSide β 1) := by
  have hsub := crossSide_neg_subset_of_disjoint hα hβ hord
  have hcl : crossRange α ⊆ closure (crossSide β (-1)) :=
    (hα.crossRange_subset_closure_crossSide (Or.inr rfl)).trans (closure_mono hsub)
  exact ((hβ.disjoint_crossSide.closure_right (hβ.isOpen_crossSide (Or.inl rfl))).mono_right hcl).symm

/-- The converse direction of `disjoint_crossRange_crossSide_swap`. -/
theorem disjoint_crossRange_crossSide_swap' (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange α) (crossSide β 1)) : Disjoint (crossRange β) (crossSide α (-1)) := by
  have hsub := crossSide_pos_subset_of_disjoint hα hβ hord
  have hcl : crossRange β ⊆ closure (crossSide α 1) :=
    (hβ.crossRange_subset_closure_crossSide (Or.inl rfl)).trans (closure_mono hsub)
  exact (hα.disjoint_crossSide.closure_left (hα.isOpen_crossSide (Or.inr rfl))).mono_left hcl

/-- A point of the closed disc off a crosscut and off its lower side is on its upper side or on the circle. -/
theorem mem_crossSide_one_of (hα : IsDiscCrosscut α) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hwα : w ∉ crossRange α)
    (hw' : w ∉ crossSide α (-1)) : w ∈ crossSide α 1 := by
  rcases hα.subset_crossSide_union ⟨hw, hwα⟩ with h | h
  · exact h
  · exact absurd h hw'

/-- **Common points of the outer curves lie on the middle curve.** If `μ` avoids the lower side of `α` and `β`
avoids the lower side of `μ`, every common point of `α` and `β` lies on `μ`. -/
theorem crossRange_inter_subset_of_between (hα : IsDiscCrosscut α) (hμ : IsDiscCrosscut μ)
    (hαμ : Disjoint (crossRange μ) (crossSide α (-1)))
    (hμβ : Disjoint (crossRange β) (crossSide μ (-1))) : crossRange α ∩ crossRange β ⊆ crossRange μ := by
  rintro p ⟨hpα, hpβ⟩
  have hpD := hα.crossRange_subset_closedBall hpα
  rw [mem_closedBall, dist_zero_right] at hpD
  rcases eq_or_lt_of_le hpD with hn | hn
  · rcases hα.eq_of_mem_crossRange_of_norm hpα hn with h | h
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hμ.zero, h]⟩
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hμ.one, h]⟩
  by_contra hpμ
  have hpball : p ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; exact hn
  rcases hμ.subset_crossSide_union ⟨hpball, hpμ⟩ with h | h
  · exact Set.disjoint_left.1 (disjoint_crossRange_crossSide_swap hα hμ hαμ) hpα h
  · exact Set.disjoint_left.1 hμβ hpβ h

end IsDiscCrosscut

/-! ### The Cayley map on the real line -/

theorem cayley_ofReal_norm (x : ℝ) : ‖cayley (x : ℂ)‖ = 1 := by
  have hx : (x : ℂ) + I ≠ 0 := QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (by simp)
  rw [cayley, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.2 hx)]
  have h1 : ‖(x : ℂ) - I‖ ^ 2 = ‖(x : ℂ) + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]; simp
  nlinarith [norm_nonneg ((x : ℂ) - I), norm_nonneg ((x : ℂ) + I)]

theorem cayley_ofReal_im (x : ℝ) : (cayley (x : ℂ)).im = -2 * x / (x ^ 2 + 1) := by
  have hx : (x : ℂ) + I ≠ 0 := QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (by simp)
  have hden : (x : ℂ) + I ≠ 0 := hx
  rw [cayley, div_im]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im, normSq_apply]
  field_simp
  ring

theorem cayleyInv_I : cayleyInv I = -1 := by
  have h : (1 : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [cayleyInv, div_eq_iff h]
  ring_nf
  rw [I_sq]; ring

theorem cayleyInv_neg_I : cayleyInv (-I) = 1 := by
  have h : (1 : ℂ) - -I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [cayleyInv, div_eq_iff h]
  ring_nf
  rw [I_sq]; ring

theorem cayley_zero : cayley 0 = -1 := by
  rw [cayley, zero_sub, zero_add, neg_div, div_self I_ne_zero]

/-! ### Simple proper arcs of `ℍ` -/

/-- A **simple proper arc** of `ℍ` from `0` to `∞`: continuous and injective on `[0, ∞)`, starting at `0`, in the open
half-plane at positive times, and tending to `∞` (Wang–Wu's simple proper seed lines, Proposition 4.18). -/
structure IsProperArc (γ : ℝ → ℂ) : Prop where
  cont : ContinuousOn γ (Ici 0)
  inj : InjOn γ (Ici 0)
  zero : γ 0 = 0
  mem_H : ∀ t, 0 < t → γ t ∈ H
  tendsto : Tendsto (fun t => ‖γ t‖) atTop atTop

/-- The range `γ([0, ∞))` of a proper arc. -/
def arcRange (γ : ℝ → ℂ) : Set ℂ := γ '' Ici 0

/-- The time change `s ↦ s/(1 − s)` from `[0, 1)` onto `[0, ∞)`. -/
def arcTime (s : ℝ) : ℝ := s / (1 - s)

/-- Its inverse `t ↦ t/(1 + t)`. -/
def discTime (t : ℝ) : ℝ := t / (1 + t)

theorem arcTime_discTime {t : ℝ} (ht : 0 ≤ t) : arcTime (discTime t) = t := by
  have h1 : (1 : ℝ) + t ≠ 0 := by linarith
  rw [arcTime, discTime]
  have h2 : 1 - t / (1 + t) = 1 / (1 + t) := by field_simp; ring
  rw [h2]; field_simp

theorem discTime_arcTime {s : ℝ} (hs : s < 1) : discTime (arcTime s) = s := by
  have h1 : (1 : ℝ) - s ≠ 0 := by linarith
  rw [arcTime, discTime]
  have h2 : 1 + s / (1 - s) = 1 / (1 - s) := by field_simp; ring
  rw [h2]; field_simp

theorem discTime_mem_Ico {t : ℝ} (ht : 0 ≤ t) : discTime t ∈ Ico (0 : ℝ) 1 :=
  ⟨div_nonneg ht (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

theorem arcTime_nonneg {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) : 0 ≤ arcTime s :=
  div_nonneg hs.1 (by linarith [hs.2])

theorem arcTime_pos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < arcTime s :=
  div_pos hs.1 (by linarith [hs.2])

theorem strictMonoOn_arcTime : StrictMonoOn arcTime (Ico 0 1) := by
  intro s hs t ht hst
  rw [arcTime, arcTime, div_lt_div_iff₀ (by linarith [hs.2]) (by linarith [ht.2])]
  nlinarith

theorem continuousOn_arcTime : ContinuousOn arcTime (Iio 1) := by
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  unfold arcTime
  exact continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by simp; linarith [mem_Iio.1 hs])

theorem tendsto_arcTime : Tendsto arcTime (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mem_Ioi.2 (sub_pos.2 (mem_Iio.1 hs))
  have h2 : Tendsto (fun s : ℝ => (1 - s)⁻¹) (𝓝[<] 1) atTop := tendsto_inv_nhdsGT_zero.comp h1
  have h3 : ∀ s : ℝ, s < 1 → arcTime s = (1 - s)⁻¹ - 1 := fun s hs => by
    have : (1 : ℝ) - s ≠ 0 := by linarith
    rw [arcTime]; field_simp; ring
  refine (tendsto_atTop_add_const_right _ (-1) h2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [h3 s (mem_Iio.1 hs)]
  ring

/-- The crosscut of the disc carried by a proper arc: `s ↦ cayley (γ (s/(1 − s)))` on `[0, 1)`, and `1` at `s = 1`. -/
def toDisc (γ : ℝ → ℂ) (s : ℝ) : ℂ := if s < 1 then cayley (γ (arcTime s)) else 1

theorem toDisc_of_lt {γ : ℝ → ℂ} {s : ℝ} (hs : s < 1) : toDisc γ s = cayley (γ (arcTime s)) := by
  simp [toDisc, hs]

theorem toDisc_one (γ : ℝ → ℂ) : toDisc γ 1 = 1 := by simp [toDisc]

theorem toDisc_discTime (γ : ℝ → ℂ) {t : ℝ} (ht : 0 ≤ t) : toDisc γ (discTime t) = cayley (γ t) := by
  rw [toDisc_of_lt (discTime_mem_Ico ht).2, arcTime_discTime ht]

namespace IsProperArc

variable {γ : ℝ → ℂ}

theorem mem_Hbar (hγ : IsProperArc γ) {t : ℝ} (ht : 0 ≤ t) : γ t ∈ Hbar := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, hγ.zero]; show (0 : ℝ) ≤ (0 : ℂ).im; simp
  · exact (show (0 : ℝ) < (γ t).im from hγ.mem_H t h).le

theorem add_I_ne_zero (hγ : IsProperArc γ) {t : ℝ} (ht : 0 ≤ t) : γ t + I ≠ 0 :=
  QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (hγ.mem_Hbar ht)

theorem tendsto_cobounded (hγ : IsProperArc γ) : Tendsto γ atTop (cobounded ℂ) :=
  tendsto_norm_atTop_iff_cobounded.1 hγ.tendsto

theorem isClosed_arcRange (hγ : IsProperArc γ) : IsClosed (arcRange γ) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hγ.tendsto (‖z‖ + 1))
  have hcpt : IsClosed (γ '' Icc 0 T) :=
    (isCompact_Icc.image_of_continuousOn (hγ.cont.mono fun t ht => mem_Ici.2 ht.1)).isClosed
  have hzT : z ∈ closure (γ '' Icc 0 T) := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨b, hbA, hb⟩ := Metric.mem_closure_iff.1 hz (min ε 1) (lt_min hε one_pos)
    obtain ⟨t, ht, rfl⟩ := hbA
    refine ⟨γ t, ⟨t, ⟨ht, ?_⟩, rfl⟩, lt_of_lt_of_le hb (min_le_left _ _)⟩
    by_contra htT
    push Not at htT
    have h1 := hT t htT.le
    have h2 : dist z (γ t) < 1 := lt_of_lt_of_le hb (min_le_right _ _)
    rw [dist_eq_norm] at h2
    have := norm_sub_norm_le (γ t) z
    rw [norm_sub_rev] at h2
    linarith
  rw [hcpt.closure_eq] at hzT
  obtain ⟨t, ht, rfl⟩ := hzT
  exact ⟨t, mem_Ici.2 ht.1, rfl⟩

end IsProperArc


theorem continuousAt_cayley_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : ContinuousAt cayley z :=
  (QuantumZipper.CA.differentiableAt_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hz)).continuousAt

theorem continuousAt_cayleyInv {w : ℂ} (hw : w ≠ 1) : ContinuousAt cayleyInv w :=
  (QuantumZipper.CA.differentiableAt_cayleyInv hw).continuousAt

theorem cayley_injOn_Hbar : InjOn cayley Hbar := fun z hz w hw h => by
  rw [← QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hz), h,
    QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hw)]

theorem cayley_ne_one_of_Hbar {z : ℂ} (hz : z ∈ Hbar) : cayley z ≠ 1 :=
  QuantumZipper.CA.cayley_ne_one (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hz)

namespace IsProperArc

variable {γ : ℝ → ℂ}

theorem continuousOn_toDisc_Ico (hγ : IsProperArc γ) : ContinuousOn (toDisc γ) (Ico 0 1) := by
  have h1 : ContinuousOn (fun s => cayley (γ (arcTime s))) (Ico 0 1) := by
    intro s hs
    have hγs : ContinuousWithinAt (fun s => γ (arcTime s)) (Ico 0 1) s :=
      (hγ.cont (arcTime s) (arcTime_nonneg hs)).comp
        ((continuousOn_arcTime s hs.2).mono fun u hu => hu.2) fun u hu => arcTime_nonneg hu
    exact ContinuousAt.comp_continuousWithinAt (f := fun s => γ (arcTime s)) (g := cayley)
      (continuousAt_cayley_of_mem_Hbar (hγ.mem_Hbar (arcTime_nonneg hs))) hγs
  exact h1.congr fun s hs => toDisc_of_lt hs.2

theorem isDiscCrosscut_toDisc (hγ : IsProperArc γ) : IsDiscCrosscut (toDisc γ) := by
  have h0 : arcTime 0 = 0 := by simp [arcTime]
  refine ⟨?_, ?_, ?_, toDisc_one γ, ?_⟩
  · intro s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · subst h
      refine ContinuousWithinAt.mono ?_ (fun u hu => mem_Iic.2 hu.2)
      refine continuousWithinAt_Iio_iff_Iic.1 ?_
      have ht : Tendsto (fun s => cayley (γ (arcTime s))) (𝓝[<] 1) (𝓝 1) :=
        QuantumZipper.CA.tendsto_cayley_cobounded.comp (hγ.tendsto_cobounded.comp tendsto_arcTime)
      rw [ContinuousWithinAt, toDisc_one]
      refine ht.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (toDisc_of_lt (mem_Iio.1 hu)).symm
    · refine (hγ.continuousOn_toDisc_Ico s ⟨hs.1, h⟩).mono_of_mem_nhdsWithin ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds h)] with u hu hu'
      exact ⟨hu.1, hu'⟩
  · intro s hs s' hs' h
    rcases eq_or_lt_of_le hs.2 with h1 | h1 <;> rcases eq_or_lt_of_le hs'.2 with h1' | h1'
    · rw [h1, h1']
    · rw [h1, toDisc_one, toDisc_of_lt h1'] at h
      exact absurd h.symm (cayley_ne_one_of_Hbar (hγ.mem_Hbar (arcTime_nonneg ⟨hs'.1, h1'⟩)))
    · rw [h1', toDisc_one, toDisc_of_lt h1] at h
      exact absurd h (cayley_ne_one_of_Hbar (hγ.mem_Hbar (arcTime_nonneg ⟨hs.1, h1⟩)))
    · rw [toDisc_of_lt h1, toDisc_of_lt h1'] at h
      have h2 := cayley_injOn_Hbar (hγ.mem_Hbar (arcTime_nonneg ⟨hs.1, h1⟩))
        (hγ.mem_Hbar (arcTime_nonneg ⟨hs'.1, h1'⟩)) h
      have h3 := hγ.inj (mem_Ici.2 (arcTime_nonneg ⟨hs.1, h1⟩)) (mem_Ici.2 (arcTime_nonneg ⟨hs'.1, h1'⟩)) h2
      exact strictMonoOn_arcTime.injOn ⟨hs.1, h1⟩ ⟨hs'.1, h1'⟩ h3
  · rw [toDisc_of_lt one_pos, h0, hγ.zero, cayley_zero]
  · intro s hs
    rw [toDisc_of_lt hs.2]
    exact QuantumZipper.CA.cayley_mem_ball (hγ.mem_H _ (arcTime_pos hs))

theorem cayley_mem_crossRange_iff (hγ : IsProperArc γ) {z : ℂ} (hz : z ∈ Hbar) :
    cayley z ∈ crossRange (toDisc γ) ↔ z ∈ arcRange γ := by
  constructor
  · rintro ⟨s, hs, h⟩
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · rw [h1, toDisc_one] at h
      exact absurd h.symm (cayley_ne_one_of_Hbar hz)
    · rw [toDisc_of_lt h1] at h
      refine ⟨arcTime s, mem_Ici.2 (arcTime_nonneg ⟨hs.1, h1⟩), ?_⟩
      exact cayley_injOn_Hbar (hγ.mem_Hbar (arcTime_nonneg ⟨hs.1, h1⟩)) hz h
  · rintro ⟨t, ht, rfl⟩
    exact ⟨discTime t, Ico_subset_Icc_self (discTime_mem_Ico ht), toDisc_discTime γ ht⟩

/-- A point of the crosscut in the open disc is the Cayley image of a point of the arc in `ℍ`. -/
theorem exists_of_mem_crossRange (hγ : IsProperArc γ) {w : ℂ} (hw : w ∈ crossRange (toDisc γ))
    (hwb : w ∈ ball (0 : ℂ) 1) : ∃ t, 0 < t ∧ w = cayley (γ t) := by
  obtain ⟨s, hs, rfl⟩ := hw
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · rw [h1, toDisc_one, mem_ball, dist_zero_right, norm_one] at hwb
    exact absurd hwb (lt_irrefl 1)
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0, (isDiscCrosscut_toDisc hγ).zero, mem_ball, dist_zero_right, norm_neg, norm_one] at hwb
    exact absurd hwb (lt_irrefl 1)
  exact ⟨arcTime s, arcTime_pos ⟨h0, h1⟩, toDisc_of_lt h1⟩

theorem ofReal_notMem_arcRange (hγ : IsProperArc γ) {x : ℝ} (hx : x ≠ 0) : (x : ℂ) ∉ arcRange γ := by
  rintro ⟨t, ht, h⟩
  rcases eq_or_lt_of_le (mem_Ici.1 ht) with h0 | h0
  · rw [← h0, hγ.zero] at h
    exact hx (ofReal_eq_zero.1 h.symm)
  · have := hγ.mem_H t h0
    rw [h] at this
    have h' : (0 : ℝ) < ((x : ℂ)).im := this
    rw [ofReal_im] at h'
    exact lt_irrefl 0 h'

/-- Core of the side correspondence (`→`). -/
theorem cayley_mem_crossSide_of (hγ : IsProperArc γ) {z : ℂ} (hz : z ∈ H) (hzA : z ∉ arcRange γ)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : ℝ}
    (hxcl : (x : ℂ) ∈ closure (connectedComponentIn (H \ arcRange γ) z)) (hx : 0 < σ * (cayley x).im) :
    cayley z ∈ crossSide (toDisc γ) σ := by
  have hα := hγ.isDiscCrosscut_toDisc
  have hzH : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hz)
  have hcz : cayley z ∈ ball (0 : ℂ) 1 \ crossRange (toDisc γ) :=
    ⟨QuantumZipper.CA.cayley_mem_ball hz, fun h => hzA ((hγ.cayley_mem_crossRange_iff hzH).1 h)⟩
  set τ : ℝ := -σ with hτ
  have hτ' : τ = 1 ∨ τ = -1 := by rcases hσ with rfl | rfl <;> simp [hτ]
  by_contra hnot
  have hcτ : cayley z ∈ crossSide (toDisc γ) τ := by
    rcases hα.subset_crossSide_union hcz with h | h <;> rcases hσ with rfl | rfl
    · exact absurd h hnot
    · simpa [hτ] using h
    · simpa [hτ] using h
    · exact absurd h hnot
  set Q := connectedComponentIn (H \ arcRange γ) z
  have hQsub : cayley '' Q ⊆ ball 0 1 \ crossRange (toDisc γ) := by
    rintro _ ⟨q, hq, rfl⟩
    have hq' := connectedComponentIn_subset _ _ hq
    exact ⟨QuantumZipper.CA.cayley_mem_ball hq'.1,
      fun h => hq'.2 ((hγ.cayley_mem_crossRange_iff (le_of_lt (show (0 : ℝ) < q.im from hq'.1))).1 h)⟩
  have hQc : IsPreconnected (cayley '' Q) :=
    isPreconnected_connectedComponentIn.image _ fun q hq =>
      (continuousAt_cayley_of_mem_Hbar
        (le_of_lt (show (0 : ℝ) < q.im from (connectedComponentIn_subset _ _ hq).1))).continuousWithinAt
  have hQτ : cayley '' Q ⊆ crossSide (toDisc γ) τ :=
    hα.subset_crossSide_of_isPreconnected hτ' hQc hQsub
      ⟨cayley z, ⟨z, mem_connectedComponentIn ⟨hz, hzA⟩, rfl⟩, hcτ⟩
  have hxH : (x : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ (x : ℂ).im; simp
  have hcl : cayley x ∈ closure (crossSide (toDisc γ) τ) :=
    closure_mono hQτ (mem_closure_image (continuousAt_cayley_of_mem_Hbar hxH) hxcl)
  rw [hα.closure_crossSide hτ'] at hcl
  have hn := cayley_ofReal_norm x
  rcases hcl with h | h | h
  · have := (hα.crossSide_subset hτ' h).1
    rw [mem_ball, dist_zero_right, hn] at this
    exact lt_irrefl _ this
  · rcases hα.eq_of_mem_crossRange_of_norm h hn with h' | h' <;> rw [h'] at hx <;> simp at hx
  · have := h.2
    rw [hτ] at this
    linarith

/-- Core of the side correspondence (`←`). -/
theorem mem_closure_of_cayley_mem_crossSide (hγ : IsProperArc γ) {z : ℂ} (hz : z ∈ H) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (h : cayley z ∈ crossSide (toDisc γ) σ) :
    z ∉ arcRange γ ∧ cayleyInv ((σ : ℂ) * I) ∈ closure (connectedComponentIn (H \ arcRange γ) z) := by
  have hα := hγ.isDiscCrosscut_toDisc
  have hzH : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hz)
  have hsub := hα.crossSide_subset hσ
  have hzA : z ∉ arcRange γ := fun hA => (hsub h).2 ((hγ.cayley_mem_crossRange_iff hzH).2 hA)
  refine ⟨hzA, ?_⟩
  set K := cayleyInv '' crossSide (toDisc γ) σ
  have hKsub : K ⊆ H \ arcRange γ := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' := hsub hw
    have hw1 : w ≠ 1 := fun h1 => by
      have := hw'.1; rw [h1, mem_ball, dist_zero_right, norm_one] at this; exact lt_irrefl 1 this
    refine ⟨QuantumZipper.CA.cayleyInv_mem_H hw'.1, fun hA => hw'.2 ?_⟩
    rw [← QuantumZipper.CA.cayley_cayleyInv hw1]
    exact (hγ.cayley_mem_crossRange_iff
      (le_of_lt (show (0 : ℝ) < (cayleyInv w).im from QuantumZipper.CA.cayleyInv_mem_H hw'.1))).2 hA
  have hKc : IsPreconnected K :=
    (hα.isPreconnected_crossSide hσ).image _ fun w hw => by
      have hw1 : w ≠ 1 := fun h1 => by
        have := (hsub hw).1; rw [h1, mem_ball, dist_zero_right, norm_one] at this; exact lt_irrefl 1 this
      exact (continuousAt_cayleyInv hw1).continuousWithinAt
  have hzK : z ∈ K := ⟨cayley z, h, QuantumZipper.CA.cayleyInv_cayley
    (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hzH)⟩
  have hKQ : K ⊆ connectedComponentIn (H \ arcRange γ) z :=
    hKc.subset_connectedComponentIn hzK hKsub
  have hp : (σ : ℂ) * I ∈ closure (crossSide (toDisc γ) σ) := by
    refine hα.semiArc_subset_closure_crossSide hσ ⟨?_, ?_⟩ <;> rcases hσ with rfl | rfl <;> simp
  have hp1 : (σ : ℂ) * I ≠ 1 := by
    rcases hσ with rfl | rfl
    · intro h; have := congrArg Complex.re h; simp at this
    · intro h; have := congrArg Complex.re h; simp at this
  exact closure_mono hKQ (mem_closure_image (continuousAt_cayleyInv hp1) hp)

/-- **The left side of a proper arc is the upper side of its crosscut.** -/
theorem mem_leftSideOf_iff (hγ : IsProperArc γ) {z : ℂ} (hz : z ∈ H) :
    z ∈ leftSideOf (arcRange γ) ↔ cayley z ∈ crossSide (toDisc γ) 1 := by
  constructor
  · rintro ⟨⟨-, hzA⟩, x, hx0, -, hxcl⟩
    refine hγ.cayley_mem_crossSide_of hz hzA (Or.inl rfl) hxcl ?_
    rw [one_mul, cayley_ofReal_im]
    exact div_pos (by linarith) (by positivity)
  · intro h
    obtain ⟨hzA, hcl⟩ := hγ.mem_closure_of_cayley_mem_crossSide hz (Or.inl rfl) h
    refine ⟨⟨hz, hzA⟩, -1, by norm_num, hγ.ofReal_notMem_arcRange (by norm_num), ?_⟩
    rw [ofReal_one, one_mul, cayleyInv_I] at hcl
    simpa using hcl

/-- **The right side of a proper arc is the lower side of its crosscut.** -/
theorem mem_rightSideOf_iff (hγ : IsProperArc γ) {z : ℂ} (hz : z ∈ H) :
    z ∈ rightSideOf (arcRange γ) ↔ cayley z ∈ crossSide (toDisc γ) (-1) := by
  constructor
  · rintro ⟨⟨-, hzA⟩, x, hx0, -, hxcl⟩
    refine hγ.cayley_mem_crossSide_of hz hzA (Or.inr rfl) hxcl ?_
    rw [cayley_ofReal_im]
    have : (-1) * (-2 * x / (x ^ 2 + 1)) = 2 * x / (x ^ 2 + 1) := by ring
    rw [this]
    exact div_pos (by linarith) (by positivity)
  · intro h
    obtain ⟨hzA, hcl⟩ := hγ.mem_closure_of_cayley_mem_crossSide hz (Or.inr rfl) h
    refine ⟨⟨hz, hzA⟩, 1, by norm_num, hγ.ofReal_notMem_arcRange (by norm_num), ?_⟩
    rw [ofReal_neg, ofReal_one, neg_one_mul, cayleyInv_neg_I] at hcl
    simpa using hcl

/-- **The two sides of a proper arc partition `ℍ \ γ`.** -/
theorem mem_leftSideOf_or_mem_rightSideOf (hγ : IsProperArc γ) {z : ℂ} (hz : z ∈ H)
    (hzA : z ∉ arcRange γ) : z ∈ leftSideOf (arcRange γ) ∨ z ∈ rightSideOf (arcRange γ) := by
  have hzH : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hz)
  rcases hγ.isDiscCrosscut_toDisc.subset_crossSide_union
    ⟨QuantumZipper.CA.cayley_mem_ball hz, fun h => hzA ((hγ.cayley_mem_crossRange_iff hzH).1 h)⟩ with h | h
  · exact Or.inl ((hγ.mem_leftSideOf_iff hz).2 h)
  · exact Or.inr ((hγ.mem_rightSideOf_iff hz).2 h)

theorem disjoint_leftSideOf_rightSideOf (hγ : IsProperArc γ) :
    Disjoint (leftSideOf (arcRange γ)) (rightSideOf (arcRange γ)) :=
  Set.disjoint_left.2 fun _ h₁ h₂ => Set.disjoint_left.1 hγ.isDiscCrosscut_toDisc.disjoint_crossSide
    ((hγ.mem_leftSideOf_iff h₁.1.1).1 h₁) ((hγ.mem_rightSideOf_iff h₂.1.1).1 h₂)

end IsProperArc

/-- **The order of two proper arcs is the order of their crosscuts**: `γ₂` avoids the right side of `γ₁` exactly
when the crosscut of `γ₂` avoids the lower side of the crosscut of `γ₁`. -/
theorem disjoint_rightSideOf_iff {γ₁ γ₂ : ℝ → ℂ} (h₁ : IsProperArc γ₁) (h₂ : IsProperArc γ₂) :
    Disjoint (arcRange γ₂) (rightSideOf (arcRange γ₁)) ↔
      Disjoint (crossRange (toDisc γ₂)) (crossSide (toDisc γ₁) (-1)) := by
  constructor
  · intro h
    refine Set.disjoint_left.2 fun w hw hwS => ?_
    have hwb := (h₁.isDiscCrosscut_toDisc.crossSide_subset (Or.inr rfl) hwS).1
    obtain ⟨t, ht, rfl⟩ := h₂.exists_of_mem_crossRange hw hwb
    exact Set.disjoint_left.1 h ⟨t, mem_Ici.2 ht.le, rfl⟩ ((h₁.mem_rightSideOf_iff (h₂.mem_H t ht)).2 hwS)
  · intro h
    refine Set.disjoint_left.2 fun z hz hzS => ?_
    have hzH : z ∈ H := hzS.1.1
    exact Set.disjoint_left.1 h ((h₂.cayley_mem_crossRange_iff (le_of_lt (show (0 : ℝ) < z.im from hzH))).2 hz)
      ((h₁.mem_rightSideOf_iff hzH).1 hzS)

/-- **Common points of the outer arcs lie on the middle arc** (Wang–Wu, proof of Lemma 4.22; specification, proof of
Lemma 7.1, p. 224). For three proper arcs with `M` avoiding the right side of `R` and `L` avoiding the right side
of `M`, every common point of `R` and `L` lies on `M`. -/
theorem arcRange_inter_subset_of_between {R M L : ℝ → ℂ} (hR : IsProperArc R) (hM : IsProperArc M)
    (hL : IsProperArc L) (hRM : Disjoint (arcRange M) (rightSideOf (arcRange R)))
    (hML : Disjoint (arcRange L) (rightSideOf (arcRange M))) :
    arcRange R ∩ arcRange L ⊆ arcRange M := by
  rintro z ⟨hzR, hzL⟩
  have hzH : z ∈ Hbar := by
    obtain ⟨t, ht, rfl⟩ := hzR
    exact hR.mem_Hbar (mem_Ici.1 ht)
  have h := IsDiscCrosscut.crossRange_inter_subset_of_between hR.isDiscCrosscut_toDisc
    hM.isDiscCrosscut_toDisc ((disjoint_rightSideOf_iff hR hM).1 hRM) ((disjoint_rightSideOf_iff hM hL).1 hML)
    ⟨(hR.cayley_mem_crossRange_iff hzH).2 hzR, (hL.cayley_mem_crossRange_iff hzH).2 hzL⟩
  exact (hM.cayley_mem_crossRange_iff hzH).1 h

end InteractingSLE.WangWu
