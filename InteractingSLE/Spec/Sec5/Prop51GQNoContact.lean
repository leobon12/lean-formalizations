/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop411QSide

/-!
# The no-wrap step without contact: a flow line leaving through the western end

Packet PROVE-PROP51G, step (3), the contact-free case. Specification p. 135 (proof of Proposition 5.1): "In the
left-strip-end case, the completed simple flow segment joins `0` to that end without meeting the revealed
counterflow. Crosscut separation puts the revealed counterflow tip on its right." In the chart `Q` (ruling R64, see
`Prop51GQ`) this is the case where the flow line `η` never meets the counterflow hull `R(K_s)` and leaves
`ℍ ∖ R(K_s)` through its western end at `∞`: in the counterflow chart `Ψ = revChart w s` the curve `Ψ ∘ η` tends to
a negative real point `x₀` as `t → ∞`.

* `noContactArc w s x₀ η = M ∘ Ψ ∘ η` (`M = mobAt x₀`, sending `x₀` to `∞`) is a proper arc
  (`isProperArc_noContactArc`);
* **`negInv_notMem_leftSideOf_of_noContact`**: then the counterflow tip `η′(s) = R(β(s))` is not on the left side of
  `η`. The right side of the arc `M ∘ Ψ ∘ η`, pulled back by `Ψ⁻¹ ∘ M⁻¹`, is a connected subset of `ℍ ∖ η` that
  contains points near the tip and points near a positive real point.

This is the landed argument of `Prop411Q.negInv_notMem_leftSideOf_of_exit'` (Proposition 4.9's exit crosscut) with
the whole flow line in place of its first excursion; no post-exit hypothesis is needed. Deterministic helpers with
distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Prop51G

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop411Q

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s x₀ : ℝ} {η : ℝ → ℂ}

/-- **The flow line read in the counterflow chart and normalized by `M = mobAt x₀`**, when it never meets the hull:
`u ↦ M(Ψ(η(u)))` for `u > 0`, and `0` at `u ≤ 0`. -/
def noContactArc (w : ℝ → ℝ) (s x₀ : ℝ) (η : ℝ → ℂ) (u : ℝ) : ℂ :=
  if u ≤ 0 then 0 else mobAt x₀ (revChart w s (η u))

theorem noContactArc_of_pos {u : ℝ} (hu : 0 < u) :
    noContactArc w s x₀ η u = mobAt x₀ (revChart w s (η u)) := by
  simp [noContactArc, not_le.2 hu]

/-- **`M ∘ Ψ ∘ η` is a proper arc** when `η` never meets `R(K_s)` and `Ψ ∘ η` tends to `x₀ ≠ 0` at the end. -/
theorem isProperArc_noContactArc (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (hx₀ : x₀ ≠ 0) (hpre : ∀ t, 0 < t → η t ∉ negInv '' fwdHull w s)
    (hlim : Tendsto (fun t => revChart w s (η t)) atTop (𝓝 (x₀ : ℂ))) :
    IsProperArc (noContactArc w s x₀ η) := by
  set G := negInv '' fwdHull w s with hG
  have hmem : ∀ u, 0 < u → η u ∈ H \ G := fun u hu => ⟨hη.mem_H u hu, hpre u hu⟩
  have hΨH : ∀ u, 0 < u → revChart w s (η u) ∈ H := fun u hu => revChart_mem_H hw hs (hmem u hu)
  have hopen : IsOpen (H \ G) := isOpen_H_diff_negInv_fwdHull hw hs
  have hηc : ∀ {t : ℝ}, 0 < t → ContinuousAt η t := fun ht =>
    hη.cont.continuousAt (Ici_mem_nhds ht)
  have hcpos : ∀ u, 0 < u → ContinuousAt (fun u => mobAt x₀ (revChart w s (η u))) u := by
    intro u hu
    have h2 : ContinuousAt (revChart w s) (η u) :=
      (continuousOn_revChart hw hs).continuousAt (hopen.mem_nhds (hmem u hu))
    have h3 : ContinuousAt (fun u => revChart w s (η u)) u :=
      ContinuousAt.comp (g := revChart w s) (f := η) h2 (hηc hu)
    exact ContinuousAt.comp (g := mobAt x₀) (f := fun u => revChart w s (η u))
      (continuousAt_mobAt x₀ (sub_ne_zero_of_mem_H x₀ (hΨH u hu))) h3
  refine ⟨?_, ?_, by simp [noContactArc], fun u hu => ?_, ?_⟩
  · intro u hu
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ u from hu) with h0 | h0
    · subst h0
      refine continuousWithinAt_Ioi_iff_Ici.1 ?_
      have hη0 : Tendsto η (𝓝[>] 0) (𝓝[H \ G] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have hc : ContinuousWithinAt η (Ici 0) 0 := hη.cont 0 (Set.mem_Ici.2 le_rfl)
          have := hc.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
          rwa [hη.zero] at this
        · filter_upwards [self_mem_nhdsWithin] with u hu using hmem u hu
      have h2 := (tendsto_revChart_zero hw hw0 hs).comp hη0
      have h3 := (continuousAt_mobAt x₀ (sub_ne_zero.2 (by simpa using hx₀))).tendsto.comp h2
      rw [mobAt_zero] at h3
      refine (h3.congr' ?_).trans (by simp [noContactArc])
      filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [Function.comp_apply]
      rw [noContactArc_of_pos hu]
    · refine ((hcpos u h0).congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds h0] with v hv
      rw [noContactArc_of_pos hv]
  · intro u hu v hv e
    have hu' : (0 : ℝ) ≤ u := hu
    have hv' : (0 : ℝ) ≤ v := hv
    rcases eq_or_lt_of_le hu' with hu0 | hu0 <;> rcases eq_or_lt_of_le hv' with hv0 | hv0
    · rw [← hu0, ← hv0]
    · exfalso
      rw [← hu0, noContactArc_of_pos hv0] at e
      simp only [noContactArc, le_refl, ↓reduceIte] at e
      exact ne_zero_of_mem_H (mobAt_mem_H hx₀ (hΨH v hv0)) e.symm
    · exfalso
      rw [← hv0, noContactArc_of_pos hu0] at e
      simp only [noContactArc, le_refl, ↓reduceIte] at e
      exact ne_zero_of_mem_H (mobAt_mem_H hx₀ (hΨH u hu0)) e
    · rw [noContactArc_of_pos hu0, noContactArc_of_pos hv0] at e
      have e1 := congrArg (mobAt (-x₀)) e
      rw [mobAt_neg_mobAt hx₀ (sub_ne_zero_of_mem_H x₀ (hΨH u hu0)),
        mobAt_neg_mobAt hx₀ (sub_ne_zero_of_mem_H x₀ (hΨH v hv0))] at e1
      have e2 := injOn_revChart hw hw0 hs (hmem u hu0) (hmem v hv0) e1
      exact hη.inj hu hv e2
  · rw [noContactArc_of_pos hu]
    exact mobAt_mem_H hx₀ (hΨH u hu)
  · have hg : Tendsto (fun u => revChart w s (η u)) atTop (𝓝[≠] (x₀ : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩
      filter_upwards [eventually_gt_atTop 0] with u hu
      exact fun h => sub_ne_zero_of_mem_H x₀ (hΨH u hu) (by rw [show (x₀ : ℂ) = _ from h.symm]; ring)
    refine ((tendsto_norm_mobAt hx₀).comp hg).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    simp only [Function.comp_apply]
    rw [noContactArc_of_pos hu]

/-- **The no-wrap step without contact** (deterministic; the left-end case of the proof of Proposition 5.1, p. 135).
Let `η` be a proper arc (the flow line), `β` a Loewner trace of the continuous driver `w` from `0` (the counterflow
`η′ = R ∘ β`), `s ≥ 0`. If `η` never meets `R(K_s)` and, in the chart `Ψ = R ∘ f_s ∘ R` of `ℍ ∖ R(K_s)`, tends to a
negative real point `x₀` as `t → ∞` (it leaves through the western end of `∞`), then the counterflow tip
`η′(s) = R(β(s))` is not on the left side of `η`. -/
theorem negInv_notMem_leftSideOf_of_noContact (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) (hx₀ : x₀ < 0) (hpre : ∀ t, 0 < t → η t ∉ negInv '' fwdHull w s)
    (hlim : Tendsto (fun t => revChart w s (η t)) atTop (𝓝 (x₀ : ℂ))) :
    negInv (β s) ∉ leftSideOf (arcRange η) := by
  intro hL
  have hβs : β s ≠ 0 := fun h => by
    rw [h] at hL
    exact ne_zero_of_mem_H hL.1.1 (by simp [negInv])
  set A := arcRange η with hA
  set γ := noContactArc w s x₀ η with hγdef
  have hx₀' : x₀ ≠ 0 := hx₀.ne
  have hγ : IsProperArc γ := isProperArc_noContactArc hη hw hw0 hs hx₀' hpre hlim
  set S := mobAt (-x₀) '' rightSideOf (arcRange γ) with hSdef
  -- `S ⊆ ℍ`, and `S` is preconnected
  have hSH : S ⊆ H := by
    rintro _ ⟨m, hm, rfl⟩
    exact mobAt_mem_H (neg_ne_zero.2 hx₀') hm.1.1
  have hSc : IsPreconnected S := by
    refine hγ.isPreconnected_rightSideOf.image _ fun m hm => ?_
    exact (continuousAt_mobAt (-x₀) (sub_ne_zero_of_mem_H (-x₀) hm.1.1)).continuousWithinAt
  -- the inverse chart maps `S` into `ℍ ∖ η`
  have hSA : revChartInv w s '' S ⊆ H \ A := by
    rintro _ ⟨ξ, hξ, rfl⟩
    obtain ⟨m, hm, rfl⟩ := hξ
    have hξH : mobAt (-x₀) m ∈ H := mobAt_mem_H (neg_ne_zero.2 hx₀') hm.1.1
    have hmem := revChartInv_mem hw hw0 hs hξH
    refine ⟨hmem.1, ?_⟩
    rintro ⟨t, ht, he⟩
    have ht' : (0 : ℝ) ≤ t := ht
    rcases eq_or_lt_of_le ht' with h0 | h0
    · rw [← h0, hη.zero] at he
      exact ne_zero_of_mem_H hmem.1 he.symm
    · have hΨ : revChart w s (η t) = mobAt (-x₀) m := by
        rw [he, revChart_revChartInv hw hw0 hs hξH]
      have hmeq : m = mobAt x₀ (revChart w s (η t)) := by
        rw [hΨ, mobAt_mobAt_neg hx₀' (fun h => ?_)]
        have := hm.1.1
        have h' : m = -(x₀ : ℂ) := by linear_combination h
        rw [h'] at this
        exact absurd this (by simp [QuantumZipper.H])
      refine hm.1.2 ⟨t, ht', ?_⟩
      rw [hmeq, hγdef, noContactArc_of_pos h0]
  have hSc' : IsPreconnected (revChartInv w s '' S) :=
    hSc.image _ ((continuousOn_revChartInv hw hw0 hs).mono hSH)
  -- the tip side: points of `S` near `∞` are mapped near the tip
  have hLopen : IsOpen (leftSideOf A) := Cond44Ref.isOpen_leftSideOf_arcRange hη
  obtain ⟨z₁, hz₁S, hz₁L⟩ : ∃ z ∈ revChartInv w s '' S, z ∈ leftSideOf A := by
    set f : ℕ → ℂ := fun n => ((n : ℝ) + 1 : ℝ) * I with hf
    have hfH : ∀ n, f n ∈ H := fun n => show (0 : ℝ) < (f n).im by simp [hf]; positivity
    have hfn : Tendsto (fun n => ‖f n‖) atTop atTop := by
      have : ∀ n, ‖f n‖ = (n : ℝ) + 1 := fun n => by
        simp only [hf, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_pos (by positivity)
      simp only [this]
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h1 := tendsto_revChartInv_tip hβ hw hw0 hs hβs (Eventually.of_forall hfH) hfn
    have h2 : Tendsto (fun n => mobAt x₀ (f n)) atTop (𝓝[H] (((-x₀ : ℝ)) : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_mobAt_cobounded hfn,
        Eventually.of_forall fun n => mobAt_mem_H hx₀' (hfH n)⟩
    have h3 := h2.eventually (eventually_mem_rightSideOf hγ (show (0 : ℝ) < -x₀ by linarith))
    have h4 := h1.eventually (hLopen.mem_nhds hL)
    obtain ⟨n, hn3, hn4⟩ := (h3.and h4).exists
    refine ⟨_, ⟨f n, ⟨mobAt x₀ (f n), hn3, mobAt_neg_mobAt hx₀' (sub_ne_zero_of_mem_H x₀ (hfH n))⟩, rfl⟩, hn4⟩
  -- hence the whole image lies on the left side of `η`
  have hSL : revChartInv w s '' S ⊆ leftSideOf A := fun z hz =>
    mem_leftSideOf_of_mem_connectedComponentIn hz₁L (hSc'.subset_connectedComponentIn hz₁S hSA hz)
  -- the boundary side: points of `S` near a far negative real are mapped near a positive real point
  obtain ⟨ω₀, y₀, hω₀, hy₀, hlimF⟩ := exists_neg_tendsto_fwdMapInv hβ hw hw0 hs
  set r₀ : ℝ := -ω₀⁻¹ with hr₀
  have hr₀pos : 0 < r₀ := by rw [hr₀]; exact neg_pos.2 (inv_lt_zero.2 hω₀)
  have hr₀c : negInv (r₀ : ℂ) = (ω₀ : ℂ) := by simp [negInv, hr₀]
  have hNe : (𝓝[H] (r₀ : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ mem_Hbar_of_im_eq_zero (by simp))
  have hneg : Tendsto negInv (𝓝[H] (r₀ : ℂ)) (𝓝[H] (ω₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuousAt_negInv (ofReal_ne_zero.2 hr₀pos.ne')).tendsto
      rw [hr₀c] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ using negInv_mem_H hξ
  have hinv : Tendsto (revChartInv w s) (𝓝[H] (r₀ : ℂ)) (𝓝[H] (negInv (y₀ : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (continuousAt_negInv (ofReal_ne_zero.2 hy₀.ne)).tendsto.comp (hlimF.comp hneg)
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ using (revChartInv_mem hw hw0 hs hξ).1
  have hy₀c : negInv (y₀ : ℂ) = ((-y₀⁻¹ : ℝ) : ℂ) := by simp [negInv]
  rw [hy₀c] at hinv
  have hR := hinv.eventually (eventually_mem_rightSideOf hη (show (0 : ℝ) < -y₀⁻¹ from
    neg_pos.2 (inv_lt_zero.2 hy₀)))
  set m₀ : ℝ := x₀ * r₀ / (x₀ - r₀) with hm₀
  have hm₀pos : 0 < m₀ := div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hx₀ hr₀pos) (by linarith)
  have hmob : Tendsto (mobAt x₀) (𝓝[H] (r₀ : ℂ)) (𝓝[H] (m₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 := (continuousAt_mobAt x₀ (z := (r₀ : ℂ)) (by
        rw [← ofReal_sub]; exact ofReal_ne_zero.2 (by linarith))).tendsto
      have h2 : mobAt x₀ (r₀ : ℂ) = (m₀ : ℂ) := by simp [mobAt, hm₀]
      rw [h2] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ using mobAt_mem_H hx₀' hξ
  have hS := hmob.eventually (eventually_mem_rightSideOf hγ hm₀pos)
  obtain ⟨ξ, hξR, hξS, hξH⟩ := (hR.and (hS.and self_mem_nhdsWithin)).exists
  have hξS' : ξ ∈ S := ⟨mobAt x₀ ξ, hξS, mobAt_neg_mobAt hx₀' (sub_ne_zero_of_mem_H x₀ hξH)⟩
  exact Set.disjoint_left.1 hη.disjoint_leftSideOf_rightSideOf (hSL ⟨ξ, hξS', rfl⟩) hξR

end InteractingSLE.Sec5.Prop51G
