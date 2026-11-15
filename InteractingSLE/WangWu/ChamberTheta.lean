/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberJordan
import InteractingSLE.Spec.Sec7.InteractionLens

/-!
# A crosscut splits the unit disc into its two sides (the θ-curve theorem)

Packet PROVE-WW-B4. The chamber geometry of Wang–Wu §4.5 (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`,
ruling R31: Proposition 4.20, "A component between two ordered simple arcs is bounded by one subarc of each …
This follows by applying the Jordan curve theorem"; Lemma 4.22) and of the specification's Lemma 7.1 is carried out
in the unit disc, where a simple proper curve of `ℍ` from `0` to `∞` becomes a **crosscut** from `−1` to `1`
(`ChamberSides.lean`).

A crosscut `α` (`IsDiscCrosscut`: continuous and injective on `[0, 1]`, `α 0 = −1`, `α 1 = 1`, interior points in the
open disc) closes with each semicircle into a Jordan curve. With `crossSide α 1` the inside of
`α[0, 1] ∪ (upper semicircle)` and `crossSide α (−1)` the inside of `α[0, 1] ∪ (lower semicircle)`:

* `crossSide_subset`: both sides lie in `𝔻 \ α[0, 1]`;
* `exists_ball_inter_subset_crossSide`: near a point of the open upper (lower) semicircle, the disc lies in the upper
  (lower) side;
* `disjoint_crossSide`: the two sides are disjoint;
* `subset_crossSide_union`: **they cover `𝔻 \ α[0, 1]`** (a component of `𝔻 \ α` outside both sides would be closed
  in the outside of `α ∪ (upper semicircle)`, hence equal to it, which is unbounded);
* `frontier_crossSide`, `crossRange_subset_closure_crossSide`: the crosscut lies on the frontier of both sides.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology

namespace InteractingSLE.WangWu

/-- A **crosscut of the unit disc** from `−1` to `1`: a path continuous and injective on `[0, 1]` whose interior
points lie in the open disc. -/
structure IsDiscCrosscut (α : ℝ → ℂ) : Prop where
  cont : ContinuousOn α (Icc 0 1)
  inj : InjOn α (Icc 0 1)
  zero : α 0 = -1
  one : α 1 = 1
  mem_disc : ∀ s ∈ Ioo (0 : ℝ) 1, α s ∈ ball (0 : ℂ) 1

/-- The range `α([0, 1])` of a crosscut. -/
def crossRange (α : ℝ → ℂ) : Set ℂ := α '' Icc 0 1

/-- The closed semicircle on the side `σ` (`σ = 1`: upper, `σ = −1`: lower), endpoints `±1` included. -/
def semiArc (σ : ℝ) : Set ℂ := {w | ‖w‖ = 1 ∧ 0 ≤ σ * w.im}

/-- The side `σ` of a crosscut: the inside of the Jordan curve `α([0, 1]) ∪ semiArc σ`. -/
def crossSide (α : ℝ → ℂ) (σ : ℝ) : Set ℂ := jordanIn (crossRange α ∪ semiArc σ)

/-! ### The semicircles -/

/-- The upper semicircle, traversed from `−1` to `1`. -/
def upperParam (s : ℝ) : ℂ := exp (((Real.pi * (1 - s) : ℝ) : ℂ) * I)

theorem continuous_upperParam : Continuous upperParam := by unfold upperParam; fun_prop

theorem upperParam_zero : upperParam 0 = -1 := by
  simp [upperParam, exp_mul_I]

theorem upperParam_one : upperParam 1 = 1 := by simp [upperParam]

theorem injOn_upperParam : InjOn upperParam (Icc 0 1) := by
  intro s hs t ht hst
  have harg : ∀ u ∈ Icc (0 : ℝ) 1, arg (upperParam u) = Real.pi * (1 - u) := by
    intro u hu
    rw [upperParam, exp_mul_I, arg_cos_add_sin_mul_I]
    constructor <;> nlinarith [Real.pi_pos, hu.1, hu.2]
  have := harg s hs
  rw [hst, harg t ht] at this
  have hpi := Real.pi_pos
  nlinarith

theorem image_upperParam : upperParam '' Icc 0 1 = semiArc 1 := by
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨by rw [upperParam, norm_exp_ofReal_mul_I], ?_⟩
    rw [one_mul, upperParam, exp_ofReal_mul_I_im]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, hs.2])
      (by nlinarith [Real.pi_pos, hs.1])
  · rintro ⟨hw, him⟩
    rw [one_mul] at him
    have hpi := Real.pi_pos
    have ha0 : 0 ≤ arg w := arg_nonneg_iff.2 him
    have hap : arg w ≤ Real.pi := arg_le_pi w
    refine ⟨1 - arg w / Real.pi, ⟨?_, ?_⟩, ?_⟩
    · rw [sub_nonneg, div_le_one hpi]; exact hap
    · linarith [div_nonneg ha0 hpi.le]
    · have : Real.pi * (1 - (1 - arg w / Real.pi)) = arg w := by field_simp; ring
      rw [upperParam, this]
      simpa [hw] using norm_mul_exp_arg_mul_I w

theorem image_conj_upperParam : (fun s => (starRingEnd ℂ) (upperParam s)) '' Icc 0 1 = semiArc (-1) := by
  rw [← image_image (g := starRingEnd ℂ), image_upperParam]
  ext w
  constructor
  · rintro ⟨v, ⟨hv, hvi⟩, rfl⟩
    exact ⟨by rw [norm_conj]; exact hv, by rw [conj_im]; linarith⟩
  · rintro ⟨hw, hwi⟩
    refine ⟨(starRingEnd ℂ) w, ⟨by rw [norm_conj]; exact hw, by rw [conj_im]; linarith⟩, conj_conj w⟩

theorem semiArc_subset_sphere (σ : ℝ) : semiArc σ ⊆ sphere 0 1 := fun _ hw => by
  rw [mem_sphere_zero_iff_norm]; exact hw.1

/-! ### Basic facts about a crosscut -/

namespace IsDiscCrosscut

variable {α : ℝ → ℂ}

theorem isCompact_crossRange (hα : IsDiscCrosscut α) : IsCompact (crossRange α) :=
  isCompact_Icc.image_of_continuousOn hα.cont

theorem crossRange_subset_closedBall (hα : IsDiscCrosscut α) : crossRange α ⊆ closedBall 0 1 := by
  rintro _ ⟨s, hs, rfl⟩
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0, hα.zero, mem_closedBall, dist_zero_right, norm_neg, norm_one]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · rw [h1, hα.one, mem_closedBall, dist_zero_right, norm_one]
  · exact ball_subset_closedBall (hα.mem_disc s ⟨h0, h1⟩)

/-- A point of the crosscut on the unit circle is one of its endpoints `±1`. -/
theorem eq_of_mem_crossRange_of_norm (hα : IsDiscCrosscut α) {w : ℂ} (hw : w ∈ crossRange α)
    (hn : ‖w‖ = 1) : w = -1 ∨ w = 1 := by
  obtain ⟨s, hs, rfl⟩ := hw
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · left; rw [← h0, hα.zero]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · right; rw [h1, hα.one]
  · have := hα.mem_disc s ⟨h0, h1⟩
    rw [mem_ball, dist_zero_right] at this
    linarith

theorem isJordanCurve_upper (hα : IsDiscCrosscut α) :
    LQGMetric.JordanMap.IsJordanCurve (crossRange α ∪ semiArc 1) := by
  have h := Sec7.isJordanCurve_image_union hα.cont continuous_upperParam.continuousOn hα.inj injOn_upperParam
    (by rw [hα.zero, upperParam_zero]) (by rw [hα.one, upperParam_one]) ?_
  · rwa [image_upperParam] at h
  rw [image_upperParam]
  rintro w ⟨hwα, hwS⟩
  rcases hα.eq_of_mem_crossRange_of_norm hwα hwS.1 with h | h
  · left; rw [h, hα.zero]
  · right; rw [h, hα.one]; rfl

theorem isJordanCurve_lower (hα : IsDiscCrosscut α) :
    LQGMetric.JordanMap.IsJordanCurve (crossRange α ∪ semiArc (-1)) := by
  have hc : ContinuousOn (fun s => (starRingEnd ℂ) (upperParam s)) (Icc 0 1) :=
    (continuous_conj.comp continuous_upperParam).continuousOn
  have hi : InjOn (fun s => (starRingEnd ℂ) (upperParam s)) (Icc 0 1) := fun s hs t ht h =>
    injOn_upperParam hs ht ((starRingEnd ℂ).injective h)
  have h := Sec7.isJordanCurve_image_union hα.cont hc hα.inj hi
    (by rw [hα.zero, upperParam_zero]; simp) (by rw [hα.one, upperParam_one]; simp) ?_
  · rwa [image_conj_upperParam] at h
  rw [image_conj_upperParam]
  rintro w ⟨hwα, hwS⟩
  rcases hα.eq_of_mem_crossRange_of_norm hwα hwS.1 with h | h
  · left; rw [h, hα.zero]
  · right; rw [h, hα.one]; rfl

theorem isJordanCurve (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    LQGMetric.JordanMap.IsJordanCurve (crossRange α ∪ semiArc σ) := by
  rcases hσ with rfl | rfl
  · exact hα.isJordanCurve_upper
  · exact hα.isJordanCurve_lower

end IsDiscCrosscut

/-! ### The θ-curve theorem -/

/-- The complement of the closed unit disc is preconnected. -/
theorem isPreconnected_one_lt_norm : IsPreconnected {w : ℂ | 1 < ‖w‖} := by
  have hconn : IsConnected ((sphere (0 : ℂ) 1) ×ˢ (Ioi (1 : ℝ))) :=
    (isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 zero_le_one).prod isConnected_Ioi
  have himg := hconn.image (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1)
    (by fun_prop : Continuous fun p : ℂ × ℝ => (p.2 : ℂ) * p.1).continuousOn
  have hset : (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) '' ((sphere (0 : ℂ) 1) ×ˢ (Ioi (1 : ℝ))) =
      {w : ℂ | 1 < ‖w‖} := by
    ext w
    constructor
    · rintro ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hu
      simp only [Set.mem_ofPred_eq, norm_mul, norm_real, Real.norm_eq_abs, hu, mul_one]
      exact lt_of_lt_of_le hr (le_abs_self r)
    · intro hw
      have hw0 : w ≠ 0 := fun h => by
        subst h
        have h' : (1 : ℝ) < ‖(0 : ℂ)‖ := hw
        rw [norm_zero] at h'
        linarith
      refine ⟨⟨w / (‖w‖ : ℂ), ‖w‖⟩, ⟨?_, hw⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_div, norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.2 hw0)]
      · have : (‖w‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hw0)
        simp only
        field_simp
  rw [← hset]
  exact himg.isPreconnected

theorem not_isBounded_one_lt_norm : ¬ IsBounded {w : ℂ | 1 < ‖w‖} := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall_lt 0 0
  have hmem : ((max R 1 + 1 : ℝ) : ℂ) ∈ {w : ℂ | 1 < ‖w‖} := by
    simp only [Set.mem_ofPred_eq, norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]; linarith [le_max_right R 1]
  have := hR.2 hmem
  rw [mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  linarith [le_max_left R 1]

namespace IsDiscCrosscut

variable {α : ℝ → ℂ}

theorem closure_ball_subset {Γ : Set ℂ} (hΓ : Γ ⊆ closedBall 0 1) : {w : ℂ | 1 < ‖w‖} ⊆ jordanOut Γ :=
  subset_jordanOut_of_isPreconnected isPreconnected_one_lt_norm not_isBounded_one_lt_norm
    (Set.disjoint_left.2 fun w hw hwΓ => by
      have := hΓ hwΓ
      rw [mem_closedBall, dist_zero_right] at this
      exact absurd hw (not_lt.2 this))

theorem union_semiArc_subset_closedBall (hα : IsDiscCrosscut α) (σ : ℝ) :
    crossRange α ∪ semiArc σ ⊆ closedBall 0 1 := by
  rintro w (hw | hw)
  · exact hα.crossRange_subset_closedBall hw
  · rw [mem_closedBall, dist_zero_right, hw.1]

/-- **Both sides lie in the open disc, off the crosscut.** -/
theorem crossSide_subset (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    crossSide α σ ⊆ ball 0 1 \ crossRange α := by
  set Γ := crossRange α ∪ semiArc σ
  have hΓ := hα.isJordanCurve hσ
  have hout := closure_ball_subset (hα.union_semiArc_subset_closedBall σ)
  intro z hz
  refine ⟨?_, fun h => hz.1 (Or.inl h)⟩
  rw [mem_ball, dist_zero_right]
  by_contra hz1
  push Not at hz1
  rcases eq_or_lt_of_le hz1 with heq | hlt
  · -- `z` on the circle, off the closed semicircle: push it out
    obtain ⟨ε, hε, hεz⟩ := Metric.isOpen_iff.1 (isOpen_jordanIn hΓ) z hz
    set w : ℂ := ((1 + ε / 2 : ℝ) : ℂ) * z
    have hwn : ‖w‖ = 1 + ε / 2 := by
      simp only [w, norm_mul, norm_real, Real.norm_eq_abs, ← heq, mul_one]
      exact abs_of_pos (by positivity)
    have hwz : dist w z < ε := by
      rw [dist_eq_norm]
      have : w - z = ((ε / 2 : ℝ) : ℂ) * z := by simp only [w]; push_cast; ring
      rw [this, norm_mul, norm_real, Real.norm_eq_abs, ← heq, mul_one, abs_of_pos (by positivity)]
      linarith
    exact Set.disjoint_left.1 (disjoint_jordanIn_jordanOut Γ) (hεz hwz)
      (hout (show 1 < ‖w‖ by rw [hwn]; linarith))
  · exact Set.disjoint_left.1 (disjoint_jordanIn_jordanOut Γ) hz (hout hlt)

/-- **Near a point of the open semicircle `σ`, the disc lies in the side `σ`.** -/
theorem exists_ball_inter_subset_crossSide (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℂ}
    (hp : ‖p‖ = 1) (hpσ : 0 < σ * p.im) :
    ∃ r > 0, ball p r ∩ ball 0 1 ⊆ crossSide α σ := by
  set Γ := crossRange α ∪ semiArc σ
  have hΓ := hα.isJordanCurve hσ
  have hpα : p ∉ crossRange α := fun h => by
    rcases hα.eq_of_mem_crossRange_of_norm h hp with h' | h' <;> simp [h'] at hpσ
  obtain ⟨r, hr, hrα⟩ := (Metric.isOpen_iff.1 hα.isCompact_crossRange.isClosed.isOpen_compl) p hpα
  refine ⟨r, hr, ?_⟩
  have hB : IsPreconnected (ball p r ∩ ball (0 : ℂ) 1) :=
    ((convex_ball p r).inter (convex_ball 0 1)).isPreconnected
  have hBΓ : Disjoint (ball p r ∩ ball (0 : ℂ) 1) Γ := by
    refine Set.disjoint_left.2 fun w hw hwΓ => ?_
    rcases hwΓ with h | h
    · exact hrα hw.1 h
    · have := hw.2
      rw [mem_ball, dist_zero_right, h.1] at this
      exact lt_irrefl _ this
  refine IsPreconnected.subset_jordanIn hΓ hB hBΓ ?_
  have hpcl : p ∈ closure (jordanIn Γ) := mem_closure_jordanIn hΓ (Or.inr ⟨hp, hpσ.le⟩)
  obtain ⟨w, hwI, hw⟩ := Metric.mem_closure_iff.1 hpcl r hr
  have hw1 := (hα.crossSide_subset hσ hwI).1
  exact ⟨w, ⟨by rw [mem_ball, dist_comm]; exact hw, hw1⟩, hwI⟩

theorem isOpen_crossSide (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : IsOpen (crossSide α σ) :=
  isOpen_jordanIn (hα.isJordanCurve hσ)

theorem isPreconnected_crossSide (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    IsPreconnected (crossSide α σ) :=
  isPreconnected_jordanIn (hα.isJordanCurve hσ)

theorem frontier_crossSide (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    frontier (crossSide α σ) = crossRange α ∪ semiArc σ :=
  frontier_jordanIn (hα.isJordanCurve hσ)

theorem crossRange_subset_closure_crossSide (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    crossRange α ⊆ closure (crossSide α σ) := fun _ hw =>
  mem_closure_jordanIn (hα.isJordanCurve hσ) (Or.inl hw)

theorem semiArc_subset_closure_crossSide (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    semiArc σ ⊆ closure (crossSide α σ) := fun _ hw =>
  mem_closure_jordanIn (hα.isJordanCurve hσ) (Or.inr hw)

theorem closure_crossSide (hα : IsDiscCrosscut α) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    closure (crossSide α σ) = crossSide α σ ∪ (crossRange α ∪ semiArc σ) :=
  closure_jordanIn (hα.isJordanCurve hσ)

/-- The point `−i` of the lower semicircle lies outside `α ∪ (upper semicircle)`. -/
theorem neg_I_mem_jordanOut_upper (hα : IsDiscCrosscut α) :
    -I ∈ jordanOut (crossRange α ∪ semiArc 1) := by
  have hn : ‖-I‖ = 1 := by simp
  have hnot : -I ∉ crossRange α ∪ semiArc 1 := by
    rintro (h | h)
    · rcases hα.eq_of_mem_crossRange_of_norm h hn with h' | h'
      · have := congrArg Complex.im h'; simp at this
      · have := congrArg Complex.im h'; simp at this
    · have := h.2; norm_num at this
  have hin : -I ∉ jordanIn (crossRange α ∪ semiArc 1) := fun h => by
    have := (hα.crossSide_subset (Or.inl rfl) h).1
    rw [mem_ball, dist_zero_right, hn] at this
    exact lt_irrefl _ this
  rcases (compl_eq_jordanIn_union_jordanOut (crossRange α ∪ semiArc 1)).subset hnot with h | h
  · exact absurd h hin
  · exact h

/-- **The two sides are disjoint.** -/
theorem disjoint_crossSide (hα : IsDiscCrosscut α) : Disjoint (crossSide α 1) (crossSide α (-1)) := by
  set Γ₁ := crossRange α ∪ semiArc 1
  set Γ₂ := crossRange α ∪ semiArc (-1)
  have hΓ₁ := hα.isJordanCurve_upper
  have hΓ₂ := hα.isJordanCurve_lower
  -- the lower side lies outside `Γ₁`
  have hsub : crossSide α (-1) ⊆ jordanOut Γ₁ := by
    refine IsPreconnected.subset_jordanOut hΓ₁ (hα.isPreconnected_crossSide (Or.inr rfl)) ?_ ?_
    · refine Set.disjoint_left.2 fun w hw hwΓ => ?_
      have hw' := hα.crossSide_subset (Or.inr rfl) hw
      rcases hwΓ with h | h
      · exact hw'.2 h
      · have := hw'.1
        rw [mem_ball, dist_zero_right, h.1] at this
        exact lt_irrefl _ this
    · obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 (isOpen_jordanOut hΓ₁) _ hα.neg_I_mem_jordanOut_upper
      have hcl : -I ∈ closure (crossSide α (-1)) :=
        hα.semiArc_subset_closure_crossSide (Or.inr rfl) ⟨by simp, by simp⟩
      obtain ⟨w, hwS, hw⟩ := Metric.mem_closure_iff.1 hcl r hr
      exact ⟨w, hwS, hrO (by rw [mem_ball, dist_comm]; exact hw)⟩
  exact Set.disjoint_left.2 fun w h₁ h₂ =>
    Set.disjoint_left.1 (disjoint_jordanIn_jordanOut Γ₁) h₁ (hsub h₂)

/-- **The two sides cover the disc off the crosscut** (θ-curve theorem). -/
theorem subset_crossSide_union (hα : IsDiscCrosscut α) :
    ball 0 1 \ crossRange α ⊆ crossSide α 1 ∪ crossSide α (-1) := by
  set Γ₁ := crossRange α ∪ semiArc 1
  set Γ₂ := crossRange α ∪ semiArc (-1)
  have hΓ₁ := hα.isJordanCurve_upper
  have hΓ₂ := hα.isJordanCurve_lower
  set U := ball (0 : ℂ) 1 \ crossRange α with hU
  have hUo : IsOpen U := isOpen_ball.sdiff hα.isCompact_crossRange.isClosed
  have hUΓ : ∀ σ : ℝ, Disjoint U (crossRange α ∪ semiArc σ) := fun σ =>
    Set.disjoint_left.2 fun w hw hwΓ => by
      rcases hwΓ with h | h
      · exact hw.2 h
      · have := hw.1
        rw [mem_ball, dist_zero_right, h.1] at this
        exact lt_irrefl _ this
  intro z hz
  by_contra hzn
  rw [mem_union, not_or] at hzn
  set Q := connectedComponentIn U z with hQ
  have hQU : Q ⊆ U := connectedComponentIn_subset U z
  have hQo : IsOpen Q := hUo.connectedComponentIn
  have hQc : IsPreconnected Q := isPreconnected_connectedComponentIn
  have hzQ : z ∈ Q := mem_connectedComponentIn hz
  have hzout : ∀ σ : ℝ, z ∉ crossSide α σ → z ∈ jordanOut (crossRange α ∪ semiArc σ) := fun σ h => by
    rcases (compl_eq_jordanIn_union_jordanOut (crossRange α ∪ semiArc σ)).subset
      (Set.disjoint_left.1 (hUΓ σ) hz) with h' | h'
    · exact absurd h' h
    · exact h'
  have hQ₁ : Q ⊆ jordanOut Γ₁ := IsPreconnected.subset_jordanOut hΓ₁ hQc
    ((hUΓ 1).mono_left hQU) ⟨z, hzQ, hzout 1 hzn.1⟩
  have hQ₂ : Q ⊆ jordanOut Γ₂ := IsPreconnected.subset_jordanOut hΓ₂ hQc
    ((hUΓ (-1)).mono_left hQU) ⟨z, hzQ, hzout (-1) hzn.2⟩
  -- `jordanOut Γ₁ ⊆ Q`
  have hsub : jordanOut Γ₁ ⊆ Q := by
    refine (isPreconnected_jordanOut hΓ₁).subset_of_closure_inter_subset hQo
      ⟨z, hQ₁ hzQ, hzQ⟩ ?_
    rintro w ⟨hwcl, hwO⟩
    by_cases hwU : w ∈ U
    · -- closure points of a component inside the open set belong to it
      have hW : connectedComponentIn U w ∩ Q ≠ ∅ := by
        obtain ⟨v, hv, hvQ⟩ := mem_closure_iff.1 hwcl _ (hUo.connectedComponentIn)
          (mem_connectedComponentIn hwU)
        exact Set.nonempty_iff_ne_empty.1 ⟨v, hv, hvQ⟩
      obtain ⟨v, hv, hvQ⟩ := Set.nonempty_iff_ne_empty.2 hW
      rw [hQ] at hvQ ⊢
      rw [connectedComponentIn_eq hvQ, ← connectedComponentIn_eq hv]
      exact mem_connectedComponentIn hwU
    · exfalso
      have hwnot : w ∉ Γ₁ := hwO.1
      have hwcb : w ∈ closedBall (0 : ℂ) 1 :=
        closure_minimal (hQU.trans (sdiff_subset.trans ball_subset_closedBall)) isClosed_closedBall hwcl
      rw [mem_closedBall, dist_zero_right] at hwcb
      have hwα : w ∉ crossRange α := fun h => hwnot (Or.inl h)
      have hwn : ‖w‖ = 1 := by
        rcases eq_or_lt_of_le hwcb with h | h
        · exact h
        · exact absurd ⟨by rw [mem_ball, dist_zero_right]; exact h, hwα⟩ hwU
      have hwim : w.im < 0 := by
        by_contra h
        push Not at h
        exact hwnot (Or.inr ⟨hwn, by rw [one_mul]; exact h⟩)
      obtain ⟨r, hr, hrS⟩ := hα.exists_ball_inter_subset_crossSide (Or.inr rfl) hwn (by linarith)
      obtain ⟨v, hvQ, hv⟩ := Metric.mem_closure_iff.1 hwcl r hr
      have hvS : v ∈ crossSide α (-1) := hrS ⟨by rw [mem_ball, dist_comm]; exact hv, (hQU hvQ).1⟩
      exact Set.disjoint_left.1 (disjoint_jordanIn_jordanOut Γ₂) hvS (hQ₂ hvQ)
  -- but `Q` is bounded and the outside is not
  exact (JordanSides hΓ₁).2.2.2.2.2.2.1 ((isBounded_ball (x := (0 : ℂ)) (r := 1)).subset
    (hsub.trans (hQU.trans sdiff_subset)))

end IsDiscCrosscut

end InteractingSLE.WangWu
