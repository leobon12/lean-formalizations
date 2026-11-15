/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.closedLeftSide
import InteractingSLE.Frozen.Spec.IsProperCompletion
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import InteractingSLE.Spec.Supplement.S7ArcUnion
import InteractingSLE.Foundations.Topology.Schoenflies.Plane
import InteractingSLE.Foundations.Topology.PathComplement.Torhorst

/-!
# Supplement §9 (continued): the two sides of a proper completion

Packet PROVE-SUPP9-B. Convention W0 (p. 528) orders two completed curves by "closed Jordan-side containment":
`closedLeftSide γ` is the component of `γ(0) − 1 − i` in the complement of `seedRayClosure γ` (the curve closed
along its lower vertical ray), together with `seedRayClosure γ`. This file proves the planar topology that makes
this predicate usable:

* **Jordan separation** (`disjoint_leftSide_rightSide`): for a proper curve `γ` from a real seed, the left
  reference point `γ(0) − 1 − i` and the right reference point `γ(0) + 1 − i` lie in different components. The
  proof closes `seedRayClosure γ` through `∞` by the inversion `z ↦ (z − p)⁻¹` at `p = γ(0) + 1 − i`, which
  gives a Jordan curve (`isJordanCurve_invImage`), and applies the Jordan curve theorem; the two half-discs at the
  ray point `γ(0) − i/2` lie on different sides because that point is on the frontier of both components.
* **The side principle** (`eventually_mem_leftSide_of_eqOn`): if two proper curves agree on `[0, A]`, then near any
  point `γ(t₀)` with `t₀ < A` they have the same left side. The proof straightens the first closed curve with the
  Schoenflies theorem and joins the two points inside a thin annular sector along the common arc, which the tail of
  the second curve cannot reach.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal

namespace InteractingSLE

namespace Supp9B

/-! ### Proper curves and their sides -/

/-- A proper curve in the closed upper half-plane: continuous, injective, with nonnegative imaginary part,
tending to `∞`. These are the first four conjuncts of `IsProperCompletion`. -/
def IsProperCurve (γ : ℝ≥0 → ℂ) : Prop :=
  Continuous γ ∧ Function.Injective γ ∧ (∀ t, 0 ≤ (γ t).im) ∧ Tendsto (fun t => ‖γ t‖) atTop atTop

theorem isProperCurve_of_isProperCompletion {γ γ' : ℝ≥0 → ℂ} {a : ℝ≥0}
    (h : IsProperCompletion γ a γ') : IsProperCurve γ' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The open left side of a curve closed along its lower vertical ray. -/
def leftSide (γ : ℝ≥0 → ℂ) : Set ℂ :=
  connectedComponentIn (seedRayClosure γ)ᶜ (γ 0 - 1 - I)

/-- The open right side of a curve closed along its lower vertical ray. -/
def rightSide (γ : ℝ≥0 → ℂ) : Set ℂ :=
  connectedComponentIn (seedRayClosure γ)ᶜ (γ 0 + 1 - I)

theorem closedLeftSide_eq (γ : ℝ≥0 → ℂ) : closedLeftSide γ = leftSide γ ∪ seedRayClosure γ := rfl

/-- The open lower-left quadrant at `x`. -/
def lowerLeft (x : ℝ) : Set ℂ := {z | z.re < x ∧ z.im < 0}

/-- The open lower-right quadrant at `x`. -/
def lowerRight (x : ℝ) : Set ℂ := {z | x < z.re ∧ z.im < 0}

theorem isOpen_lowerLeft (x : ℝ) : IsOpen (lowerLeft x) :=
  (isOpen_lt continuous_re continuous_const).inter (isOpen_lt continuous_im continuous_const)

theorem isOpen_lowerRight (x : ℝ) : IsOpen (lowerRight x) :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_im continuous_const)

theorem convex_lowerLeft (x : ℝ) : Convex ℝ (lowerLeft x) :=
  (convex_halfSpace_re_lt x).inter (convex_halfSpace_im_lt 0)

theorem convex_lowerRight (x : ℝ) : Convex ℝ (lowerRight x) :=
  (convex_halfSpace_re_gt x).inter (convex_halfSpace_im_lt 0)

variable {γ : ℝ≥0 → ℂ}

theorem notMem_seedRayClosure_of_im_neg (hγ : ∀ t, 0 ≤ (γ t).im) {z : ℂ} (hz : z.im < 0)
    (hre : z.re ≠ (γ 0).re) : z ∉ seedRayClosure γ := by
  rintro (⟨t, rfl⟩ | ⟨h, -⟩)
  · exact absurd (hγ t) (not_le.2 hz)
  · exact hre h

theorem lowerLeft_subset_compl (hγ : ∀ t, 0 ≤ (γ t).im) :
    lowerLeft (γ 0).re ⊆ (seedRayClosure γ)ᶜ := fun _ hz =>
  notMem_seedRayClosure_of_im_neg hγ hz.2 hz.1.ne

theorem lowerRight_subset_compl (hγ : ∀ t, 0 ≤ (γ t).im) :
    lowerRight (γ 0).re ⊆ (seedRayClosure γ)ᶜ := fun _ hz =>
  notMem_seedRayClosure_of_im_neg hγ hz.2 hz.1.ne'

theorem left_ref_mem_lowerLeft (h0 : (γ 0).im = 0) : γ 0 - 1 - I ∈ lowerLeft (γ 0).re := by
  constructor <;> simp [h0]

theorem right_ref_mem_lowerRight (h0 : (γ 0).im = 0) : γ 0 + 1 - I ∈ lowerRight (γ 0).re := by
  constructor <;> simp [h0]

theorem lowerLeft_subset_leftSide (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) :
    lowerLeft (γ 0).re ⊆ leftSide γ :=
  (convex_lowerLeft _).isPreconnected.subset_connectedComponentIn (left_ref_mem_lowerLeft h0)
    (lowerLeft_subset_compl hγ)

theorem lowerRight_subset_rightSide (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) :
    lowerRight (γ 0).re ⊆ rightSide γ :=
  (convex_lowerRight _).isPreconnected.subset_connectedComponentIn (right_ref_mem_lowerRight h0)
    (lowerRight_subset_compl hγ)

/-- A real point to the left of the seed and off the curve is on the left side. -/
theorem ofReal_mem_leftSide (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) {x : ℝ}
    (hx : x < (γ 0).re) (hxγ : (x : ℂ) ∉ seedRayClosure γ) : (x : ℂ) ∈ leftSide γ := by
  have hcl : (x : ℂ) ∈ closure (lowerLeft (γ 0).re) := by
    have ht : Tendsto (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have : Continuous (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    constructor <;> simp [hx, show (0 : ℝ) < s from hs]
  have hpc : IsPreconnected (insert (x : ℂ) (lowerLeft (γ 0).re)) :=
    (convex_lowerLeft _).isPreconnected.subset_closure (subset_insert _ _)
      (insert_subset hcl subset_closure)
  exact hpc.subset_connectedComponentIn (mem_insert_of_mem _ (left_ref_mem_lowerLeft h0))
    (insert_subset hxγ (lowerLeft_subset_compl hγ)) (mem_insert _ _)

/-! ### Inversion -/

/-- The inversion `z ↦ (z − p)⁻¹`. -/
def inv (p z : ℂ) : ℂ := (z - p)⁻¹

/-- Its inverse `w ↦ p + w⁻¹`. -/
def uninv (p w : ℂ) : ℂ := p + w⁻¹

@[simp] theorem uninv_inv (p z : ℂ) : uninv p (inv p z) = z := by
  simp [uninv, inv]

@[simp] theorem inv_uninv (p w : ℂ) : inv p (uninv p w) = w := by
  simp [uninv, inv]

theorem inv_apply_ne_zero {p z : ℂ} (hz : z ≠ p) : inv p z ≠ 0 :=
  _root_.inv_ne_zero (sub_ne_zero.2 hz)

theorem uninv_ne {p w : ℂ} (hw : w ≠ 0) : uninv p w ≠ p := by
  simp [uninv, hw]

theorem continuousOn_inv (p : ℂ) : ContinuousOn (inv p) {p}ᶜ :=
  (continuousOn_id.sub continuousOn_const).inv₀ fun _ hz h =>
    hz (mem_singleton_iff.2 (sub_eq_zero.1 h))

theorem continuousOn_uninv (p : ℂ) : ContinuousOn (uninv p) {0}ᶜ :=
  continuousOn_const.add (continuousOn_inv₀.mono fun _ h => h)

theorem continuousAt_inv {p z : ℂ} (hz : z ≠ p) : ContinuousAt (inv p) z :=
  (continuousOn_inv p).continuousAt (isOpen_compl_singleton.mem_nhds hz)

theorem continuousAt_uninv {p w : ℂ} (hw : w ≠ 0) : ContinuousAt (uninv p) w :=
  (continuousOn_uninv p).continuousAt (isOpen_compl_singleton.mem_nhds hw)

theorem inv_injective (p : ℂ) : Function.Injective (inv p) := fun z w h => by
  rw [← uninv_inv p z, ← uninv_inv p w, h]

/-- `inv p` tends to `0` at `∞`. -/
theorem tendsto_inv_cobounded (p : ℂ) : Tendsto (inv p) (cobounded ℂ) (𝓝 0) := by
  have h : Tendsto (fun z : ℂ => z - p) (cobounded ℂ) (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine tendsto_atTop_mono (fun z => ?_) (tendsto_atTop_add_const_right _ (-‖p‖)
      (tendsto_norm_cobounded_atTop))
    have := norm_sub_norm_le z p
    linarith
  exact tendsto_inv₀_cobounded.comp h

/-- Near `p`, `inv p` is large. -/
theorem tendsto_inv_nhdsNE (p : ℂ) : Tendsto (inv p) (𝓝[≠] p) (cobounded ℂ) := by
  have h : Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Continuous (fun z : ℂ => z - p) := by fun_prop
      simpa using (this.tendsto p).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.2 hz
  exact tendsto_inv₀_nhdsNE_zero.comp h

/-! ### A proper line closed through `∞` is a Jordan curve -/

/-- The reparametrization `s ↦ s/(1 − s)` of `[0, 1)` onto `[0, ∞)`. -/
def stretch (s : ℝ) : ℝ := s / (1 - s)

theorem stretch_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) : 0 ≤ stretch s :=
  div_nonneg h0 (by linarith)

theorem stretch_injOn : InjOn stretch (Iio 1) := fun s hs t ht h => by
  have hs' : (1 - s) ≠ 0 := by have := mem_Iio.1 hs; linarith
  have ht' : (1 - t) ≠ 0 := by have := mem_Iio.1 ht; linarith
  unfold stretch at h
  rw [div_eq_div_iff hs' ht'] at h
  linarith

theorem stretch_unstretch {t : ℝ} (ht : 0 ≤ t) : stretch (t / (1 + t)) = t := by
  unfold stretch
  have h1 : (1 + t) ≠ 0 := by linarith
  rw [show 1 - t / (1 + t) = 1 / (1 + t) by field_simp; ring]
  field_simp

/-- The closed arc `s ↦ (g(s/(1 − s)) − p)⁻¹`, `s < 1`, ending at `0`, of a proper injective path `g` on `[0, ∞)`
avoiding `p`. -/
def closeArc (p : ℂ) (g : ℝ → ℂ) (s : ℝ) : ℂ := if s < 1 then inv p (g (stretch s)) else 0

theorem continuousOn_closeArc {p : ℂ} {g : ℝ → ℂ} (hg : ContinuousOn g (Ici 0))
    (hgi : Tendsto (fun t => ‖g t‖) atTop atTop) (hp : ∀ t, 0 ≤ t → g t ≠ p) :
    ContinuousOn (closeArc p g) (Icc 0 1) := by
  intro s hs
  rcases lt_or_eq_of_le hs.2 with h1 | rfl
  · have hF : ContinuousOn (fun s => inv p (g (stretch s))) (Ico 0 1) := by
      have hst : ContinuousOn stretch (Ico 0 1) := by
        show ContinuousOn (fun s : ℝ => s / (1 - s)) (Ico 0 1)
        exact continuousOn_id.div (continuousOn_const.sub continuousOn_id) fun x hx =>
          sub_ne_zero.2 (ne_of_gt hx.2)
      have hgs : ContinuousOn (fun s => g (stretch s)) (Ico 0 1) :=
        hg.comp hst fun x hx => stretch_nonneg hx.1 hx.2
      exact (continuousOn_inv p).comp hgs fun x hx => hp _ (stretch_nonneg hx.1 hx.2)
    have hmem : Ico (0 : ℝ) 1 ∈ 𝓝[Icc 0 1] s := by
      have he : Ico (0 : ℝ) 1 = Icc 0 1 ∩ Iio 1 := by
        ext x
        simp only [mem_Ico, mem_Icc, mem_inter_iff, mem_Iio]
        exact ⟨fun h => ⟨⟨h.1, h.2.le⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
      rw [he]
      exact inter_mem_nhdsWithin _ (Iio_mem_nhds h1)
    have hcw : ContinuousWithinAt (fun s => inv p (g (stretch s))) (Icc 0 1) s :=
      (hF s ⟨hs.1, h1⟩).mono_of_mem_nhdsWithin hmem
    refine hcw.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hmem] with x hx
      simp only [closeArc, hx.2, ↓reduceIte]
    · simp only [closeArc, h1, ↓reduceIte]
  · have hlim : Tendsto (fun t => inv p (g t)) atTop (𝓝 0) :=
      (tendsto_inv_cobounded p).comp (tendsto_norm_atTop_iff_cobounded.1 hgi)
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
    set T' := max T 0 with hT'
    have hT'0 : 0 ≤ T' := le_max_right _ _
    refine ⟨1 / (T' + 1), by positivity, fun x hx hxd => ?_⟩
    have h11 : closeArc p g 1 = 0 := by simp [closeArc]
    rw [h11, dist_zero_right]
    by_cases hx1 : x < 1
    · simp only [closeArc, hx1, ↓reduceIte]
      have h1x : 0 < 1 - x := by linarith
      have hd : 1 - x < 1 / (T' + 1) := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos h1x] at hxd; exact hxd
      have hm : (1 - x) * (T' + 1) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at hd
      have hTs : T ≤ stretch x := by
        refine (le_max_left T 0).trans ?_
        unfold stretch
        rw [le_div_iff₀ h1x]
        nlinarith
      simpa [dist_zero_right] using hT _ hTs
    · simp [closeArc, hx1, hε]

theorem closeArc_of_lt {p : ℂ} {g : ℝ → ℂ} {s : ℝ} (hs : s < 1) :
    closeArc p g s = inv p (g (stretch s)) := by
  simp [closeArc, hs]

theorem closeArc_one (p : ℂ) (g : ℝ → ℂ) : closeArc p g 1 = 0 := by
  simp [closeArc]

theorem closeArc_zero (p : ℂ) (g : ℝ → ℂ) : closeArc p g 0 = inv p (g 0) := by
  simp [closeArc, stretch]

theorem injOn_closeArc {p : ℂ} {g : ℝ → ℂ} (hinj : InjOn g (Ici 0)) (hp : ∀ t, 0 ≤ t → g t ≠ p) :
    InjOn (closeArc p g) (Icc 0 1) := by
  intro s hs t ht h
  by_cases hs1 : s < 1 <;> by_cases ht1 : t < 1
  · rw [closeArc_of_lt hs1, closeArc_of_lt ht1] at h
    exact stretch_injOn hs1 ht1
      (hinj (stretch_nonneg hs.1 hs1) (stretch_nonneg ht.1 ht1) (inv_injective p h))
  · rw [closeArc_of_lt hs1, show t = 1 from le_antisymm ht.2 (not_lt.1 ht1), closeArc_one] at h
    exact absurd h (inv_apply_ne_zero (hp _ (stretch_nonneg hs.1 hs1)))
  · rw [closeArc_of_lt ht1, show s = 1 from le_antisymm hs.2 (not_lt.1 hs1), closeArc_one] at h
    exact absurd h.symm (inv_apply_ne_zero (hp _ (stretch_nonneg ht.1 ht1)))
  · rw [show s = 1 from le_antisymm hs.2 (not_lt.1 hs1), show t = 1 from le_antisymm ht.2 (not_lt.1 ht1)]

theorem image_closeArc (p : ℂ) (g : ℝ → ℂ) :
    closeArc p g '' Icc 0 1 = inv p '' (g '' Ici 0) ∪ {0} := by
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    by_cases hs1 : s < 1
    · rw [closeArc_of_lt hs1]
      exact Or.inl ⟨g (stretch s), ⟨stretch s, stretch_nonneg hs.1 hs1, rfl⟩, rfl⟩
    · rw [show s = 1 from le_antisymm hs.2 (not_lt.1 hs1), closeArc_one]
      exact Or.inr rfl
  · rintro (⟨_, ⟨t, ht, rfl⟩, rfl⟩ | h)
    · have ht' : (0 : ℝ) ≤ t := ht
      refine ⟨t / (1 + t), ⟨div_nonneg ht' (by linarith), ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]; linarith
      · rw [closeArc_of_lt (by rw [div_lt_one (by linarith)]; linarith), stretch_unstretch ht']
    · rw [mem_singleton_iff.1 h]
      exact ⟨1, ⟨zero_le_one, le_rfl⟩, closeArc_one p g⟩

/-- Two proper injective paths on `[0, ∞)` from a common point, meeting only there and avoiding `p`, close up
under `z ↦ (z − p)⁻¹` (with the point `0` at `∞`) to a Jordan curve. -/
theorem isJordanCurve_inv_image {p : ℂ} {g₁ g₂ : ℝ → ℂ} (hc₁ : ContinuousOn g₁ (Ici 0))
    (hc₂ : ContinuousOn g₂ (Ici 0)) (hi₁ : InjOn g₁ (Ici 0)) (hi₂ : InjOn g₂ (Ici 0))
    (hn₁ : Tendsto (fun t => ‖g₁ t‖) atTop atTop) (hn₂ : Tendsto (fun t => ‖g₂ t‖) atTop atTop)
    (hp₁ : ∀ t, 0 ≤ t → g₁ t ≠ p) (hp₂ : ∀ t, 0 ≤ t → g₂ t ≠ p) (h0 : g₁ 0 = g₂ 0)
    (hdisj : ∀ s t, 0 ≤ s → 0 ≤ t → g₁ s = g₂ t → s = 0) :
    LQGMetric.JordanMap.IsJordanCurve (inv p '' (g₁ '' Ici 0 ∪ g₂ '' Ici 0) ∪ {0}) := by
  set a : unitInterval → ℂ := fun s => closeArc p g₁ s with ha
  set b : unitInterval → ℂ := fun s => closeArc p g₂ s with hb
  have hca : Continuous a :=
    (continuousOn_closeArc hc₁ hn₁ hp₁).comp_continuous continuous_subtype_val fun s => s.2
  have hcb : Continuous b :=
    (continuousOn_closeArc hc₂ hn₂ hp₂).comp_continuous continuous_subtype_val fun s => s.2
  have hia : Function.Injective a := fun s t h =>
    Subtype.ext (injOn_closeArc hi₁ hp₁ s.2 t.2 h)
  have hib : Function.Injective b := fun s t h =>
    Subtype.ext (injOn_closeArc hi₂ hp₂ s.2 t.2 h)
  have hra : range a = inv p '' (g₁ '' Ici 0) ∪ {0} := by
    rw [← image_closeArc, ha, show (fun s : unitInterval => closeArc p g₁ s) =
      closeArc p g₁ ∘ Subtype.val from rfl, range_comp, Subtype.range_coe]
  have hrb : range b = inv p '' (g₂ '' Ici 0) ∪ {0} := by
    rw [← image_closeArc, hb, show (fun s : unitInterval => closeArc p g₂ s) =
      closeArc p g₂ ∘ Subtype.val from rfl, range_comp, Subtype.range_coe]
  have ha0 : a 0 = inv p (g₁ 0) := closeArc_zero p g₁
  have hb0 : b 0 = inv p (g₂ 0) := closeArc_zero p g₂
  have ha1 : a 1 = 0 := closeArc_one p g₁
  have hb1 : b 1 = 0 := closeArc_one p g₂
  have hJ := Supp7.ArcUnion.jordanCurve_union_of_arcs hca hia hcb hib (by rw [ha0, hb0, h0])
    (by rw [ha1, hb1]) (by
      apply Subset.antisymm
      · rintro w ⟨hwa, hwb⟩
        rw [hra] at hwa
        rw [hrb] at hwb
        rcases hwa with ⟨_, ⟨s, hs, rfl⟩, rfl⟩ | hw0
        · rcases hwb with ⟨_, ⟨t, ht, hst⟩, hst'⟩ | hw0'
          · have heq : g₁ s = g₂ t := inv_injective p (hst' ▸ hst ▸ rfl) |>.symm
            have := hdisj s t hs ht heq
            subst this
            exact Or.inl ha0.symm
          · exact absurd (mem_singleton_iff.1 hw0') (inv_apply_ne_zero (hp₁ s hs))
        · exact Or.inr (by rw [mem_singleton_iff.1 hw0, ha1]; rfl)
      · rintro w (rfl | hw)
        · exact ⟨mem_range_self _, 0, by rw [ha0, hb0, h0]⟩
        · rw [mem_singleton_iff.1 hw]
          exact ⟨mem_range_self _, 1, by rw [ha1, hb1]⟩)
  rwa [hra, hrb, ← union_union_distrib_right, ← image_union] at hJ

/-! ### The Jordan curve of a proper curve from a real seed -/

/-- The right reference point `γ(0) + 1 − i`, the centre of the inversion. -/
def rightRef (γ : ℝ≥0 → ℂ) : ℂ := γ 0 + 1 - I

/-- The closed curve `seedRayClosure γ ∪ {∞}` in inversion coordinates at `rightRef γ`. -/
def invCurve (γ : ℝ≥0 → ℂ) : Set ℂ := inv (rightRef γ) '' seedRayClosure γ ∪ {0}

theorem rightRef_notMem (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) :
    rightRef γ ∉ seedRayClosure γ :=
  lowerRight_subset_compl hγ (right_ref_mem_lowerRight h0)

theorem isJordanCurve_invCurve (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    LQGMetric.JordanMap.IsJordanCurve (invCurve γ) := by
  obtain ⟨hc, hi, him, hn⟩ := hγ
  set p := rightRef γ with hp
  have hpim : p.im = -1 := by simp [hp, rightRef, h0]
  have hpre : p.re = (γ 0).re + 1 := by simp [hp, rightRef]
  have key := isJordanCurve_inv_image (p := p) (g₁ := fun t : ℝ => γ t.toNNReal)
    (g₂ := fun t : ℝ => γ 0 - (t : ℂ) * I)
    ((hc.comp continuous_real_toNNReal).continuousOn) (by fun_prop)
    (fun s hs t ht h => by
      have := hi h
      rw [← Real.coe_toNNReal s hs, ← Real.coe_toNNReal t ht, this])
    (fun s _ t _ h => by
      have := congrArg Complex.im h
      simpa using this)
    (hn.comp tendsto_real_toNNReal_atTop)
    (by
      refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-‖γ 0‖) tendsto_abs_atTop_atTop)
      have h1 : ‖(t : ℂ) * I‖ = |t| := by simp
      have := norm_sub_norm_le ((t : ℂ) * I) (γ 0)
      rw [h1, norm_sub_rev] at this
      linarith)
    (fun t _ h => by
      have := congrArg Complex.im h
      rw [hpim] at this
      linarith [him t.toNNReal])
    (fun t _ h => by
      have := congrArg Complex.re h
      simp [hpre] at this)
    (by simp)
    (fun s t hs ht h => by
      have him' := congrArg Complex.im h
      simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
        h0, zero_sub] at him'
      have ht0 : t = 0 := by linarith [him s.toNNReal]
      subst ht0
      simp only [ofReal_zero, zero_mul, sub_zero] at h
      have := hi (h.trans (congrArg γ Real.toNNReal_zero).symm)
      rw [← Real.coe_toNNReal s hs, this, Real.toNNReal_zero, NNReal.coe_zero])
  have h1 : (fun t : ℝ => γ t.toNNReal) '' Ici 0 = range γ := by
    ext z
    constructor
    · rintro ⟨t, -, rfl⟩; exact mem_range_self _
    · rintro ⟨t, rfl⟩; exact ⟨t, t.2, by simp⟩
  have h2 : (fun t : ℝ => γ 0 - (t : ℂ) * I) '' Ici 0 =
      {z | z.re = (γ 0).re ∧ z.im ≤ (γ 0).im} := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : (0 : ℝ) ≤ t := ht
      constructor <;> simp [h0, ht']
    · rintro ⟨hre, him'⟩
      refine ⟨-z.im, by simp only [mem_Ici]; linarith [h0 ▸ him'], ?_⟩
      apply Complex.ext <;> simp [hre, h0]
  rw [h1, h2] at key
  exact key

theorem inv_mem_invCurve {p z : ℂ} (hz : z ∈ seedRayClosure γ) (hp : p = rightRef γ) :
    inv p z ∈ invCurve γ := by
  subst hp; exact Or.inl ⟨z, hz, rfl⟩

/-- A point off `seedRayClosure γ ∪ {p}` maps off the inverted curve. -/
theorem inv_notMem_invCurve {z : ℂ} (hz : z ∉ seedRayClosure γ) (hzp : z ≠ rightRef γ) :
    inv (rightRef γ) z ∉ invCurve γ := by
  rintro (⟨z', hz', h⟩ | h)
  · exact hz (inv_injective _ h ▸ hz')
  · exact inv_apply_ne_zero hzp (mem_singleton_iff.1 h)

/-- A point off the inverted curve pulls back off `seedRayClosure γ`. -/
theorem uninv_notMem {w : ℂ} (hw : w ∉ invCurve γ) : uninv (rightRef γ) w ∉ seedRayClosure γ :=
  fun h => hw (by simpa using inv_mem_invCurve h rfl)

theorem ne_zero_of_notMem_invCurve {w : ℂ} (hw : w ∉ invCurve γ) : w ≠ 0 :=
  fun h => hw (Or.inr (mem_singleton_iff.2 h))

theorem isPreconnected_lowerRight_diff (x : ℝ) {p : ℂ} (hp : ball p (1 / 2) ⊆ lowerRight x) :
    IsPreconnected (lowerRight x \ {p}) :=
  isPreconnected_diff_singleton_of_ball_subset (convex_lowerRight x).isPreconnected (by norm_num) hp

theorem ball_rightRef_subset (h0 : (γ 0).im = 0) : ball (rightRef γ) (1 / 2) ⊆ lowerRight (γ 0).re := by
  intro z hz
  have hd : ‖z - rightRef γ‖ < 1 / 2 := by rwa [mem_ball, dist_eq_norm] at hz
  have hre := (abs_re_le_norm (z - rightRef γ)).trans_lt hd
  have him := (abs_im_le_norm (z - rightRef γ)).trans_lt hd
  simp only [rightRef, sub_re, add_re, one_re, I_re, sub_zero, sub_im, add_im, one_im, I_im, h0] at hre him
  constructor
  · linarith [abs_lt.1 hre]
  · linarith [abs_lt.1 him]

/-- **The two complementary components of the inverted curve.** The bounded one contains the image of the
lower-left quadrant and the unbounded one the image of the punctured lower-right quadrant. -/
theorem exists_jordan_sides (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsBounded U ∧ IsPreconnected U ∧ IsPreconnected V ∧
      Disjoint U V ∧ (invCurve γ)ᶜ = U ∪ V ∧ frontier U = invCurve γ ∧ frontier V = invCurve γ ∧
      inv (rightRef γ) '' lowerLeft (γ 0).re ⊆ U ∧
      inv (rightRef γ) '' (lowerRight (γ 0).re \ {rightRef γ}) ⊆ V := by
  have hJ := isJordanCurve_invCurve hγ h0
  have hJc : IsClosed (invCurve γ) := (Foundations.Schoenflies.isCompact_of_isJordanCurve hJ).isClosed
  obtain ⟨x₁, hx₁, x₀, hx₀, hb, hub, hdisj, hun, hf₁, hf₀⟩ := jordan_curve_components hJ
  set U := connectedComponentIn (invCurve γ)ᶜ x₁ with hU
  set V := connectedComponentIn (invCurve γ)ᶜ x₀ with hV
  set p := rightRef γ with hp
  have hUo : IsOpen U := hJc.isOpen_compl.connectedComponentIn
  have hVo : IsOpen V := hJc.isOpen_compl.connectedComponentIn
  have hUJ : U ⊆ (invCurve γ)ᶜ := connectedComponentIn_subset _ _
  have hVJ : V ⊆ (invCurve γ)ᶜ := connectedComponentIn_subset _ _
  have hsplit : ∀ T : Set ℂ, IsPreconnected T → T ⊆ (invCurve γ)ᶜ → T ⊆ U ∨ T ⊆ V :=
    fun T hT hTJ => hT.subset_or_subset hUo hVo hdisj (hun ▸ hTJ)
  have himg : ∀ S : Set ℂ, S ⊆ (seedRayClosure γ)ᶜ → p ∉ S → inv p '' S ⊆ (invCurve γ)ᶜ := by
    rintro S hS hpS _ ⟨z, hz, rfl⟩
    exact inv_notMem_invCurve (hS hz) fun h => hpS (by rwa [hp, ← h])
  have hpc : ∀ S : Set ℂ, IsPreconnected S → p ∉ S → IsPreconnected (inv p '' S) := fun S hS hpS =>
    hS.image _ ((continuousOn_inv p).mono fun z hz h => hpS (mem_singleton_iff.1 h ▸ hz))
  -- the punctured lower-right quadrant goes to the unbounded component
  have hR : inv p '' (lowerRight (γ 0).re \ {p}) ⊆ V := by
    have hS : lowerRight (γ 0).re \ {p} ⊆ (seedRayClosure γ)ᶜ :=
      fun z hz => lowerRight_subset_compl hγ.2.2.1 hz.1
    rcases hsplit _ (hpc _ (isPreconnected_lowerRight_diff _ (ball_rightRef_subset h0))
      (fun h => h.2 rfl)) (himg _ hS (fun h => h.2 rfl)) with h | h
    · exfalso
      obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall 0).1 hb
      have hR0 : 0 ≤ R := by
        have := hR (mem_connectedComponentIn hx₁)
        exact dist_nonneg.trans this
      have hδ : (0 : ℝ) < 1 / (R + 1) := by positivity
      have hz : p + ((1 / (R + 1) : ℝ) : ℂ) ∈ lowerRight (γ 0).re \ {p} := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simp only [hp, rightRef, add_re, sub_re, one_re, I_re, sub_zero, ofReal_re]; linarith
        · simp [hp, rightRef, h0]
        · simp only [mem_singleton_iff, add_eq_left, ofReal_eq_zero]; exact hδ.ne'
      have hw := hR (h ⟨_, hz, rfl⟩)
      rw [mem_closedBall, dist_zero_right] at hw
      have : inv p (p + ((1 / (R + 1) : ℝ) : ℂ)) = ((R + 1 : ℝ) : ℂ) := by
        simp [inv]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hw
      linarith
    · exact h
  refine ⟨U, V, hUo, hVo, hb, isPreconnected_connectedComponentIn,
    isPreconnected_connectedComponentIn, hdisj, hun, hf₁, hf₀, ?_, hR⟩
  -- the lower-left quadrant goes to the bounded component (half discs at `γ 0 − i/2`)
  set r₀ : ℂ := γ 0 - I / 2 with hr₀
  have hr₀S : r₀ ∈ seedRayClosure γ := Or.inr ⟨by simp [hr₀], by simp [hr₀, h0]⟩
  have hr₀p : r₀ ≠ p := by
    intro h
    have := congrArg Complex.re h
    simp [hr₀, hp, rightRef] at this
  have hw₀ : inv p r₀ ≠ 0 := inv_apply_ne_zero hr₀p
  have hnhds : inv p '' ball r₀ (1 / 4) ∈ 𝓝 (inv p r₀) := by
    have h1 : uninv p ⁻¹' ball r₀ (1 / 4) ∈ 𝓝 (inv p r₀) :=
      (continuousAt_uninv hw₀).preimage_mem_nhds (isOpen_ball.mem_nhds (by simp))
    have h2 : ({0}ᶜ : Set ℂ) ∈ 𝓝 (inv p r₀) := isOpen_compl_singleton.mem_nhds hw₀
    refine mem_of_superset (inter_mem h1 h2) fun w hw => ⟨uninv p w, hw.1, inv_uninv p w⟩
  have hcl : inv p r₀ ∈ closure U := frontier_subset_closure (hf₁.symm ▸ inv_mem_invCurve hr₀S hp)
  obtain ⟨_, ⟨z, hzB, rfl⟩, hzU⟩ := mem_closure_iff_nhds.1 hcl _ hnhds
  have hzd : ‖z - r₀‖ < 1 / 4 := by rwa [mem_ball, dist_eq_norm] at hzB
  have hzim : z.im < 0 := by
    have := (abs_im_le_norm (z - r₀)).trans_lt hzd
    simp only [hr₀, sub_im, div_im, I_im, I_re, h0] at this
    norm_num at this
    linarith [abs_lt.1 this]
  have hzS : z ∉ seedRayClosure γ := fun h => hUJ hzU (inv_mem_invCurve h hp)
  have hzre : z.re ≠ (γ 0).re := fun h => hzS (Or.inr ⟨h, by rw [h0]; exact hzim.le⟩)
  rcases lt_or_gt_of_ne hzre with hlt | hgt
  · have hzL : z ∈ lowerLeft (γ 0).re := ⟨hlt, hzim⟩
    have hpL : p ∉ lowerLeft (γ 0).re := fun h => by
      have := h.1; simp [hp, rightRef] at this; linarith
    rcases hsplit _ (hpc _ (convex_lowerLeft _).isPreconnected hpL)
      (himg _ (lowerLeft_subset_compl hγ.2.2.1) hpL) with h | h
    · exact h
    · exact absurd (h ⟨z, hzL, rfl⟩) (Set.disjoint_left.1 hdisj hzU)
  · have hzp : z ≠ p := by
      intro h
      have := (abs_re_le_norm (z - r₀)).trans_lt hzd
      simp [h, hp, rightRef, hr₀] at this
      norm_num at this
    exact absurd (hR ⟨z, ⟨⟨hgt, hzim⟩, hzp⟩, rfl⟩) (Set.disjoint_left.1 hdisj hzU)

/-- The left reference point `γ(0) − 1 − i`. -/
theorem leftRef_mem_leftSide (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) :
    γ 0 - 1 - I ∈ leftSide γ :=
  mem_connectedComponentIn (lowerLeft_subset_compl hγ (left_ref_mem_lowerLeft h0))

theorem rightRef_mem_rightSide (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) :
    rightRef γ ∈ rightSide γ :=
  mem_connectedComponentIn (lowerRight_subset_compl hγ (right_ref_mem_lowerRight h0))

/-- A sample point of the punctured lower-right quadrant. -/
theorem farRight_mem (h0 : (γ 0).im = 0) :
    γ 0 + 2 - I ∈ lowerRight (γ 0).re \ {rightRef γ} := by
  refine ⟨⟨by simp, by simp [h0]⟩, fun h => ?_⟩
  have := congrArg Complex.re (mem_singleton_iff.1 h)
  simp [rightRef] at this

/-- **Sides of a proper curve, in inversion coordinates.** With `U`, `V` the bounded and unbounded components
of the inverted curve: `uninv '' U` is the left side, `uninv '' V` the right side minus nothing more, the inversion
centre is not on the left side, and the inversion maps the left side into `U` and the punctured right side
into `V`. -/
theorem exists_jordan_sides' (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsBounded U ∧ IsPreconnected U ∧ IsPreconnected V ∧
      Disjoint U V ∧ (invCurve γ)ᶜ = U ∪ V ∧ frontier U = invCurve γ ∧ frontier V = invCurve γ ∧
      inv (rightRef γ) '' leftSide γ ⊆ U ∧ inv (rightRef γ) '' (rightSide γ \ {rightRef γ}) ⊆ V ∧
      uninv (rightRef γ) '' U ⊆ leftSide γ ∧ uninv (rightRef γ) '' V ⊆ rightSide γ ∧
      rightRef γ ∉ leftSide γ := by
  obtain ⟨U, V, hUo, hVo, hb, hUc, hVc, hdisj, hun, hf₁, hf₀, hL, hR⟩ := exists_jordan_sides hγ h0
  set p := rightRef γ with hp
  have him := hγ.2.2.1
  have hUJ : U ⊆ (invCurve γ)ᶜ := hun ▸ subset_union_left
  have hVJ : V ⊆ (invCurve γ)ᶜ := hun ▸ subset_union_right
  have hsplit : ∀ T : Set ℂ, IsPreconnected T → T ⊆ (invCurve γ)ᶜ → T ⊆ U ∨ T ⊆ V :=
    fun T hT hTJ => hT.subset_or_subset hUo hVo hdisj (hun ▸ hTJ)
  have himg : ∀ S : Set ℂ, S ⊆ (seedRayClosure γ)ᶜ → p ∉ S → inv p '' S ⊆ (invCurve γ)ᶜ := by
    rintro S hS hpS _ ⟨z, hz, rfl⟩
    exact inv_notMem_invCurve (hS hz) fun h => hpS (by rwa [hp, ← h])
  have hpc : ∀ S : Set ℂ, IsPreconnected S → p ∉ S → IsPreconnected (inv p '' S) := fun S hS hpS =>
    hS.image _ ((continuousOn_inv p).mono fun z hz h => hpS (mem_singleton_iff.1 h ▸ hz))
  have hunimg : ∀ T : Set ℂ, T ⊆ (invCurve γ)ᶜ → uninv p '' T ⊆ (seedRayClosure γ)ᶜ := by
    rintro T hT _ ⟨w, hw, rfl⟩
    exact uninv_notMem (hT hw)
  have hunpc : ∀ T : Set ℂ, IsPreconnected T → T ⊆ (invCurve γ)ᶜ → IsPreconnected (uninv p '' T) :=
    fun T hT hTJ => hT.image _ ((continuousOn_uninv p).mono fun w hw =>
      ne_zero_of_notMem_invCurve (hTJ hw))
  have hlr : γ 0 - 1 - I ∈ lowerLeft (γ 0).re := left_ref_mem_lowerLeft h0
  have hlrU : inv p (γ 0 - 1 - I) ∈ U := hL ⟨_, hlr, rfl⟩
  have hfrV : inv p (γ 0 + 2 - I) ∈ V := hR ⟨_, farRight_mem h0, rfl⟩
  -- pulling back the two components
  have hUL : uninv p '' U ⊆ leftSide γ :=
    (hunpc U hUc hUJ).subset_connectedComponentIn ⟨_, hlrU, uninv_inv _ _⟩ (hunimg U hUJ)
  have hVR : uninv p '' V ⊆ rightSide γ := by
    have hsub := (hunpc V hVc hVJ).subset_connectedComponentIn ⟨_, hfrV, uninv_inv _ _⟩ (hunimg V hVJ)
    have hfr : γ 0 + 2 - I ∈ rightSide γ :=
      lowerRight_subset_rightSide him h0 (farRight_mem h0).1
    rw [rightSide, connectedComponentIn_eq hfr]
    exact hsub
  -- the centre is not on the left side
  have hpL : p ∉ leftSide γ := by
    intro hpL
    have hRL : rightSide γ = leftSide γ := (connectedComponentIn_eq hpL).symm
    have hball : ball p (1 / 2) ⊆ leftSide γ :=
      (ball_rightRef_subset h0).trans ((lowerRight_subset_rightSide him h0).trans hRL.le)
    have hc : IsPreconnected (leftSide γ \ {p}) :=
      isPreconnected_diff_singleton_of_ball_subset isPreconnected_connectedComponentIn
        (by norm_num) hball
    have hsub : leftSide γ \ {p} ⊆ (seedRayClosure γ)ᶜ :=
      fun z hz => connectedComponentIn_subset _ _ hz.1
    have hfr : γ 0 + 2 - I ∈ leftSide γ \ {p} :=
      ⟨hRL ▸ lowerRight_subset_rightSide him h0 (farRight_mem h0).1, (farRight_mem h0).2⟩
    have hlr' : γ 0 - 1 - I ∈ leftSide γ \ {p} :=
      ⟨leftRef_mem_leftSide him h0, fun h => by
        have := congrArg Complex.re (mem_singleton_iff.1 h); simp [hp, rightRef] at this; linarith⟩
    rcases hsplit _ (hpc _ hc fun h => h.2 rfl) (himg _ hsub fun h => h.2 rfl) with h | h
    · exact Set.disjoint_left.1 hdisj (h ⟨_, hfr, rfl⟩) hfrV
    · exact Set.disjoint_left.1 hdisj hlrU (h ⟨_, hlr', rfl⟩)
  have hLU : inv p '' leftSide γ ⊆ U := by
    rcases hsplit _ (hpc _ isPreconnected_connectedComponentIn hpL)
      (himg _ (connectedComponentIn_subset _ _) hpL) with h | h
    · exact h
    · exact absurd (h ⟨_, leftRef_mem_leftSide him h0, rfl⟩) (Set.disjoint_left.1 hdisj hlrU)
  have hRV : inv p '' (rightSide γ \ {p}) ⊆ V := by
    have hball : ball p (1 / 2) ⊆ rightSide γ :=
      (ball_rightRef_subset h0).trans (lowerRight_subset_rightSide him h0)
    have hc : IsPreconnected (rightSide γ \ {p}) :=
      isPreconnected_diff_singleton_of_ball_subset isPreconnected_connectedComponentIn
        (by norm_num) hball
    rcases hsplit _ (hpc _ hc fun h => h.2 rfl)
      (himg _ (fun z hz => connectedComponentIn_subset _ _ hz.1) fun h => h.2 rfl) with h | h
    · exact absurd hfrV (Set.disjoint_left.1 hdisj (h ⟨_, ⟨lowerRight_subset_rightSide him h0
        (farRight_mem h0).1, (farRight_mem h0).2⟩, rfl⟩))
    · exact h
  exact ⟨U, V, hUo, hVo, hb, hUc, hVc, hdisj, hun, hf₁, hf₀, hLU, hRV, hUL, hVR, hpL⟩

/-- **Jordan separation for a proper curve.** The two sides are disjoint. -/
theorem disjoint_leftSide_rightSide (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    Disjoint (leftSide γ) (rightSide γ) := by
  obtain ⟨U, V, -, -, -, -, -, hdisj, -, -, -, hLU, hRV, -, -, hpL⟩ := exists_jordan_sides' hγ h0
  refine Set.disjoint_left.2 fun z hzL hzR => ?_
  have hzp : z ≠ rightRef γ := fun h => hpL (h ▸ hzL)
  exact Set.disjoint_left.1 hdisj (hLU ⟨z, hzL, rfl⟩) (hRV ⟨z, ⟨hzR, hzp⟩, rfl⟩)

/-- The complement of a closed proper curve consists of its two sides. -/
theorem compl_seedRayClosure_eq (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    (seedRayClosure γ)ᶜ = leftSide γ ∪ rightSide γ := by
  obtain ⟨U, V, -, -, -, -, -, -, hun, -, -, -, -, hUL, hVR, -⟩ := exists_jordan_sides' hγ h0
  refine Subset.antisymm (fun z hz => ?_) (union_subset (connectedComponentIn_subset _ _)
    (connectedComponentIn_subset _ _))
  by_cases hzp : z = rightRef γ
  · exact Or.inr (hzp ▸ rightRef_mem_rightSide hγ.2.2.1 h0)
  have hw : inv (rightRef γ) z ∈ U ∪ V := hun ▸ inv_notMem_invCurve hz hzp
  rcases hw with hw | hw
  · exact Or.inl (by simpa using hUL ⟨_, hw, rfl⟩)
  · exact Or.inr (by simpa using hVR ⟨_, hw, rfl⟩)

/-- Every point of the closed curve is a limit of points of its right side. -/
theorem seedRayClosure_subset_closure_rightSide (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    seedRayClosure γ ⊆ closure (rightSide γ) := by
  obtain ⟨U, V, -, -, -, -, -, -, -, -, hf₀, -, -, -, hVR, -⟩ := exists_jordan_sides' hγ h0
  intro z hz
  have hzp : z ≠ rightRef γ := fun h => rightRef_notMem hγ.2.2.1 h0 (h ▸ hz)
  have hw : inv (rightRef γ) z ∈ closure V :=
    frontier_subset_closure (hf₀.symm ▸ inv_mem_invCurve hz rfl)
  have := mem_closure_image (f := uninv (rightRef γ)) (continuousAt_uninv (inv_apply_ne_zero hzp)) hw
  rw [uninv_inv] at this
  exact closure_mono hVR this

/-- Every point of the closed curve is a limit of points of its left side. -/
theorem seedRayClosure_subset_closure_leftSide (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    seedRayClosure γ ⊆ closure (leftSide γ) := by
  obtain ⟨U, V, -, -, -, -, -, -, -, hf₁, -, -, -, hUL, -, -⟩ := exists_jordan_sides' hγ h0
  intro z hz
  have hzp : z ≠ rightRef γ := fun h => rightRef_notMem hγ.2.2.1 h0 (h ▸ hz)
  have hw : inv (rightRef γ) z ∈ closure U :=
    frontier_subset_closure (hf₁.symm ▸ inv_mem_invCurve hz rfl)
  have := mem_closure_image (f := uninv (rightRef γ)) (continuousAt_uninv (inv_apply_ne_zero hzp)) hw
  rw [uninv_inv] at this
  exact closure_mono hUL this

/-! ### Closed images and the seed line -/

/-- The image of a closed set under a continuous map with compact norm-sublevel sets is closed. -/
theorem isClosed_image_of_isCompact_norm_le {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) (hK : ∀ R : ℝ, IsCompact {x | ‖f x‖ ≤ R}) {S : Set X} (hS : IsClosed S) :
    IsClosed (f '' S) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  set K := S ∩ {x | ‖f x‖ ≤ ‖z‖ + 1} with hKdef
  have hKc : IsCompact K := (hK _).inter_left hS
  have hcl : z ∈ closure (f '' K) := by
    rw [Metric.mem_closure_iff] at hz ⊢
    intro ε hε
    obtain ⟨_, ⟨x, hx, rfl⟩, hd⟩ := hz (min ε 1) (lt_min hε one_pos)
    refine ⟨f x, ⟨x, ⟨hx, ?_⟩, rfl⟩, hd.trans_le (min_le_left _ _)⟩
    have h1 : ‖f x‖ - ‖z‖ ≤ ‖f x - z‖ := norm_sub_norm_le _ _
    have h2 : ‖f x - z‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]; exact hd.trans_le (min_le_right _ _)
    show ‖f x‖ ≤ ‖z‖ + 1
    linarith
  exact image_mono inter_subset_left ((hKc.image hf).isClosed.closure_subset hcl)

theorem isCompact_norm_le (hγ : IsProperCurve γ) (R : ℝ) : IsCompact {t | ‖γ t‖ ≤ R} := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hγ.2.2.2.eventually_gt_atTop R)
  refine (isCompact_Icc (a := 0) (b := T)).of_isClosed_subset
    (isClosed_le (continuous_norm.comp hγ.1) continuous_const) fun t ht => ⟨zero_le, ?_⟩
  by_contra h
  exact absurd ht (not_le.2 (hT t (le_of_lt (not_le.1 h))))

theorem isClosed_image (hγ : IsProperCurve γ) {S : Set ℝ≥0} (hS : IsClosed S) : IsClosed (γ '' S) :=
  isClosed_image_of_isCompact_norm_le hγ.1 (isCompact_norm_le hγ) hS

/-- `inv p '' S ∪ {0}` is closed for closed `S`. -/
theorem isClosed_inv_image_union {p : ℂ} {S : Set ℂ} (hS : IsClosed S) : IsClosed (inv p '' S ∪ {0}) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro w hw
  have hw0 : w ≠ 0 := fun h => hw (Or.inr (mem_singleton_iff.2 h))
  have hwS : uninv p w ∉ S := fun h => hw (Or.inl ⟨_, h, inv_uninv p w⟩)
  have h1 : uninv p ⁻¹' Sᶜ ∈ 𝓝 w := (continuousAt_uninv hw0).preimage_mem_nhds
    (hS.isOpen_compl.mem_nhds hwS)
  have h2 : ({0}ᶜ : Set ℂ) ∈ 𝓝 w := isOpen_compl_singleton.mem_nhds hw0
  refine mem_of_superset (inter_mem h1 h2) ?_
  rintro w' ⟨h1', h2'⟩ (⟨z, hz, rfl⟩ | h)
  · exact h1' (by simpa using hz)
  · exact h2' h

/-- The closed curve `seedRayClosure γ` parametrized by `ℝ`: the lower ray for `t < 0`, the curve for `t ≥ 0`. -/
def seedLine (γ : ℝ≥0 → ℂ) (t : ℝ) : ℂ := if 0 ≤ t then γ t.toNNReal else γ 0 + (t : ℂ) * I

theorem seedLine_coe (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : seedLine γ t = γ t := by
  simp [seedLine]

theorem seedLine_of_neg (γ : ℝ≥0 → ℂ) {t : ℝ} (ht : t < 0) : seedLine γ t = γ 0 + (t : ℂ) * I := by
  simp [seedLine, not_le.2 ht]

theorem continuous_seedLine (hγ : Continuous γ) : Continuous (seedLine γ) := by
  refine Continuous.if_le (hγ.comp continuous_real_toNNReal) (by fun_prop) continuous_const
    continuous_id fun t ht => ?_
  subst ht
  simp

theorem seedLine_mem (h0 : (γ 0).im = 0) (t : ℝ) : seedLine γ t ∈ seedRayClosure γ := by
  by_cases ht : 0 ≤ t
  · simp only [seedLine, ht, ↓reduceIte]; exact Or.inl (mem_range_self _)
  · rw [seedLine_of_neg γ (not_le.1 ht)]
    exact Or.inr ⟨by simp, by simp [h0]; linarith [not_le.1 ht]⟩

theorem seedLine_surj (h0 : (γ 0).im = 0) {z : ℂ} (hz : z ∈ seedRayClosure γ) : ∃ t, seedLine γ t = z := by
  rcases hz with ⟨t, rfl⟩ | ⟨hre, him⟩
  · exact ⟨t, seedLine_coe γ t⟩
  · rw [h0] at him
    rcases him.lt_or_eq with hlt | heq
    · refine ⟨z.im, ?_⟩
      rw [seedLine_of_neg γ hlt]
      apply Complex.ext <;> simp [hre, h0]
    · refine ⟨0, ?_⟩
      rw [show (0 : ℝ) = ((0 : ℝ≥0) : ℝ) by simp, seedLine_coe]
      apply Complex.ext <;> simp [hre, h0, heq]

theorem seedLine_im_neg (h0 : (γ 0).im = 0) {t : ℝ} (ht : t < 0) : (seedLine γ t).im < 0 := by
  rw [seedLine_of_neg γ ht]; simp [h0, ht]

theorem seedLine_injective (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) : Function.Injective (seedLine γ) := by
  intro s t h
  by_cases hs : 0 ≤ s <;> by_cases ht : 0 ≤ t
  · have h' := h
    simp only [seedLine, hs, ht, ↓reduceIte] at h'
    have := hγ.2.1 h'
    rw [← Real.coe_toNNReal s hs, ← Real.coe_toNNReal t ht, this]
  · exfalso
    have h1 := seedLine_im_neg h0 (not_le.1 ht)
    rw [← h] at h1
    simp only [seedLine, hs, ↓reduceIte] at h1
    linarith [hγ.2.2.1 s.toNNReal]
  · exfalso
    have h1 := seedLine_im_neg h0 (not_le.1 hs)
    rw [h] at h1
    simp only [seedLine, ht, ↓reduceIte] at h1
    linarith [hγ.2.2.1 t.toNNReal]
  · rw [seedLine_of_neg γ (not_le.1 hs), seedLine_of_neg γ (not_le.1 ht)] at h
    have := congrArg Complex.im h
    simpa [h0] using this

theorem isCompact_seedLine_norm_le (hγ : IsProperCurve γ) (R : ℝ) :
    IsCompact {t : ℝ | ‖seedLine γ t‖ ≤ R} := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hγ.2.2.2.eventually_gt_atTop R)
  refine (isCompact_Icc (a := -(|R| + ‖γ 0‖ + 1)) (b := max (T : ℝ) 0)).of_isClosed_subset
    (isClosed_le (continuous_norm.comp (continuous_seedLine hγ.1)) continuous_const) fun t ht => ?_
  have ht' : ‖seedLine γ t‖ ≤ R := ht
  constructor
  · by_contra h
    have htn : t < 0 := by
      have : 0 ≤ |R| + ‖γ 0‖ := by positivity
      linarith [not_le.1 h]
    rw [seedLine_of_neg γ htn] at ht'
    have h1 : ‖(t : ℂ) * I‖ = |t| := by simp
    have h2 := norm_sub_norm_le ((t : ℂ) * I) (-(γ 0))
    rw [sub_neg_eq_add, add_comm, h1, norm_neg] at h2
    have h3 : |t| = -t := abs_of_neg htn
    linarith [le_abs_self R, not_le.1 h]
  · by_contra h
    have ht0 : 0 ≤ t := (le_max_right _ _).trans (le_of_lt (not_le.1 h))
    have hTt : T ≤ t.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal t ht0]
      exact (le_max_left _ _).trans (le_of_lt (not_le.1 h))
    have := hT _ hTt
    rw [← seedLine_coe γ t.toNNReal, Real.coe_toNNReal t ht0] at this
    linarith

theorem isClosed_seedLine_image (hγ : IsProperCurve γ) {S : Set ℝ} (hS : IsClosed S) :
    IsClosed (seedLine γ '' S) :=
  isClosed_image_of_isCompact_norm_le (continuous_seedLine hγ.1) (isCompact_seedLine_norm_le hγ) hS

/-! ### The side principle -/

/-- The Schoenflies straightening of a proper curve in inversion coordinates: a homeomorphism `h` of `ℂ`
carrying the unit circle onto the inverted closed curve and the unit disc onto the image of the left side. -/
theorem exists_straightening (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    ∃ h : ℂ ≃ₜ ℂ, h '' sphere 0 1 = invCurve γ ∧ h '' ball 0 1 ⊆ (invCurve γ)ᶜ ∧
      inv (rightRef γ) '' leftSide γ ⊆ h '' ball 0 1 := by
  obtain ⟨U, V, hUo, hVo, hb, hUc, -, hdisj, hun, -, -, hLU, -, -, -, -⟩ :=
    exists_jordan_sides' hγ h0
  have hJ := isJordanCurve_invCurve hγ h0
  set q := inv (rightRef γ) (γ 0 - 1 - I) with hq
  have hqU : q ∈ U := hLU ⟨_, leftRef_mem_leftSide hγ.2.2.1 h0, rfl⟩
  have hUJ : U ⊆ (invCurve γ)ᶜ := hun ▸ subset_union_left
  have hcomp : connectedComponentIn (invCurve γ)ᶜ q = U := by
    apply Subset.antisymm
    · rcases (isPreconnected_connectedComponentIn (F := (invCurve γ)ᶜ) (x := q)).subset_or_subset
        hUo hVo hdisj (by rw [← hun]; exact connectedComponentIn_subset _ _) with h | h
      · exact h
      · exact absurd (h (mem_connectedComponentIn (hUJ hqU))) (Set.disjoint_left.1 hdisj hqU)
    · exact hUc.subset_connectedComponentIn hqU hUJ
  obtain ⟨h, hs, hbl, -, -⟩ := schoenflies_plane hJ (hUJ hqU) (hcomp ▸ hb)
  rw [hcomp] at hbl
  exact ⟨h, hs, hbl ▸ hUJ, hbl ▸ hLU⟩

/-- **The side principle.** If two proper curves from the same real seed agree on `[0, A]`, then near every
point `γ₁(t₀)` with `t₀ < A`, the left side of the first curve is contained in the left side of the second. The
left side near a point of the common arc does not depend on how the curves continue after `A`. -/
theorem eventually_mem_leftSide_of_eqOn {γ₁ γ₂ : ℝ≥0 → ℂ} {A t₀ : ℝ≥0}
    (h₁ : IsProperCurve γ₁) (h₂ : IsProperCurve γ₂) (h0 : (γ₁ 0).im = 0)
    (hagree : ∀ t ≤ A, γ₂ t = γ₁ t) (ht₀ : t₀ < A) :
    ∀ᶠ w in 𝓝 (γ₁ t₀), w ∈ leftSide γ₁ → w ∈ leftSide γ₂ := by
  obtain ⟨h, hs, hbJ, hLb⟩ := exists_straightening h₁ h0
  set p := rightRef γ₁ with hp
  set ℓ := seedLine γ₁ with hℓ
  set Ψ : ℂ → ℂ := fun z => h.symm (inv p z) with hΨ
  have hpS : p ∉ seedRayClosure γ₁ := rightRef_notMem h₁.2.2.1 h0
  have hℓp : ∀ t, ℓ t ≠ p := fun t h' => hpS (h' ▸ seedLine_mem h0 t)
  have hΨs : ∀ z ∈ seedRayClosure γ₁, Ψ z ∈ sphere (0 : ℂ) 1 := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ : inv p z ∈ h '' sphere 0 1 := hs ▸ inv_mem_invCurve hz hp
    simpa [hΨ, ← hyz] using hy
  have hΨc : ∀ z, z ≠ p → ContinuousAt Ψ z := fun z hz =>
    h.symm.continuous.continuousAt.comp (continuousAt_inv hz)
  have hΨinj : ∀ z w, Ψ z = Ψ w → z = w := fun z w hzw =>
    inv_injective p (h.symm.injective hzw)
  have hrec : ∀ z, uninv p (h (Ψ z)) = z := fun z => by simp [hΨ]
  have hΨℓ : Continuous fun t => Ψ (ℓ t) := continuous_iff_continuousAt.2 fun t =>
    (hΨc _ (hℓp t)).comp (continuous_seedLine h₁.1).continuousAt
  have hagree0 : γ₂ 0 = γ₁ 0 := hagree 0 zero_le
  -- the common arc in straightened coordinates
  set thi : ℝ := ((t₀ : ℝ) + A) / 2 with hthi
  have htA : (t₀ : ℝ) < A := ht₀
  have ht₀thi : (t₀ : ℝ) < thi := by linarith
  have hthiA : thi < A := by linarith
  set C := (fun t => Ψ (ℓ t)) '' Icc (-1) thi with hC
  have hCcpt : IsCompact C := isCompact_Icc.image hΨℓ
  have hCconn : IsPreconnected C := isPreconnected_Icc.image _ hΨℓ.continuousOn
  -- the rest of the first closed curve
  set Fb := h.symm '' (inv p '' (ℓ '' (Iic (-1) ∪ Ici thi)) ∪ {0}) with hFb
  have hFbc : IsClosed Fb := by
    rw [hFb, h.image_symm]
    exact (isClosed_inv_image_union (isClosed_seedLine_image h₁ (isClosed_Iic.union isClosed_Ici))).preimage
      h.continuous
  have hsph : sphere (0 : ℂ) 1 ⊆ C ∪ Fb := by
    intro y hy
    have hhy : h y ∈ invCurve γ₁ := hs ▸ mem_image_of_mem h hy
    rcases hhy with ⟨z, hz, hzy⟩ | hz0
    · obtain ⟨t, rfl⟩ := seedLine_surj h0 hz
      have hy' : y = Ψ (ℓ t) := by
        show y = h.symm (inv p (ℓ t))
        rw [show inv p (ℓ t) = h y from hzy, Homeomorph.symm_apply_apply]
      by_cases ht : t ∈ Icc (-1) thi
      · exact Or.inl ⟨t, ht, hy'.symm⟩
      · refine Or.inr ⟨inv p (ℓ t), Or.inl ⟨ℓ t, ⟨t, ?_, rfl⟩, rfl⟩, hy'.symm⟩
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with ht | ht
        · exact Or.inl ht.le
        · exact Or.inr ht.le
    · exact Or.inr ⟨0, Or.inr rfl, by rw [← mem_singleton_iff.1 hz0, Homeomorph.symm_apply_apply]⟩
  have hnotFb : ∀ t ∈ Ioo (-1 : ℝ) thi, Ψ (ℓ t) ∉ Fb := by
    rintro t ht ⟨w, hw | hw, hwt⟩
    · obtain ⟨_, ⟨t', ht', rfl⟩, rfl⟩ := hw
      have := seedLine_injective h₁ h0 (hΨinj _ _ hwt)
      rw [this] at ht'
      rcases ht' with h' | h'
      · exact absurd (mem_Iic.1 h') (not_le.2 ht.1)
      · exact absurd (mem_Ici.1 h') (not_le.2 ht.2)
    · rw [mem_singleton_iff.1 hw] at hwt
      exact inv_apply_ne_zero (hℓp t) (h.symm.injective (hwt.symm.trans (by simp)))
  -- the tail of the second curve stays away from the common arc
  set G := γ₂ '' Ici A with hG
  set Fa := h.symm '' (inv p '' G ∪ {0}) with hFa
  have hFac : IsClosed Fa := by
    rw [hFa, h.image_symm]
    exact (isClosed_inv_image_union (isClosed_image h₂ isClosed_Ici)).preimage h.continuous
  have hCFa : C ⊆ Faᶜ := by
    rintro _ ⟨t, ht, rfl⟩ ⟨w, hw | hw, hwt⟩
    · obtain ⟨_, ⟨s, hs', rfl⟩, rfl⟩ := hw
      have heq : ℓ t = γ₂ s := (hΨinj _ _ hwt).symm
      by_cases ht0 : 0 ≤ t
      · have hle : t.toNNReal ≤ A := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal t ht0]; linarith [ht.2]
        have h1 : ℓ t = γ₂ t.toNNReal := by
          rw [hagree _ hle]
          show seedLine γ₁ t = γ₁ t.toNNReal
          simp [seedLine, ht0]
        have hts : t.toNNReal = s := h₂.2.1 (h1.symm.trans heq)
        have hsA : (A : ℝ) ≤ s := by exact_mod_cast (hs' : A ≤ s)
        rw [← hts, Real.coe_toNNReal t ht0] at hsA
        linarith [ht.2]
      · have : (ℓ t).im < 0 := seedLine_im_neg h0 (not_le.1 ht0)
        rw [heq] at this
        exact absurd (h₂.2.2.1 s) (not_le.2 this)
    · rw [mem_singleton_iff.1 hw] at hwt
      exact inv_apply_ne_zero (hℓp t) (h.symm.injective (hwt.symm.trans (by simp)))
  have hCs : C ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨t, -, rfl⟩; exact hΨs _ (seedLine_mem h0 t)
  -- a thin annular sector inside the disc along the common arc
  obtain ⟨δ, hδ, hthick⟩ := hCcpt.exists_thickening_subset_open hFac.isOpen_compl hCFa
  set η : ℝ := min (δ / 2) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  set Aη := (fun q : ℝ × ℂ => (q.1 : ℂ) * q.2) '' (Ioo (1 - η) 1 ×ˢ C) with hAη
  have hAconn : IsPreconnected Aη :=
    (isPreconnected_Ioo.prod hCconn).image _
      (by fun_prop : Continuous fun q : ℝ × ℂ => (q.1 : ℂ) * q.2).continuousOn
  have hAball : Aη ⊆ ball 0 1 := by
    rintro _ ⟨⟨r, c⟩, ⟨hr, hc⟩, rfl⟩
    have hc1 : ‖c‖ = 1 := by simpa using hCs hc
    rw [mem_ball, dist_zero_right, norm_mul, hc1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hr.1])]
    exact hr.2
  have hAthick : Aη ⊆ thickening δ C := by
    rintro _ ⟨⟨r, c⟩, ⟨hr, hc⟩, rfl⟩
    rw [mem_thickening_iff]
    refine ⟨c, hc, ?_⟩
    have hc1 : ‖c‖ = 1 := by simpa using hCs hc
    have hr1 : r - 1 < 0 := by linarith [hr.2]
    rw [dist_eq_norm, show (r : ℂ) * c - c = ((r - 1 : ℝ) : ℂ) * c by push_cast; ring, norm_mul, hc1,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hr1]
    linarith [hr.1]
  set Sη := uninv p '' (h '' Aη) with hSη
  have hhA : h '' Aη ⊆ (invCurve γ₁)ᶜ := (image_mono hAball).trans hbJ
  have hSconn : IsPreconnected Sη :=
    (hAconn.image _ h.continuous.continuousOn).image _ ((continuousOn_uninv p).mono fun w hw =>
      ne_zero_of_notMem_invCurve (hhA hw))
  have hSS : Sη ⊆ (seedRayClosure γ₂)ᶜ := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ hz
    have hwJ := hhA ⟨x, hx, rfl⟩
    have hback : inv p (uninv p (h x)) = h x := inv_uninv p (h x)
    have hS₁ : uninv p (h x) ∈ seedRayClosure γ₁ → False := fun hz1 =>
      hwJ (hback ▸ inv_mem_invCurve hz1 hp)
    rcases hz with ⟨s', hs'⟩ | ⟨hre, him⟩
    · by_cases hsA : s' ≤ A
      · exact hS₁ (Or.inl ⟨s', by rw [← hagree s' hsA]; exact hs'⟩)
      · have hxF : x ∈ Fa :=
          ⟨h x, Or.inl ⟨uninv p (h x), ⟨s', le_of_lt (not_le.1 hsA), hs'⟩, hback⟩,
            h.symm_apply_apply x⟩
        exact hthick (hAthick hx) hxF
    · exact hS₁ (Or.inr ⟨by rw [← hagree0]; exact hre, by rw [← hagree0]; exact him⟩)
  -- near every interior point of the common arc, the left side of `γ₁` lies in the sector
  have hK7 : ∀ t ∈ Ioo (-1 : ℝ) thi, ∀ᶠ w in 𝓝 (ℓ t), w ∈ leftSide γ₁ → w ∈ Sη := by
    intro t ht
    have hy₀ : Ψ (ℓ t) ∈ sphere (0 : ℂ) 1 := hΨs _ (seedLine_mem h0 t)
    have hn1 : ‖Ψ (ℓ t)‖ = 1 := by simpa using hy₀
    have hy0 : Ψ (ℓ t) ≠ 0 := by intro h'; rw [h', norm_zero] at hn1; norm_num at hn1
    have hc := hΨc _ (hℓp t)
    set N : ℂ → ℂ := fun y => y / (‖y‖ : ℂ) with hN
    have hNc : ContinuousAt N (Ψ (ℓ t)) :=
      continuousAt_id.div (continuous_ofReal.comp continuous_norm).continuousAt
        (by simpa using hy0)
    have hNy : N (Ψ (ℓ t)) = Ψ (ℓ t) := by simp [hN, hn1]
    have hO : Fbᶜ ∈ 𝓝 (N (Ψ (ℓ t))) := by
      rw [hNy]; exact hFbc.isOpen_compl.mem_nhds (hnotFb t ht)
    have e1 : ∀ᶠ w in 𝓝 (ℓ t), N (Ψ w) ∈ Fbᶜ := (hNc.comp hc).preimage_mem_nhds hO
    have e2 : ∀ᶠ w in 𝓝 (ℓ t), 1 - η < ‖Ψ w‖ :=
      (continuous_norm.continuousAt.comp hc).eventually
        (lt_mem_nhds (show 1 - η < ‖Ψ (ℓ t)‖ by rw [hn1]; linarith))
    filter_upwards [e1, e2] with w hw1 hw2 hwL
    have hΨw : Ψ w ∈ ball (0 : ℂ) 1 := by
      obtain ⟨y, hy, hyw⟩ := hLb ⟨w, hwL, rfl⟩
      have : Ψ w = y := by
        show h.symm (inv p w) = y
        rw [← hyw, Homeomorph.symm_apply_apply]
      rwa [this]
    have hnw : ‖Ψ w‖ < 1 := by simpa using hΨw
    have hw0 : Ψ w ≠ 0 := by intro h'; rw [h', norm_zero] at hw2; linarith
    have hnw0 : (‖Ψ w‖ : ℂ) ≠ 0 := by simpa using hw0
    have hu : N (Ψ w) ∈ sphere (0 : ℂ) 1 := by
      simp only [hN, mem_sphere_iff_norm, sub_zero, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_norm]
      exact div_self (norm_ne_zero_iff.2 hw0)
    have huC : N (Ψ w) ∈ C := by
      rcases hsph hu with h' | h'
      · exact h'
      · exact absurd h' hw1
    have hdecomp : ((‖Ψ w‖ : ℝ) : ℂ) * N (Ψ w) = Ψ w := by
      simp only [hN]; field_simp
    exact ⟨h (Ψ w), ⟨Ψ w, ⟨(‖Ψ w‖, N (Ψ w)), ⟨⟨hw2, hnw⟩, huC⟩, hdecomp⟩, rfl⟩, hrec w⟩
  -- a point near the lower ray on the left of both curves
  have hthi0 : (0 : ℝ) < thi := lt_of_le_of_lt (NNReal.coe_nonneg t₀) ht₀thi
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hK7 (-1 / 2) ⟨by norm_num, by linarith⟩)
  set m : ℝ := min (ε / 2) (1 / 2) with hm
  have hm0 : 0 < m := lt_min (by positivity) (by norm_num)
  set w₀ := ℓ (-1 / 2) - (m : ℂ) with hw₀
  have hℓh : ℓ (-1 / 2) = γ₁ 0 + ((-1 / 2 : ℝ) : ℂ) * I := seedLine_of_neg γ₁ (by norm_num)
  have hw₀ll : w₀ ∈ lowerLeft (γ₁ 0).re := by
    rw [hw₀, hℓh]
    constructor
    · simp; linarith
    · simp only [sub_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, h0]; norm_num
  have hw₀d : dist w₀ (ℓ (-1 / 2)) < ε := by
    rw [hw₀, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm0]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hw₀S : w₀ ∈ Sη := hball hw₀d (lowerLeft_subset_leftSide h₁.2.2.1 h0 hw₀ll)
  have hw₀L₂ : w₀ ∈ leftSide γ₂ := by
    have h0' : (γ₂ 0).im = 0 := by rw [hagree0]; exact h0
    exact lowerLeft_subset_leftSide h₂.2.2.1 h0' (by rw [hagree0]; exact hw₀ll)
  have hSL : Sη ⊆ leftSide γ₂ := by
    have := hSconn.subset_connectedComponentIn hw₀S hSS
    rwa [← connectedComponentIn_eq hw₀L₂] at this
  have hfin := hK7 t₀ ⟨by linarith [NNReal.coe_nonneg t₀], ht₀thi⟩
  rw [show ℓ (t₀ : ℝ) = γ₁ t₀ from seedLine_coe γ₁ t₀] at hfin
  filter_upwards [hfin] with w hw hwL using hSL (hw hwL)

end Supp9B

end InteractingSLE
