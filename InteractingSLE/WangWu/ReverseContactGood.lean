/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactUnion
import InteractingSLE.WangWu.Prop418RangeMain

/-!
# Good reverse histories: the unbounded-components condition of Proposition 3.8 for both slits

Packet PROVE-WW-B13 (item N1 of PROVE-WW-B12). Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling
R31), proof of Proposition 4.18 (text dump L1609–1612): "the union boundary lemma identifies its harmonic mean on every
exposed open arc." The union boundary lemma (Proposition 3.8, `ae_union_boundary_glue`) needs, for each comparison slit
`S`, that every component of `S ∪ {Im ≤ 0}` is unbounded.

* `GoodHist t`: a **Borel** set of histories, cut out by countably many conditions on the rational-time points of the
  trace read from the history (`histLine`): uniform continuity on the rational times of `[0, t]`, start at `0`, and
  positive imaginary part on rational windows away from `0`.
* On it, the stopped hull is the image `γ(0, t]` of a curve continuous on `[0, t]` with `γ(0) = 0`
  (`exists_curve_of_mem_goodHist`), so the hull together with `ℝ` is preconnected, and its reflection `R(γ(0, t])`,
  `R(z) = −1/z`, is preconnected and unbounded.
* A preconnected unbounded set `S` has only unbounded components in `S ∪ {Im ≤ 0}`
  (`not_isBounded_lowerUnion_of_isPreconnected`).
* The history of a two-seed marked chain lies in `GoodHist t` almost surely (`ae_mem_goodHist_twoSeed`), so on the
  glued space both conditions hold almost surely (`ae_unb_fwdSlit_glue`, `ae_unb_revSlit_glue`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets (lowerUnion)
open LawUnique

universe u

/-! ### Unbounded components -/

/-- **A preconnected unbounded set has only unbounded components in `S ∪ {Im ≤ 0}`**: a point of `S` lies in a
component containing `S`, a point of the closed lower half-plane in one containing that half-plane. -/
theorem not_isBounded_lowerUnion_of_isPreconnected {S : Set ℂ} (hS : IsPreconnected S)
    (hSu : ¬ Bornology.IsBounded S) :
    ∀ z ∈ lowerUnion S, ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion S) z) := by
  intro z hz hb
  rcases hz with hzS | hzL
  · exact hSu (hb.subset (hS.subset_connectedComponentIn hzS subset_union_left))
  · exact InteractingSLE.not_isBounded_lowerHalf (hb.subset
      (InteractingSLE.isPreconnected_lowerHalf.subset_connectedComponentIn hzL subset_union_right))

/-! ### Uniform continuity on rational times -/

/-- Uniform continuity of `γ` on the rational times of `[0, t]`, as a countable condition. -/
def UnifCondRat (γ : ℝ → ℂ) (t : ℚ) : Prop :=
  ∀ m : ℕ, ∃ n : ℕ, ∀ p q : ℚ, 0 ≤ p → p ≤ t → 0 ≤ q → q ≤ t → |(p : ℝ) - q| < 1 / ((n : ℝ) + 1) →
    ‖γ p - γ q‖ ≤ 1 / ((m : ℝ) + 1)

theorem uniformContinuousOn_of_unifCondRat {γ : ℝ → ℂ} {t : ℚ} (hu : UnifCondRat γ t) :
    UniformContinuousOn γ (ratWindow 0 t) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨n, hn⟩ := hu m
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  rintro _ ⟨p, rfl, hp0, hpt⟩ _ ⟨q, rfl, hq0, hqt⟩ hpq
  rw [Real.dist_eq] at hpq
  rw [dist_eq_norm]
  exact (hn p q hp0 hpt hq0 hqt hpq).trans_lt hm

/-- The rational-time points near a point of `[0, t]` form a Cauchy filter: limits exist. -/
theorem exists_tendsto_of_unifCondRat {γ : ℝ → ℂ} {t : ℚ} (hu : UnifCondRat γ t) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) t) : ∃ y, Tendsto γ (𝓝[ratWindow 0 t] x) (𝓝 y) := by
  have : NeBot (𝓝[ratWindow 0 t] x) :=
    mem_closure_iff_nhdsWithin_neBot.1 (Icc_subset_closure_ratWindow hx)
  refine cauchy_map_iff_exists_tendsto.1 ?_
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 (uniformContinuousOn_of_unifCondRat hu) ε hε
  have hδ2 : 0 < δ / 2 := by positivity
  refine ⟨γ '' (ratWindow 0 t ∩ ball x (δ / 2)),
    image_mem_map (inter_mem_nhdsWithin _ (ball_mem_nhds x hδ2)), ?_⟩
  rintro _ ⟨a, ⟨haW, ha⟩, rfl⟩ _ ⟨b, ⟨hbW, hb⟩, rfl⟩
  refine hδε a haW b hbW ?_
  calc dist a b ≤ dist a x + dist b x := dist_triangle_right a b x
    _ < δ / 2 + δ / 2 := add_lt_add ha hb
    _ = δ := by ring

/-- **The continuous curve of a uniformly continuous rational-time sample**: the extension of `γ` from the rational
times of `[0, t]` is continuous on `[0, t]` and agrees with `γ` at the rational times. -/
theorem continuousOn_extendFrom_ratWindow {γ : ℝ → ℂ} {t : ℚ} (hu : UnifCondRat γ t) :
    ContinuousOn (extendFrom (ratWindow 0 t) γ) (Icc 0 t) ∧
      EqOn (extendFrom (ratWindow 0 t) γ) γ (ratWindow 0 t) :=
  ⟨continuousOn_extendFrom Icc_subset_closure_ratWindow fun _ hx => exists_tendsto_of_unifCondRat hu hx,
    extendFrom_extends (uniformContinuousOn_of_unifCondRat hu).continuousOn⟩

/-! ### Good histories -/

section Good

variable {nL nR : ℕ}

/-- **Good histories at time `t`**: the trace read from the history is uniformly continuous on the rational times of
`[0, t]`, starts at `0`, and has imaginary part bounded below on every rational window `[a, b]`, `0 < a`. -/
def GoodHist (t : ℚ) : Set (HistorySpace nL nR) :=
  {y | UnifCondRat (histLine y) t ∧ histLine y 0 = 0 ∧ ImPosCond (histLine y)}

/-- **Good histories form a Borel set.** -/
theorem measurableSet_goodHist (t : ℚ) : MeasurableSet (GoodHist (nL := nL) (nR := nR) t) := by
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · refine measurableSet_setOfPred.2 (Measurable.forall fun m => Measurable.exists fun n => ?_)
    refine Measurable.forall fun p => Measurable.forall fun q => ?_
    refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.imp measurable_const ?_))))
    exact measurableSet_setOfPred.1
      (measurableSet_le ((measurable_histLine _).sub (measurable_histLine _)).norm measurable_const)
  · exact measurableSet_eq_fun (measurable_histLine 0) measurable_const
  · refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b => ?_)
    refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.exists fun m => ?_))
    refine Measurable.forall fun p => Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
    exact measurableSet_setOfPred.1
      (measurableSet_le measurable_const (Complex.measurable_im.comp (measurable_histLine _)))

theorem not_mem_H_zero : (0 : ℂ) ∉ H := by
  simp [QuantumZipper.H]

/-- **On a good history the stopped hull is a curve's image**: `histHull t y = γ(0, t]` for a curve `γ` continuous on
`[0, t]`, with `γ(0) = 0` and `γ(0, t] ⊆ ℍ`. -/
theorem exists_curve_of_mem_goodHist {t : ℚ} (ht : 0 < t) {y : HistorySpace nL nR} (hy : y ∈ GoodHist t) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 t) ∧ γ 0 = 0 ∧ (∀ u ∈ Ioc (0 : ℝ) t, γ u ∈ H) ∧
      histHull t y = γ '' Ioc 0 t := by
  obtain ⟨hu, h0, him⟩ := hy
  set γ := extendFrom (ratWindow 0 t) (histLine y) with hγdef
  obtain ⟨hc, heq⟩ := continuousOn_extendFrom_ratWindow hu
  have h0W : (0 : ℝ) ∈ ratWindow 0 t := ⟨0, by simp, le_rfl, ht.le⟩
  have hγ0 : γ 0 = 0 := (heq h0W).trans h0
  have hH : ∀ u ∈ Ioc (0 : ℝ) t, γ u ∈ H := by
    intro u hu'
    obtain ⟨a, ha0, hau⟩ := exists_rat_btwn hu'.1
    have ha0' : (0 : ℚ) < a := by exact_mod_cast ha0
    have hat : a < t := by exact_mod_cast hau.trans_le hu'.2
    obtain ⟨m, hm⟩ := him a t ha0' hat
    have hx : u ∈ Icc (0 : ℝ) t := ⟨hu'.1.le, hu'.2⟩
    obtain ⟨z, hz⟩ := exists_tendsto_of_unifCondRat hu hx
    have : NeBot (𝓝[ratWindow 0 t] u) :=
      mem_closure_iff_nhdsWithin_neBot.1 (Icc_subset_closure_ratWindow hx)
    have hlim : Tendsto (histLine y) (𝓝[ratWindow 0 t] u) (𝓝 (γ u)) := tendsto_extendFrom ⟨z, hz⟩
    have hev : ∀ᶠ v in 𝓝[ratWindow 0 t] u, 1 / ((m : ℝ) + 1) ≤ (histLine y v).im := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hau)] with v hv hva
      obtain ⟨p, rfl, hp0, hpt⟩ := hv
      exact hm p (by exact_mod_cast (le_of_lt (show (a : ℝ) < p from hva))) hpt
    have hle := ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hlim) hev
    show 0 < (γ u).im
    exact lt_of_lt_of_le (by positivity) hle
  refine ⟨γ, hc, hγ0, hH, ?_⟩
  have himg : histLine y '' ratWindow 0 t = γ '' ratWindow 0 t := (image_congr heq).symm
  rw [histHull, himg, closure_image_ratWindow hc]
  ext z
  constructor
  · rintro ⟨hzH, u, hu', rfl⟩
    refine ⟨u, ⟨lt_of_le_of_ne hu'.1 ?_, hu'.2⟩, rfl⟩
    rintro rfl
    have hz0 : γ 0 ∈ H := hzH
    rw [hγ0] at hz0
    exact not_mem_H_zero hz0
  · rintro ⟨u, hu', rfl⟩
    exact ⟨hH u hu', u, ⟨hu'.1.le, hu'.2⟩, rfl⟩

theorem isPreconnected_realLine : IsPreconnected {w : ℂ | w.im = 0} :=
  (convex_hyperplane (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected

/-- **The forward condition**: on a good history, the stopped hull together with `ℝ` is preconnected. -/
theorem isPreconnected_histHull_union_real {t : ℚ} (ht : 0 < t) {y : HistorySpace nL nR}
    (hy : y ∈ GoodHist t) : IsPreconnected (histHull t y ∪ {w : ℂ | w.im = 0}) := by
  obtain ⟨γ, hc, h0, -, he⟩ := exists_curve_of_mem_goodHist ht hy
  have e : histHull t y ∪ {w : ℂ | w.im = 0} = γ '' Icc 0 t ∪ {w : ℂ | w.im = 0} := by
    rw [he]
    ext z
    constructor
    · rintro (⟨u, hu, rfl⟩ | hz)
      · exact Or.inl ⟨u, ⟨hu.1.le, hu.2⟩, rfl⟩
      · exact Or.inr hz
    · rintro (⟨u, hu, rfl⟩ | hz)
      · rcases eq_or_lt_of_le hu.1 with h | h
        · subst h
          right
          simp [h0]
        · exact Or.inl ⟨u, ⟨h, hu.2⟩, rfl⟩
      · exact Or.inr hz
  rw [e]
  exact (isPreconnected_Icc.image γ hc).union 0 ⟨0, ⟨le_rfl, by exact_mod_cast ht.le⟩, h0⟩ (by simp)
    isPreconnected_realLine

/-- **The reverse conditions**: on a good history, the reflected stopped hull `R(γ(0, t])` is preconnected and
unbounded. -/
theorem isPreconnected_image_negInv_histHull {t : ℚ} (ht : 0 < t) {y : HistorySpace nL nR}
    (hy : y ∈ GoodHist t) : IsPreconnected (negInv '' histHull t y) := by
  obtain ⟨γ, hc, -, hH, he⟩ := exists_curve_of_mem_goodHist ht hy
  rw [he, image_image]
  refine isPreconnected_Ioc.image _ fun u hu => ?_
  have hne : γ u ≠ 0 := fun h => not_mem_H_zero (h ▸ hH u hu)
  exact (continuousAt_negInv hne).comp_continuousWithinAt ((hc u ⟨hu.1.le, hu.2⟩).mono Ioc_subset_Icc_self)

theorem not_isBounded_image_negInv_histHull {t : ℚ} (ht : 0 < t) {y : HistorySpace nL nR}
    (hy : y ∈ GoodHist t) : ¬ Bornology.IsBounded (negInv '' histHull t y) := by
  obtain ⟨γ, hc, h0, hH, he⟩ := exists_curve_of_mem_goodHist ht hy
  rw [he, image_image]
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hIoc : Ioc (0 : ℝ) t ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT ht'
  have hlim : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 := (hc 0 ⟨le_rfl, ht'.le⟩).tendsto
      rw [h0] at h1
      exact h1.mono_left (nhdsWithin_le_of_mem (mem_of_superset hIoc Ioc_subset_Icc_self))
    · filter_upwards [hIoc] with u hu
      exact fun h => not_mem_H_zero (h ▸ hH u hu)
  have hev := (tendsto_norm_inv_nhdsNE_zero_atTop.comp hlim).eventually_gt_atTop R
  obtain ⟨u, hu1, hu2⟩ := (hev.and hIoc).exists
  have hmem := hR ⟨u, hu2, rfl⟩
  rw [mem_closedBall, dist_zero_right] at hmem
  have : ‖negInv (γ u)‖ = ‖(γ u)⁻¹‖ := by rw [negInv, norm_neg]
  simp only [Function.comp_apply] at hu1 hmem
  rw [this] at hmem
  linarith

/-- On a good history the closure of the stopped hull adds at most the start `0`. -/
theorem closure_histHull_subset {t : ℚ} (ht : 0 < t) {y : HistorySpace nL nR} (hy : y ∈ GoodHist t) :
    closure (histHull t y) ⊆ insert 0 (histHull t y) := by
  obtain ⟨γ, hc, h0, -, he⟩ := exists_curve_of_mem_goodHist ht hy
  have hK : IsClosed (γ '' Icc 0 t) := (isCompact_Icc.image_of_continuousOn hc).isClosed
  rw [he]
  refine (closure_minimal (image_mono Ioc_subset_Icc_self) hK).trans ?_
  rintro _ ⟨u, hu, rfl⟩
  rcases eq_or_lt_of_le hu.1 with h | h
  · subst h
    exact Or.inl h0
  · exact Or.inr ⟨u, ⟨h, hu.2⟩, rfl⟩

/-- **On a good history the reflected stopped hull is closed in `ℂ`**: its points near `0` in the curve's time go to
`∞`. -/
theorem isClosed_image_negInv_histHull {t : ℚ} (ht : 0 < t) {y : HistorySpace nL nR} (hy : y ∈ GoodHist t) :
    IsClosed (negInv '' histHull t y) := by
  obtain ⟨γ, hc, h0, hH, he⟩ := exists_curve_of_mem_goodHist ht hy
  set K := γ '' Icc 0 t with hKdef
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hc
  have hS : ∀ w ∈ negInv '' histHull t y, w ≠ 0 ∧ negInv w ∈ K := by
    rintro _ ⟨z, hz, rfl⟩
    rw [he] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hne : γ u ≠ 0 := fun h => not_mem_H_zero (h ▸ hH u hu)
    refine ⟨fun h => hne ?_, ?_⟩
    · have := congrArg negInv h
      rwa [negInv_negInv, show negInv 0 = 0 by simp [negInv]] at this
    · rw [negInv_negInv]
      exact ⟨u, ⟨hu.1.le, hu.2⟩, rfl⟩
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall 0
    have hMpos : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨1 / max M 1, by positivity, fun w hw hwS => ?_⟩
    obtain ⟨hw0, hwK⟩ := hS w hwS
    have h1 := hM hwK
    rw [mem_closedBall, dist_zero_right, negInv, norm_neg, norm_inv] at h1
    rw [mem_ball, dist_zero_right] at hw
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have h2 : ‖w‖⁻¹ ≤ max M 1 := h1.trans (le_max_left _ _)
    have h3 : 1 / max M 1 ≤ ‖w‖ := by
      rw [div_le_iff₀ hMpos]
      calc 1 = ‖w‖ * ‖w‖⁻¹ := (mul_inv_cancel₀ hwpos.ne').symm
        _ ≤ ‖w‖ * max M 1 := mul_le_mul_of_nonneg_left h2 hwpos.le
    linarith
  · have hRz : negInv z ∉ K := by
      intro hK
      refine hz ?_
      by_cases hRz0 : negInv z = 0
      · exact absurd (by simpa [negInv] using hRz0) hz0
      · obtain ⟨u, hu, hu'⟩ := hK
        refine ⟨negInv z, ?_, negInv_negInv z⟩
        rw [he]
        refine ⟨u, ⟨lt_of_le_of_ne hu.1 ?_, hu.2⟩, hu'⟩
        rintro rfl
        exact hRz0 (hu'.symm.trans h0)
    have hV : (Kᶜ) ∈ 𝓝 (negInv z) := hKc.isClosed.isOpen_compl.mem_nhds hRz
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 ((continuousAt_negInv hz0).preimage_mem_nhds hV)
    exact ⟨ε, hε, fun w hw hwS => hεV hw (hS w hwS).2⟩

/-- **The history of a simple proper trace is good** (Heine–Cantor on `[0, t]` and the window conditions). -/
theorem mem_goodHist_of_isProperArc {y : HistorySpace nL nR} (hγ : IsProperArc (histLine y)) (t : ℚ) :
    y ∈ GoodHist t := by
  refine ⟨fun m => ?_, hγ.zero, hγ.imPosCond⟩
  have hK : UniformContinuousOn (histLine y) (Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hγ.cont.mono fun _ hs => hs.1)
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 hK (1 / ((m : ℝ) + 1)) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n, fun p q hp0 hpt hq0 hqt hpq => ?_⟩
  have := hδε p ⟨by exact_mod_cast hp0, by exact_mod_cast hpt⟩ q ⟨by exact_mod_cast hq0, by exact_mod_cast hqt⟩
    (by rw [Real.dist_eq]; exact hpq.trans hn)
  rw [dist_eq_norm] at this
  exact this.le

end Good

/-! ### Almost surely on the glued space -/

section Glue

variable {rL rR : ℝ}
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- **The history of a two-seed marked chain is good almost surely.** -/
theorem ae_mem_goodHist_twoSeed (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hE : IsMarkedChain LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) (t : ℚ) :
    ∀ᵐ ω ∂P, killedHistory W VL VR ζ ω ∈ GoodHist t := by
  filter_upwards [ae_good_twoSeed hL hR hE] with ω ⟨hp, he⟩
  exact mem_goodHist_of_isProperArc (by rw [he]; exact hp) t

/-- **Proposition 3.8's condition for the forward slit on the glued space.** -/
theorem ae_unb_fwdSlit_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {β : Type} [MeasurableSpace β] (k : Kernel (DistOn upperHalfPlaneOpens) β) [IsMarkovKernel k] {t : ℚ}
    (ht : 0 < t) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1), ∀ z ∈ lowerUnion (histHull t (killedHistory W VL VR ζ p.1)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (histHull t (killedHistory W VL VR ζ p.1))) z) :=
  ae_glue_fst k hC.2.1 (by
    filter_upwards [ae_mem_goodHist_twoSeed hL hR hC.1 t] with ω hω
    exact LocalSets.not_isBounded_of_isPreconnected_union_real (isPreconnected_histHull_union_real ht hω))

/-- **Proposition 3.8's condition for the reflected reverse slit on the glued space.** -/
theorem ae_unb_revSlit_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) {s : ℚ} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1), ∀ z ∈ lowerUnion (negInv '' histHull s p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (negInv '' histHull s p.2)) z) := by
  have hgood := ae_glue_snd (X₂ := fun ω => reflectField (h₂ ω)) (D₂ := killedHistory W₂ VL₂ VR₂ ζ₂) hC.2.1
    (measurable_reflectField.comp hC₂.2.1) (measurable_killedHistory hC₂.2.2.2.1) hlaw k hk
    (measurableSet_goodHist s) (ae_mem_goodHist_twoSeed hR hL hC₂.1 s)
  filter_upwards [hgood] with p hp
  exact not_isBounded_lowerUnion_of_isPreconnected (isPreconnected_image_negInv_histHull hs hp)
    (not_isBounded_image_negInv_histHull hs hp)

/-- The forward history is good on the glued space. -/
theorem ae_goodHist_fst_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {β : Type} [MeasurableSpace β] (k : Kernel (DistOn upperHalfPlaneOpens) β) [IsMarkovKernel k] (t : ℚ) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1), killedHistory W VL VR ζ p.1 ∈ GoodHist t :=
  ae_glue_fst (μ := P) k hC.2.1 (Q := fun ω => killedHistory W VL VR ζ ω ∈ GoodHist t)
    (ae_mem_goodHist_twoSeed hL hR hC.1 t)

/-- The reverse history is good on the glued space. -/
theorem ae_goodHist_snd_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) (s : ℚ) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1), p.2 ∈ GoodHist s :=
  ae_glue_snd (X₂ := fun ω => reflectField (h₂ ω)) (D₂ := killedHistory W₂ VL₂ VR₂ ζ₂) hC.2.1
    (measurable_reflectField.comp hC₂.2.1) (measurable_killedHistory hC₂.2.2.2.1) hlaw k hk
    (measurableSet_goodHist s) (ae_mem_goodHist_twoSeed hR hL hC₂.1 s)

end Glue

end InteractingSLE.WangWu
