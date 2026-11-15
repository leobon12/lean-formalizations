/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartPrefix
import InteractingSLE.WangWu.ReverseContactMartGlue
import InteractingSLE.Spec.Exist.StagedLaw2Flow
import InteractingSLE.Spec.Sec7.PocketTraversalCoords

/-!
# The image word of the contact step, part 6: the image word is measurable

Packet PROVE-WW-B17, step B1 of PROVE-WW-B15's plan ("measurable image driver"). On the glued space, with a measurable
set `E` of good samples (`IsGlueGood`):

* `measurable_gCurve`: the positions of the image curve `Ψ ∘ α` are measurable (`Ψ = R ∘ f_s ∘ R` through
  PROVE-STAGEDLAW's `measurable_fwdMap_param`, `α` through `measurable_seedLine`);
* `mem_preContact_iff_rat`: a rational time is before the first contact with `G = R(β((0, s]))` iff the forward line
  up to it keeps a positive distance from `G`, read at rational times of both lines (deterministic);
  `measurableSet_mem_gPre`: hence the rational pre-contact events are measurable;
* `measurable_indicator_capClock_gCurve`: the capacity clock at a rational time is measurable on its pre-contact event
  (PROVE-RESTART-CPL5's `measurable_hcapHit_image`);
* **`measurable_imgW`**, **`measurableSet_lt_imgT`**, **`measurable_imgVL`**, **`measurable_imgVR`**: the killed image
  word is measurable at every time, and so are the events `{t < imgT}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C Sec7.Lemma71E Restart ImgWord LawUnique MartChar.RealFlow

/-! ### Rational approximation in intervals with rational ends -/

theorem exists_rat_mem_Icc_near {a b : ℚ} {x : ℝ} (hx : x ∈ Icc (a : ℝ) b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℚ, (r : ℝ) ∈ Icc (a : ℝ) b ∧ |(r : ℝ) - x| < δ := by
  rcases hx.2.eq_or_lt with h | h
  · exact ⟨b, ⟨hx.1.trans h.le, le_rfl⟩, by rw [← h, sub_self, abs_zero]; exact hδ⟩
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x < min (b : ℝ) (x + δ) from lt_min h (by linarith))
    refine ⟨r, ⟨hx.1.trans hr1.le, hr2.le.trans (min_le_left _ _)⟩, ?_⟩
    rw [abs_lt]
    have := min_le_right (b : ℝ) (x + δ)
    constructor <;> linarith

theorem exists_rat_mem_Ioc_near {a b : ℚ} {x : ℝ} (hx : x ∈ Ioc (a : ℝ) b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℚ, (r : ℝ) ∈ Ioc (a : ℝ) b ∧ |(r : ℝ) - x| < δ := by
  obtain ⟨r, hr, hrx⟩ := exists_rat_mem_Icc_near (a := a) (b := b) ⟨hx.1.le, hx.2⟩ hδ
  rcases hx.2.eq_or_lt with h | h
  · exact ⟨b, ⟨h ▸ hx.1, le_rfl⟩, by rw [← h, sub_self, abs_zero]; exact hδ⟩
  · obtain ⟨r', hr1, hr2⟩ := exists_rat_btwn (show x < min (b : ℝ) (x + δ) from lt_min h (by linarith))
    refine ⟨r', ⟨hx.1.trans hr1, hr2.le.trans (min_le_left _ _)⟩, ?_⟩
    rw [abs_lt]
    have := min_le_right (b : ℝ) (x + δ)
    constructor <;> linarith

/-! ### The pre-contact times through rational times -/

theorem measurable_negInv : Measurable negInv := by
  unfold negInv
  exact measurable_inv.neg

/-- **Pre-contact through rational times.** For simple proper arcs `α`, `β` and `G = R(β((0, s]))` closed, a rational
time `q ≥ 0` is before the first contact of `α` with `G` iff the rational positions of `α` up to `q` keep a uniform
positive distance from the rational positions of `R ∘ β` on `(0, s]`. -/
theorem mem_preContact_iff_rat {α β : ℝ → ℂ} (hα : IsProperArc α) (hβ : IsProperArc β) {s : ℚ}
    (hGc : IsClosed (negInv '' (β '' Ioc 0 s))) {q : ℚ} (hq : (0 : ℝ) ≤ q) (hs : (0 : ℝ) < s) :
    (q : ℝ) ∈ preContact α (negInv '' (β '' Ioc 0 s)) ↔
      ∃ m : ℕ, ∀ u v : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
        1 / ((m : ℝ) + 1) ≤ ‖α u - negInv (β v)‖ := by
  set G := negInv '' (β '' Ioc 0 s) with hGdef
  have hGne : G.Nonempty := ⟨_, β s, ⟨s, ⟨hs, le_rfl⟩, rfl⟩, rfl⟩
  have hmemG : ∀ v : ℝ, v ∈ Ioc (0 : ℝ) s → negInv (β v) ∈ G := fun v hv => ⟨β v, ⟨v, hv, rfl⟩, rfl⟩
  constructor
  · intro hpre
    have hcα : ContinuousOn α (Icc 0 q) := hα.cont.mono Icc_subset_Ici_self
    have hf : ContinuousOn (fun u => infDist (α u) G) (Icc 0 q) :=
      (continuous_infDist_pt G).comp_continuousOn hcα
    obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hq) hf
    have hpos : 0 < infDist (α u₀) G :=
      (hGc.notMem_iff_infDist_pos hGne).1 (hpre.2 u₀ hu₀)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    refine ⟨m, fun u v hu0 huq hv0 hvs => ?_⟩
    have h1 : infDist (α u₀) G ≤ infDist (α u) G := hmin ⟨hu0, huq⟩
    have h2 : infDist (α u) G ≤ dist (α u) (negInv (β v)) := infDist_le_dist_of_mem (hmemG v ⟨hv0, hvs⟩)
    rw [← dist_eq_norm]
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨hq, fun u hu hαu => ?_⟩
    obtain ⟨_, ⟨v, hv, rfl⟩, hve⟩ := hαu
    set ε : ℝ := 1 / (2 * ((m : ℝ) + 1)) with hε
    have hε0 : 0 < ε := by positivity
    have hcα : ContinuousWithinAt α (Icc 0 q) u := (hα.cont u hu.1).mono Icc_subset_Ici_self
    have hβv : β v ≠ 0 := ne_zero_of_mem_H (hβ.mem_H v hv.1)
    have hcβ : ContinuousWithinAt (fun v => negInv (β v)) (Ioc 0 s) v :=
      (continuousAt_negInv hβv).comp_continuousWithinAt ((hβ.cont v (le_of_lt hv.1)).mono
        fun _ hx => le_of_lt hx.1)
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousWithinAt_iff.1 hcα ε hε0
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.1 hcβ ε hε0
    obtain ⟨u', hu', hu'd⟩ := exists_rat_mem_Icc_near (a := 0) (b := q) (by simpa using hu) hδ₁
    obtain ⟨v', hv', hv'd⟩ := exists_rat_mem_Ioc_near (a := 0) (b := s) (by simpa using hv) hδ₂
    simp only [Rat.cast_zero] at hu' hv'
    have e1 := h₁ hu' (by rw [Real.dist_eq]; exact hu'd)
    have e2 := h₂ hv' (by rw [Real.dist_eq]; exact hv'd)
    have key := hm u' v' hu'.1 hu'.2 hv'.1 hv'.2
    rw [dist_eq_norm] at e1 e2
    have htri : ‖α u' - negInv (β v')‖ ≤ ‖α u' - α u‖ + ‖negInv (β v) - negInv (β v')‖ := by
      calc ‖α u' - negInv (β v')‖ = ‖(α u' - α u) + (negInv (β v) - negInv (β v'))‖ := by
            rw [← hve]; ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev (negInv (β v))] at htri
    have : ε + ε = 1 / ((m : ℝ) + 1) := by rw [hε]; field_simp; ring
    linarith

/-! ### The glued space -/

namespace ImgWord

/-- The frozen reverse driver, recentred at `0` (it is the frozen driver on good histories). -/
def revDrv0 (s : ℚ) (y : HistorySpace 1 1) (t : ℝ) : ℝ := Ito.rpath (frzDrive s y) t - Ito.rpath (frzDrive s y) 0

end ImgWord

section Glue

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℚ} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

theorem continuous_revDrv0 (y : HistorySpace 1 1) : Continuous (revDrv0 s y) :=
  (Sec4.continuous_rpath_regPath _).sub continuous_const

theorem measurable_revDrv0_apply (t : ℝ) : Measurable fun y : HistorySpace 1 1 => revDrv0 s y t :=
  ((measurable_pi_apply _).comp (measurable_frzDrive s)).sub ((measurable_pi_apply _).comp (measurable_frzDrive s))

theorem revDrv0_of_mem (hs : 0 < s) {y : HistorySpace 1 1} (hy : y ∈ BetaSet s) :
    revDrv0 s y = Ito.rpath (frzDrive s y) := by
  funext t
  have := (trace_of_mem_betaSet hs hy).2.1
  simp only [revDrv0, this, sub_zero]

omit mΩ in
open scoped Classical in
theorem gCurve_eq (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1) (q : ℝ) :
    gCurve s ζ W E p q = if p ∈ E then (if q ≤ 0 then 0 else
      negInv (fwdMap (revDrv0 s p.2) s (negInv (seedLine ζ W p.1 q)))) else vRay q := by
  classical
  by_cases hp : p ∈ E
  · rw [gCurve_of_mem hp, revDrv0_of_mem hs (hEg p hp).2.1]
    simp only [hp, ↓reduceIte]
    rfl
  · simp only [gCurve, hp, ↓reduceIte]

/-- **The positions of the image curve are measurable.** -/
theorem measurable_gCurve (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (q : ℝ) : Measurable fun p => gCurve s ζ W E p q := by
  classical
  simp_rw [gCurve_eq hs hEg _ q]
  refine Measurable.ite hE ?_ measurable_const
  by_cases hq : q ≤ 0
  · simp only [hq, ↓reduceIte]
    exact measurable_const
  · simp only [hq, ↓reduceIte]
    have hy : Measurable fun p : Ω × HistorySpace 1 1 => negInv (seedLine ζ W p.1 q) :=
      measurable_negInv.comp ((measurable_seedLine hW q).comp measurable_fst)
    have h := (Exist.StagedLaw.measurable_fwdMap_param (W := fun p : Ω × HistorySpace 1 1 => revDrv0 s p.2)
      (fun p => continuous_revDrv0 p.2) (fun t => (measurable_revDrv0_apply t).comp measurable_snd)
      (fun p => by simp [revDrv0]) (τ := fun _ => (s : ℝ)) measurable_const (fun _ => by exact_mod_cast hs.le)
      hy).1
    exact measurable_negInv.comp h

omit mΩ in
/-- On good samples, `G = R(β((0, s]))` for the frozen reverse trace `β`, a simple proper arc; `G` is closed. -/
theorem glueG_eq (hs : 0 < s) {p : Ω × HistorySpace 1 1} (hp : IsGlueGood s ζ W p) :
    negInv '' histHull s p.2 = negInv '' (frzLine s p.2 '' Ioc 0 s) ∧ IsProperArc (frzLine s p.2) ∧
      IsClosed (negInv '' histHull s p.2) := by
  obtain ⟨-, hβ, hg⟩ := hp
  obtain ⟨-, -, hL, hP, hhull, -, -⟩ := trace_of_mem_betaSet hs hβ
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  refine ⟨by rw [hhull, fwdHull_eq_image_Ioc hL hP hs'], hP, isClosed_image_negInv_histHull hs hg⟩

/-- **The rational pre-contact events are measurable.** -/
theorem measurableSet_mem_gPre (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (q : ℚ) : MeasurableSet {p | (q : ℝ) ∈ gPre s ζ W E p} := by
  classical
  by_cases hq : (0 : ℝ) ≤ q
  · set T : Set (Ω × HistorySpace 1 1) := ⋃ m : ℕ, ⋂ u : ℚ, ⋂ v : ℚ, {p | (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
        (0 : ℝ) < v → (v : ℝ) ≤ s → 1 / ((m : ℝ) + 1) ≤ ‖seedLine ζ W p.1 u - negInv (frzLine s p.2 v)‖}
      with hTdef
    have heq : {p | (q : ℝ) ∈ gPre s ζ W E p} = (E ∩ T) ∪ Eᶜ := by
      ext p
      by_cases hp : p ∈ E
      · obtain ⟨hG, hβ, hGc⟩ := glueG_eq hs (hEg p hp)
        have hs' : (0 : ℝ) < s := by exact_mod_cast hs
        simp only [mem_ofPred_eq, gPre_of_mem hp, mem_union, mem_inter_iff, hp, true_and, mem_compl_iff,
          not_true_eq_false, or_false, hTdef, mem_iUnion, mem_iInter]
        rw [hG]
        rw [hG] at hGc
        exact mem_preContact_iff_rat (hEg p hp).1 hβ hGc hq hs'
      · simp only [mem_ofPred_eq, gPre, hp, ↓reduceIte, mem_Ici, hq, mem_union, mem_inter_iff, false_and,
          mem_compl_iff, not_false_eq_true, or_true]
    rw [heq]
    refine (hE.inter (MeasurableSet.iUnion fun m => MeasurableSet.iInter fun u => MeasurableSet.iInter
      fun v => ?_)).union hE.compl
    by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q ∧ (0 : ℝ) < v ∧ (v : ℝ) ≤ s
    · obtain ⟨h1, h2, h3, h4⟩ := hc
      simp only [h1, h2, h3, h4, forall_const]
      exact measurableSet_le measurable_const
        ((((measurable_seedLine hW u).comp measurable_fst).sub
          (measurable_negInv.comp ((measurable_frzLine s v).comp measurable_snd))).norm)
    · have e : {p : Ω × HistorySpace 1 1 | (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
          1 / ((m : ℝ) + 1) ≤ ‖seedLine ζ W p.1 u - negInv (frzLine s p.2 v)‖} = univ := by
        ext p
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro h1 h2 h3 h4
        exact absurd ⟨h1, h2, h3, h4⟩ hc
      rw [e]
      exact MeasurableSet.univ
  · have heq : {p | (q : ℝ) ∈ gPre s ζ W E p} = ∅ := by
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hmem
      by_cases hp : p ∈ E
      · rw [gPre_of_mem hp] at hmem; exact hq hmem.1
      · simp only [gPre, hp, ↓reduceIte, mem_Ici] at hmem; exact hq hmem
    rw [heq]
    exact MeasurableSet.empty

/-- **The capacity clock at a rational time is measurable on its pre-contact event.** -/
theorem measurable_indicator_capClock_gCurve (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (q : ℚ) :
    Measurable ({p | (q : ℝ) ∈ gPre s ζ W E p}.indicator fun p => capClock (gCurve s ζ W E p) q) := by
  classical
  set A := {p | (q : ℝ) ∈ gPre s ζ W E p} with hAdef
  have hA : MeasurableSet A := measurableSet_mem_gPre hs hW hE hEg q
  have hK := isKilledArc_gCurve hs hEg (ζ := ζ) (W := W)
  set Γ : Ω × HistorySpace 1 1 → ℝ≥0 → ℂ := fun p t =>
    if p ∈ A then gCurve s ζ W E p (min (t : ℝ) q) else 0 with hΓdef
  have hΓc : ∀ p, Continuous (Γ p) := by
    intro p
    by_cases hp : p ∈ A
    · simp only [hΓdef, hp, ↓reduceIte]
      have hq0 : (0 : ℝ) ≤ q := (hK p).nonneg _ hp
      refine ((hK p).cont.mono ((hK p).icc _ hp)).comp_continuous
        ((NNReal.continuous_coe.min continuous_const)) fun t => ⟨le_min t.coe_nonneg hq0, min_le_right _ _⟩
    · simp only [hΓdef, hp, ↓reduceIte]
      exact continuous_const
  have hΓm : ∀ t, Measurable fun p => Γ p t := fun t =>
    Measurable.ite hA (measurable_gCurve hs hW hE hEg _) measurable_const
  have hmeas := measurable_hcapHit_image hΓc hΓm (q : ℝ).toNNReal
  have heq : A.indicator (fun p => capClock (gCurve s ζ W E p) q) =
      A.indicator fun p => (WholeField.hcapHit (Γ p '' Icc 0 (q : ℝ).toNNReal)).toReal / 2 := by
    refine indicator_congr fun p hp => ?_
    have hq0 : (0 : ℝ) ≤ q := (hK p).nonneg _ hp
    have himg : gCurve s ζ W E p '' Icc 0 q = Γ p '' Icc 0 (q : ℝ).toNNReal := by
      rw [image_Icc_real_eq hq0]
      refine image_congr fun t ht => ?_
      have htq : (t : ℝ) ≤ q := by
        have := ht.2
        rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0] at this
      simp only [hΓdef, hp, ↓reduceIte, min_eq_left htq]
    have h0 : (Γ p 0).im ≤ 0 := by
      simp only [hΓdef, hp, ↓reduceIte, NNReal.coe_zero, min_eq_left hq0, (hK p).zero, Complex.zero_im,
        le_refl]
    rw [hcapHit_image_eq (hΓc p).continuousOn h0, ← himg]
    have hnn : 0 ≤ ConformalImage.hcapSet (fillH (gCurve s ζ W E p '' Icc 0 q)) := by
      have := (hK p).capClock_nonneg hp
      rw [capClock] at this
      linarith
    rw [ENNReal.toReal_ofReal hnn, capClock]
  rw [heq]
  exact ((ENNReal.measurable_toReal.comp hmeas).div_const _).indicator hA

/-- **The events `{t < imgT}` are measurable.** -/
theorem measurableSet_lt_imgT (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (t : ℝ≥0) :
    MeasurableSet {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} :=
  measurableSet_lt_kLife (isKilledArc_gCurve hs hEg) (measurableSet_mem_gPre hs hW hE hEg)
    (measurable_indicator_capClock_gCurve hs hW hE hEg) t

/-- **The killed image driver is measurable at every time.** -/
theorem measurable_imgW (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (t : ℝ≥0) : Measurable (imgW s ζ W E t) := by
  classical
  have h := measurable_indicator_kW_of_base (isKilledArc_gCurve hs hEg) (measurableSet_mem_gPre hs hW hE hEg)
    (measurable_indicator_capClock_gCurve hs hW hE hEg) (fun q => measurable_gCurve hs hW hE hEg q) t
  convert h using 1
  funext p
  by_cases ht : (t : WithTop ℝ≥0) < kLife (gCurve s ζ W E p) (gPre s ζ W E p)
  · rw [indicator_of_mem (show p ∈ {p | (t : WithTop ℝ≥0) < kLife (gCurve s ζ W E p) (gPre s ζ W E p)} from ht)]
    rfl
  · rw [indicator_of_notMem (show p ∉ {p | (t : WithTop ℝ≥0) < kLife (gCurve s ζ W E p) (gPre s ζ W E p)} from ht)]
    simp only [imgW, kW, ht, ↓reduceIte]

theorem measurable_gXR (hE : MeasurableSet E) : Measurable fun p : Ω × HistorySpace 1 1 => gXR s E p := by
  classical
  refine measurable_pi_iff.2 fun j => ?_
  fin_cases j
  · simp only [gXR, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact measurable_const
  · simp only [gXR, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact Measurable.ite hE (measurable_const.div ((measurable_frzVL s).comp measurable_snd)) measurable_const

theorem measurable_gXL (hE : MeasurableSet E) : Measurable fun p : Ω × HistorySpace 1 1 => gXL s E p := by
  classical
  refine measurable_pi_iff.2 fun j => ?_
  fin_cases j
  · simp only [gXL, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact measurable_const
  · simp only [gXL, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact Measurable.ite hE (measurable_const.div ((measurable_frzVR s).comp measurable_snd)) measurable_const

/-- The killed image driver frozen after `t` (on `{t < imgT}`; `0` elsewhere). -/
private def frzImg (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) (t : ℝ≥0) :
    ℝ≥0 → Ω × HistorySpace 1 1 → ℝ :=
  open scoped Classical in
  fun u p => if (t : WithTop ℝ≥0) < imgT s ζ W E p then imgW s ζ W E (min u t) p else 0

private theorem frzImg_props (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (t : ℝ≥0) :
    (∀ u, Measurable (frzImg s ζ W E t u)) ∧ (∀ p, Continuous fun u => frzImg s ζ W E t u p) ∧
      ∀ p, (t : WithTop ℝ≥0) < imgT s ζ W E p →
        EqOn (kPath (gCurve s ζ W E p) (gPre s ζ W E p)) (Bessel.realPath (frzImg s ζ W E t) p) (Icc 0 t) := by
  classical
  refine ⟨fun u => Measurable.ite (measurableSet_lt_imgT hs hW hE hEg t) (measurable_imgW hs hW hE hEg _)
    measurable_const, fun p => ?_, fun p ht r hr => ?_⟩
  · by_cases ht : (t : WithTop ℝ≥0) < imgT s ζ W E p
    · simp only [frzImg, ht, ↓reduceIte]
      refine ((isKilledArc_gCurve hs hEg p).continuousOn_kW).comp_continuous (continuous_id.min continuous_const)
        fun u => lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right u t)) ht
    · simp only [frzImg, ht, ↓reduceIte]
      exact continuous_const
  · have hrt : r.toNNReal ≤ t := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    simp only [Bessel.realPath, frzImg, ht, ↓reduceIte, min_eq_left hrt]
    rfl

/-- **The images of the right marks are measurable at every time.** -/
theorem measurable_imgVR (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (j : Fin 2) (t : ℝ≥0) : Measurable (imgVR s ζ W E j t) := by
  classical
  obtain ⟨hm, hc, hEq⟩ := frzImg_props hs hW hE hEg t
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 1 1)) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun p => rightImg (Bessel.realPath (frzImg s ζ W E t) p) (gXR s E p j) t :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) hm hc
      ((measurable_pi_apply j).comp (measurable_gXR hE)) t
  have heq : imgVR s ζ W E j t = {p | (t : WithTop ℝ≥0) < imgT s ζ W E p}.indicator
      fun p => rightImg (Bessel.realPath (frzImg s ζ W E t) p) (gXR s E p j) t := by
    funext p
    by_cases ht : (t : WithTop ℝ≥0) < imgT s ζ W E p
    · rw [indicator_of_mem (show p ∈ {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} from ht)]
      simp only [imgVR]
      rw [kVR_of_lt _ _ ht, kVRr, kImg]
      exact Sec7.Lemma71B.rightImg_congr (Bessel.continuous_realPath hc p) t.coe_nonneg (hEq p ht) _
    · rw [indicator_of_notMem (show p ∉ {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} from ht)]
      have ht' : ¬ (t : WithTop ℝ≥0) < kLife (gCurve s ζ W E p) (gPre s ζ W E p) := ht
      simp only [imgVR, kVR, ht', ↓reduceIte]
  rw [heq]
  exact hR.indicator (measurableSet_lt_imgT hs hW hE hEg t)

/-- **The images of the left marks are measurable at every time.** -/
theorem measurable_imgVL (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (i : Fin 2) (t : ℝ≥0) : Measurable (imgVL s ζ W E i t) := by
  classical
  obtain ⟨hm, hc, hEq⟩ := frzImg_props hs hW hE hEg t
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 1 1)) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun p => rightImg (Bessel.realPath (fun u p => -frzImg s ζ W E t u p) p)
      (-gXL s E p i) t :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) (fun u => (hm u).neg)
      (fun p => (hc p).neg) ((measurable_pi_apply i).comp (measurable_gXL hE)).neg t
  have heq : imgVL s ζ W E i t = {p | (t : WithTop ℝ≥0) < imgT s ζ W E p}.indicator
      fun p => -rightImg (Bessel.realPath (fun u p => -frzImg s ζ W E t u p) p) (-gXL s E p i) t := by
    funext p
    by_cases ht : (t : WithTop ℝ≥0) < imgT s ζ W E p
    · rw [indicator_of_mem (show p ∈ {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} from ht)]
      simp only [imgVL]
      rw [kVL_of_lt _ _ ht, kVLr, kImg, neg_inj]
      refine Sec7.Lemma71B.rightImg_congr (Bessel.continuous_realPath (fun p => (hc p).neg) p) t.coe_nonneg
        (fun r hr => ?_) _
      show -kPath _ _ r = -frzImg s ζ W E t r.toNNReal p
      rw [hEq p ht hr]
      rfl
    · rw [indicator_of_notMem (show p ∉ {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} from ht)]
      have ht' : ¬ (t : WithTop ℝ≥0) < kLife (gCurve s ζ W E p) (gPre s ζ W E p) := ht
      simp only [imgVL, kVL, ht', ↓reduceIte]
  rw [heq]
  exact hR.neg.indicator (measurableSet_lt_imgT hs hW hE hEg t)

end Glue

end InteractingSLE.WangWu
