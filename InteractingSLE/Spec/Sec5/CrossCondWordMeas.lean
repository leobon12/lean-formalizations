/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondWord
import InteractingSLE.WangWu.ReverseContactMartBase

/-!
# The image word of the flow line given the counterflow prefix is measurable

Packet PROVE-GLUECOND5, G4 for Proposition 4.9's direction at general `κ` (the general-`κ` form of WangWu's
`ReverseContactMartBase`, PROVE-WW-B17). On the glued space, with a measurable set `E` of good samples
(`Word49.IsGood49`):

* `measurable_gCurve`: the positions of the image curve `Ψ ∘ η` are measurable (`Ψ = R ∘ f′_s ∘ R` through
  `measurable_fwdMap_param`, `η` through `measurable_seedLine`);
* `mem_preContact_iff_ball` (deterministic): for a continuous arc `α` and a **closed** obstacle `G` (here the filled,
  non-simple counterflow hull `R(K′_s)`; no simplicity of the obstacle is used), a rational time `q ≥ 0` is before the
  first contact iff for some `m` every ball of radius `1/(m+1)` around a rational position of `α` up to `q` misses `G`;
* `measurableSet_disjoint_ball`: a ball with a random centre misses a hitting-measurable random subset of `ℍ` on a
  measurable event (rational centres and radii);
* `measurableSet_mem_gPre`: hence the rational pre-contact events are measurable;
* `measurable_indicator_capClock_gCurve`, **`measurableSet_lt_imgT`**, **`measurable_imgW`**,
  **`measurable_imgVL`**, **`measurable_imgVR`**: the killed image word is measurable at every time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond MartChar.RealFlow Cond44Ref CfRegQ Prop411Q
open Sec7.Lemma71C Sec7.Lemma71E Restart

namespace Word49

/-! ### Pre-contact with a closed obstacle through rational times -/

section PreContact

/-- **Pre-contact with a closed obstacle through rational times.** For an arc `α` continuous on `[0, ∞)` and a closed
`G`, a rational time `q ≥ 0` is before the first contact of `α` with `G` iff for some `m` the balls of radius
`1/(m+1)` around the rational positions of `α` on `[0, q]` all miss `G`. -/
theorem mem_preContact_iff_ball {α : ℝ → ℂ} (hα : ContinuousOn α (Ici 0)) {G : Set ℂ} (hG : IsClosed G) {q : ℚ}
    (hq : (0 : ℝ) ≤ q) :
    (q : ℝ) ∈ preContact α G ↔
      ∃ m : ℕ, ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q → Disjoint (ball (α u) (1 / ((m : ℝ) + 1))) G := by
  have hcα : ContinuousOn α (Icc 0 q) := hα.mono Icc_subset_Ici_self
  constructor
  · intro hpre
    have hK : IsCompact (α '' Icc 0 q) := isCompact_Icc.image_of_continuousOn hcα
    have hdis : Disjoint (α '' Icc 0 q) G := by
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨u, hu, rfl⟩ hG'
      exact hpre.2 u hu hG'
    obtain ⟨δ, hδ, hδd⟩ := hdis.exists_thickenings hK hG
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun u hu0 huq => Set.disjoint_left.2 fun z hz hzG => ?_⟩
    have h1 : z ∈ thickening δ (α '' Icc 0 q) :=
      mem_thickening_iff.2 ⟨α u, ⟨u, ⟨hu0, huq⟩, rfl⟩, (mem_ball.1 hz).trans hm⟩
    have h2 : z ∈ thickening δ G := self_subset_thickening hδ G hzG
    exact Set.disjoint_left.1 hδd h1 h2
  · rintro ⟨m, hm⟩
    refine ⟨hq, fun u hu huG => ?_⟩
    have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hαδ⟩ := Metric.continuousWithinAt_iff.1 (hcα u hu) _ hr
    obtain ⟨u', hu', hu'd⟩ := exists_rat_mem_Icc_near (a := 0) (b := q) (by simpa using hu) hδ
    simp only [Rat.cast_zero] at hu'
    have hd := hαδ hu' (by rw [Real.dist_eq]; exact hu'd)
    exact Set.disjoint_left.1 (hm u' hu'.1 hu'.2) (mem_ball.2 (by rw [dist_comm]; exact hd)) huG

end PreContact

/-! ### Balls with random centres -/

section Ball

variable {β : Type*} [MeasurableSpace β]

/-- A ball meets a set iff some ball with a Gaussian-rational centre and a rational radius, inside it, does. -/
theorem disjoint_ball_iff_rat {z : ℂ} {r : ℝ} {G : Set ℂ} :
    Disjoint (ball z r) G ↔ ∀ c : ℚ × ℚ, ∀ ρ : ℚ, (0 : ℝ) < ρ →
      ‖((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I - z‖ + ρ < r →
        Disjoint (ball (((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I) ρ) G := by
  constructor
  · intro h c ρ _ hc
    refine h.mono_left fun w hw => ?_
    rw [mem_ball] at hw ⊢
    calc dist w z ≤ dist w (((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I) +
          dist (((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I) z := dist_triangle _ _ _
      _ < ρ + ‖((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I - z‖ := by
          rw [dist_eq_norm (((c.1 : ℝ) : ℂ) + _)]; linarith
      _ < r := by linarith
  · intro h
    refine Set.disjoint_left.2 fun w hw hwG => ?_
    have hε : 0 < r - dist w z := sub_pos.2 (mem_ball.1 hw)
    obtain ⟨ρ, hρ0, hρ⟩ := exists_rat_btwn (show (0 : ℝ) < (r - dist w z) / 4 by linarith)
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show w.re - ρ / 2 < w.re by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show w.im - ρ / 2 < w.im by linarith)
    set c : ℂ := ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I with hc
    have hcw : ‖c - w‖ < ρ := by
      have h1 : |(c - w).re| < ρ / 2 := by
        simp only [hc, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero]
        rw [abs_lt]; constructor <;> linarith
      have h2 : |(c - w).im| < ρ / 2 := by
        simp only [hc, sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one, zero_add]
        rw [abs_lt]; constructor <;> linarith
      calc ‖c - w‖ ≤ |(c - w).re| + |(c - w).im| := norm_le_abs_re_add_abs_im _
        _ < ρ / 2 + ρ / 2 := by linarith
        _ = ρ := by ring
    have hcz : ‖c - z‖ + ρ < r := by
      have : ‖c - z‖ ≤ ‖c - w‖ + dist w z := by
        rw [dist_eq_norm]
        calc ‖c - z‖ = ‖(c - w) + (w - z)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    exact Set.disjoint_left.1 (h (a, b) ρ (by exact_mod_cast hρ0) hcz)
      (mem_ball.2 (by rw [dist_comm, dist_eq_norm]; exact hcw)) hwG

/-- **A ball with a random centre misses a hitting-measurable random subset of `ℍ`** on a measurable event. -/
theorem measurableSet_disjoint_ball {z : β → ℂ} (hz : Measurable z) {G : β → Set ℂ}
    (hG : Measurable[_, hittingSigma] G) (hGH : ∀ b, G b ⊆ H) (r : ℝ) :
    MeasurableSet {b | Disjoint (ball (z b) r) (G b)} := by
  have e : {b | Disjoint (ball (z b) r) (G b)} = ⋂ c : ℚ × ℚ, ⋂ ρ : ℚ,
      ({b | (0 : ℝ) < ρ ∧ ‖((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I - z b‖ + ρ < r}ᶜ ∪
        {b | Disjoint (ball (((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I) ρ) (G b)}) := by
    ext b
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, not_and_or, not_lt]
    rw [disjoint_ball_iff_rat]
    refine forall_congr' fun c => forall_congr' fun ρ => ?_
    constructor
    · intro h
      by_cases h1 : (0 : ℝ) < ρ
      · by_cases h2 : ‖((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I - z b‖ + ρ < r
        · exact Or.inr (h h1 h2)
        · exact Or.inl (Or.inr (not_lt.1 h2))
      · exact Or.inl (Or.inl (not_lt.1 h1))
    · rintro (h | h) h1 h2
      · rcases h with h | h <;> linarith
      · exact h
  rw [e]
  refine MeasurableSet.iInter fun c => MeasurableSet.iInter fun ρ => MeasurableSet.union ?_ ?_
  · exact ((MeasurableSet.const _).inter (measurableSet_lt
      (((measurable_const.sub hz).norm).add measurable_const) measurable_const)).compl
  · set U : Set ℂ := ball (((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I) ρ ∩ H with hU
    have hUo : IsOpen U := isOpen_ball.inter QuantumZipper.isOpen_H
    have hS : MeasurableSet[hittingSigma] {S : Set ℂ | (S ∩ U).Nonempty} :=
      MeasurableSpace.measurableSet_generateFrom ⟨U, hUo, inter_subset_right, rfl⟩
    have e2 : {b | Disjoint (ball (((c.1 : ℝ) : ℂ) + ((c.2 : ℝ) : ℂ) * I) ρ) (G b)} =
        G ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty}ᶜ := by
      ext b
      simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, not_nonempty_iff_eq_empty, hU]
      constructor
      · intro hd
        refine eq_empty_of_forall_notMem fun w ⟨hwG, hwB, _⟩ => Set.disjoint_left.1 hd hwB hwG
      · intro he
        refine Set.disjoint_left.2 fun w hwB hwG => ?_
        have : w ∈ G b ∩ (ball _ ρ ∩ H) := ⟨hwG, hwB, hGH b hwG⟩
        rw [he] at this
        exact this
    rw [e2]
    exact hG hS.compl

end Ball

/-! ### The image word on the glued space is measurable -/

section Glue

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {nL nR : ℕ}

omit mΩ in
open scoped Classical in
theorem gCurve_eq (p : Ω × HistorySpace 0 0) (q : ℝ) :
    gCurve s ζ W E p q = if p ∈ E then (if q ≤ 0 then 0 else
      negInv (fwdMap (cfDrv0 s p.2) s (negInv (seedLine ζ W p.1 q)))) else vRay q := by
  by_cases hp : p ∈ E
  · rw [gCurve_of_mem hp]
    simp only [hp, ↓reduceIte]
    rfl
  · simp only [gCurve, hp, ↓reduceIte]

/-- **The positions of the image curve are measurable.** -/
theorem measurable_gCurve (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E) (q : ℝ) :
    Measurable fun p => gCurve s ζ W E p q := by
  classical
  simp_rw [gCurve_eq _ q]
  refine Measurable.ite hE ?_ measurable_const
  by_cases hq : q ≤ 0
  · simp only [hq, ↓reduceIte]
    exact measurable_const
  · simp only [hq, ↓reduceIte]
    have hy : Measurable fun p : Ω × HistorySpace 0 0 => negInv (seedLine ζ W p.1 q) :=
      measurable_negInv.comp ((measurable_seedLine hW q).comp measurable_fst)
    have h := (Exist.StagedLaw.measurable_fwdMap_param (W := fun p : Ω × HistorySpace 0 0 => cfDrv0 s p.2)
      (fun p => continuous_cfDrv0 s p.2) (fun t => (measurable_cfDrv0_apply' s t).comp measurable_snd)
      (fun p => cfDrv0_zero s p.2) (τ := fun _ => (s : ℝ)) measurable_const (fun _ => s.coe_nonneg) hy).1
    exact measurable_negInv.comp h

/-- **The rational pre-contact events are measurable.** -/
theorem measurableSet_mem_gPre (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (q : ℚ) : MeasurableSet {p | (q : ℝ) ∈ gPre s ζ W E p} := by
  classical
  by_cases hq : (0 : ℝ) ≤ q
  · set T : Set (Ω × HistorySpace 0 0) := ⋃ m : ℕ, ⋂ u : ℚ,
        ({_p | (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q}ᶜ ∪
          {p | Disjoint (ball (seedLine ζ W p.1 u) (1 / ((m : ℝ) + 1))) (cfHullQ s p.2)}) with hTdef
    have heq : {p | (q : ℝ) ∈ gPre s ζ W E p} = (E ∩ T) ∪ Eᶜ := by
      ext p
      by_cases hp : p ∈ E
      · obtain ⟨hα, hG, -, -, hQ⟩ := hEg p hp
        have hGc : IsClosed (cfHullQ s p.2) := by rw [hQ]; exact hG
        simp only [mem_ofPred_eq, gPre_of_mem hp, mem_preContact_iff_ball hα.cont hGc hq, mem_union,
          mem_inter_iff, hp, true_and, mem_compl_iff, not_true_eq_false, or_false, hTdef, mem_iUnion,
          mem_iInter]
        constructor
        · rintro ⟨m, hm⟩
          refine ⟨m, fun u => ?_⟩
          by_cases hu : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q
          · exact Or.inr (hm u hu.1 hu.2)
          · exact Or.inl hu
        · rintro ⟨m, hm⟩
          refine ⟨m, fun u hu0 huq => ?_⟩
          rcases hm u with h | h
          · exact absurd ⟨hu0, huq⟩ h
          · exact h
      · simp only [mem_ofPred_eq, gPre, hp, ↓reduceIte, mem_Ici, mem_union, mem_inter_iff, false_and,
          mem_compl_iff, not_false_eq_true, or_true, iff_true]
        exact hq
    rw [heq]
    refine (hE.inter (MeasurableSet.iUnion fun m => MeasurableSet.iInter fun u =>
      (MeasurableSet.const _).compl.union ?_)).union hE.compl
    exact measurableSet_disjoint_ball ((measurable_seedLine hW u).comp measurable_fst)
      ((measurable_cfHullQ s).comp measurable_snd) (fun p => (cfHullQ_relClosed s p.2).1) _
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
theorem measurable_indicator_capClock_gCurve (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (q : ℚ) :
    Measurable ({p | (q : ℝ) ∈ gPre s ζ W E p}.indicator fun p => capClock (gCurve s ζ W E p) q) := by
  classical
  set A := {p | (q : ℝ) ∈ gPre s ζ W E p} with hAdef
  have hA : MeasurableSet A := measurableSet_mem_gPre hW hE hEg q
  have hK := isKilledArc_gCurve hEg (s := s) (ζ := ζ) (W := W)
  set Γ : Ω × HistorySpace 0 0 → ℝ≥0 → ℂ := fun p t =>
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
    Measurable.ite hA (measurable_gCurve hW hE _) measurable_const
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
theorem measurableSet_lt_imgT (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (t : ℝ≥0) :
    MeasurableSet {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} :=
  measurableSet_lt_kLife (isKilledArc_gCurve hEg) (measurableSet_mem_gPre hW hE hEg)
    (measurable_indicator_capClock_gCurve hW hE hEg) t

/-- **The killed image driver is measurable at every time.** -/
theorem measurable_imgW (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (t : ℝ≥0) : Measurable (imgW s ζ W E t) := by
  classical
  have h := measurable_indicator_kW_of_base (isKilledArc_gCurve hEg) (measurableSet_mem_gPre hW hE hEg)
    (measurable_indicator_capClock_gCurve hW hE hEg) (fun q => measurable_gCurve hW hE q) t
  convert h using 1
  funext p
  by_cases ht : (t : WithTop ℝ≥0) < kLife (gCurve s ζ W E p) (gPre s ζ W E p)
  · rw [indicator_of_mem (show p ∈ {p | (t : WithTop ℝ≥0) < kLife (gCurve s ζ W E p) (gPre s ζ W E p)} from ht)]
    rfl
  · rw [indicator_of_notMem (show p ∉ {p | (t : WithTop ℝ≥0) < kLife (gCurve s ζ W E p) (gPre s ζ W E p)} from ht)]
    simp only [imgW, kW, ht, ↓reduceIte]

end Glue

/-! ### The marks -/

section Marks

theorem measurable_rightImg_cfDrv0_one (s : ℝ≥0) (x : ℝ) :
    Measurable fun y : HistorySpace 0 0 => rightImg (cfDrv0 s y) x s := by
  have := measurable_rightImg_cfDrv0 s 1 x s
  simpa only [one_mul] using this

theorem measurable_rightImg_neg_cfDrv0 (s : ℝ≥0) (x : ℝ) :
    Measurable fun y : HistorySpace 0 0 => rightImg (fun r => -cfDrv0 s y r) x s := by
  have := measurable_rightImg_cfDrv0 s (-1) x s
  simpa only [neg_one_mul] using this

theorem measurable_psiL (s : ℝ≥0) (x : ℝ) : Measurable fun y : HistorySpace 0 0 => psiL (cfDrv0 s y) s x := by
  unfold psiL
  split_ifs
  · exact measurable_const
  · exact measurable_const.div ((measurable_rightImg_cfDrv0_one s _).sub (measurable_cfDrv0_apply' s s))

theorem measurable_psiR (s : ℝ≥0) (x : ℝ) : Measurable fun y : HistorySpace 0 0 => psiR (cfDrv0 s y) s x := by
  unfold psiR
  split_ifs
  · exact measurable_const
  · exact measurable_const.div ((measurable_rightImg_neg_cfDrv0 s _).neg.sub (measurable_cfDrv0_apply' s s))

theorem measurable_junL (s : ℝ≥0) : Measurable fun y : HistorySpace 0 0 => junL (cfDrv0 s y) s :=
  measurable_const.div ((measurable_rightImg_cfDrv0_one s 0).sub (measurable_cfDrv0_apply' s s))

theorem measurable_junR (s : ℝ≥0) : Measurable fun y : HistorySpace 0 0 => junR (cfDrv0 s y) s :=
  measurable_const.div ((measurable_rightImg_neg_cfDrv0 s 0).neg.sub (measurable_cfDrv0_apply' s s))

theorem measurable_snoc {α : Type*} [MeasurableSpace α] {n : ℕ} {f : α → Fin n → ℝ} {x : α → ℝ}
    (hf : Measurable f) (hx : Measurable x) : Measurable fun a => (Fin.snoc (f a) (x a) : Fin (n + 1) → ℝ) := by
  refine measurable_pi_iff.2 fun j => ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply i).comp hf
  · simp only [Fin.snoc_last]
    exact hx

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {nL nR : ℕ}

theorem measurable_gXL (xL : Fin nL → ℝ) (hE : MeasurableSet E) :
    Measurable fun p : Ω × HistorySpace 0 0 => gXL xL s E p := by
  classical
  unfold gXL
  refine Measurable.ite hE ?_ measurable_const
  exact measurable_snoc (measurable_pi_iff.2 fun i => (measurable_psiL s (xL i)).comp measurable_snd)
    ((measurable_junL s).comp measurable_snd)

theorem measurable_gXR (xR : Fin nR → ℝ) (hE : MeasurableSet E) :
    Measurable fun p : Ω × HistorySpace 0 0 => gXR xR s E p := by
  classical
  unfold gXR
  refine Measurable.ite hE ?_ measurable_const
  exact measurable_snoc (measurable_pi_iff.2 fun j => (measurable_psiR s (xR j)).comp measurable_snd)
    ((measurable_junR s).comp measurable_snd)

/-- The killed image driver frozen after `t` (on `{t < imgT}`; `0` elsewhere). -/
def frzImg (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (t : ℝ≥0) :
    ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  open scoped Classical in
  fun u p => if (t : WithTop ℝ≥0) < imgT s ζ W E p then imgW s ζ W E (min u t) p else 0

theorem frzImg_props (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    (t : ℝ≥0) :
    (∀ u, Measurable (frzImg s ζ W E t u)) ∧ (∀ p, Continuous fun u => frzImg s ζ W E t u p) ∧
      ∀ p, (t : WithTop ℝ≥0) < imgT s ζ W E p →
        EqOn (kPath (gCurve s ζ W E p) (gPre s ζ W E p)) (Bessel.realPath (frzImg s ζ W E t) p) (Icc 0 t) := by
  classical
  refine ⟨fun u => Measurable.ite (measurableSet_lt_imgT hW hE hEg t) (measurable_imgW hW hE hEg _)
    measurable_const, fun p => ?_, fun p ht r hr => ?_⟩
  · by_cases ht : (t : WithTop ℝ≥0) < imgT s ζ W E p
    · simp only [frzImg, ht, ↓reduceIte]
      refine ((isKilledArc_gCurve hEg p).continuousOn_kW).comp_continuous (continuous_id.min continuous_const)
        fun u => lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right u t)) ht
    · simp only [frzImg, ht, ↓reduceIte]
      exact continuous_const
  · have hrt : r.toNNReal ≤ t := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    simp only [Bessel.realPath, frzImg, ht, ↓reduceIte, min_eq_left hrt]
    rfl

/-- **The images of the right marks are measurable at every time.** -/
theorem measurable_imgVR (xR : Fin nR → ℝ) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (j : Fin (nR + 1)) (t : ℝ≥0) : Measurable (imgVR xR s ζ W E j t) := by
  classical
  obtain ⟨hm, hc, hEq⟩ := frzImg_props hW hE hEg t
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun p => rightImg (Bessel.realPath (frzImg s ζ W E t) p) (gXR xR s E p j) t :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) hm hc
      ((measurable_pi_apply j).comp (measurable_gXR xR hE)) t
  have heq : imgVR xR s ζ W E j t = {p | (t : WithTop ℝ≥0) < imgT s ζ W E p}.indicator
      fun p => rightImg (Bessel.realPath (frzImg s ζ W E t) p) (gXR xR s E p j) t := by
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
  exact hR.indicator (measurableSet_lt_imgT hW hE hEg t)

/-- **The images of the left marks are measurable at every time.** -/
theorem measurable_imgVL (xL : Fin nL → ℝ) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (i : Fin (nL + 1)) (t : ℝ≥0) : Measurable (imgVL xL s ζ W E i t) := by
  classical
  obtain ⟨hm, hc, hEq⟩ := frzImg_props hW hE hEg t
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun p => rightImg (Bessel.realPath (fun u p => -frzImg s ζ W E t u p) p)
      (-gXL xL s E p i) t :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) (fun u => (hm u).neg)
      (fun p => (hc p).neg) ((measurable_pi_apply i).comp (measurable_gXL xL hE)).neg t
  have heq : imgVL xL s ζ W E i t = {p | (t : WithTop ℝ≥0) < imgT s ζ W E p}.indicator
      fun p => -rightImg (Bessel.realPath (fun u p => -frzImg s ζ W E t u p) p) (-gXL xL s E p i) t := by
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
  exact hR.neg.indicator (measurableSet_lt_imgT hW hE hEg t)

end Marks

end Word49

end InteractingSLE.Sec5.CrossCond
