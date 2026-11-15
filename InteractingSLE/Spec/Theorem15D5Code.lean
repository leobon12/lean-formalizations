/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15D5Borel
import InteractingSLE.Spec.Sec2.AssemblyCode
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import InteractingSLE.Foundations.Measure.AnalyticUniversal

/-!
# W0's completion predicate is universally measurable on dyadic codes

Packet PROVE-T15-D5, infrastructure for D.5's crossing step. W0's predicate `HasOrderedProperCompletions α a β c`
is an `∃` over proper completions; the specification remarks that it is analytic (supplement §9, p. 528). Here:

* complex paths are coded by their values at the dyadic times (`CCode`, `encC`) and decoded by the real and
  imaginary decodings of Theorem 2.2's assembly (`decC`; `GoodC`, `GoodAll`: uniformly continuous codes);
* each clause of `IsProperCompletion` and the closed-left-side inclusion is a countable condition on the codes of a
  continuous completion (`injective_iff_injC`, `im_nonneg_iff_imC`, `tendsto_norm_iff_propC`, `agree_iff_agreeC`,
  `range_subset_closedLeftSide_iff`, `mem_closedLeftSide_decC_iff`), so the relation `CompRel a c` between the codes
  of `(α, β)` and the codes of a pair of completions is Borel (`measurableSet_compRel`);
* for paths continuous on the prefixes, `HasOrderedProperCompletions α a β c` holds iff the code of `(α, β)` lies in
  the projection of `CompRel a c` (`hasOrderedProperCompletions_iff_exists`), which is universally measurable
  (Lusin: `LQGMetric.UMeasurableSet.setOf_exists`; `uMeasurableSet_hopcCode`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Topology Filter MeasureTheory
open scoped NNReal

namespace InteractingSLE

namespace Theorem15D5

open Sec2.Assembly

/-! ### Codes of complex paths -/

/-- Codes of complex paths: `q n k` is the value at the dyadic time `k / 2ⁿ`. -/
abbrev CCode : Type := ℕ → ℕ → ℂ

/-- The real-part code. -/
def reCode (q : CCode) : PCode := fun n k => (q n k).re

/-- The imaginary-part code. -/
def imCode (q : CCode) : PCode := fun n k => (q n k).im

/-- Decoding a complex code. -/
def decC (q : CCode) (t : ℝ≥0) : ℂ := (dec (reCode q) t : ℂ) + (dec (imCode q) t : ℂ) * Complex.I

/-- The code of a complex path. -/
def encC (γ : ℝ≥0 → ℂ) : CCode := fun n k => γ (dyad n k)

/-- A code uniformly continuous on the dyadic times of `[0, T]`. -/
def GoodC (q : CCode) (T : ℝ≥0) : Prop := UC (reCode q) T ∧ UC (imCode q) T

/-- A code uniformly continuous on the dyadic times of every `[0, N]`. -/
def GoodAll (q : CCode) : Prop := ∀ N : ℕ, GoodC q N

theorem measurable_coord (n k : ℕ) : Measurable fun q : CCode => q n k :=
  (measurable_pi_apply k).comp (measurable_pi_apply n)

theorem measurable_reCode : Measurable reCode :=
  measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k =>
    Complex.measurable_re.comp (measurable_coord n k)

theorem measurable_imCode : Measurable imCode :=
  measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k =>
    Complex.measurable_im.comp (measurable_coord n k)

theorem measurable_goodC (T : ℝ≥0) : Measurable fun q : CCode => GoodC q T :=
  ((measurableSet_UC T).mem.comp measurable_reCode).and ((measurableSet_UC T).mem.comp measurable_imCode)

theorem measurable_goodAll : Measurable GoodAll :=
  Measurable.forall fun N => measurable_goodC N

theorem GoodC.continuousOn {q : CCode} {T : ℝ≥0} (h : GoodC q T) : ContinuousOn (decC q) (Iic T) := by
  unfold decC
  exact (Complex.continuous_ofReal.comp_continuousOn h.1.continuousOn).add
    ((Complex.continuous_ofReal.comp_continuousOn h.2.continuousOn).mul continuousOn_const)

theorem GoodC.decC_dyad {q : CCode} {T : ℝ≥0} (h : GoodC q T) {n k : ℕ} (hle : dyad n k ≤ T) :
    decC q (dyad n k) = q n k := by
  unfold decC
  rw [h.1.dec_dyad hle, h.2.dec_dyad hle]
  exact Complex.re_add_im (q n k)

theorem GoodC.tendsto {q : CCode} {T t : ℝ≥0} (h : GoodC q T) (ht : t ≤ T) :
    Tendsto (fun n => q n (flr n t)) atTop (𝓝 (decC q t)) := by
  have h1 := (Complex.continuous_ofReal.tendsto _).comp (h.1.tendsto_flr ht)
  have h2 := (Complex.continuous_ofReal.tendsto _).comp (h.2.tendsto_flr ht)
  unfold decC
  exact (h1.add (h2.mul_const Complex.I)).congr fun n => Complex.re_add_im (q n (flr n t))

theorem goodC_encC {γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hγ : ContinuousOn γ (Iic T)) : GoodC (encC γ) T :=
  ⟨uc_enc (f := fun t => (γ t).re) (Complex.continuous_re.comp_continuousOn hγ),
    uc_enc (f := fun t => (γ t).im) (Complex.continuous_im.comp_continuousOn hγ)⟩

theorem decC_encC {γ : ℝ≥0 → ℂ} {t : ℝ≥0} (hγ : ContinuousWithinAt γ (Iic t) t) :
    decC (encC γ) t = γ t := by
  unfold decC
  have h1 : dec (reCode (encC γ)) t = (γ t).re :=
    dec_enc (f := fun t => (γ t).re) (Complex.continuous_re.continuousAt.comp_continuousWithinAt hγ)
  have h2 : dec (imCode (encC γ)) t = (γ t).im :=
    dec_enc (f := fun t => (γ t).im) (Complex.continuous_im.continuousAt.comp_continuousWithinAt hγ)
  rw [h1, h2]
  exact Complex.re_add_im _

theorem decC_encC_of_continuousOn {γ : ℝ≥0 → ℂ} {a t : ℝ≥0} (hγ : ContinuousOn γ (Iic a)) (ht : t ≤ a) :
    decC (encC γ) t = γ t :=
  decC_encC ((hγ.mono (Iic_subset_Iic.mpr ht)) t self_mem_Iic)

theorem GoodAll.continuous {q : CCode} (h : GoodAll q) : Continuous (decC q) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt t
  exact (h N).continuousOn.continuousAt (Iic_mem_nhds hN)

theorem GoodAll.decC_dyad {q : CCode} (h : GoodAll q) (n k : ℕ) : decC q (dyad n k) = q n k := by
  obtain ⟨N, hN⟩ := exists_nat_ge (dyad n k)
  exact (h N).decC_dyad hN

theorem GoodAll.tendsto {q : CCode} (h : GoodAll q) (t : ℝ≥0) :
    Tendsto (fun n => q n (flr n t)) atTop (𝓝 (decC q t)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge t
  exact (h N).tendsto hN

theorem dyad_zero_zero : dyad 0 0 = 0 := by simp [dyad]

theorem GoodAll.decC_zero {q : CCode} (h : GoodAll q) : decC q 0 = q 0 0 := by
  rw [← h.decC_dyad 0 0, dyad_zero_zero]

theorem goodAll_encC {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) : GoodAll (encC γ) := fun _ =>
  goodC_encC hγ.continuousOn

theorem decC_encC_of_continuous {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) : decC (encC γ) = γ :=
  funext fun _ => decC_encC hγ.continuousAt.continuousWithinAt

/-- Dyadic floors converge to `t` in `ℝ`. -/
theorem tendsto_dyad_flr_real (t : ℝ≥0) : Tendsto (fun n => ((dyad n (flr n t) : ℝ≥0) : ℝ)) atTop (𝓝 (t : ℝ)) :=
  NNReal.tendsto_coe.mpr (tendsto_dyad_flr t)

/-! ### Injectivity -/

/-- Countable injectivity: the images of disjoint rational intervals stay a positive distance apart at the dyadic
times. -/
def InjC (q : CCode) : Prop :=
  ∀ a b c d : ℚ, b < c → ∃ m : ℕ, ∀ n i j : ℕ, (a : ℝ) ≤ dyad n i → (dyad n i : ℝ) ≤ b →
    (c : ℝ) ≤ dyad n j → (dyad n j : ℝ) ≤ d → 1 / ((m : ℝ) + 1) ≤ dist (q n i) (q n j)

theorem measurable_injC : Measurable InjC :=
  Measurable.forall fun _ => Measurable.forall fun _ => Measurable.forall fun _ => Measurable.forall fun _ =>
    measurable_const.imp <| Measurable.exists fun _ => Measurable.forall fun n => Measurable.forall fun i =>
      Measurable.forall fun j => measurable_const.imp <| measurable_const.imp <| measurable_const.imp <|
        measurable_const.imp <| measurableSet_setOfPred.mp
          (measurableSet_le measurable_const ((measurable_coord n i).dist (measurable_coord n j)))

theorem isCompact_Icc_nnreal (x y : ℝ≥0) : IsCompact (Icc x y) := isCompact_Icc

theorem injective_iff_injC {q : CCode} (h : GoodAll q) : Function.Injective (decC q) ↔ InjC q := by
  have hc := h.continuous
  constructor
  · intro hinj a b c d hbc
    by_cases hb : (b : ℝ) < 0
    · refine ⟨0, fun n i j hai hib => absurd (hib.trans_lt hb) (not_lt.mpr (dyad n i).2)⟩
    push Not at hb
    set K₁ : Set ℝ≥0 := Icc (Real.toNNReal a) (Real.toNNReal b)
    set K₂ : Set ℝ≥0 := Icc (Real.toNNReal c) (Real.toNNReal d)
    have hcb : (b : ℝ) < c := by exact_mod_cast hbc
    have hdis : Disjoint (decC q '' K₁) (decC q '' K₂) := by
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hxy' : y = x := hinj hxy
      rw [hxy'] at hy
      have h1 : (x : ℝ) ≤ b := by
        have := hx.2
        rwa [Real.toNNReal_of_nonneg hb, ← NNReal.coe_le_coe, NNReal.coe_mk] at this
      have h2 : (c : ℝ) ≤ x := (Real.toNNReal_le_iff_le_coe).mp hy.1
      linarith
    have hK₁ : IsCompact (decC q '' K₁) := (isCompact_Icc_nnreal _ _).image hc
    have hK₂ : IsCompact (decC q '' K₂) := (isCompact_Icc_nnreal _ _).image hc
    obtain ⟨δ, hδ, hsub⟩ := hK₁.exists_thickening_subset_open hK₂.isClosed.isOpen_compl
      (subset_compl_iff_disjoint_right.mpr hdis)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun n i j hai hib hcj hjd => ?_⟩
    have hi : dyad n i ∈ K₁ :=
      ⟨Real.toNNReal_le_iff_le_coe.mpr hai, Real.le_toNNReal_iff_coe_le hb |>.mpr hib⟩
    have hj : dyad n j ∈ K₂ :=
      ⟨Real.toNNReal_le_iff_le_coe.mpr hcj,
        Real.le_toNNReal_iff_coe_le ((Rat.cast_nonneg.mpr ?_)) |>.mpr hjd⟩
    · by_contra hlt
      push Not at hlt
      have hmem : decC q (dyad n j) ∈ thickening δ (decC q '' K₁) := by
        rw [mem_thickening_iff]
        refine ⟨decC q (dyad n i), mem_image_of_mem _ hi, ?_⟩
        rw [h.decC_dyad, h.decC_dyad, dist_comm]
        exact hlt.trans hm
      exact hsub hmem (mem_image_of_mem _ hj)
    · have : (0 : ℝ) ≤ d := (dyad n j).2.trans hjd
      exact_mod_cast this
  · intro hI s t hst
    by_contra hne
    wlog hlt : s < t generalizing s t
    · exact this hst.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    obtain ⟨b, hsb, hbt⟩ := exists_rat_btwn (show (s : ℝ) < t from hlt)
    obtain ⟨c, hbc, hct⟩ := exists_rat_btwn hbt
    obtain ⟨a, -, has⟩ := exists_rat_btwn (show (s : ℝ) - 1 < s by linarith)
    obtain ⟨d, htd, -⟩ := exists_rat_btwn (show (t : ℝ) < t + 1 by linarith)
    obtain ⟨m, hm⟩ := hI a b c d (by exact_mod_cast hbc)
    have hs₁ := (tendsto_dyad_flr_real s).eventually (lt_mem_nhds has)
    have ht₁ := (tendsto_dyad_flr_real t).eventually (lt_mem_nhds hct)
    have hev : ∀ᶠ n in atTop, 1 / ((m : ℝ) + 1) ≤ dist (q n (flr n s)) (q n (flr n t)) := by
      filter_upwards [hs₁, ht₁] with n hn₁ hn₂
      refine hm n _ _ hn₁.le ?_ hn₂.le ?_
      · exact (NNReal.coe_le_coe.mpr (dyad_flr_le n s)).trans hsb.le
      · exact (NNReal.coe_le_coe.mpr (dyad_flr_le n t)).trans htd.le
    have hlim := ge_of_tendsto ((h.tendsto s).dist (h.tendsto t)) hev
    rw [hst, dist_self] at hlim
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

/-! ### The closed half-plane, properness, agreement on the prefix -/

/-- Countable form of `0 ≤ Im`. -/
def ImC (q : CCode) : Prop := ∀ n k, 0 ≤ (q n k).im

theorem measurable_imC : Measurable ImC :=
  Measurable.forall fun n => Measurable.forall fun k => measurableSet_setOfPred.mp
    (measurableSet_le measurable_const (Complex.measurable_im.comp (measurable_coord n k)))

theorem im_nonneg_iff_imC {q : CCode} (h : GoodAll q) : (∀ t, 0 ≤ (decC q t).im) ↔ ImC q := by
  constructor
  · intro hq n k
    rw [← h.decC_dyad]
    exact hq _
  · intro hq t
    exact ge_of_tendsto' ((Complex.continuous_im.tendsto _).comp (h.tendsto t)) fun n => hq n _

/-- Countable form of properness `‖γ t‖ → ∞`. -/
def PropC (q : CCode) : Prop := ∀ N : ℕ, ∃ K : ℕ, ∀ n k, (K : ℝ≥0) ≤ dyad n k → (N : ℝ) ≤ ‖q n k‖

theorem measurable_propC : Measurable PropC :=
  Measurable.forall fun _ => Measurable.exists fun _ => Measurable.forall fun n => Measurable.forall fun k =>
    measurable_const.imp <| measurableSet_setOfPred.mp
      (measurableSet_le measurable_const (measurable_coord n k).norm)

theorem tendsto_norm_iff_propC {q : CCode} (h : GoodAll q) :
    Tendsto (fun t => ‖decC q t‖) atTop atTop ↔ PropC q := by
  constructor
  · intro hT N
    obtain ⟨T, hT'⟩ := eventually_atTop.mp (Filter.tendsto_atTop.mp hT N)
    refine ⟨⌈T⌉₊, fun n k hk => ?_⟩
    rw [← h.decC_dyad]
    exact hT' _ ((Nat.le_ceil T).trans hk)
  · intro hP
    rw [Filter.tendsto_atTop]
    intro r
    obtain ⟨N, hN⟩ := exists_nat_ge r
    obtain ⟨K, hK⟩ := hP N
    rw [eventually_atTop]
    refine ⟨(K : ℝ≥0) + 1, fun t ht => hN.trans ?_⟩
    have hKt : ((K : ℝ≥0) : ℝ) < t := by
      have : ((K : ℝ≥0) : ℝ) + 1 ≤ t := by exact_mod_cast ht
      linarith
    have hev : ∀ᶠ n in atTop, (N : ℝ) ≤ ‖q n (flr n t)‖ := by
      filter_upwards [(tendsto_dyad_flr_real t).eventually (lt_mem_nhds hKt)] with n hn
      exact hK n _ (by exact_mod_cast hn.le)
    exact ge_of_tendsto ((continuous_norm.tendsto _).comp (h.tendsto t)) hev

/-- Countable agreement with a prefix code on `[0, a]`. -/
def AgreeC (q p : CCode) (a : ℝ≥0) : Prop := ∀ n k, dyad n k ≤ a → q n k = p n k

theorem measurable_agreeC (a : ℝ≥0) : Measurable fun x : CCode × CCode => AgreeC x.1 x.2 a :=
  Measurable.forall fun n => Measurable.forall fun k => measurable_const.imp <|
    measurableSet_setOfPred.mp (measurableSet_eq_fun ((measurable_coord n k).comp measurable_fst)
      ((measurable_coord n k).comp measurable_snd))

theorem agree_iff_agreeC {q p : CCode} {a : ℝ≥0} (hq : GoodAll q) (hp : GoodC p a) :
    (∀ t ≤ a, decC q t = decC p t) ↔ AgreeC q p a := by
  constructor
  · intro h n k hk
    rw [← hq.decC_dyad, ← hp.decC_dyad hk]
    exact h _ hk
  · intro h t ht
    refine tendsto_nhds_unique (hq.tendsto t) ((hp.tendsto ht).congr fun n => ?_)
    exact (h n _ ((dyad_flr_le n t).trans ht)).symm

/-! ### The seed-ray closure and the closed left side of a decoded completion -/

/-- A continuous proper path has closed range. -/
theorem isClosed_range_of_tendsto_norm {g : ℝ≥0 → ℂ} (hg : Continuous g)
    (hp : Tendsto (fun t => ‖g t‖) atTop atTop) : IsClosed (range g) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  obtain ⟨T, hT⟩ := eventually_atTop.mp (Filter.tendsto_atTop.mp hp (‖z‖ + 1))
  have hsub : range g ⊆ g '' Icc 0 T ∪ {w | ‖z‖ + 1 ≤ ‖w‖} := by
    rintro _ ⟨t, rfl⟩
    rcases le_total t T with htT | hTt
    · exact Or.inl ⟨t, ⟨zero_le, htT⟩, rfl⟩
    · exact Or.inr (hT t hTt)
  have hcl : IsClosed (g '' Icc 0 T ∪ {w | ‖z‖ + 1 ≤ ‖w‖}) :=
    ((isCompact_Icc_nnreal 0 T).image hg).isClosed.union (isClosed_le continuous_const continuous_norm)
  rcases closure_minimal hsub hcl hz with ⟨t, -, rfl⟩ | h
  · exact mem_range_self t
  · exact absurd h (by simp only [mem_ofPred_eq, not_le]; linarith)

/-- The countable family whose closure is the seed-ray closure of a decoded completion: the dyadic values and the
points `γ 0 − |r| i`, `r ∈ ℚ`. -/
def seedFamily (q : CCode) : (ℕ × ℕ) ⊕ ℚ → ℂ :=
  Sum.elim (fun p => q p.1 p.2) fun r => q 0 0 - ((|(r : ℝ)| : ℝ) : ℂ) * Complex.I

theorem measurable_seedFamily {X : Type*} [MeasurableSpace X] {q : X → CCode}
    (hq : ∀ n k, Measurable fun x => q x n k) (i : (ℕ × ℕ) ⊕ ℚ) :
    Measurable fun x => seedFamily (q x) i := by
  rcases i with p | r
  · exact hq p.1 p.2
  · exact (hq 0 0).sub measurable_const

/-- **The seed-ray closure of a decoded proper completion** is the closure of `seedFamily`. -/
theorem seedRayClosure_decC {q : CCode} (h : GoodAll q) (hp : PropC q) :
    seedRayClosure (decC q) = closure (range (seedFamily q)) := by
  have hc := h.continuous
  have hT := (tendsto_norm_iff_propC h).mpr hp
  unfold seedRayClosure seedFamily
  rw [Set.Sum.elim_range, closure_union, h.decC_zero]
  congr 1
  · apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      exact mem_closure_of_tendsto (h.tendsto t) (Eventually.of_forall fun n => ⟨(n, flr n t), rfl⟩)
    · refine closure_minimal ?_ (isClosed_range_of_tendsto_norm hc hT)
      rintro _ ⟨p, rfl⟩
      exact ⟨dyad p.1 p.2, h.decC_dyad p.1 p.2⟩
  · apply Subset.antisymm
    · intro z hz
      rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball]
      intro ε hε
      set s : ℝ := (q 0 0).im - z.im with hs
      have hs0 : 0 ≤ s := by rw [hs]; linarith [hz.2]
      obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show s - ε < s + ε by linarith)
      refine ⟨_, ⟨r, rfl⟩, ?_⟩
      rw [mem_ball, Complex.dist_eq]
      have hz' : z = q 0 0 - (s : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [hz.1]
        · simp [hs]
      rw [hz']
      have : q 0 0 - ((|(r : ℝ)| : ℝ) : ℂ) * Complex.I - (q 0 0 - (s : ℂ) * Complex.I) =
          ((s - |(r : ℝ)| : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      calc abs (s - |(r : ℝ)|) = abs (|s| - |(r : ℝ)|) := by rw [abs_of_nonneg hs0]
        _ ≤ abs (s - r) := abs_abs_sub_abs_le_abs_sub _ _
        _ < ε := by rw [abs_lt]; constructor <;> linarith
    · refine closure_minimal ?_ ((isClosed_eq Complex.continuous_re continuous_const).inter
        (isClosed_le Complex.continuous_im continuous_const))
      rintro _ ⟨r, rfl⟩
      refine ⟨by simp, ?_⟩
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
        Complex.I_re, mul_one, mul_zero, add_zero]
      linarith [abs_nonneg (r : ℝ)]

/-- Membership in the closed left side of a decoded proper completion, through `seedFamily` and polygonal
reachability from the base point `q 0 0 − 1 − i`. -/
theorem mem_closedLeftSide_decC_iff {q : CCode} (h : GoodAll q) (hp : PropC q) (z : ℂ) :
    z ∈ closedLeftSide (decC q) ↔ z ∈ closure (range (seedFamily q)) ∨
      ∃ j, Reach (closure (range (seedFamily q)))ᶜ (q 0 0 - 1 - Complex.I) j z := by
  have hF : IsClosed (seedRayClosure (decC q)) := by
    rw [seedRayClosure_decC h hp]; exact isClosed_closure
  rw [mem_closedLeftSide_iff hF, seedRayClosure_decC h hp, h.decC_zero]

/-- The range of a decoded path lies in the closed left side of a decoded proper completion iff its dyadic values
do (the closed left side is closed). -/
theorem range_subset_closedLeftSide_iff {q₁ q₂ : CCode} (h₁ : GoodAll q₁) (hp₁ : PropC q₁)
    (h₂ : GoodAll q₂) : range (decC q₂) ⊆ closedLeftSide (decC q₁) ↔ ∀ n k, q₂ n k ∈ closedLeftSide (decC q₁) := by
  constructor
  · intro hs n k
    rw [← h₂.decC_dyad]
    exact hs (mem_range_self _)
  · rintro hs _ ⟨t, rfl⟩
    have hF : IsClosed (seedRayClosure (decC q₁)) := by
      rw [seedRayClosure_decC h₁ hp₁]; exact isClosed_closure
    exact (isClosed_closedLeftSide hF).mem_of_tendsto (h₂.tendsto t) (Eventually.of_forall fun n => hs n _)

/-! ### The Borel relation and the universally measurable completion event -/

/-- **The completion relation** between the codes `(p₁, p₂)` of two prefixes `α|[0, a]`, `β|[0, c]` and the codes
`(q₁, q₂)` of a pair of ordered proper completions. -/
def CompRel (a c : ℝ≥0) : Set ((CCode × CCode) × (CCode × CCode)) :=
  {x | GoodC x.1.1 a ∧ GoodC x.1.2 c ∧ GoodAll x.2.1 ∧ GoodAll x.2.2 ∧
    IsProperCompletion (decC x.1.1) a (decC x.2.1) ∧ IsProperCompletion (decC x.1.2) c (decC x.2.2) ∧
    range (decC x.2.2) ⊆ closedLeftSide (decC x.2.1)}

/-- The countable form of `CompRel`. -/
def CompRelC (a c : ℝ≥0) : Set ((CCode × CCode) × (CCode × CCode)) :=
  {x | GoodC x.1.1 a ∧ GoodC x.1.2 c ∧ GoodAll x.2.1 ∧ GoodAll x.2.2 ∧
    (InjC x.2.1 ∧ ImC x.2.1 ∧ PropC x.2.1 ∧ AgreeC x.2.1 x.1.1 a) ∧
    (InjC x.2.2 ∧ ImC x.2.2 ∧ PropC x.2.2 ∧ AgreeC x.2.2 x.1.2 c) ∧
    ∀ n k, x.2.2 n k ∈ closure (range (seedFamily x.2.1)) ∨
      ∃ j, Reach (closure (range (seedFamily x.2.1)))ᶜ (x.2.1 0 0 - 1 - Complex.I) j (x.2.2 n k)}

theorem isProperCompletion_decC_iff {p q : CCode} {a : ℝ≥0} (hp : GoodC p a) (hq : GoodAll q) :
    IsProperCompletion (decC p) a (decC q) ↔ InjC q ∧ ImC q ∧ PropC q ∧ AgreeC q p a := by
  unfold IsProperCompletion
  rw [injective_iff_injC hq, im_nonneg_iff_imC hq, tendsto_norm_iff_propC hq, agree_iff_agreeC hq hp]
  exact ⟨fun h => h.2, fun h => ⟨hq.continuous, h⟩⟩

theorem compRel_eq (a c : ℝ≥0) : CompRel a c = CompRelC a c := by
  ext x
  constructor
  · rintro ⟨g₁, g₂, g₃, g₄, c₁, c₂, hr⟩
    have c₁' := (isProperCompletion_decC_iff g₁ g₃).mp c₁
    refine ⟨g₁, g₂, g₃, g₄, c₁', (isProperCompletion_decC_iff g₂ g₄).mp c₂, fun n k => ?_⟩
    exact (mem_closedLeftSide_decC_iff g₃ c₁'.2.2.1 _).mp
      ((range_subset_closedLeftSide_iff g₃ c₁'.2.2.1 g₄).mp hr n k)
  · rintro ⟨g₁, g₂, g₃, g₄, c₁, c₂, hr⟩
    refine ⟨g₁, g₂, g₃, g₄, (isProperCompletion_decC_iff g₁ g₃).mpr c₁,
      (isProperCompletion_decC_iff g₂ g₄).mpr c₂, ?_⟩
    exact (range_subset_closedLeftSide_iff g₃ c₁.2.2.1 g₄).mpr fun n k =>
      (mem_closedLeftSide_decC_iff g₃ c₁.2.2.1 _).mpr (hr n k)

/-- **The completion relation is Borel.** -/
theorem measurableSet_compRel (a c : ℝ≥0) : MeasurableSet (CompRel a c) := by
  rw [compRel_eq]
  have m11 : Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.1.1 := measurable_fst.fst
  have m12 : Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.1.2 := measurable_fst.snd
  have m21 : Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.2.1 := measurable_snd.fst
  have m22 : Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.2.2 := measurable_snd.snd
  have hc21 : ∀ n k, Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.2.1 n k :=
    fun n k => (measurable_coord n k).comp m21
  have hc22 : ∀ n k, Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.2.2 n k :=
    fun n k => (measurable_coord n k).comp m22
  have hfam : ∀ i, Measurable fun x : (CCode × CCode) × (CCode × CCode) => seedFamily x.2.1 i :=
    measurable_seedFamily hc21
  have hw : Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.2.1 0 0 - 1 - Complex.I :=
    ((hc21 0 0).sub measurable_const).sub measurable_const
  refine measurableSet_setOfPred.mpr ?_
  refine ((measurable_goodC a).comp m11).and <| ((measurable_goodC c).comp m12).and <|
    (measurable_goodAll.comp m21).and <| (measurable_goodAll.comp m22).and <| ?_
  refine (((measurable_injC.comp m21).and <| (measurable_imC.comp m21).and <| (measurable_propC.comp m21).and <|
    (measurable_agreeC a).comp (m21.prodMk m11))).and <| ?_
  refine (((measurable_injC.comp m22).and <| (measurable_imC.comp m22).and <| (measurable_propC.comp m22).and <|
    (measurable_agreeC c).comp (m22.prodMk m12))).and <| ?_
  refine Measurable.forall fun n => Measurable.forall fun k => ?_
  exact (measurableSet_setOfPred.mp (measurableSet_mem_closure_range hfam (hc22 n k))).or
    (Measurable.exists fun j => measurableSet_setOfPred.mp (measurableSet_reach hfam hw j (hc22 n k)))

/-- **W0's predicate through codes**: for paths continuous on the prefixes, `HasOrderedProperCompletions α a β c`
holds iff the code of `(α, β)` lies in the projection of `CompRel a c`. -/
theorem hasOrderedProperCompletions_iff_exists {α β : ℝ≥0 → ℂ} {a c : ℝ≥0} (hα : ContinuousOn α (Iic a))
    (hβ : ContinuousOn β (Iic c)) :
    HasOrderedProperCompletions α a β c ↔ ∃ y, ((encC α, encC β), y) ∈ CompRel a c := by
  constructor
  · rintro ⟨α', β', hα', hβ', hsub⟩
    refine ⟨(encC α', encC β'), goodC_encC hα, goodC_encC hβ, goodAll_encC hα'.1, goodAll_encC hβ'.1, ?_, ?_, ?_⟩
    · rw [decC_encC_of_continuous hα'.1]
      exact ⟨hα'.1, hα'.2.1, hα'.2.2.1, hα'.2.2.2.1, fun t ht => by
        rw [decC_encC_of_continuousOn hα ht]; exact hα'.2.2.2.2 t ht⟩
    · rw [decC_encC_of_continuous hβ'.1]
      exact ⟨hβ'.1, hβ'.2.1, hβ'.2.2.1, hβ'.2.2.2.1, fun t ht => by
        rw [decC_encC_of_continuousOn hβ ht]; exact hβ'.2.2.2.2 t ht⟩
    · rw [decC_encC_of_continuous hα'.1, decC_encC_of_continuous hβ'.1]
      exact hsub
  · rintro ⟨y, -, -, -, -, h₁, h₂, hsub⟩
    refine ⟨decC y.1, decC y.2, ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, fun t ht => ?_⟩,
      ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, fun t ht => ?_⟩, hsub⟩
    · rw [h₁.2.2.2.2 t ht]; exact decC_encC_of_continuousOn hα ht
    · rw [h₂.2.2.2.2 t ht]; exact decC_encC_of_continuousOn hβ ht

/-- **The coded completion event is universally measurable** (Lusin; analytic sets). -/
theorem uMeasurableSet_hopcCode (a c : ℝ≥0) :
    LQGMetric.UMeasurableSet {p : CCode × CCode | ∃ y, (p, y) ∈ CompRel a c} := by
  have : StandardBorelSpace (CCode × CCode) := StandardBorelSpace.prod
  exact LQGMetric.UMeasurableSet.setOf_exists (measurableSet_compRel a c)

end Theorem15D5

end InteractingSLE
