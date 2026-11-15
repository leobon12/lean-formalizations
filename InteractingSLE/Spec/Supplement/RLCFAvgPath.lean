/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCFAvgSide
import InteractingSLE.Spec.Supplement.RLCFAvgCode
import InteractingSLE.Spec.Supplement.RLCERestart

/-!
# The pathwise reduction of the real completion property at the contact to the per-datum event

Packet PROVE-RLC-F, piece (iv) (the realization of Astra's countable witness construction, R52, at one ω; W5's real
local frame, pp. 535–536).

* `eq_of_noJump_Icc`, `exists_both_sides`, `exists_strips_of_isCompact`, `exists_im_of_prefix_strips`,
  `exists_dyad_avoid`, `isOpen_setOf_fn_eq`: real-line and buffer facts;
* **`chartRealCompletionAt_of_event`**: at an ordinary retained pair with the real joint chart and the untouched word,
  the per-datum countable event `RLC.RealEventC` gives `RLC.ChartRealCompletionAt`. The contact point is not a jump of
  the datum (the event's jump part); all untouched real chart points over the ball lie on the side of the chart seeds
  of the contact (`RLC.chart_side_of_real`) and carry the contact's height (`RLC.IsUntouchedWord` and the strict
  monotonicity of `ψ` at the contact); the visited real points form a compact set covered by rational strips satisfying
  the datum condition; the prefixes, extended to dyadic times, fit a rational strip buffer below the event's collar
  threshold, and the event gives the completability, which passes to the shorter prefixes.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Theorem15D5 Sec2.Assembly Restart Supp7

/-! ### Real-line facts -/

/-- Off its jumps a word is locally constant, so the points of a given height off the jumps form an open set. -/
theorem isOpen_setOf_fn_eq (c : BoundaryWord) (C : ℝ) : IsOpen {x | x ∉ c.jumps ∧ c.fn x = C} := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  have hJ : IsOpen ((c.jumps : Set ℝ)ᶜ) := c.jumps.finite_toSet.isClosed.isOpen_compl
  filter_upwards [c.isPiecewiseConstantBoundaryData x hx.1, hJ.mem_nhds hx.1] with z hz hzJ
  exact ⟨hzJ, hz.trans hx.2⟩

/-- **Piecewise constant data are constant on a closed interval without jump candidates.** -/
theorem eq_of_noJump_Icc {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {s t : ℝ}
    (hst : s ≤ t) (hoff : ∀ r ∈ Icc s t, r ∉ J) : b s = b t := by
  have : PreconnectedSpace (Icc s t) := Subtype.preconnectedSpace isPreconnected_Icc
  have hlc : IsLocallyConstant fun r : Icc s t => b r := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun r => ?_
    exact (continuous_subtype_val.tendsto r).eventually (hb r.1 (hoff r.1 r.2))
  exact hlc.apply_eq_of_preconnectedSpace ⟨s, left_mem_Icc.2 hst⟩ ⟨t, right_mem_Icc.2 hst⟩

/-- **A continuous map injective near `y₀` takes values on both sides of `f y₀` arbitrarily close to `y₀`.** -/
theorem exists_both_sides {f : ℝ → ℝ} {y₀ δ : ℝ} (hδ : 0 < δ) (hf : ContinuousOn f (Ioo (y₀ - δ) (y₀ + δ)))
    (hi : InjOn f (Ioo (y₀ - δ) (y₀ + δ))) :
    ∃ ym yp : ℝ, |ym - y₀| < δ ∧ |yp - y₀| < δ ∧ f ym < f y₀ ∧ f y₀ < f yp := by
  have hm : y₀ - δ / 2 ∈ Ioo (y₀ - δ) (y₀ + δ) := ⟨by linarith, by linarith⟩
  have hp : y₀ + δ / 2 ∈ Ioo (y₀ - δ) (y₀ + δ) := ⟨by linarith, by linarith⟩
  have h0 : y₀ ∈ Ioo (y₀ - δ) (y₀ + δ) := ⟨by linarith, by linarith⟩
  have dm : |y₀ - δ / 2 - y₀| < δ := by
    rw [show y₀ - δ / 2 - y₀ = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)]; linarith
  have dp : |y₀ + δ / 2 - y₀| < δ := by
    rw [show y₀ + δ / 2 - y₀ = δ / 2 by ring, abs_of_pos (half_pos hδ)]; linarith
  rcases hf.strictMonoOn_of_injOn_Ioo (by linarith) hi with hmono | hanti
  · exact ⟨_, _, dm, dp, hmono hm h0 (by linarith), hmono h0 hp (by linarith)⟩
  · exact ⟨_, _, dp, dm, hanti h0 hp (by linarith), hanti hm h0 (by linarith)⟩

/-- **A compact subset of an open subset of `ℝ` is covered by finitely many nondegenerate rational strips whose
closures lie in the open set.** -/
theorem exists_strips_of_isCompact {K G : Set ℝ} (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ S : List (ℚ × ℚ), (∀ ab ∈ S, (ab.1 : ℝ) < ab.2 ∧ Icc (ab.1 : ℝ) ab.2 ⊆ G) ∧ K ⊆ StripSet S := by
  set I : Set (ℚ × ℚ) := {ab | (ab.1 : ℝ) < ab.2 ∧ Icc (ab.1 : ℝ) ab.2 ⊆ G} with hI
  have hcov : K ⊆ ⋃ ab ∈ I, Ioo (ab.1 : ℝ) ab.2 := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hG x (hKG hx)
    obtain ⟨q₁, hq₁, hq₁x⟩ := exists_rat_btwn (show x - ε / 2 < x by linarith)
    obtain ⟨q₂, hxq₂, hq₂⟩ := exists_rat_btwn (show x < x + ε / 2 by linarith)
    refine mem_biUnion (x := (q₁, q₂)) ⟨hq₁x.trans hxq₂, fun z hz => hball ?_⟩ ⟨hq₁x, hxq₂⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  obtain ⟨I', hI'I, hfin, hcov'⟩ := hK.elim_finite_subcover_image (fun _ _ => isOpen_Ioo) hcov
  refine ⟨hfin.toFinset.toList, fun ab hab => ?_, fun x hx => ?_⟩
  · rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hab
    exact hI'I hab
  · obtain ⟨ab, hab, hx'⟩ := mem_iUnion₂.1 (hcov' hx)
    exact ⟨ab, by rw [Finset.mem_toList, Set.Finite.mem_toFinset]; exact hab, hx'.1, hx'.2⟩

/-! ### Fitting a prefix into a strip buffer -/

/-- **A prefix from a real seed whose later real points lie in the open strips fits into a strip buffer** with
seed collar radius `ε` around a centre `ω₀` within `ε/2` of the seed. -/
theorem exists_im_of_prefix_strips {g : ℝ≥0 → ℂ} {s : ℝ≥0} {w₀ ω₀ ε : ℝ} {S : List (ℚ × ℚ)}
    (hg : ContinuousOn g (Iic s)) (h0 : g 0 = w₀) (hε : 0 < ε)
    (hpt : ∀ t : ℝ≥0, 0 < t → t ≤ s → g t ∈ H ∨ ((g t).im = 0 ∧ (g t).re ∈ StripSet S))
    (hω : |w₀ - ω₀| < ε / 2) :
    ∃ ε' : ℚ, 0 < (ε' : ℝ) ∧ ∀ t ≤ s, ‖g t - ω₀‖ < ε ∨ (ε' : ℝ) < (g t).im ∨
      ((g t).im < 2 * ε' ∧ (g t).re ∈ StripSet S) := by
  set T : Set ℝ≥0 := {t | t ∈ Icc 0 s ∧ ε / 2 ≤ ‖g t - w₀‖ ∧ (g t).re ∉ StripSet S} with hT
  have hTc : IsCompact T := by
    refine isCompact_Icc.of_isClosed_subset ?_ fun t ht => ht.1
    have hc : ContinuousOn g (Icc 0 s) := hg.mono fun t ht => ht.2
    have h1 : IsClosed {t | t ∈ Icc 0 s ∧ ε / 2 ≤ ‖g t - w₀‖} :=
      (continuous_norm.comp_continuousOn (hc.sub continuousOn_const)).preimage_isClosed_of_isClosed isClosed_Icc
        (isClosed_Ici (a := ε / 2))
    have h2 : IsClosed {t | t ∈ Icc 0 s ∧ (g t).re ∉ StripSet S} :=
      (Complex.continuous_re.comp_continuousOn hc).preimage_isClosed_of_isClosed isClosed_Icc
        (isOpen_stripSet S).isClosed_compl
    have : T = {t | t ∈ Icc 0 s ∧ ε / 2 ≤ ‖g t - w₀‖} ∩ {t | t ∈ Icc 0 s ∧ (g t).re ∉ StripSet S} := by
      ext t; simp only [hT, mem_ofPred_eq, mem_inter_iff]; tauto
    rw [this]; exact h1.inter h2
  have hTpos : ∀ t ∈ T, 0 < (g t).im := by
    intro t ht
    have ht0 : 0 < t := by
      refine pos_iff_ne_zero.2 fun h => ?_
      have := ht.2.1
      rw [h, h0, sub_self, norm_zero] at this
      linarith
    rcases hpt t ht0 ht.1.2 with h | h
    · exact h
    · exact absurd h.2 ht.2.2
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine ⟨1, by norm_num, fun t ht => ?_⟩
    by_cases hd : ‖g t - w₀‖ < ε / 2
    · left
      have := norm_sub_le_norm_sub_add_norm_sub (g t) (w₀ : ℂ) ω₀
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    · have hS : (g t).re ∈ StripSet S := by
        by_contra hno
        have : t ∈ T := ⟨⟨zero_le, ht⟩, not_lt.1 hd, hno⟩
        rw [hTe] at this; exact this
      by_cases him : (g t).im < 2 * ((1 : ℚ) : ℝ)
      · exact Or.inr (Or.inr ⟨him, hS⟩)
      · exact Or.inr (Or.inl (by push_cast at him ⊢; linarith))
  · obtain ⟨t₀, ht₀, hmin⟩ := hTc.exists_isMinOn hTne
      (Complex.continuous_im.comp_continuousOn (hg.mono fun t ht => ht.1.2))
    obtain ⟨ε', hε'0, hε't⟩ := exists_rat_btwn (hTpos t₀ ht₀)
    refine ⟨ε', hε'0, fun t ht => ?_⟩
    by_cases hd : ‖g t - w₀‖ < ε / 2
    · left
      have := norm_sub_le_norm_sub_add_norm_sub (g t) (w₀ : ℂ) ω₀
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    · by_cases hS : (g t).re ∈ StripSet S
      · by_cases him : (g t).im < 2 * (ε' : ℝ)
        · exact Or.inr (Or.inr ⟨him, hS⟩)
        · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inl (lt_of_lt_of_le hε't (hmin ⟨⟨zero_le, ht⟩, not_lt.1 hd, hS⟩)))

/-- **A continuous path off a closed set at `s < U` stays off it up to a dyadic time after `s`.** -/
theorem exists_dyad_avoid {g : ℝ≥0 → ℂ} {U : ℝ≥0∞} {s : ℝ≥0} {F : Set ℂ} (hF : IsClosed F)
    (hsU : (s : ℝ≥0∞) < U) (hc : ContinuousOn g {t | (t : ℝ≥0∞) ≤ U}) (hs : g s ∉ F) :
    ∃ p : ℕ × ℕ, s ≤ dyad p.1 p.2 ∧ (dyad p.1 p.2 : ℝ≥0∞) < U ∧
      ∀ t : ℝ≥0, s ≤ t → t ≤ dyad p.1 p.2 → g t ∉ F := by
  obtain ⟨V', hV', hVU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsU
  have hsV' : s < V' := by exact_mod_cast hV'
  have hnb : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ U} ∈ 𝓝 s :=
    mem_of_superset (Iio_mem_nhds hsV') fun t ht => (ENNReal.coe_le_coe.2 (le_of_lt ht)).trans hVU.le
  have hca : ContinuousAt g s := (hc s hsU.le).continuousAt hnb
  have hpre : g ⁻¹' Fᶜ ∈ 𝓝 s := hca.preimage_mem_nhds (hF.isOpen_compl.mem_nhds hs)
  obtain ⟨b', hb', hsub⟩ := exists_Ico_subset_of_mem_nhds hpre ⟨V', hsV'⟩
  obtain ⟨q, ⟨⟨n, k⟩, rfl⟩, hsq, hqb⟩ := Supp9D.exists_dyadSet_btwn (lt_min hb' hsV')
  refine ⟨(n, k), hsq.le, ?_, fun t hst htq => hsub ⟨hst, lt_of_le_of_lt htq (lt_of_lt_of_le hqb (min_le_left _ _))⟩⟩
  exact lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (lt_of_lt_of_le hqb (min_le_right _ _))) hVU.le

/-! ### The pathwise reduction -/

/-- **The real completion property at the contact, pathwise, from the per-datum event** (Astra's Prop. 5.2 realized
at one ω; W5's real local frame). At an ordinary retained pair with the real joint chart `ψ` (chart seeds `W > 0` and
`0`), the untouched word, chart paths continuous and in `ℍ̄` before their lifetimes, the countable-form per-datum event
`RealEventC` of the datum implies `ChartRealCompletionAt`: the common real point over the contact is not a jump of the
datum (jump part); the untouched real chart points over the ball lie on one side of the chart seeds, the side of the
contact (`chart_side_of_real`), and carry the height of the contact (`IsUntouchedWord` with the local monotonicity of
`ψ` at the contact); the visited real points form a compact set covered by rational strips satisfying the datum
condition; the prefixes, slightly extended to dyadic times, fit a rational strip buffer below the collar threshold. -/
theorem chartRealCompletionAt_of_event {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {u r : ℝ≥0}
    {Γ₁ Γ₂ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞} {ψ : ℂ → ℂ} {b : ℝ → ℝ} {jumps : Finset ℝ} {c : BoundaryWord} {W : ℝ}
    (hc₁ : ContinuousOn η₁ {x | (x : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ {y | (y : ℝ≥0∞) ≤ ζ₂})
    (hi₁ : InjOn η₁ {x | (x : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {y | (y : ℝ≥0∞) ≤ ζ₂})
    (hm₁ : ∀ x : ℝ≥0, (x : ℝ≥0∞) ≤ ζ₁ → 0 ≤ (η₁ x).im) (hm₂ : ∀ y : ℝ≥0, (y : ℝ≥0∞) ≤ ζ₂ → 0 ≤ (η₂ y).im)
    (h01 : (η₁ 0).im = 0) (h02 : (η₂ 0).im = 0)
    (hord : IsOrdinaryRetainedPair η₁ ζ₁ u η₂ ζ₂ r) (hJ : IsRealJointChart η₁ ζ₁ u η₂ ζ₂ r Γ₁ Γ₂ U₁ U₂ ψ)
    (hΓ₁0 : Γ₁ 0 = W) (hΓ₂0 : Γ₂ 0 = 0)
    (hk₁ : ContinuousOn Γ₁ {t | (t : ℝ≥0∞) ≤ U₁}) (hk₂ : ContinuousOn Γ₂ {t | (t : ℝ≥0∞) ≤ U₂})
    (hH₁ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U₁ → Γ₁ t ∈ Hbar) (hH₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U₂ → Γ₂ t ∈ Hbar)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (huw : IsUntouchedWord b jumps (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) ψ c)
    (hE : RealEventC c W (encC Γ₁) U₁ (encC Γ₂) U₂) :
    ChartRealCompletionAt jumps (η₁ 0).re (η₂ 0).re (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) ψ Γ₁ U₁ Γ₂ U₂ := by
  obtain ⟨hbij, hoff, hψc, ⟨M, hψM⟩, hψ0, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁⟩,
    ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂⟩, hinj⟩ := hJ
  obtain ⟨hJF, hSE'⟩ := hE
  set A := η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r with hAdef
  have hle₁ : ∀ x : ℝ≥0, x ≤ u → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => (ENNReal.coe_le_coe.2 hx).trans (le_of_lt hord.1)
  have hle₂ : ∀ y : ℝ≥0, y ≤ r → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => (ENNReal.coe_le_coe.2 hy).trans (le_of_lt hord.2.1)
  have hA : IsClosed A :=
    isClosed_prefixUnion (hc₁.mono fun x hx => hle₁ x hx.2) (hc₂.mono fun y hy => hle₂ y hy.2)
  have hDH : activeDomain η₁ u η₂ r ⊆ H := fun z hz => hz.1.1
  have hDA : ∀ z ∈ activeDomain η₁ u η₂ r, z ∉ A := fun z hz => hz.1.2
  have hc₁0 : c₁ 0 = u := clock_zero hord.1.le hmono₁ himg₁
  have hψW : ψ W = η₁ u := by rw [← hΓ₁0, ← (hpth₁ 0 (by simp)).1, hc₁0]
  have hψ0' : ψ ((0 : ℝ) : ℂ) = η₂ r := by rw [Complex.ofReal_zero]; exact hψ0
  have hWA : ψ W ∈ A := by rw [hψW]; exact Or.inl ⟨u, ⟨zero_le, le_rfl⟩, rfl⟩
  have h0A : ψ ((0 : ℝ) : ℂ) ∈ A := by rw [hψ0']; exact Or.inr ⟨r, ⟨zero_le, le_rfl⟩, rfl⟩
  intro p ρ hρ hjump hρ1 hρ2 s₁ s₂ hs₁ hs₂ _ _ hpre₁ hpre₂ hcom
  obtain ⟨t₁, t₂, ht₁0, ht₁s, ht₂0, ht₂s, hcom, hψp⟩ := hcom
  -- the untouched real chart points over the ball
  set E : Set ℝ := {y | ψ y ∈ ball (p : ℂ) ρ ∧ ψ y ∉ A} with hEdef
  have hψR : Continuous fun y : ℝ => ψ y :=
    hψc.comp_continuous continuous_ofReal fun y => show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hEo : IsOpen E := (isOpen_ball.inter hA.isOpen_compl).preimage hψR
  have hEr : ∀ y ∈ E, (ψ y).im = 0 := fun y hy => im_eq_zero_of_real hA hbij hoff hψc y hy.2
  have hEre : ∀ y ∈ E, ψ y = (((ψ y).re : ℝ) : ℂ) := fun y hy => Complex.ext (by simp) (by simp [hEr y hy])
  have hEi : ∀ y ∈ E, ∀ y' ∈ E, (ψ y).re = (ψ y').re → y = y' := fun y hy y' hy' he =>
    hinj y y' (by rw [hEre y hy, hEre y' hy', he]) (hEr y hy) hy.2
  have hEball : ∀ y ∈ E, |(ψ y).re - p| < ρ := fun y hy => by
    have h1 := hy.1
    rw [mem_ball, Complex.dist_eq] at h1
    have := Complex.abs_re_le_norm (ψ y - p)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  -- the real points of the prefixes after their seeds lie over the ball
  have hvis : ∀ (g : ℝ≥0 → ℂ) (U : ℝ≥0∞) (s : ℝ≥0), (s : ℝ≥0∞) < U → (∀ t : ℝ≥0, (t : ℝ≥0∞) < U → g t ∈ Hbar) →
      (∀ t : ℝ≥0, 0 < t → t ≤ s → ψ (g t) ∈ ball (p : ℂ) ρ ∧ ψ (g t) ∉ A) →
      ∀ t : ℝ≥0, 0 < t → t ≤ s → g t ∈ H ∨ ((g t).im = 0 ∧ (g t).re ∈ E) := by
    intro g U s hsU hgH hpre t ht hts
    rcases (show (0 : ℝ) ≤ (g t).im from hgH t ((ENNReal.coe_le_coe.2 hts).trans_lt hsU)).lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.symm, ?_⟩
      have hg : g t = (((g t).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← h])
      show ψ (((g t).re : ℝ) : ℂ) ∈ ball (p : ℂ) ρ ∧ ψ (((g t).re : ℝ) : ℂ) ∉ A
      rw [← hg]; exact hpre t ht hts
  have hvis₁ := hvis Γ₁ U₁ s₁ hs₁ hH₁ hpre₁
  have hvis₂ := hvis Γ₂ U₂ s₂ hs₂ hH₂ hpre₂
  -- the common real point over the contact
  have hreal₁ : (Γ₁ t₁).im = 0 := by
    rcases hvis₁ t₁ ht₁0 ht₁s with h | h
    · have h' : (0 : ℝ) < (ψ (Γ₁ t₁)).im := hDH (hbij.mapsTo h)
      rw [hψp, Complex.ofReal_im] at h'
      exact absurd h' (lt_irrefl 0)
    · exact h.1
  set yp := (Γ₁ t₁).re with hypdef
  have hΓyp : Γ₁ t₁ = (yp : ℂ) := Complex.ext (by simp [hypdef]) (by simp [hreal₁])
  have hypE : yp ∈ E := by
    rcases hvis₁ t₁ ht₁0 ht₁s with h | h
    · exact absurd hreal₁ (ne_of_gt h)
    · exact h.2
  have hψyp : ψ yp = (p : ℂ) := by rw [← hΓyp]; exact hψp
  have hfyp : (ψ yp).re = p := by rw [hψyp, Complex.ofReal_re]
  -- the side of the chart seeds
  have hx₁p : p ≠ (η₁ 0).re := fun h => by rw [h, sub_self, abs_zero] at hρ1; linarith
  have hx₂p : p ≠ (η₂ 0).re := fun h => by rw [h, sub_self, abs_zero] at hρ2; linarith
  have hside₁ : ∀ y ∈ E, ((η₁ 0).re < (ψ y).re → W < y) ∧ ((ψ y).re < (η₁ 0).re → y < W) := fun y hy =>
    chart_side_of_real (η := η₁) (u := u) (w₀ := W) (D := activeDomain η₁ u η₂ r) (M := M)
      (hc₁.mono fun x hx => hle₁ x hx.2) (hi₁.mono fun x hx => hle₁ x hx.2) (fun t ht => hm₁ t (hle₁ t ht)) h01
      hDH (fun z hz hzA => hDA z hz (Or.inl hzA)) hbij.mapsTo hbij.injOn hψc hψM hψW
      (fun h => hy.2 (Or.inl h)) (hEr y hy)
  have hside₂ : ∀ y ∈ E, ((η₂ 0).re < (ψ y).re → 0 < y) ∧ ((ψ y).re < (η₂ 0).re → y < 0) := fun y hy =>
    chart_side_of_real (η := η₂) (u := r) (w₀ := 0) (D := activeDomain η₁ u η₂ r) (M := M)
      (hc₂.mono fun x hx => hle₂ x hx.2) (hi₂.mono fun x hx => hle₂ x hx.2) (fun t ht => hm₂ t (hle₂ t ht)) h02
      hDH (fun z hz hzA => hDA z hz (Or.inr hzA)) hbij.mapsTo hbij.injOn hψc hψM hψ0'
      (fun h => hy.2 (Or.inr h)) (hEr y hy)
  have hreg : (∀ y ∈ E, y < 0) ∨ (∀ y ∈ E, 0 < y ∧ y < W) ∨ (∀ y ∈ E, W < y) := by
    rcases lt_or_gt_of_ne hx₁p with h1 | h1
    · rw [abs_of_pos (sub_pos.2 h1)] at hρ1
      rcases lt_or_gt_of_ne hx₂p with h2 | h2
      · rw [abs_of_pos (sub_pos.2 h2)] at hρ2
        refine Or.inl fun y hy => (hside₂ y hy).2 ?_
        have := hEball y hy; rw [abs_lt] at this; linarith
      · rw [abs_of_neg (sub_neg.2 h2)] at hρ2
        refine Or.inr (Or.inl fun y hy => ⟨(hside₂ y hy).1 ?_, (hside₁ y hy).2 ?_⟩)
        · have := hEball y hy; rw [abs_lt] at this; linarith
        · have := hEball y hy; rw [abs_lt] at this; linarith
    · rw [abs_of_neg (sub_neg.2 h1)] at hρ1
      refine Or.inr (Or.inr fun y hy => (hside₁ y hy).1 ?_)
      have := hEball y hy; rw [abs_lt] at this; linarith
  -- the contact is not a jump of the datum
  have hypW : yp ≠ W := fun h => hypE.2 (by rw [h]; exact hWA)
  obtain ⟨pp, hpp1, hpp2, -⟩ := exists_dyad_avoid (F := (∅ : Set ℂ)) isClosed_empty hs₁ hk₁ (notMem_empty _)
  have hcs : ContinuousOn Γ₁ (Iic (dyad pp.1 pp.2)) :=
    hk₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hpp2.le
  have hypJ : yp ∉ c.jumps := by
    intro hJ'
    obtain ⟨i, hi, hie⟩ := BoundaryWord.mem_jumps.1 hJ'
    have hav := hJF i hi (by rw [hie]; exact hypW) pp hpp2
    rw [avoidPtC_iff, avoidC_encC_iff hcs isClosed_singleton (singleton_nonempty _)] at hav
    exact hav t₁ ht₁0 (ht₁s.trans hpp1) (by rw [hΓyp, hie]; rfl)
  -- every untouched real chart point over the ball carries the height of the contact
  set C := c.fn yp with hCdef
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1 (isOpen_setOf_fn_eq c C) yp ⟨hypJ, rfl⟩
  obtain ⟨δ', hδ', hδ'b⟩ := Metric.isOpen_iff.1 hEo yp hypE
  have hsubI : ∀ z : ℝ, |z - yp| < min δ δ' → z ∈ E ∧ z ∉ c.jumps ∧ c.fn z = C := fun z hz => by
    have h1 : dist z yp < min δ δ' := by rw [Real.dist_eq]; exact hz
    exact ⟨hδ'b (lt_of_lt_of_le h1 (min_le_right _ _)), hδb (lt_of_lt_of_le h1 (min_le_left _ _))⟩
  have hIsub : ∀ z ∈ Ioo (yp - min δ δ') (yp + min δ δ'), |z - yp| < min δ δ' := fun z hz => by
    rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]
  have hfc : ContinuousOn (fun y : ℝ => (ψ y).re) (Ioo (yp - min δ δ') (yp + min δ δ')) :=
    (Complex.continuous_re.comp hψR).continuousOn
  have hfi : InjOn (fun y : ℝ => (ψ y).re) (Ioo (yp - min δ δ') (yp + min δ δ')) := fun y hy y' hy' he =>
    hEi y (hsubI y (hIsub y hy)).1 y' (hsubI y' (hIsub y' hy')).1 he
  obtain ⟨ym, ypl, hym, hypl, hfm, hfp⟩ := exists_both_sides (lt_min hδ hδ') hfc hfi
  simp only [hfyp] at hfm hfp
  obtain ⟨hymE, -, hymC⟩ := hsubI ym hym
  obtain ⟨hyplE, -, hyplC⟩ := hsubI ypl hypl
  have hnoJ : ∀ z : ℝ, |z - p| < ρ → z ≠ p → z ∉ jumps := hjump
  have hbm : b (ψ ym).re = C := by
    rw [← hymC, (huw ym (hEr ym hymE) hymE.2 (hnoJ _ (hEball ym hymE) (ne_of_lt hfm))).2]
  have hbp : b (ψ ypl).re = C := by
    rw [← hyplC, (huw ypl (hEr ypl hyplE) hyplE.2 (hnoJ _ (hEball ypl hyplE) (ne_of_gt hfp))).2]
  have hconst : ∀ z z' : ℝ, |z - p| < ρ → |z' - p| < ρ → (z < p ∧ z' < p ∨ p < z ∧ p < z') → b z = b z' := by
    intro z z' hz hz' hs
    rw [abs_lt] at hz hz'
    have key : ∀ x x' : ℝ, x ≤ x' → -ρ < x - p → x' - p < ρ → (x < p ∧ x' < p ∨ p < x ∧ p < x') → b x = b x' :=
      fun x x' hxx' h1 h2 hs' => eq_of_noJump_Icc hb hxx' fun w hw => hnoJ w (by
        rw [abs_lt]; constructor <;> linarith [hw.1, hw.2]) (by
        rcases hs' with ⟨_, h⟩ | ⟨h, _⟩
        · exact ne_of_lt (lt_of_le_of_lt hw.2 h)
        · exact ne_of_gt (lt_of_lt_of_le h hw.1))
    rcases le_total z z' with hle | hle
    · exact key z z' hle hz.1 hz'.2 hs
    · exact (key z' z hle hz'.1 hz.2 (hs.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩))).symm
  have hheight : ∀ y ∈ E, y ∉ c.jumps ∧ c.fn y = C := by
    intro y hy
    rcases lt_trichotomy (ψ y).re p with h | h | h
    · have hu := huw y (hEr y hy) hy.2 (hnoJ _ (hEball y hy) (ne_of_lt h))
      exact ⟨hu.1, hu.2.trans ((hconst _ _ (hEball y hy) (hEball ym hymE) (Or.inl ⟨h, hfm⟩)).trans hbm)⟩
    · have := hEi y hy yp hypE (by rw [h, hfyp])
      rw [this]; exact ⟨hypJ, rfl⟩
    · have hu := huw y (hEr y hy) hy.2 (hnoJ _ (hEball y hy) (ne_of_gt h))
      exact ⟨hu.1, hu.2.trans ((hconst _ _ (hEball y hy) (hEball ypl hyplE) (Or.inr ⟨h, hfp⟩)).trans hbp)⟩
  -- near the chart seeds no real chart point is untouched
  have hnear : ∀ w₀ : ℝ, ψ w₀ ∈ H → ∃ δ₀ > 0, ∀ y : ℝ, |y - w₀| < δ₀ → y ∉ E := by
    intro w₀ hw₀
    have hcw : ContinuousAt (fun y : ℝ => (ψ y).im) w₀ := (Complex.continuous_im.comp hψR).continuousAt
    obtain ⟨δ₀, hδ₀, hball⟩ := Metric.continuousAt_iff.1 hcw ((ψ w₀).im) hw₀
    refine ⟨δ₀, hδ₀, fun y hy hyE => ?_⟩
    have := hball (by rw [Real.dist_eq]; exact hy)
    rw [Real.dist_eq, hEr y hyE, zero_sub, abs_neg, abs_of_pos (show (0 : ℝ) < (ψ w₀).im from hw₀)] at this
    exact lt_irrefl _ this
  -- the visited real points form a compact subset of `E`
  have hKex : ∀ (g : ℝ≥0 → ℂ) (U : ℝ≥0∞) (s : ℝ≥0) (w₀ : ℝ), g 0 = w₀ → ψ w₀ ∈ H → (s : ℝ≥0∞) < U →
      ContinuousOn g {t | (t : ℝ≥0∞) ≤ U} → (∀ t : ℝ≥0, 0 < t → t ≤ s → g t ∈ H ∨ ((g t).im = 0 ∧ (g t).re ∈ E)) →
      ∃ K : Set ℝ, IsCompact K ∧ K ⊆ E ∧ ∀ t : ℝ≥0, 0 < t → t ≤ s → (g t).im = 0 → (g t).re ∈ K := by
    intro g U s w₀ hg0 hw₀ hsU hgc hpt
    obtain ⟨δ₀, hδ₀, hfar⟩ := hnear w₀ hw₀
    have hcs : ContinuousOn g (Iic s) := hgc.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hsU.le
    obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.continuousWithinAt_iff.1 (hcs 0 (show (0 : ℝ≥0) ≤ s from zero_le)) δ₀ hδ₀
    set a : ℝ≥0 := ⟨δ₁ / 2, by positivity⟩ with ha
    set T : Set ℝ≥0 := {t | t ∈ Icc a s ∧ (g t).im = 0} with hT
    have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset
      ((Complex.continuous_im.comp_continuousOn (hcs.mono fun t ht => ht.2)).preimage_isClosed_of_isClosed
        isClosed_Icc (isClosed_singleton (x := (0 : ℝ)))) fun t ht => ht.1
    have hlow : ∀ t : ℝ≥0, 0 < t → t ≤ s → (g t).im = 0 → a ≤ t := by
      intro t ht hts him
      by_contra hlt
      rw [not_le] at hlt
      have hd : dist t 0 < δ₁ := by
        rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]
        have : (t : ℝ) < δ₁ / 2 := hlt
        linarith
      have h1 := hδ₁b (show t ∈ Iic s from hts) hd
      rw [dist_eq_norm, hg0] at h1
      have h2 := Complex.abs_re_le_norm (g t - w₀)
      simp only [Complex.sub_re, Complex.ofReal_re] at h2
      rcases hpt t ht hts with h | h
      · exact absurd him (ne_of_gt h)
      · exact hfar _ (lt_of_le_of_lt h2 h1) h.2
    refine ⟨(fun t => (g t).re) '' T, hTc.image_of_continuousOn
      (Complex.continuous_re.comp_continuousOn (hcs.mono fun t ht => ht.1.2)), ?_, fun t ht hts him =>
        ⟨t, ⟨⟨hlow t ht hts him, hts⟩, him⟩, rfl⟩⟩
    rintro _ ⟨t, ⟨⟨hat, hts⟩, him⟩, rfl⟩
    have ht0 : 0 < t := lt_of_lt_of_le (show (0 : ℝ≥0) < a from show (0 : ℝ) < δ₁ / 2 by positivity) hat
    rcases hpt t ht0 hts with h | h
    · exact absurd him (ne_of_gt h)
    · exact h.2
  have hW₀H : ψ W ∈ H := by rw [hψW]; exact hord.2.2.1
  have h0H : ψ ((0 : ℝ) : ℂ) ∈ H := by rw [hψ0']; exact hord.2.2.2.1
  obtain ⟨K₁, hK₁c, hK₁E, hK₁⟩ := hKex Γ₁ U₁ s₁ W hΓ₁0 hW₀H hs₁ hk₁ hvis₁
  obtain ⟨K₂, hK₂c, hK₂E, hK₂⟩ := hKex Γ₂ U₂ s₂ 0 (by rw [hΓ₂0]; simp) h0H hs₂ hk₂ hvis₂
  -- rational strips covering the visited real points inside `E`
  obtain ⟨S, hS, hKS⟩ := exists_strips_of_isCompact (hK₁c.union hK₂c) hEo (union_subset hK₁E hK₂E)
  have hSE : ∀ ab ∈ S, ∀ x ∈ Icc (ab.1 : ℝ) ab.2, x ∈ E := fun ab hab x hx => (hS ab hab).2 hx
  have hSC : StripCond c W S := by
    refine ⟨?_, ?_, ?_⟩
    · rcases hreg with h | h | h
      · exact Or.inl fun ab hab => h _ (hSE ab hab _ (right_mem_Icc.2 (hS ab hab).1.le))
      · exact Or.inr (Or.inl fun ab hab => ⟨(h _ (hSE ab hab _ (left_mem_Icc.2 (hS ab hab).1.le))).1,
          (h _ (hSE ab hab _ (right_mem_Icc.2 (hS ab hab).1.le))).2⟩)
      · exact Or.inr (Or.inr fun ab hab => h _ (hSE ab hab _ (left_mem_Icc.2 (hS ab hab).1.le)))
    · intro ab hab i hi
      by_contra hno
      rw [not_or, not_lt, not_lt] at hno
      exact (hheight _ (hSE ab hab _ ⟨hno.1, hno.2⟩)).1 (BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩)
    · intro ab hab ab' hab'
      rw [(hheight _ (hSE ab hab _ (left_mem_Icc.2 (hS ab hab).1.le))).2,
        (hheight _ (hSE ab' hab' _ (left_mem_Icc.2 (hS ab' hab').1.le))).2]
  obtain ⟨k, hk⟩ := hSE' S hSC
  -- extending both prefixes to dyadic times with the same real points
  have hext : ∀ (g : ℝ≥0 → ℂ) (U : ℝ≥0∞) (s : ℝ≥0) (K : Set ℝ), (s : ℝ≥0∞) < U → 0 < s →
      ContinuousOn g {t | (t : ℝ≥0∞) ≤ U} → (∀ t : ℝ≥0, (t : ℝ≥0∞) < U → g t ∈ Hbar) → K ⊆ StripSet S →
      (∀ t : ℝ≥0, 0 < t → t ≤ s → (g t).im = 0 → (g t).re ∈ K) →
      ∃ q : ℕ × ℕ, s ≤ dyad q.1 q.2 ∧ (dyad q.1 q.2 : ℝ≥0∞) < U ∧
        ∀ t : ℝ≥0, 0 < t → t ≤ dyad q.1 q.2 → g t ∈ H ∨ ((g t).im = 0 ∧ (g t).re ∈ StripSet S) := by
    intro g U s K hsU hs0 hgc hgH hKS' hK
    have hgs : g s ∉ offStrips S := fun h => h.2 (hKS' (hK s hs0 le_rfl h.1))
    obtain ⟨q, hq1, hq2, hq3⟩ := exists_dyad_avoid (isClosed_offStrips S) hsU hgc hgs
    refine ⟨q, hq1, hq2, fun t ht htq => ?_⟩
    rcases (show (0 : ℝ) ≤ (g t).im from hgH t ((ENNReal.coe_le_coe.2 htq).trans_lt hq2)).lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.symm, ?_⟩
      rcases le_or_gt t s with hts | hts
      · exact hKS' (hK t ht hts h.symm)
      · by_contra hno
        exact hq3 t hts.le htq ⟨h.symm, hno⟩
  obtain ⟨p₁, hp₁s, hp₁U, pt₁⟩ := hext Γ₁ U₁ s₁ K₁ hs₁ (lt_of_lt_of_le ht₁0 ht₁s) hk₁ hH₁
    (fun x hx => hKS (Or.inl hx)) fun t ht hts him => hK₁ t ht hts him
  obtain ⟨p₂, hp₂s, hp₂U, pt₂⟩ := hext Γ₂ U₂ s₂ K₂ hs₂ (lt_of_lt_of_le ht₂0 ht₂s) hk₂ hH₂
    (fun x hx => hKS (Or.inr hx)) fun t ht hts him => hK₂ t ht hts him
  have cs₁ : ContinuousOn Γ₁ (Iic (dyad p₁.1 p₁.2)) :=
    hk₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hp₁U.le
  have cs₂ : ContinuousOn Γ₂ (Iic (dyad p₂.1 p₂.2)) :=
    hk₂.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hp₂U.le
  -- a rational strip buffer below the collar threshold
  obtain ⟨ε, hε0, hεk⟩ := exists_rat_btwn (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
  obtain ⟨ω, hω1, hω2⟩ := exists_rat_btwn (show W - (ε : ℝ) / 2 < W + (ε : ℝ) / 2 by linarith)
  have hWω : |W - ω| < (ε : ℝ) / 2 := by rw [abs_lt]; constructor <;> linarith
  obtain ⟨e₁, he₁, hfit₁⟩ := exists_im_of_prefix_strips cs₁ hΓ₁0 hε0 pt₁ hWω
  obtain ⟨e₂, he₂, hfit₂⟩ := exists_im_of_prefix_strips (w₀ := 0) (ω₀ := 0) cs₂
    (by rw [hΓ₂0, Complex.ofReal_zero]) hε0 pt₂ (by rw [sub_zero, abs_zero]; exact half_pos hε0)
  obtain ⟨R₁, hR₁⟩ := exists_rat_norm_lt_of_prefix cs₁
  obtain ⟨R₂, hR₂⟩ := exists_rat_norm_lt_of_prefix cs₂
  set e : ℚ := min e₁ e₂ with he
  set R : ℚ := max R₁ R₂ with hR
  have he0 : (0 : ℝ) < e := by rw [he]; push_cast; exact lt_min he₁ he₂
  have he₁' : (e : ℝ) ≤ e₁ := by rw [he]; push_cast; exact min_le_left _ _
  have he₂' : (e : ℝ) ≤ e₂ := by rw [he]; push_cast; exact min_le_right _ _
  have hfit : ∀ (g : ℝ≥0 → ℂ) (s : ℝ≥0) (e' : ℚ) (R' : ℚ), (e : ℝ) ≤ e' → (R' : ℝ) ≤ R →
      (∀ t ≤ s, ‖g t‖ < R') → (∀ t ≤ s, (‖g t‖ < ε ∨ ‖g t - ω‖ < ε) ∨ (e' : ℝ) < (g t).im ∨
        ((g t).im < 2 * e' ∧ (g t).re ∈ StripSet S)) → ∀ t ≤ s, g t ∈ stripBuffer S e ε R ω := by
    intro g s e' R' hee' hRR' hnorm hf t ht
    refine ⟨lt_of_lt_of_le (hnorm t ht) hRR', ?_⟩
    rcases hf t ht with (h | h) | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (lt_of_le_of_lt hee' h)
    · by_cases him : (g t).im < 2 * (e : ℝ)
      · exact Or.inr (Or.inr (Or.inr ⟨him, h.2⟩))
      · exact Or.inl (by linarith)
  have mem₁ := hfit Γ₁ _ e₁ R₁ he₁' (by rw [hR]; push_cast; exact le_max_left _ _) hR₁
    fun t ht => (hfit₁ t ht).imp_left Or.inr
  have mem₂ := hfit Γ₂ _ e₂ R₂ he₂' (by rw [hR]; push_cast; exact le_max_right _ _) hR₂
    fun t ht => (hfit₂ t ht).imp_left fun h => Or.inl (by simpa using h)
  -- the countable hypotheses of the event
  have hav : ∀ (g : ℝ≥0 → ℂ) (s : ℝ≥0), ContinuousOn g (Iic s) →
      (∀ t : ℝ≥0, 0 < t → t ≤ s → g t ∈ H ∨ ((g t).im = 0 ∧ (g t).re ∈ StripSet S)) →
      AvoidC (encC g) s (offStrips S) := by
    intro g s hgs hpt
    refine (avoidC_encC_iff hgs (isClosed_offStrips S) (offStrips_nonempty S)).2 fun t ht hts hF => ?_
    rcases hpt t ht hts with h | h
    · exact absurd hF.1 (ne_of_gt h)
    · exact hF.2 h.2
  have hin : ∀ (g : ℝ≥0 → ℂ) (s : ℝ≥0), ContinuousOn g (Iic s) → (∀ t ≤ s, g t ∈ stripBuffer S e ε R ω) →
      InC (encC g) s (stripBuffer S e ε R ω)ᶜ := fun g s hgs hm =>
    (inC_encC_iff hgs (isClosed_compl_stripBuffer _ _ _ _ _) (compl_stripBuffer_nonempty _ _ _ _ _)).2
      fun t ht h => h (hm t ht)
  have hcomΓ : Γ₂ t₂ = (yp : ℂ) := by rw [← hcom, hΓyp]
  obtain ⟨y, hy⟩ := hk e ε R ω he0 hε0 hεk (lt_trans hWω (half_lt_self hε0)) p₁ p₂ hp₁U hp₂U
    (hin Γ₁ _ cs₁ mem₁) (hin Γ₂ _ cs₂ mem₂) (hav Γ₁ _ cs₁ pt₁) (hav Γ₂ _ cs₂ pt₂)
    ((hitC_encC_iff cs₁ isClosed_realAxis realAxis_nonempty).2 ⟨t₁, ht₁0, ht₁s.trans hp₁s, hreal₁⟩)
    ((hitC_encC_iff cs₂ isClosed_realAxis realAxis_nonempty).2 ⟨t₂, ht₂0, ht₂s.trans hp₂s, by
      show (Γ₂ t₂).im = 0; rw [hcomΓ, Complex.ofReal_im]⟩)
    ((commonC_encC_iff cs₁ cs₂).2 ⟨t₁, t₂, ht₁0, ht₁s.trans hp₁s, ht₂0, ht₂s.trans hp₂s, hcom⟩)
  exact ((isChartCompletable_iff_exists cs₁ cs₂).2 ⟨y, hy⟩).mono hp₁s hp₂s

end RLC

end InteractingSLE
