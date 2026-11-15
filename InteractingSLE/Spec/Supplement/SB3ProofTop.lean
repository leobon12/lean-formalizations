/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB3Top

/-!
# Lemma SB3's final certificate (deterministic)

Packet PROVE-T14-SB3. Proof of `SB.SB3TopologyStatement` (supplement p. 634, `source/spec/p625-671.md` L157: "A point
of `b` on its open right side would give a finite crossing or initial-germ certificate between a finite upper prefix
and an interior-in-parameter compact subarc of `B`. In a small Jordan collar of those retained subarcs any proper
completion of the upper prefix has the same local sides [...] The lower subarc then has points on both sides of that
completion, contradicting S1.").

* `exists_leftCollar` — **a left collar avoiding a closed set**: for a proper curve `γ₁` from a real seed and a
  closed set `F` missing the closed arc `seedLine γ₁ '' [−1, A]` (the lower seed ray segment followed by `γ₁([0, A])`),
  a preconnected set off the closed curve and off `F` which contains the left side of `γ₁` near every interior point
  of that arc. This is the thin annular sector of the side principle `Supp9B.eventually_mem_leftSide_of_eqOn` (the
  same Schoenflies straightening), with the tail of the second curve replaced by an arbitrary closed set.
* `rightSideOf_range_subset_rightSide` — the frozen `rightSideOf` of a proper curve from `0` lies in its right side.
* `exists_crossing_certificate` — **the crossing certificate**: if a proper curve `η'` from a real seed `u ≤ 0`
  reaches the right side of a proper curve `γ` from `0` at time `t`, then at some earlier time `t₁ < t` the point
  `η'(t₁)` is a limit of points of `γ` on the left side of `η'`. (Otherwise the left collar of `η'([0, t])` avoids
  `γ`, and joins the left side of `γ` near the seed to its right side near `η'(t)`.)
* `sb3TopologyStatement` — the statement: the certificate, the boundedness of `γ` near it, S1 for a long enough
  prefix of `γ`, and the side principle for two completions of the same upper prefix;
* `sb3Statement_of_param_induction` — Lemma SB3 from `GW1ParamStatement` and `SB3InductionStatement` alone.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

open Supp9B

/-! ### A left collar avoiding a closed set -/

/-- **A left collar avoiding a closed set.** Let `γ₁` be a proper curve from a real seed, `0 < A`, and `F` a closed
set missing the closed arc `seedLine γ₁ '' [−1, A]`. There is a preconnected set `S` off the closed curve and off `F`
which contains the left side of `γ₁` near every point `seedLine γ₁ τ`, `−1 < τ < A`. -/
theorem exists_leftCollar {γ₁ : ℝ≥0 → ℂ} {A : ℝ} (h₁ : IsProperCurve γ₁) (h0 : (γ₁ 0).im = 0)
    {F : Set ℂ} (hF : IsClosed F) (hFℓ : ∀ τ ∈ Icc (-1 : ℝ) A, seedLine γ₁ τ ∉ F) :
    ∃ S : Set ℂ, IsPreconnected S ∧ S ⊆ (seedRayClosure γ₁)ᶜ ∧ Disjoint S F ∧
      ∀ τ ∈ Ioo (-1 : ℝ) A, ∀ᶠ w in 𝓝 (seedLine γ₁ τ), w ∈ leftSide γ₁ → w ∈ S := by
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
  -- the arc in straightened coordinates
  set C := (fun t => Ψ (ℓ t)) '' Icc (-1) A with hC
  have hCcpt : IsCompact C := isCompact_Icc.image hΨℓ
  have hCconn : IsPreconnected C := isPreconnected_Icc.image _ hΨℓ.continuousOn
  -- the rest of the closed curve
  set Fb := h.symm '' (inv p '' (ℓ '' (Iic (-1) ∪ Ici A)) ∪ {0}) with hFb
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
      by_cases ht : t ∈ Icc (-1) A
      · exact Or.inl ⟨t, ht, hy'.symm⟩
      · refine Or.inr ⟨inv p (ℓ t), Or.inl ⟨ℓ t, ⟨t, ?_, rfl⟩, rfl⟩, hy'.symm⟩
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with ht | ht
        · exact Or.inl ht.le
        · exact Or.inr ht.le
    · exact Or.inr ⟨0, Or.inr rfl, by rw [← mem_singleton_iff.1 hz0, Homeomorph.symm_apply_apply]⟩
  have hnotFb : ∀ t ∈ Ioo (-1 : ℝ) A, Ψ (ℓ t) ∉ Fb := by
    rintro t ht ⟨w, hw | hw, hwt⟩
    · obtain ⟨_, ⟨t', ht', rfl⟩, rfl⟩ := hw
      have := seedLine_injective h₁ h0 (hΨinj _ _ hwt)
      rw [this] at ht'
      rcases ht' with h' | h'
      · exact absurd (mem_Iic.1 h') (not_le.2 ht.1)
      · exact absurd (mem_Ici.1 h') (not_le.2 ht.2)
    · rw [mem_singleton_iff.1 hw] at hwt
      exact inv_apply_ne_zero (hℓp t) (h.symm.injective (hwt.symm.trans (by simp)))
  -- the obstacle in straightened coordinates
  set Fa := h.symm '' (inv p '' F ∪ {0}) with hFa
  have hFac : IsClosed Fa := by
    rw [hFa, h.image_symm]
    exact (isClosed_inv_image_union hF).preimage h.continuous
  have hCFa : C ⊆ Faᶜ := by
    rintro _ ⟨t, ht, rfl⟩ ⟨w, hw | hw, hwt⟩
    · obtain ⟨f, hf, rfl⟩ := hw
      have heq : f = ℓ t := hΨinj _ _ hwt
      exact hFℓ t ht (heq ▸ hf)
    · rw [mem_singleton_iff.1 hw] at hwt
      exact inv_apply_ne_zero (hℓp t) (h.symm.injective (hwt.symm.trans (by simp)))
  have hCs : C ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨t, -, rfl⟩; exact hΨs _ (seedLine_mem h0 t)
  -- a thin annular sector inside the disc along the arc
  obtain ⟨δ, hδ, hthick⟩ := hCcpt.exists_thickening_subset_open hFac.isOpen_compl hCFa
  set η : ℝ := min (δ / 2) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
  set Aη := (fun q : ℝ × ℂ => (q.1 : ℂ) * q.2) '' (Ioo (1 - η) 1 ×ˢ C) with hAη
  have hAconn : IsPreconnected Aη :=
    (isPreconnected_Ioo.prod hCconn).image _
      (by fun_prop : Continuous fun q : ℝ × ℂ => (q.1 : ℂ) * q.2).continuousOn
  have hAball : Aη ⊆ ball 0 1 := by
    rintro _ ⟨⟨r, c⟩, ⟨hr, hc⟩, rfl⟩
    have hc1 : ‖c‖ = 1 := by simpa using hCs hc
    rw [mem_ball, dist_zero_right, norm_mul, hc1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hr.1, min_le_right (δ / 2) (1 / 2 : ℝ)])]
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
  have hSS : Sη ⊆ (seedRayClosure γ₁)ᶜ := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ hz
    have hwJ := hhA ⟨x, hx, rfl⟩
    have hback : inv p (uninv p (h x)) = h x := inv_uninv p (h x)
    exact hwJ (hback ▸ inv_mem_invCurve hz hp)
  have hSF : Disjoint Sη F := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ hzF
    have hxF : x ∈ Fa :=
      ⟨h x, Or.inl ⟨uninv p (h x), hzF, inv_uninv p (h x)⟩, h.symm_apply_apply x⟩
    exact hthick (hAthick hx) hxF
  -- near every interior point of the arc, the left side of `γ₁` lies in the sector
  refine ⟨Sη, hSconn, hSS, hSF, ?_⟩
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
  have hw0 : Ψ w ≠ 0 := by
    intro h'; rw [h', norm_zero] at hw2; linarith [min_le_right (δ / 2) (1 / 2 : ℝ)]
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

/-! ### The right side of a proper curve from `0` -/

/-- The frozen `rightSideOf` of the range of a proper curve from `0` lies in its open right side. -/
theorem rightSideOf_range_subset_rightSide {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) :
    rightSideOf (range γ) ⊆ rightSide γ := by
  rintro z ⟨⟨hzH, hzγ⟩, x, hx, hxγ, hxcl⟩
  have h0 : (γ 0).im = 0 := by rw [hγ0]; rfl
  set K := connectedComponentIn (H \ range γ) z with hK
  have hKS : K ⊆ (seedRayClosure γ)ᶜ := by
    intro w hw hwS
    have hw' := connectedComponentIn_subset _ _ hw
    rcases hwS with hwγ | ⟨-, him⟩
    · exact hw'.2 hwγ
    · have : (0 : ℝ) < w.im := hw'.1
      rw [hγ0] at him
      exact absurd him (not_le.2 this)
  have hxS : (x : ℂ) ∉ seedRayClosure γ := by
    rintro (hxγ' | ⟨hre, -⟩)
    · exact hxγ hxγ'
    · rw [hγ0] at hre; simp at hre; linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isClosed_seedRayClosure hγ).isOpen_compl _ hxS
  obtain ⟨y, hyK, hyx⟩ := Metric.mem_closure_iff.1 hxcl ε hε
  have hyB : y ∈ ball (x : ℂ) ε := by rw [mem_ball, dist_comm]; exact hyx
  set q : ℂ := (x : ℂ) - ((ε / 2 : ℝ) : ℂ) * I with hq
  have hqB : q ∈ ball (x : ℂ) ε := by
    rw [mem_ball, hq, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hqR : q ∈ rightSide γ := by
    refine lowerRight_subset_rightSide hγ.2.2.1 h0 ⟨?_, ?_⟩
    · rw [hγ0]; simp [hq]; exact hx
    · simp [hq]; positivity
  have hpre : IsPreconnected (K ∪ ball (x : ℂ) ε) :=
    IsPreconnected.union y hyK hyB isPreconnected_connectedComponentIn (convex_ball _ _).isPreconnected
  have hsub := hpre.subset_connectedComponentIn (subset_union_right hqB) (union_subset hKS hball)
  rw [← connectedComponentIn_eq hqR] at hsub
  exact hsub (subset_union_left (mem_connectedComponentIn (⟨hzH, hzγ⟩ : z ∈ H \ range γ)))

/-! ### The crossing certificate -/

/-- **The crossing certificate.** Let `γ` be a proper curve from `0` and `η'` a proper curve from a real seed
`u ≤ 0`. If `η'(t)` is on the right side of `γ`, then for some `t₁ < t` the point `η'(t₁)` is a limit of points of
`γ` on the left side of `η'`. -/
theorem exists_crossing_certificate {γ η' : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hη' : IsProperCurve η') (hu : (η' 0).im = 0) (hu0 : (η' 0).re ≤ 0) {t : ℝ≥0}
    (ht : η' t ∈ rightSide γ) :
    ∃ t₁ < t, η' t₁ ∈ closure (range γ ∩ leftSide η') := by
  have h0 : (γ 0).im = 0 := by rw [hγ0]; rfl
  have hRo : IsOpen (rightSide γ) := (isClosed_seedRayClosure hγ).isOpen_compl.connectedComponentIn
  have hRS : rightSide γ ⊆ (seedRayClosure γ)ᶜ := connectedComponentIn_subset _ _
  have hγcl : IsClosed (range γ) := by rw [← image_univ]; exact isClosed_image hγ isClosed_univ
  have hdisj := disjoint_leftSide_rightSide hγ h0
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  set F := closure (range γ ∩ leftSide η') with hF
  have hFγ : F ⊆ range γ := closure_minimal inter_subset_left hγcl
  have hFim : ∀ w ∈ F, 0 ≤ w.im := by
    rintro w hw
    obtain ⟨r, rfl⟩ := hFγ hw
    exact hγ.2.2.1 r
  have hzγ : η' t ∉ range γ := fun h' => hRS ht (Or.inl h')
  -- the time `t` is positive
  have ht0 : (0 : ℝ) < t := by
    rcases eq_or_ne t 0 with h' | h'
    · exfalso
      rw [h'] at ht
      have hη0 : η' 0 = ((η' 0).re : ℂ) := Complex.ext (by simp) (by simp [hu])
      by_cases hS : ((η' 0).re : ℂ) ∈ seedRayClosure γ
      · exact hRS ht (hη0 ▸ hS)
      · rcases hu0.lt_or_eq with hlt | heq
        · have hL := ofReal_mem_leftSide hγ.2.2.1 h0 (by rw [hγ0]; exact hlt) hS
          exact Set.disjoint_left.1 hdisj (hη0 ▸ hL) ht
        · exact hS (Or.inl ⟨0, by rw [hγ0, heq]; simp⟩)
    · exact_mod_cast pos_iff_ne_zero.2 h'
  -- the collar of `η'([0, t])` avoids `F`
  have hFℓ : ∀ τ ∈ Icc (-1 : ℝ) t, seedLine η' τ ∉ F := by
    intro τ hτ hτF
    rcases lt_or_ge τ 0 with hτ0 | hτ0
    · exact absurd (hFim _ hτF) (not_le.2 (seedLine_im_neg hu hτ0))
    · have e : seedLine η' τ = η' τ.toNNReal := by simp [seedLine, hτ0]
      rw [e] at hτF
      rcases (show τ.toNNReal ≤ t from by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal τ hτ0]; exact hτ.2).lt_or_eq with hlt | heq
      · exact hcon _ hlt hτF
      · exact hzγ (hFγ (heq ▸ hτF))
  obtain ⟨S, hSc, hSS, hSF, hSL⟩ := exists_leftCollar hη' hu isClosed_closure hFℓ
  -- a point of `S` near the seed ray, on the left of both curves
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff.1 (hSL (-1 / 2) ⟨by norm_num, by linarith⟩)
  set w₁ : ℂ := seedLine η' (-1 / 2) - ((ε₁ / 2 : ℝ) : ℂ) with hw₁
  have hℓ₁ : seedLine η' (-1 / 2) = η' 0 + ((-1 / 2 : ℝ) : ℂ) * I := seedLine_of_neg η' (by norm_num)
  have hw₁re : w₁.re = (η' 0).re - ε₁ / 2 := by simp [hw₁, hℓ₁]
  have hw₁im : w₁.im = -1 / 2 := by simp [hw₁, hℓ₁, hu]
  have hw₁L : w₁ ∈ leftSide η' :=
    lowerLeft_subset_leftSide hη'.2.2.1 hu ⟨by rw [hw₁re]; linarith, by rw [hw₁im]; norm_num⟩
  have hw₁S : w₁ ∈ S := by
    refine hb₁ ?_ hw₁L
    rw [hw₁, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have hw₁γ : w₁ ∈ leftSide γ :=
    lowerLeft_subset_leftSide hγ.2.2.1 h0 ⟨by rw [hw₁re, hγ0]; simp; linarith, by rw [hw₁im]; norm_num⟩
  -- a point of `S` near `η'(t)`, on the right of `γ`
  obtain ⟨r, hr, hrR⟩ := Metric.isOpen_iff.1 hRo _ ht
  have hcont : ContinuousAt (seedLine η') (t : ℝ) := (continuous_seedLine hη'.1).continuousAt
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hcont (r / 2) (by positivity)
  set τ : ℝ := (t : ℝ) - min (δ / 2) ((t : ℝ) / 2) with hτ
  have hm1 : 0 < min (δ / 2) ((t : ℝ) / 2) := lt_min (by positivity) (by positivity)
  have hm2 : min (δ / 2) ((t : ℝ) / 2) ≤ δ / 2 := min_le_left _ _
  have hm3 : min (δ / 2) ((t : ℝ) / 2) ≤ (t : ℝ) / 2 := min_le_right _ _
  have hτI : τ ∈ Ioo (-1 : ℝ) t := ⟨by rw [hτ]; linarith, by rw [hτ]; linarith⟩
  have hτd : dist (seedLine η' τ) (η' t) < r / 2 := by
    rw [← seedLine_coe η' t]
    refine hδb ?_
    rw [Real.dist_eq, hτ, show (t : ℝ) - min (δ / 2) ((t : ℝ) / 2) - t = -min (δ / 2) ((t : ℝ) / 2) by ring,
      abs_neg, abs_of_pos hm1]
    linarith
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.eventually_nhds_iff.1 (hSL τ hτI)
  have hcl := seedRayClosure_subset_closure_leftSide hη' hu (seedLine_mem hu τ)
  obtain ⟨w₂, hw₂L, hw₂d⟩ := Metric.mem_closure_iff.1 hcl (min ε₂ (r / 2)) (lt_min hε₂ (by positivity))
  have hw₂S : w₂ ∈ S := hb₂ (by rw [dist_comm]; exact hw₂d.trans_le (min_le_left _ _)) hw₂L
  have hw₂R : w₂ ∈ rightSide γ := by
    refine hrR ?_
    rw [mem_ball]
    calc dist w₂ (η' t) ≤ dist w₂ (seedLine η' τ) + dist (seedLine η' τ) (η' t) := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by
          refine add_lt_add ?_ hτd
          rw [dist_comm]; exact hw₂d.trans_le (min_le_right _ _)
      _ = r := by ring
  -- `S` lies on the left of `η'`, hence off `γ`'s closed curve
  have hSL' : S ⊆ leftSide η' := by
    have := hSc.subset_connectedComponentIn hw₁S hSS
    rwa [← connectedComponentIn_eq hw₁L] at this
  have hSγ : S ⊆ (seedRayClosure γ)ᶜ := by
    intro x hxS hxγ
    have hxL := hSL' hxS
    have hxnotγ : x ∉ range γ := fun h' =>
      Set.disjoint_left.1 hSF hxS (subset_closure ⟨h', hxL⟩)
    rcases hxγ with h' | ⟨hre, him⟩
    · exact hxnotγ h'
    · rw [hγ0] at hre him
      simp only [Complex.zero_re, Complex.zero_im] at hre him
      rcases him.lt_or_eq with himlt | himeq
      · rcases hu0.lt_or_eq with hult | hueq
        · have hxR : x ∈ rightSide η' :=
            lowerRight_subset_rightSide hη'.2.2.1 hu ⟨by rw [hre]; exact hult, himlt⟩
          exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hη' hu) hxL hxR
        · exact connectedComponentIn_subset _ _ hxL
            (Or.inr ⟨by rw [hre, hueq], by rw [hu]; exact himlt.le⟩)
      · exact hxnotγ ⟨0, by rw [hγ0]; exact Complex.ext (by simp [hre]) (by simp [himeq])⟩
  -- `S` joins the two sides of `γ`
  have := hSc.subset_connectedComponentIn hw₁S hSγ
  rw [← connectedComponentIn_eq hw₁γ] at this
  exact Set.disjoint_left.1 hdisj (this hw₂S) hw₂R

/-! ### SB3's final certificate -/

/-- **SB3's final certificate** (supplement p. 634): if S1 holds for every finite prefix of the proper lower walk `γ`
(with the bridge `[u, 0]`) and every available prefix of the upper path `η` from `u ≤ 0`, the whole available range of
`η` misses the open right side of the walk. A point `η(t)` there gives, for one completion `η₀` of `η([0, t])`, an
earlier point `η(t₁)` approached by points `γ(r)` on the left of `η₀` (`exists_crossing_certificate`); these `r` are
bounded, so S1 for a long enough prefix `γ([0, s])` supplies a completion `η₁` with all of them on its closed right,
while the side principle puts the points near `η(t₁)` on the left of `η₁`. -/
theorem sb3TopologyStatement : SB3TopologyStatement := by
  intro γ η ζ u hγ hγ0 hu hη0 _ hS1
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro z ⟨⟨t, ht, rfl⟩, hz⟩
  have hzR := rightSideOf_range_subset_rightSide hγ hγ0 hz
  obtain ⟨η₀, hη₀, -⟩ := hS1 0 t ht
  have P₀ := isProperCurve_of_isProperCompletion hη₀
  have e₀ : η₀ 0 = u := (hη₀.2.2.2.2 0 zero_le).trans hη0
  have hu₀ : (η₀ 0).im = 0 := by rw [e₀]; rfl
  have hu₀' : (η₀ 0).re ≤ 0 := by rw [e₀]; exact hu
  have ht₀ : η₀ t = η t := hη₀.2.2.2.2 t le_rfl
  obtain ⟨t₁, ht₁, hcl⟩ := exists_crossing_certificate hγ hγ0 P₀ hu₀ hu₀' (ht₀ ▸ hzR)
  -- the walk's parameters near the certificate are bounded
  set R : ℝ := ‖η₀ t₁‖ + 1 with hR
  obtain ⟨s, hs⟩ := eventually_atTop.1 (hγ.2.2.2.eventually_gt_atTop R)
  obtain ⟨η₁, hη₁, hsub⟩ := hS1 s t ht
  have P₁ := isProperCurve_of_isProperCompletion hη₁
  have hagree : ∀ τ ≤ t, η₁ τ = η₀ τ := fun τ hτ =>
    (hη₁.2.2.2.2 τ hτ).trans (hη₀.2.2.2.2 τ hτ).symm
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (eventually_mem_leftSide_of_eqOn P₀ P₁ hu₀ hagree ht₁)
  obtain ⟨w, ⟨⟨r, rfl⟩, hwL⟩, hwd⟩ := Metric.mem_closure_iff.1 hcl (min ε 1) (lt_min hε one_pos)
  have hw₁ : γ r ∈ leftSide η₁ := hball (by rw [dist_comm]; exact hwd.trans_le (min_le_left _ _)) hwL
  have hrs : r ≤ s := by
    by_contra hrs
    have h1 := hs r (not_le.1 hrs).le
    have h2 : ‖γ r‖ ≤ ‖η₀ t₁‖ + dist (η₀ t₁) (γ r) := by
      have := norm_le_norm_add_norm_sub' (γ r) (η₀ t₁)
      rw [dist_eq_norm, norm_sub_rev]; linarith
    have h3 : dist (η₀ t₁) (γ r) < 1 := hwd.trans_le (min_le_right _ _)
    linarith
  have hmem : γ r ∈ closedRightSide η₁ := hsub (Or.inl ⟨r, ⟨zero_le, hrs⟩, rfl⟩)
  have hu₁ : (η₁ 0).im = 0 := by rw [hagree 0 zero_le]; exact hu₀
  rcases hmem with hR' | hS'
  · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide P₁ hu₁) hw₁ hR'
  · exact connectedComponentIn_subset _ _ hw₁ hS'

/-- **Lemma SB3 from GW1's parametrization and the stage induction** (supplement pp. 633–634): the final certificate
is `sb3TopologyStatement`. -/
theorem sb3Statement_of_param_induction (hP : GW1ParamStatement.{u}) (hI : SB3InductionStatement.{u}) :
    SB3Statement.{u} :=
  sb3Statement_of_inputs hP hI sb3TopologyStatement

end SB

end Theorem14

end InteractingSLE
