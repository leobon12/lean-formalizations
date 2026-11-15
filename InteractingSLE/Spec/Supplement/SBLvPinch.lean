/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsFiber
import InteractingSLE.Spec.Supplement.SB2FinConfig

/-!
# Pinch-finiteness: finite fibres of a boundary map

Packet PROVE-T14-SBLEAVES, ruling R87. The finite fibres of the boundary extension `g` of a chart inverse
(`∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite`) are a hypothesis of Lemma S5 (`SB.s5Statement`, `Erase.ErasureStep`),
of S2's lift and of SB2(1)'s relative chain (`FinRel.exists_relConfig_of_path`). This file proves them once, for an
abstract boundary map.

**Boundary maps** (`IsBoundaryMap F`): `F` is continuous on `ℍ̄`, holomorphic and injective on `ℍ` with open image in
`ℍ`, its real boundary values are not values on `ℍ`, and `F → ∞` at `∞` in `ℍ`.

**The counting argument** (`finite_real_fibre_of_cover`). Let `y < y'` be two real preimages of `z`.
* The semicircle over `[y, y']` is mapped onto a Jordan curve `J` through `z` (`exists_isSemiJordan`, following
  PROVE-WALK-WORDS' `false_of_extendFrom_eq_of_lt`). The image of the open half-disc is inside `J`, and the image of the
  rest of `ℍ` is outside it.
* Every real boundary value `F m ≠ z` with `y < m < y'` is inside `J`.
* Semicircles over intervals with disjoint interiors give Jordan curves with disjoint insides
  (`disjoint_jordanIn_of_le`).
* Suppose the real boundary values other than `z` are covered by finitely many preconnected sets (*germs*), each
  missing `z` and `F(ℍ)`. A germ through such a value `F m` lies inside `J`. So `n + 1` consecutive gaps between
  preimages need `n + 1` distinct germs, and the real fibre has at most one more point than there are germs.

`finite_fibre_of_finite_real` adds the at most one preimage in `ℍ`.

**Paths.** `finite_fibre_of_paths`: if the real boundary values lie in `ℝ` or on finitely many continuous paths with
finite fibres whose ranges miss `F(ℍ)`, every fibre of `F` on `ℍ̄` is finite. The germs are the real rays at `z` and
the images of the gaps of `p⁻¹(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric Bornology
open QuantumZipper (H Hbar)
open LQGMetric.JordanMap (IsJordanCurve)

namespace InteractingSLE.Theorem14.SB.Lv

open WangWu (jordanIn jordanOut)
open WalkWords (semiPt)

/-! ### Boundary maps and their semicircle Jordan curves -/

/-- **A boundary map**: continuous on `ℍ̄`, holomorphic and injective on `ℍ` with open image in `ℍ`, with real
boundary values off the image of `ℍ`, and proper at `∞` in `ℍ`. The continuous extension of the inverse of a conformal
chart is one (`isBoundaryMap_of_isConformal`). -/
def IsBoundaryMap (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F H ∧ ContinuousOn F Hbar ∧ InjOn F H ∧ MapsTo F H H ∧ IsOpen (F '' H) ∧
    (∀ x : ℝ, F x ∉ F '' H) ∧ Tendsto F (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ)

/-- The image of the semicircle of centre `c` and radius `ρ` under `F`, with its two sides: `F` of the open
half-disc is inside, `F` of the rest of `ℍ` is outside. -/
def IsSemiJordan (F : ℂ → ℂ) (z : ℂ) (c ρ : ℝ) (J : Set ℂ) : Prop :=
  IsJordanCurve J ∧ z ∈ J ∧ (∀ p ∈ J, p = z ∨ ∃ w ∈ H, ‖w - c‖ = ρ ∧ p = F w) ∧
    (∀ w ∈ H, ‖w - c‖ = ρ → F w ∈ J) ∧ (∀ w ∈ H, ρ < ‖w - c‖ → F w ∈ jordanOut J) ∧
    (∀ w ∈ H, ‖w - c‖ < ρ → F w ∈ jordanIn J)

variable {F : ℂ → ℂ}

/-- A point of `ℍ` in a closed disc whose centre and radius are those of a real interval lies strictly outside the
disc of an interval further right. -/
theorem lt_norm_sub_of_le {c ρ c' ρ' : ℝ} (hle : c + ρ ≤ c' - ρ') (hρ : 0 ≤ ρ) {w : ℂ} (hw : w ∈ H)
    (hwc : ‖w - c'‖ ≤ ρ') : ρ < ‖w - c‖ := by
  have hb : 0 < w.im := hw
  have h1 : ‖w - c'‖ ^ 2 = (w.re - c') ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]; ring
  have h2 : ‖w - c‖ ^ 2 = (w.re - c) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]; ring
  have hρ' : 0 ≤ ρ' := (norm_nonneg _).trans hwc
  have h3 : (w.re - c') ^ 2 + w.im ^ 2 ≤ ρ' ^ 2 := by rw [← h1]; gcongr
  have h4 : c' - ρ' < w.re := by nlinarith
  have h5 : ρ ^ 2 < ‖w - c‖ ^ 2 := by rw [h2]; nlinarith
  nlinarith [norm_nonneg (w - c)]

/-- The mirror statement: a point of `ℍ` in the closed left disc lies strictly outside the right disc. -/
theorem lt_norm_sub_of_le' {c ρ c' ρ' : ℝ} (hle : c + ρ ≤ c' - ρ') (hρ' : 0 ≤ ρ') {w : ℂ} (hw : w ∈ H)
    (hwc : ‖w - c‖ ≤ ρ) : ρ' < ‖w - c'‖ := by
  have hb : 0 < w.im := hw
  have h1 : ‖w - c‖ ^ 2 = (w.re - c) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]; ring
  have h2 : ‖w - c'‖ ^ 2 = (w.re - c') ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]; ring
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hwc
  have h3 : (w.re - c) ^ 2 + w.im ^ 2 ≤ ρ ^ 2 := by rw [← h1]; gcongr
  have h4 : w.re < c + ρ := by nlinarith
  have h5 : ρ' ^ 2 < ‖w - c'‖ ^ 2 := by rw [h2]; nlinarith
  nlinarith [norm_nonneg (w - c')]

/-- **Semicircles over intervals with disjoint interiors have disjoint insides.** -/
theorem disjoint_jordanIn_of_le {z : ℂ} {c ρ c' ρ' : ℝ} {J J' : Set ℂ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hle : c + ρ ≤ c' - ρ') (hS : IsSemiJordan F z c ρ J) (hS' : IsSemiJordan F z c' ρ' J') :
    Disjoint (jordanIn J) (jordanIn J') := by
  obtain ⟨hJ, -, hJp, -, hJout, -⟩ := hS
  obtain ⟨hJ', hzJ', -, hJ'on, hJ'out, -⟩ := hS'
  have hsub : jordanIn J' ⊆ Jᶜ := by
    intro p hp hpJ
    rcases hJp p hpJ with rfl | ⟨w, hw, hwc, rfl⟩
    · exact hp.1 hzJ'
    · exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut J') hp
        (hJ'out w hw (lt_norm_sub_of_le' hle hρ'.le hw hwc.le))
  have htop : semiPt c' ρ' (Real.pi / 2) ∈ H :=
    WalkWords.semiPt_mem_H hρ' ⟨by positivity, by linarith [Real.pi_pos]⟩
  have htopc : ‖semiPt c' ρ' (Real.pi / 2) - c'‖ = ρ' := WalkWords.norm_semiPt_sub hρ'.le _
  have hin := Foundations.ThetaCurve.jordanIn_subset_jordanOut hJ' hJ hsub (hJ'on _ htop htopc)
    (hJout _ htop (lt_norm_sub_of_le hle hρ.le htop htopc.le))
  exact Set.disjoint_left.2 fun x hx hx' =>
    Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut J) hx (hin hx')

/-- **The semicircle Jordan curve.** Two real preimages `y₁ < y₂` of `z` give the Jordan curve `F(semicircle)`, with
the open half-disc mapped inside and the rest of `ℍ` mapped outside (PROVE-WALK-WORDS' argument, for any boundary
map). -/
theorem exists_isSemiJordan (hF : IsBoundaryMap F) {y₁ y₂ : ℝ} (hy : y₁ < y₂) {z : ℂ} (h₁ : F y₁ = z)
    (h₂ : F y₂ = z) : ∃ J, IsSemiJordan F z ((y₁ + y₂) / 2) ((y₂ - y₁) / 2) J := by
  obtain ⟨-, hFc, hFi, -, hFo, hFR, hFinf⟩ := hF
  have hqF : z ∉ F '' H := h₁ ▸ hFR y₁
  set c : ℝ := (y₁ + y₂) / 2 with hc
  set ρ : ℝ := (y₂ - y₁) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  set A : ℝ → ℂ := semiPt c ρ with hA
  have hA0 : A 0 = (y₂ : ℂ) := by rw [hA, WalkWords.semiPt_zero]; congr 1; rw [hc, hρ]; ring
  have hAπ : A Real.pi = (y₁ : ℂ) := by rw [hA, WalkWords.semiPt_pi]; congr 1; rw [hc, hρ]; ring
  have hpi := Real.pi_pos
  have hAre : ∀ θ ∈ Icc 0 Real.pi, θ = 0 ∨ θ = Real.pi → F (A θ) = z := by
    rintro θ - (rfl | rfl)
    · rw [hA0]; exact h₂
    · rw [hAπ]; exact h₁
  have hAH : ∀ θ ∈ Icc 0 Real.pi, θ ≠ 0 → θ ≠ Real.pi → A θ ∈ H := fun θ hθ h1 h2 =>
    WalkWords.semiPt_mem_H hρ0 ⟨lt_of_le_of_ne hθ.1 (Ne.symm h1), lt_of_le_of_ne hθ.2 h2⟩
  have hAF : ∀ θ ∈ Icc 0 Real.pi, ∀ θ' ∈ Icc 0 Real.pi, F (A θ) = F (A θ') →
      θ = θ' ∨ ((θ = 0 ∨ θ = Real.pi) ∧ (θ' = 0 ∨ θ' = Real.pi)) := by
    intro θ hθ θ' hθ' he
    by_cases hb : θ = 0 ∨ θ = Real.pi
    · by_cases hb' : θ' = 0 ∨ θ' = Real.pi
      · exact Or.inr ⟨hb, hb'⟩
      · rw [not_or] at hb'
        exact absurd ⟨A θ', hAH θ' hθ' hb'.1 hb'.2, he.symm.trans (hAre θ hθ hb)⟩ hqF
    · rw [not_or] at hb
      by_cases hb' : θ' = 0 ∨ θ' = Real.pi
      · exact absurd ⟨A θ, hAH θ hθ hb.1 hb.2, he.trans (hAre θ' hθ' hb')⟩ hqF
      · rw [not_or] at hb'
        exact Or.inl (WalkWords.semiPt_injOn hρ0 hθ hθ'
          (hFi (hAH θ hθ hb.1 hb.2) (hAH θ' hθ' hb'.1 hb'.2) he))
  have hAc : ContinuousOn (fun θ => F (A θ)) (Icc 0 Real.pi) :=
    hFc.comp (WalkWords.continuous_semiPt c ρ).continuousOn fun θ hθ =>
      WalkWords.semiPt_mem_Hbar hρ0.le hθ
  set u : ℝ → ℂ := fun t => F (A (Real.pi / 2 * t)) with hu
  set v : ℝ → ℂ := fun t => F (A (Real.pi - Real.pi / 2 * t)) with hv
  have hut : ∀ t ∈ Icc (0 : ℝ) 1, Real.pi / 2 * t ∈ Icc 0 Real.pi := fun t ht =>
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hvt : ∀ t ∈ Icc (0 : ℝ) 1, Real.pi - Real.pi / 2 * t ∈ Icc 0 Real.pi := fun t ht =>
    ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
  have huc : ContinuousOn u (Icc 0 1) := hAc.comp (by fun_prop) fun t ht => hut t ht
  have hvc : ContinuousOn v (Icc 0 1) := hAc.comp (by fun_prop) fun t ht => hvt t ht
  have hui : InjOn u (Icc 0 1) := by
    intro t ht t' ht' he
    rcases hAF _ (hut t ht) _ (hut t' ht') he with h | ⟨h1, h2⟩
    · exact mul_left_cancel₀ (by positivity) h
    · have e1 : Real.pi / 2 * t = 0 := h1.resolve_right fun h => by nlinarith [ht.2]
      have e2 : Real.pi / 2 * t' = 0 := h2.resolve_right fun h => by nlinarith [ht'.2]
      exact mul_left_cancel₀ (show Real.pi / 2 ≠ 0 by positivity) (e1.trans e2.symm)
  have hvi : InjOn v (Icc 0 1) := by
    intro t ht t' ht' he
    rcases hAF _ (hvt t ht) _ (hvt t' ht') he with h | ⟨h1, h2⟩
    · have : Real.pi / 2 * t = Real.pi / 2 * t' := by linarith
      exact mul_left_cancel₀ (by positivity) this
    · have e1 : Real.pi - Real.pi / 2 * t = Real.pi := h1.resolve_left fun h => by nlinarith [ht.2]
      have e2 : Real.pi - Real.pi / 2 * t' = Real.pi := h2.resolve_left fun h => by nlinarith [ht'.2]
      have : Real.pi / 2 * t = Real.pi / 2 * t' := by linarith
      exact mul_left_cancel₀ (show Real.pi / 2 ≠ 0 by positivity) this
  have hu0 : u 0 = z := by simp only [hu, mul_zero]; exact hAre 0 ⟨le_rfl, hpi.le⟩ (Or.inl rfl)
  have hv0 : v 0 = z := by
    simp only [hv, mul_zero, sub_zero]; exact hAre _ ⟨hpi.le, le_rfl⟩ (Or.inr rfl)
  have huv1 : u 1 = v 1 := by simp only [hu, hv, mul_one]; congr 2; ring
  have hint : u '' Icc 0 1 ∩ v '' Icc 0 1 ⊆ {u 0, u 1} := by
    rintro w ⟨⟨t, ht, rfl⟩, ⟨t', ht', he⟩⟩
    rcases hAF _ (hut t ht) _ (hvt t' ht') he.symm with h | ⟨h1, -⟩
    · have : t = 1 := by nlinarith [ht.2, ht'.2]
      rw [this]; exact Or.inr rfl
    · have : t = 0 := by
        rcases h1 with h1 | h1
        · nlinarith
        · nlinarith [ht.2]
      rw [this]; exact Or.inl rfl
  set J : Set ℂ := u '' Icc 0 1 ∪ v '' Icc 0 1 with hJdef
  have hJ : IsJordanCurve J :=
    Sec7.isJordanCurve_image_union huc hvc hui hvi (hu0.trans hv0.symm) huv1 hint
  have hzJ : z ∈ J := Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hu0⟩
  have hJpt : ∀ p ∈ J, p = z ∨ ∃ θ ∈ Ioo 0 Real.pi, p = F (A θ) := by
    have key : ∀ θ ∈ Icc 0 Real.pi, F (A θ) = z ∨ ∃ θ' ∈ Ioo 0 Real.pi, F (A θ) = F (A θ') := by
      intro θ hθ
      by_cases hb : θ = 0 ∨ θ = Real.pi
      · exact Or.inl (hAre θ hθ hb)
      · rw [not_or] at hb
        exact Or.inr ⟨θ, ⟨lt_of_le_of_ne hθ.1 (Ne.symm hb.1), lt_of_le_of_ne hθ.2 hb.2⟩, rfl⟩
    rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact key _ (hut t ht)
    · exact key _ (hvt t ht)
  have hcircJ : ∀ θ ∈ Ioo 0 Real.pi, F (A θ) ∈ J := by
    intro θ hθ
    by_cases hθ2 : θ ≤ Real.pi / 2
    · refine Or.inl ⟨θ / (Real.pi / 2), ⟨div_nonneg hθ.1.le (by positivity), ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]; exact hθ2
      · simp only [hu]; congr 2; field_simp
    · refine Or.inr ⟨(Real.pi - θ) / (Real.pi / 2), ⟨div_nonneg (by linarith [hθ.2]) (by positivity), ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]; linarith
      · simp only [hv]; congr 2; field_simp; ring
  have hJp : ∀ p ∈ J, p = z ∨ ∃ w ∈ H, ‖w - c‖ = ρ ∧ p = F w := by
    intro p hp
    rcases hJpt p hp with h | ⟨θ, hθ, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨A θ, WalkWords.semiPt_mem_H hρ0 hθ, WalkWords.norm_semiPt_sub hρ0.le θ, rfl⟩
  have hJon : ∀ w ∈ H, ‖w - c‖ = ρ → F w ∈ J := by
    intro w hw hwc
    obtain ⟨θ, hθ, rfl⟩ := WalkWords.exists_semiPt_eq hρ0 hw hwc
    exact hcircJ θ hθ
  have hnotJ : ∀ w ∈ H, ‖w - c‖ ≠ ρ → F w ∉ J := by
    intro w hw hwc hJw
    rcases hJpt _ hJw with he | ⟨θ, hθ, he⟩
    · exact hqF ⟨w, hw, he⟩
    · have := hFi hw (WalkWords.semiPt_mem_H hρ0 hθ) he
      exact hwc (by rw [this]; exact WalkWords.norm_semiPt_sub hρ0.le θ)
  have hout : ∀ w ∈ H, ρ < ‖w - c‖ → F w ∈ jordanOut J := by
    intro w hw hwc
    set R : Set ℂ := (fun t : ℝ => w + (t : ℂ) * I) '' Ici 0 with hR
    have hRH : ∀ x ∈ R, x ∈ H ∧ ρ < ‖x - c‖ := by
      rintro _ ⟨t, ht, rfl⟩
      have hzim : 0 < w.im := hw
      have ht0 : (0 : ℝ) ≤ t := ht
      refine ⟨show 0 < (w + (t : ℂ) * I).im by simp; linarith, ?_⟩
      have h1 : ‖w - c‖ ^ 2 ≤ ‖w + (t : ℂ) * I - c‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
          add_zero, sub_im, add_im, mul_im]
        nlinarith
      have h2 : 0 ≤ ‖w + (t : ℂ) * I - c‖ := norm_nonneg _
      nlinarith [norm_nonneg (w - c)]
    have hRc : IsPreconnected (F '' R) :=
      (isPreconnected_Ici.image _ (by fun_prop)).image F
        (hFc.mono fun x hx => QuantumZipper.H_subset_Hbar (hRH x hx).1)
    have hRb : ¬ IsBounded (F '' R) := by
      intro hb
      have hpath : Tendsto (fun t : ℝ => w + (t : ℂ) * I) atTop (cobounded ℂ ⊓ 𝓟 H) := by
        refine tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 ?_, tendsto_principal.2 ?_⟩
        · refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right atTop (-‖w‖) tendsto_id)
          have : ‖(t : ℂ) * I‖ ≤ ‖w + (t : ℂ) * I‖ + ‖w‖ := by
            calc ‖(t : ℂ) * I‖ = ‖(w + (t : ℂ) * I) - w‖ := by ring_nf
              _ ≤ ‖w + (t : ℂ) * I‖ + ‖w‖ := norm_sub_le _ _
          rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] at this
          simp only [id]
          linarith [le_abs_self t]
        · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
          exact (hRH _ ⟨t, ht, rfl⟩).1
      obtain ⟨T, hT⟩ := eventually_atTop.1 ((hFinf.comp hpath) (isBounded_def.1 hb))
      exact hT (max T 0) (le_max_left _ _) ⟨_, ⟨max T 0, Set.mem_Ici.2 (le_max_right T 0), rfl⟩, rfl⟩
    have hRJ : Disjoint (F '' R) J := Set.disjoint_left.2 fun _ ⟨x, hx, he⟩ hJ' =>
      hnotJ x (hRH x hx).1 (hRH x hx).2.ne' (he ▸ hJ')
    exact WangWu.subset_jordanOut_of_isPreconnected hRc hRb hRJ ⟨w, ⟨0, Set.self_mem_Ici, by simp⟩, rfl⟩
  have hpi2 : Real.pi / 2 ∈ Ioo 0 Real.pi := ⟨by positivity, by linarith⟩
  have htop : F (A (Real.pi / 2)) ∈ J := hcircJ _ hpi2
  have htopH : F (A (Real.pi / 2)) ∈ F '' H := ⟨_, WalkWords.semiPt_mem_H hρ0 hpi2, rfl⟩
  obtain ⟨x, hxI, w, hw, rfl⟩ : (jordanIn J ∩ F '' H).Nonempty := by
    have := WangWu.mem_closure_jordanIn hJ htop
    rw [_root_.mem_closure_iff] at this
    obtain ⟨x, hx1, hx2⟩ := this _ hFo htopH
    exact ⟨x, hx2, hx1⟩
  have hwc : ‖w - c‖ < ρ := by
    rcases lt_trichotomy ‖w - c‖ ρ with h | h | h
    · exact h
    · exact absurd (hJon w hw h) hxI.1
    · exact absurd (hout w hw h) (Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut J) hxI)
  have hin : ∀ x ∈ H, ‖x - c‖ < ρ → F x ∈ jordanIn J := by
    have hQc : IsPreconnected (F '' (H ∩ ball (c : ℂ) ρ)) :=
      ((convex_H.inter (convex_ball _ _)).isPreconnected).image F
        (hFc.mono fun x hx => QuantumZipper.H_subset_Hbar hx.1)
    have hQin : F '' (H ∩ ball (c : ℂ) ρ) ⊆ jordanIn J := by
      refine WangWu.IsPreconnected.subset_jordanIn hJ hQc
        (Set.disjoint_left.2 fun _ ⟨x, hx, he⟩ hJx => ?_) ⟨_, ⟨w, ⟨hw, ?_⟩, rfl⟩, hxI⟩
      · have hx2 := hx.2
        rw [mem_ball, dist_eq_norm] at hx2
        exact hnotJ x hx.1 hx2.ne (he ▸ hJx)
      · rw [mem_ball, dist_eq_norm]; exact hwc
    intro x hx hxc
    exact hQin ⟨x, ⟨hx, by rw [mem_ball, dist_eq_norm]; exact hxc⟩, rfl⟩
  exact ⟨J, hJ, hzJ, hJp, hJon, hout, hin⟩

/-- **A real boundary value under the semicircle is inside.** If `|m − c| < ρ` and `F m ≠ z`, then `F m` is inside the
semicircle Jordan curve: it is the limit of `F` along the vertical approach through the half-disc, and it is not on the
curve (real boundary values are not values on `ℍ`). -/
theorem mem_jordanIn_of_isSemiJordan (hF : IsBoundaryMap F) {z : ℂ} {c ρ : ℝ} {J : Set ℂ}
    (hS : IsSemiJordan F z c ρ J) {m : ℝ} (hm : |m - c| < ρ) (hFm : F m ≠ z) : F m ∈ jordanIn J := by
  obtain ⟨-, hFc, -, -, -, hFR, -⟩ := hF
  obtain ⟨hJ, -, hJp, -, -, hin⟩ := hS
  have happroach : Tendsto (fun ε : ℝ => (m : ℂ) + (ε : ℂ) * I) (𝓝[>] 0) (𝓝[H] (m : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : Continuous (fun ε : ℝ => (m : ℂ) + (ε : ℂ) * I) := by fun_prop
      have h := hcont.tendsto 0
      simp only [ofReal_zero, zero_mul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      show 0 < ((m : ℂ) + (ε : ℂ) * I).im
      simpa using hε
  have hFlim : Tendsto (fun ε : ℝ => F ((m : ℂ) + (ε : ℂ) * I)) (𝓝[>] 0) (𝓝 (F m)) :=
    ((hFc _ (show (0 : ℝ) ≤ ((m : ℂ)).im by simp)).tendsto.mono_left
      (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)).comp happroach
  have hcl : F m ∈ closure (jordanIn J) := by
    refine mem_closure_of_tendsto hFlim ?_
    have hδ : 0 < ρ - |m - c| := by linarith
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    refine hin _ (show 0 < ((m : ℂ) + (ε : ℂ) * I).im by simpa using hε.1) ?_
    calc ‖(m : ℂ) + (ε : ℂ) * I - c‖ ≤ ‖((m - c : ℝ) : ℂ)‖ + ‖(ε : ℂ) * I‖ := by
          rw [show (m : ℂ) + (ε : ℂ) * I - c = ((m - c : ℝ) : ℂ) + (ε : ℂ) * I by push_cast; ring]
          exact norm_add_le _ _
      _ < ρ := by
          rw [norm_mul, norm_I, mul_one, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos hε.1]
          linarith [hε.2]
  rw [WangWu.closure_jordanIn hJ] at hcl
  rcases hcl with h | h
  · exact h
  · rcases hJp _ h with he | ⟨w, hw, -, he⟩
    · exact absurd he hFm
    · exact absurd ⟨w, hw, he.symm⟩ (hFR m)

/-! ### Counting -/

/-- **Pinch-finiteness, germ form.** If the real boundary values of a boundary map other than `z` are covered by
finitely many preconnected germs, each missing `z` and `F(ℍ)`, the real fibre over `z` is finite (with at most one
more point than there are germs). -/
theorem finite_real_fibre_of_cover (hF : IsBoundaryMap F) {z : ℂ} {ι : Type*} [Fintype ι] (G : ι → Set ℂ)
    (hGc : ∀ j, IsPreconnected (G j)) (hGz : ∀ j, z ∉ G j) (hGF : ∀ j, Disjoint (G j) (F '' H))
    (hcov : ∀ x : ℝ, F x ≠ z → ∃ j, F x ∈ G j) : {x : ℝ | F x = z}.Finite := by
  by_contra hinf
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (Fintype.card ι + 2)
  set e := t.orderEmbOfFin htc with he_def
  have he : ∀ i, F (e i) = z := fun i => hts (t.orderEmbOfFin_mem htc i)
  have hlt : ∀ i : Fin (Fintype.card ι + 1), e i.castSucc < e i.succ := fun i =>
    e.strictMono (Fin.castSucc_lt_succ (i := i))
  have key : ∀ i : Fin (Fintype.card ι + 1), ∃ (J : Set ℂ) (m : ℝ) (j : ι),
      IsSemiJordan F z ((e i.castSucc + e i.succ) / 2) ((e i.succ - e i.castSucc) / 2) J ∧
        F m ∈ G j ∧ G j ⊆ jordanIn J := by
    intro i
    obtain ⟨J, hJ⟩ := exists_isSemiJordan hF (hlt i) (he _) (he _)
    obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hF.1 hF.2.1 hF.2.2.1 (hlt i) z
    obtain ⟨j, hj⟩ := hcov m hFm
    have hmin := mem_jordanIn_of_isSemiJordan hF hJ
      (abs_lt.2 ⟨by linarith [hm.1, hm.2], by linarith [hm.1, hm.2]⟩) hFm
    refine ⟨J, m, j, hJ, hj, WangWu.IsPreconnected.subset_jordanIn hJ.1 (hGc j) ?_ ⟨_, hj, hmin⟩⟩
    refine Set.disjoint_left.2 fun p hpG hpJ => ?_
    rcases hJ.2.2.1 p hpJ with rfl | ⟨w, hw, -, rfl⟩
    · exact hGz j hpG
    · exact Set.disjoint_left.1 (hGF j) hpG ⟨w, hw, rfl⟩
  choose J m j hJ hm hj using key
  have hdisj : ∀ i k : Fin (Fintype.card ι + 1), i < k → Disjoint (jordanIn (J i)) (jordanIn (J k)) := by
    intro i k hik
    have hle : e i.succ ≤ e k.castSucc := e.monotone (Fin.succ_le_castSucc_iff.2 hik)
    refine disjoint_jordanIn_of_le (by linarith [hlt i]) (by linarith [hlt k]) ?_ (hJ i) (hJ k)
    linarith
  have hinj : Function.Injective j := by
    intro i k hik
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Set.disjoint_left.1 (hdisj i k h) (hj i (hm i)) (hik ▸ hj k |> fun hsub => hsub (hik ▸ hm i))
    · exact Set.disjoint_left.1 (hdisj k i h) (hj k (hm k)) (hik ▸ hj i |> fun hsub => hsub (hik.symm ▸ hm k))
  have hcard := Fintype.card_le_of_injective j hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Pinch-finiteness, germ form, for a finite set of germs. -/
theorem finite_real_fibre_of_finite_cover (hF : IsBoundaryMap F) {z : ℂ} {𝒢 : Set (Set ℂ)} (h𝒢 : 𝒢.Finite)
    (hGc : ∀ G ∈ 𝒢, IsPreconnected G) (hGz : ∀ G ∈ 𝒢, z ∉ G) (hGF : ∀ G ∈ 𝒢, Disjoint G (F '' H))
    (hcov : ∀ x : ℝ, F x ≠ z → ∃ G ∈ 𝒢, F x ∈ G) : {x : ℝ | F x = z}.Finite := by
  have := h𝒢.fintype
  exact finite_real_fibre_of_cover hF (fun G : 𝒢 => (G : Set ℂ)) (fun G => hGc G G.2) (fun G => hGz G G.2)
    (fun G => hGF G G.2) fun x hx => by
      obtain ⟨G, hG, hxG⟩ := hcov x hx
      exact ⟨⟨G, hG⟩, hxG⟩

/-- The whole fibre on `ℍ̄` is finite once the real fibre is: there is at most one preimage in `ℍ`. -/
theorem finite_fibre_of_finite_real (hF : IsBoundaryMap F) {z : ℂ} (hR : {x : ℝ | F x = z}.Finite) :
    (F ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := by
  have hHsub : (F ⁻¹' {z} ∩ H).Subsingleton := fun a ha b hb => hF.2.2.1 ha.2 hb.2 (ha.1.trans hb.1.symm)
  refine ((hR.image ((↑) : ℝ → ℂ)).union hHsub.finite).subset ?_
  rintro v ⟨hv, hv0⟩
  rcases (show (0 : ℝ) ≤ v.im from hv0).lt_or_eq with hpos | h0
  · exact Or.inr ⟨hv, hpos⟩
  · refine Or.inl ⟨v.re, ?_, ?_⟩
    · show F (v.re : ℂ) = z
      rw [show ((v.re : ℝ) : ℂ) = v from Complex.ext (by simp) (by simp [h0])]
      exact hv
    · exact Complex.ext (by simp) (by simp [h0])

/-! ### Germs: the real rays and the gaps of a path's fibre -/

/-- The real points `≤ Re z` other than `z`. -/
def realGermL (z : ℂ) : Set ℂ := ((↑) : ℝ → ℂ) '' {x : ℝ | (x : ℂ) ≠ z ∧ x ≤ z.re}

/-- The real points `≥ Re z` other than `z`. -/
def realGermR (z : ℂ) : Set ℂ := ((↑) : ℝ → ℂ) '' {x : ℝ | (x : ℂ) ≠ z ∧ z.re ≤ x}

theorem isPreconnected_realGermL (z : ℂ) : IsPreconnected (realGermL z) := by
  have hoc : Set.OrdConnected {x : ℝ | (x : ℂ) ≠ z ∧ x ≤ z.re} := by
    refine ⟨?_⟩
    intro x _ y hy t ht
    refine ⟨fun htz => ?_, ht.2.trans hy.2⟩
    have hzt : z.re = t := by rw [← htz]; simp
    have hyt : y = t := le_antisymm (hzt ▸ hy.2) ht.2
    exact hy.1 (hyt ▸ htz)
  exact hoc.isPreconnected.image _ Complex.continuous_ofReal.continuousOn

theorem isPreconnected_realGermR (z : ℂ) : IsPreconnected (realGermR z) := by
  have hoc : Set.OrdConnected {x : ℝ | (x : ℂ) ≠ z ∧ z.re ≤ x} := by
    refine ⟨?_⟩
    intro x hx y _ t ht
    refine ⟨fun htz => ?_, hx.2.trans ht.1⟩
    have hzt : z.re = t := by rw [← htz]; simp
    have hxt : x = t := le_antisymm ht.1 (hzt ▸ hx.2)
    exact hx.1 (hxt ▸ htz)
  exact hoc.isPreconnected.image _ Complex.continuous_ofReal.continuousOn

theorem notMem_realGermL (z : ℂ) : z ∉ realGermL z := fun ⟨_, hx, he⟩ => hx.1 he

theorem notMem_realGermR (z : ℂ) : z ∉ realGermR z := fun ⟨_, hx, he⟩ => hx.1 he

/-- Every real point other than `z` is in one of the two real germs. -/
theorem mem_realGerm {z : ℂ} {x : ℝ} (hx : (x : ℂ) ≠ z) : (x : ℂ) ∈ realGermL z ∨ (x : ℂ) ∈ realGermR z := by
  rcases le_total x z.re with h | h
  · exact Or.inl ⟨x, ⟨hx, h⟩, rfl⟩
  · exact Or.inr ⟨x, ⟨hx, h⟩, rfl⟩

/-- **The germs of a path at `z`**: the images of the open gaps between consecutive points of its fibre over `z`
(with `−1` and `2` as outer ends). -/
def pathGerms (p : ℝ → ℂ) (z : ℂ) : Set (Set ℂ) :=
  {G | ∃ a b : ℝ, (a = -1 ∨ (a ∈ Icc (0 : ℝ) 1 ∧ p a = z)) ∧ (b = 2 ∨ (b ∈ Icc (0 : ℝ) 1 ∧ p b = z)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, p t = z → t ∉ Ioo a b) ∧ G = p '' (Icc 0 1 ∩ Ioo a b)}

theorem finite_pathGerms {p : ℝ → ℂ} {z : ℂ} (hpf : (p ⁻¹' {z} ∩ Icc 0 1).Finite) : (pathGerms p z).Finite := by
  set T : Set ℝ := insert (-1) (insert 2 (p ⁻¹' {z} ∩ Icc 0 1)) with hT
  have hTf : T.Finite := (hpf.insert 2).insert (-1)
  refine ((hTf.prod hTf).image fun ab : ℝ × ℝ => p '' (Icc 0 1 ∩ Ioo ab.1 ab.2)).subset ?_
  rintro G ⟨a, b, ha, hb, -, rfl⟩
  refine ⟨(a, b), ⟨?_, ?_⟩, rfl⟩
  · rcases ha with rfl | ⟨ha, hpa⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨hpa, ha⟩)
  · rcases hb with rfl | ⟨hb, hpb⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨hpb, hb⟩)

theorem isPreconnected_of_mem_pathGerms {p : ℝ → ℂ} {z : ℂ} (hp : ContinuousOn p (Icc 0 1)) {G : Set ℂ}
    (hG : G ∈ pathGerms p z) : IsPreconnected G := by
  obtain ⟨a, b, -, -, -, rfl⟩ := hG
  exact ((convex_Icc 0 1).inter (convex_Ioo a b)).isPreconnected.image p (hp.mono inter_subset_left)

theorem notMem_of_mem_pathGerms {p : ℝ → ℂ} {z : ℂ} {G : Set ℂ} (hG : G ∈ pathGerms p z) : z ∉ G := by
  obtain ⟨a, b, -, -, hgap, rfl⟩ := hG
  rintro ⟨t, ⟨ht, hab⟩, hpt⟩
  exact hgap t ht hpt hab

theorem subset_of_mem_pathGerms {p : ℝ → ℂ} {z : ℂ} {G : Set ℂ} (hG : G ∈ pathGerms p z) :
    G ⊆ p '' Icc 0 1 := by
  obtain ⟨a, b, -, -, -, rfl⟩ := hG
  exact image_mono inter_subset_left

/-- Every point of the path other than `z` lies in one of its germs. -/
theorem exists_mem_pathGerms {p : ℝ → ℂ} {z : ℂ} (hpf : (p ⁻¹' {z} ∩ Icc 0 1).Finite) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hps : p s ≠ z) : ∃ G ∈ pathGerms p z, p s ∈ G := by
  classical
  set Tf : Finset ℝ := hpf.toFinset with hTf
  have hmemT : ∀ t, t ∈ Tf ↔ t ∈ Icc (0 : ℝ) 1 ∧ p t = z := fun t => by
    rw [hTf, Set.Finite.mem_toFinset]; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  set A : Finset ℝ := insert (-1) (Tf.filter (· < s)) with hA
  set B : Finset ℝ := insert 2 (Tf.filter (s < ·)) with hB
  have hAne : A.Nonempty := ⟨-1, Finset.mem_insert_self _ _⟩
  have hBne : B.Nonempty := ⟨2, Finset.mem_insert_self _ _⟩
  set a := A.max' hAne with ha
  set b := B.min' hBne with hb
  have haA : a ∈ A := A.max'_mem hAne
  have hbB : b ∈ B := B.min'_mem hBne
  have has : a < s := by
    rcases Finset.mem_insert.1 haA with h | h
    · rw [h]; linarith [hs.1]
    · exact (Finset.mem_filter.1 h).2
  have hsb : s < b := by
    rcases Finset.mem_insert.1 hbB with h | h
    · rw [h]; linarith [hs.2]
    · exact (Finset.mem_filter.1 h).2
  refine ⟨p '' (Icc 0 1 ∩ Ioo a b), ⟨a, b, ?_, ?_, ?_, rfl⟩, ⟨s, ⟨hs, has, hsb⟩, rfl⟩⟩
  · rcases Finset.mem_insert.1 haA with h | h
    · exact Or.inl h
    · exact Or.inr ((hmemT a).1 (Finset.mem_filter.1 h).1)
  · rcases Finset.mem_insert.1 hbB with h | h
    · exact Or.inl h
    · exact Or.inr ((hmemT b).1 (Finset.mem_filter.1 h).1)
  · intro t ht hpt htab
    have htT : t ∈ Tf := (hmemT t).2 ⟨ht, hpt⟩
    rcases lt_trichotomy t s with hts | rfl | hst
    · have : t ∈ A := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨htT, hts⟩)
      exact absurd (A.le_max' t this) (not_le.2 htab.1)
    · exact hps hpt
    · have : t ∈ B := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨htT, hst⟩)
      exact absurd (B.min'_le t this) (not_le.2 htab.2)

/-! ### Pinch-finiteness for paths -/

/-- **Pinch-finiteness for paths.** If every real boundary value of a boundary map is real or lies on one of finitely
many continuous paths with finite fibres on `[0, 1]` whose ranges miss `F(ℍ)`, then every fibre of `F` on `ℍ̄` is
finite. -/
theorem finite_fibre_of_paths (hF : IsBoundaryMap F) {n : ℕ} {p : Fin n → ℝ → ℂ}
    (hp : ∀ k, ContinuousOn (p k) (Icc 0 1)) (hpf : ∀ k z, (p k ⁻¹' {z} ∩ Icc 0 1).Finite)
    (hpF : ∀ k, Disjoint (p k '' Icc 0 1) (F '' H))
    (hval : ∀ x : ℝ, (F x).im = 0 ∨ ∃ k, F x ∈ p k '' Icc 0 1) (z : ℂ) :
    (F ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := by
  refine finite_fibre_of_finite_real hF ?_
  have hRH : ∀ w : ℂ, w.im = 0 → w ∉ F '' H := by
    rintro w hw ⟨v, hv, he⟩
    have h1 : 0 < (F v).im := hF.2.2.2.1 hv
    rw [he, hw] at h1
    exact lt_irrefl 0 h1
  have hreal : ∀ G ∈ ({realGermL z, realGermR z} : Set (Set ℂ)), ∀ w ∈ G, w.im = 0 := by
    rintro G (rfl | rfl) w ⟨x, -, rfl⟩ <;> simp
  refine finite_real_fibre_of_finite_cover hF
    (𝒢 := {realGermL z, realGermR z} ∪ ⋃ k, pathGerms (p k) z)
    ((Set.toFinite _).union (Set.finite_iUnion fun k => finite_pathGerms (hpf k z))) ?_ ?_ ?_ ?_
  · rintro G (hG | hG)
    · rcases hG with rfl | rfl
      · exact isPreconnected_realGermL z
      · exact isPreconnected_realGermR z
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hG
      exact isPreconnected_of_mem_pathGerms (hp k) hk
  · rintro G (hG | hG)
    · rcases hG with rfl | rfl
      · exact notMem_realGermL z
      · exact notMem_realGermR z
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hG
      exact notMem_of_mem_pathGerms hk
  · rintro G (hG | hG)
    · exact Set.disjoint_left.2 fun w hw => hRH w (hreal G hG w hw)
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hG
      exact (hpF k).mono_left (subset_of_mem_pathGerms hk)
  · intro x hx
    rcases hval x with h0 | ⟨k, s, hs, hps⟩
    · have hre : (((F x).re : ℝ) : ℂ) = F x := Complex.ext (by simp) (by simp [h0])
      rcases mem_realGerm (z := z) (x := (F x).re) (by rw [hre]; exact hx) with h | h
      · exact ⟨_, Or.inl (Or.inl rfl), hre ▸ h⟩
      · exact ⟨_, Or.inl (Or.inr rfl), hre ▸ h⟩
    · obtain ⟨G, hG, hsG⟩ := exists_mem_pathGerms (hpf k z) hs (hps ▸ hx)
      exact ⟨G, Or.inr (Set.mem_iUnion.2 ⟨k, hG⟩), hps ▸ hsG⟩

/-! ### Charts -/

/-- The vertical approach to a real point, inside `ℍ`. -/
theorem tendsto_vertical (x : ℝ) :
    Tendsto (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * I) (𝓝[>] 0) (𝓝[H] (x : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hcont : Continuous (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * I) := by fun_prop
    have h := hcont.tendsto 0
    simp only [ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    show 0 < ((x : ℂ) + (ε : ℂ) * I).im
    simpa using hε

/-- **The continuous extension of a conformal chart inverse is a boundary map** once it is proper at `∞`. -/
theorem isBoundaryMap_of_isConformal {c : Chart} (hc : c.IsConformal) {g : ℂ → ℂ} (hgc : ContinuousOn g Hbar)
    (hgi : EqOn g c.2.1 H) (hinf : Tendsto g (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ)) : IsBoundaryMap g := by
  have himg : g '' H = c.2.1 '' H := image_congr fun w hw => hgi hw
  refine ⟨hc.1.congr fun w hw => hgi hw, hgc, fun a ha b hb h => hc.injOn ha hb (by rwa [← hgi ha, ← hgi hb]),
    fun w hw => (hgi hw).symm ▸ hc.2.1 hw, himg ▸ hc.isOpen_image, ?_, hinf⟩
  rintro x ⟨w, hw, hwx⟩
  have hcw : c.2.1 w ∈ c.dom := hc.inv_mem_dom hw
  have hcont : ContinuousAt c.1 (c.2.1 w) :=
    (hc.differentiableOn_fwd.differentiableAt (c.dom.isOpen.mem_nhds hcw)).continuousAt
  have hglim : Tendsto (fun ε : ℝ => g ((x : ℂ) + (ε : ℂ) * I)) (𝓝[>] 0) (𝓝 (c.2.1 w)) := by
    rw [← hgi hw, hwx]
    exact ((hgc _ (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)).tendsto.mono_left
      (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)).comp (tendsto_vertical x)
  have h1 : Tendsto (fun ε : ℝ => c.1 (g ((x : ℂ) + (ε : ℂ) * I))) (𝓝[>] 0) (𝓝 w) := by
    have := hcont.tendsto.comp hglim
    rwa [Function.comp_def, hc.2.2 w hw] at this
  have h2 : Tendsto (fun ε : ℝ => c.1 (g ((x : ℂ) + (ε : ℂ) * I))) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    refine ((tendsto_vertical x).mono_right nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hH : (x : ℂ) + (ε : ℂ) * I ∈ H := show 0 < ((x : ℂ) + (ε : ℂ) * I).im by simpa using hε
    rw [hgi hH, hc.2.2 _ hH]
  have hwx' : w = (x : ℂ) := tendsto_nhds_unique h1 h2
  have : (0 : ℝ) < w.im := hw
  rw [hwx'] at this
  simp at this

/-- **Pinch-finiteness for a left entry chart of a path with finite fibres** (the `hgf` hypothesis of Lemma S5,
`Erase.ErasureStep.relative`, and of SB2(1)'s `FinRel.exists_relConfig_of_path`). Let `A = p([0, 1])` for a continuous
path `p` with finite fibres on `[0, 1]` starting on `ℝ`, let `c` be a left entry chart of `A`, and let `g` be the
continuous extension of its inverse to `ℍ̄`. Then every fibre of `g` on `ℍ̄` is finite. -/
theorem finite_fibre_of_isLeftEntryChart {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : (p 0).im = 0)
    (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) {L : ℝ} {c : Chart}
    (hc : IsLeftEntryChart (p '' Icc 0 1) L c) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) : ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := by
  intro z
  have hAcpt : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  have hAc : IsPreconnected (p '' Icc 0 1 ∪ {z : ℂ | z.im ≤ 0}) :=
    (isPreconnected_Icc.image p hp).union (p 0) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      (show (p 0).im ≤ 0 by rw [hp0]) isPreconnected_lowerHalf
  obtain ⟨C₁, C₂, hC₁, hb⟩ := exists_norm_le_norm_g hc hAcpt.isBounded hAc hgc hgi
  have hM : 0 < max C₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hinf : Tendsto g (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 (tendsto_atTop_mono' _ ?_
      ((Tendsto.atTop_div_const hM (tendsto_atTop_add_const_right _ (-C₂)
        tendsto_norm_cobounded_atTop)).mono_left inf_le_left))
    refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
    have h1 := hb w (le_of_lt hw)
    have h2 : C₁ * ‖g w‖ ≤ max C₁ 1 * ‖g w‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    rw [div_le_iff₀ hM]
    linarith
  have hF := isBoundaryMap_of_isConformal hc.1.isConformal hgc hgi hinf
  have himg : g '' H = H \ fillH (p '' Icc 0 1) := by
    rw [image_congr fun w hw => hgi hw]; exact hc.1.image_eq
  refine finite_fibre_of_paths hF (p := fun _ : Fin 1 => p) (fun _ => hp) (fun _ => hpf) (fun _ => ?_) ?_ z
  · rw [himg]
    refine Set.disjoint_left.2 fun a ha haD => haD.2 ⟨haD.1, Or.inl (subset_closure ha)⟩
  · intro x
    rcases FinRel.g_ofReal_mem hc.1 hgc hgi x with h | h
    · rw [hAcpt.isClosed.closure_eq] at h
      exact Or.inr ⟨0, h⟩
    · exact Or.inl h
