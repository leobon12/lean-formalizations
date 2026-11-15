/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GSide
import InteractingSLE.Spec.Supplement.SBLemmaS2LiftSide
import InteractingSLE.Foundations.Loewner.CapacityEstimates

/-!
# Right-side approaches reach nonnegative real points only at the extreme one

Packet PROVE-T14-SB2FIN2 (Theorem 1.4's SB2, the `cusp` field of `IsRelConfigJC`). Setting of `SB2GSide`. Let
`q_M = γ(r_M) ≥ 0` be the largest nonnegative real point of `γ([0, s])` and `γ₂ = rayCurve γ r_M q_M` the curve `γ` on
`[0, r_M]` followed by the real ray `[q_M, ∞)`.

* `mem_leftSide_rayCurve_of_far`: points of `ℍ` outside a disc containing `γ([0, r_M])` are on the left side of `γ₂`
  (path: up, left, down into the lower-left quadrant).
* **`rightSide_rayCurve_subset_fillH`**: `rightSide γ₂ ∩ ℍ ⊆ fill γ([0, r_M])` (a component of `ℍ ∖ γ([0, r_M])`
  on the right side is bounded, since far points are on the left side).
* **`false_of_rightApproach`**: no real point `x > 0` right of the tip coordinate has `F(x) = γ(r)` with `r < r_M`:
  the approaches `F(y)`, `y → x`, lie on the right side of `extCurve` (`mem_rightSide_extCurve`), hence (the side
  principle `Supp9B.eventually_mem_leftSide_of_eqOn` near `γ(r)`, `r < r_M`) on the right side of `γ₂`, hence in
  `fill γ([0, r_M]) ⊆ K_u`, which the values of `F` on `ℍ` avoid.
* **`re_neg_of_im_eq_zero_of_lt`**: after `r_M` (up to `s`) every real point of `γ` is negative: `γ̂((r_M, ∞))` is
  connected, off the closed curve `γ₂` and unbounded in `ℍ`, so it lies on the left side of `γ₂`, while a point of
  `(0, q_M)` off `γ₂` lies on its right side.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric Bornology
open scoped NNReal
open QuantumZipper (H Hbar fwdMapInv fwdHull)
open InteractingSLE.Supp9B (IsProperCurve leftSide rightSide lowerLeft lowerRight)

namespace InteractingSLE.Theorem14.SB.FinRel

/-- The curve `γ` up to `r_M`, then the real ray from `q_M` to `+∞`. -/
def rayCurve (γ : ℝ≥0 → ℂ) (rM : ℝ≥0) (qM : ℝ) : ℝ≥0 → ℂ :=
  fun t => if t ≤ rM then γ t else ((qM + ((t : ℝ) - rM) : ℝ) : ℂ)

theorem rayCurve_of_le {γ : ℝ≥0 → ℂ} {rM t : ℝ≥0} {qM : ℝ} (ht : t ≤ rM) : rayCurve γ rM qM t = γ t := by
  simp only [rayCurve, ht, ↓reduceIte]

theorem rayCurve_of_lt {γ : ℝ≥0 → ℂ} {rM t : ℝ≥0} {qM : ℝ} (ht : rM < t) :
    rayCurve γ rM qM t = ((qM + ((t : ℝ) - rM) : ℝ) : ℂ) := by
  simp only [rayCurve, not_le.2 ht, ↓reduceIte]

section Ray

variable {γ : ℝ≥0 → ℂ} {rM : ℝ≥0} {qM : ℝ}

theorem isProperCurve_rayCurve (hγ : IsProperCurve γ) (hM : γ rM = qM)
    (hmax : ∀ t ≤ rM, (γ t).im = 0 → (γ t).re ≤ qM) : IsProperCurve (rayCurve γ rM qM) := by
  have hpos : ∀ t : ℝ≥0, rM < t → (0 : ℝ) < (t : ℝ) - rM := fun t ht => sub_pos.2 (NNReal.coe_lt_coe.2 ht)
  refine ⟨?_, ?_, fun t => ?_, ?_⟩
  · refine continuous_if_le (f := fun t : ℝ≥0 => t) (g := fun _ => rM) continuous_id continuous_const
      hγ.1.continuousOn (by fun_prop) fun t ht => ?_
    have ht' : t = rM := ht
    rw [ht', hM, sub_self, add_zero]
  · intro t₁ t₂ he
    rcases le_or_gt t₁ rM with h₁ | h₁ <;> rcases le_or_gt t₂ rM with h₂ | h₂
    · rw [rayCurve_of_le h₁, rayCurve_of_le h₂] at he; exact hγ.2.1 he
    · rw [rayCurve_of_le h₁, rayCurve_of_lt h₂] at he
      have := hmax t₁ h₁ (by rw [he]; simp)
      rw [he, ofReal_re] at this
      linarith [hpos t₂ h₂]
    · rw [rayCurve_of_lt h₁, rayCurve_of_le h₂] at he
      have := hmax t₂ h₂ (by rw [← he]; simp)
      rw [← he, ofReal_re] at this
      linarith [hpos t₁ h₁]
    · rw [rayCurve_of_lt h₁, rayCurve_of_lt h₂, ofReal_inj] at he
      exact NNReal.coe_injective (by linarith)
  · rcases le_or_gt t rM with ht | ht
    · rw [rayCurve_of_le ht]; exact hγ.2.2.1 t
    · rw [rayCurve_of_lt ht, ofReal_im]
  · have hlow : Tendsto (fun t : ℝ≥0 => (t : ℝ) + (qM - rM)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (NNReal.tendsto_coe_atTop.2 tendsto_id)
    refine tendsto_atTop_mono' _ ?_ hlow
    filter_upwards [eventually_gt_atTop rM] with t ht
    rw [rayCurve_of_lt ht, norm_real, Real.norm_eq_abs]
    exact le_trans (le_of_eq (by ring)) (le_abs_self _)

/-- **Far points of `ℍ` are on the left side of the ray-completed curve.** -/
theorem mem_leftSide_rayCurve_of_far (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hM : γ rM = qM)
    (hmax : ∀ t ≤ rM, (γ t).im = 0 → (γ t).re ≤ qM) (hq : 0 ≤ qM) {B : ℝ} (hB : ∀ t ≤ rM, ‖γ t‖ ≤ B)
    {w : ℂ} (hw : w ∈ H) (hwB : B < ‖w‖) : w ∈ leftSide (rayCurve γ rM qM) := by
  have hP := isProperCurve_rayCurve hγ hM hmax
  have h0 : rayCurve γ rM qM 0 = 0 := by rw [rayCurve_of_le zero_le]; exact hγ0
  have hwim : 0 < w.im := hw
  have hoff : ∀ z : ℂ, B < ‖z‖ → (0 < z.im ∨ z.re < 0) → z ∉ seedRayClosure (rayCurve γ rM qM) := by
    intro z hzB hz hmem
    rcases hmem with ⟨τ, hτ⟩ | ⟨hre, him⟩
    · rcases le_or_gt τ rM with hτr | hτr
      · rw [rayCurve_of_le hτr] at hτ
        have := hB τ hτr
        rw [hτ] at this
        linarith
      · rw [rayCurve_of_lt hτr] at hτ
        have hp : (0 : ℝ) < (τ : ℝ) - rM := sub_pos.2 (NNReal.coe_lt_coe.2 hτr)
        rcases hz with hz | hz
        · rw [← hτ, ofReal_im] at hz; exact lt_irrefl _ hz
        · rw [← hτ, ofReal_re] at hz; linarith
    · rw [h0] at hre him
      simp only [zero_re, zero_im] at hre him
      rcases hz with hz | hz <;> linarith
  set K : ℝ := |B| + 1 with hK
  set N : ℝ := |B| + |w.re| + 1 with hN
  have hKpos : 0 < K := by positivity
  have hNpos : 0 < N := by positivity
  have hBK : B < K := by rw [hK]; linarith [le_abs_self B]
  have hBN : B < N := by rw [hN]; linarith [le_abs_self B, abs_nonneg w.re]
  set P₁ := (fun t : ℝ => w + (t : ℂ) * I) '' Icc 0 K with hP₁
  set P₂ := (fun τ : ℝ => (τ : ℂ) + ((w.im + K : ℝ) : ℂ) * I) '' uIcc (-N) w.re with hP₂
  set P₃ := (fun τ : ℝ => ((-N : ℝ) : ℂ) + (τ : ℂ) * I) '' Icc (-1) (w.im + K) with hP₃
  have hc₁ : IsPreconnected P₁ := isPreconnected_Icc.image _ (by fun_prop)
  have hc₂ : IsPreconnected P₂ := isPreconnected_uIcc.image _ (by fun_prop)
  have hc₃ : IsPreconnected P₃ := isPreconnected_Icc.image _ (by fun_prop)
  have he₁₂ : w + (K : ℂ) * I = (w.re : ℂ) + ((w.im + K : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hm₁₂ : w + (K : ℂ) * I ∈ P₁ ∩ P₂ := ⟨⟨K, ⟨hKpos.le, le_rfl⟩, rfl⟩, ⟨w.re, right_mem_uIcc, he₁₂.symm⟩⟩
  have hm₂₃ : ((-N : ℝ) : ℂ) + ((w.im + K : ℝ) : ℂ) * I ∈ (P₁ ∪ P₂) ∩ P₃ :=
    ⟨Or.inr ⟨-N, left_mem_uIcc, rfl⟩, ⟨w.im + K, ⟨by linarith, le_rfl⟩, rfl⟩⟩
  have hS : IsPreconnected (P₁ ∪ P₂ ∪ P₃) :=
    (hc₁.union _ hm₁₂.1 hm₁₂.2 hc₂).union _ hm₂₃.1 hm₂₃.2 hc₃
  have hSsub : P₁ ∪ P₂ ∪ P₃ ⊆ (seedRayClosure (rayCurve γ rM qM))ᶜ := by
    rintro z ((⟨t, ht, rfl⟩ | ⟨τ, hτ, rfl⟩) | ⟨τ, hτ, rfl⟩)
    · have him : (w + (t : ℂ) * I).im = w.im + t := by simp
      refine hoff _ ?_ (Or.inl (by rw [him]; linarith [ht.1]))
      have h1 : ‖w‖ ^ 2 ≤ ‖w + (t : ℂ) * I‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, him]
        have hre : (w + (t : ℂ) * I).re = w.re := by simp
        rw [hre]
        nlinarith [ht.1]
      nlinarith [norm_nonneg w, norm_nonneg (w + (t : ℂ) * I)]
    · have him : ((τ : ℂ) + ((w.im + K : ℝ) : ℂ) * I).im = w.im + K := by simp
      refine hoff _ ?_ (Or.inl (by rw [him]; linarith))
      have := Complex.abs_im_le_norm ((τ : ℂ) + ((w.im + K : ℝ) : ℂ) * I)
      rw [him, abs_of_pos (by linarith)] at this
      linarith
    · have hre : (((-N : ℝ) : ℂ) + (τ : ℂ) * I).re = -N := by simp
      refine hoff _ ?_ (Or.inr (by rw [hre]; linarith))
      have := Complex.abs_re_le_norm (((-N : ℝ) : ℂ) + (τ : ℂ) * I)
      rw [hre, abs_neg, abs_of_pos hNpos] at this
      linarith
  have hmw : w ∈ P₁ ∪ P₂ ∪ P₃ := Or.inl (Or.inl ⟨0, ⟨le_rfl, hKpos.le⟩, by simp⟩)
  have hmL : ((-N : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I ∈ P₁ ∪ P₂ ∪ P₃ :=
    Or.inr ⟨-1, ⟨le_rfl, by linarith⟩, rfl⟩
  have hL : ((-N : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I ∈ leftSide (rayCurve γ rM qM) := by
    refine Supp9B.lowerLeft_subset_leftSide hP.2.2.1 (by rw [h0]; rfl) ⟨?_, ?_⟩
    · rw [h0]
      have : (((-N : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I).re = -N := by simp
      rw [this, zero_re]; linarith
    · simp
  rw [Supp9B.leftSide, connectedComponentIn_eq hL]
  exact hS.subset_connectedComponentIn hmL hSsub hmw

/-- **The right side of the ray-completed curve meets `ℍ` only inside `fill γ([0, r_M])`.** -/
theorem rightSide_rayCurve_subset_fillH (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hM : γ rM = qM)
    (hmax : ∀ t ≤ rM, (γ t).im = 0 → (γ t).re ≤ qM) (hq : 0 ≤ qM) {z : ℂ}
    (hz : z ∈ rightSide (rayCurve γ rM qM)) (hzH : z ∈ H) : z ∈ fillH (γ '' Icc 0 rM) := by
  have hP := isProperCurve_rayCurve hγ hM hmax
  have h0 : rayCurve γ rM qM 0 = 0 := by rw [rayCurve_of_le zero_le]; exact hγ0
  set Y := γ '' Icc 0 rM with hY
  have hYc : IsCompact Y := isCompact_Icc.image hγ.1
  obtain ⟨B, hB⟩ := hYc.isBounded.exists_norm_le
  have hB' : ∀ t ≤ rM, ‖γ t‖ ≤ B := fun t ht => hB _ ⟨t, ⟨zero_le, ht⟩, rfl⟩
  have hYγ : Y ⊆ seedRayClosure (rayCurve γ rM qM) := by
    rintro _ ⟨t, ht, rfl⟩
    exact Or.inl ⟨t, by rw [rayCurve_of_le ht.2]⟩
  have hzS : z ∉ seedRayClosure (rayCurve γ rM qM) := connectedComponentIn_subset _ _ hz
  have hzY : z ∉ Y := fun h => hzS (hYγ h)
  refine ⟨hzH, Or.inr ?_⟩
  rw [hYc.isClosed.closure_eq]
  by_contra hunb
  set Cz := connectedComponentIn (H \ Y) z with hCz
  have hsub : Cz ⊆ (seedRayClosure (rayCurve γ rM qM))ᶜ := by
    intro w hw hmem
    have hw' := connectedComponentIn_subset _ _ hw
    have hwim : 0 < w.im := hw'.1
    rcases hmem with ⟨τ, hτ⟩ | ⟨-, him⟩
    · rcases le_or_gt τ rM with hτr | hτr
      · rw [rayCurve_of_le hτr] at hτ
        exact hw'.2 ⟨τ, ⟨zero_le, hτr⟩, hτ⟩
      · rw [rayCurve_of_lt hτr] at hτ
        rw [← hτ, ofReal_im] at hwim
        exact lt_irrefl _ hwim
    · rw [h0, zero_im] at him
      linarith
  have hCR : Cz ⊆ rightSide (rayCurve γ rM qM) := by
    have hzm : z ∈ H \ Y := ⟨hzH, hzY⟩
    have := (isPreconnected_connectedComponentIn (F := H \ Y) (x := z)).subset_connectedComponentIn
      (mem_connectedComponentIn hzm) hsub
    rwa [← connectedComponentIn_eq hz] at this
  obtain ⟨w, hwC, hwB⟩ : ∃ w ∈ Cz, B < ‖w‖ := by
    by_contra h
    exact hunb (isBounded_iff_forall_norm_le.2 ⟨B, fun w hw => not_lt.1 fun hlt => h ⟨w, hw, hlt⟩⟩)
  have hwH : w ∈ H := (connectedComponentIn_subset _ _ hwC).1
  have hwL := mem_leftSide_rayCurve_of_far hγ hγ0 hM hmax hq hB' hwH hwB
  exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hP (by rw [h0]; rfl)) hwL (hCR hwC)

/-- The largest nonnegative real point of `γ([0, s])`. -/
theorem exists_realMax (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (s : ℝ≥0) :
    ∃ rM ≤ s, (γ rM).im = 0 ∧ 0 ≤ (γ rM).re ∧ ∀ t ≤ s, (γ t).im = 0 → (γ t).re ≤ (γ rM).re := by
  set T := {t ∈ Icc 0 s | (γ t).im = 0 ∧ 0 ≤ (γ t).re} with hT
  have hTc : IsCompact T := isCompact_Icc.inter_right
    ((isClosed_eq (continuous_im.comp hγ.1) continuous_const).inter
      (isClosed_le continuous_const (continuous_re.comp hγ.1)))
  have h0T : (0 : ℝ≥0) ∈ T := ⟨⟨le_rfl, zero_le⟩, by rw [hγ0]; simp, by rw [hγ0]; simp⟩
  obtain ⟨rM, hrM, hmax⟩ := hTc.exists_isMaxOn ⟨0, h0T⟩ (continuous_re.comp hγ.1).continuousOn
  refine ⟨rM, hrM.1.2, hrM.2.1, hrM.2.2, fun t ht him => ?_⟩
  by_cases hre : 0 ≤ (γ t).re
  · exact hmax ⟨⟨zero_le, ht⟩, him, hre⟩
  · linarith [hrM.2.2]

end Ray

section RightApproach

variable {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {γ : ℝ≥0 → ℂ} {u : ℝ} {s rM : ℝ≥0} {qM : ℝ}

/-- **No right-side approach to a real point before the extreme one.** -/
theorem false_of_rightApproach (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hu : 0 ≤ u) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hηu : ηr u = γ s)
    (hK : fwdHull Wr u = fillH (γ '' Icc 0 s)) (hrM : rM ≤ s) (hM : γ rM = qM) (hq : 0 ≤ qM)
    (hmax : ∀ t ≤ s, (γ t).im = 0 → (γ t).re ≤ qM) {x : ℝ} (hx : 0 < x) {r : ℝ≥0} (hr : r < rM)
    (hFx : extendFrom H (fwdMapInv Wr u) x = γ r) : False := by
  set F := extendFrom H (fwdMapInv Wr u) with hF
  obtain ⟨-, hFc, -, -⟩ := hηr.fiber_hyps hWr hWr0 hu
  have hmax' : ∀ t ≤ rM, (γ t).im = 0 → (γ t).re ≤ qM := fun t ht => hmax t (ht.trans hrM)
  have hP₂ := isProperCurve_rayCurve hγ hM hmax'
  have hP := isProperCurve_extCurve hηr hWr hWr0 hu hγ hηu hK
  have h0 : rayCurve γ rM qM 0 = 0 := by rw [rayCurve_of_le zero_le]; exact hγ0
  have hside := Supp9B.eventually_mem_leftSide_of_eqOn hP₂ hP (by rw [h0]; rfl)
    (fun t ht => by rw [extCurve_of_le (ht.trans hrM), rayCurve_of_le ht]) hr
  rw [rayCurve_of_le hr.le] at hside
  have hxb : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hlim : Tendsto F (𝓝[H] (x : ℂ)) (𝓝 (γ r)) := by
    rw [← hFx]
    exact ((hFc _ hxb).mono QuantumZipper.H_subset_Hbar).tendsto
  have hne : (𝓝[H] (x : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hxb)
  have hre : ∀ᶠ y in 𝓝[H] (x : ℂ), 0 < y.re :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const continuous_re).mem_nhds (by simpa using hx))
  obtain ⟨y, hyL, hyre, hyH⟩ := ((hlim.eventually hside).and (hre.and self_mem_nhdsWithin)).exists
  have hFyR := mem_rightSide_extCurve hηr hWr hWr0 hu hγ hγ0 hηu hK hyH hyre
  have hFyL : F y ∉ leftSide (rayCurve γ rM qM) := fun h =>
    Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hP (by rw [extCurve_of_le zero_le, hγ0]; rfl))
      (hyL h) hFyR
  have hFyH : F y ∈ H := by
    rw [hF, ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hyH]
    exact QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hyH
  have hFyS : F y ∉ seedRayClosure (rayCurve γ rM qM) := by
    rintro (⟨τ, hτ⟩ | ⟨-, him⟩)
    · rcases le_or_gt τ rM with hτr | hτr
      · rw [rayCurve_of_le hτr] at hτ
        exact fwdMapInv_ne_of_le hWr hWr0 hu hK hyH (hτr.trans hrM) hτ.symm
      · rw [rayCurve_of_lt hτr] at hτ
        have : 0 < (F y).im := hFyH
        rw [← hτ, ofReal_im] at this
        exact lt_irrefl _ this
    · rw [h0, zero_im] at him
      have : 0 < (F y).im := hFyH
      linarith
  have hFyR₂ : F y ∈ rightSide (rayCurve γ rM qM) := by
    have hc : F y ∈ (seedRayClosure (rayCurve γ rM qM))ᶜ := hFyS
    rw [Supp9B.compl_seedRayClosure_eq hP₂ (by rw [h0]; rfl)] at hc
    exact hc.resolve_left hFyL
  have hfill := fillH_mono (image_mono (Icc_subset_Icc_right hrM))
    (rightSide_rayCurve_subset_fillH hγ hγ0 hM hmax' hq hFyR₂ hFyH)
  rw [← hK] at hfill
  have hm : fwdMapInv Wr u y ∈ H \ fwdHull Wr u := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hWr hWr0 hu]; exact ⟨y, hyH, rfl⟩
  rw [hF, ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hyH] at hfill
  exact hm.2 hfill

/-- **After the extreme time, the real points of `γ` (up to `s`) are negative.** -/
theorem re_neg_of_im_eq_zero_of_lt (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hu : 0 ≤ u) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hηu : ηr u = γ s)
    (hK : fwdHull Wr u = fillH (γ '' Icc 0 s)) (hrM : rM ≤ s) (hM : γ rM = qM) (hq : 0 ≤ qM)
    (hmax : ∀ t ≤ s, (γ t).im = 0 → (γ t).re ≤ qM) {r : ℝ≥0} (hr : rM < r) (hrs : r ≤ s)
    (him : (γ r).im = 0) : (γ r).re < 0 := by
  by_contra hge
  rw [not_lt] at hge
  have hmax' : ∀ t ≤ rM, (γ t).im = 0 → (γ t).re ≤ qM := fun t ht => hmax t (ht.trans hrM)
  have hP₂ := isProperCurve_rayCurve hγ hM hmax'
  have hP := isProperCurve_extCurve hηr hWr hWr0 hu hγ hηu hK
  have h0 : rayCurve γ rM qM 0 = 0 := by rw [rayCurve_of_le zero_le]; exact hγ0
  have hγr : γ r = (((γ r).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hne0 : (γ r).re ≠ 0 := by
    intro h
    have : γ r = γ 0 := by rw [hγ0, hγr, h, ofReal_zero]
    have := hγ.2.1 this
    rw [this] at hr
    exact absurd hr (not_lt.2 zero_le)
  have hneq : (γ r).re ≠ qM := by
    intro h
    have : γ r = γ rM := by rw [hM, hγr, h]
    exact absurd (hγ.2.1 this) hr.ne'
  have hlt : (γ r).re < qM := lt_of_le_of_ne (hmax r hrs him) hneq
  have hpos : 0 < (γ r).re := lt_of_le_of_ne hge (Ne.symm hne0)
  -- the real point is on the right side of the ray-completed curve
  have hR : (((γ r).re : ℝ) : ℂ) ∈ rightSide (rayCurve γ rM qM) := by
    refine SB.ofReal_mem_rightSide_of_gt hP₂ (by rw [h0]; rfl) (by rw [h0, zero_re]; exact hpos) ?_
    rintro (⟨τ, hτ⟩ | ⟨hre, -⟩)
    · rcases le_or_gt τ rM with hτr | hτr
      · rw [rayCurve_of_le hτr, ← hγr] at hτ
        exact absurd (hγ.2.1 hτ) (ne_of_lt (lt_of_le_of_lt hτr hr))
      · rw [rayCurve_of_lt hτr, ofReal_inj] at hτ
        have : (0 : ℝ) < (τ : ℝ) - rM := sub_pos.2 (NNReal.coe_lt_coe.2 hτr)
        linarith
    · rw [h0, zero_re, ofReal_re] at hre
      exact hne0 hre
  -- the continued curve after `r_M` is on the left side
  have hoff : extCurve Wr u γ s '' Ioi rM ⊆ (seedRayClosure (rayCurve γ rM qM))ᶜ := by
    rintro _ ⟨t, ht, rfl⟩ (⟨τ, hτ⟩ | ⟨hre, him'⟩)
    · have htr : rM < t := ht
      rcases le_or_gt τ rM with hτr | hτr
      · rw [rayCurve_of_le hτr] at hτ
        rcases le_or_gt t s with hts | hts
        · rw [extCurve_of_le hts] at hτ
          exact absurd (hγ.2.1 hτ) (ne_of_lt (lt_of_le_of_lt hτr htr))
        · rw [extCurve_of_lt hts] at hτ
          have hp : (0 : ℝ) < (t : ℝ) - s := sub_pos.2 (NNReal.coe_lt_coe.2 hts)
          exact fwdMapInv_ne_of_le hWr hWr0 hu hK (mul_I_mem_H hp) (hτr.trans hrM) hτ.symm
      · rw [rayCurve_of_lt hτr] at hτ
        have hp : (0 : ℝ) < (τ : ℝ) - rM := sub_pos.2 (NNReal.coe_lt_coe.2 hτr)
        rcases le_or_gt t s with hts | hts
        · rw [extCurve_of_le hts] at hτ
          have h1 := hmax t hts (by rw [← hτ, ofReal_im])
          rw [← hτ, ofReal_re] at h1
          linarith
        · have h1 : 0 < (extCurve Wr u γ s t).im := im_extCurve_pos hWr hWr0 hu hts
          rw [← hτ, ofReal_im] at h1
          exact lt_irrefl _ h1
    · rw [h0] at hre him'
      have him0 : (extCurve Wr u γ s t).im = 0 := le_antisymm (by simpa using him') (hP.2.2.1 t)
      have hz : extCurve Wr u γ s t = extCurve Wr u γ s 0 := by
        rw [extCurve_of_le zero_le, hγ0]
        exact Complex.ext (by simpa using hre) (by simpa using him0)
      have := hP.2.1 hz
      rw [this] at ht
      exact absurd (show rM < 0 from ht) (not_lt.2 zero_le)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image hγ.1 : IsCompact (γ '' Icc (0 : ℝ≥0) rM)).isBounded.exists_norm_le
  have hB' : ∀ t ≤ rM, ‖γ t‖ ≤ B := fun t ht => hB _ ⟨t, ⟨zero_le, ht⟩, rfl⟩
  obtain ⟨t, htB, hts⟩ := ((hP.2.2.2.eventually (eventually_gt_atTop B)).and (eventually_gt_atTop s)).exists
  have htL := mem_leftSide_rayCurve_of_far hγ hγ0 hM hmax' hq hB' (im_extCurve_pos hWr hWr0 hu hts) htB
  have hG : extCurve Wr u γ s '' Ioi rM ⊆ leftSide (rayCurve γ rM qM) := by
    have := (isPreconnected_Ioi.image _ hP.1.continuousOn).subset_connectedComponentIn
      (⟨t, show rM < t from lt_of_le_of_lt hrM hts, rfl⟩ : extCurve Wr u γ s t ∈ extCurve Wr u γ s '' Ioi rM) hoff
    rwa [← connectedComponentIn_eq htL] at this
  have hL : γ r ∈ leftSide (rayCurve γ rM qM) := by
    have := hG ⟨r, hr, rfl⟩
    rwa [extCurve_of_le hrs] at this
  rw [hγr] at hL
  exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hP₂ (by rw [h0]; rfl)) hL hR

end RightApproach

end InteractingSLE.Theorem14.SB.FinRel
