/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GFibre
import InteractingSLE.Spec.Supplement.S9BSide

/-!
# The relative curve continued along the tip ray; sides of the approaches

Packet PROVE-T14-SB2FIN2 (Theorem 1.4's SB2, the `cusp` field of `IsRelConfigJC`). Let `ηr` be a Loewner trace of a
continuous driver `Wr` (`Wr 0 = 0`), `u ≥ 0`, and let `γ` be a proper curve from `0` with `ηr(u) = γ(s)` and
`K_u = fill γ([0, s])`. Write `F = extendFrom ℍ (F_u)` (the centred inverse map, tip coordinate `0`).

* **`extCurve`**: `γ̂ = γ` on `[0, s]`, then `F(i(t − s))` — the image of the vertical ray over the tip coordinate.
  **`isProperCurve_extCurve`**: `γ̂` is a proper curve; it has no real point after `s` (`im_extCurve_pos`).
* **`mem_leftSide_extCurve`** / **`mem_rightSide_extCurve`**: for `y ∈ ℍ` with `Re y < 0` (resp. `> 0`), `F(y)` lies on
  the open left (resp. right) side of `γ̂`.

Proof of the side lemma: join `y` horizontally and then vertically to a far real point `x'` on the same side
(`|x'|` larger than the hull and the displacement bound `‖F z − z‖ ≤ C`), so that `F(x')` is real, far from `γ([0, s])`,
and on the same side of `0`; continue straight down into the lower half-plane. The `F`-image of the path stays in
`ℍ ∖ K_u` and off `F(iℝ₊)` (injectivity of `F` on `ℍ`, the path misses the imaginary axis), the last segment misses the
curve (real or negative imaginary parts) and the seed ray (real part `≠ 0`). It ends in the lower-left (resp.
lower-right) quadrant, which lies on the left (resp. right) side. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric Bornology
open scoped NNReal
open QuantumZipper (H Hbar fwdMapInv fwdHull)
open InteractingSLE.Supp9B (IsProperCurve leftSide rightSide lowerLeft lowerRight)

namespace InteractingSLE.Theorem14.SB.FinRel

/-- **The relative curve continued along the tip ray**: `γ` on `[0, s]`, then the image of the vertical ray over the
tip coordinate under the extended inverse map of time `u`. -/
def extCurve (Wr : ℝ → ℝ) (u : ℝ) (γ : ℝ≥0 → ℂ) (s : ℝ≥0) : ℝ≥0 → ℂ :=
  fun t => if t ≤ s then γ t else extendFrom H (fwdMapInv Wr u) ((((t : ℝ) - s : ℝ) : ℂ) * I)

theorem extCurve_of_le {Wr : ℝ → ℝ} {u : ℝ} {γ : ℝ≥0 → ℂ} {s t : ℝ≥0} (ht : t ≤ s) :
    extCurve Wr u γ s t = γ t := by
  simp only [extCurve, ht, ↓reduceIte]

theorem extCurve_of_lt {Wr : ℝ → ℝ} {u : ℝ} {γ : ℝ≥0 → ℂ} {s t : ℝ≥0} (ht : s < t) :
    extCurve Wr u γ s t = extendFrom H (fwdMapInv Wr u) ((((t : ℝ) - s : ℝ) : ℂ) * I) := by
  simp only [extCurve, not_le.2 ht, ↓reduceIte]

theorem mul_I_mem_H {r : ℝ} (hr : 0 < r) : (r : ℂ) * I ∈ H := by
  show 0 < ((r : ℂ) * I).im
  simpa using hr

section Ext

variable {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {γ : ℝ≥0 → ℂ} {u : ℝ} {s : ℝ≥0}

/-- Values of the inverse map on `ℍ` are not points of `γ([0, s])`. -/
theorem fwdMapInv_ne_of_le (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hK : fwdHull Wr u = fillH (γ '' Icc 0 s)) {z : ℂ} (hz : z ∈ H) {t : ℝ≥0} (ht : t ≤ s) :
    extendFrom H (fwdMapInv Wr u) z ≠ γ t := by
  intro he
  rw [ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hz] at he
  have hm : fwdMapInv Wr u z ∈ H \ fwdHull Wr u := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hWr hWr0 hu]; exact ⟨z, hz, rfl⟩
  rw [he, hK] at hm
  exact hm.2 ⟨hm.1, Or.inl (subset_closure ⟨t, ⟨zero_le, ht⟩, rfl⟩)⟩

/-- The inverse map moves points of `ℍ̄` by a bounded amount. -/
theorem exists_norm_extendFrom_sub_le (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hu : 0 ≤ u) : ∃ C, ∀ w ∈ Hbar, ‖extendFrom H (fwdMapInv Wr u) w - w‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hWr hWr0 hu
  obtain ⟨-, hFc, -, -⟩ := hηr.fiber_hyps hWr hWr0 hu
  refine ⟨C, fun w hw => ?_⟩
  have hcl : w ∈ closure H := by rw [closure_H]; exact hw
  have hlim : Tendsto (fun z => extendFrom H (fwdMapInv Wr u) z - z) (𝓝[H] w)
      (𝓝 (extendFrom H (fwdMapInv Wr u) w - w)) :=
    (((hFc w hw).mono QuantumZipper.H_subset_Hbar).tendsto).sub
      (tendsto_id.mono_left nhdsWithin_le_nhds)
  have : (𝓝[H] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  refine le_of_tendsto hlim.norm (eventually_nhdsWithin_of_forall fun z hz => ?_)
  rw [ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hz]
  exact hC z hz

/-- After `s` the continued curve lies in `ℍ`. -/
theorem im_extCurve_pos (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u) {t : ℝ≥0} (ht : s < t) :
    extCurve Wr u γ s t ∈ H := by
  have hts : (0 : ℝ) < (t : ℝ) - s := sub_pos.2 (NNReal.coe_lt_coe.2 ht)
  rw [extCurve_of_lt ht, ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu (mul_I_mem_H hts)]
  exact QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu (mul_I_mem_H hts)

/-- **The continued curve is a proper curve.** -/
theorem isProperCurve_extCurve (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hγ : IsProperCurve γ) (hηu : ηr u = γ s) (hK : fwdHull Wr u = fillH (γ '' Icc 0 s)) :
    IsProperCurve (extCurve Wr u γ s) := by
  set F := extendFrom H (fwdMapInv Wr u) with hF
  obtain ⟨-, hFc, hFi, -⟩ := hηr.fiber_hyps hWr hWr0 hu
  have hF0 : F 0 = γ s := (hηr.loewnerTip_eq hWr hWr0 hu).trans hηu
  have hsub : ∀ t : ℝ≥0, s < t → (0 : ℝ) < (t : ℝ) - s := fun t ht => sub_pos.2 (NNReal.coe_lt_coe.2 ht)
  refine ⟨?_, ?_, fun t => ?_, ?_⟩
  · refine continuous_if_le (f := fun t : ℝ≥0 => t) (g := fun _ => s) continuous_id continuous_const
      hγ.1.continuousOn ?_ ?_
    · refine hFc.comp (by fun_prop) fun t (ht : s ≤ t) => ?_
      show (0 : ℝ) ≤ (((((t : ℝ) - s : ℝ) : ℂ) * I)).im
      simpa using NNReal.coe_le_coe.2 ht
    · intro t ht
      have ht' : t = s := ht
      rw [ht', sub_self, ofReal_zero, zero_mul]; exact hF0.symm
  · intro t₁ t₂ he
    rcases le_or_gt t₁ s with h₁ | h₁ <;> rcases le_or_gt t₂ s with h₂ | h₂
    · rw [extCurve_of_le h₁, extCurve_of_le h₂] at he; exact hγ.2.1 he
    · rw [extCurve_of_le h₁, extCurve_of_lt h₂] at he
      exact absurd he.symm (fwdMapInv_ne_of_le hWr hWr0 hu hK (mul_I_mem_H (hsub t₂ h₂)) h₁)
    · rw [extCurve_of_lt h₁, extCurve_of_le h₂] at he
      exact absurd he (fwdMapInv_ne_of_le hWr hWr0 hu hK (mul_I_mem_H (hsub t₁ h₁)) h₂)
    · rw [extCurve_of_lt h₁, extCurve_of_lt h₂] at he
      have h := congrArg Complex.im (hFi (mul_I_mem_H (hsub t₁ h₁)) (mul_I_mem_H (hsub t₂ h₂)) he)
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at h
      exact NNReal.coe_injective (by linarith)
  · rcases le_or_gt t s with ht | ht
    · rw [extCurve_of_le ht]; exact hγ.2.2.1 t
    · exact (im_extCurve_pos hWr hWr0 hu ht).le
  · obtain ⟨C, hC⟩ := exists_norm_extendFrom_sub_le hηr hWr hWr0 hu
    have hlow : Tendsto (fun t : ℝ≥0 => (t : ℝ) + (-(s : ℝ) - C)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (NNReal.tendsto_coe_atTop.2 tendsto_id)
    refine tendsto_atTop_mono' _ ?_ hlow
    filter_upwards [eventually_gt_atTop s] with t ht
    rw [extCurve_of_lt ht]
    have hz := hC _ (QuantumZipper.H_subset_Hbar (mul_I_mem_H (hsub t ht)))
    have hn : ‖(((t : ℝ) - s : ℝ) : ℂ) * I‖ = (t : ℝ) - s := by
      rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (hsub t ht)]
    have := norm_sub_norm_le (F ((((t : ℝ) - s : ℝ) : ℂ) * I)) ((((t : ℝ) - s : ℝ) : ℂ) * I)
    have h2 := norm_sub_rev (F ((((t : ℝ) - s : ℝ) : ℂ) * I)) ((((t : ℝ) - s : ℝ) : ℂ) * I)
    have h3 := norm_sub_norm_le ((((t : ℝ) - s : ℝ) : ℂ) * I) (F ((((t : ℝ) - s : ℝ) : ℂ) * I))
    linarith

/-- Far out on the real line the extended inverse map is real and within the displacement bound. -/
theorem exists_far_real (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u) :
    ∃ R C : ℝ, ∀ x : ℝ, R ≤ |x| → (extendFrom H (fwdMapInv Wr u) x).im = 0 ∧
      |(extendFrom H (fwdMapInv Wr u) x).re - x| ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_extendFrom_sub_le hηr hWr hWr0 hu
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn
    (hηr.2.1.mono fun r (hr : r ∈ Icc 0 u) => hr.1)).isBounded.exists_norm_le
  refine ⟨|M| + |C| + 1, C, fun x hx => ?_⟩
  have hd := hC x (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)
  have hre : |(extendFrom H (fwdMapInv Wr u) x).re - x| ≤ C := by
    have := Complex.abs_re_le_norm (extendFrom H (fwdMapInv Wr u) x - x)
    simp only [sub_re, ofReal_re] at this
    linarith
  refine ⟨?_, hre⟩
  rcases WalkNorm.extendFrom_real_cases hηr hWr hWr0 hu x with h | ⟨r, hr, he⟩
  · exact h
  · have h1 := hM _ ⟨r, hr, he⟩
    have h2 := norm_sub_norm_le (x : ℂ) (extendFrom H (fwdMapInv Wr u) x)
    rw [norm_real, Real.norm_eq_abs, norm_sub_rev] at h2
    linarith [le_abs_self M, le_abs_self C]

/-- **The path argument**: `F(y)` and `F(x') − i` lie in one component of the complement of the closed continued
curve, when the horizontal segment from `y` to `Re = x'` misses the imaginary axis and `F(x')` is a real point off
`γ([0, s])` with nonzero real part. -/
theorem mem_component_extCurve (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hu : 0 ≤ u) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hηu : ηr u = γ s)
    (hK : fwdHull Wr u = fillH (γ '' Icc 0 s)) {y : ℂ} (hy : y ∈ H) {x' : ℝ}
    (hsign : ∀ t ∈ uIcc x' y.re, t ≠ 0) (hx'im : (extendFrom H (fwdMapInv Wr u) x').im = 0)
    (hx're : (extendFrom H (fwdMapInv Wr u) x').re ≠ 0)
    (hx'γ : ∀ t ≤ s, γ t ≠ extendFrom H (fwdMapInv Wr u) x') :
    extendFrom H (fwdMapInv Wr u) y ∈
      connectedComponentIn (seedRayClosure (extCurve Wr u γ s))ᶜ (extendFrom H (fwdMapInv Wr u) x' - I) := by
  set F := extendFrom H (fwdMapInv Wr u) with hF
  obtain ⟨-, hFc, hFi, -⟩ := hηr.fiber_hyps hWr hWr0 hu
  set γ' := extCurve Wr u γ s with hγ'
  have hP := isProperCurve_extCurve hηr hWr hWr0 hu hγ hηu hK
  have hγ'0 : γ' 0 = 0 := by rw [hγ', extCurve_of_le zero_le]; exact hγ0
  have hoffH : ∀ w ∈ H, w.re ≠ 0 → F w ∉ seedRayClosure γ' := by
    intro w hw hwre hmem
    have hFw : F w ∈ H := by
      rw [hF, ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hw]
      exact QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hw
    rcases hmem with ⟨t, ht⟩ | ⟨-, him⟩
    · rcases le_or_gt t s with hts | hts
      · rw [hγ', extCurve_of_le hts] at ht
        exact fwdMapInv_ne_of_le hWr hWr0 hu hK hw hts ht.symm
      · rw [hγ', extCurve_of_lt hts] at ht
        have hts' : (0 : ℝ) < (t : ℝ) - s := sub_pos.2 (NNReal.coe_lt_coe.2 hts)
        have he := hFi (mul_I_mem_H hts') hw ht
        apply hwre
        rw [← he]
        simp
    · rw [hγ'0] at him
      have : 0 < (F w).im := hFw
      simp only [zero_im] at him
      linarith
  have hoffL : ∀ t ∈ Icc (0 : ℝ) 1, F x' - (t : ℂ) * I ∉ seedRayClosure γ' := by
    intro t ht hmem
    rcases hmem with ⟨τ, hτ⟩ | ⟨hre, -⟩
    · have him : (γ' τ).im = -t := by rw [hτ]; simp [hx'im]
      rcases eq_or_lt_of_le ht.1 with h0 | hpos
      · rw [← h0, ofReal_zero, zero_mul, sub_zero] at hτ
        rcases le_or_gt τ s with hts | hts
        · rw [hγ', extCurve_of_le hts] at hτ
          exact hx'γ τ hts hτ
        · have : 0 < (γ' τ).im := im_extCurve_pos hWr hWr0 hu hts
          linarith
      · linarith [hP.2.2.1 τ]
    · rw [hγ'0] at hre
      simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, zero_re] at hre
      exact hx're hre
  have hx'0 : x' ≠ 0 := hsign x' left_mem_uIcc
  have hyim : 0 ≤ y.im := (show 0 < y.im from hy).le
  set P₁ := (fun t : ℝ => F ((t : ℂ) + (y.im : ℂ) * I)) '' uIcc x' y.re with hP₁
  set P₂ := (fun t : ℝ => F ((x' : ℂ) + (t : ℂ) * I)) '' Icc 0 y.im with hP₂
  set P₃ := (fun t : ℝ => F x' - (t : ℂ) * I) '' Icc 0 1 with hP₃
  have hc₁ : IsPreconnected P₁ := isPreconnected_uIcc.image _ (hFc.comp (by fun_prop) fun t _ =>
    show (0 : ℝ) ≤ ((t : ℂ) + (y.im : ℂ) * I).im by simpa using hyim)
  have hc₂ : IsPreconnected P₂ := isPreconnected_Icc.image _ (hFc.comp (by fun_prop) fun t ht =>
    show (0 : ℝ) ≤ ((x' : ℂ) + (t : ℂ) * I).im by simpa using ht.1)
  have hc₃ : IsPreconnected P₃ := isPreconnected_Icc.image _ (by fun_prop)
  have hF₂₀ : F ((x' : ℂ) + ((0 : ℝ) : ℂ) * I) = F x' := by simp
  have hF₃₀ : F x' - ((0 : ℝ) : ℂ) * I = F x' := by simp
  have hm₁₂ : F ((x' : ℂ) + (y.im : ℂ) * I) ∈ P₁ ∩ P₂ :=
    ⟨⟨x', left_mem_uIcc, rfl⟩, ⟨y.im, ⟨hyim, le_rfl⟩, rfl⟩⟩
  have hm₂₃ : F x' ∈ (P₁ ∪ P₂) ∩ P₃ :=
    ⟨Or.inr ⟨0, ⟨le_rfl, hyim⟩, hF₂₀⟩, ⟨0, ⟨le_rfl, zero_le_one⟩, hF₃₀⟩⟩
  have hS : IsPreconnected (P₁ ∪ P₂ ∪ P₃) :=
    (hc₁.union _ hm₁₂.1 hm₁₂.2 hc₂).union _ hm₂₃.1 hm₂₃.2 hc₃
  have hSsub : P₁ ∪ P₂ ∪ P₃ ⊆ (seedRayClosure γ')ᶜ := by
    rintro z ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
    · exact hoffH _ (show 0 < ((t : ℂ) + (y.im : ℂ) * I).im by simpa using (show 0 < y.im from hy))
        (by simpa using hsign t ht)
    · rcases eq_or_lt_of_le ht.1 with h0 | hpos
      · simp only [← h0]
        rw [hF₂₀, ← hF₃₀]
        exact hoffL 0 ⟨le_rfl, zero_le_one⟩
      · exact hoffH _ (show 0 < ((x' : ℂ) + (t : ℂ) * I).im by simpa using hpos) (by simpa using hx'0)
    · exact hoffL t ht
  have hmy : F y ∈ P₁ ∪ P₂ ∪ P₃ := Or.inl (Or.inl ⟨y.re, right_mem_uIcc, by simp only [Complex.re_add_im]⟩)
  have hmI : F x' - I ∈ P₁ ∪ P₂ ∪ P₃ := Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  exact hS.subset_connectedComponentIn hmI hSsub hmy

/-- A bound for `γ([0, s])`. -/
theorem exists_norm_le_of_le (hγ : IsProperCurve γ) : ∃ M : ℝ, ∀ t ≤ s, ‖γ t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image hγ.1 : IsCompact (γ '' Icc (0 : ℝ≥0) s)).isBounded.exists_norm_le
  exact ⟨M, fun t ht => hM _ ⟨t, ⟨zero_le, ht⟩, rfl⟩⟩

/-- **Approaches from left of the tip coordinate lie on the left side of the continued curve.** -/
theorem mem_leftSide_extCurve (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hu : 0 ≤ u) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hηu : ηr u = γ s)
    (hK : fwdHull Wr u = fillH (γ '' Icc 0 s)) {y : ℂ} (hy : y ∈ H) (hyre : y.re < 0) :
    extendFrom H (fwdMapInv Wr u) y ∈ leftSide (extCurve Wr u γ s) := by
  set F := extendFrom H (fwdMapInv Wr u) with hF
  obtain ⟨R, C, hRC⟩ := exists_far_real hηr hWr hWr0 hu
  obtain ⟨M, hM⟩ := exists_norm_le_of_le (s := s) hγ
  set x' : ℝ := min y.re (-(|R| + |C| + |M| + 1)) with hx'
  have hx'y : x' ≤ y.re := min_le_left _ _
  have hx'b : x' ≤ -(|R| + |C| + |M| + 1) := min_le_right _ _
  have habs : R ≤ |x'| := by
    rw [abs_of_neg (by linarith [abs_nonneg R, abs_nonneg C, abs_nonneg M])]
    linarith [le_abs_self R, abs_nonneg C, abs_nonneg M]
  obtain ⟨hx'im, hx're⟩ := hRC x' habs
  have hre : (F x').re < -|M| := by
    have := (abs_le.1 hx're).2
    linarith [le_abs_self C, abs_nonneg R]
  have hγx : ∀ t ≤ s, γ t ≠ F x' := by
    intro t ht he
    have h1 := hM t ht
    rw [he] at h1
    have h2 := Complex.abs_re_le_norm (F x')
    rw [abs_of_neg (by linarith [abs_nonneg M])] at h2
    linarith [le_abs_self M]
  have hsign : ∀ t ∈ uIcc x' y.re, t ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hx'y] at ht
    exact (lt_of_le_of_lt ht.2 hyre).ne
  have hcomp := mem_component_extCurve hηr hWr hWr0 hu hγ hγ0 hηu hK hy hsign hx'im
    (by linarith [abs_nonneg M] : (F x').re < 0).ne hγx
  have hP := isProperCurve_extCurve hηr hWr hWr0 hu hγ hηu hK
  have h0 : extCurve Wr u γ s 0 = 0 := by rw [extCurve_of_le zero_le]; exact hγ0
  have hL : F x' - I ∈ leftSide (extCurve Wr u γ s) := by
    refine Supp9B.lowerLeft_subset_leftSide hP.2.2.1 (by rw [h0]; rfl) ⟨?_, ?_⟩
    · rw [h0]; simp only [sub_re, I_re, sub_zero, zero_re]; linarith [abs_nonneg M]
    · have hFim : (F x').im = 0 := hx'im
      simp [hFim]
  rw [Supp9B.leftSide, connectedComponentIn_eq hL]
  exact hcomp

/-- **Approaches from right of the tip coordinate lie on the right side of the continued curve.** -/
theorem mem_rightSide_extCurve (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hu : 0 ≤ u) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hηu : ηr u = γ s)
    (hK : fwdHull Wr u = fillH (γ '' Icc 0 s)) {y : ℂ} (hy : y ∈ H) (hyre : 0 < y.re) :
    extendFrom H (fwdMapInv Wr u) y ∈ rightSide (extCurve Wr u γ s) := by
  set F := extendFrom H (fwdMapInv Wr u) with hF
  obtain ⟨R, C, hRC⟩ := exists_far_real hηr hWr hWr0 hu
  obtain ⟨M, hM⟩ := exists_norm_le_of_le (s := s) hγ
  set x' : ℝ := max y.re (|R| + |C| + |M| + 1) with hx'
  have hx'y : y.re ≤ x' := le_max_left _ _
  have hx'b : |R| + |C| + |M| + 1 ≤ x' := le_max_right _ _
  have habs : R ≤ |x'| := by
    rw [abs_of_pos (by linarith [abs_nonneg R, abs_nonneg C, abs_nonneg M])]
    linarith [le_abs_self R, abs_nonneg C, abs_nonneg M]
  obtain ⟨hx'im, hx're⟩ := hRC x' habs
  have hre : |M| < (F x').re := by
    have := (abs_le.1 hx're).1
    linarith [le_abs_self C, abs_nonneg R]
  have hγx : ∀ t ≤ s, γ t ≠ F x' := by
    intro t ht he
    have h1 := hM t ht
    rw [he] at h1
    have h2 := Complex.abs_re_le_norm (F x')
    rw [abs_of_pos (by linarith [abs_nonneg M])] at h2
    linarith [le_abs_self M]
  have hsign : ∀ t ∈ uIcc x' y.re, t ≠ 0 := by
    intro t ht
    rw [uIcc_of_ge hx'y] at ht
    exact (lt_of_lt_of_le hyre ht.1).ne'
  have hcomp := mem_component_extCurve hηr hWr hWr0 hu hγ hγ0 hηu hK hy hsign hx'im
    (by linarith [abs_nonneg M] : 0 < (F x').re).ne' hγx
  have hP := isProperCurve_extCurve hηr hWr hWr0 hu hγ hηu hK
  have h0 : extCurve Wr u γ s 0 = 0 := by rw [extCurve_of_le zero_le]; exact hγ0
  have hR : F x' - I ∈ rightSide (extCurve Wr u γ s) := by
    refine Supp9B.lowerRight_subset_rightSide hP.2.2.1 (by rw [h0]; rfl) ⟨?_, ?_⟩
    · rw [h0]; simp only [sub_re, I_re, sub_zero, zero_re]; linarith [abs_nonneg M]
    · have hFim : (F x').im = 0 := hx'im
      simp [hFim]
  rw [Supp9B.rightSide, connectedComponentIn_eq hR]
  exact hcomp

end Ext

end InteractingSLE.Theorem14.SB.FinRel
