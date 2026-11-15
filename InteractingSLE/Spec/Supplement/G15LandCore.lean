/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBFinTerminal
import InteractingSLE.Spec.Sec7.ReverseArcSep
import InteractingSLE.Spec.Sec7.Lemma77Conf

/-!
# Lemma G15, pathwise: the continuing outer path supplies the completion

Packet PROVE-T14-G15. Lemma G15 (supplement pp. 508–509, `source/spec/p481-528.md` L666–L700): two canonical flows
`α` (seed `x₁`) and `β` (seed `x₂ ≤ x₁`) with `θ₁ < θ₂` meet at an exterior real point `q > x₁`, where the `α` prefix
is cut. The source proves (i) **the hull containment**: "the entire `α` prefix through `q` is contained in the filled
hull of the `β` prefix through `q`" (a first exit of `α` would cross an old `β` point strictly before `q`,
contradicting W5), and (ii) **the proper witnesses**: "Complete `α` by following this same `β` tail from `q`. Its added
part avoids the old `α` by the hull containment just proved. [...] The old `α` part stays on the closed right of the
completed `β`".

This file proves the right-hand case deterministically, `hasOrderedProperCompletions_of_rightContact`, from:
W5 for strict prefixes; slit completions of the two cut prefixes; and the good-path property of both paths
(`Restart.IsPathGood`: injectivity, continuity, and the tip freeness `Sec7.IsPathGood.isFreeAt_of_lt` — a later point
of `β` is free for an earlier prefix). Termination of either path is not used. The hull containment is phrased with
the free/trapped labels of `HalfPlaneSep` for `F = β([0, y])` (`q = β(y)`): no point `α(t)`, `t < a`, off `F` is free
for `F`.

* `exists_noRealBeyond`: the real points of `β([0, y))` are left of `q` (an earlier real point beyond `q` would trap
  `q`, but `β(y) = q` is free for that earlier prefix);
* `closingCurve`: `β([0, y])` followed by the real ray `[q, ∞)` is a proper curve, and the unbounded domain of `F` lies
  in its left side (`H_diff_fillH_subset_leftSide_closingCurve`);
* `not_isFreeAt_of_lt` (the hull containment): a first free point of `α` after its last visit to `F` would put `α`
  in the left side of the closing curve near an interior point `β(s₀)`, `s₀ < y`, of the common arc; by the side
  principle that is the left side of W5's `β` completion, which `α` avoids by duality;
* `tail_ne`: the `β` slit completion after `y` consists of free points, so it avoids `α([0, a))`;
* **`hasOrderedProperCompletions_of_rightContact`**: the junction `α([0, a])` + `β`-tail and the `β` slit completion
  are ordered proper completions (the order of `β([0, y))` by W5 and the pieces argument).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.G15Land

open Supp9B HalfPlaneSep

/-! ### The real ray -/

/-- The real ray `t ↦ Q + t` from a real point `Q`. -/
def realRay (Q : ℝ) (t : ℝ≥0) : ℂ := ((Q + t : ℝ) : ℂ)

theorem isProperCurve_realRay (Q : ℝ) : IsProperCurve (realRay Q) := by
  refine ⟨?_, ?_, fun t => by simp [realRay], ?_⟩
  · exact Complex.continuous_ofReal.comp (continuous_const.add NNReal.continuous_coe)
  · intro s t h
    have h' := Complex.ofReal_injective h
    exact NNReal.coe_injective (by linarith)
  · have h1 : ∀ t : ℝ≥0, (t : ℝ) - |Q| ≤ ‖realRay Q t‖ := by
      intro t
      rw [realRay, Complex.norm_real, Real.norm_eq_abs]
      have h3 : (t : ℝ) ≤ |Q + t| + |Q| := by
        calc (t : ℝ) = (Q + t) - Q := by ring
          _ ≤ |(Q + t) - Q| := le_abs_self _
          _ ≤ |Q + t| + |Q| := abs_sub _ _
      linarith
    have h4 : Tendsto (fun t : ℝ≥0 => (t : ℝ) - |Q|) atTop atTop := by
      simpa only [sub_eq_add_neg, id] using
        tendsto_atTop_add_const_right atTop (-|Q|) (NNReal.tendsto_coe_atTop.2 tendsto_id)
    exact tendsto_atTop_mono h1 h4

/-! ### The closing curve: `β([0, y])` followed by the real ray -/

section Closing

variable {Sc : ℝ≥0 → ℂ} {y : ℝ≥0} {Q : ℝ}

/-- The curve `Sc` up to time `y`, then the real ray from `Q`. With `Sc` a completion of `β([0, y])` and
`β(y) = Q`, this closes the prefix `β([0, y])` along `[Q, ∞)`. -/
def closingCurve (Sc : ℝ≥0 → ℂ) (y : ℝ≥0) (Q : ℝ) : ℝ≥0 → ℂ := junction Sc (realRay Q) y 0

theorem isProperCurve_closingCurve (hSc : IsProperCurve Sc) (hy : Sc y = (Q : ℂ))
    (hR : ∀ u < y, ∀ s : ℝ≥0, Sc u ≠ realRay Q s) : IsProperCurve (closingCurve Sc y Q) :=
  isProperCurve_junction hSc (isProperCurve_realRay Q) (by rw [hy]; simp [realRay])
    (fun u hu s _ => hR u hu s)

theorem closingCurve_of_le {t : ℝ≥0} (ht : t ≤ y) : closingCurve Sc y Q t = Sc t := by
  rw [closingCurve, junction_of_le ht]

/-- Every point of the closing curve is on `Sc([0, y])` or a real point `≥ Q`. -/
theorem closingCurve_mem (t : ℝ≥0) :
    closingCurve Sc y Q t ∈ Sc '' Icc 0 y ∨
      ((closingCurve Sc y Q t).im = 0 ∧ Q ≤ (closingCurve Sc y Q t).re) := by
  by_cases ht : t ≤ y
  · left
    rw [closingCurve_of_le ht]
    exact ⟨t, ⟨zero_le, ht⟩, rfl⟩
  · right
    rw [closingCurve, junction_of_lt (not_le.1 ht)]
    simp [realRay]

/-- A point of the closed closing curve with nonnegative imaginary part is on `Sc([0, y])` or a real point `≥ Q`. -/
theorem mem_seedRayClosure_closingCurve {w : ℂ} (h0 : (Sc 0).im = 0)
    (hw : w ∈ seedRayClosure (closingCurve Sc y Q)) (hwim : 0 ≤ w.im) :
    w ∈ Sc '' Icc 0 y ∨ (w.im = 0 ∧ Q ≤ w.re) := by
  rcases hw with ⟨t, rfl⟩ | ⟨hre, him⟩
  · exact closingCurve_mem t
  · left
    rw [closingCurve_of_le zero_le, h0] at him
    rw [closingCurve_of_le zero_le] at hre
    refine ⟨0, ⟨le_rfl, zero_le⟩, Complex.ext hre.symm ?_⟩
    rw [h0]
    exact (le_antisymm him hwim).symm

/-- **The unbounded domain of `Sc([0, y])` lies on the left of the closing curve.** It is connected, misses the
closed curve, and contains a far point `x₂ − M + i` joined to the lower-left quadrant by a vertical segment. -/
theorem H_diff_fillH_subset_leftSide_closingCurve (hSc : IsProperCurve Sc) (hy : Sc y = (Q : ℂ))
    (hR : ∀ u < y, ∀ s : ℝ≥0, Sc u ≠ realRay Q s) (h0 : (Sc 0).im = 0) (hQ : (Sc 0).re < Q) :
    H \ fillH (Sc '' Icc 0 y) ⊆ leftSide (closingCurve Sc y Q) := by
  set γ := closingCurve Sc y Q with hγ
  have hP := isProperCurve_closingCurve hSc hy hR
  set F := Sc '' Icc 0 y with hF
  have hFc : IsCompact F := isCompact_Icc.image hSc.1
  have hγ0 : γ 0 = Sc 0 := closingCurve_of_le zero_le
  have hγ0im : (γ 0).im = 0 := by rw [hγ0]; exact h0
  -- the unbounded domain misses the closed curve
  have hDS : H \ fillH F ⊆ (seedRayClosure γ)ᶜ := by
    intro z hz hzS
    have hz' := H_diff_fillH_subset_H_diff hFc.isClosed hz
    have hzH : 0 < z.im := hz'.1
    rcases mem_seedRayClosure_closingCurve h0 hzS hzH.le with h | h
    · exact hz'.2 h
    · exact hzH.ne' h.1
  -- a far reference point
  obtain ⟨R₀, hR₀⟩ := hFc.isBounded.subset_ball (0 : ℂ)
  set R : ℝ := max R₀ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hFR : F ⊆ ball (0 : ℂ) R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  set x₂ : ℝ := (Sc 0).re with hx₂
  set M : ℝ := R + |x₂| + 1 with hM
  have hMpos : 0 < M := by positivity
  set p₀ : ℝ := x₂ - M with hp₀
  have hp₀x : p₀ < x₂ := by linarith
  have hp₀R : R + 1 ≤ |p₀| := by
    have hx := le_abs_self x₂
    have hneg : p₀ < 0 := by rw [hp₀, hM]; linarith
    rw [abs_of_neg hneg, hp₀, hM]
    linarith
  set seg : ℝ → ℂ := fun s => (p₀ : ℂ) + (s : ℂ) * I with hseg
  have hsegc : Continuous seg := by fun_prop
  set S := seg '' Icc (-1 : ℝ) 1 with hS
  have hSre : ∀ w ∈ S, w.re = p₀ := by
    rintro _ ⟨s, -, rfl⟩
    simp [hseg]
  have hSnorm : ∀ w ∈ S, R + 1 ≤ ‖w‖ := fun w hw =>
    hp₀R.trans ((hSre w hw) ▸ Complex.abs_re_le_norm w)
  have hSS : S ⊆ (seedRayClosure γ)ᶜ := by
    intro w hw hwS
    rcases hwS with ⟨t, rfl⟩ | ⟨hre, -⟩
    · rcases closingCurve_mem (Sc := Sc) (y := y) (Q := Q) t with h | h
      · have := mem_ball_zero_iff.1 (hFR h)
        linarith [hSnorm _ hw]
      · have := hSre _ hw
        linarith [h.2]
    · rw [hSre w hw, hγ0] at hre
      exact hp₀x.ne hre
  have hlow : seg (-1) ∈ leftSide γ := by
    refine lowerLeft_subset_leftSide hP.2.2.1 hγ0im ⟨?_, ?_⟩
    · show (seg (-1)).re < (closingCurve Sc y Q 0).re
      rw [closingCurve_of_le zero_le, show (seg (-1)).re = p₀ by simp [hseg]]
      exact hp₀x
    · simp [hseg]
  have hSL : S ⊆ leftSide γ := by
    have hsub := (isPreconnected_Icc.image seg hsegc.continuousOn).subset_connectedComponentIn
      (⟨-1, ⟨le_rfl, by norm_num⟩, rfl⟩ : seg (-1) ∈ S) hSS
    rwa [← connectedComponentIn_eq hlow] at hsub
  have hz₀S : seg 1 ∈ S := ⟨1, ⟨by norm_num, le_rfl⟩, rfl⟩
  have hz₀D : seg 1 ∈ H \ fillH F := by
    refine mem_H_diff_fillH_of_le_norm hFc.isClosed (by linarith) hFR ?_ (by linarith [hSnorm _ hz₀S])
    show 0 < (seg 1).im
    simp [hseg]
  have hsub := (isPreconnected_H_diff_fillH hFc.isClosed hFc.isBounded).subset_connectedComponentIn
    hz₀D hDS
  rwa [← connectedComponentIn_eq (hSL hz₀S)] at hsub

end Closing

/-! ### The largest real point of the prefix -/

/-- **No real point of `β([0, y))` at or beyond `q = β(y)`** (supplement p. 508: "`q` is its largest real point: an
earlier contact farther to the right would have swallowed a trace-free upper collar of `q`"). An earlier real point
`r ≥ q` would trap `q` (the trapping lemma, with `x₂ < q < r`), while `β(y) = q` is free for the earlier prefix. -/
theorem ne_realRay_of_isPathGood {β : ℝ≥0 → ℂ} {ζ₂ : ℝ≥0∞} {x₂ Q : ℝ} (hp : Restart.IsPathGood β ζ₂ x₂)
    {y : ℝ≥0} (hy : (y : ℝ≥0∞) ≤ ζ₂) (hβy : β y = Q) (hQ : x₂ < Q) :
    ∀ u < y, ∀ s : ℝ≥0, β u ≠ realRay Q s := by
  intro u hu s he
  have huζ : (u : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hu.le).trans hy
  have hinj := Sec7.IsPathGood.injOn_Icc hp hy
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
  · rw [← hs] at he
    have he' : β u = β y := by rw [he, hβy]; simp [realRay]
    exact hu.ne (hinj ⟨zero_le, hu.le⟩ ⟨zero_le, le_rfl⟩ he')
  · set K := β '' Icc 0 u with hK
    have hKc : IsCompact K := Sec7.IsPathGood.isCompact_image hp huζ
    have hKpc : IsPreconnected K :=
      isPreconnected_Icc.image _ (Sec7.IsPathGood.continuousOn_Icc hp huζ)
    have hKim : ∀ w ∈ K, 0 ≤ w.im := by
      rintro _ ⟨t, ht, rfl⟩
      exact Sec7.IsPathGood.im_nonneg hp ((ENNReal.coe_le_coe.2 ht.2).trans huζ)
    have hx₂K : (x₂ : ℂ) ∈ K := ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hp⟩
    have hrK : ((Q + s : ℝ) : ℂ) ∈ K := ⟨u, ⟨zero_le, le_rfl⟩, he⟩
    have hQK : (Q : ℂ) ∉ K := by
      rintro ⟨t, ht, htQ⟩
      have := hinj ⟨zero_le, ht.2.trans hu.le⟩ ⟨zero_le, le_rfl⟩ (htQ.trans hβy.symm)
      exact absurd (this ▸ ht.2) (not_le.2 hu)
    have hlt : Q < Q + s := by have : (0 : ℝ) < s := hs; linarith
    have htrap := Sec7.isTrappedAt_of_isPreconnected hKc hKpc hKim hx₂K hrK hQ hlt hQK
    have hfree := Sec7.IsPathGood.isFreeAt_of_lt hp hu hy
    rw [hβy] at hfree
    exact hfree.not_isTrappedAt (by simp) htrap

/-! ### The hull containment -/

section Hull

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **The hull containment of Lemma G15** (supplement p. 508: "the entire `α` prefix through `q` is contained in
the filled hull of the `β` prefix through `q`"), in label form: with `q = α(a) = β(y)` a real point beyond the seeds,
no point `α(t)`, `t < a`, off `F = β([0, y])` is free for `F`.

Proof. Suppose `α(t₁)` is free. If `α([0, t₁])` misses `F`, the label is constant along it, so the seed `x₁` would be
free; but `x₁ = α(0) ∈ (x₂, q)` misses `F` and is trapped by the connected `F`, which joins `x₂` and `q`. Otherwise let
`t₀` be the last visit of `F` before `t₁`: `α(t₀) = β(s₀)` with `s₀ < y`, and `α` is free on `(t₀, t₁]`. Free points
near `β(s₀)` lie on the left of the closing curve (`β([0, y])` + `[q, ∞)`); by the side principle they lie on the left
of the `β` completion `β₀` of W5's ordered pair at `(t₁, c')`, `s₀ < c' < y`, which `α([0, t₁])` avoids by duality. -/
theorem not_isFreeAt_of_lt (hpα : Restart.IsPathGood α ζ₁ x₁) (hpβ : Restart.IsPathGood β ζ₂ x₂)
    (hx : x₂ ≤ x₁)
    (hW5 : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c)
    {a c y : ℝ≥0} {Q : ℝ} (ha : (a : ℝ≥0∞) ≤ ζ₁) (hc : (c : ℝ≥0∞) ≤ ζ₂) (hyc : y ≤ c)
    {Sc : ℝ≥0 → ℂ} (hSc : IsSlitCompletion β c Sc)
    (hαa : α a = Q) (hβy : β y = Q) (hQ : x₁ < Q) :
    ∀ t < a, α t ∉ β '' Icc 0 y → ¬ IsFreeAt (β '' Icc 0 y) (α t) := by
  intro t₁ ht₁ hF₁ hfree₁
  have hyζ : (y : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hyc).trans hc
  have hα0 : α 0 = x₁ := Sec7.IsPathGood.zero hpα
  have hβ0 : β 0 = x₂ := Sec7.IsPathGood.zero hpβ
  have hx₂Q : x₂ < Q := hx.trans_lt hQ
  set F := β '' Icc 0 y with hF
  have hFc : IsCompact F := Sec7.IsPathGood.isCompact_image hpβ hyζ
  have hFpc : IsPreconnected F := isPreconnected_Icc.image _ (Sec7.IsPathGood.continuousOn_Icc hpβ hyζ)
  have hFim : ∀ w ∈ F, 0 ≤ w.im := by
    rintro _ ⟨t, ht, rfl⟩
    exact Sec7.IsPathGood.im_nonneg hpβ ((ENNReal.coe_le_coe.2 ht.2).trans hyζ)
  have ht₁ζ : (t₁ : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.2 ht₁).trans_le ha
  have hαc : ContinuousOn α (Icc 0 t₁) := Sec7.IsPathGood.continuousOn_Icc hpα ht₁ζ.le
  have hαim : ∀ t ≤ t₁, 0 ≤ (α t).im := fun t ht =>
    Sec7.IsPathGood.im_nonneg hpα ((ENNReal.coe_le_coe.2 ht).trans ht₁ζ.le)
  have hinjα := Sec7.IsPathGood.injOn_Icc hpα ha
  set A₀ := {t ∈ Icc 0 t₁ | α t ∈ F} with hA₀
  have hA₀c : IsClosed A₀ := hαc.preimage_isClosed_of_isClosed isClosed_Icc hFc.isClosed
  rcases A₀.eq_empty_or_nonempty with hA₀e | hA₀n
  · -- no visit before `t₁`: the seed would be free
    have hX : α '' Icc 0 t₁ ⊆ {w | 0 ≤ w.im} \ F := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨hαim t ht.2, fun hmem => ?_⟩
      have : t ∈ A₀ := ⟨ht, hmem⟩
      rw [hA₀e] at this
      exact this
    have hx₁F : (x₁ : ℂ) ∉ F := by
      rw [← hα0]
      exact (hX ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩).2
    have hlt : x₂ < x₁ := lt_of_le_of_ne hx fun h => hx₁F ⟨0, ⟨le_rfl, zero_le⟩, by rw [hβ0, h]⟩
    have htr := Sec7.isTrappedAt_of_isPreconnected hFc hFpc hFim (u := x₂) (v := Q) (y := x₁)
      ⟨0, ⟨le_rfl, zero_le⟩, hβ0⟩ ⟨y, ⟨zero_le, le_rfl⟩, hβy⟩ hlt hQ hx₁F
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hFc.isClosed
        (isPreconnected_Icc.image _ hαc) hX with h | h
    · have h0 := h (α 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
      rw [hα0] at h0
      exact h0.not_isTrappedAt (by simp) htr
    · exact hfree₁.not_isTrappedAt (hαim t₁ le_rfl) (h _ ⟨t₁, ⟨zero_le, le_rfl⟩, rfl⟩)
  -- the last visit `t₀ < t₁`
  have hbdd : BddAbove A₀ := ⟨t₁, fun t ht => ht.1.2⟩
  set t₀ := sSup A₀ with ht₀
  have ht₀A : t₀ ∈ A₀ := hA₀c.csSup_mem hA₀n hbdd
  have ht₀t₁ : t₀ < t₁ := lt_of_le_of_ne ht₀A.1.2 fun h => hF₁ (h ▸ ht₀A.2)
  have hfreeI : ∀ t, t₀ < t → t ≤ t₁ → IsFreeAt F (α t) := by
    have hX : α '' Ioc t₀ t₁ ⊆ {w | 0 ≤ w.im} \ F := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨hαim t ht.2, fun hmem => absurd (le_csSup hbdd ⟨⟨zero_le, ht.2⟩, hmem⟩) (not_le.2 ht.1)⟩
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hFc.isClosed
        (isPreconnected_Ioc.image _ (hαc.mono fun t ht => ⟨zero_le, ht.2⟩)) hX with h | h
    · exact fun t h1 h2 => h _ ⟨t, ⟨h1, h2⟩, rfl⟩
    · exact absurd (h _ ⟨t₁, ⟨ht₀t₁, le_rfl⟩, rfl⟩) (hfree₁.not_isTrappedAt (hαim t₁ le_rfl))
  have hnotF : ∀ t, t₀ < t → t ≤ t₁ → α t ∉ F := fun t h1 h2 hmem =>
    absurd (le_csSup hbdd ⟨⟨zero_le, h2⟩, hmem⟩) (not_le.2 h1)
  -- the visited point `β(s₀)`, `s₀ < y`
  obtain ⟨s₀, hs₀, hs₀e⟩ := ht₀A.2
  have hs₀y : s₀ < y := by
    refine lt_of_le_of_ne hs₀.2 fun h => ?_
    rw [h, hβy, ← hαa] at hs₀e
    have := hinjα ⟨zero_le, ht₀A.1.2.trans (le_of_lt ht₁)⟩ ⟨zero_le, le_rfl⟩ hs₀e.symm
    exact absurd this (ne_of_lt (ht₀t₁.trans ht₁))
  obtain ⟨c', hs₀c', hc'y⟩ := exists_between hs₀y
  have hc'ζ : (c' : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hc'y).trans_le hyζ
  -- W5's ordered pair at `(t₁, c')` and duality
  obtain ⟨α₀, β₀, hα₀, hβ₀, hord⟩ := hW5 t₁ c' ht₁ζ hc'ζ
  have Pα₀ := isProperCurve_of_isProperCompletion hα₀
  have Pβ₀ := isProperCurve_of_isProperCompletion hβ₀
  have hα₀0 : α₀ 0 = x₁ := (hα₀.2.2.2.2 0 zero_le).trans hα0
  have hβ₀0 : β₀ 0 = x₂ := (hβ₀.2.2.2.2 0 zero_le).trans hβ0
  have hβ₀im : (β₀ 0).im = 0 := by rw [hβ₀0]; simp
  have hdual := range_subset_closedRightSide Pα₀ Pβ₀ (by rw [hα₀0]; simp) hβ₀im
    (by rw [hα₀0, hβ₀0]; simpa using hx) hord
  have hnotL : ∀ t ≤ t₁, α t ∉ leftSide β₀ := by
    intro t ht hL
    have hmem := hdual ⟨t, rfl⟩
    rw [hα₀.2.2.2.2 t ht] at hmem
    rcases hmem with hR' | hS'
    · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide Pβ₀ hβ₀im) hL hR'
    · exact leftSide_subset_compl β₀ hL hS'
  -- the closing curve
  have PSc := isProperCurve_of_isProperCompletion hSc.1
  have hScβ : ∀ t ≤ c, Sc t = β t := hSc.1.2.2.2.2
  have hR : ∀ u < y, ∀ s : ℝ≥0, Sc u ≠ realRay Q s := fun u hu s h =>
    ne_realRay_of_isPathGood hpβ hyζ hβy hx₂Q u hu s (by rw [← hScβ u (hu.le.trans hyc)]; exact h)
  have hScy : Sc y = (Q : ℂ) := by rw [hScβ y hyc, hβy]
  have hSc0 : Sc 0 = x₂ := (hScβ 0 zero_le).trans hβ0
  set γ := closingCurve Sc y Q with hγ
  have Pγ := isProperCurve_closingCurve PSc hScy hR
  have hγ0 : γ 0 = x₂ := (closingCurve_of_le zero_le).trans hSc0
  have hγ0im : (γ 0).im = 0 := by rw [hγ0]; simp
  have hFSc : Sc '' Icc 0 y = F := image_congr fun t ht => hScβ t (ht.2.trans hyc)
  have hDL : H \ fillH F ⊆ leftSide γ := by
    have := H_diff_fillH_subset_leftSide_closingCurve PSc hScy hR (by rw [hSc0]; simp)
      (by rw [hSc0]; simp [hx₂Q])
    rwa [hFSc] at this
  -- free points off the closed curve are on the left of `γ`
  have hfreeL : ∀ w : ℂ, IsFreeAt F w → 0 ≤ w.im → w ∉ seedRayClosure γ → w ∈ leftSide γ := by
    intro w hw hwim hwS
    have hcl : w ∈ closure (leftSide γ) :=
      closure_mono hDL (Sec7.mem_closure_H_diff_fillH_of_isFreeAt hw hwim)
    rcases (compl_seedRayClosure_eq Pγ hγ0im ▸ hwS : w ∈ leftSide γ ∪ rightSide γ) with h | h
    · exact h
    · exfalso
      have hd : Disjoint (rightSide γ) (closure (leftSide γ)) :=
        (disjoint_leftSide_rightSide Pγ hγ0im).symm.closure_right (isOpen_rightSide Pγ)
      exact Set.disjoint_left.1 hd h hcl
  -- the side principle at `s₀ < c'`
  have hagree : ∀ t ≤ c', β₀ t = γ t := fun t ht => by
    rw [hγ, closingCurve_of_le (ht.trans hc'y.le), hScβ t ((ht.trans hc'y.le).trans hyc), hβ₀.2.2.2.2 t ht]
  have hSP := eventually_mem_leftSide_of_eqOn Pγ Pβ₀ hγ0im hagree hs₀c'
  have hγs₀ : γ s₀ = α t₀ := by
    rw [hγ, closingCurve_of_le hs₀.2, hScβ s₀ (hs₀.2.trans hyc), hs₀e]
  -- near `β(s₀)`, the ray `[Q, ∞)` is absent
  set KR : Set ℂ := {w | w.im = 0 ∧ Q ≤ w.re} with hKR
  have hKRc : IsClosed KR :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_const continuous_re)
  have hs₀KR : γ s₀ ∉ KR := by
    rintro ⟨him, hre⟩
    have hsβ : Sc s₀ = realRay Q ((γ s₀).re - Q).toNNReal := by
      have e : γ s₀ = Sc s₀ := closingCurve_of_le hs₀.2
      rw [← e]
      apply Complex.ext
      · simp [realRay, Real.coe_toNNReal _ (sub_nonneg.2 hre)]
      · simp [realRay, him]
    exact hR s₀ hs₀y _ hsβ
  have hfar : ∀ᶠ w in 𝓝 (γ s₀), w ∉ KR := hKRc.isOpen_compl.mem_nhds hs₀KR
  -- approach from the right in time
  set I₀ := Ioc t₀ t₁ with hI₀
  have hNe : (𝓝[I₀] t₀).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc ht₀t₁.ne]
    exact ⟨le_rfl, ht₀t₁.le⟩
  have hT : Tendsto α (𝓝[I₀] t₀) (𝓝 (γ s₀)) := by
    rw [hγs₀]
    exact ((hαc t₀ ⟨zero_le, ht₀t₁.le⟩).mono fun t ht => ⟨zero_le, ht.2⟩).tendsto
  have hev := (hT.eventually (hSP.and hfar)).and (self_mem_nhdsWithin : I₀ ∈ 𝓝[I₀] t₀)
  obtain ⟨t, ⟨hSPt, hfart⟩, htI⟩ := hev.exists
  -- `α(t)` is free, off the closed curve, hence on the left of `γ`, hence of `β₀`
  have hαtS : α t ∉ seedRayClosure γ := by
    intro hS
    rcases mem_seedRayClosure_closingCurve (by rw [hSc0]; simp) hS (hαim t htI.2) with h | h
    · exact hnotF t htI.1 htI.2 (hFSc ▸ h)
    · exact hfart h
  exact hnotL t htI.2 (hSPt (hfreeL _ (hfreeI t htI.1 htI.2) (hαim t htI.2) hαtS))

/-! ### The proper witnesses -/

/-- **The `β` slit tail avoids the old `α`** (supplement p. 509: "Its added part avoids the old `α` by the hull
containment just proved"): every point `Sc(s)`, `s ≥ y`, of the slit completion of `β([0, c])` after `q = β(y)` is
either `q` itself or free for `β([0, y])` (a later trace point by the tip property, a slit point because the slit is
connected and unbounded), so it is not a point `α(u)`, `u < a`. -/
theorem tail_ne (hpα : Restart.IsPathGood α ζ₁ x₁) (hpβ : Restart.IsPathGood β ζ₂ x₂) (hx : x₂ ≤ x₁)
    (hW5 : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c)
    {a c y : ℝ≥0} {Q : ℝ} (ha : (a : ℝ≥0∞) ≤ ζ₁) (hc : (c : ℝ≥0∞) ≤ ζ₂) (hyc : y ≤ c)
    {Sc : ℝ≥0 → ℂ} (hSc : IsSlitCompletion β c Sc)
    (hαa : α a = Q) (hβy : β y = Q) (hQ : x₁ < Q) :
    ∀ u < a, ∀ s, y ≤ s → α u ≠ Sc s := by
  intro u hu s hs he
  have hyζ : (y : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hyc).trans hc
  have hinjα := Sec7.IsPathGood.injOn_Icc hpα ha
  have hinjβ := Sec7.IsPathGood.injOn_Icc hpβ hc
  have hScβ : ∀ t ≤ c, Sc t = β t := hSc.1.2.2.2.2
  set F := β '' Icc 0 y with hF
  have hFc : IsCompact F := Sec7.IsPathGood.isCompact_image hpβ hyζ
  have hhull := not_isFreeAt_of_lt hpα hpβ hx hW5 ha hc hyc hSc hαa hβy hQ
  have huζ : (u : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hu.le).trans ha
  have hαim : 0 ≤ (α u).im := Sec7.IsPathGood.im_nonneg hpα huζ
  rcases hs.lt_or_eq with hys | rfl
  · -- `α(u)` would be a point off `F` that is free for `F`
    have hnotF : Sc s ∉ F := by
      rintro ⟨t, ht, hts⟩
      by_cases hsc : s ≤ c
      · rw [hScβ s hsc] at hts
        have := hinjβ ⟨zero_le, ht.2.trans hyc⟩ ⟨zero_le, hsc⟩ hts
        exact absurd (this ▸ ht.2) (not_le.2 hys)
      · rw [← hScβ t (ht.2.trans hyc)] at hts
        have := hSc.1.2.1 hts
        exact absurd (this ▸ ht.2.trans hyc) (not_le.2 (not_le.1 hsc))
    have hfree : IsFreeAt F (Sc s) := by
      by_cases hsc : s ≤ c
      · rw [hScβ s hsc]
        exact Sec7.IsPathGood.isFreeAt_of_lt hpβ hys ((ENNReal.coe_le_coe.2 hsc).trans hc)
      · -- the slit after `c` is connected, unbounded and off `F`
        have hX : Sc '' Ioi c ⊆ {w | 0 ≤ w.im} \ F := by
          rintro _ ⟨r, hr, rfl⟩
          refine ⟨(hSc.2 r hr).1.le, fun hmem => (hSc.2 r hr).2 ?_⟩
          obtain ⟨t, ht, hte⟩ := hmem
          exact ⟨t, ⟨zero_le, ht.2.trans hyc⟩, hte⟩
        have hXu : ¬ IsBounded (Sc '' Ioi c) := by
          intro hb
          obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
          obtain ⟨r, hr1, hr2⟩ :=
            ((hSc.1.2.2.2.1.eventually_gt_atTop C).and (eventually_gt_atTop c)).exists
          exact absurd (hC _ ⟨r, hr2, rfl⟩) (not_le.2 hr1)
        exact isFreeAt_of_not_isBounded hFc.isClosed hFc.isBounded
          (isPreconnected_Ioi.image _ hSc.1.1.continuousOn) hXu hX _ ⟨s, not_le.1 hsc, rfl⟩
    rw [← he] at hnotF hfree
    exact hhull u hu hnotF hfree
  · -- `Sc(y) = q = α(a)`
    rw [hScβ y hyc, hβy, ← hαa] at he
    have := hinjα ⟨zero_le, hu.le⟩ ⟨zero_le, le_rfl⟩ he
    exact absurd this (ne_of_lt hu)

/-- **Lemma G15's proper witnesses, right-hand case** (supplement p. 509: "Complete `α` by following this same `β`
tail from `q`. [...] Both curves are therefore injective and proper. The old `α` part stays on the closed right of the
completed `β`"). Let `α` (seed `x₁`) and `β` (seed `x₂ ≤ x₁`) be good paths whose strict prefixes have W5's ordered
completions. If the cut `α(a)` of `α` is a real point `q > x₁` that `β` visits at a time `y ≤ c`, then `α([0, a])` and
`β([0, c])` have ordered proper completions: the slit completion `Sc` of `β([0, c])`, and `α([0, a])` followed by the
tail `Sc([y, ∞))`. Termination of either path is not used. -/
theorem hasOrderedProperCompletions_of_rightContact (hpα : Restart.IsPathGood α ζ₁ x₁)
    (hpβ : Restart.IsPathGood β ζ₂ x₂) (hx : x₂ ≤ x₁)
    (hW5 : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c)
    {a c y : ℝ≥0} {Q : ℝ} (ha : (a : ℝ≥0∞) ≤ ζ₁) (hc : (c : ℝ≥0∞) ≤ ζ₂) (hyc : y ≤ c)
    {Sα Sc : ℝ≥0 → ℂ} (hSα : IsSlitCompletion α a Sα) (hSc : IsSlitCompletion β c Sc)
    (hαa : α a = Q) (hβy : β y = Q) (hQ : x₁ < Q) :
    HasOrderedProperCompletions α a β c := by
  have hyζ : (y : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hyc).trans hc
  have hα0 : α 0 = x₁ := Sec7.IsPathGood.zero hpα
  have hβ0 : β 0 = x₂ := Sec7.IsPathGood.zero hpβ
  have hinjβ := Sec7.IsPathGood.injOn_Icc hpβ hc
  have hScβ : ∀ t ≤ c, Sc t = β t := hSc.1.2.2.2.2
  have hSαα : ∀ t ≤ a, Sα t = α t := hSα.1.2.2.2.2
  have PSα := isProperCurve_of_isProperCompletion hSα.1
  have PSc := isProperCurve_of_isProperCompletion hSc.1
  have htail := tail_ne hpα hpβ hx hW5 ha hc hyc hSc hαa hβy hQ
  have ha0 : 0 < a := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hα0] at hαa
    exact hQ.ne (Complex.ofReal_injective hαa)
  -- the junction completion of `α([0, a])`
  have hj : Sα a = Sc y := by rw [hSαα a le_rfl, hScβ y hyc, hαa, hβy]
  have hdisj : ∀ u < a, ∀ s, y ≤ s → Sα u ≠ Sc s := fun u hu s hs => by
    rw [hSαα u hu.le]; exact htail u hu s hs
  set α' := junction Sα Sc a y with hα'
  have Pα' := isProperCurve_junction PSα PSc hj hdisj
  have hα'c : IsProperCompletion α a α' :=
    ⟨Pα'.1, Pα'.2.1, Pα'.2.2.1, Pα'.2.2.2, fun t ht => by rw [hα', junction_of_le ht]; exact hSαα t ht⟩
  refine ⟨α', Sc, hα'c, hSc.1, ?_⟩
  rintro _ ⟨s, rfl⟩
  rcases lt_or_ge s y with hsy | hys
  · -- an old `β` point: W5 at `(a₀, s)` with `α([a₀, a])` clear of `β([0, s])`
    have hsζ : (s : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hsy).trans_le hyζ
    set K := β '' Icc 0 s with hK
    have hKc : IsCompact K := Sec7.IsPathGood.isCompact_image hpβ hsζ.le
    have hQK : α a ∉ K := by
      rintro ⟨t, ht, hte⟩
      rw [hαa, ← hβy] at hte
      have := hinjβ ⟨zero_le, (ht.2.trans hsy.le).trans hyc⟩ ⟨zero_le, hyc⟩ hte
      exact absurd (this ▸ ht.2) (not_le.2 hsy)
    obtain ⟨a₀, ha₀, hclr⟩ := Fin.exists_lt_forall_Icc_notMem ha0 (Sec7.IsPathGood.continuousOn_Icc hpα ha)
      hKc.isClosed hQK
    obtain ⟨α₀, β₀, hα₀, hβ₀, hord⟩ := hW5 a₀ s ((ENNReal.coe_lt_coe.2 ha₀).trans_le ha) hsζ
    have Pα₀ := isProperCurve_of_isProperCompletion hα₀
    have Pβ₀ := isProperCurve_of_isProperCompletion hβ₀
    have hα₀0 : α₀ 0 = x₁ := (hα₀.2.2.2.2 0 zero_le).trans hα0
    have hβ₀0 : β₀ 0 = x₂ := (hβ₀.2.2.2.2 0 zero_le).trans hβ0
    have hagree : ∀ t ≤ a₀, α' t = α₀ t := fun t ht => by
      rw [hα', junction_of_le (ht.trans ha₀.le), hSαα t (ht.trans ha₀.le), hα₀.2.2.2.2 t ht]
    have hmem := mem_closedLeftSide_of_avoid Pα₀ Pα' (by rw [hα₀0]; simp) hagree Pβ₀
      (by rw [hβ₀0]; simp) (by rw [hα₀0, hβ₀0]; simpa using hx) hord (t := s) ?_
    · rwa [hβ₀.2.2.2.2 s le_rfl, ← hScβ s (hsy.le.trans hyc)] at hmem
    intro u hu r hr he
    rw [hβ₀.2.2.2.2 u hu] at he
    by_cases hra : r ≤ a
    · rw [junction_of_le hra, hSαα r hra] at he
      exact hclr r ⟨hr, hra⟩ ⟨u, ⟨zero_le, hu⟩, he⟩
    · rw [junction_of_lt (not_le.1 hra), ← hScβ u ((hu.trans hsy.le).trans hyc)] at he
      have := PSc.2.1 he
      have hlt : u < y + (r - a) := (hu.trans_lt hsy).trans_le le_self_add
      exact hlt.ne this
  · -- a tail point is on the completed `α`
    refine Or.inr (Or.inl ⟨a + (s - y), ?_⟩)
    rcases hys.lt_or_eq with hys' | rfl
    · rw [hα', junction_of_lt (lt_add_of_pos_right a (tsub_pos_of_lt hys')), add_tsub_cancel_left,
        add_tsub_cancel_of_le hys]
    · rw [tsub_self, add_zero, hα', junction_of_le le_rfl]
      exact hj

end Hull

end InteractingSLE.Theorem14.SB.G15Land
