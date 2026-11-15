/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS2Lift
import InteractingSLE.Spec.Supplement.S9BTransfer

/-!
# Lemma S5, main clause: the left collar shift of a proper completion

Packet PROVE-T14-SB6. The proof of Lemma S5's main clause (supplement pp. 582–583, `source/spec/p577-624.md`
L109–L122) starts in the relative chart: "take an ordered proper completion `b̂` of the retained relative second
prefix. Move only its unretained future slightly to its left. [...] Adjoin its lower vertical closing ray and use a
Schoenflies annular collar of that oriented Jordan curve on the sphere. The retained prefix and the closing ray have
displacement zero. On the future arc choose a continuous positive left displacement [...] and set it to zero at every
negative-real contact. The displacement can be chosen small enough to keep the moved curve in `closure ℍ`. [...] The
resulting curve is a proper injective extension of the same retained prefix [...]. Its new future has no real point at
or to the right of its seed. Moving left enlarges its closed right side".

* **`exists_leftShift`** (proved): for a proper curve `b̂` from `0` and a prefix length `a₀`, there is a proper
  completion `b̃` of `b̂|[0, a₀]` whose points after `a₀` are either points of `b̂` or points of `ℍ` on the open left
  side of `b̂`, whose real points after `a₀` are negative, and whose closed right side contains that of `b̂`.

Construction. With `p` the right reference point, the inverted closed curve is a Jordan curve; Schoenflies gives a
homeomorphism `Ψ` of the plane with `Ψ(S¹) =` that curve and `Ψ(𝔻) ⊆` the inverted open left side. Put
`u(s) = Ψ⁻¹(inv_p (b̂ s)) ∈ S¹` and `M(s, ρ) = uninv_p (Ψ((1 − ρ) u(s)))` (`M(s, 0) = b̂ s`; for `0 < ρ < 1` a point
of the left side). The displacement is `ρ(s) = min(f(s)/2, dist(s, C))`, where `C = [0, a₀] ∪ b̂⁻¹((−∞, 0])` and
`f(s)` is the distance from `(s, 0)` to the closed set of `(s, ρ)` with `ρ ≥ 1/2` or
`|M(s, ρ) − b̂ s| ≥ min(dist(b̂ s, Q), 1)`, `Q` the closed lower-left quadrant. A left-side point within
`dist(b̂ s, Q)` of `b̂ s` lies in `ℍ`, since left-side points with `Im ≤ 0` have `Re < 0`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B (IsProperCurve leftSide rightSide closedRightSide invCurve rightRef inv uninv)

namespace InteractingSLE

namespace Theorem14

namespace SB

variable {γ : ℝ≥0 → ℂ}

/-- The closed lower-left quadrant at `0`. -/
def lowerQuad : Set ℂ := {z | z.re ≤ 0 ∧ z.im ≤ 0}

theorem isClosed_lowerQuad : IsClosed lowerQuad :=
  (isClosed_le continuous_re continuous_const).inter (isClosed_le continuous_im continuous_const)

theorem zero_mem_lowerQuad : (0 : ℂ) ∈ lowerQuad := ⟨le_rfl, le_rfl⟩

/-- **A left-side point near the curve is in `ℍ`**: within `dist(z, Q)` of any `z`, a point of the open left side of a
proper curve from `0` is in `ℍ` (left-side points with `Im ≤ 0` have `Re < 0`). -/
theorem mem_H_of_mem_leftSide_of_dist_lt (hγ : IsProperCurve γ) (h0 : γ 0 = 0) {w z : ℂ} (hw : w ∈ leftSide γ)
    (hd : dist w z < infDist z lowerQuad) : w ∈ H := by
  have hwQ : w ∉ lowerQuad := fun hQ =>
    absurd ((infDist_le_dist_of_mem hQ).trans_lt (by rwa [dist_comm] at hd)) (lt_irrefl _)
  show 0 < w.im
  by_contra him
  have him' : w.im ≤ 0 := not_lt.1 him
  have hre := re_lt_of_mem_leftSide hγ (by rw [h0]; rfl) hw him'
  rw [h0, zero_re] at hre
  exact hwQ ⟨hre.le, him'⟩

/-- Every point of the closed curve is a limit of right-side points. -/
theorem mem_closure_rightSide (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) {z : ℂ} (hz : z ∈ seedRayClosure γ) :
    z ∈ closure (rightSide γ) := by
  obtain ⟨U, V, -, -, -, -, -, -, -, -, hfV, -, -, -, hVR, -⟩ := Supp9B.exists_jordan_sides' hγ h0
  have hq : inv (rightRef γ) z ∈ closure V :=
    frontier_subset_closure (by rw [hfV]; exact Supp9B.inv_mem_invCurve hz rfl)
  have hzp : z ≠ rightRef γ := fun e => Supp9B.rightRef_notMem hγ.2.2.1 h0 (e ▸ hz)
  have hc := Supp9B.continuousAt_uninv (p := rightRef γ) (Supp9B.inv_apply_ne_zero hzp)
  have := mem_closure_image hc hq
  rw [Supp9B.uninv_inv] at this
  exact closure_mono hVR this

/-- **The Schoenflies collar map**: a homeomorphism `Ψ` of the plane taking the unit circle onto the inverted closed
curve and the open unit disc into the inverted open left side (which misses `0`, the image of `∞`). -/
theorem exists_collarMap (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    ∃ Ψ : ℂ ≃ₜ ℂ, Ψ '' sphere 0 1 = invCurve γ ∧ uninv (rightRef γ) '' (Ψ '' ball 0 1) ⊆ leftSide γ ∧
      ∀ v ∈ ball (0 : ℂ) 1, Ψ v ≠ 0 := by
  obtain ⟨U, V', hUo, hVo, hUb, hUc, -, hdisj, hun, -, -, hLU, -, hUL, -, -⟩ :=
    Supp9B.exists_jordan_sides' hγ h0
  set p := rightRef γ with hp
  have hJ := Supp9B.isJordanCurve_invCurve hγ h0
  have hx₁ : inv p (γ 0 - 1 - I) ∈ U := hLU ⟨_, Supp9B.leftRef_mem_leftSide hγ.2.2.1 h0, rfl⟩
  have hUJ : U ⊆ (invCurve γ)ᶜ := hun ▸ subset_union_left
  have hUeq : connectedComponentIn (invCurve γ)ᶜ (inv p (γ 0 - 1 - I)) = U := by
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hUo hVo hdisj
        (hun ▸ connectedComponentIn_subset _ _) ⟨_, mem_connectedComponentIn (hUJ hx₁), hx₁⟩
    · exact hUc.subset_connectedComponentIn hx₁ hUJ
  obtain ⟨Ψ, hΨs, hΨb, -, -⟩ := InteractingSLE.schoenflies_plane hJ (hUJ hx₁) (hUeq ▸ hUb)
  rw [hUeq] at hΨb
  refine ⟨Ψ, hΨs, by rw [hΨb]; exact hUL, fun v hv h => ?_⟩
  have hvU : Ψ v ∈ U := hΨb ▸ mem_image_of_mem Ψ hv
  exact hUJ hvU (by rw [h]; exact Or.inr rfl)

/-- The displacement clamp `ρ ↦ max 0 (min ρ (1/2))`. -/
def clampHalf (ρ : ℝ) : ℝ := max 0 (min ρ (1 / 2))

theorem continuous_clampHalf : Continuous clampHalf :=
  continuous_const.max (continuous_id.min continuous_const)

/-- **The left collar shift of a proper completion** (Lemma S5's first step, supplement pp. 582–583). For a proper
curve `γ` in `closure ℍ` from `0` and a prefix length `a₀` there is a proper completion `γ'` of `γ|[0, a₀]` such that
every point `γ' s` is `γ s` or a point of `ℍ` on the open left side of `γ`; every real point `γ' s` with `s > a₀` is
negative ("Its new future has no real point at or to the right of its seed"); and the closed right side of `γ` lies in
that of `γ'` ("Moving left enlarges its closed right side"). -/
theorem exists_leftShift (hγ : IsProperCurve γ) (h0 : γ 0 = 0) (a₀ : ℝ≥0) :
    ∃ γ' : ℝ≥0 → ℂ, IsProperCompletion γ a₀ γ' ∧ γ' 0 = 0 ∧
      (∀ s, a₀ < s → (γ' s).im = 0 → (γ' s).re < 0) ∧
      (∀ s, γ' s = γ s ∨ (γ' s ∈ leftSide γ ∧ γ' s ∈ H)) ∧
      closedRightSide γ ⊆ closedRightSide γ' := by
  have h0im : (γ 0).im = 0 := by rw [h0]; rfl
  obtain ⟨Ψ, hΨs, hΨL, hΨ0⟩ := exists_collarMap hγ h0im
  set p := rightRef γ with hp
  have hne : ∀ s, γ s ≠ p := fun s e =>
    Supp9B.rightRef_notMem hγ.2.2.1 h0im (by rw [← hp, ← e]; exact Or.inl ⟨s, rfl⟩)
  -- the circle coordinate
  set u : ℝ≥0 → ℂ := fun s => Ψ.symm (inv p (γ s)) with hu
  have hΨu : ∀ s, Ψ (u s) = inv p (γ s) := fun s => Ψ.apply_symm_apply _
  have hus : ∀ s, ‖u s‖ = 1 := by
    intro s
    have hmem : inv p (γ s) ∈ Ψ '' sphere 0 1 := hΨs ▸ Supp9B.inv_mem_invCurve (Or.inl ⟨s, rfl⟩) hp
    obtain ⟨v, hv, hve⟩ := hmem
    have : u s = v := by rw [hu]; simp only [← hve, Homeomorph.symm_apply_apply]
    rw [this]; simpa using hv
  have huc : Continuous u := continuous_iff_continuousAt.2 fun s =>
    Ψ.symm.continuous.continuousAt.comp ((Supp9B.continuousAt_inv (hne s)).comp hγ.1.continuousAt)
  -- the moved point
  have hcl : ∀ ρ, 0 ≤ clampHalf ρ ∧ clampHalf ρ ≤ 1 / 2 := fun ρ =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  have hnorm : ∀ (c : ℝ) (s : ℝ≥0), 0 ≤ c → c ≤ 1 / 2 → ‖((1 - c : ℝ) : ℂ) * u s‖ = 1 - c := by
    intro c s hc0 hc1
    rw [norm_mul, hus, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  set M : ℝ≥0 × ℝ → ℂ := fun q => uninv p (Ψ (((1 - clampHalf q.2 : ℝ) : ℂ) * u q.1)) with hM
  have hMne : ∀ q : ℝ≥0 × ℝ, Ψ (((1 - clampHalf q.2 : ℝ) : ℂ) * u q.1) ≠ 0 := by
    intro q
    rcases (hcl q.2).1.lt_or_eq with hc | hc
    · refine hΨ0 _ ?_
      rw [mem_ball_zero_iff, hnorm _ _ (hcl q.2).1 (hcl q.2).2]
      linarith
    · rw [← hc, sub_zero, ofReal_one, one_mul, hΨu]
      exact Supp9B.inv_apply_ne_zero (hne q.1)
  have hin : Continuous fun q : ℝ≥0 × ℝ => ((1 - clampHalf q.2 : ℝ) : ℂ) * u q.1 :=
    (continuous_ofReal.comp (continuous_const.sub (continuous_clampHalf.comp continuous_snd))).mul
      (huc.comp continuous_fst)
  have hMc : Continuous M := continuous_iff_continuousAt.2 fun q =>
    ContinuousAt.comp (f := ⇑Ψ ∘ fun q : ℝ≥0 × ℝ => ((1 - clampHalf q.2 : ℝ) : ℂ) * u q.1)
      (Supp9B.continuousAt_uninv (hMne q)) (Ψ.continuous.comp hin).continuousAt
  have hM0 : ∀ (s : ℝ≥0) (ρ : ℝ), clampHalf ρ = 0 → M (s, ρ) = γ s := by
    intro s ρ hρ
    simp only [hM, hρ, sub_zero, ofReal_one, one_mul, hΨu, Supp9B.uninv_inv]
  have hML : ∀ q : ℝ≥0 × ℝ, 0 < clampHalf q.2 → M q ∈ leftSide γ := by
    intro q hq
    refine hΨL ⟨_, ⟨_, ?_, rfl⟩, rfl⟩
    rw [mem_ball_zero_iff, hnorm _ _ (hcl q.2).1 (hcl q.2).2]
    linarith
  -- the displacement
  set Z : Set (ℝ≥0 × ℝ) := {q | 1 / 2 ≤ q.2} ∪
    {q | min (infDist (γ q.1) lowerQuad) 1 ≤ dist (M q) (γ q.1)} with hZ
  have hZc : IsClosed Z := (isClosed_le continuous_const continuous_snd).union
    (isClosed_le (((continuous_infDist_pt _).comp (hγ.1.comp continuous_fst)).min continuous_const)
      (hMc.dist (hγ.1.comp continuous_fst)))
  have hZne : Z.Nonempty := ⟨(0, 1), Or.inl (by norm_num)⟩
  set C : Set ℝ≥0 := Iic a₀ ∪ γ ⁻¹' lowerQuad with hC
  have hCc : IsClosed C := isClosed_Iic.union (isClosed_lowerQuad.preimage hγ.1)
  have hCne : C.Nonempty := ⟨0, Or.inl (show (0 : ℝ≥0) ≤ a₀ from zero_le)⟩
  set ρ : ℝ≥0 → ℝ := fun s => min (infDist ((s, (0 : ℝ)) : ℝ≥0 × ℝ) Z / 2) (infDist s C) with hρdef
  have hρc : Continuous ρ :=
    (((continuous_infDist_pt Z).comp (continuous_id.prodMk continuous_const)).div_const 2).min
      (continuous_infDist_pt C)
  have hρ0 : ∀ s, 0 ≤ ρ s := fun s => le_min (div_nonneg infDist_nonneg (by norm_num)) infDist_nonneg
  have hρZ : ∀ s, 0 < ρ s → ρ s < 1 / 2 ∧
      dist (M (s, ρ s)) (γ s) < min (infDist (γ s) lowerQuad) 1 := by
    intro s hs
    have hf : 0 < infDist ((s, (0 : ℝ)) : ℝ≥0 × ℝ) Z := by
      have := hs.trans_le (min_le_left _ _); linarith
    have hlt : ρ s < infDist ((s, (0 : ℝ)) : ℝ≥0 × ℝ) Z := by
      have := min_le_left (infDist ((s, (0 : ℝ)) : ℝ≥0 × ℝ) Z / 2) (infDist s C); linarith
    have hd : dist ((s, (0 : ℝ)) : ℝ≥0 × ℝ) (s, ρ s) = ρ s := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hρ0 s)]
      exact max_eq_right (hρ0 s)
    have hnot : (s, ρ s) ∉ Z := fun hZm => by
      have := infDist_le_dist_of_mem (x := ((s, (0 : ℝ)) : ℝ≥0 × ℝ)) hZm
      linarith
    simp only [hZ, mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    exact hnot
  have hclamp : ∀ s, clampHalf (ρ s) = ρ s := by
    intro s
    rcases (hρ0 s).lt_or_eq with h | h
    · have h2 := (hρZ s h).1
      simp only [clampHalf, min_eq_left h2.le, max_eq_right (hρ0 s)]
    · rw [← h]; simp [clampHalf]
  have hρ1 : ∀ s, ρ s < 1 := fun s => by
    rcases (hρ0 s).lt_or_eq with h | h
    · linarith [(hρZ s h).1]
    · rw [← h]; norm_num
  set γ' : ℝ≥0 → ℂ := fun s => M (s, ρ s) with hγ'
  have hγ'eq : ∀ s, ρ s = 0 → γ' s = γ s := fun s h => hM0 s (ρ s) (by rw [hclamp, h])
  have hγ'L : ∀ s, 0 < ρ s → γ' s ∈ leftSide γ ∧ γ' s ∈ H ∧ dist (γ' s) (γ s) < 1 := by
    intro s h
    have hL : γ' s ∈ leftSide γ := hML (s, ρ s) (by rw [hclamp]; exact h)
    refine ⟨hL, mem_H_of_mem_leftSide_of_dist_lt hγ h0 hL ((hρZ s h).2.trans_le (min_le_left _ _)),
      (hρZ s h).2.trans_le (min_le_right _ _)⟩
  have hρpre : ∀ s, s ≤ a₀ → ρ s = 0 := fun s hs =>
    le_antisymm ((min_le_right _ _).trans (infDist_zero_of_mem (show s ∈ C from Or.inl hs)).le) (hρ0 s)
  have hρpos : ∀ s, a₀ < s → (γ s).im = 0 → 0 ≤ (γ s).re → 0 < ρ s := by
    intro s hs him hre
    have hγQ : γ s ∉ lowerQuad := by
      rintro ⟨hre', -⟩
      have hz : γ s = γ 0 := by
        rw [h0]; exact Complex.ext (le_antisymm hre' hre) him
      have := hγ.2.1 hz
      rw [this] at hs
      exact absurd hs (not_lt.2 zero_le)
    have hsC : s ∉ C := by
      rintro (h | h)
      · exact absurd h (not_le.2 hs)
      · exact hγQ h
    have hg : 0 < infDist s C := (hCc.notMem_iff_infDist_pos hCne).1 hsC
    have hδ : 0 < infDist (γ s) lowerQuad :=
      (isClosed_lowerQuad.notMem_iff_infDist_pos ⟨0, zero_mem_lowerQuad⟩).1 hγQ
    have hnZ : ((s, (0 : ℝ)) : ℝ≥0 × ℝ) ∉ Z := by
      rintro (h | h)
      · norm_num at h
      · rw [Set.mem_ofPred_eq, hM0 s 0 (by simp [clampHalf]), dist_self] at h
        exact absurd h (not_le.2 (lt_min hδ one_pos))
    have hf := (hZc.notMem_iff_infDist_pos hZne).1 hnZ
    exact lt_min (half_pos hf) hg
  -- the completion
  have hγ'c : Continuous γ' := hMc.comp (continuous_id.prodMk hρc)
  have hγ'inj : Function.Injective γ' := by
    intro s s' e
    have e0 : Ψ (((1 - ρ s : ℝ) : ℂ) * u s) = Ψ (((1 - ρ s' : ℝ) : ℂ) * u s') := by
      have e' := congrArg (inv p) e
      simp only [hγ', hM, hclamp, Supp9B.inv_uninv] at e'
      exact e'
    have e1 := Ψ.injective e0
    have hn := congrArg norm e1
    rw [norm_mul, norm_mul, hus, hus, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by linarith [hρ1 s]), abs_of_pos (by linarith [hρ1 s'])] at hn
    have hρe : ρ s = ρ s' := by linarith
    rw [hρe] at e1
    have hne1 : ((1 - ρ s' : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by linarith [hρ1 s'])
    have e2 := mul_left_cancel₀ hne1 e1
    have e3 : inv p (γ s) = inv p (γ s') := by rw [← hΨu, ← hΨu, e2]
    exact hγ.2.1 (Supp9B.inv_injective p e3)
  have hγ'im : ∀ s, 0 ≤ (γ' s).im := by
    intro s
    rcases (hρ0 s).lt_or_eq with h | h
    · exact le_of_lt (show (0 : ℝ) < (γ' s).im from (hγ'L s h).2.1)
    · rw [hγ'eq s h.symm]; exact hγ.2.2.1 s
  have hγ'n : ∀ s, ‖γ s‖ + (-1) ≤ ‖γ' s‖ := by
    intro s
    rcases (hρ0 s).lt_or_eq with h | h
    · have hd := (hγ'L s h).2.2
      rw [dist_eq_norm] at hd
      have := norm_sub_norm_le (γ s) (γ' s)
      rw [norm_sub_rev] at this
      linarith
    · rw [hγ'eq s h.symm]; linarith
  have hγ'P : IsProperCompletion γ a₀ γ' :=
    ⟨hγ'c, hγ'inj, hγ'im, tendsto_atTop_mono hγ'n (tendsto_atTop_add_const_right _ _ hγ.2.2.2),
      fun t ht => hγ'eq t (hρpre t ht)⟩
  have hγ'0 : γ' 0 = 0 := (hγ'eq 0 (hρpre 0 zero_le)).trans h0
  have hdich : ∀ s, γ' s = γ s ∨ (γ' s ∈ leftSide γ ∧ γ' s ∈ H) := by
    intro s
    rcases (hρ0 s).lt_or_eq with h | h
    · exact Or.inr ⟨(hγ'L s h).1, (hγ'L s h).2.1⟩
    · exact Or.inl (hγ'eq s h.symm)
  refine ⟨γ', hγ'P, hγ'0, ?_, hdich, ?_⟩
  · -- no real point at or to the right of the seed after `a₀`
    intro s hs him
    rcases (hρ0 s).lt_or_eq with h | h
    · exact absurd him (ne_of_gt (show (0 : ℝ) < (γ' s).im from (hγ'L s h).2.1))
    · rw [hγ'eq s h.symm] at him ⊢
      by_contra hre
      exact absurd h (ne_of_lt (hρpos s hs him (not_lt.1 hre)))
  · -- moving left enlarges the closed right side
    have hP' : IsProperCurve γ' := Supp9B.isProperCurve_of_isProperCompletion hγ'P
    have hγ00 : γ' 0 = γ 0 := hγ'0.trans h0.symm
    have hray : ∀ z : ℂ, (z.re = (γ' 0).re ∧ z.im ≤ (γ' 0).im) ↔ (z.re = (γ 0).re ∧ z.im ≤ (γ 0).im) := by
      intro z; rw [hγ00]
    have hdisjLR := Supp9B.disjoint_leftSide_rightSide hγ h0im
    have hRsub : rightSide γ ⊆ (seedRayClosure γ)ᶜ := connectedComponentIn_subset _ _
    have hLsub : leftSide γ ⊆ (seedRayClosure γ)ᶜ := connectedComponentIn_subset _ _
    have hRR : rightSide γ ⊆ rightSide γ' := by
      have hsub : rightSide γ ⊆ (seedRayClosure γ')ᶜ := by
        intro z hz hz'
        rcases hz' with ⟨s, rfl⟩ | hzr
        · rcases hdich s with e | ⟨hL, -⟩
          · exact hRsub hz (e ▸ Or.inl ⟨s, rfl⟩)
          · exact Set.disjoint_left.1 hdisjLR hL hz
        · exact hRsub hz (Or.inr ((hray z).1 hzr))
      have hx : γ 0 + 1 - I ∈ rightSide γ := Supp9B.rightRef_mem_rightSide hγ.2.2.1 h0im
      have := isPreconnected_connectedComponentIn.subset_connectedComponentIn hx hsub
      show rightSide γ ⊆ connectedComponentIn (seedRayClosure γ')ᶜ (γ' 0 + 1 - I)
      rw [hγ00]
      exact this
    rintro z (hz | hz)
    · exact Or.inl (hRR hz)
    rcases hz with ⟨s, rfl⟩ | hzr
    · rcases (hρ0 s).lt_or_eq with h | h
      · -- `γ s` was moved: it is now on the right of `γ'`
        left
        have hnot : γ s ∉ seedRayClosure γ' := by
          rintro (⟨s', e⟩ | ⟨hre, him⟩)
          · rcases (hρ0 s').lt_or_eq with h' | h'
            · exact hLsub (hγ'L s' h').1 (e ▸ Or.inl ⟨s, rfl⟩)
            · rw [hγ'eq s' h'.symm] at e
              have := hγ.2.1 e
              subst this
              exact absurd h (by rw [← h']; exact lt_irrefl _)
          · rw [hγ'0, zero_re] at hre
            rw [hγ'0, zero_im] at him
            have hz : γ s = γ 0 := by
              rw [h0]; exact Complex.ext hre (le_antisymm him (hγ.2.2.1 s))
            have hs0 := hγ.2.1 hz
            subst hs0
            exact absurd (hρpre 0 zero_le) (ne_of_gt h)
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (Supp9B.isClosed_seedRayClosure hP').isOpen_compl _ hnot
        obtain ⟨y, hyR, hyb⟩ := Metric.mem_closure_iff.1
          (mem_closure_rightSide hγ h0im (Or.inl ⟨s, rfl⟩)) ε hε
        have hyR' : y ∈ rightSide γ' := hRR hyR
        have hyb' : y ∈ ball (γ s) ε := by rw [mem_ball, dist_comm]; exact hyb
        have hcc := (convex_ball (γ s) ε).isPreconnected.subset_connectedComponentIn hyb' hball
        have heq : connectedComponentIn (seedRayClosure γ')ᶜ y = rightSide γ' :=
          (connectedComponentIn_eq hyR').symm
        rw [heq] at hcc
        exact hcc (mem_ball_self hε)
      · right
        exact Or.inl ⟨s, hγ'eq s h.symm⟩
    · exact Or.inr (Or.inr ((hray z).2 hzr))

/-- **Lemma S5, the relative step** (supplement p. 582: "take an ordered proper completion `b̂` of the retained
relative second prefix. Move only its unretained future slightly to its left [...] Moving left enlarges its closed right
side, so the whole finite first prefix `a` remains on its right"). If `aR([0, a₁])` (from `w ≥ 0`) and `bR([0, c])`
(from `0`) have ordered proper completions with `bR` on the left, then `bR([0, c])` has a proper completion `b̃` whose
real points after `c` are negative, whose points are points of the old completion or of `ℍ`, and whose closed right
side contains the whole completion of `aR`, in particular `aR([0, a₁])`. -/
theorem exists_leftShift_of_ordered {aR bR : ℝ≥0 → ℂ} {a₁ c : ℝ≥0} {w : ℝ} (hb0 : bR 0 = 0) (hw : 0 ≤ w)
    (ha0 : aR 0 = w) (hord : HasOrderedProperCompletions aR a₁ bR c) :
    ∃ bt : ℝ≥0 → ℂ, IsProperCompletion bR c bt ∧ bt 0 = 0 ∧
      (∀ s, c < s → (bt s).im = 0 → (bt s).re < 0) ∧ (∀ s, (bt s).im = 0 ∨ bt s ∈ H) ∧
      aR '' Icc 0 a₁ ⊆ closedRightSide bt := by
  obtain ⟨ah, bh, hah, hbh, hlr⟩ := hord
  have hahP := Supp9B.isProperCurve_of_isProperCompletion hah
  have hbhP := Supp9B.isProperCurve_of_isProperCompletion hbh
  have hbh0 : bh 0 = 0 := (hbh.2.2.2.2 0 zero_le).trans hb0
  have hah0 : ah 0 = w := (hah.2.2.2.2 0 zero_le).trans ha0
  have hdual := Supp9B.range_subset_closedRightSide hahP hbhP (by rw [hah0]; rfl) (by rw [hbh0]; rfl)
    (by rw [hah0, hbh0]; exact hw) hlr
  obtain ⟨bt, hbt, hbt0, hreal, hdich, hR⟩ := exists_leftShift hbhP hbh0 c
  refine ⟨bt, ⟨hbt.1, hbt.2.1, hbt.2.2.1, hbt.2.2.2.1, fun t ht => (hbt.2.2.2.2 t ht).trans (hbh.2.2.2.2 t ht)⟩,
    hbt0, hreal, fun s => ?_, ?_⟩
  · rcases hdich s with e | ⟨-, hH⟩
    · rcases (hbh.2.2.1 s).lt_or_eq with h | h
      · exact Or.inr (by rw [e]; exact h)
      · exact Or.inl (by rw [e]; exact h.symm)
    · exact Or.inr hH
  · rintro _ ⟨t, ht, rfl⟩
    rw [← hah.2.2.2.2 t ht.2]
    exact hR (hdual ⟨t, rfl⟩)

/-! ### S5b: the boundary values of a left entry chart increase -/

/-- **Boundary values of a chart increase along an untouched real interval** (S5's "On the untouched original-real ray
the inverse map is reflected and injective", with the orientation fixed by the zero lift). Let `c` be a chart of `D`,
let every real `x < L` have an upper half-neighbourhood in `D`, let `c.fwd` have the real boundary value `e x` at each
such `x` from `ℍ`, and let the lift `Im log c.fwd'` tend to `0` there (the fourth clause of `IsLeftEntryChart`).
Then `e` is monotone on `(−∞, L)`. Proof: near a compact `[x₁, x₂]` the lift is below `1 < π/2` on `D`, so
`Re c.fwd'` is positive and `t ↦ Re c.fwd(t + iy)` increases for all small `y > 0`; let `y ↓ 0`. -/
theorem monotoneOn_boundaryValue {D : Set ℂ} {c : Chart} {L : ℝ} {e : ℝ → ℝ} (hD : IsDomainChart D c)
    (hfree : ∀ x < L, ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ D)
    (he : ∀ x < L, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ)))
    (hlift : ∀ x < L, Tendsto c.2.2 (𝓝[H] (x : ℂ)) (𝓝 0)) :
    MonotoneOn e (Iio L) := by
  obtain ⟨Lg, hLg, hLeq⟩ := hD.2.2
  intro x₁ hx₁ x₂ hx₂ h12
  have hx₁' : x₁ < L := hx₁
  have hx₂' : x₂ < L := hx₂
  -- good points: in `D`, with lift below `1`
  have hloc : ∀ t < L, ∃ r > 0, ∀ z ∈ H, dist z t < r → z ∈ D ∧ |c.2.2 z| < 1 := by
    intro t ht
    obtain ⟨r, hr, hs⟩ := Metric.mem_nhdsWithin_iff.1
      ((hfree t ht).and ((hlift t ht).eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)))
    refine ⟨r, hr, fun z hz hd => ?_⟩
    have h := hs ⟨mem_ball.2 hd, hz⟩
    refine ⟨h.1, ?_⟩
    have h2 : dist (c.2.2 z) 0 < 1 := h.2
    rwa [Real.dist_eq, sub_zero] at h2
  have hK : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), ∀ t ∈ Icc x₁ x₂, 0 < y →
      ((t : ℂ) + (y : ℂ) * I) ∈ D ∧ |c.2.2 ((t : ℂ) + (y : ℂ) * I)| < 1 := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t ht => ?_
    obtain ⟨r, hr, hs⟩ := hloc t (lt_of_le_of_lt ht.2 hx₂')
    filter_upwards [Metric.ball_mem_nhds (((0 : ℝ), t) : ℝ × ℝ) (half_pos hr)] with q hq hy
    have hq' : dist q ((0 : ℝ), t) < r / 2 := hq
    rw [Prod.dist_eq] at hq'
    have h1 : |q.1| < r / 2 := by
      have := lt_of_le_of_lt (le_max_left _ _) hq'; rwa [Real.dist_eq, sub_zero] at this
    have h2 : |q.2 - t| < r / 2 := by
      have := lt_of_le_of_lt (le_max_right _ _) hq'; rwa [Real.dist_eq] at this
    refine hs _ (show 0 < ((q.2 : ℂ) + q.1 * I).im by simpa using hy) ?_
    rw [Complex.dist_eq]
    have he' : (q.2 : ℂ) + q.1 * I - t = ((q.2 - t : ℝ) : ℂ) + (q.1 : ℂ) * I := by push_cast; ring
    rw [he']
    calc ‖((q.2 - t : ℝ) : ℂ) + (q.1 : ℂ) * I‖ ≤ ‖((q.2 - t : ℝ) : ℂ)‖ + ‖(q.1 : ℂ) * I‖ := norm_add_le _ _
      _ = |q.2 - t| + |q.1| := by
        rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
      _ < r := by linarith
  obtain ⟨y₀, hy₀, hy₀s⟩ := Metric.eventually_nhds_iff.1 hK
  have hpi : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : ∀ y : ℝ, 0 < y → y < y₀ →
      (c.1 ((x₁ : ℂ) + (y : ℂ) * I)).re ≤ (c.1 ((x₂ : ℂ) + (y : ℂ) * I)).re := by
    intro y hy hyy
    have hPt : ∀ t ∈ Icc x₁ x₂, ((t : ℂ) + (y : ℂ) * I) ∈ D ∧ |c.2.2 ((t : ℂ) + (y : ℂ) * I)| < 1 := fun t ht =>
      hy₀s (by rw [Real.dist_eq, sub_zero, abs_of_pos hy]; exact hyy) t ht hy
    have hder : ∀ t ∈ Icc x₁ x₂, HasDerivAt (fun s : ℝ => (c.1 ((s : ℂ) + (y : ℂ) * I)).re)
        (deriv c.1 ((t : ℂ) + (y : ℂ) * I)).re t := by
      intro t ht
      have hz := (hPt t ht).1
      have hd : DifferentiableAt ℂ c.1 ((t : ℂ) + (y : ℂ) * I) :=
        (hD.differentiableOn_fwd _ hz).differentiableAt (hD.isOpen.mem_nhds hz)
      have h1 := hd.hasDerivAt.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).add_const ((y : ℂ) * I))
      rw [mul_one] at h1
      exact h1.real_of_complex
    have hpos : ∀ t ∈ Icc x₁ x₂, 0 < (deriv c.1 ((t : ℂ) + (y : ℂ) * I)).re := by
      intro t ht
      obtain ⟨hz, hl⟩ := hPt t ht
      have hEq : c.2.2 ((t : ℂ) + (y : ℂ) * I) = (Lg ((t : ℂ) + (y : ℂ) * I)).im := hLeq hz
      rw [← hLg.2 _ hz, Complex.exp_re]
      refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
      · rw [← hEq]; linarith [neg_abs_le (c.2.2 ((t : ℂ) + (y : ℂ) * I))]
      · rw [← hEq]; linarith [le_abs_self (c.2.2 ((t : ℂ) + (y : ℂ) * I))]
    have hM := monotoneOn_of_deriv_nonneg (convex_Icc x₁ x₂)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hder t (interior_subset ht)).deriv]; exact (hpos t (interior_subset ht)).le)
    exact hM ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12
  have hlim : ∀ x < L, Tendsto (fun y : ℝ => (c.1 ((x : ℂ) + y * I)).re) (𝓝[>] 0) (𝓝 (e x)) := by
    intro x hx
    have hcont : Continuous fun y : ℝ => (x : ℂ) + y * I := by fun_prop
    have hmap : Tendsto (fun y : ℝ => (x : ℂ) + y * I) (𝓝[>] 0) (𝓝[H] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h0 := hcont.tendsto 0
        simp only [ofReal_zero, zero_mul, add_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        show 0 < ((x : ℂ) + y * I).im
        simpa using hy
    have := (Complex.continuous_re.tendsto _).comp ((he x hx).comp hmap)
    simpa [Function.comp_def] using this
  exact le_of_tendsto_of_tendsto (hlim x₁ hx₁') (hlim x₂ hx₂')
    (by filter_upwards [Ioo_mem_nhdsGT hy₀] with y hy using hmono y hy.1 hy.2)

/-- **S5b: orientation of the left entry chart on the untouched real ray** (S5: "Every new real contact of this
completion is strictly below `v_L`, hence outside `I`. It therefore pulls back to a genuine original-real point to the
left of the old base [...] On the untouched original-real ray the inverse map is reflected and injective"). For
`A = p([0, 1])`, a left entry chart `c` of `D_A` at `L = min(A ∩ ℝ)` and a continuous extension `g` of its inverse to
`closure ℍ`, the boundary values `e` of `c` on `(−∞, L)` are strictly increasing and negative, `g ∘ e` is the identity
there, and every negative real is a boundary value. -/
theorem IsLeftEntryChart.exists_boundary_orient {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    {c : Chart} (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) :
    ∃ e : ℝ → ℝ, (∀ x < realMin (p '' Icc 0 1), Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ))) ∧
      StrictMonoOn e (Iio (realMin (p '' Icc 0 1))) ∧
      (∀ x < realMin (p '' Icc 0 1), e x < 0 ∧ g (e x) = x) ∧
      ∀ y : ℝ, y < 0 → ∃ x < realMin (p '' Icc 0 1), e x = y := by
  set A := p '' Icc 0 1 with hA
  set L := realMin A with hL
  obtain ⟨e, he, he0⟩ := hc.2.1
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  obtain ⟨-, -, hrb, -, -⟩ := realBase_facts hp hp0
  have hfreeAt : ∀ x < L, HalfPlaneSep.IsFreeAt A (x : ℂ) := fun x hx =>
    isFreeAt_of_lt hAc (fun y hy => (hrb y hy).1) hx
  have hfree : ∀ x < L, ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ fillH A := fun x hx =>
    eventually_mem_of_isFreeAt (hfreeAt x hx)
  have hmono := monotoneOn_boundaryValue hc.1 hfree he hc.2.2.2
  have hginv : ∀ x < L, g (e x) = x := fun x hx => eq_of_boundaryValue hc.1 hgc hgi (he x hx) (hfreeAt x hx)
  have hstrict : StrictMonoOn e (Iio L) := by
    intro x₁ hx₁ x₂ hx₂ h12
    refine lt_of_le_of_ne (hmono hx₁ hx₂ h12.le) fun h => ?_
    have := (hginv x₁ hx₁).symm.trans ((congrArg (fun r : ℝ => g (r : ℂ)) h).trans (hginv x₂ hx₂))
    exact absurd (Complex.ofReal_injective this) (ne_of_lt h12)
  have hle0 : ∀ x < L, e x ≤ 0 := by
    intro x hx
    refine ge_of_tendsto he0 ?_
    filter_upwards [Ioo_mem_nhdsLT hx] with x' hx'
    exact hmono hx (show x' < L from hx'.2) hx'.1.le
  have hneg : ∀ x < L, e x < 0 := by
    intro x hx
    obtain ⟨x', hx'1, hx'2⟩ := exists_between hx
    exact (hstrict hx (show x' < L from hx'2) hx'1).trans_le (hle0 x' hx'2)
  have hcont : ContinuousOn e (Iio L) := fun x hx => by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_boundaryValue he hx)
    simp only [Function.comp_def, Complex.ofReal_re] at h
    exact ContinuousAt.continuousWithinAt h
  refine ⟨e, he, hstrict, fun x hx => ⟨hneg x hx, hginv x hx⟩, fun y hy => ?_⟩
  -- a boundary value below `y`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z ∈ H \ fillH A, R < ‖z‖ → |y| + 1 < ‖c.1 z‖ := by
    have h1 := hc.2.2.1
      (show (closedBall (0 : ℂ) (|y| + 1))ᶜ ∈ cobounded ℂ from Metric.isBounded_closedBall)
    obtain ⟨S, hS, T, hT, hST⟩ := mem_inf_iff.1 h1
    obtain ⟨R, hRs⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).mem_iff.1 hS
    refine ⟨R, fun z hz hzR => ?_⟩
    have hzS : z ∈ S := hRs.2 (by simpa [mem_closedBall, dist_zero_right] using hzR)
    have hzT : z ∈ T := mem_principal.1 hT hz
    have : z ∈ S ∩ T := ⟨hzS, hzT⟩
    rw [← hST] at this
    simpa [mem_closedBall, dist_zero_right] using this
  set x₀ : ℝ := min (L - 1) (-(|R| + 1)) with hx₀
  have hx₀L : x₀ < L := (min_le_left _ _).trans_lt (by linarith)
  have hx₀R : R < ‖((x₀ : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : x₀ ≤ -(|R| + 1) := min_le_right _ _
    have h2 : |R| + 1 ≤ |x₀| := by rw [abs_of_neg (show x₀ < 0 by linarith [abs_nonneg R])]; linarith
    linarith [le_abs_self R]
  have hbig : |y| + 1 ≤ |e x₀| := by
    have : (𝓝[H] ((x₀ : ℝ) : ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_H_of_im_nonneg (by simp))
    have hlim := (continuous_norm.tendsto _).comp (he x₀ hx₀L)
    rw [Complex.norm_real, Real.norm_eq_abs] at hlim
    refine ge_of_tendsto hlim ?_
    have hR' : ∀ᶠ z in 𝓝[H] ((x₀ : ℝ) : ℂ), R < ‖z‖ :=
      nhdsWithin_le_nhds ((continuous_norm.isOpen_preimage _ isOpen_Ioi).mem_nhds hx₀R)
    filter_upwards [hfree x₀ hx₀L, hR'] with z hz hzR
    exact (hR z hz hzR).le
  have he₀ : e x₀ < y := by
    have := hneg x₀ hx₀L
    rw [abs_of_neg this] at hbig
    linarith [neg_abs_le y]
  obtain ⟨x₁, hx₁, hx₁y⟩ : ∃ x₁ ∈ Ioo x₀ L, y < e x₁ :=
    ((Filter.eventually_mem_set.2 (Ioo_mem_nhdsLT hx₀L)).and (he0.eventually (lt_mem_nhds hy))).exists.imp
      fun x h => ⟨h.1, h.2⟩
  have hsub : Icc x₀ x₁ ⊆ Iio L := fun x hx => lt_of_le_of_lt hx.2 hx₁.2
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hx₁.1.le (hcont.mono hsub) ⟨he₀.le, hx₁y.le⟩
  exact ⟨x, hsub hx, hxy⟩

end SB

end Theorem14

end InteractingSLE
