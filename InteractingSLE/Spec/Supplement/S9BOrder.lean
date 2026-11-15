/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BTransfer
import InteractingSLE.Spec.Supplement.S9Contacts
import InteractingSLE.Spec.Supplement.S10Order

/-!
# Supplement §7.2 / §9: the contact order of ordered proper curves (Lemma G5, Aux. lemma 84)

Packet PROVE-SUPP9-C.

**Theorem** (`contact_order`; Lemma G5, supplement p. 493, for a common seed, and Aux. lemma 84, p. 298, for
distinct seeds). Let `γ₁`, `γ₂` be continuous injective proper curves in the closed upper half-plane from real
seeds `γ₂(0) ≤ γ₁(0)`, with `γ₂` in the closed left side of `γ₁` (the side of `γ₁` closed along its lower
vertical ray). If `γ₁(s) = γ₂(t)`, `γ₁(s') = γ₂(t')` and `s < s'`, then `t < t'`.

*Proof.* Suppose `t' < t`. Replace `t'` by the first time `γ₂` meets `γ₁([s', ∞))` (and `s'` by the corresponding
parameter); then `γ₂([0, t'))` avoids `γ₁([s', ∞))`. Let `δ` follow `γ₂` up to `t'` and then `γ₁` from `s'`: a proper
curve from `γ₂(0)` sharing its tail with `γ₁`.

1. `γ₁(s)` lies on the right of `δ`: `γ₁` is on the closed right of `γ₂` (duality), `δ` agrees with `γ₂` on
   `[0, t']`, and `γ₁([0, s])` avoids the rest of `δ` (the reflected pieces lemma, `mem_closedRightSide_of_avoid`).
2. Near every point of the common open tail `γ₁((s', ∞))` the two closed curves coincide, so their sides pair up
   (`local_sides_pairing`: the left side of `δ` is locally the left or the right side of `γ₁`). Away from the closed
   set `Z = γ₂([0, t']) ∪ γ₁([0, s']) ∪` (the two seed rays) the statement "left of `δ` iff left of `γ₁`" is
   therefore locally constant. It holds in the far lower left, which is connected in the complement of `Z` to the
   whole region far from the origin outside a vertical strip below the real line, and to the tail: there the
   sides of `δ` and `γ₁` agree.
3. After time `t`, `γ₂` is on the right of `δ`: it starts there, cannot meet `γ₂([0, t'])` or the seed ray, and at a
   first meeting with the tail of `γ₁` it would approach the tail from the right of `δ`, hence from the right of
   `γ₁`, while it lies in the closed left of `γ₁`. So `γ₂(u)` stays on the right of `δ`; for `u` large it is far
   from the origin in the closed upper half-plane, where the right of `δ` is the right of `γ₁`. Contradiction.

The local pairing (step 2) is proved with the Schoenflies straightening of the inverted closed curve
(`exists_straightening`, PROVE-SUPP9-B): near a point of a proper curve, the left side and the right side are each
contained in one preconnected thin sector (`exists_local_sides`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal

namespace InteractingSLE

namespace Supp9B

/-! ### Reflection of the left side and the reflected pieces lemma -/

theorem refl_image_leftSide_subset {γ : ℝ≥0 → ℂ} (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) :
    refl '' leftSide γ ⊆ rightSide (reflectCurve γ) := by
  have hx : γ 0 - 1 - I ∈ (seedRayClosure γ)ᶜ :=
    lowerLeft_subset_compl hγ (left_ref_mem_lowerLeft h0)
  have h1 := continuous_refl.continuousOn.image_connectedComponentIn_subset (s := (seedRayClosure γ)ᶜ) hx
  have h2 : refl '' (seedRayClosure γ)ᶜ ⊆ (seedRayClosure (reflectCurve γ))ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzS
    have := refl_image_seedRayClosure_subset (reflectCurve γ) ⟨_, hzS, rfl⟩
    rw [refl_refl, reflectCurve_reflectCurve] at this
    exact hz this
  have hr : refl (γ 0 - 1 - I) = reflectCurve γ 0 + 1 - I := by
    apply Complex.ext
    · simp [reflectCurve]; ring
    · simp [reflectCurve, h0]
  rw [hr] at h1
  exact h1.trans (connectedComponentIn_mono _ h2)

theorem isProperCurve_reflectCurve {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) : IsProperCurve (reflectCurve γ) :=
  isProperCurve_of_isProperCompletion (isProperCompletion_reflectCurve (a := 0) ⟨hγ.1, hγ.2.1, hγ.2.2.1,
    hγ.2.2.2, fun _ _ => rfl⟩)

/-- **The reflected pieces lemma.** Let `α'`, `α''` be proper curves from the same real seed agreeing on `[0, a]`,
and let `β'` be a proper curve from a real seed weakly to the right, contained in the closed right side of `α'`.
If `β'([0, t])` avoids `α''([a, ∞))`, then `β'(t)` lies in the closed right side of `α''`. -/
theorem mem_closedRightSide_of_avoid {α' α'' β' : ℝ≥0 → ℂ} {a : ℝ≥0} (hα' : IsProperCurve α')
    (hα'' : IsProperCurve α'') (h0 : (α' 0).im = 0) (hagree : ∀ t ≤ a, α'' t = α' t)
    (hβ' : IsProperCurve β') (hβ0 : (β' 0).im = 0) (hseed : (α' 0).re ≤ (β' 0).re)
    (hord : range β' ⊆ closedRightSide α') {t : ℝ≥0} (havoid : ∀ u ≤ t, ∀ s, a ≤ s → β' u ≠ α'' s) :
    β' t ∈ closedRightSide α'' := by
  have hordr : range (reflectCurve β') ⊆ closedLeftSide (reflectCurve α') := by
    rintro _ ⟨u, rfl⟩
    rcases hord ⟨u, rfl⟩ with hR | hS
    · exact Or.inl (refl_image_rightSide_subset hα'.2.2.1 h0 ⟨_, hR, rfl⟩)
    · exact Or.inr (refl_image_seedRayClosure_subset α' ⟨_, hS, rfl⟩)
  have hmem := mem_closedLeftSide_of_avoid (isProperCurve_reflectCurve hα')
    (isProperCurve_reflectCurve hα'') (by simp [reflectCurve, h0])
    (fun u hu => by simp [reflectCurve, hagree u hu]) (isProperCurve_reflectCurve hβ')
    (by simp [reflectCurve, hβ0]) (by simp [reflectCurve, hseed]) hordr
    (fun u hu s hs h => havoid u hu s hs (refl_injective h))
  have h0'' : (α'' 0).im = 0 := by rw [hagree 0 zero_le]; exact h0
  rcases hmem with hL | hS
  · have := refl_image_leftSide_subset (isProperCurve_reflectCurve hα'').2.2.1
      (by simp [reflectCurve, h0'']) ⟨_, hL, rfl⟩
    rw [reflectCurve_reflectCurve] at this
    exact Or.inl (by simpa [reflectCurve] using this)
  · have := refl_image_seedRayClosure_subset (reflectCurve α'') ⟨_, hS, rfl⟩
    rw [reflectCurve_reflectCurve] at this
    exact Or.inr (by simpa [reflectCurve] using this)

/-! ### Local sides near a point of a proper curve -/

section LocalSides

variable {γ : ℝ≥0 → ℂ}

/-- **The straightening with both sides.** The Schoenflies homeomorphism `h` carries the unit circle onto the
inverted closed curve; in the straightened coordinates `Ψ = h⁻¹ ∘ inv` the left side lies inside the unit disc and
the punctured right side outside the closed unit disc, and conversely. -/
theorem exists_straightening_sides (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    ∃ h : ℂ ≃ₜ ℂ, h '' sphere 0 1 = invCurve γ ∧
      (∀ z ∈ leftSide γ, ‖h.symm (inv (rightRef γ) z)‖ < 1) ∧
      (∀ z ∈ rightSide γ, z ≠ rightRef γ → 1 < ‖h.symm (inv (rightRef γ) z)‖) ∧
      (∀ x : ℂ, ‖x‖ < 1 → uninv (rightRef γ) (h x) ∈ leftSide γ) ∧
      (∀ x : ℂ, 1 < ‖x‖ → uninv (rightRef γ) (h x) ∈ rightSide γ) := by
  obtain ⟨U, V, hUo, hVo, -, hUc, -, hdisj, hun, -, -, hLU, hRV, hUL, hVR, -⟩ :=
    exists_jordan_sides' hγ h0
  obtain ⟨h, hs, hbJ, hLb⟩ := exists_straightening hγ h0
  set p := rightRef γ with hp
  have hVJ : V ⊆ (invCurve γ)ᶜ := hun ▸ subset_union_right
  have hqL := leftRef_mem_leftSide hγ.2.2.1 h0
  have hqU : inv p (γ 0 - 1 - I) ∈ U := hLU ⟨_, hqL, rfl⟩
  have hqb : inv p (γ 0 - 1 - I) ∈ h '' ball 0 1 := hLb ⟨_, hqL, rfl⟩
  have hbo : IsOpen (h '' ball (0 : ℂ) 1) := h.isOpenMap _ isOpen_ball
  have heo : IsOpen (h '' (closedBall (0 : ℂ) 1)ᶜ) := h.isOpenMap _ isClosed_closedBall.isOpen_compl
  have hbe : Disjoint (h '' ball (0 : ℂ) 1) (h '' (closedBall (0 : ℂ) 1)ᶜ) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    rw [h.injective hxy] at hy
    exact hy (ball_subset_closedBall hx)
  have hUb : U ⊆ h '' ball 0 1 := by
    have hcov : U ⊆ h '' ball 0 1 ∪ h '' (closedBall (0 : ℂ) 1)ᶜ := by
      intro w hw
      obtain ⟨x, rfl⟩ := h.surjective w
      have hxs : x ∉ sphere (0 : ℂ) 1 := fun hx => (hun ▸ subset_union_left : U ⊆ (invCurve γ)ᶜ) hw
        (hs ▸ mem_image_of_mem h hx)
      rcases lt_trichotomy ‖x‖ 1 with hlt | heq | hgt
      · exact Or.inl ⟨x, by simpa using hlt, rfl⟩
      · exact absurd (by simpa using heq) hxs
      · exact Or.inr ⟨x, by simpa using hgt, rfl⟩
    rcases hUc.subset_or_subset hbo heo hbe hcov with h' | h'
    · exact h'
    · obtain ⟨x, hx, hxq⟩ := hqb
      exact absurd (hxq ▸ h' hqU) (Set.disjoint_left.1 hbe ⟨x, hx, rfl⟩)
  have hbU : h '' ball 0 1 ⊆ U := by
    have hpc : IsPreconnected (h '' ball (0 : ℂ) 1) :=
      (convex_ball _ _).isPreconnected.image _ h.continuous.continuousOn
    rcases hpc.subset_or_subset hUo hVo hdisj (hun ▸ hbJ) with h' | h'
    · exact h'
    · exact absurd (h' hqb) (Set.disjoint_left.1 hdisj hqU)
  refine ⟨h, hs, fun z hz => ?_, fun z hz hzp => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := hLb ⟨z, hz, rfl⟩
    rw [← hyz, Homeomorph.symm_apply_apply]
    simpa using hy
  · have hzV : inv p z ∈ V := hRV ⟨z, ⟨hz, hzp⟩, rfl⟩
    set x := h.symm (inv p z) with hx
    have hhx : h x = inv p z := by rw [hx, Homeomorph.apply_symm_apply]
    rcases lt_trichotomy ‖x‖ 1 with hlt | heq | hgt
    · exact absurd (hbU ⟨x, by simpa using hlt, hhx⟩) (Set.disjoint_right.1 hdisj hzV)
    · exact absurd (hs ▸ mem_image_of_mem h (show x ∈ sphere (0 : ℂ) 1 by simpa using heq))
        (hhx ▸ hVJ hzV)
    · exact hgt
  · exact hUL ⟨h x, hbU ⟨x, by simpa using hx, rfl⟩, rfl⟩
  · have hxs : h x ∉ invCurve γ := by
      rw [← hs]
      rintro ⟨y, hy, hyx⟩
      rw [h.injective hyx] at hy
      exact absurd (by simpa using hy : ‖x‖ = 1) hx.ne'
    have hxU : h x ∉ U := fun hU => by
      obtain ⟨y, hy, hyx⟩ := hUb hU
      rw [h.injective hyx] at hy
      exact absurd (by simpa using hy : ‖x‖ < 1) (not_lt.2 hx.le)
    have hxV : h x ∈ V := by
      rcases (hun ▸ hxs : h x ∈ U ∪ V) with h' | h'
      · exact absurd h' hxU
      · exact h'
    exact hVR ⟨h x, hxV, rfl⟩

/-- **Local sides.** Near a point `ℓ(t₀)` of a closed proper curve (`ℓ` its seed-line parametrization), the left
side lies in one preconnected set `PL` and the right side in one preconnected set `PR`, both inside any prescribed
neighbourhood `N`: thin sectors on the two sides of a short arc in the Schoenflies coordinates. -/
theorem exists_local_sides (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) (t₀ : ℝ) {N : Set ℂ}
    (hN : N ∈ 𝓝 (seedLine γ t₀)) :
    ∃ PL PR : Set ℂ, IsPreconnected PL ∧ IsPreconnected PR ∧ PL ⊆ leftSide γ ∩ N ∧
      PR ⊆ rightSide γ ∩ N ∧
      ∀ᶠ w in 𝓝 (seedLine γ t₀), (w ∈ leftSide γ → w ∈ PL) ∧ (w ∈ rightSide γ → w ∈ PR) := by
  obtain ⟨h, hs, hL, hR, hbL, hbR⟩ := exists_straightening_sides hγ h0
  set p := rightRef γ with hp
  set ℓ := seedLine γ with hℓ
  set Ψ : ℂ → ℂ := fun z => h.symm (inv p z) with hΨ
  have hpS : p ∉ seedRayClosure γ := rightRef_notMem hγ.2.2.1 h0
  have hℓp : ∀ t, ℓ t ≠ p := fun t h' => hpS (h' ▸ seedLine_mem h0 t)
  have hΨs : ∀ z ∈ seedRayClosure γ, Ψ z ∈ sphere (0 : ℂ) 1 := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ : inv p z ∈ h '' sphere 0 1 := hs ▸ inv_mem_invCurve hz hp
    simpa [hΨ, ← hyz] using hy
  have hΨc : ∀ z, z ≠ p → ContinuousAt Ψ z := fun z hz =>
    h.symm.continuous.continuousAt.comp (continuousAt_inv hz)
  have hΨinj : ∀ z w, Ψ z = Ψ w → z = w := fun z w hzw =>
    inv_injective p (h.symm.injective hzw)
  have hrec : ∀ z, uninv p (h (Ψ z)) = z := fun z => by simp [hΨ]
  have hΨℓ : Continuous fun t => Ψ (ℓ t) := continuous_iff_continuousAt.2 fun t =>
    (hΨc _ (hℓp t)).comp (continuous_seedLine hγ.1).continuousAt
  set q := ℓ t₀ with hq
  obtain ⟨ε₀, hε₀, hε₀N⟩ := Metric.mem_nhds_iff.1 hN
  -- the straightened image of the ball `B(q, ε₀)`
  set W' := h ⁻¹' ({0}ᶜ ∩ uninv p ⁻¹' ball q ε₀) with hW'
  have hW'o : IsOpen W' :=
    ((continuousOn_uninv p).isOpen_inter_preimage isOpen_compl_singleton isOpen_ball).preimage h.continuous
  -- a short parameter interval around `t₀`
  obtain ⟨ρ, hρ, hρb⟩ : ∃ ρ > 0, ∀ t, dist t t₀ ≤ ρ → dist (ℓ t) q < ε₀ := by
    obtain ⟨ρ', hρ', hb⟩ := Metric.continuous_iff.1 (continuous_seedLine hγ.1) t₀ ε₀ hε₀
    exact ⟨ρ' / 2, by positivity, fun t ht => hb t (by linarith)⟩
  set C := (fun t => Ψ (ℓ t)) '' Icc (t₀ - ρ) (t₀ + ρ) with hC
  have hCcpt : IsCompact C := isCompact_Icc.image hΨℓ
  have hCconn : IsPreconnected C := isPreconnected_Icc.image _ hΨℓ.continuousOn
  have hCs : C ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨t, -, rfl⟩; exact hΨs _ (seedLine_mem h0 t)
  have hCW' : C ⊆ W' := by
    rintro _ ⟨t, ht, rfl⟩
    have hd : dist t t₀ ≤ ρ := by rw [Real.dist_eq, abs_le]; constructor <;> linarith [ht.1, ht.2]
    refine ⟨?_, ?_⟩
    · show h (h.symm (inv p (ℓ t))) ∈ ({0}ᶜ : Set ℂ)
      rw [Homeomorph.apply_symm_apply]; exact inv_apply_ne_zero (hℓp t)
    · show uninv p (h (h.symm (inv p (ℓ t)))) ∈ ball q ε₀
      rw [Homeomorph.apply_symm_apply, uninv_inv]; exact hρb t hd
  obtain ⟨η₀, hη₀, hthick⟩ := hCcpt.exists_thickening_subset_open hW'o hCW'
  set η : ℝ := min (η₀ / 2) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hηη₀ : η < η₀ := (min_le_left _ _).trans_lt (by linarith)
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  -- the two thin sectors
  set mul : ℝ × ℂ → ℂ := fun q => (q.1 : ℂ) * q.2 with hmul
  have hmulc : Continuous mul := by rw [hmul]; fun_prop
  set Ain := mul '' (Ioo (1 - η) 1 ×ˢ C) with hAin
  set Aout := mul '' (Ioo 1 (1 + η) ×ˢ C) with hAout
  have hnorm : ∀ r : ℝ, ∀ c ∈ C, 0 < r → ‖mul (r, c)‖ = r := by
    intro r c hc hr
    have hc1 : ‖c‖ = 1 := by simpa using hCs hc
    simp only [hmul, norm_mul, hc1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hthin : ∀ r : ℝ, ∀ c ∈ C, |r - 1| < η → mul (r, c) ∈ W' := by
    intro r c hc hr
    refine hthick (mem_thickening_iff.2 ⟨c, hc, ?_⟩)
    have hc1 : ‖c‖ = 1 := by simpa using hCs hc
    rw [dist_eq_norm, show mul (r, c) - c = ((r - 1 : ℝ) : ℂ) * c by simp only [hmul]; push_cast; ring,
      norm_mul, hc1, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hr.trans hηη₀
  have hAinW : Ain ⊆ W' := by
    rintro _ ⟨⟨r, c⟩, ⟨hr, hc⟩, rfl⟩
    exact hthin r c hc (by rw [abs_lt]; constructor <;> linarith [hr.1, hr.2])
  have hAoutW : Aout ⊆ W' := by
    rintro _ ⟨⟨r, c⟩, ⟨hr, hc⟩, rfl⟩
    exact hthin r c hc (by rw [abs_lt]; constructor <;> linarith [hr.1, hr.2])
  have hpcA : ∀ A ⊆ W', IsPreconnected A → IsPreconnected (uninv p '' (h '' A)) := by
    intro A hAW hA
    refine (hA.image _ h.continuous.continuousOn).image _ ((continuousOn_uninv p).mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact (hAW hx).1
  have hAinc : IsPreconnected Ain := (isPreconnected_Ioo.prod hCconn).image _ hmulc.continuousOn
  have hAoutc : IsPreconnected Aout := (isPreconnected_Ioo.prod hCconn).image _ hmulc.continuousOn
  refine ⟨uninv p '' (h '' Ain), uninv p '' (h '' Aout), hpcA _ hAinW hAinc, hpcA _ hAoutW hAoutc,
    ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨⟨r, c⟩, ⟨hr, hc⟩, rfl⟩ := hx
    refine ⟨hbL _ ?_, hε₀N (hAinW ⟨(r, c), ⟨hr, hc⟩, rfl⟩).2⟩
    rw [hnorm r c hc (by linarith [hr.1])]; exact hr.2
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨⟨r, c⟩, ⟨hr, hc⟩, rfl⟩ := hx
    refine ⟨hbR _ ?_, hε₀N (hAoutW ⟨(r, c), ⟨hr, hc⟩, rfl⟩).2⟩
    rw [hnorm r c hc (by linarith [hr.1])]; exact hr.1
  -- the rest of the closed curve, in straightened coordinates
  set Fb := h.symm '' (inv p '' (ℓ '' (Iic (t₀ - ρ) ∪ Ici (t₀ + ρ))) ∪ {0}) with hFb
  have hFbc : IsClosed Fb := by
    rw [hFb, h.image_symm]
    exact (isClosed_inv_image_union (isClosed_seedLine_image hγ (isClosed_Iic.union isClosed_Ici))).preimage
      h.continuous
  have hsph : sphere (0 : ℂ) 1 ⊆ C ∪ Fb := by
    intro y hy
    have hhy : h y ∈ invCurve γ := hs ▸ mem_image_of_mem h hy
    rcases hhy with ⟨z, hz, hzy⟩ | hz0
    · obtain ⟨t, rfl⟩ := seedLine_surj h0 hz
      have hy' : y = Ψ (ℓ t) := by
        show y = h.symm (inv p (ℓ t))
        rw [show inv p (ℓ t) = h y from hzy, Homeomorph.symm_apply_apply]
      by_cases ht : t ∈ Icc (t₀ - ρ) (t₀ + ρ)
      · exact Or.inl ⟨t, ht, hy'.symm⟩
      · refine Or.inr ⟨inv p (ℓ t), Or.inl ⟨ℓ t, ⟨t, ?_, rfl⟩, rfl⟩, hy'.symm⟩
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with ht | ht
        · exact Or.inl ht.le
        · exact Or.inr ht.le
    · exact Or.inr ⟨0, Or.inr rfl, by rw [← mem_singleton_iff.1 hz0, Homeomorph.symm_apply_apply]⟩
  have hnotFb : Ψ q ∉ Fb := by
    rintro ⟨w, hw | hw, hwt⟩
    · obtain ⟨_, ⟨t', ht', rfl⟩, rfl⟩ := hw
      have := seedLine_injective hγ h0 (hΨinj _ _ hwt)
      rw [this] at ht'
      rcases ht' with h' | h'
      · exact absurd (mem_Iic.1 h') (by linarith)
      · exact absurd (mem_Ici.1 h') (by linarith)
    · rw [mem_singleton_iff.1 hw] at hwt
      exact inv_apply_ne_zero (hℓp t₀) (h.symm.injective (hwt.symm.trans (by simp)))
  -- the eventual statement, by radial projection
  have hy₀ : Ψ q ∈ sphere (0 : ℂ) 1 := hΨs _ (seedLine_mem h0 t₀)
  have hn1 : ‖Ψ q‖ = 1 := by simpa using hy₀
  have hy0 : Ψ q ≠ 0 := by intro h'; rw [h', norm_zero] at hn1; norm_num at hn1
  have hc := hΨc _ (hℓp t₀)
  set Nr : ℂ → ℂ := fun y => y / (‖y‖ : ℂ) with hNr
  have hNc : ContinuousAt Nr (Ψ q) :=
    continuousAt_id.div (continuous_ofReal.comp continuous_norm).continuousAt (by simpa using hy0)
  have hNy : Nr (Ψ q) = Ψ q := by simp [hNr, hn1]
  have hO : Fbᶜ ∈ 𝓝 (Nr (Ψ q)) := by
    rw [hNy]; exact hFbc.isOpen_compl.mem_nhds hnotFb
  have e1 : ∀ᶠ w in 𝓝 q, Nr (Ψ w) ∈ Fbᶜ := (hNc.comp hc).preimage_mem_nhds hO
  have e2 : ∀ᶠ w in 𝓝 q, 1 - η < ‖Ψ w‖ :=
    (continuous_norm.continuousAt.comp hc).eventually
      (lt_mem_nhds (show 1 - η < ‖Ψ q‖ by rw [hn1]; linarith))
  have e3 : ∀ᶠ w in 𝓝 q, ‖Ψ w‖ < 1 + η :=
    (continuous_norm.continuousAt.comp hc).eventually
      (gt_mem_nhds (show ‖Ψ q‖ < 1 + η by rw [hn1]; linarith))
  have e4 : ∀ᶠ w in 𝓝 q, w ≠ p := isOpen_compl_singleton.mem_nhds (hℓp t₀)
  have hdec : ∀ w, 1 - η < ‖Ψ w‖ → Nr (Ψ w) ∉ Fb →
      Nr (Ψ w) ∈ C ∧ mul (‖Ψ w‖, Nr (Ψ w)) = Ψ w := by
    intro w hw2 hw1
    have hw0 : Ψ w ≠ 0 := by intro h'; rw [h', norm_zero] at hw2; linarith
    have hu : Nr (Ψ w) ∈ sphere (0 : ℂ) 1 := by
      simp only [hNr, mem_sphere_iff_norm, sub_zero, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_norm]
      exact div_self (norm_ne_zero_iff.2 hw0)
    refine ⟨?_, ?_⟩
    · rcases hsph hu with h' | h'
      · exact h'
      · exact absurd h' hw1
    · have hnw0 : (‖Ψ w‖ : ℂ) ≠ 0 := by simpa using hw0
      simp only [hmul, hNr]; field_simp
  filter_upwards [e1, e2, e3, e4] with w hw1 hw2 hw3 hw4
  obtain ⟨huC, hdecw⟩ := hdec w hw2 hw1
  refine ⟨fun hwL => ?_, fun hwR => ?_⟩
  · have hlt := hL w hwL
    exact ⟨h (Ψ w), ⟨Ψ w, ⟨(‖Ψ w‖, Nr (Ψ w)), ⟨⟨hw2, hlt⟩, huC⟩, hdecw⟩, rfl⟩, hrec w⟩
  · have hgt := hR w hwR hw4
    exact ⟨h (Ψ w), ⟨Ψ w, ⟨(‖Ψ w‖, Nr (Ψ w)), ⟨⟨hgt, hw3⟩, huC⟩, hdecw⟩, rfl⟩, hrec w⟩

theorem isOpen_leftSide (hγ : IsProperCurve γ) : IsOpen (leftSide γ) :=
  (isClosed_seedRayClosure hγ).isOpen_compl.connectedComponentIn

theorem isOpen_rightSide (hγ : IsProperCurve γ) : IsOpen (rightSide γ) :=
  (isClosed_seedRayClosure hγ).isOpen_compl.connectedComponentIn

theorem leftSide_subset_compl (γ : ℝ≥0 → ℂ) : leftSide γ ⊆ (seedRayClosure γ)ᶜ :=
  connectedComponentIn_subset _ _

theorem rightSide_subset_compl (γ : ℝ≥0 → ℂ) : rightSide γ ⊆ (seedRayClosure γ)ᶜ :=
  connectedComponentIn_subset _ _

/-- **Pairing of sides at a common point.** If the closed curves of two proper curves `γ`, `δ` coincide on an open
set `N` containing a point `q` of the first, then near `q` the left side of `δ` is either the left side or the right
side of `γ` (off the curve). -/
theorem local_sides_pairing {δ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (hδ : IsProperCurve δ)
    (h0 : (γ 0).im = 0) (hδ0 : (δ 0).im = 0) {q : ℂ} (hq : q ∈ seedRayClosure γ) {N : Set ℂ}
    (hNo : IsOpen N) (hqN : q ∈ N) (hNeq : N ∩ seedRayClosure δ = N ∩ seedRayClosure γ) :
    (∀ᶠ w in 𝓝 q, w ∉ seedRayClosure γ → (w ∈ leftSide δ ↔ w ∈ leftSide γ)) ∨
      (∀ᶠ w in 𝓝 q, w ∉ seedRayClosure γ → (w ∈ leftSide δ ↔ w ∈ rightSide γ)) := by
  obtain ⟨t₀, rfl⟩ := seedLine_surj h0 hq
  obtain ⟨PL, PR, hPLc, hPRc, hPL, hPR, hev⟩ := exists_local_sides hγ h0 t₀ (hNo.mem_nhds hqN)
  have hdisj := disjoint_leftSide_rightSide hδ hδ0
  have hcompl := compl_seedRayClosure_eq hδ hδ0
  have hγcompl := compl_seedRayClosure_eq hγ h0
  have hoff : ∀ z ∈ N, z ∉ seedRayClosure γ → z ∉ seedRayClosure δ := fun z hzN hzγ hzδ =>
    hzγ (show z ∈ N ∩ seedRayClosure γ from hNeq ▸ ⟨hzN, hzδ⟩).2
  have hoff' : ∀ z ∈ N, z ∉ seedRayClosure δ → z ∉ seedRayClosure γ := fun z hzN hzδ hzγ =>
    hzδ (show z ∈ N ∩ seedRayClosure δ from hNeq.symm ▸ ⟨hzN, hzγ⟩).2
  have hPLδ : PL ⊆ leftSide δ ∪ rightSide δ := fun z hz =>
    hcompl ▸ hoff z (hPL hz).2 (leftSide_subset_compl γ (hPL hz).1)
  have hPRδ : PR ⊆ leftSide δ ∪ rightSide δ := fun z hz =>
    hcompl ▸ hoff z (hPR hz).2 (rightSide_subset_compl γ (hPR hz).1)
  have hsL := hPLc.subset_or_subset (isOpen_leftSide hδ) (isOpen_rightSide hδ) hdisj hPLδ
  have hsR := hPRc.subset_or_subset (isOpen_leftSide hδ) (isOpen_rightSide hδ) hdisj hPRδ
  have hqδ : seedLine γ t₀ ∈ seedRayClosure δ :=
    (show seedLine γ t₀ ∈ N ∩ seedRayClosure δ from hNeq.symm ▸ ⟨hqN, seedLine_mem h0 t₀⟩).2
  have hev' : ∀ᶠ w in 𝓝 (seedLine γ t₀), w ∈ N ∧ ((w ∈ leftSide γ → w ∈ PL) ∧ (w ∈ rightSide γ → w ∈ PR)) :=
    (Filter.eventually_mem_set.2 (hNo.mem_nhds hqN)).and hev
  have hkey : ∀ w, w ∈ N ∧ ((w ∈ leftSide γ → w ∈ PL) ∧ (w ∈ rightSide γ → w ∈ PR)) →
      w ∉ seedRayClosure δ → w ∈ PL ∪ PR := by
    rintro w ⟨hwN, hw⟩ hwδ
    rcases (hγcompl ▸ hoff' w hwN hwδ : w ∈ leftSide γ ∪ rightSide γ) with h' | h'
    · exact Or.inl (hw.1 h')
    · exact Or.inr (hw.2 h')
  have hex : ∀ S : Set ℂ, S ⊆ (seedRayClosure δ)ᶜ → seedLine γ t₀ ∈ closure S → ∃ w ∈ S, w ∈ PL ∪ PR := by
    intro S hS hcl
    obtain ⟨w, hwS, hw⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually hev').exists
    exact ⟨w, hwS, hkey w hw (hS hwS)⟩
  obtain ⟨wL, hwL, hwLP⟩ := hex _ (leftSide_subset_compl δ) (seedRayClosure_subset_closure_leftSide hδ hδ0 hqδ)
  obtain ⟨wR, hwR, hwRP⟩ := hex _ (rightSide_subset_compl δ) (seedRayClosure_subset_closure_rightSide hδ hδ0 hqδ)
  rcases hsL with hL | hL <;> rcases hsR with hR | hR
  · exfalso
    rcases hwRP with h' | h'
    · exact Set.disjoint_left.1 hdisj (hL h') hwR
    · exact Set.disjoint_left.1 hdisj (hR h') hwR
  · left
    filter_upwards [hev'] with w hw hwγ
    rcases (hγcompl ▸ hwγ : w ∈ leftSide γ ∪ rightSide γ) with h' | h'
    · exact ⟨fun _ => h', fun _ => hL (hw.2.1 h')⟩
    · exact ⟨fun hwLδ => absurd (hR (hw.2.2 h')) (Set.disjoint_left.1 hdisj hwLδ),
        fun hwLγ => absurd h' (Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ h0) hwLγ)⟩
  · right
    filter_upwards [hev'] with w hw hwγ
    rcases (hγcompl ▸ hwγ : w ∈ leftSide γ ∪ rightSide γ) with h' | h'
    · exact ⟨fun hwLδ => absurd (hL (hw.2.1 h')) (Set.disjoint_left.1 hdisj hwLδ),
        fun hwRγ => absurd hwRγ (Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ h0) h')⟩
    · exact ⟨fun _ => h', fun _ => hR (hw.2.2 h')⟩
  · exfalso
    rcases hwLP with h' | h'
    · exact Set.disjoint_left.1 hdisj hwL (hL h')
    · exact Set.disjoint_left.1 hdisj hwL (hR h')

end LocalSides

/-! ### The contact-order theorem -/

section ContactOrder

/-- The lower vertical ray at `x`. -/
def lowerRay (x : ℝ) : Set ℂ := {z | z.re = x ∧ z.im ≤ 0}

theorem isClosed_lowerRay (x : ℝ) : IsClosed (lowerRay x) :=
  (isClosed_eq continuous_re continuous_const).inter (isClosed_le continuous_im continuous_const)

theorem seedRayClosure_eq_range_union {γ : ℝ≥0 → ℂ} (h0 : (γ 0).im = 0) :
    seedRayClosure γ = range γ ∪ lowerRay (γ 0).re := by
  simp only [seedRayClosure, lowerRay, h0]

/-- A point of the closed upper half-plane on the lower ray at a real seed is the seed. -/
theorem eq_seed_of_mem_lowerRay {γ : ℝ≥0 → ℂ} (h0 : (γ 0).im = 0) {z : ℂ} (hz : 0 ≤ z.im)
    (hzr : z ∈ lowerRay (γ 0).re) : z = γ 0 :=
  eq_of_re_eq_of_im_eq_zero hzr.1 (le_antisymm hzr.2 hz) h0

variable {γ₁ γ₂ : ℝ≥0 → ℂ}

/-- The range of the junction that follows `γ₂` up to `T` and then `γ₁` from `S`. -/
theorem mem_range_junction_iff {T S : ℝ≥0} (hj : γ₂ T = γ₁ S) {z : ℂ} :
    z ∈ range (junction γ₂ γ₁ T S) ↔ (∃ u ≤ T, γ₂ u = z) ∨ ∃ σ, S ≤ σ ∧ γ₁ σ = z := by
  constructor
  · rintro ⟨u, rfl⟩
    by_cases hu : u ≤ T
    · exact Or.inl ⟨u, hu, (junction_of_le hu).symm⟩
    · exact Or.inr ⟨S + (u - T), le_self_add, (junction_of_lt (not_le.1 hu)).symm⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨σ, hσ, rfl⟩)
    · exact ⟨u, junction_of_le hu⟩
    · rcases hσ.lt_or_eq with hσ' | hσ'
      · refine ⟨T + (σ - S), ?_⟩
        have hlt : T < T + (σ - S) := lt_add_of_pos_right _ (tsub_pos_of_lt hσ')
        rw [junction_of_lt hlt, add_tsub_cancel_left, add_tsub_cancel_of_le hσ]
      · exact ⟨T, by rw [junction_of_le le_rfl, hj, hσ']⟩

/-- **The contact-order theorem, at a minimal reversed pair.** A reversed pair of contacts
`γ₁(s) = γ₂(t)`, `γ₁(s') = γ₂(t')`, `s < s'`, `t' < t`, where `γ₂([0, t'))` avoids `γ₁([s', ∞))`, is impossible. -/
theorem contact_order_core (h₁ : IsProperCurve γ₁) (h₂ : IsProperCurve γ₂) (h₁0 : (γ₁ 0).im = 0)
    (h₂0 : (γ₂ 0).im = 0) (hseed : (γ₂ 0).re ≤ (γ₁ 0).re) (hord : range γ₂ ⊆ closedLeftSide γ₁)
    {s s' t t' : ℝ≥0} (hst : γ₁ s = γ₂ t) (hst' : γ₁ s' = γ₂ t') (hss' : s < s') (htt' : t' < t)
    (hmin : ∀ u < t', ∀ σ, s' ≤ σ → γ₂ u ≠ γ₁ σ) : False := by
  set δ := junction γ₂ γ₁ t' s' with hδdef
  have hj : γ₂ t' = γ₁ s' := hst'.symm
  have hδ : IsProperCurve δ := isProperCurve_junction h₂ h₁ hj hmin
  have hagree : ∀ u ≤ t', δ u = γ₂ u := fun u hu => junction_of_le hu
  have hδlt : ∀ σ, t' < σ → δ σ = γ₁ (s' + (σ - t')) := fun σ hσ => junction_of_lt hσ
  have hδ0' : δ 0 = γ₂ 0 := hagree 0 zero_le
  have hδ0 : (δ 0).im = 0 := by rw [hδ0']; exact h₂0
  set x₁ := (γ₁ 0).re with hx₁
  set x₂ := (γ₂ 0).re with hx₂
  have hclδ : seedRayClosure δ = range δ ∪ lowerRay x₂ := by
    rw [seedRayClosure_eq_range_union hδ0, hδ0']
  have hcl₁ : seedRayClosure γ₁ = range γ₁ ∪ lowerRay x₁ := seedRayClosure_eq_range_union h₁0
  have hrδ : ∀ z, z ∈ range δ ↔ (∃ u ≤ t', γ₂ u = z) ∨ ∃ σ, s' ≤ σ ∧ γ₁ σ = z := fun z =>
    mem_range_junction_iff hj
  -- the open tail `T` and the obstacle `Z`
  set T := γ₁ '' Ioi s' with hT
  set Z := γ₂ '' Icc 0 t' ∪ γ₁ '' Icc 0 s' ∪ lowerRay x₁ ∪ lowerRay x₂ with hZ
  have hZc : IsClosed Z :=
    ((((isCompact_Icc.image h₂.1).isClosed).union (isCompact_Icc.image h₁.1).isClosed).union
      (isClosed_lowerRay _)).union (isClosed_lowerRay _)
  set O := Zᶜ with hO
  have hOo : IsOpen O := hZc.isOpen_compl
  have hTZ : ∀ σ, s' < σ → γ₁ σ ∉ Z := by
    intro σ hσ hz
    rcases hz with ((⟨u, hu, hue⟩ | ⟨u, hu, hue⟩) | hr) | hr
    · rcases hu.2.lt_or_eq with hu' | hu'
      · exact hmin u hu' σ hσ.le hue
      · rw [hu', hj] at hue; exact hσ.ne (h₁.2.1 hue)
    · have := h₁.2.1 hue
      rw [this] at hu
      exact absurd hu.2 (not_le.2 hσ)
    · have := eq_seed_of_mem_lowerRay h₁0 (h₁.2.2.1 σ) hr
      exact (lt_of_le_of_lt zero_le hσ).ne' (h₁.2.1 this)
    · have h' : γ₁ σ = γ₂ 0 := eq_seed_of_mem_lowerRay h₂0 (h₁.2.2.1 σ) hr
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t') with ht0 | ht0
      · rw [ht0, hj] at h'; exact hσ.ne' (h₁.2.1 h')
      · exact hmin 0 ht0 σ hσ.le h'.symm
  have hTsub₁ : T ⊆ seedRayClosure γ₁ := by rintro _ ⟨σ, -, rfl⟩; exact Or.inl ⟨σ, rfl⟩
  have hTsubδ : T ⊆ seedRayClosure δ := by
    rintro _ ⟨σ, hσ, rfl⟩; rw [hclδ]; exact Or.inl ((hrδ _).2 (Or.inr ⟨σ, le_of_lt hσ, rfl⟩))
  have hTO : T ⊆ O := by rintro _ ⟨σ, hσ, rfl⟩; exact hTZ σ hσ
  have hO₁ : ∀ z ∈ O, z ∈ seedRayClosure γ₁ → z ∈ T := by
    intro z hzO hz
    rw [hcl₁] at hz
    rcases hz with ⟨σ, rfl⟩ | hr
    · by_cases hσ : σ ≤ s'
      · exact absurd (Or.inl (Or.inl (Or.inr ⟨σ, ⟨zero_le, hσ⟩, rfl⟩))) hzO
      · exact ⟨σ, not_le.1 hσ, rfl⟩
    · exact absurd (Or.inl (Or.inr hr)) hzO
  have hOδ : ∀ z ∈ O, z ∈ seedRayClosure δ → z ∈ T := by
    intro z hzO hz
    rw [hclδ] at hz
    rcases hz with hz | hr
    · rcases (hrδ z).1 hz with ⟨u, hu, rfl⟩ | ⟨σ, hσ, rfl⟩
      · exact absurd (Or.inl (Or.inl (Or.inl ⟨u, ⟨zero_le, hu⟩, rfl⟩))) hzO
      · rcases hσ.lt_or_eq with hσ' | hσ'
        · exact ⟨σ, hσ', rfl⟩
        · exact absurd (Or.inl (Or.inl (Or.inr ⟨s', ⟨zero_le, le_rfl⟩, by rw [hσ']⟩))) hzO
    · exact absurd (Or.inr hr) hzO
  have hNeq : O ∩ seedRayClosure δ = O ∩ seedRayClosure γ₁ := by
    ext z
    constructor
    · rintro ⟨hzO, hz⟩; exact ⟨hzO, hTsub₁ (hOδ z hzO hz)⟩
    · rintro ⟨hzO, hz⟩; exact ⟨hzO, hTsubδ (hO₁ z hzO hz)⟩
  have hd₁ := disjoint_leftSide_rightSide h₁ h₁0
  have hdδ := disjoint_leftSide_rightSide hδ hδ0
  have hc₁ := compl_seedRayClosure_eq h₁ h₁0
  have hcδ := compl_seedRayClosure_eq hδ hδ0
  -- the matched and the swapped sets
  set P : ℂ → Prop := fun z => (z ∈ leftSide δ ↔ z ∈ leftSide γ₁) with hP
  set G := {w : ℂ | ∀ᶠ z in 𝓝 w, z ∉ seedRayClosure γ₁ → z ∉ seedRayClosure δ → P z} with hG
  set Bd := {w : ℂ | ∀ᶠ z in 𝓝 w, z ∉ seedRayClosure γ₁ → z ∉ seedRayClosure δ → ¬ P z} with hBd
  have hGo : IsOpen G := isOpen_setOfPred_eventually_nhds
  have hBo : IsOpen Bd := isOpen_setOfPred_eventually_nhds
  have hcov : O ⊆ G ∪ Bd := by
    intro w hwO
    by_cases hwT : w ∈ T
    · rcases local_sides_pairing h₁ hδ h₁0 hδ0 (hTsub₁ hwT) hOo hwO hNeq with hm | hs
      · left
        filter_upwards [hm] with z hz hz₁ _ using hz hz₁
      · right
        filter_upwards [hs] with z hz hz₁ _ hPz
        rcases (hc₁ ▸ hz₁ : z ∈ leftSide γ₁ ∪ rightSide γ₁) with h' | h'
        · exact Set.disjoint_left.1 hd₁ h' ((hz hz₁).1 (hPz.2 h'))
        · exact Set.disjoint_left.1 hd₁ (hPz.1 ((hz hz₁).2 h')) h'
    · have hw₁ : w ∉ seedRayClosure γ₁ := fun h' => hwT (hO₁ w hwO h')
      have hwδ : w ∉ seedRayClosure δ := fun h' => hwT (hOδ w hwO h')
      rcases (hc₁ ▸ hw₁ : w ∈ leftSide γ₁ ∪ rightSide γ₁) with h1 | h1 <;>
        rcases (hcδ ▸ hwδ : w ∈ leftSide δ ∪ rightSide δ) with h2 | h2
      · left
        filter_upwards [(isOpen_leftSide h₁).mem_nhds h1, (isOpen_leftSide hδ).mem_nhds h2] with
          z hz1 hz2 _ _ using ⟨fun _ => hz1, fun _ => hz2⟩
      · right
        filter_upwards [(isOpen_leftSide h₁).mem_nhds h1, (isOpen_rightSide hδ).mem_nhds h2] with
          z hz1 hz2 _ _ hPz using Set.disjoint_left.1 hdδ (hPz.2 hz1) hz2
      · right
        filter_upwards [(isOpen_rightSide h₁).mem_nhds h1, (isOpen_leftSide hδ).mem_nhds h2] with
          z hz1 hz2 _ _ hPz using Set.disjoint_left.1 hd₁ (hPz.1 hz2) hz1
      · left
        filter_upwards [(isOpen_rightSide h₁).mem_nhds h1, (isOpen_rightSide hδ).mem_nhds h2] with
          z hz1 hz2 _ _
        exact ⟨fun h' => absurd hz2 (Set.disjoint_left.1 hdδ h'),
          fun h' => absurd hz1 (Set.disjoint_left.1 hd₁ h')⟩
  have hGB : ∀ w ∈ O, w ∈ G → w ∈ Bd → False := by
    intro w hwO hwG hwB
    have hev := (Filter.eventually_mem_set.2 (hOo.mem_nhds hwO)).and (hwG.and hwB)
    by_cases hwT : w ∈ T
    · have hcl := seedRayClosure_subset_closure_leftSide h₁ h₁0 (hTsub₁ hwT)
      obtain ⟨z, hzL, hzO, hz1, hz2⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually hev).exists
      have hz₁ : z ∉ seedRayClosure γ₁ := leftSide_subset_compl γ₁ hzL
      have hzδ : z ∉ seedRayClosure δ := fun h' => hz₁ (hTsub₁ (hOδ z hzO h'))
      exact hz2 hz₁ hzδ (hz1 hz₁ hzδ)
    · have hw₁ : w ∉ seedRayClosure γ₁ := fun h' => hwT (hO₁ w hwO h')
      have hwδ : w ∉ seedRayClosure δ := fun h' => hwT (hOδ w hwO h')
      obtain ⟨-, h1, h2⟩ := hev.self_of_nhds
      exact h2 hw₁ hwδ (h1 hw₁ hwδ)
  -- the far region
  obtain ⟨R₀, hR₀⟩ :=
    ((isCompact_Icc.image h₂.1).union (isCompact_Icc.image h₁.1)).isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ (|x₁| + |x₂|) + 1 with hR
  have hRR₀ : R₀ < R := by have := le_max_left R₀ (|x₁| + |x₂|); linarith
  have hR1 : |x₁| < R := by
    have := le_max_right R₀ (|x₁| + |x₂|); linarith [abs_nonneg x₂]
  have hR2 : |x₂| < R := by
    have := le_max_right R₀ (|x₁| + |x₂|); linarith [abs_nonneg x₁]
  set Q := {z : ℂ | R < z.im} ∪ {z : ℂ | z.re < -R} ∪ {z : ℂ | R < z.re} with hQ
  have hQZ : ∀ z ∈ Q, z ∉ Z := by
    intro z hzQ hzZ
    have hnorm : R < ‖z‖ := by
      rcases hzQ with (h | h) | h
      · have h' : R < z.im := h
        exact h'.trans_le ((le_abs_self _).trans (abs_im_le_norm z))
      · have h' : z.re < -R := h
        have : R < |z.re| := by rw [abs_of_neg (by linarith [abs_nonneg x₁])]; linarith
        exact this.trans_le (abs_re_le_norm z)
      · have h' : R < z.re := h
        exact h'.trans_le ((le_abs_self _).trans (abs_re_le_norm z))
    have hray : ∀ x : ℝ, |x| < R → z ∉ lowerRay x := by
      rintro x hx ⟨hre, him⟩
      rcases hzQ with (h | h) | h
      · have h' : R < z.im := h; linarith [abs_nonneg x]
      · have h' : z.re < -R := h; rw [hre] at h'; linarith [neg_abs_le x]
      · have h' : R < z.re := h; rw [hre] at h'; linarith [le_abs_self x]
    rcases hzZ with ((h | h) | h) | h
    · have := hR₀ (Or.inl h); rw [mem_closedBall, dist_zero_right] at this; linarith
    · have := hR₀ (Or.inr h); rw [mem_closedBall, dist_zero_right] at this; linarith
    · exact hray x₁ hR1 h
    · exact hray x₂ hR2 h
  have hfarQ : ∀ z : ℂ, 0 ≤ z.im → 2 * R < ‖z‖ → z ∈ Q := by
    intro z him hn
    by_contra hzQ
    have h1 : z.im ≤ R := not_lt.1 fun h => hzQ (Or.inl (Or.inl h))
    have h2 : -R ≤ z.re := not_lt.1 fun h => hzQ (Or.inl (Or.inr h))
    have h3 : z.re ≤ R := not_lt.1 fun h => hzQ (Or.inr h)
    have hre : |z.re| ≤ R := abs_le.2 ⟨h2, h3⟩
    have him' : |z.im| ≤ R := by rw [abs_of_nonneg him]; exact h1
    linarith [norm_le_abs_re_add_abs_im z]
  have hQc : IsPreconnected Q := by
    have hA := (convex_halfSpace_im_gt R).isPreconnected
    have hB := (convex_halfSpace_re_lt (-R)).isPreconnected
    have hC := (convex_halfSpace_re_gt R).isPreconnected
    refine IsPreconnected.union' ?_ (IsPreconnected.union' ?_ hA hB) hC
    · refine ⟨((R + 1 : ℝ) : ℂ) + ((R + 1 : ℝ) : ℂ) * I, Or.inl ?_, ?_⟩
      · show R < (((R + 1 : ℝ) : ℂ) + ((R + 1 : ℝ) : ℂ) * I).im
        simp
      · show R < (((R + 1 : ℝ) : ℂ) + ((R + 1 : ℝ) : ℂ) * I).re
        simp
    · refine ⟨((-(R + 1) : ℝ) : ℂ) + ((R + 1 : ℝ) : ℂ) * I, ?_, ?_⟩
      · show R < (((-(R + 1) : ℝ) : ℂ) + ((R + 1 : ℝ) : ℂ) * I).im
        simp
      · show (((-(R + 1) : ℝ) : ℂ) + ((R + 1 : ℝ) : ℂ) * I).re < -R
        simp
  have hTc : IsPreconnected T := isPreconnected_Ioi.image _ h₁.1.continuousOn
  obtain ⟨σ₀, hσ₀n, hσ₀⟩ := ((h₁.2.2.2.eventually_gt_atTop (2 * R)).and (eventually_gt_atTop s')).exists
  have hQT : (Q ∩ T).Nonempty := ⟨γ₁ σ₀, hfarQ _ (h₁.2.2.1 σ₀) hσ₀n, σ₀, hσ₀, rfl⟩
  set K := Q ∪ T with hK
  have hKc : IsPreconnected K := hQc.union' hQT hTc
  have hKO : K ⊆ O := union_subset (fun z hz => hQZ z hz) hTO
  -- the far lower left is on the left of both curves
  set z₀ : ℂ := ((-(R + 1) : ℝ) : ℂ) - I with hz₀
  have hz₀Q : z₀ ∈ Q := Or.inl (Or.inr (show z₀.re < -R by simp [hz₀]))
  have hz₀G : z₀ ∈ G := by
    have hll₁ : z₀ ∈ lowerLeft x₁ := ⟨by simp [hz₀]; linarith [neg_abs_le x₁], by simp [hz₀]⟩
    have hll₂ : z₀ ∈ lowerLeft x₂ := ⟨by simp [hz₀]; linarith [neg_abs_le x₂], by simp [hz₀]⟩
    have hLδ : lowerLeft x₂ ⊆ leftSide δ := by
      have := lowerLeft_subset_leftSide hδ.2.2.1 hδ0
      rwa [hδ0'] at this
    filter_upwards [(isOpen_lowerLeft x₁).mem_nhds hll₁, (isOpen_lowerLeft x₂).mem_nhds hll₂] with
      z hz1 hz2 _ _
    exact ⟨fun _ => lowerLeft_subset_leftSide h₁.2.2.1 h₁0 hz1, fun _ => hLδ hz2⟩
  have hKG : K ⊆ G := by
    rcases isPreconnected_iff_subset_of_disjoint.1 hKc G Bd hGo hBo (hKO.trans hcov)
      (Set.eq_empty_iff_forall_notMem.2 fun w ⟨hwK, hwG, hwB⟩ => hGB w (hKO hwK) hwG hwB) with h' | h'
    · exact h'
    · exact absurd (h' (Or.inl hz₀Q)) fun hB => hGB z₀ (hKO (Or.inl hz₀Q)) hz₀G hB
  -- a point of `γ₂` on the right of `δ`, away from the obstacle, where the sides match, is impossible
  have hfin : ∀ u, γ₂ u ∈ rightSide δ → γ₂ u ∈ O →
      (γ₂ u ∉ seedRayClosure γ₁ → γ₂ u ∉ seedRayClosure δ → P (γ₂ u)) → False := by
    intro u hR hO' hP'
    have hnδ : γ₂ u ∉ seedRayClosure δ := rightSide_subset_compl δ hR
    have hn₁ : γ₂ u ∉ seedRayClosure γ₁ := fun h' => hnδ (hTsubδ (hO₁ _ hO' h'))
    have hnL : γ₂ u ∉ leftSide δ := fun h' => Set.disjoint_left.1 hdδ h' hR
    rcases hord ⟨u, rfl⟩ with hL | hS
    · exact hnL ((hP' hn₁ hnδ).2 hL)
    · exact hn₁ hS
  -- step 1: `γ₂(t) = γ₁(s)` is on the right of `δ`
  have hA : γ₂ t ∈ rightSide δ := by
    have hdual := range_subset_closedRightSide h₁ h₂ h₁0 h₂0 hseed hord
    have hav : ∀ u ≤ s, ∀ σ, t' ≤ σ → γ₁ u ≠ δ σ := by
      intro u hu σ hσ h'
      rcases hσ.lt_or_eq with hσ' | hσ'
      · rw [hδlt σ hσ'] at h'
        have := h₁.2.1 h'
        have hle : s' ≤ u := this ▸ le_self_add
        exact absurd (hle.trans hu) (not_le.2 hss')
      · rw [← hσ', hagree t' le_rfl, hj] at h'
        exact absurd (h₁.2.1 h' ▸ hu) (not_le.2 hss')
    have hmem := mem_closedRightSide_of_avoid h₂ hδ h₂0 hagree h₁ h₁0 hseed hdual hav
    rw [← hst]
    rcases hmem with h' | h'
    · exact h'
    · exfalso
      rw [hclδ] at h'
      rcases h' with h' | h'
      · rcases (hrδ _).1 h' with ⟨u, hu, hue⟩ | ⟨σ, hσ, hσe⟩
        · rw [hst] at hue
          exact absurd (h₂.2.1 hue ▸ hu) (not_le.2 htt')
        · exact absurd (h₁.2.1 hσe ▸ hσ) (not_le.2 hss')
      · have := eq_seed_of_mem_lowerRay h₂0 (h₁.2.2.1 s) h'
        rw [hst] at this
        exact absurd (h₂.2.1 this ▸ htt') (not_lt.2 zero_le)
  -- step 3: `γ₂` stays on the right of `δ` after `t`
  set E := {u : ℝ≥0 | t ≤ u ∧ γ₂ u ∉ rightSide δ} with hE
  rcases E.eq_empty_or_nonempty with hEe | hEne
  · have hRt : ∀ u, t ≤ u → γ₂ u ∈ rightSide δ := fun u hu => by
      by_contra h'
      have : u ∈ E := ⟨hu, h'⟩
      rw [hEe] at this
      exact this
    obtain ⟨u, hu1, hu2⟩ := ((h₂.2.2.2.eventually_gt_atTop (2 * R)).and (eventually_ge_atTop t)).exists
    have huQ : γ₂ u ∈ Q := hfarQ _ (h₂.2.2.1 u) hu1
    exact hfin u (hRt u hu2) (hKO (Or.inl huQ)) (hKG (Or.inl huQ)).self_of_nhds
  · have hEc : IsClosed E := isClosed_Ici.inter ((isOpen_rightSide hδ).isClosed_compl.preimage h₂.1)
    set u₁ := sInf E with hu₁
    have hu₁E : u₁ ∈ E := hEc.csInf_mem hEne (OrderBot.bddBelow E)
    have hbef : ∀ u, t ≤ u → u < u₁ → γ₂ u ∈ rightSide δ := fun u htu hu => by
      by_contra h'
      exact absurd (csInf_le (OrderBot.bddBelow E) ⟨htu, h'⟩) (not_le.2 hu)
    have htu₁ : t < u₁ := lt_of_le_of_ne hu₁E.1 fun h' => hu₁E.2 (h' ▸ hA)
    have : (𝓝[<] u₁).NeBot := nhdsLT_neBot_of_exists_lt ⟨t, htu₁⟩
    have hlim : Tendsto γ₂ (𝓝[<] u₁) (𝓝 (γ₂ u₁)) :=
      h₂.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hevR : ∀ᶠ u in 𝓝[<] u₁, γ₂ u ∈ rightSide δ := by
      filter_upwards [Ioo_mem_nhdsLT htu₁] with u hu using hbef u hu.1.le hu.2
    have hcl : γ₂ u₁ ∈ closure (rightSide δ) := mem_closure_of_tendsto hlim hevR
    have hnL : γ₂ u₁ ∉ leftSide δ := fun hL => by
      obtain ⟨z, hzR, hzL⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually
        ((isOpen_leftSide hδ).mem_nhds hL)).exists
      exact Set.disjoint_left.1 hdδ hzL hzR
    have hu₁δ : γ₂ u₁ ∈ seedRayClosure δ := by
      by_contra h'
      rcases (hcδ ▸ h' : γ₂ u₁ ∈ leftSide δ ∪ rightSide δ) with h'' | h''
      · exact hnL h''
      · exact hu₁E.2 h''
    have hu₁T : γ₂ u₁ ∈ T := by
      rw [hclδ] at hu₁δ
      rcases hu₁δ with h' | h'
      · rcases (hrδ _).1 h' with ⟨v, hv, hve⟩ | ⟨σ, hσ, hσe⟩
        · exact absurd (h₂.2.1 hve ▸ hv) (not_le.2 (htt'.trans htu₁))
        · rcases hσ.lt_or_eq with hσ' | hσ'
          · exact ⟨σ, hσ', hσe⟩
          · exfalso
            rw [← hσ', hst'] at hσe
            exact (htt'.trans htu₁).ne (h₂.2.1 hσe)
      · have := eq_seed_of_mem_lowerRay h₂0 (h₂.2.2.1 u₁) h'
        exact absurd (h₂.2.1 this ▸ htu₁) (not_lt.2 zero_le)
    have hev := hlim.eventually ((hKG (Or.inr hu₁T)).and
      (Filter.eventually_mem_set.2 (hOo.mem_nhds (hTO hu₁T))))
    obtain ⟨u, ⟨hPu, hOu⟩, hRu⟩ := (hev.and hevR).exists
    exact hfin u hRu hOu hPu

/-- **The contact-order theorem** (Lemma G5, supplement p. 493; Aux. lemma 84, p. 298). Two continuous injective
proper curves in the closed upper half-plane from real seeds `γ₂(0) ≤ γ₁(0)`, with `γ₂` in the closed left side of
`γ₁`, meet in increasing order in both parametrizations. -/
theorem contact_order (h₁ : IsProperCurve γ₁) (h₂ : IsProperCurve γ₂) (h₁0 : (γ₁ 0).im = 0)
    (h₂0 : (γ₂ 0).im = 0) (hseed : (γ₂ 0).re ≤ (γ₁ 0).re) (hord : range γ₂ ⊆ closedLeftSide γ₁)
    {s s' t t' : ℝ≥0} (hst : γ₁ s = γ₂ t) (hst' : γ₁ s' = γ₂ t') (hss' : s < s') : t < t' := by
  by_contra hcon
  have htt' : t' < t := lt_of_le_of_ne (not_lt.1 hcon) fun h =>
    hss'.ne (h₁.2.1 (hst.trans (h ▸ hst').symm))
  set F := γ₁ '' Ici s' with hF
  have hFc : IsClosed F := isClosed_image h₁ isClosed_Ici
  set M := {u : ℝ≥0 | γ₂ u ∈ F} with hM
  have hMc : IsClosed M := hFc.preimage h₂.1
  have ht'M : t' ∈ M := ⟨s', mem_Ici.2 le_rfl, hst'⟩
  have ht₀M : sInf M ∈ M := hMc.csInf_mem ⟨t', ht'M⟩ (OrderBot.bddBelow M)
  obtain ⟨s₀, hs₀, hs₀e⟩ := ht₀M
  have ht₀t' : sInf M ≤ t' := csInf_le (OrderBot.bddBelow M) ht'M
  exact contact_order_core h₁ h₂ h₁0 h₂0 hseed hord hst hs₀e (hss'.trans_le hs₀) (ht₀t'.trans_lt htt')
    fun u hu σ hσ h' => absurd (csInf_le (OrderBot.bddBelow M) ⟨σ, le_trans hs₀ hσ, h'.symm⟩)
      (not_le.2 hu)

end ContactOrder

/-! ### The named contact-order inputs, proved -/

section Inputs

/-- **`Supp9.OrderedContactOrderStatement` holds** (Lemma G5 and Aux. lemma 84, the input of W1's order part,
PROVE-SUPP9). -/
theorem orderedContactOrderStatement : Supp9.OrderedContactOrderStatement := by
  intro γ₁ γ₂ h₁ h₂ h₁0 h₂0 hseed hord s s' t t' hst hst' hss'
  exact contact_order (isProperCurve_of_isProperCompletion h₁) (isProperCurve_of_isProperCompletion h₂)
    h₁0 h₂0 hseed hord hst hst' hss'

/-- **`Supp10.G5Statement` holds** (Lemma G5, supplement p. 493: same-seed contact order, both directions). -/
theorem g5Statement : Supp10.G5Statement := by
  intro γ₁ γ₂ h₁ h₂ h₁0 h₂0 hord s s' t t' hst hst'
  have P₁ := isProperCurve_of_isProperCompletion h₁
  have P₂ := isProperCurve_of_isProperCompletion h₂
  have h₁0' : (γ₁ 0).im = 0 := by rw [h₁0]; simp
  have h₂0' : (γ₂ 0).im = 0 := by rw [h₂0]; simp
  have hseed : (γ₂ 0).re ≤ (γ₁ 0).re := by rw [h₁0, h₂0]
  refine ⟨contact_order P₁ P₂ h₁0' h₂0' hseed hord hst hst', fun htt' => ?_⟩
  rcases lt_trichotomy s s' with h | h | h
  · exact h
  · exact absurd (P₂.2.1 (hst.symm.trans (by rw [h]; exact hst'))) htt'.ne
  · exact absurd (contact_order P₁ P₂ h₁0' h₂0' hseed hord hst' hst h) (not_lt.2 htt'.le)

/-- **`Supp10.Aux84Statement` holds** (Aux. lemma 84, p. 298: contact order for distinct seeds). -/
theorem aux84Statement : Supp10.Aux84Statement := by
  intro α β x₁ x₂ hx hα hβ hα0 hβ0 hord u₁ u₂ v₁ v₂ h1 h2 hu
  exact contact_order (isProperCurve_of_isProperCompletion hα) (isProperCurve_of_isProperCompletion hβ)
    (by rw [hα0]; simp) (by rw [hβ0]; simp) (by rw [hα0, hβ0]; simp [hx.le]) hord h1 h2 hu

end Inputs

end Supp9B

end InteractingSLE
