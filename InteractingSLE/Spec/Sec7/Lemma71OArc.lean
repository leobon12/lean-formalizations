/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71OFrame

/-!
# Lemma 7.1's inherited branch: constancy along a wall arc

Packet PROVE-LEMMA71O (supplement §2.3, proof of the normalization lemma: the integer is "constant on the smaller
arc", "aligns the two retained sides at once").

* `eq_of_isPreconnected_of_local`: a property `P x m` with at most one integer `m` at each point, holding with a locally
  constant integer, holds with one integer on a preconnected set;
* `continuousOn_invFun_comp`: the time along a simple proper curve of a continuous path in its range is continuous;
* **`arc_times_lt`**: a continuous injective path in the range of a simple proper curve whose two endpoints have curve
  times `< q` has all curve times `< q` (the times are strictly monotone).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71O

/-- **One integer on a preconnected set.** If `P x m` holds for at most one integer `m` at each point of a preconnected
`I`, and every point of `I` has a neighbourhood in `I` on which `P · m` holds for one `m`, then `P x m` propagates from
`x` to every `y ∈ I`. -/
theorem eq_of_isPreconnected_of_local {I : Set ℝ} (hI : IsPreconnected I) {P : ℝ → ℤ → Prop}
    (huniq : ∀ x ∈ I, ∀ m m' : ℤ, P x m → P x m' → m = m')
    (hloc : ∀ x ∈ I, ∃ m : ℤ, ∃ ε > 0, ∀ y ∈ I, |y - x| < ε → P y m) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    {m : ℤ} (hm : P x m) : P y m := by
  classical
  set K : ℝ → ℤ := fun z => if h : ∃ m, P z m then h.choose else 0 with hK
  have hKspec : ∀ z ∈ I, P z (K z) := fun z hz => by
    obtain ⟨m', ε, hε, h⟩ := hloc z hz
    have hex : ∃ m, P z m := ⟨m', h z hz (by simpa using hε)⟩
    simp only [hK, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hKc : ContinuousOn K I := by
    intro z hz
    obtain ⟨m', ε, hε, h⟩ := hloc z hz
    have hKz : K z = m' := huniq z hz _ _ (hKspec z hz) (h z hz (by simpa using hε))
    refine tendsto_nhds_of_eventually_eq ?_
    have hb : ∀ᶠ w in 𝓝[I] z, w ∈ I ∧ |w - z| < ε := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds z hε)] with w h1 h2
      exact ⟨h1, by rwa [mem_ball, Real.dist_eq] at h2⟩
    filter_upwards [hb] with w hw
    rw [hKz]
    exact huniq w hw.1 _ _ (hKspec w hw.1) (h w hw.1 hw.2)
  have hKxy : K x = K y := hI.constant hKc hx hy
  have hKx : K x = m := huniq x hx _ _ (hKspec x hx) hm
  rw [← hKx, hKxy]
  exact hKspec y hy

/-- **The curve time of a continuous path in the range of a simple proper curve is continuous** (a continuous
injective map of a compact interval is a closed embedding). -/
theorem continuousOn_invFun_comp {η : ℝ≥0 → ℂ} (hη : Lemma71I.IsSimpleProper η) {ℓ : ℝ → ℂ} {u v : ℝ}
    (hℓc : ContinuousOn ℓ (Icc u v)) (hmem : ∀ w ∈ Icc u v, ℓ w ∈ range η) :
    ContinuousOn (fun w => Function.invFun η (ℓ w)) (Icc u v) := by
  classical
  -- a bound on the curve times
  obtain ⟨R, hR⟩ := ((isCompact_Icc.image_of_continuousOn hℓc).isBounded).exists_norm_le
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 ((tendsto_atTop.1 hη.2.2.2.2) (R + 1))
  set σ : ℝ → ℝ≥0 := fun w => Function.invFun η (ℓ w) with hσ
  have hσeq : ∀ w ∈ Icc u v, η (σ w) = ℓ w := fun w hw => Function.invFun_eq (hmem w hw)
  have hσT : ∀ w ∈ Icc u v, σ w ∈ Icc 0 T := fun w hw => by
    refine ⟨zero_le (a := σ w), ?_⟩
    by_contra hlt
    have h1 := hT (σ w) (le_of_lt (not_le.1 hlt))
    have h2 := hR _ ⟨w, hw, rfl⟩
    rw [← hσeq w hw] at h2
    linarith
  rw [continuousOn_iff_continuous_domRestrict]
  set f : Icc (0 : ℝ≥0) T → ℂ := (Icc 0 T).domRestrict η with hf
  have hfc : Continuous f := hη.1.continuousOn.domRestrict
  have hfi : Function.Injective f := fun x y hxy => Subtype.ext (hη.2.1 hxy)
  have hemb := (hfc.isClosedEmbedding hfi).isEmbedding
  set g' : Icc u v → Icc (0 : ℝ≥0) T := fun w => ⟨σ w, hσT w w.2⟩ with hg'
  have hg'c : Continuous g' := by
    rw [hemb.continuous_iff]
    have : f ∘ g' = (Icc u v).domRestrict ℓ := funext fun w => hσeq w w.2
    rw [this]
    exact hℓc.domRestrict
  exact continuous_subtype_val.comp hg'c

/-- **Curve times along an arc stay below `q`.** Let `ℓ` be continuous and injective on `[u, v]` with values in the
range of the simple proper curve `η`, and let the curve times of `ℓ u` and `ℓ v` be `< q`. Then every point `ℓ w`,
`w ∈ [u, v]`, is `η s` with `s < q`. -/
theorem arc_times_lt {η : ℝ≥0 → ℂ} (hη : Lemma71I.IsSimpleProper η) {ℓ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hℓc : ContinuousOn ℓ (Icc u v)) (hℓi : InjOn ℓ (Icc u v)) (hmem : ∀ w ∈ Icc u v, ℓ w ∈ range η)
    {q su sv : ℝ≥0} (hu : ℓ u = η su) (hv : ℓ v = η sv) (hsu : su < q) (hsv : sv < q) :
    ∀ w ∈ Icc u v, ∃ s < q, ℓ w = η s := by
  classical
  set σ : ℝ → ℝ≥0 := fun w => Function.invFun η (ℓ w) with hσ
  have hσeq : ∀ w ∈ Icc u v, η (σ w) = ℓ w := fun w hw => Function.invFun_eq (hmem w hw)
  have hσc : ContinuousOn σ (Icc u v) := continuousOn_invFun_comp hη hℓc hmem
  have hσi : InjOn σ (Icc u v) := fun w₁ h₁ w₂ h₂ h => hℓi h₁ h₂ (by rw [← hσeq w₁ h₁, ← hσeq w₂ h₂, h])
  have huI : u ∈ Icc u v := ⟨le_rfl, huv⟩
  have hvI : v ∈ Icc u v := ⟨huv, le_rfl⟩
  have hσu : σ u = su := hη.2.1 (by rw [hσeq u huI, hu])
  have hσv : σ v = sv := hη.2.1 (by rw [hσeq v hvI, hv])
  intro w hw
  refine ⟨σ w, ?_, (hσeq w hw).symm⟩
  rcases hσc.strictMonoOn_of_injOn_Icc' huv hσi with hm | hm
  · exact lt_of_le_of_lt (hm.monotoneOn hw hvI hw.2) (hσv ▸ hsv)
  · exact lt_of_le_of_lt (hm.antitoneOn huI hw hw.1) (hσu ▸ hsu)

end InteractingSLE.Sec7.Lemma71O
