import InteractingSLE.Foundations.Loewner.ConformalImageFullRateMain

/-!
# Specification Aux. lemma 8 with the capacity rate

Packet PROVE-GEO-LOC2. The final statements:

* `ConformalImageFull.hasDerivWithinAt_hcap_image`: for every mapping-out function `R` of
  `E_t = g_t(A)`, `R` extends holomorphically across the real line near `W_t`; for every such
  extension `R̂`, `R̂'(W_t)` is real and positive and `t ↦ ½ hcap(φ(K_t))` has derivative
  `R̂'(W_t)²` at `t` within `[0, T]` ([Law05] §4.6.1, `ḃ = 2 Φ_t'(U_t)²`);
* `ConformalImageFull.exists_loewner_image_rate`: Specification Aux. lemma 8, (HD1)–(HD3),
  together with `ȧ = R_t'(W_t)²`, for a continuous driver with arbitrary `W 0`;
* `ConformalImageFull.exists_loewner_image_rate_of_pos`: the same for `T > 0`, with (HD1) in the
  form `closure A ∩ closure K_T = ∅`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace ConformalImageFull

open ConformalImage

/-- Two holomorphic functions on `ball x δ` (`x` real) that agree on its upper half agree on the
ball. -/
theorem eqOn_ball_of_eqOn_upper {f g : ℂ → ℂ} {x δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball (x : ℂ) δ)) (hg : DifferentiableOn ℂ g (ball (x : ℂ) δ))
    (hfg : EqOn f g (ball (x : ℂ) δ ∩ H)) : EqOn f g (ball (x : ℂ) δ) := by
  have hz₀ : ((x : ℂ) + ((δ / 2 : ℝ) : ℂ) * I) ∈ ball (x : ℂ) δ ∩ H :=
    mem_ball_inter_H (by positivity) (by linarith)
  refine (hf.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd isOpen_ball) (convex_ball _ _).isPreconnected hz₀.1 ?_
  filter_upwards [(isOpen_ball.inter QuantumZipper.isOpen_H).mem_nhds hz₀] with z hz
  exact hfg hz

namespace ImageHyp

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T ρ : ℝ}

/-- **The capacity rate for every holomorphic extension** of a mapping-out function `R` of
`E_t` (with `W 0 = 0` and the clearance hypothesis). -/
theorem rate (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) {R : ℂ → ℂ}
    (hR : IsMapOut (obstacle W A t) R) :
    (∃ δ > 0, ∃ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) ∧
        EqOn Rext R (ball (W t : ℂ) δ ∩ H)) ∧
      ∀ δ > 0, ∀ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) →
        EqOn Rext R (ball (W t : ℂ) δ ∩ H) →
        0 < (deriv Rext (W t)).re ∧ (deriv Rext (W t)).im = 0 ∧
          HasDerivWithinAt (cap (imageHull W φ)) ((deriv Rext (W t)).re ^ 2) (Icc 0 T) t := by
  have hρ := h.pos
  have hobs := h.isHPHull_obstacle ht
  obtain ⟨G, hG, hGx⟩ := IsMapOut.exists_isRefl hobs (isMapOut_mapOut hobs) hρ
    (h.disjoint_ball_obstacle ht)
  have hGx' : G (W t) = bdryDriver W A t := by rw [hGx, h.bdryDriver_eq ht]
  have hRm : EqOn (mapOut (obstacle W A t)) R (H \ obstacle W A t) :=
    (isMapOut_mapOut hobs).eqOn hobs hR
  have hnot : ∀ z ∈ ball (W t : ℂ) (ρ / 2) ∩ H, z ∈ H \ obstacle W A t := fun z hz =>
    ⟨hz.2, fun hzE => Set.disjoint_left.1 (h.disjoint_ball_obstacle ht)
      (ball_subset_ball (by linarith) hz.1) hzE⟩
  have hGR : EqOn G R (ball (W t : ℂ) (ρ / 2) ∩ H) := fun z hz =>
    (hG.eqOn hz).trans (hRm (hnot z hz))
  have hup : ∀ z ∈ ball (W t : ℂ) (ρ / 2) ∩ H, 0 < (G z).im := fun z hz => by
    rw [hG.eqOn hz]; exact (isMapOut_mapOut hobs).1.2.mapsTo (hnot z hz)
  obtain ⟨hpos, hreal⟩ := hG.deriv_pos hρ hup
  refine ⟨⟨ρ / 2, by positivity, G, hG.diff, hGR⟩, fun δ hδ Rext hRd hRe => ?_⟩
  set δ' := min δ (ρ / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by positivity)
  have hEq : EqOn Rext G (ball (W t : ℂ) δ') := by
    refine eqOn_ball_of_eqOn_upper hδ'0 (hRd.mono (ball_subset_ball (min_le_left _ _)))
      (hG.diff.mono (ball_subset_ball (min_le_right _ _))) fun z hz => ?_
    rw [hRe ⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩]
    exact (hGR ⟨ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩).symm
  have hderiv : deriv Rext (W t) = deriv G (W t) := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ'0)] with z hz
    exact hEq hz
  rw [hderiv]
  refine ⟨hpos, ?_, ?_⟩
  · rw [hreal]; simp
  · have := hasDerivWithinAt_cap h ht hG hGx'
    rwa [hreal, ← ofReal_pow, ofReal_re] at this

end ImageHyp
/-- **The capacity rate** `ȧ = R_t'(W_t)²` ([Law05] §4.6.1) for a driver with arbitrary `W 0`,
under (HD1). For every mapping-out function `R` of `E_t = g_t(A)`: `R` extends holomorphically
across the real line near `W_t`, and for every such extension `R̂`, `R̂'(W_t)` is real and
positive and `t ↦ ½ hcap(φ(K_t))` has derivative `R̂'(W_t)²` at `t` (within `[0, T]`). -/
theorem hasDerivWithinAt_hcap_image {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (insert (W 0 : ℂ) (closure (QuantumZipper.fwdHull W T))))
    {t : ℝ} (ht : t ∈ Icc 0 T) {R : ℂ → ℂ}
    (hR : IsMapOut ((fun z => QuantumZipper.fwdMap W t z + W t) '' A) R) :
    (∃ δ > 0, ∃ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) ∧
        EqOn Rext R (ball (W t : ℂ) δ ∩ H)) ∧
      ∀ δ > 0, ∀ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) →
        EqOn Rext R (ball (W t : ℂ) δ ∩ H) →
        0 < (deriv Rext (W t)).re ∧ (deriv Rext (W t)).im = 0 ∧
          HasDerivWithinAt (fun s => hcapSet (φ '' QuantumZipper.fwdHull W s) / 2)
            ((deriv Rext (W t)).re ^ 2) (Icc 0 T) t := by
  set c := W 0 with hc
  set V : ℝ → ℝ := fun s => W s - c with hV
  have hVc : Continuous V := hW.sub continuous_const
  have hV0 : V 0 = 0 := sub_self _
  have hWV : (fun s => V s + c) = W := funext fun s => sub_add_cancel _ _
  set e := affHomeo 1 one_pos (-c) with he
  set ep := affHomeo 1 one_pos c with hep
  have he_apply : ∀ z, e z = z - c := fun z => by
    rw [he, affHomeo_one_apply]; push_cast; ring
  have he_symm : ∀ w, e.symm w = w + c := fun w => by
    rw [he, affHomeo_one_symm_apply]; push_cast; ring
  have hep_apply : ∀ z, ep z = z + c := fun z => affHomeo_one_apply c z
  have hKW : ∀ s, QuantumZipper.fwdHull W s =
      (fun z : ℂ => z + c) '' QuantumZipper.fwdHull V s := fun s => by
    rw [← fwdHull_add_const, hWV]
  have hMW : ∀ s z, QuantumZipper.fwdMap W s z = QuantumZipper.fwdMap V s (z - c) :=
    fun s z => by rw [← fwdMap_add_const, hWV]
  have hKV : ∀ s, QuantumZipper.fwdHull V s = e '' QuantumZipper.fwdHull W s := fun s => by
    rw [hKW, image_image]
    conv_lhs => rw [← image_id (QuantumZipper.fwdHull V s)]
    refine image_congr fun z _ => ?_
    simp [he_apply]
  set A' := e '' A with hA'
  set φ' : ℂ → ℂ := fun w => e (φ (e.symm w)) with hφ'
  have hA'h : IsHPHull A' := hA.image_affHomeo one_pos
  have hφ'm : IsMapOut A' φ' := hφ.comp_affHomeo one_pos
  have hd' : Disjoint (closure A') (closure (QuantumZipper.fwdHull V T)) := by
    rw [hKV, hA', ← e.image_closure, ← e.image_closure, disjoint_image_iff e.injective]
    exact hd.mono_right (subset_insert _ _)
  have h0' : (0 : ℂ) ∉ closure A' := by
    rw [hA', ← e.image_closure]
    rintro ⟨z, hz, hz0⟩
    rw [he_apply, sub_eq_zero] at hz0
    exact Set.disjoint_left.1 hd hz (hz0 ▸ mem_insert _ _)
  obtain ⟨ρ, hρ, hclr⟩ := exists_clearance hVc hV0 hT hA'h hd' h0'
  have hH : ImageHyp V A' φ' T ρ := ⟨hVc, hV0, hT, hA'h, hφ'm, hd', hρ, hclr⟩
  have hVt : ((V t : ℝ) : ℂ) = (W t : ℂ) - c := by rw [hV]; push_cast; ring
  have hEV : obstacle V A' t = e '' ((fun z => QuantumZipper.fwdMap W t z + W t) '' A) := by
    simp only [obstacle, gmap]
    rw [hA', image_image, image_image]
    refine image_congr fun z _ => ?_
    rw [he_apply, he_apply, hMW]
    simp only [gmap]
    rw [hVt]
    ring
  set R' : ℂ → ℂ := fun w => e (R (e.symm w)) with hR'def
  have hR' : IsMapOut (obstacle V A' t) R' := by rw [hEV]; exact hR.comp_affHomeo one_pos
  obtain ⟨⟨δ₀, hδ₀, Rext₀, hRd₀, hRe₀⟩, hrate⟩ := ImageHyp.rate hH ht hR'
  have hball : ∀ δ : ℝ, ∀ w : ℂ, w ∈ ball (W t : ℂ) δ ↔ w - c ∈ ball (V t : ℂ) δ := fun δ w => by
    rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hVt]
    ring_nf
  have hHc : ∀ w : ℂ, w ∈ H ↔ w - c ∈ H := fun w => by
    show 0 < w.im ↔ 0 < (w - c).im
    simp
  refine ⟨⟨δ₀, hδ₀, fun w => Rext₀ (w - c) + c, ?_, ?_⟩, fun δ hδ Rext hRd hRe => ?_⟩
  · have h1 : DifferentiableOn ℂ (fun w : ℂ => w - (c : ℂ)) (ball (W t : ℂ) δ₀) :=
      differentiableOn_id.sub_const _
    exact (hRd₀.comp h1 fun w hw => (hball δ₀ w).1 hw).add_const _
  · intro w hw
    have := hRe₀ ⟨(hball δ₀ w).1 hw.1, (hHc w).1 hw.2⟩
    simp only [hR'def, he_symm, he_apply, sub_add_cancel] at this
    simp only [this, sub_add_cancel]
  · set Rext' : ℂ → ℂ := fun w => Rext (w + c) - c with hRext'
    have hball' : ∀ w : ℂ, w ∈ ball (V t : ℂ) δ → w + c ∈ ball (W t : ℂ) δ := fun w hw => by
      rw [hball]; simpa using hw
    have h2 : DifferentiableOn ℂ (fun w : ℂ => w + (c : ℂ)) (ball (V t : ℂ) δ) :=
      differentiableOn_id.add_const _
    have hRd' : DifferentiableOn ℂ Rext' (ball (V t : ℂ) δ) :=
      (hRd.comp h2 hball').sub_const _
    have hRe' : EqOn Rext' R' (ball (V t : ℂ) δ ∩ H) := by
      intro w hw
      have hwH : w + c ∈ H := by rw [hHc]; simpa using hw.2
      simp only [hRext', hR'def, he_apply, he_symm, hRe ⟨hball' w hw.1, hwH⟩]
    obtain ⟨hpos, him, hder⟩ := hrate δ hδ Rext' hRd' hRe'
    have hderiv : deriv Rext' (V t) = deriv Rext (W t) := by
      rw [hRext', deriv_sub_const, deriv_comp_add_const, hVt, sub_add_cancel]
    rw [hderiv] at hpos him hder
    refine ⟨hpos, him, hder.congr_of_mem (fun s hs => ?_) ht⟩
    -- `½ hcap(φ(K_s))` is translation invariant
    have hK' := hH.isHPHull_image hs
    have himg : imageHull V φ' s = e '' (φ '' QuantumZipper.fwdHull W s) := by
      simp only [imageHull]
      rw [hKV, image_image, image_image]
      refine image_congr fun z _ => ?_
      simp only [hφ', he_symm, he_apply, sub_add_cancel]
    have hX : φ '' QuantumZipper.fwdHull W s = ep '' imageHull V φ' s := by
      rw [himg, image_image]
      conv_lhs => rw [← image_id (φ '' QuantumZipper.fwdHull W s)]
      refine image_congr fun z _ => ?_
      simp [hep_apply, he_apply]
    have hXh : IsHPHull (φ '' QuantumZipper.fwdHull W s) := by
      rw [hX]; exact hK'.image_affHomeo one_pos
    show hcapSet (φ '' QuantumZipper.fwdHull W s) / 2 = hcapSet (imageHull V φ' s) / 2
    rw [hcapSet_eq hXh, hcapSet_eq hK']
    have h1 := HPHull.hcap_affHomeo (x := c) ⟨_, hK'⟩ one_pos
    rw [one_pow, one_mul] at h1
    rw [← h1]
    congr 1
    exact HPHull.hcap_congr hX
/-- For `T > 0` the seed `W_0` lies in `closure K_T`, so `closure A ∩ closure K_T = ∅` is (HD1). -/
theorem disjoint_insert_of_pos {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {A : Set ℂ} (hd : Disjoint (closure A) (closure (QuantumZipper.fwdHull W T))) :
    Disjoint (closure A) (insert (W 0 : ℂ) (closure (QuantumZipper.fwdHull W T))) := by
  rw [Set.disjoint_insert_right]
  refine ⟨fun h => ?_, hd⟩
  have h0 := zero_mem_closure_fwdHull (W := fun s => W s - W 0) (hW.sub continuous_const)
    (sub_self _) hT
  have hK : QuantumZipper.fwdHull W T = (fun z : ℂ => z + W 0) ''
      QuantumZipper.fwdHull (fun s => W s - W 0) T := by
    rw [← fwdHull_add_const]
    simp only [sub_add_cancel]
  have hmem : (W 0 : ℂ) ∈ closure (QuantumZipper.fwdHull W T) := by
    rw [hK]
    exact image_closure_subset_closure_image (f := fun z : ℂ => z + W 0) (by fun_prop)
      ⟨0, h0, zero_add _⟩
  exact Set.disjoint_left.1 hd h hmem

/-- **Specification Aux. lemma 8** ((HD1)–(HD3)) **with the capacity rate**
([Law05] §4.6.1).

Let `W` be continuous, `K_t = fwdHull W t`, `g_t = f_t + W_t`, `A` a compact `ℍ`-hull with
mapping-out function `φ = g_A`, and assume (HD1): `closure A` is disjoint from
`closure K_T ∪ {W_0}`. Then there are a capacity clock `a` (continuous, strictly increasing on
`[0, T]`, `a 0 = 0`) and a continuous driver `W'` such that for every `t ∈ [0, T]`:
* (HD2) `φ(K_t)` is a compact `ℍ`-hull and `a t = ½ hcap(φ(K_t))`;
* `φ(K_t)` is the hull at time `a t` of the Loewner chain driven by `W'`;
* for every mapping-out function `R` of `E_t = g_t(A)`: (HD3) `g̃_{a(t)} ∘ φ = R ∘ g_t` on
  `ℍ \ (A ∪ K_t)` and `W'(a t) = R(W_t)` (boundary limit); `R` extends holomorphically across the
  real line near `W_t`; and for every such extension `R̂`, `R̂'(W_t)` is real and positive and
  `ȧ(t) = R̂'(W_t)²` (derivative within `[0, T]`). -/
theorem exists_loewner_image_rate {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (insert (W 0 : ℂ) (closure (QuantumZipper.fwdHull W T)))) :
    ∃ (a : ℝ → ℝ) (W' : ℝ → ℝ), Continuous W' ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 T) ∧
      ContinuousOn a (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        (∃ hK : IsHPHull (φ '' QuantumZipper.fwdHull W t), a t = HPHull.hcap ⟨_, hK⟩ / 2) ∧
        QuantumZipper.fwdHull W' (a t) = φ '' QuantumZipper.fwdHull W t ∧
        ∀ R : ℂ → ℂ, IsMapOut ((fun z => QuantumZipper.fwdMap W t z + W t) '' A) R →
          (∀ z ∈ H \ (A ∪ QuantumZipper.fwdHull W t),
            QuantumZipper.fwdMap W' (a t) (φ z) + W' (a t) =
              R (QuantumZipper.fwdMap W t z + W t)) ∧
          Tendsto R (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) ∧
          (∃ δ > 0, ∃ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) ∧
            EqOn Rext R (ball (W t : ℂ) δ ∩ H)) ∧
          ∀ δ > 0, ∀ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) →
            EqOn Rext R (ball (W t : ℂ) δ ∩ H) →
            0 < (deriv Rext (W t)).re ∧ (deriv Rext (W t)).im = 0 ∧
              HasDerivWithinAt a ((deriv Rext (W t)).re ^ 2) (Icc 0 T) t := by
  obtain ⟨a, W', hW'c, ha0, hamono, hacont, hmain⟩ := exists_loewner_image hW hT hA hφ hd
  refine ⟨a, W', hW'c, ha0, hamono, hacont, fun t ht => ?_⟩
  obtain ⟨hHD2, hhull, hR⟩ := hmain t ht
  refine ⟨hHD2, hhull, fun R hRm => ?_⟩
  obtain ⟨h1, h2⟩ := hR R hRm
  obtain ⟨hex, hrate⟩ := hasDerivWithinAt_hcap_image hW hT hA hφ hd ht hRm
  refine ⟨h1, h2, hex, fun δ hδ Rext hRd hRe => ?_⟩
  obtain ⟨hpos, him, hder⟩ := hrate δ hδ Rext hRd hRe
  refine ⟨hpos, him, hder.congr_of_mem (fun s hs => ?_) ht⟩
  obtain ⟨hK, has⟩ := (hmain s hs).1
  show a s = hcapSet (φ '' QuantumZipper.fwdHull W s) / 2
  rw [has, hcapSet_eq hK]

/-- **Specification Aux. lemma 8 with the capacity rate**, for `T > 0`: (HD1) is
`closure A ∩ closure K_T = ∅` (the seed `W_0` lies in `closure K_T`). -/
theorem exists_loewner_image_rate_of_pos {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (QuantumZipper.fwdHull W T))) :
    ∃ (a : ℝ → ℝ) (W' : ℝ → ℝ), Continuous W' ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 T) ∧
      ContinuousOn a (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        (∃ hK : IsHPHull (φ '' QuantumZipper.fwdHull W t), a t = HPHull.hcap ⟨_, hK⟩ / 2) ∧
        QuantumZipper.fwdHull W' (a t) = φ '' QuantumZipper.fwdHull W t ∧
        ∀ R : ℂ → ℂ, IsMapOut ((fun z => QuantumZipper.fwdMap W t z + W t) '' A) R →
          (∀ z ∈ H \ (A ∪ QuantumZipper.fwdHull W t),
            QuantumZipper.fwdMap W' (a t) (φ z) + W' (a t) =
              R (QuantumZipper.fwdMap W t z + W t)) ∧
          Tendsto R (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) ∧
          (∃ δ > 0, ∃ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) ∧
            EqOn Rext R (ball (W t : ℂ) δ ∩ H)) ∧
          ∀ δ > 0, ∀ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) →
            EqOn Rext R (ball (W t : ℂ) δ ∩ H) →
            0 < (deriv Rext (W t)).re ∧ (deriv Rext (W t)).im = 0 ∧
              HasDerivWithinAt a ((deriv Rext (W t)).re ^ 2) (Icc 0 T) t :=
  exists_loewner_image_rate hW hT.le hA hφ (disjoint_insert_of_pos hW hT hd)

end ConformalImageFull

end InteractingSLE
