/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoTime2Clock
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import QuantumZipper.Proofs.Complex.KoebeDistortion

/-!
# (D9), first part: a far obstacle keeps a uniform distance from the driver

Packet PROVE-ZHAN-GT4-A6. Source: Astra, *Follow-up proofs and dependency audit*, Part A.1.3
(`source/external/AstraIG1/ig1_followup_proofs.txt` L300–L340, ruling R38): "Consequently the real image interval
of `K_j` has a neighborhood, of uniform positive width in the `g_j`-chart, disjoint from `g_j(H_k)`." The source
proves this by kernel compactness; we give a direct quantitative proof at the driver, which is the point the Itô
step of A.1 needs.

Let `H₁` be a compact `ℍ`-hull (the enclosure of the growing curve) and let `S₂` be a bounded subset of `ℍ` at distance
at least `2δ` from `H₁` (the enclosure of the frozen curve). Then there is `r > 0`, depending only on `H₁`, `S₂`, `δ`,
such that for **every** continuous driver `W` starting in `closure H₁` whose hull stays in `H₁` up to time `T`, and
every `t ≤ T`, `a ∈ S₂`: `r ≤ |f_t(a)| = |g_t(a) − W_t|` (`exists_le_norm_fwdMap_uniform`).

Also here: `isMapOut_fwdMap_gen` (`g_t` maps out `K_t` for any starting point `W 0`, by translation),
`exists_isForwardSol_of_disjoint_ball_gen` (a real point `≠ W 0` with a disc missing `K_T` is alive), and
`driver_not_mem_image_of_refl` (the Schwarz reflection of `g_t` near a far real point omits `W_t`).

## Proof

* (Height monotonicity, `im_le_im_of_subset`.) For hulls `K ⊆ B`, `g_B = g_C ∘ g_K` with `C = g_K(B \ K)`, and
  `Im g_C(w) ≤ Im w`; hence `Im g_B(z) ≤ Im g_K(z)` on `ℍ \ B`. With `K = K_t ⊆ H₁`: `Im g_t(a) ≥ Im g_{H₁}(a)`.
* (High points.) On the compact set `Q` of points of height `≥ η` near `S₂`, `Im g_{H₁} ≥ m₁ > 0`; so
  `|f_t(a)| ≥ Im g_t(a) ≥ m₁` there.
* (Low points.) For `a ∈ S₂` of height `< η = δ/8`, put `x = Re a`. The disc `B(x, δ)` misses `K_t`, so `g_t` has an
  injective Schwarz reflection `G` on `B(x, δ/2)`, which omits `W_t` (real points of the disc are alive, their
  images are `W_t + u_t(y)`, `u_t(y) ≠ 0`). With `a' = x + iη ∈ Q`: the growth theorem at `a'` and
  `Im G(a') ≥ m₁ > 0 = Im G(x)` give `|G'(a')| ≥ 4m₁/(Mδ)`; the distortion theorem gives
  `|G'(a)| ≥ 2^{−C₂}|G'(a')|`; Koebe's covering theorem at `a` gives `|G(a) − W_t| ≥ (3δ/(8·48))|G'(a)|`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-! ### Height monotonicity of mapping-out functions -/

/-- **Mapping out a larger hull lowers points more**: for compact `ℍ`-hulls `K ⊆ B`,
`Im g_B(z) ≤ Im g_K(z)` on `ℍ \ B`. -/
theorem im_le_im_of_subset {K B : Set ℂ} {gK gB : ℂ → ℂ} (hK : IsHPHull K) (hB : IsHPHull B)
    (hKB : K ⊆ B) (hgK : IsMapOut K gK) (hgB : IsMapOut B gB) {z : ℂ} (hz : z ∈ H \ B) :
    (gB z).im ≤ (gK z).im := by
  have hC := hgK.isHPHull_image hK hB hKB
  obtain ⟨gC, hgC⟩ := hC.exists_isMapOut
  have hcomp := IsMapOut.comp hK hB hKB hgK hgC
  have heq := IsMapOut.eqOn hB hgB hcomp hz
  rw [heq, Function.comp_apply]
  have hzC : gK z ∈ H \ gK '' (B \ K) := by
    rw [hgK.H_diff_image hKB hB.1]; exact ⟨z, hz, rfl⟩
  exact hgC.im_le hC hzC

/-- **`g_t = f_t + W_t` maps out `K_t` for any starting point `W 0`** (translation of `isMapOut_fwdMap`). -/
theorem isMapOut_fwdMap_gen {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsMapOut (fwdHull W t) (fun z => fwdMap W t z + W t) := by
  set c := W 0 with hc
  set U : ℝ → ℝ := fun s => W s - c with hUdef
  have hU : Continuous U := hW.sub continuous_const
  have hU0 : U 0 = 0 := by simp [hUdef, hc]
  have hWU : W = fun s => U s + c := by funext s; simp [hUdef]
  have h := (isMapOut_fwdMap hU hU0 ht).comp_affHomeo (r := 1) (x := c) one_pos
  have hset : affHomeo 1 one_pos c '' fwdHull U t = fwdHull W t := by
    rw [hWU, ConformalImageFull.fwdHull_add_const]
    congr 1
    funext z
    exact ConformalImageFull.affHomeo_one_apply c z
  have hfun : (fun w => affHomeo 1 one_pos c
      ((fun z => fwdMap U t z + (U t : ℂ)) ((affHomeo 1 one_pos c).symm w))) =
      fun z => fwdMap W t z + W t := by
    funext w
    rw [ConformalImageFull.affHomeo_one_apply, ConformalImageFull.affHomeo_one_symm_apply]
    conv_rhs => rw [hWU]
    rw [ConformalImageFull.fwdMap_add_const]
    push_cast; ring
  rw [hset, hfun] at h
  exact h

/-- The Loewner map at time `t ≤ T` lowers points at least as little as the mapping-out function of an enclosure
of `K_T`. -/
theorem im_le_im_fwdMap {W : ℝ → ℝ} (hW : Continuous W) {T t : ℝ} (ht : t ∈ Icc 0 T)
    {H₁ : Set ℂ} (hH₁ : IsHPHull H₁) (hKH : fwdHull W T ⊆ H₁) {g₁ : ℂ → ℂ} (hg₁ : IsMapOut H₁ g₁)
    {z : ℂ} (hz : z ∈ H \ H₁) : (g₁ z).im ≤ (fwdMap W t z).im := by
  have hKt : fwdHull W t ⊆ H₁ := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hKH
  have h := im_le_im_of_subset (isHPHull_fwdHull hW ht.1) hH₁ hKt (isMapOut_fwdMap_gen hW ht.1) hg₁ hz
  simpa using h

/-! ### The driver is omitted by the reflection of `g_t` near a far real point -/

/-- **A real point with a disc outside the hull is alive** (any starting point `W 0`, by translating
`exists_isForwardSol_of_disjoint_ball`). -/
theorem exists_isForwardSol_of_disjoint_ball_gen {W : ℝ → ℝ} (hW : Continuous W) {x : ℝ} (hx : x ≠ W 0)
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 < r) (hd : Disjoint (ball (x : ℂ) r) (fwdHull W T)) :
    ∃ v, IsForwardSol W (x : ℂ) T v := by
  set c := W 0 with hc
  have hU : Continuous (fun s => W s - c) := hW.sub continuous_const
  have hU0 : (fun s => W s - c) 0 = 0 := sub_self _
  have hxU : x - c ≠ 0 := sub_ne_zero.2 hx
  have hdU : Disjoint (ball (((x - c : ℝ)) : ℂ) r) (fwdHull (fun s => W s - c) T) := by
    rw [Set.disjoint_left]
    intro z hz hzK
    have key := QuantumZipper.ASep.GC.mem_fwdHull_sub_const W c (z + c) T
    rw [add_sub_cancel_right] at key
    refine Set.disjoint_left.1 hd ?_ (key.1 hzK)
    rw [mem_ball, dist_eq_norm] at hz ⊢
    have e : z + (c : ℂ) - (x : ℂ) = z - (((x - c : ℝ)) : ℂ) := by push_cast; ring
    rw [e]; exact hz
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_disjoint_ball hU hU0 hxU hT hr hdU
  refine ⟨v, ?_⟩
  have key := QuantumZipper.ASep.GC.isForwardSol_sub_const W c (x : ℂ) T
  have e : (((x - c : ℝ)) : ℂ) = (x : ℂ) - (c : ℂ) := by push_cast; ring
  rw [e] at hv
  rw [← key]
  exact hv

/-- If `B(x, δ)` misses `K_t` and no real point of `B(x, δ/2)` is the starting point `W 0`, the Schwarz reflection
`G` of `g_t` across `B(x, δ/2) ∩ ℝ` omits the driver value `W_t`. -/
theorem driver_not_mem_image_of_refl {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {x δ : ℝ} (hδ : 0 < δ) (hd : Disjoint (ball (x : ℂ) δ) (fwdHull W t))
    (h0 : ∀ y : ℝ, (y : ℂ) ∈ ball (x : ℂ) (δ / 2) → y ≠ W 0) {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G (ball (x : ℂ) (δ / 2)))
    (hGg : EqOn G (fun z => fwdMap W t z + W t) (ball (x : ℂ) (δ / 2) ∩ H))
    (hup : ∀ z ∈ ball (x : ℂ) (δ / 2), 0 < z.im → 0 < (G z).im)
    (hlow : ∀ z ∈ ball (x : ℂ) (δ / 2), z.im < 0 → (G z).im < 0) :
    (W t : ℂ) ∉ G '' ball (x : ℂ) (δ / 2) := by
  rintro ⟨z, hz, hzW⟩
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have := hlow z hz hneg
    rw [hzW] at this; simp at this
  · -- a real point of the disc
    set y : ℝ := z.re with hy
    have hzy : z = (y : ℂ) := by
      apply Complex.ext <;> simp [hy, hzero]
    rw [hzy] at hz hzW
    have hy0 := h0 y hz
    have hdy : Disjoint (ball (y : ℂ) (δ / 2)) (fwdHull W t) := by
      refine hd.mono_left (ball_subset_ball' ?_)
      have := mem_ball.1 hz
      linarith
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_disjoint_ball_gen hW hy0 ht (by linarith) hdy
    have hlim := tendsto_fwdMap_of_isForwardSol hW ht hv
    have hlim' : Tendsto (fun w => fwdMap W t w + W t) (𝓝[H] (y : ℂ)) (𝓝 (v t + W t)) :=
      hlim.add tendsto_const_nhds
    have hGc : Tendsto G (𝓝[H] (y : ℂ)) (𝓝 (G y)) :=
      ((hGd.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)).tendsto).mono_left
        nhdsWithin_le_nhds
    have hev : ∀ᶠ w in 𝓝[H] (y : ℂ), G w = fwdMap W t w + W t := by
      filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hz)] with w hw
      exact hGg ⟨hw.2, hw.1⟩
    have hne : (𝓝[H] (y : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    have heq : G y = v t + W t := tendsto_nhds_unique (hGc.congr' hev) hlim'
    rw [heq] at hzW
    exact (hv.2 t ⟨ht, le_rfl⟩).1 (by linear_combination hzW)
  · have := hup z hz hpos
    rw [hzW] at this; simp at this

/-! ### The uniform clearance -/

/-- **(D9), uniform clearance of a far set from the driver.** If `H₁` is a compact `ℍ`-hull and `S₂ ⊆ ℍ` is bounded
with `2δ ≤ ‖a − z‖` for `a ∈ S₂`, `z ∈ H₁`, then there is `r > 0` such that for every continuous driver `W` starting in
`closure H₁` with `K_T ⊆ H₁`, every `t ∈ [0, T]` and every `a ∈ S₂`: `r ≤ |f_t(a)|`. -/
theorem exists_le_norm_fwdMap_uniform {H₁ S₂ : Set ℂ} (hH₁ : IsHPHull H₁)
    (hS₂ : Bornology.IsBounded S₂) (hS₂H : S₂ ⊆ H) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ S₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) :
    ∃ r > 0, ∀ W : ℝ → ℝ, Continuous W → ((W 0 : ℝ) : ℂ) ∈ closure H₁ → ∀ T : ℝ, fwdHull W T ⊆ H₁ →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ S₂, r ≤ ‖fwdMap W t a‖ := by
  obtain ⟨g₁, hg₁⟩ := hH₁.exists_isMapOut
  obtain ⟨R₀, hR₀⟩ := hS₂.exists_norm_le
  set η : ℝ := δ / 8 with hη
  set Q : Set ℂ := {z : ℂ | η ≤ z.im ∧ ‖z‖ ≤ R₀ + δ ∧ ∀ w ∈ H₁, δ / 2 ≤ ‖z - w‖} with hQ
  have hQc : IsCompact Q := by
    refine (isCompact_closedBall (0 : ℂ) (R₀ + δ)).of_isClosed_subset ?_ ?_
    · refine (isClosed_le continuous_const continuous_im).inter
        ((isClosed_le continuous_norm continuous_const).inter ?_)
      have : {z : ℂ | ∀ w ∈ H₁, δ / 2 ≤ ‖z - w‖} = ⋂ w ∈ H₁, {z : ℂ | δ / 2 ≤ ‖z - w‖} := by
        ext z; simp
      have hcl : IsClosed {z : ℂ | ∀ w ∈ H₁, δ / 2 ≤ ‖z - w‖} := by
        rw [this]
        exact isClosed_biInter fun w _ =>
          isClosed_le continuous_const (continuous_id.sub continuous_const).norm
      exact hcl
    · intro z hz; rw [mem_closedBall_zero_iff]; exact hz.2.1
  have hQH : Q ⊆ H \ H₁ := fun z hz => ⟨show 0 < z.im by linarith [hz.1], fun hz1 => by
    have := hz.2.2 z hz1; rw [sub_self, norm_zero] at this; linarith⟩
  obtain ⟨m₁, hm₁, hm₁le⟩ : ∃ m₁ > 0, ∀ q ∈ Q, m₁ ≤ (g₁ q).im := by
    rcases Q.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun q hq => by rw [he] at hq; exact absurd hq (notMem_empty q)⟩
    · have hc : ContinuousOn (fun q => (g₁ q).im) Q :=
        continuous_im.comp_continuousOn (hg₁.1.1.continuousOn.mono hQH)
      obtain ⟨q₀, hq₀, hmin⟩ := hQc.exists_isMinOn hne hc
      exact ⟨(g₁ q₀).im, hg₁.1.2.mapsTo (hQH hq₀), fun q hq => hmin hq⟩
  set M := QuantumZipper.CA.Koebe.koebeGrowthConst with hMdef
  set C₂ := QuantumZipper.CA.Koebe.koebeDistExp with hC₂def
  have hM : 0 < M := QuantumZipper.CA.Koebe.koebeGrowthConst_pos
  have hC₂ : 0 < C₂ := QuantumZipper.CA.Koebe.koebeDistExp_pos
  set c : ℝ := (1 / 2 : ℝ) ^ C₂ with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨min m₁ (m₁ * c / (32 * M)), lt_min hm₁ (by positivity), ?_⟩
  intro W hW hW0 T hKH t ht a ha
  have haH : a ∈ H := hS₂H ha
  have haH₁ : a ∉ H₁ := fun h => by
    have := hsep a ha a h; rw [sub_self, norm_zero] at this; linarith
  by_cases hhigh : η ≤ a.im
  · -- a high point
    have haQ : a ∈ Q := ⟨hhigh, by linarith [hR₀ a ha], fun w hw => by linarith [hsep a ha w hw]⟩
    have h1 := hm₁le a haQ
    have h2 := im_le_im_fwdMap hW ht hH₁ hKH hg₁ ⟨haH, haH₁⟩
    calc min m₁ (m₁ * c / (32 * M)) ≤ m₁ := min_le_left _ _
      _ ≤ (fwdMap W t a).im := h1.trans h2
      _ ≤ |(fwdMap W t a).im| := le_abs_self _
      _ ≤ ‖fwdMap W t a‖ := abs_im_le_norm _
  · -- a low point
    rw [not_le] at hhigh
    have ha0 : 0 < a.im := haH
    set x : ℝ := a.re with hx
    have hax_eq : a - (x : ℂ) = (a.im : ℂ) * I := by
      apply Complex.ext <;> simp [hx]
    have hax : ‖a - x‖ = a.im := by
      rw [hax_eq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ha0]
    have hxH₁ : ∀ w ∈ H₁, δ < ‖(x : ℂ) - w‖ := by
      intro w hw
      have h1 := hsep a ha w hw
      have h2 : ‖a - w‖ ≤ ‖a - x‖ + ‖(x : ℂ) - w‖ := by
        calc ‖a - w‖ = ‖(a - x) + ((x : ℂ) - w)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    have ht0 : 0 ≤ t := ht.1
    have hKt : fwdHull W t ⊆ H₁ := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hKH
    have hd : Disjoint (ball (x : ℂ) δ) (fwdHull W t) := by
      rw [Set.disjoint_left]
      intro z hz hzK
      have := hxH₁ z (hKt hzK)
      rw [mem_ball, dist_eq_norm, ← norm_neg, neg_sub] at hz
      linarith
    obtain ⟨G, hGd, hGg, -, -, -, hGinj, hup, hlow, hreal⟩ :=
      ConformalImageFull.IsMapOut.exists_reflection_full (isHPHull_fwdHull hW ht0)
        (isMapOut_fwdMap_gen hW ht0) hδ hd
    have hδ2 : 0 < δ / 2 := by linarith
    have h0' : ∀ y : ℝ, (y : ℂ) ∈ ball (x : ℂ) (δ / 2) → y ≠ W 0 := by
      intro y hy hy0
      obtain ⟨w, hw, hdw⟩ := Metric.mem_closure_iff.1 hW0 (δ / 2) hδ2
      have h1 := hxH₁ w hw
      rw [← hy0] at hdw
      rw [mem_ball, dist_eq_norm] at hy
      rw [dist_eq_norm] at hdw
      have := norm_sub_le_norm_sub_add_norm_sub (x : ℂ) (y : ℂ) w
      rw [norm_sub_rev (x : ℂ) (y : ℂ)] at this
      linarith
    have hWnot := driver_not_mem_image_of_refl hW ht0 hδ hd h0' hGd hGg hup hlow
    have haB : a ∈ ball (x : ℂ) (δ / 2) := by rw [mem_ball, dist_eq_norm, hax]; linarith
    set a' : ℂ := (x : ℂ) + (η : ℂ) * I with ha'
    have ha'x : ‖a' - x‖ = η := by
      rw [ha', add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    have haa' : dist a a' = η - a.im := by
      have : a - a' = ((a.im - η : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp [ha', hx]
      rw [dist_eq_norm, this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith), neg_sub]
    have hsub : ball a' (δ / 4) ⊆ ball (x : ℂ) (δ / 2) :=
      ball_subset_ball' (by rw [dist_eq_norm, ha'x]; linarith)
    have ha'B : a' ∈ ball (x : ℂ) (δ / 2) := hsub (mem_ball_self (by linarith))
    have ha'H : a' ∈ H := show 0 < a'.im by simp [ha']; linarith
    -- the height of `G a'`
    have ha'Q : a' ∈ Q := by
      refine ⟨by simp [ha'], ?_, fun w hw => ?_⟩
      · have h1 : ‖a'‖ ≤ ‖a‖ + ‖a' - a‖ := by
          calc ‖a'‖ = ‖a + (a' - a)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        have h2 : ‖a' - a‖ = η - a.im := by rw [← dist_eq_norm, dist_comm, haa']
        linarith [hR₀ a ha]
      · have h1 : ‖(x : ℂ) - w‖ ≤ ‖(x : ℂ) - a'‖ + ‖a' - w‖ := by
          calc ‖(x : ℂ) - w‖ = ‖((x : ℂ) - a') + (a' - w)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        rw [norm_sub_rev (x : ℂ) a', ha'x] at h1
        linarith [hxH₁ w hw]
    have hGa' : G a' = fwdMap W t a' + W t := hGg ⟨ha'B, ha'H⟩
    have him : m₁ ≤ (G a').im := by
      rw [hGa']
      simpa using (hm₁le a' ha'Q).trans (im_le_im_fwdMap hW ht hH₁ hKH hg₁ (hQH ha'Q))
    have hGx : (G x).im = 0 := hreal x (mem_ball_self hδ2) (by simp)
    -- growth at `a'`
    have hgrowth := QuantumZipper.CA.Koebe.norm_sub_le_growth (hGd.mono hsub) (hGinj.mono hsub)
      (by linarith : (0 : ℝ) < δ / 4) (w := (x : ℂ))
      (by rw [dist_eq_norm, ← norm_neg, neg_sub, ha'x]; linarith)
    have h1 : m₁ ≤ M * (δ / 4) * ‖deriv G a'‖ := by
      refine le_trans ?_ hgrowth
      calc m₁ ≤ (G a').im := him
        _ = -((G x - G a').im) := by simp [hGx]
        _ ≤ |(G x - G a').im| := neg_le_abs _
        _ ≤ ‖G x - G a'‖ := abs_im_le_norm _
    -- distortion from `a'` to `a`
    have haB' : a ∈ ball a' (δ / 4) := by rw [mem_ball, haa']; linarith
    have hdist := QuantumZipper.CA.Koebe.distortion_le_norm_deriv (hGd.mono hsub) (hGinj.mono hsub) haB'
    have hratio : (1 / 2 : ℝ) ≤ 1 - dist a a' / (δ / 4) := by
      rw [haa']
      have : (η - a.im) / (δ / 4) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have h2 : c * ‖deriv G a'‖ ≤ ‖deriv G a‖ := by
      refine le_trans ?_ hdist
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num) hratio hC₂.le) (norm_nonneg _)
    -- Koebe at `a`
    have hkoebe := QuantumZipper.CA.Koebe.koebeCovConst_mul_le_infDist_of_mem hGd hGinj haB
    have hinf : infDist (G a) (G '' ball (x : ℂ) (δ / 2))ᶜ ≤ dist (G a) (W t) :=
      infDist_le_dist_of_mem hWnot
    have hGa : G a = fwdMap W t a + W t := hGg ⟨haB, haH⟩
    have hdGa : dist (G a) (W t) = ‖fwdMap W t a‖ := by rw [hGa, dist_eq_norm]; ring_nf
    have hax' : dist a x = a.im := by rw [dist_eq_norm, hax]
    have h3 : δ / 128 * ‖deriv G a‖ ≤ ‖fwdMap W t a‖ := by
      have hk : QuantumZipper.CA.Koebe.koebeCovConst = 1 / 48 := rfl
      rw [hk, hax'] at hkoebe
      have hle : δ / 128 * ‖deriv G a‖ ≤ 1 / 48 * (δ / 2 - a.im) * ‖deriv G a‖ := by
        rw [show 1 / 48 * (δ / 2 - a.im) * ‖deriv G a‖ = (δ / 2 - a.im) / 48 * ‖deriv G a‖ by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      linarith [hle.trans hkoebe, hdGa ▸ hinf]
    -- combine
    have hD' : 4 * m₁ / (M * δ) ≤ ‖deriv G a'‖ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc min m₁ (m₁ * c / (32 * M)) ≤ m₁ * c / (32 * M) := min_le_right _ _
      _ = δ / 128 * (c * (4 * m₁ / (M * δ))) := by field_simp; ring
      _ ≤ δ / 128 * (c * ‖deriv G a'‖) := by gcongr
      _ ≤ δ / 128 * ‖deriv G a‖ := by gcongr
      _ ≤ ‖fwdMap W t a‖ := h3

end InteractingSLE.ZhanGT4
