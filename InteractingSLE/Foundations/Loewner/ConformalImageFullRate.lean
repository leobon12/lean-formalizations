import InteractingSLE.Foundations.Loewner.ConformalImageFull
import InteractingSLE.Foundations.Loewner.ConformalImageFullCircle

/-!
# The capacity rate of the conformal image of a Loewner chain

Packet PROVE-GEO-LOC2, step (2): [Law05] §4.6.1, `ḃ(t) = 2 Φ_t'(U_t)²`, i.e. in the notation of
Specification Aux. lemma 8, `ȧ(t) = R_t'(W_t)²` where `a(t) = ½ hcap(φ(K_t))` and `R_t = g_{E_t}`,
`E_t = g_t(A)`.

## Proof

For `s₁ < s₂` let `L = g_{s₁}(K_{s₂} \ K_{s₁})` (a small hull at `W_{s₁}`, `hcap L = 2(s₂ − s₁)`)
and `inc = R_{s₁}(L)` (a small hull at `R_{s₁}(W_{s₁})`, `hcap inc = 2(a(s₂) − a(s₁))`). Then
`R_{s₂} ∘ g_L = g_inc ∘ R_{s₁}` near `W_{s₁}`. Write `F, F̃` for the reflections of `R_{s₁}, R_{s₂}`
across the real line near the driver. On the circle `|w − W_{s₁}| = r`, [Law05] Proposition 3.46
for `g_L` and `g_inc` and Taylor's formula for `F̃` give
`F̃ − F = h'/(F − y) − F̃' h/(w − x) + O(ε' h' + ε h + h²)`,
and the circle integral (`ConformalImageFullCircle.lean`) gives `h'/F'(x) − h F̃'(x) = O(…)`;
`F̃'(x) → F'(x)` by Cauchy's estimate. Hence `(a(s₂) − a(s₁))/(s₂ − s₁) → R_s'(W_s)²` as
`s₁ ≤ s ≤ s₂`, `s₂ − s₁ → 0`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace ConformalImageFull

open ConformalImage

/-! ### The reflection of a mapping-out function near a real point -/

/-- If `G` is holomorphic on `ball a δ` (`a` real), sends upper points up, lower points down and
real points to real points, and is injective on the upper half of the ball, its image is open. -/
theorem isOpen_image_ball {G : ℂ → ℂ} {a : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hGd : DifferentiableOn ℂ G (ball (a : ℂ) δ)) (hinj : InjOn G (ball (a : ℂ) δ ∩ H)) :
    IsOpen (G '' ball (a : ℂ) δ) := by
  have hGa : AnalyticOnNhd ℂ G (ball (a : ℂ) δ) := hGd.analyticOnNhd isOpen_ball
  have h1 : ((a : ℂ) + ((δ / 2 : ℝ) : ℂ) * I) ∈ ball (a : ℂ) δ ∩ H :=
    mem_ball_inter_H (by positivity) (by linarith)
  have h2 : ((a : ℂ) + ((δ / 4 : ℝ) : ℂ) * I) ∈ ball (a : ℂ) δ ∩ H :=
    mem_ball_inter_H (by positivity) (by linarith)
  rcases hGa.is_constant_or_isOpen (convex_ball _ _).isPreconnected with ⟨c, hc⟩ | h
  · exfalso
    have := hinj h1 h2 ((hc _ h1.1).trans (hc _ h2.1).symm)
    have him := congrArg Complex.im this
    simp at him
    linarith
  · exact h _ subset_rfl isOpen_ball

/-- **The full reflection package** of a mapping-out function across a real interval with
clearance `ρ`: holomorphic, symmetric, `48`-Lipschitz towards the centre, injective, and sending
the upper (lower) half-disc into the upper (lower) half-plane. -/
theorem IsMapOut.exists_reflection_full {E : Set ℂ} {g : ℂ → ℂ} (hE : IsHPHull E)
    (hg : IsMapOut E g) {x ρ : ℝ} (hρ : 0 < ρ) (hd : Disjoint (ball (x : ℂ) ρ) E) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (x : ℂ) (ρ / 2)) ∧
      EqOn G g (ball (x : ℂ) (ρ / 2) ∩ H) ∧
      (∀ z ∈ ball (x : ℂ) (ρ / 2), G (conj z) = conj (G z)) ∧
      G x = limUnder (𝓝[H] (x : ℂ)) g ∧
      (∀ z ∈ ball (x : ℂ) (ρ / 2), ‖G z - G x‖ ≤ 48 * ‖z - x‖) ∧
      InjOn G (ball (x : ℂ) (ρ / 2)) ∧
      (∀ z ∈ ball (x : ℂ) (ρ / 2), 0 < z.im → 0 < (G z).im) ∧
      (∀ z ∈ ball (x : ℂ) (ρ / 2), z.im < 0 → (G z).im < 0) ∧
      (∀ z ∈ ball (x : ℂ) (ρ / 2), z.im = 0 → (G z).im = 0) := by
  obtain ⟨G, hGd, hGS, hGconj, hGreal, hLip, hGlim⟩ := hg.exists_reflection hE hd
  set B := ball (x : ℂ) (ρ / 2) with hB
  have hxB : (x : ℂ) ∈ B := mem_ball_self (by positivity)
  have hupper : ∀ z ∈ B, 0 < z.im → 0 < (G z).im := fun z hz hz0 => by
    rw [hGS ⟨hz, hz0⟩]
    exact hg.1.2.mapsTo (ball_half_inter_H_subset hd ⟨hz, hz0⟩)
  have hlower : ∀ z ∈ B, z.im < 0 → (G z).im < 0 := fun z hz hz0 => by
    have hcz : conj z ∈ B := conj_mem_ball hz
    have h1 := hupper _ hcz (by simp; linarith)
    rw [hGconj z hz, Complex.conj_im] at h1
    linarith
  have hpos_of : ∀ z ∈ B, 0 < (G z).im → 0 < z.im := fun z hz h => by
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · exact absurd (hlower z hz hneg) (not_lt.2 h.le)
    · exact absurd (hGreal z hz hzero) h.ne'
    · exact hpos
  have hreal_of : ∀ z ∈ B, (G z).im = 0 → z.im = 0 := fun z hz h => by
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · exact absurd h (hlower z hz hneg).ne
    · exact hzero
    · exact absurd h (hupper z hz hpos).ne'
  have hinjH : InjOn G (B ∩ H) := fun a ha b hb hab => by
    rw [hGS ha, hGS hb] at hab
    exact hg.1.2.injOn (ball_half_inter_H_subset hd ha) (ball_half_inter_H_subset hd hb) hab
  -- the boundary value
  have hGx : G x = limUnder (𝓝[H] (x : ℂ)) g := by
    have hlim := hGlim x hxB (by simp)
    have hnhds : 𝓝[B ∩ H] (x : ℂ) = 𝓝[H] (x : ℂ) :=
      nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hxB))
    rw [hnhds] at hlim
    have hne : (𝓝[H] (x : ℂ)).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.1 ?_
      exact closure_mono inter_subset_right
        (subset_closure_ball_inter_H (x : ℂ) 1 ⟨mem_ball_self one_pos, show (0 : ℝ) ≤ (x : ℂ).im
          by simp⟩)
    exact hlim.limUnder_eq.symm
  have hGxr : conj (G x) = G x := by
    have := hGreal x hxB (by simp)
    exact Complex.conj_eq_iff_im.2 this
  refine ⟨G, hGd, hGS, hGconj, hGx, ?_, ?_, hupper, hlower, hGreal⟩
  · intro z hz
    have hxH : (x : ℂ) ∈ B ∩ Hbar := ⟨hxB, show (0 : ℝ) ≤ (x : ℂ).im by simp⟩
    by_cases hz0 : 0 ≤ z.im
    · exact hLip (x : ℂ) hxH z ⟨hz, hz0⟩
    · have hcz : conj z ∈ B ∩ Hbar := ⟨conj_mem_ball hz, show 0 ≤ (conj z).im by simp; linarith⟩
      have h1 := hLip (x : ℂ) hxH (conj z) hcz
      have e1 : G z = conj (G (conj z)) := by
        rw [← hGconj (conj z) hcz.1, Complex.conj_conj]
      have e2 : ‖conj z - (x : ℂ)‖ = ‖z - x‖ := by
        rw [show conj z - (x : ℂ) = conj (z - x) by simp [map_sub, Complex.conj_ofReal],
          Complex.norm_conj]
      rw [e1, ← hGxr, ← map_sub, Complex.norm_conj]
      rw [e2] at h1
      exact h1
  · -- injectivity
    intro a ha b hb hab
    rcases lt_trichotomy a.im 0 with ha0 | ha0 | ha0
    · have hb0 : b.im < 0 := by
        rcases lt_trichotomy b.im 0 with hb0 | hb0 | hb0
        · exact hb0
        · have := hlower a ha ha0
          rw [hab, hGreal b hb hb0] at this
          exact absurd this (lt_irrefl _)
        · have := hlower a ha ha0; rw [hab] at this; linarith [hupper b hb hb0]
      have hca : conj a ∈ B ∩ H := ⟨conj_mem_ball ha, show 0 < (conj a).im by simp; linarith⟩
      have hcb : conj b ∈ B ∩ H := ⟨conj_mem_ball hb, show 0 < (conj b).im by simp; linarith⟩
      have := hinjH hca hcb (by rw [hGconj a ha, hGconj b hb, hab])
      have := congrArg conj this
      simpa only [Complex.conj_conj] using this
    · -- real points: open mapping on two disjoint small balls
      have hb0 : b.im = 0 := hreal_of b hb (by rw [← hab]; exact hGreal a ha ha0)
      by_contra hne
      have hare : ((a.re : ℝ) : ℂ) = a := Complex.ext (by simp) (by simp [ha0])
      have hbre : ((b.re : ℝ) : ℂ) = b := Complex.ext (by simp) (by simp [hb0])
      have hab0 : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      obtain ⟨δa, hδa, hδaB⟩ := Metric.isOpen_iff.1 isOpen_ball a ha
      obtain ⟨δb, hδb, hδbB⟩ := Metric.isOpen_iff.1 isOpen_ball b hb
      set δ := min (min δa δb) (‖a - b‖ / 2) with hδ
      have hδpos : 0 < δ := lt_min (lt_min hδa hδb) (by positivity)
      have hBa : ball a δ ⊆ B :=
        (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))).trans hδaB
      have hBb : ball b δ ⊆ B :=
        (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))).trans hδbB
      have hopen : ∀ c : ℂ, c.im = 0 → ball c δ ⊆ B → IsOpen (G '' ball c δ) := fun c hc0 hcB => by
        have hcre : ((c.re : ℝ) : ℂ) = c := Complex.ext (by simp) (by simp [hc0])
        rw [← hcre] at hcB ⊢
        exact isOpen_image_ball hδpos (hGd.mono hcB) (hinjH.mono (inter_subset_inter_left _ hcB))
      have hGaO := hopen a ha0 hBa
      have hGbO := hopen b hb0 hBb
      have hmem : G a ∈ G '' ball a δ ∩ G '' ball b δ :=
        ⟨⟨a, mem_ball_self hδpos, rfl⟩, ⟨b, mem_ball_self hδpos, hab.symm⟩⟩
      obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.1 (hGaO.inter hGbO) _ hmem
      set u := G a + ((η / 2 : ℝ) : ℂ) * I with hu
      have huball : u ∈ ball (G a) η := by
        rw [mem_ball, dist_eq_norm, hu, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hη)]
        linarith
      have huim : 0 < u.im := by simp [hu, hGreal a ha ha0, hη]
      obtain ⟨⟨a', ha', hua⟩, ⟨b', hb', hub⟩⟩ := hηsub huball
      have ha'H : a' ∈ B ∩ H := ⟨hBa ha', hpos_of a' (hBa ha') (hua ▸ huim)⟩
      have hb'H : b' ∈ B ∩ H := ⟨hBb hb', hpos_of b' (hBb hb') (hub ▸ huim)⟩
      have := hinjH ha'H hb'H (hua.trans hub.symm)
      rw [this] at ha'
      have h1 : ‖a - b‖ < ‖a - b‖ := by
        calc ‖a - b‖ ≤ ‖a - b'‖ + ‖b' - b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ < δ + δ := by
            rw [mem_ball, dist_eq_norm] at ha' hb'
            exact add_lt_add (by rw [norm_sub_rev]; exact ha') hb'
          _ ≤ ‖a - b‖ := by linarith [min_le_right (min δa δb) (‖a - b‖ / 2)]
      exact lt_irrefl _ h1
    · have hb0 : 0 < b.im := hpos_of b hb (by rw [← hab]; exact hupper a ha ha0)
      exact hinjH ⟨ha, ha0⟩ ⟨hb, hb0⟩ hab
/-! ### Cauchy estimates and Taylor's formula -/

theorem closedBall_subset_ball_of_mem {c w : ℂ} {r₁ r₂ : ℝ} (hw : w ∈ ball c (r₂ - r₁)) :
    closedBall w r₁ ⊆ ball c r₂ := by
  intro z hz
  rw [mem_closedBall] at hz
  rw [mem_ball] at hw ⊢
  calc dist z c ≤ dist z w + dist w c := dist_triangle _ _ _
    _ < r₁ + (r₂ - r₁) := by linarith
    _ = r₂ := by ring

theorem diffContOnCl_of_subset {G : ℂ → ℂ} {c w : ℂ} {r R : ℝ} (hr : 0 < r)
    (hGd : DifferentiableOn ℂ G (ball c R)) (hsub : closedBall w r ⊆ ball c R) :
    DiffContOnCl ℂ G (ball w r) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_ball w hr.ne']
  exact hGd.mono hsub

/-- **Cauchy estimate** for the first derivative. -/
theorem norm_deriv_le_96 {G : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hGd : DifferentiableOn ℂ G (ball c (ρ / 2)))
    (hL : ∀ z ∈ ball c (ρ / 2), ‖G z - G c‖ ≤ 48 * ‖z - c‖) {w : ℂ} (hw : w ∈ ball c (ρ / 4)) :
    ‖deriv G w‖ ≤ 96 := by
  have hsub : closedBall w (ρ / 4) ⊆ ball c (ρ / 2) :=
    closedBall_subset_ball_of_mem (by rw [show ρ / 2 - ρ / 4 = ρ / 4 by ring]; exact hw)
  have hd : DiffContOnCl ℂ (fun z => G z - G c) (ball w (ρ / 4)) :=
    diffContOnCl_of_subset (by positivity) (hGd.sub_const _) hsub
  have hC : ∀ z ∈ sphere w (ρ / 4), ‖G z - G c‖ ≤ 24 * ρ := by
    intro z hz
    have hzc : ‖z - c‖ ≤ ρ / 2 := by
      have := hsub (sphere_subset_closedBall hz)
      rw [mem_ball, dist_eq_norm] at this
      exact this.le
    calc ‖G z - G c‖ ≤ 48 * ‖z - c‖ := hL z (hsub (sphere_subset_closedBall hz))
      _ ≤ 48 * (ρ / 2) := by gcongr
      _ = 24 * ρ := by ring
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hd hC
  rw [deriv_sub_const] at this
  calc ‖deriv G w‖ ≤ 24 * ρ / (ρ / 4) := this
    _ = 96 := by field_simp; ring

/-- **Cauchy estimate** for the second derivative. -/
theorem norm_deriv_deriv_le {G : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hGd : DifferentiableOn ℂ G (ball c (ρ / 2)))
    (hL : ∀ z ∈ ball c (ρ / 2), ‖G z - G c‖ ≤ 48 * ‖z - c‖) {w : ℂ} (hw : w ∈ ball c (ρ / 8)) :
    ‖deriv (deriv G) w‖ ≤ 768 / ρ := by
  have hsub : closedBall w (ρ / 8) ⊆ ball c (ρ / 4) :=
    closedBall_subset_ball_of_mem (by rw [show ρ / 4 - ρ / 8 = ρ / 8 by ring]; exact hw)
  have hG' : DifferentiableOn ℂ (deriv G) (ball c (ρ / 2)) :=
    (hGd.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hd : DiffContOnCl ℂ (deriv G) (ball w (ρ / 8)) :=
    diffContOnCl_of_subset (by positivity) hG' (hsub.trans (ball_subset_ball (by linarith)))
  have hC : ∀ z ∈ sphere w (ρ / 8), ‖deriv G z‖ ≤ 96 := fun z hz =>
    norm_deriv_le_96 hρ hGd hL (hsub (sphere_subset_closedBall hz))
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hd hC
  calc ‖deriv (deriv G) w‖ ≤ 96 / (ρ / 8) := this
    _ = 768 / ρ := by field_simp; ring

/-- **Taylor's formula** with a second-derivative bound on a convex open set. -/
theorem norm_taylor_le {G : ℂ → ℂ} {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S)
    (hGd : DifferentiableOn ℂ G S) {M : ℝ} (hM : ∀ z ∈ S, ‖deriv (deriv G) z‖ ≤ M) {w w₁ : ℂ}
    (hw : w ∈ S) (hw₁ : w₁ ∈ S) :
    ‖G w₁ - G w - deriv G w * (w₁ - w)‖ ≤ M * ‖w₁ - w‖ ^ 2 := by
  have hGa := hGd.analyticOnNhd hSo
  have hG'd : DifferentiableOn ℂ (deriv G) S := hGa.deriv.differentiableOn
  have hseg : segment ℝ w w₁ ⊆ S := hS.segment_subset hw hw₁
  have hlip : ∀ z ∈ segment ℝ w w₁, ‖deriv G z - deriv G w‖ ≤ M * ‖w₁ - w‖ := by
    intro z hz
    have h1 := hS.norm_image_sub_le_of_norm_deriv_le
      (fun u hu => hG'd.differentiableAt (hSo.mem_nhds hu)) hM hw (hseg hz)
    exact h1.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz)
      ((norm_nonneg _).trans (hM w hw)))
  set φ : ℂ → ℂ := fun z => G z - deriv G w * z with hφ
  have hφd : ∀ z ∈ segment ℝ w w₁, DifferentiableAt ℂ φ z := fun z hz =>
    ((hGd.differentiableAt (hSo.mem_nhds (hseg hz))).sub
      ((differentiableAt_id).const_mul _))
  have hφ' : ∀ z ∈ segment ℝ w w₁, ‖deriv φ z‖ ≤ M * ‖w₁ - w‖ := by
    intro z hz
    have : deriv φ z = deriv G z - deriv G w := by
      have hd := ((hGd.differentiableAt (hSo.mem_nhds (hseg hz))).hasDerivAt.sub
        ((hasDerivAt_id z).const_mul (deriv G w)))
      rw [mul_one] at hd
      exact hd.deriv
    rw [this]
    exact hlip z hz
  have := (convex_segment w w₁).norm_image_sub_le_of_norm_deriv_le hφd hφ'
    (left_mem_segment ℝ w w₁) (right_mem_segment ℝ w w₁)
  have e : φ w₁ - φ w = G w₁ - G w - deriv G w * (w₁ - w) := by simp only [hφ]; ring
  rw [e] at this
  calc ‖G w₁ - G w - deriv G w * (w₁ - w)‖ ≤ M * ‖w₁ - w‖ * ‖w₁ - w‖ := this
    _ = M * ‖w₁ - w‖ ^ 2 := by ring
/-- The derivative of a conjugation-symmetric holomorphic function is conjugation-symmetric. -/
theorem deriv_conj_eq {G : ℂ → ℂ} {c R : ℝ} (hGd : DifferentiableOn ℂ G (ball (c : ℂ) R))
    (hsym : ∀ z ∈ ball (c : ℂ) R, G (conj z) = conj (G z)) {z : ℂ} (hz : z ∈ ball (c : ℂ) R) :
    deriv G (conj z) = conj (deriv G z) := by
  have hd : HasDerivAt G (deriv G z) z :=
    (hGd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have h2 := hd.conj_conj
  have heq : (conj ∘ G ∘ conj) =ᶠ[𝓝 (conj z)] G := by
    filter_upwards [isOpen_ball.mem_nhds (conj_mem_ball hz)] with w hw
    have := hsym (conj w) (conj_mem_ball hw)
    simp only [Complex.conj_conj] at this
    simp only [Function.comp_apply, this]
  exact (h2.congr_of_eventuallyEq heq.symm).deriv

/-- A bound at the non-real points of a circle centred on the real line extends to the whole
circle, for a function continuous on the circle. -/
theorem norm_le_of_sphere_im_ne {f : ℂ → ℂ} {c r M : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (sphere (c : ℂ) r))
    (hb : ∀ w ∈ sphere (c : ℂ) r, w.im ≠ 0 → ‖f w‖ ≤ M) :
    ∀ w ∈ sphere (c : ℂ) r, ‖f w‖ ≤ M := by
  intro w hw
  by_cases hw0 : w.im = 0
  swap
  · exact hb w hw hw0
  set p : ℝ → ℂ := fun θ => (c : ℂ) + (w - c) * exp ((θ : ℂ) * I) with hp
  have hp0 : p 0 = w := by simp [hp]
  have hpc : Continuous p := by fun_prop
  have hwc : ‖w - c‖ = r := by rw [← dist_eq_norm]; exact hw
  have hps : ∀ θ : ℝ, p θ ∈ sphere (c : ℂ) r := by
    intro θ
    rw [mem_sphere, dist_eq_norm, hp, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, hwc]
  have hre : (w - c).re ≠ 0 := by
    intro h0
    have hz : w - c = 0 := Complex.ext (by simpa using h0) (by simp [hw0])
    rw [hz, norm_zero] at hwc
    linarith
  have hpim : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, (p θ).im ≠ 0 := by
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have him : (p θ).im = (w - c).re * Real.sin θ := by
      simp only [hp, add_im, ofReal_im, zero_add, mul_im, exp_ofReal_mul_I_re,
        exp_ofReal_mul_I_im, sub_im, hw0, sub_zero, zero_mul, add_zero]
    rw [him]
    exact mul_ne_zero hre hs.ne'
  have htend : Tendsto (fun θ => f (p θ)) (𝓝[>] (0 : ℝ)) (𝓝 (f w)) := by
    have h1 : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝[sphere (c : ℂ) r] w) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall hps⟩
      rw [← hp0]
      exact (hpc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (hf w hw).tendsto.comp h1
  refine le_of_tendsto htend.norm ?_
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with θ hθ
  exact hb _ (hps θ) (hpim θ hθ)

/-- The reflection data of a mapping-out function `R` across `B(x, ρ/2) ∩ ℝ`. -/
structure IsRefl (R : ℂ → ℂ) (x ρ : ℝ) (G : ℂ → ℂ) : Prop where
  diff : DifferentiableOn ℂ G (ball (x : ℂ) (ρ / 2))
  eqOn : EqOn G R (ball (x : ℂ) (ρ / 2) ∩ H)
  symm : ∀ z ∈ ball (x : ℂ) (ρ / 2), G (conj z) = conj (G z)
  lip : ∀ z ∈ ball (x : ℂ) (ρ / 2), ‖G z - G x‖ ≤ 48 * ‖z - x‖
  injOn : InjOn G (ball (x : ℂ) (ρ / 2))
  real : ∀ z ∈ ball (x : ℂ) (ρ / 2), z.im = 0 → (G z).im = 0

theorem IsMapOut.exists_isRefl {E : Set ℂ} {g : ℂ → ℂ} (hE : IsHPHull E)
    (hg : IsMapOut E g) {x ρ : ℝ} (hρ : 0 < ρ) (hd : Disjoint (ball (x : ℂ) ρ) E) :
    ∃ G : ℂ → ℂ, IsRefl g x ρ G ∧ G x = limUnder (𝓝[H] (x : ℂ)) g := by
  obtain ⟨G, hd', hS, hc, hx, hl, hi, -, -, hr⟩ := IsMapOut.exists_reflection_full hE hg hρ hd
  exact ⟨G, ⟨hd', hS, hc, hl, hi, hr⟩, hx⟩

/-! ### Two times: the increment hulls and the composition identity -/

namespace ImageHyp

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T ρ : ℝ}

theorem isHPHull_L (h : ImageHyp W A φ T ρ) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hst : s ≤ t) :
    IsHPHull (gmap W s '' (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s)) :=
  (h.isMapOut_g hs).isHPHull_image (h.isHPHull_K hs) (h.isHPHull_K ht)
    (ConformalImage.ImageHyp.K_mono hst)

/-- `hcap(g_s(K_t \ K_s)) = 2 (t − s)`. -/
theorem hcapSet_L (h : ImageHyp W A φ T ρ) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hst : s ≤ t) :
    hcapSet (gmap W s '' (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s)) =
      2 * (t - s) := by
  rw [hcapSet_eq (isHPHull_L h hs ht hst)]
  have := HPHull.hcap_eq_add (A := ⟨_, h.isHPHull_K hs⟩) (B := ⟨_, h.isHPHull_K ht⟩)
    (ConformalImage.ImageHyp.K_mono hst) (h.isMapOut_g hs)
  have h1 := hcap_fwdHull h.continuous h.zero ht.1
  have h2 := hcap_fwdHull h.continuous h.zero hs.1
  linarith

/-- The image increment is `R_s(L)`. -/
theorem inc_eq (h : ImageHyp W A φ T ρ) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    inc (imageHull W φ) s t = mapOut (obstacle W A s) ''
      (gmap W s '' (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s)) :=
  h.image_inc_eq hs ht

/-- **Composition identity**: `R_t ∘ g_L = g_inc ∘ R_s` on `ℍ \ (E_s ∪ L)`. -/
theorem mapOut_comp_eq (h : ImageHyp W A φ T ρ) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) {w : ℂ}
    (hw : w ∈ H \ (obstacle W A s ∪
      gmap W s '' (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s))) :
    mapOut (obstacle W A t)
        (mapOut (gmap W s '' (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s)) w) =
      mapOut (inc (imageHull W φ) s t) (mapOut (obstacle W A s) w) := by
  set L := gmap W s '' (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s) with hL
  obtain ⟨z, hz, rfl⟩ := (h.isMapOut_g hs).1.2.surjOn hw.1
  have hzt : z ∉ QuantumZipper.fwdHull W t := fun hzt => hw.2 (Or.inr ⟨z, ⟨hzt, hz.2⟩, rfl⟩)
  have hzA : z ∉ A := fun hzA => hw.2 (Or.inl ⟨z, hzA, rfl⟩)
  have hzAK' : z ∈ H \ (A ∪ QuantumZipper.fwdHull W t) := ⟨hz.1, fun h' => h'.elim hzA hzt⟩
  have hzAK : z ∈ H \ (A ∪ QuantumZipper.fwdHull W s) := ⟨hz.1, fun h' => h'.elim hzA hz.2⟩
  have hcomp : IsMapOut (QuantumZipper.fwdHull W t) (mapOut L ∘ gmap W s) :=
    (h.isMapOut_g hs).comp (h.isHPHull_K hs) (h.isHPHull_K ht) (ConformalImage.ImageHyp.K_mono hst)
      (isMapOut_mapOut (isHPHull_L h hs ht hst))
  have hflow : gmap W t z = mapOut L (gmap W s z) :=
    (h.isMapOut_g ht).eqOn (h.isHPHull_K ht) hcomp ⟨hz.1, hzt⟩
  have hφz : φ z ∈ H \ imageHull W φ t := by
    refine ⟨h.isMapOut.1.2.mapsTo ⟨hz.1, hzA⟩, ?_⟩
    rintro ⟨z'', hz'', hzz⟩
    have := h.isMapOut.1.2.injOn ⟨(h.isHPHull_K ht).1 hz'', h.notMem_A_of_mem_K ht hz''⟩
      ⟨hz.1, hzA⟩ hzz
    exact hzt (this ▸ hz'')
  have hid1 := h.eqOn_comp ht hzAK'
  have hid2 := h.eqOn_mapOut_image hs ht hst hφz
  have hid3 := h.eqOn_comp hs hzAK
  simp only [Function.comp_apply] at hid1 hid2 hid3
  rw [← hflow, ← hid1, hid2, hid3]
/-- **The expansion on the circle** `|w − W_{s₁}| = ρ/32` (upper half) for two times
`s₁ ≤ s₂`: with `F`, `F̃` the reflections of `R_{s₁}`, `R_{s₂}`, `h = hcap L = 2(s₂ − s₁)`,
`h' = hcap(inc)`,
`|(F̃ − F)(w) − (h'/(F(w) − y₁) − F̃'(w) h/(w − x₁))|`
`≤ 12 ε' h'/d² + 96 · 12 ε h/r² + (768/ρ)(2h/r)²`.
-/
theorem norm_expansion_le (h : ImageHyp W A φ T ρ) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc 0 T)
    (hs₂ : s₂ ∈ Icc 0 T) (hss : s₁ ≤ s₂) {F G : ℂ → ℂ}
    (hFS : EqOn F (mapOut (obstacle W A s₁)) (ball (W s₁ : ℂ) (ρ / 2) ∩ H))
    (hGd : DifferentiableOn ℂ G (ball (W s₂ : ℂ) (ρ / 2)))
    (hGS : EqOn G (mapOut (obstacle W A s₂)) (ball (W s₂ : ℂ) (ρ / 2) ∩ H))
    (hGL : ∀ z ∈ ball (W s₂ : ℂ) (ρ / 2), ‖G z - G (W s₂)‖ ≤ 48 * ‖z - W s₂‖)
    {ε ε' d : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ / 384) (hx : |W s₂ - W s₁| ≤ ρ / 64)
    (hL : gmap W s₁ '' (QuantumZipper.fwdHull W s₂ \ QuantumZipper.fwdHull W s₁) ⊆
      closedBall (W s₁ : ℂ) ε)
    (hε' : 0 < ε') (hinc : inc (imageHull W φ) s₁ s₂ ⊆ closedBall (bdryDriver W A s₁ : ℂ) ε')
    (hd0 : 0 < d) (hd4 : 4 * ε' ≤ d) {w : ℂ} (hw : w ∈ sphere (W s₁ : ℂ) (ρ / 32))
    (hwH : 0 < w.im) (hdw : d ≤ ‖F w - bdryDriver W A s₁‖) :
    ‖(G w - F w) - ((hcapSet (inc (imageHull W φ) s₁ s₂) : ℂ) / (F w - bdryDriver W A s₁) -
        deriv G w * ((2 * (s₂ - s₁) : ℝ) : ℂ) / (w - W s₁))‖ ≤
      12 * ε' * hcapSet (inc (imageHull W φ) s₁ s₂) / d ^ 2 +
        96 * (12 * ε * (2 * (s₂ - s₁)) / (ρ / 32) ^ 2) +
          768 / ρ * (2 * (2 * (s₂ - s₁)) / (ρ / 32)) ^ 2 := by
  have hρ := h.pos
  set x₁ : ℂ := (W s₁ : ℂ) with hx₁
  set x₂ : ℂ := (W s₂ : ℂ) with hx₂
  set y₁ : ℂ := (bdryDriver W A s₁ : ℂ) with hy₁
  set r : ℝ := ρ / 32 with hr
  have hrpos : 0 < r := by positivity
  set hh : ℝ := 2 * (s₂ - s₁) with hhh
  have hh0 : 0 ≤ hh := by linarith
  set Ls := gmap W s₁ '' (QuantumZipper.fwdHull W s₂ \ QuantumZipper.fwdHull W s₁) with hLs
  have hLh : IsHPHull Ls := isHPHull_L h hs₁ hs₂ hss
  have hcapL : HPHull.hcap ⟨Ls, hLh⟩ = hh := by
    rw [← hcapSet_eq hLh]; exact hcapSet_L h hs₁ hs₂ hss
  set I := inc (imageHull W φ) s₁ s₂ with hI
  have hIh : IsHPHull I := h.isHPHull_inc hs₁ hs₂ hss
  set hh' := hcapSet I with hhh'
  have hcapI : HPHull.hcap ⟨I, hIh⟩ = hh' := (hcapSet_eq hIh).symm
  have hh'0 : 0 ≤ hh' := by rw [← hcapI]; exact HPHull.hcap_nonneg _
  have hgL := isMapOut_mapOut hLh
  have hgI := isMapOut_mapOut hIh
  have hwx : ‖w - x₁‖ = r := by rw [← dist_eq_norm]; exact hw
  have h4ε : 4 * ε ≤ ‖w - x₁‖ := by rw [hwx]; linarith
  -- Proposition 3.46 for `g_L`
  have hσ := hgL.norm_sub_sub_hcap_div_le hLh hε hL hwH h4ε
  rw [hcapL, hwx, ← hx₁] at hσ
  have hmove := hgL.norm_sub_le_of_four_mul_le hLh hε hL hwH h4ε
  set w₁ := mapOut Ls w with hw₁
  -- positions
  have hx12 : ‖x₁ - x₂‖ ≤ ρ / 64 := by
    rw [hx₁, hx₂, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hx
  have hwx₂ : ‖w - x₂‖ < ρ / 8 := by
    calc ‖w - x₂‖ ≤ ‖w - x₁‖ + ‖x₁ - x₂‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ρ / 8 := by rw [hwx]; linarith
  have hw₁x₂ : ‖w₁ - x₂‖ < ρ / 8 := by
    calc ‖w₁ - x₂‖ ≤ ‖w₁ - w‖ + ‖w - x₂‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ρ / 8 := by
        have : ‖w - x₂‖ ≤ ‖w - x₁‖ + ‖x₁ - x₂‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        rw [hwx] at this
        linarith
  have hwLs : w ∉ Ls := fun hwL => by
    have := hL hwL
    rw [mem_closedBall, dist_eq_norm, hwx] at this
    linarith
  have hw₁H : w₁ ∈ H := hgL.1.2.mapsTo ⟨hwH, hwLs⟩
  have hwB₁ : w ∈ ball x₁ (ρ / 2) := by
    rw [mem_ball, dist_eq_norm, hwx]; linarith
  have hwE : w ∉ obstacle W A s₁ := fun hwE =>
    Set.disjoint_left.1 (h.disjoint_ball_obstacle hs₁)
      (ball_subset_ball (by linarith) hwB₁) hwE
  -- the identity `G(w₁) = g_I(F w)`
  have hid : G w₁ = mapOut I (F w) := by
    rw [hGS ⟨by rw [mem_ball, dist_eq_norm]; linarith, hw₁H⟩, hFS ⟨hwB₁, hwH⟩]
    exact mapOut_comp_eq h hs₁ hs₂ hss ⟨hwH, fun h' => h'.elim hwE hwLs⟩
  -- Proposition 3.46 for `g_I`
  set v := F w with hv
  have hvH : v ∈ H := by
    rw [hv, hFS ⟨hwB₁, hwH⟩]
    exact (isMapOut_mapOut (h.isHPHull_obstacle hs₁)).1.2.mapsTo ⟨hwH, hwE⟩
  have hvy : 4 * ε' ≤ ‖v - y₁‖ := hd4.trans hdw
  have hσ' := hgI.norm_sub_sub_hcap_div_le hIh hε' hinc hvH hvy
  rw [hcapI, ← hy₁] at hσ'
  have hσ'' : 12 * ε' * hh' / ‖v - y₁‖ ^ 2 ≤ 12 * ε' * hh' / d ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hd0.le hdw 2
  -- Taylor for `G` on `ball x₂ (ρ/8)`
  have hM : ∀ z ∈ ball x₂ (ρ / 8), ‖deriv (deriv G) z‖ ≤ 768 / ρ := fun z hz =>
    norm_deriv_deriv_le hρ hGd hGL hz
  have hτ := norm_taylor_le (convex_ball _ _) isOpen_ball
    (hGd.mono (ball_subset_ball (by linarith))) hM
    (by rw [mem_ball, dist_eq_norm]; exact hwx₂) (by rw [mem_ball, dist_eq_norm]; exact hw₁x₂)
  have hG'w : ‖deriv G w‖ ≤ 96 :=
    norm_deriv_le_96 hρ hGd hGL (by rw [mem_ball, dist_eq_norm]; linarith)
  -- `|w₁ − w| ≤ 2h/r`
  have hw₁w : ‖w₁ - w‖ ≤ 2 * hh / r := by
    have h1 : ‖(hh : ℂ) / (w - x₁)‖ = hh / r := by
      rw [norm_div, hwx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh0]
    have h2 : ‖w₁ - w‖ ≤ ‖w₁ - w - (hh : ℂ) / (w - x₁)‖ + ‖(hh : ℂ) / (w - x₁)‖ := by
      have := norm_add_le (w₁ - w - (hh : ℂ) / (w - x₁)) ((hh : ℂ) / (w - x₁))
      rwa [sub_add_cancel] at this
    have h3 : 12 * ε * hh / r ^ 2 ≤ hh / r := by
      rw [div_le_div_iff₀ (by positivity) hrpos]
      have : 12 * ε ≤ r := by linarith
      nlinarith [mul_nonneg (mul_nonneg hh0 hrpos.le) (sub_nonneg.2 this)]
    have h4 : 2 * hh / r = hh / r + hh / r := by ring
    rw [h1] at h2
    linarith
  have hτ' : ‖G w₁ - G w - deriv G w * (w₁ - w)‖ ≤ 768 / ρ * (2 * hh / r) ^ 2 :=
    hτ.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw₁w 2)
      (by positivity))
  -- combine
  have hkey : (G w - v) - ((hh' : ℂ) / (v - y₁) - deriv G w * (hh : ℂ) / (w - x₁)) =
      (mapOut I v - v - (hh' : ℂ) / (v - y₁)) -
        deriv G w * (w₁ - w - (hh : ℂ) / (w - x₁)) -
          (G w₁ - G w - deriv G w * (w₁ - w)) := by
    rw [hid]; ring
  rw [hkey]
  have hb2 : ‖deriv G w * (w₁ - w - (hh : ℂ) / (w - x₁))‖ ≤ 96 * (12 * ε * hh / r ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul hG'w hσ (norm_nonneg _) (by norm_num)
  calc _ ≤ ‖mapOut I v - v - (hh' : ℂ) / (v - y₁)‖ +
        ‖deriv G w * (w₁ - w - (hh : ℂ) / (w - x₁))‖ +
          ‖G w₁ - G w - deriv G w * (w₁ - w)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ 12 * ε' * hh' / d ^ 2 + 96 * (12 * ε * hh / r ^ 2) + 768 / ρ * (2 * hh / r) ^ 2 := by
        gcongr
        exact hσ'.trans hσ''
/-- **The pair estimates**: for `s₁ ≤ s₂` close, with `F`, `G` the reflections of `R_{s₁}`,
`R_{s₂}`, `h = 2(s₂ − s₁)`, `h' = hcap(inc)`:
(1) `|h'/F'(x₁) − h G'(x₁)| ≤ r · err`; (2) `|G'(x₁) − F'(x₁)| ≤ (h'/d + 96 h/r + err)/r`. -/
theorem pair_estimates (h : ImageHyp W A φ T ρ) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc 0 T)
    (hs₂ : s₂ ∈ Icc 0 T) (hss : s₁ ≤ s₂) {F G : ℂ → ℂ}
    (hF : IsRefl (mapOut (obstacle W A s₁)) (W s₁) ρ F) (hFx : F (W s₁) = bdryDriver W A s₁)
    (hG : IsRefl (mapOut (obstacle W A s₂)) (W s₂) ρ G)
    {ε ε' d : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ / 384) (hx : |W s₂ - W s₁| ≤ ρ / 64)
    (hL : gmap W s₁ '' (QuantumZipper.fwdHull W s₂ \ QuantumZipper.fwdHull W s₁) ⊆
      closedBall (W s₁ : ℂ) ε)
    (hε' : 0 < ε') (hinc : inc (imageHull W φ) s₁ s₂ ⊆ closedBall (bdryDriver W A s₁ : ℂ) ε')
    (hd0 : 0 < d) (hd4 : 4 * ε' ≤ d)
    (hdw : ∀ w ∈ sphere (W s₁ : ℂ) (ρ / 32), 0 < w.im → d ≤ ‖F w - bdryDriver W A s₁‖) :
    ‖(hcapSet (inc (imageHull W φ) s₁ s₂) : ℂ) / deriv F (W s₁) -
        ((2 * (s₂ - s₁) : ℝ) : ℂ) * deriv G (W s₁)‖ ≤
      ρ / 32 * (12 * ε' * hcapSet (inc (imageHull W φ) s₁ s₂) / d ^ 2 +
        96 * (12 * ε * (2 * (s₂ - s₁)) / (ρ / 32) ^ 2) +
          768 / ρ * (2 * (2 * (s₂ - s₁)) / (ρ / 32)) ^ 2) ∧
    ‖deriv G (W s₁) - deriv F (W s₁)‖ ≤
      (hcapSet (inc (imageHull W φ) s₁ s₂) / d + 96 * (2 * (s₂ - s₁)) / (ρ / 32) +
        (12 * ε' * hcapSet (inc (imageHull W φ) s₁ s₂) / d ^ 2 +
          96 * (12 * ε * (2 * (s₂ - s₁)) / (ρ / 32) ^ 2) +
            768 / ρ * (2 * (2 * (s₂ - s₁)) / (ρ / 32)) ^ 2)) / (ρ / 32) := by
  have hρ := h.pos
  set r : ℝ := ρ / 32 with hr
  have hrpos : 0 < r := by positivity
  set hh : ℝ := 2 * (s₂ - s₁) with hhh
  have hh0 : 0 ≤ hh := by linarith
  set hh' := hcapSet (inc (imageHull W φ) s₁ s₂) with hhh'
  have hh'0 : 0 ≤ hh' := by
    rw [hhh', hcapSet_eq (h.isHPHull_inc hs₁ hs₂ hss)]; exact HPHull.hcap_nonneg _
  set err := 12 * ε' * hh' / d ^ 2 + 96 * (12 * ε * hh / r ^ 2) + 768 / ρ * (2 * hh / r) ^ 2
    with herr
  set x₁ : ℂ := (W s₁ : ℂ) with hx₁
  set y₁ : ℂ := (bdryDriver W A s₁ : ℂ) with hy₁
  have hx12 : ‖x₁ - (W s₂ : ℂ)‖ ≤ ρ / 64 := by
    rw [hx₁, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hx
  -- membership facts for points of the closed disc `B̄(x₁, r)`
  have hB1 : ∀ w, ‖w - x₁‖ ≤ r → w ∈ ball x₁ (ρ / 2) := fun w hw => by
    rw [mem_ball, dist_eq_norm]; linarith
  have hB2 : ∀ w, ‖w - x₁‖ ≤ r → ‖w - W s₂‖ < ρ / 8 := fun w hw => by
    calc ‖w - W s₂‖ ≤ ‖w - x₁‖ + ‖x₁ - W s₂‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ρ / 8 := by linarith
  have hB2' : ∀ w, ‖w - x₁‖ ≤ r → w ∈ ball (W s₂ : ℂ) (ρ / 2) := fun w hw => by
    rw [mem_ball, dist_eq_norm]; linarith [hB2 w hw]
  have hsph : ∀ w ∈ sphere x₁ r, ‖w - x₁‖ = r := fun w hw => by rw [← dist_eq_norm]; exact hw
  have hsph' : ∀ w ∈ sphere x₁ r, conj w ∈ sphere x₁ r := fun w hw => by
    rw [mem_sphere, dist_eq_norm, show conj w - x₁ = conj (w - x₁) by
      simp [hx₁, map_sub, Complex.conj_ofReal], Complex.norm_conj, ← dist_eq_norm]
    exact hw
  have hFne : ∀ w ∈ sphere x₁ r, F w - y₁ ≠ 0 := fun w hw h0 => by
    have hw1 := hB1 w (hsph w hw).le
    have hx1 : x₁ ∈ ball x₁ (ρ / 2) := mem_ball_self (by positivity)
    have := hF.injOn hw1 hx1 (by rw [hFx]; exact sub_eq_zero.1 h0)
    have := hsph w hw
    rw [‹w = x₁›, sub_self, norm_zero] at this
    linarith
  have hFsymm : ∀ w ∈ sphere x₁ r, ‖F w - y₁‖ = ‖F (conj w) - y₁‖ := fun w hw => by
    rw [hF.symm w (hB1 w (hsph w hw).le), show conj (F w) - y₁ = conj (F w - y₁) by
      simp [hy₁, map_sub, Complex.conj_ofReal], Complex.norm_conj]
  have hdall : ∀ w ∈ sphere x₁ r, w.im ≠ 0 → d ≤ ‖F w - y₁‖ := fun w hw hw0 => by
    rcases lt_or_gt_of_ne hw0 with hneg | hpos
    · rw [hFsymm w hw]
      exact hdw _ (hsph' w hw) (by simp; linarith)
    · exact hdw w hw hpos
  -- the expression on the circle
  set E : ℂ → ℂ := fun w => (G w - F w) -
    ((hh' : ℂ) / (F w - y₁) - deriv G w * (hh : ℂ) / (w - x₁)) with hE
  have hEup : ∀ w ∈ sphere x₁ r, 0 < w.im → ‖E w‖ ≤ err := fun w hw hwH =>
    norm_expansion_le h hs₁ hs₂ hss hF.eqOn hG.diff hG.eqOn hG.lip hε hερ hx hL hε' hinc hd0
      hd4 hw hwH (hdw w hw hwH)
  have hEconj : ∀ w ∈ sphere x₁ r, E (conj w) = conj (E w) := fun w hw => by
    have h1 := hG.symm w (hB2' w (hsph w hw).le)
    have h2 := hF.symm w (hB1 w (hsph w hw).le)
    have h3 := deriv_conj_eq hG.diff hG.symm (hB2' w (hsph w hw).le)
    simp only [hE, h1, h2, h3, map_sub, map_div₀, map_mul, Complex.conj_ofReal, hy₁, hx₁]
  have hEnr : ∀ w ∈ sphere x₁ r, w.im ≠ 0 → ‖E w‖ ≤ err := fun w hw hw0 => by
    rcases lt_or_gt_of_ne hw0 with hneg | hpos
    · have := hEup (conj w) (hsph' w hw) (by simp; linarith)
      rwa [hEconj w hw, Complex.norm_conj] at this
    · exact hEup w hw hpos
  -- continuity on the circle
  have hsubB1 : sphere x₁ r ⊆ ball x₁ (ρ / 2) := fun w hw => hB1 w (hsph w hw).le
  have hsubB2 : sphere x₁ r ⊆ ball (W s₂ : ℂ) (ρ / 2) := fun w hw => hB2' w (hsph w hw).le
  have hG'c : ContinuousOn (deriv G) (ball (W s₂ : ℂ) (ρ / 2)) :=
    (hG.diff.analyticOnNhd isOpen_ball).deriv.continuousOn
  have hDc : ContinuousOn (fun w => G w - F w) (sphere x₁ r) :=
    (hG.diff.continuousOn.mono hsubB2).sub (hF.diff.continuousOn.mono hsubB1)
  have hEc : ContinuousOn E (sphere x₁ r) := by
    refine hDc.sub ((continuousOn_const.div ((hF.diff.continuousOn.mono hsubB1).sub
      continuousOn_const) hFne).sub (((hG'c.mono hsubB2).mul continuousOn_const).div
        (continuousOn_id.sub continuousOn_const) fun w hw => ?_))
    rw [sub_ne_zero]; rintro rfl; have := hsph _ hw; simp at this; linarith
  have hEall := norm_le_of_sphere_im_ne hrpos hEc hEnr
  -- (1): the circle integral
  have hF16 : DifferentiableOn ℂ F (ball x₁ (ρ / 16)) :=
    hF.diff.mono (ball_subset_ball (by linarith))
  have hG16 : DifferentiableOn ℂ G (ball x₁ (ρ / 16)) := hG.diff.mono fun w hw => by
    rw [mem_ball, dist_eq_norm] at hw ⊢
    calc ‖w - W s₂‖ ≤ ‖w - x₁‖ + ‖x₁ - W s₂‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ρ / 2 := by linarith
  have hx1B : x₁ ∈ ball x₁ (ρ / 2) := mem_ball_self (by positivity)
  have hne : ∀ w ∈ closedBall x₁ r, w ≠ x₁ → F w ≠ y₁ := fun w hw hwx hFw => by
    rw [mem_closedBall, dist_eq_norm] at hw
    exact hwx (hF.injOn (hB1 w hw) hx1B (by rw [hFw, hFx]))
  have hdF : deriv F x₁ ≠ 0 :=
    QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hF.diff hF.injOn hx1B
  have P1 := norm_div_deriv_sub_mul_deriv_le (h := (hh : ℂ)) (h' := (hh' : ℂ)) hrpos
    (show r < ρ / 16 by linarith) hF16 hG16 hFx hne hdF hEall
  refine ⟨P1, ?_⟩
  -- (2): Cauchy's estimate for `G − F`
  have hDbound : ∀ w ∈ sphere x₁ r, ‖G w - F w‖ ≤ hh' / d + 96 * hh / r + err := by
    refine norm_le_of_sphere_im_ne hrpos hDc fun w hw hw0 => ?_
    have h1 : ‖(hh' : ℂ) / (F w - y₁)‖ ≤ hh' / d := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh'0]
      exact div_le_div_of_nonneg_left hh'0 hd0 (hdall w hw hw0)
    have h2 : ‖deriv G w * (hh : ℂ) / (w - x₁)‖ ≤ 96 * hh / r := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh0, hsph w hw]
      have := norm_deriv_le_96 hρ hG.diff hG.lip (show w ∈ ball (W s₂ : ℂ) (ρ / 4) by
        rw [mem_ball, dist_eq_norm]; linarith [hB2 w (hsph w hw).le])
      gcongr
    have h3 : G w - F w = E w + ((hh' : ℂ) / (F w - y₁) - deriv G w * (hh : ℂ) / (w - x₁)) := by
      simp only [hE]; ring
    rw [h3]
    calc _ ≤ ‖E w‖ + (‖(hh' : ℂ) / (F w - y₁)‖ + ‖deriv G w * (hh : ℂ) / (w - x₁)‖) :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ err + (hh' / d + 96 * hh / r) := by gcongr; exact hEall w hw
      _ = hh' / d + 96 * hh / r + err := by ring
  have hDd : DiffContOnCl ℂ (fun w => G w - F w) (ball x₁ r) :=
    diffContOnCl_of_subset hrpos (hG16.sub hF16) (closedBall_subset_ball (by linarith))
  have P2 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hDd hDbound
  have hderiv : deriv (fun w => G w - F w) x₁ = deriv G x₁ - deriv F x₁ :=
    deriv_sub (hG16.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity))))
      (hF16.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity))))
  rw [hderiv] at P2
  exact P2

end ImageHyp

end ConformalImageFull

end InteractingSLE
