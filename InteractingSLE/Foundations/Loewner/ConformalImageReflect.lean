import InteractingSLE.Foundations.Loewner.ConformalImageUnion
import QuantumZipper.Proofs.Complex.KoebeCovering
import QuantumZipper.Proofs.Complex.BasicsReflection
import Mathlib.Topology.ExtendFrom

/-!
# Mapping-out functions near real points away from the hull

Packet GEO-LOC (`planning/INFRA-GEO.md` §4), second layer. Let `g` map out a compact `ℍ`-hull
`E`, and let `y ∈ ℝ` with `B(y, ρ) ∩ E = ∅`.

* `IsMapOut.norm_deriv_le_of_disjoint`: `|g'(w)| ≤ 48` at every `w ∈ ℍ` with `B(w, Im w) ∩ E = ∅`.
  (Koebe's covering theorem, QuantumZipper's non-sharp `1/48` form, on `B(w, Im w)`: the image
  contains `B(g w, |g'(w)| Im w / 48)` and lies in `ℍ`, so `|g'(w)| Im w / 48 ≤ Im g(w) ≤ Im w`.)
* `IsMapOut.lipschitz_of_disjoint`: `g` is `48`-Lipschitz on `B(y, ρ/2) ∩ ℍ`.
* `IsMapOut.exists_tendsto_of_disjoint`: `g` has a real limit at every point of
  `B(y, ρ/2) ∩ ℝ`, and `|g(w) − g(y)| ≤ 48 |w − y|` for the limit value.
* `IsMapOut.exists_reflection`: **Schwarz reflection** — `g` extends to a holomorphic function on
  `B(y, ρ/2)` commuting with `conj` (QuantumZipper's `CA.exists_reflection_extension`).

These are the "maps extend analytically by reflection through all real neighborhoods needed"
of Specification Aux. lemma 8, proof (L329), and the locally real property of [Law05] §4.6.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

/-- A ball around a point of `ℍ` that lies in `ℍ` has radius at most the imaginary part. -/
theorem le_im_of_ball_subset_H {p : ℂ} {s : ℝ} (hp : p ∈ H) (h : ball p s ⊆ H) : s ≤ p.im := by
  by_contra hlt
  rw [not_le] at hlt
  have hmem : (p.re : ℂ) ∈ ball p s := by
    rw [mem_ball, dist_eq_norm]
    have : (p.re : ℂ) - p = -(p.im * I) := by
      apply Complex.ext <;> simp
    rw [this, norm_neg, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp]
    exact hlt
  have := h hmem
  simp [QuantumZipper.H] at this

theorem ball_im_subset_H {w : ℂ} : ball w w.im ⊆ H := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz
  show 0 < z.im
  have h1 : |(z - w).im| ≤ ‖z - w‖ := abs_im_le_norm _
  rw [sub_im] at h1
  have := neg_abs_le (z.im - w.im)
  linarith

/-- **Derivative bound for mapping-out functions** (Koebe covering on `B(w, Im w)`):
`|g'(w)| ≤ 48` whenever `B(w, Im w)` avoids the hull. -/
theorem IsMapOut.norm_deriv_le_of_disjoint {E : Set ℂ} {g : ℂ → ℂ} (hE : IsHPHull E)
    (hg : IsMapOut E g) {w : ℂ} (hw : w ∈ H) (hd : Disjoint (ball w w.im) E) :
    ‖deriv g w‖ ≤ 48 := by
  have hsub : ball w w.im ⊆ H \ E := fun z hz =>
    ⟨ball_im_subset_H hz, fun h => Set.disjoint_left.1 hd hz h⟩
  have hdiff : DifferentiableOn ℂ g (ball w w.im) := hg.1.1.mono hsub
  have hinj : InjOn g (ball w w.im) := hg.1.2.injOn.mono hsub
  have hcov := QuantumZipper.CA.Koebe.ball_subset_image_koebe hdiff hinj
  have hgw : g w ∈ H := hg.1.2.mapsTo (hsub (mem_ball_self hw))
  have himg : g '' ball w w.im ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact hg.1.2.mapsTo (hsub hz)
  have h1 := le_im_of_ball_subset_H hgw (hcov.trans himg)
  have h2 := hg.im_le hE (hsub (mem_ball_self hw))
  have hwpos : 0 < w.im := hw
  rw [QuantumZipper.CA.Koebe.koebeCovConst] at h1
  have h3 : 1 / 48 * w.im * ‖deriv g w‖ ≤ w.im := h1.trans h2
  nlinarith [norm_nonneg (deriv g w)]

/-- The half-ball `B(y, r) ∩ ℍ` is convex. -/
theorem convex_ball_inter_H (c : ℂ) (r : ℝ) : Convex ℝ (ball c r ∩ H) := by
  refine (convex_ball c r).inter ?_
  have : H = {z : ℂ | 0 < Complex.imLm z} := rfl
  rw [this]
  exact convex_halfSpace_gt Complex.imLm.isLinear 0

/-- If `B(y, ρ)` avoids the hull, every `w ∈ B(y, ρ/2) ∩ ℍ` has `B(w, Im w) ⊆ B(y, ρ)`. -/
theorem ball_im_subset_ball {y w : ℂ} {ρ : ℝ} (hy : y.im = 0) (hw : w ∈ ball y (ρ / 2) ∩ H) :
    ball w w.im ⊆ ball y ρ := by
  intro z hz
  rw [mem_ball] at hz ⊢
  have h1 : dist w y < ρ / 2 := hw.1
  have h2 : w.im ≤ dist w y := by
    rw [dist_eq_norm]
    calc w.im = (w - y).im := by simp [hy]
      _ ≤ |(w - y).im| := le_abs_self _
      _ ≤ ‖w - y‖ := abs_im_le_norm _
  calc dist z y ≤ dist z w + dist w y := dist_triangle _ _ _
    _ < w.im + dist w y := by linarith
    _ ≤ ρ := by linarith

/-- **Lipschitz bound near real points**: if `B(y, ρ)` (`y ∈ ℝ`) avoids the hull, the mapping-out
function is `48`-Lipschitz on `B(y, ρ/2) ∩ ℍ`. -/
theorem IsMapOut.norm_sub_le_of_disjoint {E : Set ℂ} {g : ℂ → ℂ} (hE : IsHPHull E)
    (hg : IsMapOut E g) {y : ℝ} {ρ : ℝ} (hd : Disjoint (ball (y : ℂ) ρ) E) {w₁ w₂ : ℂ}
    (hw₁ : w₁ ∈ ball (y : ℂ) (ρ / 2) ∩ H) (hw₂ : w₂ ∈ ball (y : ℂ) (ρ / 2) ∩ H) :
    ‖g w₂ - g w₁‖ ≤ 48 * ‖w₂ - w₁‖ := by
  have hsub : ∀ w ∈ ball (y : ℂ) (ρ / 2) ∩ H, ball w w.im ⊆ ball (y : ℂ) ρ := fun w hw =>
    ball_im_subset_ball (by simp) hw
  refine Convex.norm_image_sub_le_of_norm_deriv_le (fun w hw => ?_) (fun w hw => ?_)
    (convex_ball_inter_H _ _) hw₁ hw₂
  · have hwE : w ∈ H \ E := ⟨hw.2, fun h => Set.disjoint_left.1 hd
      (hsub w hw (mem_ball_self hw.2)) h⟩
    exact hg.1.1.differentiableAt (hE.isOpen.mem_nhds hwE)
  · exact hg.norm_deriv_le_of_disjoint hE hw.2 (hd.mono_left (hsub w hw))


theorem ball_half_inter_H_subset {E : Set ℂ} {y : ℝ} {ρ : ℝ} (hd : Disjoint (ball (y : ℂ) ρ) E) :
    ball (y : ℂ) (ρ / 2) ∩ H ⊆ H \ E := by
  intro w hw
  refine ⟨hw.2, fun h => Set.disjoint_left.1 hd ?_ h⟩
  have h1 := mem_ball.1 hw.1
  have h0 := dist_nonneg (x := w) (y := (y : ℂ))
  rw [mem_ball]
  linarith

/-- Points of the closed upper half-ball are limits of points of the open upper half-ball. -/
theorem subset_closure_ball_inter_H (c : ℂ) (r : ℝ) :
    ball c r ∩ Hbar ⊆ closure (ball c r ∩ H) := by
  rintro x ⟨hxb, hx⟩
  have hx0 : 0 ≤ x.im := hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hδ : 0 < r - dist x c := sub_pos.2 (mem_ball.1 hxb)
  set η := min ε (r - dist x c) / 2 with hη
  have hηpos : 0 < η := by positivity
  have hηε : η < ε := by
    have := min_le_left ε (r - dist x c); linarith
  have hηr : η < r - dist x c := by
    have := min_le_right ε (r - dist x c); linarith
  have hd : dist x (x + η * I) = η := by
    rw [dist_eq_norm, show x - (x + η * I) = -(η * I) by ring, norm_neg, norm_mul, norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
  refine ⟨x + η * I, ⟨?_, ?_⟩, by rw [hd]; exact hηε⟩
  · rw [mem_ball]
    calc dist (x + η * I) c ≤ dist (x + η * I) x + dist x c := dist_triangle _ _ _
      _ = η + dist x c := by rw [dist_comm, hd]
      _ < r := by linarith
  · show 0 < (x + η * I).im
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith

/-- **Boundary values near real points**: if `B(y, ρ)` (`y ∈ ℝ`) avoids the hull, the mapping-out
function has a real limit at every real point of `B(y, ρ/2)`. -/
theorem IsMapOut.exists_tendsto_of_disjoint {E : Set ℂ} {g : ℂ → ℂ} (hE : IsHPHull E)
    (hg : IsMapOut E g) {y : ℝ} {ρ : ℝ} (hd : Disjoint (ball (y : ℂ) ρ) E) {x : ℂ}
    (hx : x ∈ ball (y : ℂ) (ρ / 2)) (hx0 : x.im = 0) :
    ∃ L : ℂ, L.im = 0 ∧ Tendsto g (𝓝[ball (y : ℂ) (ρ / 2) ∩ H] x) (𝓝 L) := by
  set S := ball (y : ℂ) (ρ / 2) ∩ H with hS
  have hxS : x ∈ closure S :=
    subset_closure_ball_inter_H _ _ ⟨hx, show 0 ≤ x.im from hx0.ge⟩
  have : (𝓝[S] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxS
  have hSE : S ⊆ H \ E := ball_half_inter_H_subset hd
  have hcauchy : Cauchy (map g (𝓝[S] x)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ⟨g '' (S ∩ ball x (ε / 100)), ?_, ?_⟩⟩
    · exact image_mem_map (inter_mem_nhdsWithin S (ball_mem_nhds x (by positivity)))
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have h := hg.norm_sub_le_of_disjoint hE hd ha.1 hb.1
      rw [dist_eq_norm, ← norm_neg, neg_sub]
      have hab : ‖b - a‖ < ε / 50 := by
        have h1 := mem_ball.1 ha.2
        have h2 := mem_ball.1 hb.2
        rw [← dist_eq_norm]
        calc dist b a ≤ dist b x + dist a x := dist_triangle_right _ _ _
          _ < ε / 100 + ε / 100 := add_lt_add h2 h1
          _ = ε / 50 := by ring
      calc ‖g b - g a‖ ≤ 48 * ‖b - a‖ := h
        _ < 48 * (ε / 50) := by linarith
        _ < ε := by linarith
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hcauchy
  refine ⟨L, ?_, hL⟩
  have him : Tendsto (fun z => (g z).im) (𝓝[S] x) (𝓝 0) :=
    (hg.tendsto_im_nhdsWithin hE (fun h => by
      have : (0 : ℝ) < x.im := h.1
      linarith)).mono_left (nhdsWithin_mono _ hSE)
  exact tendsto_nhds_unique ((continuous_im.tendsto L).comp hL) him

/-- **Schwarz reflection for mapping-out functions** (Specification Aux. lemma 8, proof, L329;
[Law05] §4.6 "locally real"): if `B(y, ρ)` (`y ∈ ℝ`) avoids the hull, the mapping-out function
extends to a holomorphic `G` on `B(y, ρ/2)` with `G(z̄) = conj G(z)`, real on the real diameter and
`48`-Lipschitz on the closed upper half-ball. -/
theorem IsMapOut.exists_reflection {E : Set ℂ} {g : ℂ → ℂ} (hE : IsHPHull E) (hg : IsMapOut E g)
    {y : ℝ} {ρ : ℝ} (hd : Disjoint (ball (y : ℂ) ρ) E) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (y : ℂ) (ρ / 2)) ∧
      EqOn G g (ball (y : ℂ) (ρ / 2) ∩ H) ∧
      (∀ z ∈ ball (y : ℂ) (ρ / 2), G (conj z) = conj (G z)) ∧
      (∀ z ∈ ball (y : ℂ) (ρ / 2), z.im = 0 → (G z).im = 0) ∧
      (∀ z ∈ ball (y : ℂ) (ρ / 2) ∩ Hbar, ∀ w ∈ ball (y : ℂ) (ρ / 2) ∩ Hbar,
        ‖G w - G z‖ ≤ 48 * ‖w - z‖) ∧
      (∀ z ∈ ball (y : ℂ) (ρ / 2), z.im = 0 →
        Tendsto g (𝓝[ball (y : ℂ) (ρ / 2) ∩ H] z) (𝓝 (G z))) := by
  set S := ball (y : ℂ) (ρ / 2) ∩ H with hS
  have hSE : S ⊆ H \ E := ball_half_inter_H_subset hd
  have hSo : IsOpen S := isOpen_ball.inter QuantumZipper.isOpen_H
  have hgc : ContinuousOn g S := (hg.1.1.mono hSE).continuousOn
  set g' := extendFrom S g with hg'
  have hext : ∀ w ∈ S, g' w = g w := extendFrom_extends hgc
  have hlim : ∀ z ∈ ball (y : ℂ) (ρ / 2) ∩ Hbar, ∃ L, Tendsto g (𝓝[S] z) (𝓝 L) := by
    rintro z ⟨hzb, hz⟩
    rcases (show 0 ≤ z.im from hz).lt_or_eq with hpos | hzero
    · exact ⟨g z, (hgc z ⟨hzb, hpos⟩).tendsto⟩
    · obtain ⟨L, -, hL⟩ := hg.exists_tendsto_of_disjoint hE hd hzb hzero.symm
      exact ⟨L, hL⟩
  have hc : ContinuousOn g' (Hbar ∩ ball (y : ℂ) (ρ / 2)) := by
    refine continuousOn_extendFrom (fun z hz => ?_) (fun z hz => hlim z ⟨hz.2, hz.1⟩)
    exact subset_closure_ball_inter_H _ _ ⟨hz.2, hz.1⟩
  have hdiff : DifferentiableOn ℂ g' (H ∩ ball (y : ℂ) (ρ / 2)) := by
    have h1 : DifferentiableOn ℂ g' S := (hg.1.1.mono hSE).congr fun w hw => hext w hw
    rw [inter_comm]
    exact h1
  have hreal : ∀ z ∈ ball (y : ℂ) (ρ / 2), z.im = 0 → (g' z).im = 0 := by
    intro z hz hz0
    obtain ⟨L, hL0, hL⟩ := hg.exists_tendsto_of_disjoint hE hd hz hz0
    have hxS : z ∈ closure S := subset_closure_ball_inter_H _ _ ⟨hz, show 0 ≤ z.im from hz0.ge⟩
    have : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxS
    have := tendsto_nhds_unique (tendsto_extendFrom ⟨L, hL⟩) hL
    rw [← hg'] at this
    rw [this]; exact hL0
  obtain ⟨G, hGd, hGeq, hGsymm⟩ :=
    QuantumZipper.CA.exists_reflection_extension (x := y) (r := ρ / 2) hdiff hc hreal
  have hGS : EqOn G g S := fun w hw => by
    rw [hGeq ⟨show 0 ≤ w.im from hw.2.le, hw.1⟩, hext w hw]
  refine ⟨G, hGd, hGS, hGsymm, fun z hz hz0 => ?_, ?_, fun z hz hz0 => ?_⟩
  · rw [hGeq ⟨show 0 ≤ z.im from hz0.ge, hz⟩]; exact hreal z hz hz0
  · -- Lipschitz on the closed upper half-ball, by continuity from the open one
    intro z hz w hw
    have hGc : ContinuousOn G (ball (y : ℂ) (ρ / 2)) := hGd.continuousOn
    have hshift : ∀ u ∈ ball (y : ℂ) (ρ / 2) ∩ Hbar,
        ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), u + (η : ℂ) * I ∈ S := by
      rintro u ⟨hub, hu⟩
      have hu0 : 0 ≤ u.im := hu
      have hball : ∀ᶠ η : ℝ in 𝓝 (0 : ℝ), u + (η : ℂ) * I ∈ ball (y : ℂ) (ρ / 2) := by
        have hc : Continuous fun η : ℝ => u + (η : ℂ) * I := by fun_prop
        have := hc.tendsto 0
        simp only [ofReal_zero, zero_mul, add_zero] at this
        exact this.eventually_mem (isOpen_ball.mem_nhds hub)
      filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with η h1 h2
      refine ⟨h1, ?_⟩
      show 0 < (u + η * I).im
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      have : (0 : ℝ) < η := h2
      linarith
    have hT : ∀ u ∈ ball (y : ℂ) (ρ / 2) ∩ Hbar,
        Tendsto (fun η : ℝ => G (u + (η : ℂ) * I)) (𝓝[>] 0) (𝓝 (G u)) := by
      intro u hu
      have hc : Tendsto (fun η : ℝ => u + (η : ℂ) * I) (𝓝[>] (0 : ℝ)) (𝓝 u) := by
        have : Continuous fun η : ℝ => u + (η : ℂ) * I := by fun_prop
        have h := this.tendsto 0
        simp only [ofReal_zero, zero_mul, add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact (hGc u hu.1).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hc, by
        filter_upwards [hshift u hu] with η hη using hη.1⟩)
    refine le_of_tendsto ((continuous_norm.tendsto _).comp ((hT w hw).sub (hT z hz))) ?_
    filter_upwards [hshift z hz, hshift w hw] with η hz' hw'
    simp only [Function.comp_apply]
    rw [hGS hz', hGS hw']
    have := hg.norm_sub_le_of_disjoint hE hd hz' hw'
    simpa [add_sub_add_right_eq_sub] using this
  · obtain ⟨L, -, hL⟩ := hg.exists_tendsto_of_disjoint hE hd hz hz0
    have hxS : z ∈ closure S := subset_closure_ball_inter_H _ _ ⟨hz, show 0 ≤ z.im from hz0.ge⟩
    have : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxS
    have h1 := tendsto_nhds_unique (tendsto_extendFrom ⟨L, hL⟩) hL
    rw [hGeq ⟨show 0 ≤ z.im from hz0.ge, hz⟩]
    have h2 : g' z = L := h1
    rw [h2]
    exact hL

end InteractingSLE
