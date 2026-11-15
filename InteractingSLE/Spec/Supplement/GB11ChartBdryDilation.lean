/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3LawChart
import InteractingSLE.Foundations.PrimeEnd.Basic

/-!
# Lemma GB11's pocket charts: a component chart is a dilated Jordan coordinate

Packet PROVE-T14-GW4T5, item (1a), analytic part. Let `ψ : C → ℍ` be a conformal bijection whose inverse extends to
a continuous injective `G` on `ℍ̄` (a Jordan coordinate) with `G(0) = P` the exit, the real line going into the two open
boundary arcs `A \ B` (on the right wall `R`, off `L`) and `B \ A` (on `L`, off `R`), and `G` tending at `∞` to a filter
disjoint from `𝓝 P` (the entry). Then every component chart `c` of `C` (frozen `IsComponentChart`: boundary limits on
`R` at positive and on `L` at negative points) with exit limit `P` at `0` is `c⁻¹(w) = G(k w)` for some `k > 0`, and `G`
sends the positive half-line into `A \ B` and the negative one into `B \ A`.

## The argument

`ψ ∘ c⁻¹` is a conformal automorphism of `ℍ`, a real Möbius map `N(w) = (a w + b)/(c w + d)` with `ad − bc > 0`, and
`c⁻¹ = G ∘ N` on `ℍ`; at a real point `x` off the pole the boundary limit of `c⁻¹` is `G(N x)`. At `0` this limit is
`P = G(0)`, so `N(0) = 0`: `b = 0` (a pole at `0` would send `c⁻¹` to the entry). Each half-line goes by `G` into one of
the two open arcs (`G` is continuous, `A \ B` and `B \ A` are separated by the closed sets `A`, `B`). If `c ≠ 0`
the pole `x* = −d/c ≠ 0` makes `N` change sign on one side of `0`, so some boundary limit of `c⁻¹` at a positive point
lies on the arc of `L`, or at a negative point on the arc of `R` — impossible. So `N(w) = (a/d) w`.

## Main results

* `forall_mem_of_isPreconnected` (a half-line goes into one arc);
* **`exists_dilation_of_extInv`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Theorem14

namespace GB11Chart

theorem ofReal_mem_Hbar (r : ℝ) : (r : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (r : ℂ).im by simp

theorem H_subset_Hbar : H ⊆ Hbar := fun _ hz => le_of_lt (show (0 : ℝ) < _ from hz)

/-- `0 < u / q ↔ 0 < u q` for `q ≠ 0`. -/
theorem div_pos_iff_mul_pos {u q : ℝ} (hq : q ≠ 0) : 0 < u / q ↔ 0 < u * q := by
  have h : u / q = (u * q) / (q * q) := by field_simp
  rw [h, div_pos_iff_of_pos_right (mul_self_pos.2 hq)]

/-- `u / q < 0 ↔ u q < 0` for `q ≠ 0`. -/
theorem div_neg_iff_mul_neg {u q : ℝ} (hq : q ≠ 0) : u / q < 0 ↔ u * q < 0 := by
  have h := div_pos_iff_mul_pos (u := -u) hq
  rw [neg_div, neg_mul, neg_pos, neg_pos] at h
  exact h

/-- **A half-line goes into one arc.** If `G` is continuous on `ℍ̄` and sends a preconnected set `S ⊆ ℝ` into
`(A \ B) ∪ (B \ A)` (`A`, `B` closed), then as soon as one point goes into `A \ B` (resp. `B \ A`), all do. -/
theorem forall_mem_of_isPreconnected {G : ℂ → ℂ} (hGc : ContinuousOn G Hbar) {A B : Set ℂ} (hA : IsClosed A)
    (hB : IsClosed B) {S : Set ℝ} (hS : IsPreconnected S) (hGr : ∀ r ∈ S, G r ∈ (A \ B) ∪ (B \ A)) {r₀ : ℝ}
    (hr₀ : r₀ ∈ S) :
    (G r₀ ∈ A \ B → ∀ r ∈ S, G r ∈ A \ B) ∧ (G r₀ ∈ B \ A → ∀ r ∈ S, G r ∈ B \ A) := by
  have hT : IsPreconnected ((fun r : ℝ => G r) '' S) :=
    hS.image _ (hGc.comp Complex.continuous_ofReal.continuousOn fun r _ => ofReal_mem_Hbar r)
  have hsplit := isPreconnected_iff_subset_of_disjoint.1 hT Bᶜ Aᶜ hB.isOpen_compl hA.isOpen_compl
    (by
      rintro _ ⟨r, hr, rfl⟩
      rcases hGr r hr with h | h
      exacts [Or.inl h.2, Or.inr h.2])
    (by
      ext z
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]
      rintro ⟨r, hr, rfl⟩ hzB
      rcases hGr r hr with h | h
      exacts [h.1, absurd h.1 hzB])
  constructor
  · intro h₀ r hr
    rcases hsplit with hs | hs
    · rcases hGr r hr with h | h
      exacts [h, absurd h.1 (hs ⟨r, hr, rfl⟩)]
    · exact absurd h₀.1 (hs ⟨r₀, hr₀, rfl⟩)
  · intro h₀ r hr
    rcases hsplit with hs | hs
    · exact absurd h₀.1 (hs ⟨r₀, hr₀, rfl⟩)
    · rcases hGr r hr with h | h
      exacts [absurd h.1 (hs ⟨r, hr, rfl⟩), h]

/-- **A component chart is a dilated Jordan coordinate.** Let `ψ` be a conformal bijection `C → ℍ` whose inverse
extends to a continuous injective `G` on `ℍ̄`, sending the nonzero reals into the open arcs `A \ B` (off `L`) and
`B \ A` (off `R`), with `G(0)` the exit limit of the chart `c` and `G → F` at `∞`, `F` disjoint from `𝓝 (G 0)`. Then
`c⁻¹(w) = G(k w)` on `ℍ` for some `k > 0`, and `G` sends the positive reals into `A \ B`, the negative into `B \ A`. -/
theorem exists_dilation_of_extInv {R L C : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) (hCo : IsOpen C)
    {ψ G : ℂ → ℂ} (hψd : DifferentiableOn ℂ ψ C) (hψC : MapsTo ψ C H) (hGψ : ∀ z ∈ C, G (ψ z) = z)
    (hψG : ∀ w ∈ H, ψ (G w) = w) (hGH : MapsTo G H C) (hGc : ContinuousOn G Hbar) (hGi : InjOn G Hbar)
    {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B) (hGr : ∀ r : ℝ, r ≠ 0 → G r ∈ (A \ B) ∪ (B \ A))
    (hAL : ∀ z ∈ A \ B, z ∉ L) (hBR : ∀ z ∈ B \ A, z ∉ R)
    (hP : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (G 0))) {F : Filter ℂ} (hGinf : Tendsto G (cobounded ℂ ⊓ 𝓟 H) F)
    (hFP : Disjoint F (𝓝 (G 0))) :
    ∃ k : ℝ, 0 < k ∧ (∀ w ∈ H, c.2.1 w = G ((k : ℂ) * w)) ∧
      (∀ r : ℝ, 0 < r → G r ∈ A \ B) ∧ (∀ r : ℝ, r < 0 → G r ∈ B \ A) := by
  have hdi := GW3Word.differentiableOn_inv_of_isComponentChart hc hCo
  obtain ⟨-, hmF, hmI, hinv, hlim, -, -⟩ := hc
  -- `ψ ∘ c⁻¹` is a conformal automorphism of `ℍ`, a real Möbius map
  have hψbij : BijOn ψ C H := by
    refine ⟨hψC, fun z hz z' hz' h => ?_, fun w hw => ⟨G w, hGH hw, hψG w hw⟩⟩
    rw [← hGψ z hz, ← hGψ z' hz', h]
  have hφd : DifferentiableOn ℂ (fun w => ψ (c.2.1 w)) H := by
    intro w hw
    have h1 : DifferentiableAt ℂ ψ (c.2.1 w) := (hψd _ (hmI hw)).differentiableAt (hCo.mem_nhds (hmI hw))
    exact h1.comp_differentiableWithinAt w (hdi w hw)
  have hφb : BijOn (fun w => ψ (c.2.1 w)) H H := hψbij.comp (hinv.symm.bijOn hmI hmF)
  obtain ⟨a, b, cc, d, hdet, hφ⟩ := QuantumZipper.CA.exists_realMobius_of_bijOn_H hφd hφb
  have hcomp : ∀ w ∈ H, c.2.1 w = G (realMobius a b cc d w) := fun w hw => by
    rw [← hφ hw]; exact (hGψ _ (hmI hw)).symm
  -- boundary limits off the pole
  set m : ℝ → ℝ := fun x => (a * x + b) / (cc * x + d) with hm
  have hside : ∀ x : ℝ, cc * x + d ≠ 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (G (m x))) := by
    intro x hx
    exact GW3Law.tendsto_comp_realMobius hdet hcomp hx ((hGc _ (ofReal_mem_Hbar _)).mono H_subset_Hbar).tendsto
  have harc : ∀ x : ℝ, cc * x + d ≠ 0 → m x ≠ 0 →
      (0 < x → G (m x) ∈ A \ B) ∧ (x < 0 → G (m x) ∈ B \ A) := by
    intro x hx hmx
    have hNe : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    obtain ⟨p, hp, hpR, hpL⟩ := hlim x
    have e : G (m x) = p := tendsto_nhds_unique (hside x hx) hp
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hGr (m x) hmx with h' | h'
      exacts [h', absurd (e ▸ hpR h) (hBR _ h')]
    · rcases hGr (m x) hmx with h' | h'
      exacts [absurd (e ▸ hpL h) (hAL _ h'), h']
  have hpos : ∀ r₀ : ℝ, 0 < r₀ → (G r₀ ∈ A \ B → ∀ r ∈ Ioi (0 : ℝ), G r ∈ A \ B) ∧
      (G r₀ ∈ B \ A → ∀ r ∈ Ioi (0 : ℝ), G r ∈ B \ A) := fun r₀ hr₀ =>
    forall_mem_of_isPreconnected hGc hA hB isPreconnected_Ioi (fun r hr => hGr r (ne_of_gt hr)) hr₀
  have hneg : ∀ r₀ : ℝ, r₀ < 0 → (G r₀ ∈ A \ B → ∀ r ∈ Iio (0 : ℝ), G r ∈ A \ B) ∧
      (G r₀ ∈ B \ A → ∀ r ∈ Iio (0 : ℝ), G r ∈ B \ A) := fun r₀ hr₀ =>
    forall_mem_of_isPreconnected hGc hA hB isPreconnected_Iio (fun r hr => hGr r (ne_of_lt hr)) hr₀
  -- `N(0) = 0`
  have hne0 : (𝓝[H] (0 : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hd0 : d ≠ 0 := by
    intro hd
    have hN : Tendsto (realMobius a b cc d) (𝓝[H] (0 : ℂ)) (cobounded ℂ ⊓ 𝓟 H) := by
      have := PrimeEnd.tendsto_realMobius_approachH hdet ((0 : ℝ) : OnePoint ℝ)
      simpa [hd] using this
    have hF : Tendsto c.2.1 (𝓝[H] (0 : ℂ)) F :=
      (hGinf.comp hN).congr' (eventually_nhdsWithin_of_forall fun w hw => (hcomp w hw).symm)
    exact (hne0.map c.2.1).ne (disjoint_self.1 (hFP.mono hF hP))
  have hb0 : b = 0 := by
    have h0 : cc * 0 + d ≠ 0 := by simpa using hd0
    have h1 := hside 0 h0
    rw [Complex.ofReal_zero] at h1
    have e : G (m 0) = G 0 := tendsto_nhds_unique h1 hP
    have e' : ((m 0 : ℝ) : ℂ) = 0 := hGi (ofReal_mem_Hbar _) (by simpa using ofReal_mem_Hbar 0) e
    have e'' : b / d = 0 := by
      have := Complex.ofReal_eq_zero.1 e'
      simpa [hm] using this
    rcases div_eq_zero_iff.1 e'' with h | h
    exacts [h, absurd h hd0]
  subst hb0
  have had : 0 < a * d := by simpa using hdet
  -- no pole: `c = 0`
  have hcc : cc = 0 := by
    by_contra hcc
    rcases lt_or_gt_of_ne (mul_ne_zero hd0 hcc) with hdc | hdc
    · -- pole `−d/c > 0`
      have hacc : a * cc < 0 := by
        by_contra h
        push Not at h
        have h1 : a * d * (d * cc) < 0 := mul_neg_of_pos_of_neg had hdc
        nlinarith [mul_nonneg h (mul_self_nonneg d)]
      set x₂ : ℝ := -d / cc + 1 with hx₂def
      have hx₂ : cc * x₂ + d = cc := by rw [hx₂def]; field_simp; ring
      have hx₂pos : 0 < x₂ := by
        have : 0 < -d / cc := (div_pos_iff_mul_pos hcc).2 (by linarith)
        linarith
      have hmx₂ : m x₂ < 0 := by
        show (a * x₂ + 0) / (cc * x₂ + d) < 0
        rw [hx₂, add_zero, div_neg_iff_mul_neg hcc]
        nlinarith
      have hx₃ : cc * (-1) + d ≠ 0 := by
        intro h
        have : d = cc := by linarith
        rw [this] at hdc
        nlinarith [mul_self_nonneg cc]
      have hmx₃ : m (-1) < 0 := by
        show (a * (-1) + 0) / (cc * (-1) + d) < 0
        rw [add_zero, div_neg_iff_mul_neg hx₃]
        have h1 : 0 < a * d * ((cc * (-1) + d) * d) := mul_pos had (by nlinarith)
        nlinarith [mul_self_nonneg d, mul_self_pos.2 hd0]
      have h1 := (harc x₂ (by rw [hx₂]; exact hcc) hmx₂.ne).1 hx₂pos
      have h2 := (harc (-1) hx₃ hmx₃.ne).2 (by norm_num)
      have h3 := (hneg (m x₂) hmx₂).1 h1 (m (-1)) hmx₃
      exact h2.2 h3.1
    · -- pole `−d/c < 0`
      have hacc : 0 < a * cc := by
        by_contra h
        push Not at h
        have h1 : 0 < a * d * (d * cc) := mul_pos had hdc
        nlinarith [mul_nonneg (neg_nonneg.2 h) (mul_self_nonneg d)]
      set x₂ : ℝ := -d / cc - 1 with hx₂def
      have hx₂ : cc * x₂ + d = -cc := by rw [hx₂def]; field_simp; ring
      have hx₂neg : x₂ < 0 := by
        have : -d / cc < 0 := (div_neg_iff_mul_neg hcc).2 (by linarith)
        linarith
      have hmx₂ : 0 < m x₂ := by
        show 0 < (a * x₂ + 0) / (cc * x₂ + d)
        rw [hx₂, add_zero, div_pos_iff_mul_pos (neg_ne_zero.2 hcc)]
        nlinarith
      have hx₃ : cc * 1 + d ≠ 0 := by
        intro h
        have : d = -cc := by linarith
        rw [this] at hdc
        nlinarith [mul_self_nonneg cc]
      have hmx₃ : 0 < m 1 := by
        show 0 < (a * 1 + 0) / (cc * 1 + d)
        rw [add_zero, div_pos_iff_mul_pos hx₃]
        have h1 : 0 < a * d * ((cc * 1 + d) * d) := mul_pos had (by nlinarith)
        nlinarith [mul_self_nonneg d, mul_self_pos.2 hd0]
      have h1 := (harc x₂ (by rw [hx₂]; exact neg_ne_zero.2 hcc) hmx₂.ne').2 hx₂neg
      have h2 := (harc 1 hx₃ hmx₃.ne').1 (by norm_num)
      have h3 := (hpos (m x₂) hmx₂).2 h1 (m 1) hmx₃
      exact h2.2 h3.1
  subst hcc
  have hk : 0 < a / d := (div_pos_iff_mul_pos hd0).2 had
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0
  refine ⟨a / d, hk, fun w hw => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · rw [hcomp w hw]
    congr 1
    simp only [QuantumZipper.CA.realMobius, Complex.ofReal_zero, zero_mul, zero_add, add_zero,
      Complex.ofReal_div]
    field_simp
  · have h1 : (0 : ℝ) * 1 + d ≠ 0 := by simpa using hd0
    have hm1 : 0 < m 1 := by
      show 0 < (a * 1 + 0) / (0 * 1 + d)
      simpa using hk
    exact (hpos (m 1) hm1).1 ((harc 1 h1 hm1.ne').1 one_pos) r hr
  · have h1 : (0 : ℝ) * (-1) + d ≠ 0 := by simpa using hd0
    have hm1 : m (-1) < 0 := by
      show (a * (-1) + 0) / (0 * (-1) + d) < 0
      simpa [neg_div] using hk
    exact (hneg (m (-1)) hm1).2 ((harc (-1) h1 hm1.ne).2 (by norm_num)) r hr

end GB11Chart

end Theorem14

end InteractingSLE
