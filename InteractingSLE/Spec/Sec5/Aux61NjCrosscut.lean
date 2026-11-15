/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.Complex.BasicsReflection
import QuantumZipper.Proofs.Complex.CaraBdry

/-!
# The component of a small ball reached through a boundary collar

Packet PROVE-AUX61-NOJUMP (ruling R103). The component comparisons of the fibre cover
(`Aux61GPrime.ZeroComparisons.cover`) need, at a window point, that the inverse chart enters
**one component** of `Ω ∩ B(z₀, ρ)` that avoids the marked set (`freeNear`); other accesses at the
same physical boundary point `z₀` (other prime ends over a pinch point) may meet it. This file
proves, for an abstract conformal chart, that a component reached through a collar is contained in
the collar's image, with no condition on the fibre of the boundary map — so pinch points of the
counterflow hull are harmless.

* `exists_ne_of_injOn`: the boundary values of a holomorphic injective map on a half-disc are not
  constant on its diameter (Schwarz reflection and the identity theorem, QuantumZipper's
  `CA.eqOn_const_of_eq_const_on_Ioo`).
* `component_subset_of_crosscut`: if the boundary values at `m ± r` differ from `z₀ ∉ Ω`, the image
  `C` of the closed semicircle over `[m − r, m + r]` is compact and misses `z₀`; on a ball `B(z₀, ρ)`
  missing `C`, the chart image of any component of `Ω ∩ B(z₀, ρ)` that meets the half-disc stays in
  it (it is preconnected and avoids the semicircle).
* **`exists_component_subset_of_collar`**: along an open collar `H ∩ B(ξ₀, δ)` mapped by `Φ` into
  `D`, at every collar real point `x` there is `ρ > 0` such that near `x` (in `ℍ`) the component of
  `Φ ζ` in `Ω ∩ B(φ x, ρ)` lies in `D`.

## Proof of the collar form

Choose real `a < x < b` in the collar with `φ a ≠ φ x ≠ φ b` (nonconstancy on each side of `x`), and
apply the crosscut lemma to the semicircle over `[a, b]`, which lies in the collar.

Deterministic; nothing here replaces a source statement.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61Nj

theorem hbar_subset_closure_H : Hbar ⊆ closure H := by
  rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]

theorem ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext (by simp) (by simp [hz])

/-- Real points of the ball `B(m, r)` have real part in `(m − r, m + r)`. -/
theorem re_mem_Ioo_of_mem_ball {z : ℂ} {m r : ℝ} (hz : z ∈ ball (m : ℂ) r) :
    z.re ∈ Ioo (m - r) (m + r) := by
  have h := (abs_re_le_norm (z - m)).trans_lt (mem_ball_iff_norm.1 hz)
  rw [sub_re, ofReal_re] at h
  exact ⟨by linarith [neg_abs_le (z.re - m)], by linarith [le_abs_self (z.re - m)]⟩

theorem ofReal_mem_ball_of_mem_Ioo {t m r : ℝ} (ht : t ∈ Ioo (m - r) (m + r)) :
    (t : ℂ) ∈ ball (m : ℂ) r := by
  rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-! ### Nonconstant boundary values -/

/-- **Boundary values of a conformal map are not constant on an interval.** If `Φ` is holomorphic
and injective on the half-disc `ℍ ∩ B(m, r)` with boundary limits `φ a` at the real points `a` of
the ball, then `φ` is not constant on `(m − r, m + r)`. -/
theorem exists_ne_of_injOn {Φ : ℂ → ℂ} {φ : ℝ → ℂ} {m r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ Φ (H ∩ ball (m : ℂ) r)) (hinj : InjOn Φ (H ∩ ball (m : ℂ) r))
    (hlim : ∀ a : ℝ, (a : ℂ) ∈ ball (m : ℂ) r → Tendsto Φ (𝓝[H] (a : ℂ)) (𝓝 (φ a))) (c : ℂ) :
    ∃ a ∈ Ioo (m - r) (m + r), φ a ≠ c := by
  refine by_contra fun hcon' => ?_
  have hcon : ∀ a ∈ Ioo (m - r) (m + r), φ a = c := fun a ha =>
    not_not.1 fun h => hcon' ⟨a, ha, h⟩
  have hHo : IsOpen (H ∩ ball (m : ℂ) r) := QuantumZipper.isOpen_H.inter isOpen_ball
  have hcontH : ∀ z ∈ H ∩ ball (m : ℂ) r, Tendsto Φ (𝓝[H] z) (𝓝 (Φ z)) := fun z hz =>
    ((hd.differentiableAt (hHo.mem_nhds hz)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hlimall : ∀ z ∈ Hbar ∩ ball (m : ℂ) r, ∃ y, Tendsto Φ (𝓝[H] z) (𝓝 y) := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact ⟨Φ z, hcontH z ⟨hzH, hz.2⟩⟩
    · have h0 : z.im = 0 := le_antisymm (not_lt.1 hzH) hz.1
      have hzr := ofReal_re_of_im_eq_zero h0
      refine ⟨φ z.re, ?_⟩
      have h := hlim z.re (by rw [hzr]; exact hz.2)
      rwa [hzr] at h
  have hc : ContinuousOn (extendFrom H Φ) (Hbar ∩ ball (m : ℂ) r) :=
    continuousOn_extendFrom (fun z hz => hbar_subset_closure_H hz.1) hlimall
  have hext : ∀ z ∈ H ∩ ball (m : ℂ) r, extendFrom H Φ z = Φ z := fun z hz =>
    extendFrom_eq (subset_closure hz.1) (hcontH z hz)
  have hextR : ∀ a : ℝ, (a : ℂ) ∈ ball (m : ℂ) r → extendFrom H Φ a = φ a := fun a ha =>
    extendFrom_eq (hbar_subset_closure_H (show (0 : ℝ) ≤ (a : ℂ).im by simp)) (hlim a ha)
  set g : ℂ → ℂ := fun z => extendFrom H Φ z - c with hg
  have hgd : DifferentiableOn ℂ g (H ∩ ball (m : ℂ) r) :=
    (hd.sub_const c).congr fun z hz => by simp only [hg, hext z hz]
  have hgc : ContinuousOn g (Hbar ∩ ball (m : ℂ) r) := hc.sub continuousOn_const
  have hgreal : ∀ z ∈ ball (m : ℂ) r, z.im = 0 → (g z).im = 0 := by
    intro z hz h0
    have hzr := ofReal_re_of_im_eq_zero h0
    have hzb : ((z.re : ℝ) : ℂ) ∈ ball (m : ℂ) r := by rw [hzr]; exact hz
    simp only [hg]
    rw [← hzr, hextR z.re hzb, hcon z.re (re_mem_Ioo_of_mem_ball hz), sub_self, zero_im]
  have hab : m - r < m + r := by linarith
  have hI : ∀ t ∈ Ioo (m - r) (m + r), (t : ℂ) ∈ ball (m : ℂ) r ∧ g t = 0 := fun t ht => by
    have htb := ofReal_mem_ball_of_mem_Ioo ht
    refine ⟨htb, ?_⟩
    simp only [hg]
    rw [hextR t htb, hcon t ht, sub_self]
  have hzero := QuantumZipper.CA.eqOn_const_of_eq_const_on_Ioo hgd hgc hgreal hab hI
  -- two distinct points of the half-disc with the same image
  have hmem : ∀ k : ℝ, 0 < k → k < r → (m : ℂ) + (k : ℂ) * I ∈ H ∩ ball (m : ℂ) r := by
    intro k hk hkr
    refine ⟨show (0 : ℝ) < ((m : ℂ) + (k : ℂ) * I).im by simp [hk], ?_⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hk]
    exact hkr
  have h1 := hmem (r / 2) (by linarith) (by linarith)
  have h2 := hmem (r / 3) (by linarith) (by linarith)
  have hv : ∀ z ∈ H ∩ ball (m : ℂ) r, Φ z = c := fun z hz => by
    have := hzero z ⟨QuantumZipper.H_subset_Hbar hz.1, hz.2⟩
    simp only [hg, hext z hz] at this
    exact sub_eq_zero.1 this
  have he := hinj h1 h2 ((hv _ h1).trans (hv _ h2).symm)
  have him := congrArg Complex.im he
  simp at him
  linarith

/-- Nonconstancy on the left of a point. -/
theorem exists_lt_ne_of_injOn {Φ : ℂ → ℂ} {φ : ℝ → ℂ} {x ε : ℝ} (hε : 0 < ε)
    (hd : DifferentiableOn ℂ Φ H) (hinj : InjOn Φ H)
    (hlim : ∀ a : ℝ, (a : ℂ) ∈ ball (x : ℂ) ε → Tendsto Φ (𝓝[H] (a : ℂ)) (𝓝 (φ a))) (c : ℂ) :
    ∃ a ∈ Ioo (x - ε) x, φ a ≠ c := by
  have hsub : ball ((x - ε / 2 : ℝ) : ℂ) (ε / 2) ⊆ ball (x : ℂ) ε := by
    refine ball_subset_ball' ?_
    rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    rw [show x - ε / 2 - x = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  obtain ⟨a, ha, hne⟩ := exists_ne_of_injOn (half_pos hε) (hd.mono inter_subset_left)
    (hinj.mono inter_subset_left) (fun a ha => hlim a (hsub ha)) c
  refine ⟨a, ⟨by linarith [ha.1], by linarith [ha.2]⟩, hne⟩

/-- Nonconstancy on the right of a point. -/
theorem exists_gt_ne_of_injOn {Φ : ℂ → ℂ} {φ : ℝ → ℂ} {x ε : ℝ} (hε : 0 < ε)
    (hd : DifferentiableOn ℂ Φ H) (hinj : InjOn Φ H)
    (hlim : ∀ a : ℝ, (a : ℂ) ∈ ball (x : ℂ) ε → Tendsto Φ (𝓝[H] (a : ℂ)) (𝓝 (φ a))) (c : ℂ) :
    ∃ a ∈ Ioo x (x + ε), φ a ≠ c := by
  have hsub : ball ((x + ε / 2 : ℝ) : ℂ) (ε / 2) ⊆ ball (x : ℂ) ε := by
    refine ball_subset_ball' ?_
    rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    rw [show x + ε / 2 - x = ε / 2 by ring, abs_of_pos (by linarith)]
    linarith
  obtain ⟨a, ha, hne⟩ := exists_ne_of_injOn (half_pos hε) (hd.mono inter_subset_left)
    (hinj.mono inter_subset_left) (fun a ha => hlim a (hsub ha)) c
  refine ⟨a, ⟨by linarith [ha.1], by linarith [ha.2]⟩, hne⟩

/-! ### The crosscut over a real interval -/

/-- The closed upper semicircle over `[m − r, m + r]`. -/
def semicircle (m r : ℝ) : Set ℂ := sphere (m : ℂ) r ∩ Hbar

theorem isCompact_semicircle (m r : ℝ) : IsCompact (semicircle m r) :=
  (isCompact_sphere _ _).inter_right QuantumZipper.isClosed_Hbar

/-- The real points of the semicircle are its two endpoints. -/
theorem eq_or_eq_of_mem_semicircle {m r : ℝ} {ζ : ℂ} (hζ : ζ ∈ semicircle m r) (h0 : ζ.im = 0) :
    ζ = ((m - r : ℝ) : ℂ) ∨ ζ = ((m + r : ℝ) : ℂ) := by
  have hzr := ofReal_re_of_im_eq_zero h0
  have hn := hζ.1
  rw [mem_sphere, dist_eq_norm, ← hzr, ← ofReal_sub, norm_real, Real.norm_eq_abs] at hn
  rcases abs_eq (show (0 : ℝ) ≤ r by rw [← hn]; exact abs_nonneg _) |>.1 hn with h | h
  · right; rw [← hzr]; congr 1; linarith
  · left; rw [← hzr]; congr 1; linarith

variable {Φ Ψ : ℂ → ℂ} {Ω : Set ℂ} {φ : ℝ → ℂ}

/-- **The crosscut lemma.** Let `Φ : ℍ → Ω` have the left inverse `Ψ` on `Ω` (continuous, into
`ℍ`), boundary limits `φ (m ∓ r)` at the endpoints of `[m − r, m + r]`, both different from a point
`z₀ ∉ Ω`. Then for some `ρ > 0`, every component of `Ω ∩ B(z₀, ρ)` through a point `w` with
`Ψ w ∈ B(m, r)` is contained in `Φ(ℍ ∩ B(m, r))`. -/
theorem component_subset_of_crosscut {m r : ℝ} {z₀ : ℂ}
    (hΦ : ContinuousOn Φ H) (hΦΩ : MapsTo Φ H Ω) (hΨ : ContinuousOn Ψ Ω) (hΨH : MapsTo Ψ Ω H)
    (hΦΨ : ∀ w ∈ Ω, Φ (Ψ w) = w)
    (hl : Tendsto Φ (𝓝[H] ((m - r : ℝ) : ℂ)) (𝓝 (φ (m - r))))
    (hr : Tendsto Φ (𝓝[H] ((m + r : ℝ) : ℂ)) (𝓝 (φ (m + r))))
    (hz₀ : z₀ ∉ Ω) (hl0 : φ (m - r) ≠ z₀) (hr0 : φ (m + r) ≠ z₀) :
    ∃ ρ > 0, ∀ w ∈ Ω ∩ ball z₀ ρ, Ψ w ∈ ball (m : ℂ) r →
      connectedComponentIn (Ω ∩ ball z₀ ρ) w ⊆ Φ '' (H ∩ ball (m : ℂ) r) := by
  set E := extendFrom H Φ with hE
  have hlimA : ∀ ζ ∈ semicircle m r, Tendsto Φ (𝓝[H] ζ) (𝓝 (E ζ)) ∧
      (ζ ∈ H → E ζ = Φ ζ) ∧ (ζ.im = 0 → E ζ ≠ z₀) := by
    intro ζ hζ
    by_cases hζH : ζ ∈ H
    · have ht : Tendsto Φ (𝓝[H] ζ) (𝓝 (Φ ζ)) :=
        (hΦ.continuousAt (QuantumZipper.isOpen_H.mem_nhds hζH)).tendsto.mono_left nhdsWithin_le_nhds
      have he : E ζ = Φ ζ := extendFrom_eq (subset_closure hζH) ht
      refine ⟨he ▸ ht, fun _ => he, fun h0 => absurd hζH (by simp [QuantumZipper.H, h0])⟩
    · have h0 : ζ.im = 0 := le_antisymm (not_lt.1 hζH) hζ.2
      rcases eq_or_eq_of_mem_semicircle hζ h0 with rfl | rfl
      · have he : E ((m - r : ℝ) : ℂ) = φ (m - r) :=
          extendFrom_eq (hbar_subset_closure_H hζ.2) hl
        exact ⟨he ▸ hl, fun h => absurd h hζH, fun _ => he ▸ hl0⟩
      · have he : E ((m + r : ℝ) : ℂ) = φ (m + r) :=
          extendFrom_eq (hbar_subset_closure_H hζ.2) hr
        exact ⟨he ▸ hr, fun h => absurd h hζH, fun _ => he ▸ hr0⟩
  have hEc : ContinuousOn E (semicircle m r) :=
    continuousOn_extendFrom (fun ζ hζ => hbar_subset_closure_H hζ.2) fun ζ hζ => ⟨_, (hlimA ζ hζ).1⟩
  have hCc : IsClosed (E '' semicircle m r) := ((isCompact_semicircle m r).image_of_continuousOn hEc).isClosed
  have hz₀C : z₀ ∉ E '' semicircle m r := by
    rintro ⟨ζ, hζ, he⟩
    by_cases hζH : ζ ∈ H
    · rw [(hlimA ζ hζ).2.1 hζH] at he
      exact hz₀ (he ▸ hΦΩ hζH)
    · exact (hlimA ζ hζ).2.2 (le_antisymm (not_lt.1 hζH) hζ.2) he
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hCc.isOpen_compl z₀ hz₀C
  refine ⟨ρ, hρ, fun w hw hΨw => ?_⟩
  set Wc := connectedComponentIn (Ω ∩ ball z₀ ρ) w with hWc
  have hWsub : Wc ⊆ Ω ∩ ball z₀ ρ := connectedComponentIn_subset _ _
  have hWpre : IsPreconnected Wc := isPreconnected_connectedComponentIn
  have himg : IsPreconnected (Ψ '' Wc) := hWpre.image Ψ (hΨ.mono fun v hv => (hWsub hv).1)
  have hcover : Ψ '' Wc ⊆ ball (m : ℂ) r ∪ (closedBall (m : ℂ) r)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩
    by_cases hb : Ψ v ∈ ball (m : ℂ) r
    · exact Or.inl hb
    · refine Or.inr fun hcb => ?_
      have hs : Ψ v ∈ sphere (m : ℂ) r := by
        rw [mem_sphere]
        exact le_antisymm (mem_closedBall.1 hcb) (not_lt.1 fun h => hb (mem_ball.2 h))
      have hH := hΨH (hWsub hv).1
      have hA : Ψ v ∈ semicircle m r := ⟨hs, QuantumZipper.H_subset_Hbar hH⟩
      have he : E (Ψ v) = v := by rw [(hlimA _ hA).2.1 hH, hΦΨ v (hWsub hv).1]
      exact hball (hWsub hv).2 ⟨Ψ v, hA, he⟩
  have hin : Ψ '' Wc ⊆ ball (m : ℂ) r :=
    himg.subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_compl_right.mono_left ball_subset_closedBall) hcover
      ⟨Ψ w, ⟨w, mem_connectedComponentIn hw, rfl⟩, hΨw⟩
  intro v hv
  exact ⟨Ψ v, ⟨hΨH (hWsub hv).1, hin ⟨v, hv, rfl⟩⟩, hΦΨ v (hWsub hv).1⟩

/-- **The component through an open collar.** Let `Φ` be holomorphic and injective on `ℍ`, with
values in `Ω` and left inverse `Ψ` there, mapping the collar `ℍ ∩ B(ξ₀, δ)` into `D`, with boundary
limits `φ` at the collar's real points, and let `φ x ∉ Ω` at a collar real point `x`. Then for some
`ρ > 0`, near `x` in `ℍ`, `Φ ζ` lies in `Ω ∩ B(φ x, ρ)` and its component there lies in `D`. No
condition on the other preimages of `φ x` is needed. -/
theorem exists_component_subset_of_collar {D : Set ℂ} {ξ₀ δ x : ℝ}
    (hd : DifferentiableOn ℂ Φ H) (hinj : InjOn Φ H) (hΦΩ : MapsTo Φ H Ω)
    (hΨ : ContinuousOn Ψ Ω) (hΨH : MapsTo Ψ Ω H) (hΦΨ : ∀ w ∈ Ω, Φ (Ψ w) = w)
    (hΨΦ : ∀ ζ ∈ H, Ψ (Φ ζ) = ζ)
    (hcol : MapsTo Φ (H ∩ ball (ξ₀ : ℂ) δ) D)
    (hlim : ∀ a : ℝ, (a : ℂ) ∈ ball (ξ₀ : ℂ) δ → Tendsto Φ (𝓝[H] (a : ℂ)) (𝓝 (φ a)))
    (hx : (x : ℂ) ∈ ball (ξ₀ : ℂ) δ) (hxΩ : φ x ∉ Ω) :
    ∃ ρ > 0, ∀ᶠ ζ in 𝓝[H] (x : ℂ), Φ ζ ∈ Ω ∩ ball (φ x) ρ ∧
      connectedComponentIn (Ω ∩ ball (φ x) ρ) (Φ ζ) ⊆ D := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 isOpen_ball (x : ℂ) hx
  have hε2 : 0 < ε / 2 := half_pos hε
  have hlim' : ∀ a : ℝ, (a : ℂ) ∈ ball (x : ℂ) (ε / 2) →
      Tendsto Φ (𝓝[H] (a : ℂ)) (𝓝 (φ a)) := fun a ha =>
    hlim a (hεsub (ball_subset_ball (by linarith) ha))
  obtain ⟨a, ha, hane⟩ := exists_lt_ne_of_injOn hε2 hd hinj hlim' (φ x)
  obtain ⟨b, hb, hbne⟩ := exists_gt_ne_of_injOn hε2 hd hinj hlim' (φ x)
  set m : ℝ := (a + b) / 2 with hm
  set r : ℝ := (b - a) / 2 with hr
  have hr0 : 0 < r := by simp only [hr]; linarith [ha.2, hb.1]
  have hma : m - r = a := by simp only [hm, hr]; ring
  have hmb : m + r = b := by simp only [hm, hr]; ring
  have hballsub : ball (m : ℂ) r ⊆ ball (ξ₀ : ℂ) δ := by
    refine fun z hz => hεsub (ball_subset_ball' ?_ hz)
    rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    rcases le_total m x with hmx | hmx
    · rw [abs_of_nonpos (by linarith)]; simp only [hm, hr]; linarith [ha.1]
    · rw [abs_of_nonneg (by linarith)]; simp only [hm, hr]; linarith [hb.2]
  have hmemA : ((m - r : ℝ) : ℂ) ∈ ball (ξ₀ : ℂ) δ := by
    rw [hma]; exact hεsub (ofReal_mem_ball_of_mem_Ioo ⟨by linarith [ha.1], by linarith [ha.2, hε]⟩)
  have hmemB : ((m + r : ℝ) : ℂ) ∈ ball (ξ₀ : ℂ) δ := by
    rw [hmb]; exact hεsub (ofReal_mem_ball_of_mem_Ioo ⟨by linarith [hb.1, hε], by linarith [hb.2]⟩)
  obtain ⟨ρ, hρ, hcomp⟩ := component_subset_of_crosscut (φ := φ) (m := m) (r := r) (z₀ := φ x)
    hd.continuousOn hΦΩ hΨ hΨH hΦΨ (hlim _ hmemA) (hlim _ hmemB) hxΩ
    (by rw [hma]; exact hane) (by rw [hmb]; exact hbne)
  refine ⟨ρ, hρ, ?_⟩
  have hxm : (x : ℂ) ∈ ball (m : ℂ) r :=
    ofReal_mem_ball_of_mem_Ioo ⟨by rw [hma]; exact ha.2, by rw [hmb]; exact hb.1⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hxm),
    hlim x hx (isOpen_ball.mem_nhds (mem_ball_self hρ))] with ζ hζH hζm hζρ
  refine ⟨⟨hΦΩ hζH, hζρ⟩, ?_⟩
  refine (hcomp _ ⟨hΦΩ hζH, hζρ⟩ (by rw [hΨΦ ζ hζH]; exact hζm)).trans ?_
  rintro _ ⟨η, hη, rfl⟩
  exact hcol ⟨hη.1, hballsub hη.2⟩

end InteractingSLE.Sec5.Aux61Nj
