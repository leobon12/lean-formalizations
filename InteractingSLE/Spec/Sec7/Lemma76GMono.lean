/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanFiber

/-!
# The boundary correspondence of a composite of two charts is increasing

Packet PROVE-LEMMA76G (proof of Lemma 7.6, pp. 268–269: "Its image under `ψ` is an open interval", and the side of a
prefix seen from the joint domain). Let `ψ` be continuous on `ℍ̄`, holomorphic and injective on `ℍ` with `ψ(ℍ) ⊆ U`,
and let `f` be holomorphic and injective on the open set `U` with `f(U) ⊆ ℍ`. If the composite `f ∘ ψ` has a real limit
`F(w)` at every point `w` of a real open set `I` (from `ℍ`), then:

* `F` is continuous on `I` (`continuousOn_of_tendsto_comp`);
* near every point of `I`, `f ∘ ψ` extends by Schwarz reflection to a holomorphic function equal to `F` on the real
  line (`exists_reflection_comp`);
* `F` is injective on `I` (`injOn_of_tendsto_comp`: two real points with the same value would give, by the open
  mapping theorem, two disjoint half-discs with overlapping images);
* if `I = (c, ∞)` (or `(−∞, c)`) and `f ∘ ψ` has bounded displacement, `F` is strictly increasing on `I`
  (`strictMonoOn_Ioi_of_tendsto_comp`, `strictMonoOn_Iio_of_tendsto_comp`).

In the retained chart of a disjoint pair, `ψ` is the chart inverse and `f` the single-path chart of one prefix; the
sign of `F` then tells which side of the prefix a chart point sees.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

variable {f ψ : ℂ → ℂ} {U : Set ℂ}

theorem ofReal_mem_Hbar (x : ℝ) : ((x : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp

theorem ofReal_notMem_H (x : ℝ) : ((x : ℝ) : ℂ) ∉ H := fun h => by
  have : (0 : ℝ) < ((x : ℝ) : ℂ).im := h
  simp at this

theorem neBot_nhdsWithin_H (x : ℝ) : (𝓝[H] ((x : ℝ) : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.1 ?_
  rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
  exact ofReal_mem_Hbar x

theorem dist_ofReal' (x y : ℝ) : dist ((x : ℝ) : ℂ) ((y : ℝ) : ℂ) = dist x y :=
  (Complex.dist_of_im_eq (by simp)).trans (by simp)

/-- The composite is continuous on `ℍ`. -/
theorem continuousOn_comp (hψc : ContinuousOn ψ Hbar) (hψU : MapsTo ψ H U) (hfd : DifferentiableOn ℂ f U) :
    ContinuousOn (fun z => f (ψ z)) H :=
  hfd.continuousOn.comp (hψc.mono H_subset_Hbar) hψU

/-- **The boundary values are continuous.** -/
theorem continuousOn_of_tendsto_comp {F : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hlim : ∀ w ∈ J, Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((F w : ℝ) : ℂ))) :
    ContinuousOn F J := by
  intro x hx
  refine (Metric.continuousAt_iff.2 fun ε hε => ?_).continuousWithinAt
  obtain ⟨δ, hδ, hδε⟩ := Metric.mem_nhdsWithin_iff.1 ((hlim x hx) (ball_mem_nhds _ (half_pos hε)))
  obtain ⟨ρ, hρ, hρI⟩ := Metric.isOpen_iff.1 hJ x hx
  refine ⟨min δ ρ, lt_min hδ hρ, fun {x'} hx' => ?_⟩
  have hx'I : x' ∈ J := hρI (lt_of_lt_of_le hx' (min_le_right _ _))
  have hxx : dist x' x < δ := lt_of_lt_of_le hx' (min_le_left _ _)
  have hx'n : ball ((x' : ℝ) : ℂ) (δ - dist x' x) ⊆ ball ((x : ℝ) : ℂ) δ := by
    intro z hz
    rw [mem_ball] at hz ⊢
    calc dist z (x : ℂ) ≤ dist z (x' : ℂ) + dist ((x' : ℝ) : ℂ) (x : ℂ) := dist_triangle _ _ _
      _ < (δ - dist x' x) + dist x' x := by
        rw [dist_ofReal' x' x]; linarith
      _ = δ := by ring
  have hpos : 0 < δ - dist x' x := by linarith
  have hev : ∀ᶠ z in 𝓝[H] ((x' : ℝ) : ℂ), f (ψ z) ∈ closedBall ((F x : ℝ) : ℂ) (ε / 2) := by
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds _ hpos), self_mem_nhdsWithin] with z hz hzH
    exact ball_subset_closedBall (hδε ⟨hx'n hz.2, hzH⟩)
  have := neBot_nhdsWithin_H x'
  have hcl := (isClosed_closedBall (x := ((F x : ℝ) : ℂ)) (ε := ε / 2)).mem_of_tendsto (hlim x' hx'I) hev
  rw [mem_closedBall, dist_ofReal'] at hcl
  linarith

section Reflect

variable (hψc : ContinuousOn ψ Hbar) (hψd : DifferentiableOn ℂ ψ H) (hψU : MapsTo ψ H U) (hU : IsOpen U)
  (hfd : DifferentiableOn ℂ f U) (hfH : MapsTo f U H)
include hψc hψd hψU hU hfd

omit hψc in
/-- The composite is holomorphic on `ℍ`. -/
theorem differentiableOn_comp : DifferentiableOn ℂ (fun z => f (ψ z)) H := fun z hz =>
  ((hfd (ψ z) (hψU hz)).differentiableAt (hU.mem_nhds (hψU hz))).comp_differentiableWithinAt z
    (hψd z hz)

/-- **Schwarz reflection of the composite** across a real interval where it has real limits: a holomorphic function
on the disc, equal to `f ∘ ψ` on `ℍ` and to the limits on the real diameter, commuting with conjugation. -/
theorem exists_reflection_comp {F : ℝ → ℝ} {x r : ℝ}
    (hlim : ∀ w ∈ Ioo (x - r) (x + r), Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((F w : ℝ) : ℂ))) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (x : ℂ) r) ∧ (∀ z ∈ H ∩ ball (x : ℂ) r, G z = f (ψ z)) ∧
      (∀ w ∈ Ioo (x - r) (x + r), G w = F w) ∧ ∀ z ∈ ball (x : ℂ) r, G (conj z) = conj (G z) := by
  set g : ℂ → ℂ := fun z => f (ψ z) with hg
  have hgc : ContinuousOn g H := continuousOn_comp hψc hψU hfd
  have hgd : DifferentiableOn ℂ g H := differentiableOn_comp hψd hψU hU hfd
  have hreIoo : ∀ z ∈ ball (x : ℂ) r, z.re ∈ Ioo (x - r) (x + r) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - x)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    constructor <;> linarith [abs_lt.1 (lt_of_le_of_lt this hz)]
  have hlimE : ∀ z ∈ Hbar ∩ ball (x : ℂ) r, ∃ v, Tendsto g (𝓝[H] z) (𝓝 v) := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact ⟨g z, (hgc z hzH).tendsto⟩
    · have hz0 : z.im = 0 := le_antisymm (not_lt.1 hzH) hz.1
      have hze : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz0])
      refine ⟨(F z.re : ℂ), ?_⟩
      rw [hze]
      exact hlim _ (hreIoo z hz.2)
  have hEc : ContinuousOn (extendFrom H g) (Hbar ∩ ball (x : ℂ) r) :=
    continuousOn_extendFrom (fun z hz => by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hz.1) hlimE
  have hEg : ∀ z ∈ H, extendFrom H g z = g z := fun z hz =>
    extendFrom_eq (subset_closure hz) (hgc z hz).tendsto
  have hEF : ∀ w ∈ Ioo (x - r) (x + r), extendFrom H g w = F w := fun w hw =>
    extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact ofReal_mem_Hbar w) (hlim w hw)
  have hEd : DifferentiableOn ℂ (extendFrom H g) (H ∩ ball (x : ℂ) r) :=
    (hgd.mono inter_subset_left).congr fun z hz => hEg z hz.1
  have hEr : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (extendFrom H g z).im = 0 := by
    intro z hz hz0
    have hze : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz0])
    rw [hze, hEF _ (hreIoo z hz)]
    simp
  obtain ⟨G, hGd, hGeq, hGc⟩ := QuantumZipper.CA.exists_reflection_extension hEd hEc hEr
  refine ⟨G, hGd, fun z hz => by rw [hGeq ⟨H_subset_Hbar hz.1, hz.2⟩, hEg z hz.1], fun w hw => ?_, hGc⟩
  have hwb : ((w : ℝ) : ℂ) ∈ ball (x : ℂ) r := by
    rw [mem_ball, dist_ofReal', Real.dist_eq, abs_lt]
    constructor <;> linarith [hw.1, hw.2]
  rw [hGeq ⟨ofReal_mem_Hbar w, hwb⟩, hEF w hw]

include hfH in
/-- **The boundary values are injective** on an open real set where they exist (open mapping theorem). -/
theorem injOn_of_tendsto_comp (hψi : InjOn ψ H) (hfi : InjOn f U) {F : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hlim : ∀ w ∈ J, Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((F w : ℝ) : ℂ))) : InjOn F J := by
  intro w₁ hw₁ w₂ hw₂ heq
  by_contra hne
  have hgi : InjOn (fun z => f (ψ z)) H := fun z hz z' hz' h => hψi hz hz' (hfi (hψU hz) (hψU hz') h)
  obtain ⟨ρ₁, hρ₁, hρ₁I⟩ := Metric.isOpen_iff.1 hJ w₁ hw₁
  obtain ⟨ρ₂, hρ₂, hρ₂I⟩ := Metric.isOpen_iff.1 hJ w₂ hw₂
  have hd : 0 < dist w₁ w₂ := dist_pos.2 hne
  set r : ℝ := min (min ρ₁ ρ₂) (dist w₁ w₂ / 2) with hr
  have hr0 : 0 < r := lt_min (lt_min hρ₁ hρ₂) (half_pos hd)
  have hIoo : ∀ {w ρ : ℝ}, ball w ρ ⊆ J → r ≤ ρ → ∀ t ∈ Ioo (w - r) (w + r), t ∈ J := by
    intro w ρ hρI hrρ t ht
    refine hρI ?_
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  -- the local picture at one point
  have hloc : ∀ w, (∀ t ∈ Ioo (w - r) (w + r), t ∈ J) →
      ∃ G : ℂ → ℂ, (∀ z ∈ H ∩ ball (w : ℂ) r, G z = f (ψ z)) ∧ (∀ t ∈ Ioo (w - r) (w + r), G t = F t) ∧
        (∀ z ∈ ball (w : ℂ) r, G (conj z) = conj (G z)) ∧ G '' ball (w : ℂ) r ∈ 𝓝 ((F w : ℝ) : ℂ) := by
    intro w hwI
    obtain ⟨G, hGd, hGg, hGF, hGc⟩ := exists_reflection_comp hψc hψd hψU hU hfd
      (fun t ht => hlim t (hwI t ht))
    have hwmem : ((w : ℝ) : ℂ) ∈ ball (w : ℂ) r := mem_ball_self hr0
    have hGa : AnalyticAt ℂ G w := (hGd.analyticOnNhd isOpen_ball) _ hwmem
    have hGw : G w = F w := hGF w ⟨by linarith, by linarith⟩
    refine ⟨G, hGg, hGF, hGc, ?_⟩
    rcases hGa.eventually_constant_or_nhds_le_map_nhds with hcst | hopen
    · exfalso
      -- two distinct points of `ℍ` near `w` with the same value
      obtain ⟨δ, hδ, hδc⟩ := Metric.eventually_nhds_iff.1 hcst
      set ε := min (δ / 2) (r / 2) with hε
      have hε0 : 0 < ε := lt_min (half_pos hδ) (half_pos hr0)
      have hmem : ∀ k : ℝ, 0 < k → k ≤ 1 → ((w : ℂ) + (k * ε : ℝ) * I) ∈ H ∩ ball (w : ℂ) r ∧
          dist ((w : ℂ) + (k * ε : ℝ) * I) (w : ℂ) < δ := by
        intro k hk hk1
        have hn : ‖((k * ε : ℝ) : ℂ) * I‖ = k * ε := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (mul_pos hk hε0)]
        have hkε : k * ε ≤ ε := by nlinarith
        refine ⟨⟨show 0 < ((w : ℂ) + (k * ε : ℝ) * I).im by simp [mul_pos hk hε0], ?_⟩, ?_⟩
        · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hn]
          linarith [min_le_right (δ / 2) (r / 2)]
        · rw [dist_eq_norm, add_sub_cancel_left, hn]
          linarith [min_le_left (δ / 2) (r / 2)]
      obtain ⟨h1H, h1d⟩ := hmem 1 one_pos le_rfl
      obtain ⟨h2H, h2d⟩ := hmem (1 / 2) (by norm_num) (by norm_num)
      have hv1 := hδc h1d
      have hv2 := hδc h2d
      rw [hGg _ h1H] at hv1
      rw [hGg _ h2H] at hv2
      have := hgi h1H.1 h2H.1 (hv1.trans hv2.symm)
      have h3 := congrArg Complex.im this
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at h3
      nlinarith
    · rw [← hGw]
      exact hopen (image_mem_map (ball_mem_nhds _ hr0))
  obtain ⟨G₁, hG₁g, -, hG₁c, hG₁n⟩ := hloc w₁ (hIoo hρ₁I ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨G₂, hG₂g, -, hG₂c, hG₂n⟩ := hloc w₂ (hIoo hρ₂I ((min_le_left _ _).trans (min_le_right _ _)))
  rw [← heq] at hG₂n
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hG₁n hG₂n)
  set v : ℂ := ((F w₁ : ℝ) : ℂ) + ((ε / 2 : ℝ) : ℂ) * I with hv
  have hvb : v ∈ ball ((F w₁ : ℝ) : ℂ) ε := by
    rw [mem_ball, hv, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hvim : 0 < v.im := by simp [hv, hε]
  -- a preimage of `v` in each disc lies in `ℍ`
  have hpre : ∀ {G : ℂ → ℂ} {w : ℝ}, (∀ z ∈ H ∩ ball (w : ℂ) r, G z = f (ψ z)) →
      (∀ z ∈ ball (w : ℂ) r, G (conj z) = conj (G z)) → v ∈ G '' ball (w : ℂ) r →
      ∃ z ∈ H ∩ ball (w : ℂ) r, f (ψ z) = v := by
    intro G w hGg hGc ⟨z, hzb, hzv⟩
    rcases lt_trichotomy z.im 0 with hz | hz | hz
    · exfalso
      have hcb : conj z ∈ ball (w : ℂ) r := by
        rw [mem_ball, dist_eq_norm] at hzb ⊢
        rw [← Complex.conj_ofReal w, ← map_sub, Complex.norm_conj]
        exact hzb
      have hcH : conj z ∈ H := show 0 < (conj z).im by simp [hz]
      have h1 := hGc z hzb
      rw [← hzv] at hvim
      have h2 := congrArg Complex.im (hGc (conj z) hcb)
      rw [Complex.conj_conj, hGg _ ⟨hcH, hcb⟩] at h2
      have h3 := hfH (hψU hcH)
      have h4 : (G z).im = -(f (ψ (conj z))).im := by rw [h2]; simp
      have h5 : 0 < (f (ψ (conj z))).im := h3
      linarith
    · exfalso
      have hze : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz])
      have hzr : z.re ∈ Ioo (w - r) (w + r) := by
        rw [hze, mem_ball, dist_ofReal', Real.dist_eq, abs_lt] at hzb
        exact ⟨by linarith [hzb.1], by linarith [hzb.2]⟩
      -- the value at a real point is real
      have hGr : (G z).im = 0 := by
        have h1 := hGc z hzb
        rw [show conj z = z by rw [hze, Complex.conj_ofReal]] at h1
        have h2 := congrArg Complex.im h1
        simp only [Complex.conj_im] at h2
        linarith
      rw [hzv] at hGr
      linarith
    · exact ⟨z, ⟨hz, hzb⟩, by rw [← hGg z ⟨hz, hzb⟩, hzv]⟩
  obtain ⟨z₁, hz₁, hz₁v⟩ := hpre hG₁g hG₁c (hεsub hvb).1
  obtain ⟨z₂, hz₂, hz₂v⟩ := hpre hG₂g hG₂c (hεsub hvb).2
  have hz12 := hgi hz₁.1 hz₂.1 (hz₁v.trans hz₂v.symm)
  have hd₁ := hz₁.2
  rw [hz12, mem_ball] at hd₁
  have hd₂ : dist z₂ (w₂ : ℂ) < r := hz₂.2
  have htri := dist_triangle_left ((w₁ : ℝ) : ℂ) ((w₂ : ℝ) : ℂ) z₂
  rw [dist_ofReal'] at htri
  have hrd : r ≤ dist w₁ w₂ / 2 := min_le_right _ _
  linarith

omit hψc hψd hψU hU hfd in
/-- The limits inherit a displacement bound. -/
theorem abs_sub_le_of_tendsto_comp {F : ℝ → ℝ} {w M : ℝ} (hM : ∀ z ∈ H, ‖f (ψ z) - z‖ ≤ M)
    (hlim : Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((F w : ℝ) : ℂ))) : |F w - w| ≤ M := by
  have := neBot_nhdsWithin_H w
  have h1 : Tendsto (fun z => ‖f (ψ z) - z‖) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ‖((F w : ℝ) : ℂ) - ((w : ℝ) : ℂ)‖) :=
    (hlim.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm
  have h2 := le_of_tendsto h1 (eventually_nhdsWithin_of_forall fun z hz => hM z hz)
  rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2

include hfH in
/-- **The boundary values are strictly increasing on a right half-line** (bounded displacement fixes the
direction). -/
theorem strictMonoOn_Ioi_of_tendsto_comp (hψi : InjOn ψ H) (hfi : InjOn f U) {F : ℝ → ℝ} {c M : ℝ}
    (hlim : ∀ w ∈ Ioi c, Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((F w : ℝ) : ℂ)))
    (hM : ∀ z ∈ H, ‖f (ψ z) - z‖ ≤ M) : StrictMonoOn F (Ioi c) := by
  have hinj := injOn_of_tendsto_comp hψc hψd hψU hU hfd hfH hψi hfi isOpen_Ioi hlim
  have hcont := continuousOn_of_tendsto_comp isOpen_Ioi hlim
  have hdisp : ∀ w ∈ Ioi c, |F w - w| ≤ M := fun w hw =>
    abs_sub_le_of_tendsto_comp hM (hlim w hw)
  intro a ha b hb hab
  by_contra hle
  have hlt : F b < F a := lt_of_le_of_ne (not_lt.1 hle) fun h => (ne_of_lt hab) (hinj ha hb h.symm)
  set B : ℝ := max b (F a + M) + 1 with hB
  have hbB : b < B := by rw [hB]; linarith [le_max_left b (F a + M)]
  have hBc : B ∈ Ioi c := lt_trans hb hbB
  have hFB : F a < F B := by
    have := hdisp B hBc
    rw [abs_le] at this
    linarith [le_max_right b (F a + M)]
  set c' : ℝ := (c + a) / 2 with hc'
  have hc'a : c' < a := by rw [hc']; linarith [show c < a from ha]
  have hsub : Ioo c' (B + 1) ⊆ Ioi c := fun t ht => by
    show c < t
    linarith [ht.1, show c < a from ha]
  have hmem : ∀ t, a ≤ t → t ≤ B → t ∈ Ioo c' (B + 1) := fun t h1 h2 => ⟨by linarith, by linarith⟩
  rcases ContinuousOn.strictMonoOn_of_injOn_Ioo (by linarith) (hcont.mono hsub) (hinj.mono hsub) with hm | ha'
  · exact absurd (hm (hmem a le_rfl (by linarith)) (hmem b hab.le hbB.le) hab) (not_lt.2 hlt.le)
  · have := ha' (hmem b hab.le hbB.le) (hmem B (hab.le.trans hbB.le) le_rfl) hbB
    linarith

include hfH in
/-- **The boundary values are strictly increasing on a left half-line.** -/
theorem strictMonoOn_Iio_of_tendsto_comp (hψi : InjOn ψ H) (hfi : InjOn f U) {F : ℝ → ℝ} {c M : ℝ}
    (hlim : ∀ w ∈ Iio c, Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((F w : ℝ) : ℂ)))
    (hM : ∀ z ∈ H, ‖f (ψ z) - z‖ ≤ M) : StrictMonoOn F (Iio c) := by
  have hinj := injOn_of_tendsto_comp hψc hψd hψU hU hfd hfH hψi hfi isOpen_Iio hlim
  have hcont := continuousOn_of_tendsto_comp isOpen_Iio hlim
  have hdisp : ∀ w ∈ Iio c, |F w - w| ≤ M := fun w hw =>
    abs_sub_le_of_tendsto_comp hM (hlim w hw)
  intro a ha b hb hab
  by_contra hle
  have hlt : F b < F a := lt_of_le_of_ne (not_lt.1 hle) fun h => (ne_of_lt hab) (hinj ha hb h.symm)
  set B : ℝ := min a (F b - M) - 1 with hB
  have hBa : B < a := by rw [hB]; linarith [min_le_left a (F b - M)]
  have hBc : B ∈ Iio c := lt_trans hBa ha
  have hFB : F B < F b := by
    have := hdisp B hBc
    rw [abs_le] at this
    linarith [min_le_right a (F b - M)]
  set c' : ℝ := (b + c) / 2 with hc'
  have hbc' : b < c' := by rw [hc']; linarith [show b < c from hb]
  have hsub : Ioo (B - 1) c' ⊆ Iio c := fun t ht => by
    show t < c
    linarith [ht.2, show b < c from hb]
  have hmem : ∀ t, B ≤ t → t ≤ b → t ∈ Ioo (B - 1) c' := fun t h1 h2 => ⟨by linarith, by linarith⟩
  rcases ContinuousOn.strictMonoOn_of_injOn_Ioo (by linarith) (hcont.mono hsub) (hinj.mono hsub) with hm | ha'
  · exact absurd (hm (hmem a hBa.le hab.le) (hmem b (hBa.le.trans hab.le) le_rfl) hab) (not_lt.2 hlt.le)
  · have := ha' (hmem B le_rfl (hBa.le.trans hab.le)) (hmem a hBa.le hab.le) hBa
    linarith

end Reflect

end Lemma76G

end Sec7

end InteractingSLE
