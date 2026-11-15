import InteractingSLE.Foundations.Loewner.ConformalImageLoewner
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# The conformal image of a Loewner chain

Packet GEO-LOC (`planning/INFRA-GEO.md` §4, `Loewner/ConformalImage.lean`): Specification Aux.
lemma 8 (`source/spec/p049-096.md#aux-8`, (HD2)–(HD3)) and [Law05] §4.6.1. Let `K_t` be the hulls
of the chordal Loewner chain driven by a continuous `W` (`W 0 = 0`), `g_t = f_t + W_t` its
mapping-out functions, `A` a compact `ℍ`-hull with mapping-out function `φ = g_A`, and assume
(HD1) `closure A ∩ closure K_T = ∅`. Put `E_t = g_t(A)`, `R_t = g_{E_t}`, `a(t) = ½ hcap(φ(K_t))`.

`exists_loewner_image_of_clearance`: if moreover the centered images of `A` keep a clearance
`ρ > 0` from the driver (`ρ ≤ |f_t(a)|` for `a ∈ A`, `t ≤ T`; the uniform form of "E_t has
positive distance from the driver", (HD4)), then `φ(K_t)` is the hull at time `a(t)` of the
Loewner chain driven by a continuous `W̃` with `W̃(a(t)) = R_t(W_t)` (boundary value), and
`g̃_{a(t)} ∘ φ = R_t ∘ g_t` (HD3). The capacity clock `a` is continuous, strictly increasing,
`a(0) = 0`.

The proof verifies `IsContinuouslyGrowing` (`ConformalImageLoewner.lean`) for `t ↦ φ(K_t)`:
increments are `R_t(g_t(K_{t'} \ K_t))`, and `g_t(K_{t'} \ K_t)` lies in a small ball around
`W_t` (QuantumZipper's hull radius bound for the shifted driver); `R_t` is `48`-Lipschitz near
`W_t` (`IsMapOut.norm_sub_le_of_disjoint`). Continuity of the driver uses the flow property and
[Law05] Proposition 3.46.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

open ConformalImage

/-! ### Consequences of [Law05] Proposition 3.46 -/

/-- Far from a small hull, its mapping-out function moves points by at most the radius. -/
theorem IsMapOut.norm_sub_le_of_four_mul_le {L : Set ℂ} {g : ℂ → ℂ} (hL : IsHPHull L)
    (hg : IsMapOut L g) {x r : ℝ} (hr : 0 < r) (hLr : L ⊆ closedBall (x : ℂ) r) {w : ℂ}
    (hw : w ∈ H) (hwx : 4 * r ≤ ‖w - x‖) : ‖g w - w‖ ≤ r := by
  have h := hg.norm_sub_sub_hcap_div_le hL hr hLr hw hwx
  have hcap := HPHull.hcap_le_rad_sq ⟨L, hL⟩ hLr
  have hcap0 := HPHull.hcap_nonneg ⟨L, hL⟩
  set c := HPHull.hcap ⟨L, hL⟩
  set D := ‖w - x‖
  have hDpos : 0 < D := by linarith
  have h1 : ‖(c : ℂ) / (w - x)‖ ≤ r / 4 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcap0, div_le_iff₀ hDpos]
    nlinarith
  have h2 : 12 * r * c / D ^ 2 ≤ 3 * r / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : r ^ 2 * 16 ≤ D ^ 2 := by nlinarith
    nlinarith
  calc ‖g w - w‖ = ‖(g w - w - (c : ℂ) / (w - x)) + (c : ℂ) / (w - x)‖ := by rw [sub_add_cancel]
    _ ≤ ‖g w - w - (c : ℂ) / (w - x)‖ + ‖(c : ℂ) / (w - x)‖ := norm_add_le _ _
    _ ≤ 3 * r / 4 + r / 4 := add_le_add (h.trans h2) h1
    _ = r := by ring

/-- **Image of the neighbourhood of a small hull**: if `L ⊆ B̄(x, r)`, then
`|g_L(v) − x| ≤ |v − x| + 5r` for every `v ∈ ℍ \ L` (near `L` by a continuity argument along the
preimage of a vertical ray, far from `L` by [Law05] Proposition 3.46). -/
theorem IsMapOut.norm_sub_center_le {L : Set ℂ} {g : ℂ → ℂ} (hL : IsHPHull L)
    (hg : IsMapOut L g) {x r : ℝ} (hr : 0 < r) (hLr : L ⊆ closedBall (x : ℂ) r) {v : ℂ}
    (hv : v ∈ H \ L) : ‖g v - x‖ ≤ ‖v - x‖ + 5 * r := by
  by_cases hfar : 4 * r ≤ ‖v - x‖
  · have := hg.norm_sub_le_of_four_mul_le hL hr hLr hv.1 hfar
    calc ‖g v - x‖ = ‖(g v - v) + (v - x)‖ := by ring_nf
      _ ≤ ‖g v - v‖ + ‖v - x‖ := norm_add_le _ _
      _ ≤ ‖v - x‖ + 5 * r := by linarith
  rw [not_le] at hfar
  suffices h5 : ‖g v - x‖ ≤ 5 * r by linarith [norm_nonneg (v - x)]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨hinv, hinvd, hright, hleft⟩ := hg.exists_symm hL
  obtain ⟨C', hC'⟩ := hg.exists_norm_le hL
  set C := max C' 0 with hCdef
  have hC : ∀ z ∈ H \ L, ‖g z‖ ≤ ‖z‖ + C := fun z hz =>
    (hC' z hz).trans (by linarith [le_max_left C' 0])
  have hC0 : 0 ≤ C := le_max_right _ _
  set ζ₀ := g v with hζ₀
  have hζ₀H : ζ₀ ∈ H := hg.1.2.mapsTo hv
  set p : ℝ → ℂ := fun τ => ζ₀ + (τ : ℂ) * I with hp
  have hpH : ∀ τ : ℝ, 0 ≤ τ → p τ ∈ H := fun τ hτ => by
    show 0 < (ζ₀ + (τ : ℂ) * I).im
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    have : 0 < ζ₀.im := hζ₀H
    linarith
  have hpx : ∀ τ : ℝ, 0 ≤ τ → ‖ζ₀ - x‖ ≤ ‖p τ - x‖ := by
    intro τ hτ
    have h1 : ‖p τ - x‖ ^ 2 = ‖ζ₀ - x‖ ^ 2 + 2 * τ * ζ₀.im + τ ^ 2 := by
      simp only [hp, Complex.sq_norm, normSq_apply, sub_re, add_re, mul_re, ofReal_re, I_re,
        ofReal_im, I_im, sub_im, add_im, mul_im]
      ring
    have h2 : 0 ≤ 2 * τ * ζ₀.im + τ ^ 2 := by
      have : 0 < ζ₀.im := hζ₀H
      positivity
    nlinarith [norm_nonneg (p τ - x), norm_nonneg (ζ₀ - x)]
  set f : ℝ → ℝ := fun τ => ‖hinv (p τ) - x‖ with hf
  have hfc : ContinuousOn f (Icc 0 (4 * r + ‖ζ₀‖ + C + ‖(x : ℂ)‖)) := by
    have hpc : Continuous p := by fun_prop
    refine (continuous_norm.comp_continuousOn ?_)
    refine ContinuousOn.sub ?_ continuousOn_const
    exact hinvd.continuousOn.comp hpc.continuousOn fun τ hτ => hpH τ hτ.1
  set τ₁ := 4 * r + ‖ζ₀‖ + C + ‖(x : ℂ)‖ with hτ₁
  have hτ₁0 : 0 ≤ τ₁ := by positivity
  have hf0 : f 0 < 4 * r := by
    simp only [hf, hp, ofReal_zero, zero_mul, add_zero, hζ₀, hleft v hv]
    exact hfar
  have hf1 : 4 * r ≤ f τ₁ := by
    have hq := hright (p τ₁) (hpH τ₁ hτ₁0)
    have h1 := hC _ hq.1
    rw [hq.2] at h1
    have h2 : τ₁ - ‖ζ₀‖ ≤ ‖p τ₁‖ := by
      have h4 := norm_sub_le (p τ₁) ζ₀
      have h5 : ‖p τ₁ - ζ₀‖ = τ₁ := by
        simp only [hp, add_sub_cancel_left, norm_mul, norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hτ₁0]
      linarith
    have h3 := norm_sub_norm_le (hinv (p τ₁)) (x : ℂ)
    simp only [hf]
    linarith
  obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Icc hτ₁0 hfc ⟨hf0.le, hf1⟩
  have hq := hright (p τ) (hpH τ hτ.1)
  have hfτ' : ‖hinv (p τ) - x‖ = 4 * r := hfτ
  have hfar' : 4 * r ≤ ‖hinv (p τ) - x‖ := le_of_eq hfτ'.symm
  have hmove := hg.norm_sub_le_of_four_mul_le hL hr hLr hq.1.1 hfar'
  rw [hq.2] at hmove
  have h1 : ‖p τ - x‖ ≤ 5 * r := by
    calc ‖p τ - x‖ = ‖(p τ - hinv (p τ)) + (hinv (p τ) - x)‖ := by ring_nf
      _ ≤ ‖p τ - hinv (p τ)‖ + ‖hinv (p τ) - x‖ := norm_add_le _ _
      _ ≤ r + 4 * r := add_le_add hmove (le_of_eq hfτ')
      _ = 5 * r := by ring
  have := hpx τ hτ.1
  linarith

/-- The boundary value of a mapping-out function at a real point with clearance `ρ`, and the
`48`-Lipschitz bound towards it. -/
theorem IsMapOut.norm_sub_limUnder_le {E : Set ℂ} {g : ℂ → ℂ} (hE : IsHPHull E)
    (hg : IsMapOut E g) {y ρ : ℝ} (hd : Disjoint (ball (y : ℂ) ρ) E) {ζ : ℂ}
    (hζ : ζ ∈ ball (y : ℂ) (ρ / 2) ∩ H) :
    ‖g ζ - limUnder (𝓝[H] (y : ℂ)) g‖ ≤ 48 * ‖ζ - y‖ := by
  obtain ⟨G, -, hGS, -, -, hLip, hGlim⟩ := hg.exists_reflection hE hd
  have hρ : 0 < ρ := by
    have := mem_ball.1 hζ.1
    linarith [dist_nonneg (x := ζ) (y := (y : ℂ))]
  have hyb : (y : ℂ) ∈ ball (y : ℂ) (ρ / 2) := mem_ball_self (by positivity)
  have hlim := hGlim y hyb (by simp)
  have hnhds : 𝓝[ball (y : ℂ) (ρ / 2) ∩ H] (y : ℂ) = 𝓝[H] (y : ℂ) :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hyb))
  rw [hnhds] at hlim
  have hne : (𝓝[H] (y : ℂ)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    exact closure_mono inter_subset_right
      (subset_closure_ball_inter_H (y : ℂ) 1 ⟨mem_ball_self one_pos, show (0 : ℝ) ≤ (y : ℂ).im
        by simp⟩)
  rw [hlim.limUnder_eq, ← hGS hζ]
  have := hLip (y : ℂ) ⟨hyb, show (0 : ℝ) ≤ (y : ℂ).im by simp⟩ ζ
    ⟨hζ.1, show (0 : ℝ) ≤ ζ.im from le_of_lt hζ.2⟩
  exact this

/-- The boundary value of a mapping-out function at a real point with clearance is real, and is
the limit from `ℍ`. -/
theorem IsMapOut.tendsto_limUnder_of_disjoint {E : Set ℂ} {g : ℂ → ℂ} (hE : IsHPHull E)
    (hg : IsMapOut E g) {y ρ : ℝ} (hρ : 0 < ρ) (hd : Disjoint (ball (y : ℂ) ρ) E) :
    (limUnder (𝓝[H] (y : ℂ)) g).im = 0 ∧
      Tendsto g (𝓝[H] (y : ℂ)) (𝓝 (limUnder (𝓝[H] (y : ℂ)) g)) := by
  obtain ⟨G, -, -, -, hGreal, -, hGlim⟩ := hg.exists_reflection hE hd
  have hyb : (y : ℂ) ∈ ball (y : ℂ) (ρ / 2) := mem_ball_self (by positivity)
  have hlim := hGlim y hyb (by simp)
  have hnhds : 𝓝[ball (y : ℂ) (ρ / 2) ∩ H] (y : ℂ) = 𝓝[H] (y : ℂ) :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hyb))
  rw [hnhds] at hlim
  have hne : (𝓝[H] (y : ℂ)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    exact closure_mono inter_subset_right
      (subset_closure_ball_inter_H (y : ℂ) 1 ⟨mem_ball_self one_pos, show (0 : ℝ) ≤ (y : ℂ).im
        by simp⟩)
  rw [hlim.limUnder_eq]
  exact ⟨hGreal y hyb (by simp), hlim⟩

namespace ConformalImage

/-! ### The image family -/

/-- The uncentered Loewner map `g_t = f_t + W_t`. -/
def gmap (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ := QuantumZipper.fwdMap W t z + W t

/-- The image hulls `φ(K_t)`. -/
def imageHull (W : ℝ → ℝ) (φ : ℂ → ℂ) (t : ℝ) : Set ℂ := φ '' QuantumZipper.fwdHull W t

/-- The moving obstacle `E_t = g_t(A)`. -/
def obstacle (W : ℝ → ℝ) (A : Set ℂ) (t : ℝ) : Set ℂ := gmap W t '' A

/-- The driver of the image chain: the boundary value `R_t(W_t)` of `R_t = g_{E_t}`. -/
def bdryDriver (W : ℝ → ℝ) (A : Set ℂ) (t : ℝ) : ℝ :=
  (limUnder (𝓝[H] (W t : ℂ)) (mapOut (obstacle W A t))).re

/-- Hypotheses: Specification Aux. lemma 8 with (HD1), plus a uniform clearance `ρ` of the
centered images of `A` from the driver. -/
structure ImageHyp (W : ℝ → ℝ) (A : Set ℂ) (φ : ℂ → ℂ) (T ρ : ℝ) : Prop where
  continuous : Continuous W
  zero : W 0 = 0
  nonneg : 0 ≤ T
  isHPHull : IsHPHull A
  isMapOut : IsMapOut A φ
  disjoint : Disjoint (closure A) (closure (QuantumZipper.fwdHull W T))
  pos : 0 < ρ
  clearance : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, ρ ≤ ‖QuantumZipper.fwdMap W t a‖

namespace ImageHyp

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T ρ : ℝ}

theorem isHPHull_K (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsHPHull (QuantumZipper.fwdHull W t) := isHPHull_fwdHull h.continuous ht.1

theorem isMapOut_g (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsMapOut (QuantumZipper.fwdHull W t) (gmap W t) := isMapOut_fwdMap h.continuous h.zero ht.1

theorem K_mono {s t : ℝ} (hst : s ≤ t) :
    QuantumZipper.fwdHull W s ⊆ QuantumZipper.fwdHull W t :=
  (QuantumZipper.fwdHull_mono (W := W)).1 hst

theorem disjoint_t (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Disjoint (closure A) (closure (QuantumZipper.fwdHull W t)) :=
  h.disjoint.mono_right (closure_mono (K_mono ht.2))

theorem isHPHull_image (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsHPHull (imageHull W φ t) :=
  h.isMapOut.isHPHull_image_of_disjoint_closure h.isHPHull (h.isHPHull_K ht) (h.disjoint_t ht)

theorem isHPHull_obstacle (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsHPHull (obstacle W A t) :=
  (h.isMapOut_g ht).isHPHull_image_of_disjoint_closure (h.isHPHull_K ht) h.isHPHull
    (h.disjoint_t ht).symm

/-- (HD3), first identity: `g_{φ(K_t)} ∘ φ = R_t ∘ g_t` off `A ∪ K_t`. -/
theorem eqOn_comp (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    EqOn (mapOut (imageHull W φ t) ∘ φ) (mapOut (obstacle W A t) ∘ gmap W t)
      (H \ (A ∪ QuantumZipper.fwdHull W t)) :=
  IsMapOut.comp_eqOn_comp_of_disjoint_closure h.isHPHull (h.isHPHull_K ht) (h.disjoint_t ht)
    h.isMapOut (h.isMapOut_g ht) (isMapOut_mapOut (h.isHPHull_image ht))
    (isMapOut_mapOut (h.isHPHull_obstacle ht))

theorem disjoint_ball_obstacle (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Disjoint (ball (W t : ℂ) ρ) (obstacle W A t) := by
  rw [Set.disjoint_left]
  rintro ζ hζ ⟨a, ha, rfl⟩
  rw [mem_ball, dist_eq_norm] at hζ
  have := h.clearance t ht a ha
  simp only [gmap, add_sub_cancel_right] at hζ
  linarith

theorem bdryDriver_eq (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ((bdryDriver W A t : ℝ) : ℂ) = limUnder (𝓝[H] (W t : ℂ)) (mapOut (obstacle W A t)) := by
  have := ((isMapOut_mapOut (h.isHPHull_obstacle ht)).tendsto_limUnder_of_disjoint
    (h.isHPHull_obstacle ht) h.pos (h.disjoint_ball_obstacle ht)).1
  apply Complex.ext <;> simp [bdryDriver, this]

/-- `R_t` is `48`-Lipschitz towards its boundary value near `W_t`. -/
theorem norm_R_sub_le (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) {ζ : ℂ}
    (hζ : ζ ∈ ball (W t : ℂ) (ρ / 2) ∩ H) :
    ‖mapOut (obstacle W A t) ζ - bdryDriver W A t‖ ≤ 48 * ‖ζ - W t‖ := by
  rw [h.bdryDriver_eq ht]
  exact (isMapOut_mapOut (h.isHPHull_obstacle ht)).norm_sub_limUnder_le
    (h.isHPHull_obstacle ht) (h.disjoint_ball_obstacle ht) hζ

theorem notMem_A_of_mem_K (h : ImageHyp W A φ T ρ) {t : ℝ} (ht : t ∈ Icc 0 T) {z : ℂ}
    (hz : z ∈ QuantumZipper.fwdHull W t) : z ∉ A := fun hzA =>
  Set.disjoint_left.1 (h.disjoint_t ht) (subset_closure hzA) (subset_closure hz)

/-- The image increments: `φ(K_t) \ φ(K_s) = φ(K_t \ K_s)`. -/
theorem imageHull_diff (h : ImageHyp W A φ T ρ) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) :
    imageHull W φ t \ imageHull W φ s =
      φ '' (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s) := by
  ext y
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hy⟩
    exact ⟨z, ⟨hz, fun hzs => hy ⟨z, hzs, rfl⟩⟩, rfl⟩
  · rintro ⟨z, ⟨hzt, hzs⟩, rfl⟩
    refine ⟨⟨z, hzt, rfl⟩, ?_⟩
    rintro ⟨z', hz', hzz'⟩
    have hz1 : z ∈ H \ A := ⟨(h.isHPHull_K ht).1 hzt, h.notMem_A_of_mem_K ht hzt⟩
    have hz2 : z' ∈ H \ A := ⟨(h.isHPHull_K hs).1 hz', h.notMem_A_of_mem_K hs hz'⟩
    exact hzs (h.isMapOut.1.2.injOn hz2 hz1 hzz' ▸ hz')

/-- The image increments are `R_s(g_s(K_t \ K_s))`. -/
theorem image_inc_eq (h : ImageHyp W A φ T ρ) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) :
    mapOut (imageHull W φ s) '' (imageHull W φ t \ imageHull W φ s) =
      mapOut (obstacle W A s) '' (gmap W s '' (QuantumZipper.fwdHull W t \
        QuantumZipper.fwdHull W s)) := by
  rw [h.imageHull_diff hs ht, image_image, image_image]
  refine image_congr fun z hz => ?_
  exact h.eqOn_comp hs ⟨(h.isHPHull_K ht).1 hz.1,
    fun hz' => hz'.elim (h.notMem_A_of_mem_K ht hz.1) hz.2⟩

theorem exists_uniform (h : ImageHyp W A φ T ρ) {μ : ℝ} (hμ : 0 < μ) :
    ∃ δ > 0, ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, |u - v| ≤ δ → |W u - W v| ≤ μ := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous (h.continuous.continuousOn
    (s := Icc (0 : ℝ) T))
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff_le.1 huc μ hμ
  exact ⟨δ, hδ, fun u hu v hv huv => by
    have := hd u hu v hv (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this⟩

/-- **Local growth of the original chain**, uniformly: `g_s(K_t \ K_s) ⊆ B̄(W_s, η)` for
`0 ≤ t − s ≤ δ` (QuantumZipper's domain Markov property and hull-radius bound
`|K| ≤ M + 3√h` for the shifted driver). -/
theorem exists_gmap_diff_subset (h : ImageHyp W A φ T ρ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → t - s ≤ δ →
      gmap W s '' (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s) ⊆
        closedBall (W s : ℂ) η := by
  obtain ⟨δ₁, hδ₁, hW⟩ := h.exists_uniform (half_pos hη)
  refine ⟨min δ₁ ((η / 6) ^ 2), lt_min hδ₁ (by positivity), ?_⟩
  rintro s hs t ht hst hδ _ ⟨z, ⟨hzt, hzs⟩, rfl⟩
  rcases eq_or_lt_of_le hst with heq | hlt
  · subst heq; exact absurd hzt hzs
  set hh := t - s with hhh
  have hhpos : 0 < hh := sub_pos.2 hlt
  set V : ℝ → ℝ := fun r => W (s + r) - W s with hV
  have hVc : Continuous V := by have := h.continuous; fun_prop
  have hkey := QuantumZipper.fwdHull_add_diff h.continuous hs.1 hhpos.le
  rw [show s + hh = t by ring] at hkey
  have hmem : z ∈ QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s := ⟨hzt, hzs⟩
  rw [hkey] at hmem
  have hbound : ∀ r ∈ Icc (0 : ℝ) hh, |V r| ≤ η / 2 := by
    intro r hr
    refine hW (s + r) ⟨by linarith [hs.1, hr.1], by linarith [ht.2, hr.2]⟩ s hs ?_
    rw [show s + r - s = r by ring, abs_of_nonneg hr.1]
    linarith [hr.2, min_le_left δ₁ ((η / 6) ^ 2)]
  have hsub := QuantumZipper.CaraR.fwdHull_subset_closedBall hVc hhpos hbound hmem.2
  rw [mem_closedBall, dist_zero_right] at hsub
  have hsq : Real.sqrt hh ≤ η / 6 := by
    rw [show η / 6 = Real.sqrt ((η / 6) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by linarith [min_le_right δ₁ ((η / 6) ^ 2)])
  rw [mem_closedBall, dist_eq_norm]
  simp only [gmap, add_sub_cancel_right]
  linarith

/-- **Local growth of the image chain** at the driver `R_s(W_s)`. -/
theorem growth_image (h : ImageHyp W A φ T ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → t - s ≤ δ →
      mapOut (imageHull W φ s) '' (imageHull W φ t \ imageHull W φ s) ⊆
        closedBall (bdryDriver W A s : ℂ) ε := by
  set η := min (ρ / 4) (ε / 48) with hηdef
  have hη : 0 < η := lt_min (by linarith [h.pos]) (by positivity)
  obtain ⟨δ, hδ, hg⟩ := h.exists_gmap_diff_subset hη
  refine ⟨δ, hδ, fun s hs t ht hst hd => ?_⟩
  rw [h.image_inc_eq hs ht]
  rintro _ ⟨ζ, ⟨z, hz, rfl⟩, rfl⟩
  have hζ := hg s hs t ht hst hd ⟨z, hz, rfl⟩
  have hζH : gmap W s z ∈ H :=
    (h.isMapOut_g hs).1.2.mapsTo ⟨(h.isHPHull_K ht).1 hz.1, hz.2⟩
  rw [mem_closedBall, dist_eq_norm] at hζ
  have hζb : gmap W s z ∈ ball (W s : ℂ) (ρ / 2) ∩ H := by
    refine ⟨?_, hζH⟩
    rw [mem_ball, dist_eq_norm]
    linarith [min_le_left (ρ / 4) (ε / 48), h.pos]
  have := h.norm_R_sub_le hs hζb
  rw [mem_closedBall, dist_eq_norm]
  linarith [min_le_right (ρ / 4) (ε / 48)]

theorem isHPHull_inc (h : ImageHyp W A φ T ρ) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hst : s ≤ t) : IsHPHull (inc (imageHull W φ) s t) :=
  (isMapOut_mapOut (h.isHPHull_image hs)).isHPHull_image (h.isHPHull_image hs)
    (h.isHPHull_image ht) (image_mono (K_mono hst))

theorem eqOn_mapOut_image (h : ImageHyp W A φ T ρ) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    EqOn (mapOut (imageHull W φ t))
      (mapOut (inc (imageHull W φ) s t) ∘ mapOut (imageHull W φ s)) (H \ imageHull W φ t) :=
  (isMapOut_mapOut (h.isHPHull_image ht)).eqOn (h.isHPHull_image ht)
    ((isMapOut_mapOut (h.isHPHull_image hs)).comp (h.isHPHull_image hs) (h.isHPHull_image ht)
      (image_mono (K_mono hst)) (isMapOut_mapOut (h.isHPHull_inc hs ht hst)))

/-- **Uniform continuity of the image driver** `t ↦ R_t(W_t)`: compare `R_{s'}` at
`W_{s'} + iη` with `g_{L} ∘ R_s ∘ g_s ∘ g_{s'}⁻¹` (flow property), where `L` is the image
increment; QuantumZipper's bound `|f_h(z) − z| ≤ 24M + 8√h` for the shifted chain, the
Lipschitz bound for `R_s` near `W_s` and the bound for `g_L` near `L`. -/
theorem abs_bdryDriver_sub_le (h : ImageHyp W A φ T ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc 0 T, ∀ s' ∈ Icc 0 T, s ≤ s' → s' - s ≤ δ →
      |bdryDriver W A s' - bdryDriver W A s| ≤ ε := by
  set ε₁ := ε / 20 with hε₁
  obtain ⟨δk, hδk, hk⟩ := h.growth_image (show 0 < ε₁ by positivity)
  set μ := min (ε / 4608) (ρ / 192) with hμ
  have hμpos : 0 < μ := lt_min (by positivity) (by linarith [h.pos])
  obtain ⟨δW, hδW, hW⟩ := h.exists_uniform hμpos
  set q := min (ε / 1536) (ρ / 64) with hq
  have hqpos : 0 < q := lt_min (by positivity) (by linarith [h.pos])
  refine ⟨min δk (min δW (q ^ 2)), lt_min hδk (lt_min hδW (by positivity)), ?_⟩
  intro s hs s' hs' hss' hd
  rcases eq_or_lt_of_le hss' with heq | hlt
  · subst heq; simp [hε.le]
  have hρ := h.pos
  set hh := s' - s with hhh
  have hhpos : 0 < hh := sub_pos.2 hlt
  set η := min (ρ / 8) (ε / 384) with hηdef
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hW' := h.continuous
  have hηI : (η : ℂ) * I ∈ H := by
    show 0 < ((η : ℂ) * I).im
    simpa using hηpos
  set z := QuantumZipper.fwdMapInv W s' ((η : ℂ) * I) with hz
  have hzK : z ∈ H \ QuantumZipper.fwdHull W s' :=
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW' h.zero hs'.1 hηI
  have hfz : QuantumZipper.fwdMap W s' z = (η : ℂ) * I :=
    QuantumZipper.RS.fwdMap_fwdMapInv hW' h.zero hs'.1 hηI
  set ζ := (W s' : ℂ) + (η : ℂ) * I with hζ
  have hgz : gmap W s' z = ζ := by simp only [gmap, hfz, hζ]; ring
  have hζb : ζ ∈ ball (W s' : ℂ) (ρ / 2) ∩ H := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, hζ, add_sub_cancel_left, norm_mul, norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
      linarith [min_le_left (ρ / 8) (ε / 384)]
    · show 0 < ζ.im
      simpa [hζ] using hηpos
  have hzA : z ∉ A := by
    intro hzA
    have hmem : gmap W s' z ∈ obstacle W A s' := ⟨z, hzA, rfl⟩
    rw [hgz] at hmem
    exact Set.disjoint_left.1 (h.disjoint_ball_obstacle hs') (ball_subset_ball (by linarith)
      hζb.1) hmem
  have hzs : z ∉ QuantumZipper.fwdHull W s := fun hz' => hzK.2 (K_mono hss' hz')
  have hzAK' : z ∈ H \ (A ∪ QuantumZipper.fwdHull W s') :=
    ⟨hzK.1, fun h' => h'.elim hzA hzK.2⟩
  have hzAK : z ∈ H \ (A ∪ QuantumZipper.fwdHull W s) :=
    ⟨hzK.1, fun h' => h'.elim hzA hzs⟩
  -- the image point `φ z`
  have hφz : φ z ∈ H \ imageHull W φ s' := by
    refine ⟨h.isMapOut.1.2.mapsTo ⟨hzK.1, hzA⟩, ?_⟩
    rintro ⟨z'', hz'', hzz⟩
    have := h.isMapOut.1.2.injOn ⟨(h.isHPHull_K hs').1 hz'', h.notMem_A_of_mem_K hs' hz''⟩
      ⟨hzK.1, hzA⟩ hzz
    exact hzK.2 (this ▸ hz'')
  have hid1 := h.eqOn_comp hs' hzAK'
  have hid2 := h.eqOn_mapOut_image hs hs' hss' hφz
  have hid3 := h.eqOn_comp hs hzAK
  simp only [Function.comp_apply] at hid1 hid2 hid3
  rw [hgz] at hid1
  set v := mapOut (obstacle W A s) (gmap W s z) with hv
  -- bound (1): at `s'`
  have hb1 := h.norm_R_sub_le hs' hζb
  have hζW : ‖ζ - W s'‖ = η := by
    rw [hζ, add_sub_cancel_left, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hηpos]
  rw [hζW] at hb1
  -- bound (2): the point `ξ = f_s(z)` is close to `iη`
  set V : ℝ → ℝ := fun r => W (s + r) - W s with hV
  have hVc : Continuous V := by fun_prop
  have hV0 : V 0 = 0 := by simp [hV]
  set ξ := QuantumZipper.fwdMap W s z with hξ
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs'.1 hzK.1 hzK.2
  have hflow := QuantumZipper.fwdMap_add hW' hzK.1 hs.1 hhpos.le
    (by rw [show s + hh = s' by ring]; exact ⟨u, hu⟩)
  rw [show s + hh = s' by ring, hfz] at hflow
  have hkey := QuantumZipper.fwdHull_add_diff hW' hs.1 hhpos.le
  rw [show s + hh = s' by ring] at hkey
  have hgsH : gmap W s z ∈ H := (h.isMapOut_g hs).1.2.mapsTo ⟨hzK.1, hzs⟩
  have hξH : ξ ∈ H \ QuantumZipper.fwdHull V hh := by
    refine ⟨?_, fun hξK => ?_⟩
    · show 0 < ξ.im
      have : 0 < (gmap W s z).im := hgsH
      simpa [gmap, hξ] using this
    · have : z ∈ QuantumZipper.fwdHull W s' \ QuantumZipper.fwdHull W s := by
        rw [hkey]; exact ⟨⟨hzK.1, hzs⟩, hξK⟩
      exact hzK.2 this.1
  have hbound : ∀ r ∈ Icc (0 : ℝ) hh, |V r| ≤ μ := by
    intro r hr
    refine hW (s + r) ⟨by linarith [hs.1, hr.1], by linarith [hs'.2, hr.2]⟩ s hs ?_
    rw [show s + r - s = r by ring, abs_of_nonneg hr.1]
    have h1 := min_le_right δk (min δW (q ^ 2))
    have h2 := min_le_left δW (q ^ 2)
    linarith [hr.2]
  have hcore := norm_fwdMap_sub_self_le hVc hV0 hhpos.le hbound hξH ⟨hhpos.le, le_rfl⟩
  rw [← hflow] at hcore
  have hdq : hh ≤ q ^ 2 := by
    have h1 := min_le_right δk (min δW (q ^ 2))
    have h2 := min_le_right δW (q ^ 2)
    linarith
  have hdW : hh ≤ δW := by
    have h1 := min_le_right δk (min δW (q ^ 2))
    have h2 := min_le_left δW (q ^ 2)
    linarith
  have hsq : Real.sqrt hh ≤ q := by
    rw [show q = Real.sqrt (q ^ 2) from (Real.sqrt_sq hqpos.le).symm]
    exact Real.sqrt_le_sqrt hdq
  have hξn : ‖ξ‖ ≤ η + 24 * μ + 8 * q := by
    have h1 : ‖ξ‖ ≤ ‖(η : ℂ) * I‖ + ‖(η : ℂ) * I - ξ‖ := by
      have := norm_sub_le ((η : ℂ) * I) ((η : ℂ) * I - ξ)
      rwa [sub_sub_cancel] at this
    have h2 : ‖(η : ℂ) * I‖ = η := by
      rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    linarith
  have hgξ : gmap W s z - W s = ξ := by simp [gmap, hξ]
  -- bound (3): at `s`
  have hgsb : gmap W s z ∈ ball (W s : ℂ) (ρ / 2) ∩ H := by
    refine ⟨?_, hgsH⟩
    rw [mem_ball, dist_eq_norm, hgξ]
    linarith [min_le_left (ρ / 8) (ε / 384), min_le_right (ε / 4608) (ρ / 192),
      min_le_right (ε / 1536) (ρ / 64)]
  have hb3 := h.norm_R_sub_le hs hgsb
  rw [hgξ] at hb3
  -- bound (4): the increment hull
  have hLsub := hk s hs s' hs' hss' (by linarith [min_le_left δk (min δW (q ^ 2))])
  have hvL : v ∈ H \ inc (imageHull W φ) s s' := by
    rw [← hid3]
    have hG := isMapOut_mapOut (h.isHPHull_image hs)
    have hφzs : φ z ∈ H \ imageHull W φ s := ⟨hφz.1, fun h' => hφz.2 (image_mono
      (K_mono hss') h')⟩
    refine ⟨hG.1.2.mapsTo hφzs, ?_⟩
    rintro ⟨y, hy, hyz⟩
    have := hG.1.2.injOn ⟨(h.isHPHull_image hs').1 hy.1, hy.2⟩ hφzs hyz
    exact hφz.2 (this ▸ hy.1)
  have hb4 := (isMapOut_mapOut (h.isHPHull_inc hs hs' hss')).norm_sub_center_le
    (h.isHPHull_inc hs hs' hss') (show 0 < ε₁ by positivity) hLsub hvL
  -- combine
  have hcomb : mapOut (inc (imageHull W φ) s s') v = mapOut (obstacle W A s') ζ := by
    rw [← hid3, ← hid2, hid1]
  rw [hcomb] at hb4
  have hfinal : ‖((bdryDriver W A s' : ℝ) : ℂ) - (bdryDriver W A s : ℝ)‖ ≤ ε := by
    calc ‖((bdryDriver W A s' : ℝ) : ℂ) - (bdryDriver W A s : ℝ)‖
        = ‖((bdryDriver W A s' : ℂ) - mapOut (obstacle W A s') ζ) +
            (mapOut (obstacle W A s') ζ - bdryDriver W A s)‖ := by ring_nf
      _ ≤ ‖(bdryDriver W A s' : ℂ) - mapOut (obstacle W A s') ζ‖ +
            ‖mapOut (obstacle W A s') ζ - bdryDriver W A s‖ := norm_add_le _ _
      _ ≤ 48 * η + (48 * ‖ξ‖ + 5 * ε₁) := by
          rw [← norm_neg, neg_sub]
          exact add_le_add hb1 (hb4.trans (by linarith))
      _ ≤ ε := by
          have h1 : η ≤ ε / 384 := min_le_right _ _
          have h2 : μ ≤ ε / 4608 := min_le_left _ _
          have h3 : q ≤ ε / 1536 := min_le_left _ _
          rw [hε₁]
          nlinarith
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hfinal
  exact hfinal

theorem continuousOn_bdryDriver (h : ImageHyp W A φ T ρ) :
    ContinuousOn (bdryDriver W A) (Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hd⟩ := h.abs_bdryDriver_sub_le (half_pos hε)
  refine ⟨δ, hδ, fun s hs hst => ?_⟩
  rw [Real.dist_eq] at hst ⊢
  rcases le_total t s with hle | hle
  · have := hd t ht s hs hle (by linarith [le_abs_self (s - t)])
    linarith
  · have := hd s hs t ht hle (by linarith [neg_abs_le (s - t)])
    rw [abs_sub_comm]
    linarith

theorem K_zero (h : ImageHyp W A φ T ρ) : QuantumZipper.fwdHull W 0 = ∅ := by
  have h0 := hcap_fwdHull h.continuous h.zero (le_refl 0)
  rw [mul_zero] at h0
  exact (HPHull.hcap_eq_zero_iff _).1 h0

theorem diff_nonempty (h : ImageHyp W A φ T ρ) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hst : s < t) : (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s).Nonempty := by
  by_contra hne
  have hsub : QuantumZipper.fwdHull W t ⊆ QuantumZipper.fwdHull W s := fun z hz =>
    by_contra fun hz' => hne ⟨z, hz, hz'⟩
  have heq : QuantumZipper.fwdHull W t = QuantumZipper.fwdHull W s :=
    Subset.antisymm hsub (K_mono hst.le)
  have h1 := hcap_fwdHull h.continuous h.zero ht.1
  have h2 := hcap_fwdHull h.continuous h.zero hs.1
  have h3 : HPHull.hcap ⟨QuantumZipper.fwdHull W t, isHPHull_fwdHull h.continuous ht.1⟩ =
      HPHull.hcap ⟨QuantumZipper.fwdHull W s, isHPHull_fwdHull h.continuous hs.1⟩ :=
    HPHull.hcap_congr heq
  linarith

/-- The image family `t ↦ φ(K_t)` is continuously growing, with driver `t ↦ R_t(W_t)`. -/
theorem isContinuouslyGrowing (h : ImageHyp W A φ T ρ) :
    IsContinuouslyGrowing (imageHull W φ) (bdryDriver W A) T where
  isHPHull := fun _ ht => h.isHPHull_image ht
  zero := by simp [imageHull, h.K_zero]
  mono := fun _ _ _ _ hst => image_mono (K_mono hst)
  strict := fun _ hs _ ht hst => by
    rw [h.imageHull_diff hs ht]
    exact (h.diff_nonempty hs ht hst).image _
  continuousOn := h.continuousOn_bdryDriver
  growth := fun _ hε => h.growth_image hε

end ImageHyp

end ConformalImage

open ConformalImage in
/-- **The conformal image of a Loewner chain** (Specification Aux. lemma 8, (HD2)–(HD3);
[Law05] §4.6.1), under a uniform clearance of the obstacle from the driver.

Let `W` be continuous with `W 0 = 0`, `K_t = fwdHull W t`, `g_t = f_t + W_t`, `A` a compact
`ℍ`-hull with mapping-out function `φ`, (HD1) `closure A ∩ closure K_T = ∅`, and suppose
`ρ ≤ |f_t(a)|` for all `a ∈ A`, `t ∈ [0, T]` (`ρ > 0`). Then there are a capacity clock `a`
(continuous, strictly increasing on `[0, T]`, `a 0 = 0`, `a t = ½ hcap(φ(K_t))`) and a continuous
driver `W'` such that for every `t ∈ [0, T]`:
* `φ(K_t)` is the Loewner hull of `W'` at time `a t`;
* for every mapping-out function `R` of `E_t = g_t(A)`: `g̃_{a(t)} ∘ φ = R ∘ g_t` off `A ∪ K_t`
  (with `g̃_σ = f̃_σ + W'_σ`), and `W'(a t) = R(W_t)` as the boundary limit of `R` at `W_t`. -/
theorem exists_loewner_image_of_clearance {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (QuantumZipper.fwdHull W T))) {ρ : ℝ} (hρ : 0 < ρ)
    (hclr : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, ρ ≤ ‖QuantumZipper.fwdMap W t a‖) :
    ∃ (a : ℝ → ℝ) (W' : ℝ → ℝ), Continuous W' ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 T) ∧
      ContinuousOn a (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        (∃ hK : IsHPHull (φ '' QuantumZipper.fwdHull W t), a t = HPHull.hcap ⟨_, hK⟩ / 2) ∧
        QuantumZipper.fwdHull W' (a t) = φ '' QuantumZipper.fwdHull W t ∧
        ∀ R : ℂ → ℂ, IsMapOut ((fun z => QuantumZipper.fwdMap W t z + W t) '' A) R →
          (∀ z ∈ H \ (A ∪ QuantumZipper.fwdHull W t),
            QuantumZipper.fwdMap W' (a t) (φ z) + W' (a t) =
              R (QuantumZipper.fwdMap W t z + W t)) ∧
          Tendsto R (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) := by
  have h : ImageHyp W A φ T ρ := ⟨hW, hW0, hT, hA, hφ, hd, hρ, hclr⟩
  have hg := h.isContinuouslyGrowing
  refine ⟨cap (imageHull W φ), IsContinuouslyGrowing.drv (imageHull W φ) (bdryDriver W A) T,
    hg.continuous_drv hT,
    hg.cap_zero hT, hg.strictMonoOn_cap, hg.continuousOn_cap, fun t ht => ?_⟩
  obtain ⟨hU, hhull, hmap⟩ := hg.loewner hT ht
  have hobs := h.isHPHull_obstacle ht
  refine ⟨⟨h.isHPHull_image ht, by rw [cap, hcapSet_eq (h.isHPHull_image ht)]; rfl⟩, hhull,
    fun R hR => ⟨fun z hz => ?_, ?_⟩⟩
  · have hzA : z ∈ H \ A := ⟨hz.1, fun h' => hz.2 (Or.inl h')⟩
    have hzK : z ∈ H \ QuantumZipper.fwdHull W t := ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩
    have hφz : φ z ∈ H \ imageHull W φ t := by
      refine ⟨hφ.1.2.mapsTo hzA, ?_⟩
      rintro ⟨z'', hz'', hzz⟩
      have := hφ.1.2.injOn ⟨(h.isHPHull_K ht).1 hz'', h.notMem_A_of_mem_K ht hz''⟩ hzA hzz
      exact hzK.2 (this ▸ hz'')
    rw [hmap (φ z) hφz]
    have h1 := h.eqOn_comp ht hz
    simp only [Function.comp_apply] at h1
    rw [h1]
    have hgz : gmap W t z ∈ H \ obstacle W A t := by
      refine ⟨(h.isMapOut_g ht).1.2.mapsTo hzK, ?_⟩
      rintro ⟨a', ha', haz⟩
      have := (h.isMapOut_g ht).1.2.injOn ⟨hA.1 ha', fun h' => h.notMem_A_of_mem_K ht h' ha'⟩
        hzK haz
      exact hzA.2 (this ▸ ha')
    exact (isMapOut_mapOut hobs).eqOn hobs hR hgz
  · rw [hU, h.bdryDriver_eq ht]
    have hT' := ((isMapOut_mapOut hobs).tendsto_limUnder_of_disjoint hobs hρ
      (h.disjoint_ball_obstacle ht)).2
    refine hT'.congr' ?_
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (W t : ℂ) hρ)] with ζ hζ
    exact (isMapOut_mapOut hobs).eqOn hobs hR
      ⟨hζ.1, fun hmem => Set.disjoint_left.1 (h.disjoint_ball_obstacle ht) hζ.2 hmem⟩

end InteractingSLE
