/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.ConformalImageFullAux8

/-!
# The image of a Loewner chain under a real Möbius map that moves `∞`

Packet PROVE-SEC5-F (the coordinate change of `CounterflowSegmentRestartStatement`, obstruction (ii) of
`planning/handoffs/PROVE-SEC5-E.md`). Lemma 5.7's proof (specification p. 138) and Proposition 5.9's proof (p. 143)
map the remaining component of the strip, after an initial segment of another curve, to a half-plane in which the
explored curve's tip goes to `∞`. In the counterflow's own chart the old target `∞` then moves to a finite boundary
point: the change of coordinates is not a hydrodynamic mapping-out function, and Specification Aux. lemma 8
(`ConformalImageFull.exists_loewner_image`) does not apply to it directly. It factors through real Möbius maps
`m(z) = (az + b)/(cz + d)` (`ad − bc > 0`, `c ≠ 0`) and one mapping-out function. This file treats the Möbius
factor.

**Main result** (`exists_loewner_mobius_image`). Let `W` be continuous with `W 0 = 0`, `K_t` its Loewner hulls,
`g_t = f_t + W_t`, and let the pole `p = −d/c ≠ 0` of `m` keep a positive distance from `K_T`. Then `t ↦ m(K_t)`,
`t ∈ [0, T]`, is a Loewner chain after the capacity time change `σ(t) = ½ hcap(m(K_t))`: there is a continuous `W̃`
with `K̃_{σ(t)} = m(K_t)`, and

  `g̃_{σ(t)}(m(z)) = α_t − κ_t / (g_t(z) − P_t)`  for `z ∈ ℍ \ K_t`,  `W̃(σ(t)) = α_t − κ_t / (W_t − P_t)`,

where `P_t = g_t(p)` is the boundary value of `g_t` at the pole, `κ_t > 0` and `α_t` is real ([Law05] §4.6, the
target change of [SW05]).

**Proof.** `g̃ ∘ m ∘ g_t⁻¹` is a holomorphic bijection of `ℍ`, hence a real Möbius map (QuantumZipper's
classification of `Aut ℍ`); its pole is `P_t` because `g̃(m(z)) → ∞` as `z → p`. Comparing the residues at the pole
(`g̃(w) − w → 0` at `∞`) with the `48`-Lipschitz bound of `g_t` near `p` gives `κ_t ≤ 48 (ad − bc)/c²`; the
continuity of `t ↦ P_t` and `P_t ≠ W_t` give a uniform clearance `|W_t − P_t| ≥ ρ`. The image family is then
continuously growing ([Law05] §4.1, `ConformalImage.IsContinuouslyGrowing`), with the argument of
`ConformalImage.ImageHyp.abs_bdryDriver_sub_le` for the continuity of the image driver.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H)
open QuantumZipper.CA (realMobius)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull

/-! ### Real Möbius maps: the normal form at the pole -/

section Algebra

variable {a b c d : ℝ}

/-- The pole `−d/c` of `z ↦ (az + b)/(cz + d)`. -/
def mobPole (c d : ℝ) : ℝ := -d / c

/-- The normal form `w ↦ α − κ/(w − P)` of a real Möbius map with pole `P`. -/
def nf (α κ P : ℝ) (w : ℂ) : ℂ := (α : ℂ) - (κ : ℂ) / (w - P)

theorem denom_eq (hc : c ≠ 0) (z : ℂ) : (c : ℂ) * z + d = c * (z - mobPole c d) := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc
  simp only [mobPole, ofReal_div, ofReal_neg]
  field_simp
  ring

/-- The normal form of `realMobius a b c d` when its pole is `P`. -/
theorem realMobius_eq_nf_of_pole (hc : c ≠ 0) {P : ℝ} (hP : c * P + d = 0) {w : ℂ}
    (hw : w - P ≠ 0) : realMobius a b c d w = nf (a / c) ((a * d - b * c) / c ^ 2) P w := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc
  have hP' : (c : ℂ) * P + d = 0 := by exact_mod_cast hP
  have hden : (c : ℂ) * w + d = c * (w - P) := by linear_combination hP'
  rw [realMobius, hden, nf]
  push_cast
  field_simp
  linear_combination (a : ℂ) * hP'

theorem mul_mobPole_add (hc : c ≠ 0) : c * mobPole c d + d = 0 := by
  rw [mobPole]; field_simp; ring

/-- `m(z) = a/c − ((ad − bc)/c²)/(z − p)`. -/
theorem realMobius_eq_nf (hc : c ≠ 0) {z : ℂ} (hz : z - mobPole c d ≠ 0) :
    realMobius a b c d z = nf (a / c) ((a * d - b * c) / c ^ 2) (mobPole c d) z :=
  realMobius_eq_nf_of_pole hc (mul_mobPole_add hc) hz

theorem c_ne_zero_of_pole (hdet : 0 < a * d - b * c) {P : ℝ} (hP : c * P + d = 0) : c ≠ 0 := by
  rintro rfl
  have hd : d = 0 := by linarith
  subst hd
  simp at hdet

theorem nf_sub_nf {α κ P : ℝ} {w w' : ℂ} (hw : w - P ≠ 0) (hw' : w' - P ≠ 0) :
    nf α κ P w - nf α κ P w' = κ * (w - w') / ((w - P) * (w' - P)) := by
  rw [nf, nf]
  field_simp
  ring

theorem nf_sub_const {α κ P : ℝ} {w : ℂ} : nf α κ P w - α = -((κ : ℂ) / (w - P)) := by
  rw [nf]; ring

/-- The normal form is real on the real line off its pole. -/
theorem nf_ofReal {α κ P x : ℝ} : nf α κ P x = ((α - κ / (x - P) : ℝ) : ℂ) := by
  simp [nf]

/-- **Lipschitz bound of the normal form** away from its pole. -/
theorem norm_nf_sub_le {α κ P ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 0 < ρ) {w w' : ℂ}
    (hw : ρ / 2 ≤ ‖w - P‖) (hw' : ρ ≤ ‖w' - P‖) :
    ‖nf α κ P w - nf α κ P w'‖ ≤ 2 * κ / ρ ^ 2 * ‖w - w'‖ := by
  have h1 : w - P ≠ 0 := norm_pos_iff.1 (by linarith)
  have h2 : w' - P ≠ 0 := norm_pos_iff.1 (by linarith)
  rw [nf_sub_nf h1 h2, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hκ]
  have hden : ρ ^ 2 / 2 ≤ ‖w - P‖ * ‖w' - P‖ := by
    have := mul_le_mul hw hw' hρ.le (norm_nonneg _)
    nlinarith
  have hpos : 0 < ρ ^ 2 / 2 := by positivity
  rw [div_le_iff₀ (hpos.trans_le hden)]
  calc κ * ‖w - w'‖ = 2 * κ / ρ ^ 2 * ‖w - w'‖ * (ρ ^ 2 / 2) := by field_simp
    _ ≤ 2 * κ / ρ ^ 2 * ‖w - w'‖ * (‖w - P‖ * ‖w' - P‖) := by gcongr

theorem continuousAt_realMobius {a' b' c' d' : ℝ} {w : ℂ} (hw : (c' : ℂ) * w + d' ≠ 0) :
    ContinuousAt (realMobius a' b' c' d') w := by
  unfold realMobius
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hw

theorem differentiableOn_realMobius (hdet : 0 < a * d - b * c) :
    DifferentiableOn ℂ (realMobius a b c d) H := by
  unfold realMobius
  exact DifferentiableOn.div (by fun_prop) (by fun_prop)
    (fun z hz => QuantumZipper.CA.realMobius_denom_ne_zero hdet hz)

end Algebra

/-! ### Images of hulls -/

section Hulls

variable {a b c d : ℝ}

theorem realMobius_mobInv (hdet : 0 < a * d - b * c) {w : ℂ} (hw : w ∈ H) :
    realMobius a b c d (realMobius d (-b) (-c) a w) = w := by
  have h' : 0 < d * a - (-b) * (-c) := by linarith
  have := QuantumZipper.CA.realMobius_inv_apply h' hw
  simpa using this

theorem image_H_diff (hdet : 0 < a * d - b * c) {K : Set ℂ} (hK : K ⊆ H) :
    realMobius a b c d '' (H \ K) = H \ realMobius a b c d '' K := by
  have hbij := QuantumZipper.CA.bijOn_realMobius_H hdet
  ext w
  constructor
  · rintro ⟨z, ⟨hz, hzK⟩, rfl⟩
    refine ⟨hbij.mapsTo hz, ?_⟩
    rintro ⟨z', hz', hzz'⟩
    exact hzK (hbij.injOn (hK hz') hz hzz' ▸ hz')
  · rintro ⟨hw, hwK⟩
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hw
    exact ⟨z, ⟨hz, fun hzK => hwK ⟨z, hzK, rfl⟩⟩, rfl⟩

/-- A point at distance `≥ r` from the pole has a bounded image. -/
theorem norm_realMobius_le (hc : c ≠ 0) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : r ≤ ‖z - mobPole c d‖) :
    ‖realMobius a b c d z‖ ≤ (|a| * ‖z‖ + |b|) / (|c| * r) := by
  have hzp : 0 < ‖z - mobPole c d‖ := hr.trans_le hz
  rw [realMobius, denom_eq hc, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnum : ‖(a : ℂ) * z + b‖ ≤ |a| * ‖z‖ + |b| := by
    calc ‖(a : ℂ) * z + b‖ ≤ ‖(a : ℂ) * z‖ + ‖(b : ℂ)‖ := norm_add_le _ _
      _ = |a| * ‖z‖ + |b| := by rw [norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
  have hcpos : 0 < |c| := abs_pos.2 hc
  calc ‖(a : ℂ) * z + b‖ / (|c| * ‖z - mobPole c d‖)
      ≤ (|a| * ‖z‖ + |b|) / (|c| * ‖z - mobPole c d‖) := by gcongr
    _ ≤ (|a| * ‖z‖ + |b|) / (|c| * r) := by
        gcongr

/-- **The Möbius image of a hull away from the pole is a hull.** -/
theorem isHPHull_image (hdet : 0 < a * d - b * c) (hc : c ≠ 0) {K : Set ℂ} (hK : IsHPHull K)
    {r : ℝ} (hr : 0 < r) (hd : Disjoint (ball (mobPole c d : ℂ) r) K) :
    IsHPHull (realMobius a b c d '' K) := by
  have hbij := QuantumZipper.CA.bijOn_realMobius_H hdet
  have hmd := differentiableOn_realMobius hdet
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hbij.mapsTo (hK.1 hz)
  · obtain ⟨M, hM⟩ := hK.2.1.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨(|a| * M + |b|) / (|c| * r), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzr : r ≤ ‖z - mobPole c d‖ := by
      by_contra hlt
      push Not at hlt
      exact Set.disjoint_left.1 hd (by rw [mem_ball, dist_eq_norm]; exact hlt) hz
    refine (norm_realMobius_le hc hr hzr).trans ?_
    gcongr
    exact hM z hz
  · rw [← image_H_diff hdet hK.1]
    exact QuantumZipper.CA.isOpen_image_of_injOn QuantumZipper.isOpen_H hmd hbij.injOn
      hK.isOpen sdiff_subset
  · rw [← image_H_diff hdet hK.1]
    exact isSimplyConnected_of_isConformalBijection hK.isOpen
      ⟨hmd.mono sdiff_subset, (hbij.injOn.mono sdiff_subset).bijOn_image⟩ hK.2.2.2

/-- **Conjugation to a real Möbius map.** If `g` maps out `A` and `G ∘ φ` is a holomorphic bijection of
`ℍ \ A` onto `ℍ`, then `G ∘ φ = M ∘ g` on `ℍ \ A` for a real Möbius map `M` (`G ∘ φ ∘ g⁻¹ ∈ Aut ℍ`). -/
theorem exists_realMobius_conj {A B : Set ℂ} {g G φ : ℂ → ℂ} (hA : IsHPHull A) (hg : IsMapOut A g)
    (hφd : DifferentiableOn ℂ φ (H \ A)) (hφb : BijOn φ (H \ A) (H \ B))
    (hG : IsConformalBijection G (H \ B) H) :
    ∃ a' b' c' d' : ℝ, 0 < a' * d' - b' * c' ∧
      ∀ z ∈ H \ A, G (φ z) = realMobius a' b' c' d' (g z) := by
  set S := H \ A with hSdef
  have hS : IsOpen S := hA.isOpen
  set e := QuantumZipper.CA.univalentOPH hS hg.1.1 hg.1.2.injOn with he
  have himg : g '' S = H := hg.1.2.image_eq
  have hsd : DifferentiableOn ℂ e.symm H := by
    have := QuantumZipper.CA.differentiableOn_univalentOPH_symm hS hg.1.1 hg.1.2.injOn
    rwa [himg] at this
  have hleft : ∀ z ∈ S, e.symm (g z) = z := fun z hz =>
    QuantumZipper.CA.univalentOPH_symm_apply_apply hS hg.1.1 hg.1.2.injOn hz
  have hright : ∀ w ∈ H, g (e.symm w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hS hg.1.1 hg.1.2.injOn (himg.symm ▸ hw)
  have hsS : ∀ w ∈ H, e.symm w ∈ S := fun w hw => by
    have : w ∈ e.target := by rw [QuantumZipper.CA.univalentOPH_target, himg]; exact hw
    exact e.map_target this
  set m : ℂ → ℂ := fun w => G (φ (e.symm w)) with hmdef
  have hmd : DifferentiableOn ℂ m H :=
    hG.1.comp (hφd.comp hsd hsS) fun w hw => hφb.mapsTo (hsS w hw)
  have hmb : BijOn m H H := by
    refine ⟨fun w hw => hG.2.mapsTo (hφb.mapsTo (hsS w hw)), fun w hw w' hw' hww' => ?_,
      fun v hv => ?_⟩
    · have h1 := hφb.injOn (hsS w hw) (hsS w' hw')
        (hG.2.injOn (hφb.mapsTo (hsS w hw)) (hφb.mapsTo (hsS w' hw')) hww')
      rw [← hright w hw, ← hright w' hw', h1]
    · obtain ⟨y, hy, rfl⟩ := hG.2.surjOn hv
      obtain ⟨z, hz, rfl⟩ := hφb.surjOn hy
      exact ⟨g z, hg.1.2.mapsTo hz, by simp only [hmdef, hleft z hz]⟩
  obtain ⟨a', b', c', d', hdet, hm⟩ := QuantumZipper.CA.exists_realMobius_of_bijOn_H hmd hmb
  refine ⟨a', b', c', d', hdet, fun z hz => ?_⟩
  have := hm (hg.1.2.mapsTo hz)
  simp only [hmdef, hleft z hz] at this
  exact this

end Hulls

/-! ### The setting -/

/-- Hypotheses of the Möbius image theorem: `W` continuous with `W 0 = 0`, `T ≥ 0`, a real Möbius map with
`ad − bc > 0` and `c ≠ 0` whose pole `p = −d/c ≠ 0` keeps distance `≥ r > 0` from `K_T`. -/
structure MobHyp (W : ℝ → ℝ) (a b c d T r : ℝ) : Prop where
  continuous : Continuous W
  zero : W 0 = 0
  nonneg : 0 ≤ T
  det : 0 < a * d - b * c
  c_ne : c ≠ 0
  pos : 0 < r
  disjoint : Disjoint (ball (mobPole c d : ℂ) r) (QuantumZipper.fwdHull W T)
  pole_ne : mobPole c d ≠ 0

/-- The image hulls `m(K_t)`. -/
def mobHull (W : ℝ → ℝ) (a b c d t : ℝ) : Set ℂ := realMobius a b c d '' QuantumZipper.fwdHull W t

namespace MobHyp

variable {W : ℝ → ℝ} {a b c d T r : ℝ}

theorem disjoint_t (h : MobHyp W a b c d T r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Disjoint (ball (mobPole c d : ℂ) r) (QuantumZipper.fwdHull W t) :=
  disjoint_ball_of_le h.disjoint ht.2

theorem isHPHull_K (h : MobHyp W a b c d T r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsHPHull (QuantumZipper.fwdHull W t) := isHPHull_fwdHull h.continuous ht.1

theorem isMapOut_g (h : MobHyp W a b c d T r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsMapOut (QuantumZipper.fwdHull W t) (gmap W t) := isMapOut_fwdMap h.continuous h.zero ht.1

theorem isHPHull_mob (h : MobHyp W a b c d T r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsHPHull (mobHull W a b c d t) :=
  isHPHull_image h.det h.c_ne (h.isHPHull_K ht) h.pos (h.disjoint_t ht)

theorem bijOn_diff (h : MobHyp W a b c d T r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    BijOn (realMobius a b c d) (H \ QuantumZipper.fwdHull W t) (H \ mobHull W a b c d t) := by
  have hbij := QuantumZipper.CA.bijOn_realMobius_H h.det
  have := (hbij.injOn.mono (sdiff_subset (s := H) (t := QuantumZipper.fwdHull W t))).bijOn_image
  rwa [image_H_diff h.det (h.isHPHull_K ht).1] at this

theorem nhdsWithin_neBot (y : ℝ) : (𝓝[H] (y : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.1 ?_
  exact closure_mono inter_subset_right
    (subset_closure_ball_inter_H (y : ℂ) 1 ⟨mem_ball_self one_pos, show (0 : ℝ) ≤ (y : ℂ).im
      by simp⟩)

theorem sub_ofReal_ne_zero {w : ℂ} (hw : w ∈ H) (x : ℝ) : w - x ≠ 0 := by
  intro h0
  have := congrArg Complex.im h0
  simp only [sub_im, ofReal_im, sub_zero, zero_im] at this
  exact (ne_of_gt (show 0 < w.im from hw)) this

/-- **The conjugated map in normal form.** For `t ∈ [0, T]` the map `g_{m(K_t)} ∘ m ∘ g_t⁻¹` is the real Möbius map
`w ↦ α − κ/(w − P)` with pole the boundary value `P = g_t(p)` and `0 < κ ≤ 48 (ad − bc)/c²`. -/
theorem exists_nf (h : MobHyp W a b c d T r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ α κ P : ℝ, 0 < κ ∧ κ ≤ 48 * ((a * d - b * c) / c ^ 2) ∧
      (P : ℂ) = bdryVal W (mobPole c d) t ∧
      ∀ z ∈ H \ QuantumZipper.fwdHull W t,
        mapOut (mobHull W a b c d t) (realMobius a b c d z) = nf α κ P (gmap W t z) := by
  set p := mobPole c d with hpdef
  set m := realMobius a b c d with hmdef
  set K := QuantumZipper.fwdHull W t with hKdef
  set B := mobHull W a b c d t with hBdef
  set G := mapOut B with hGdef
  have hK := h.isHPHull_K ht
  have hg := h.isMapOut_g ht
  have hB := h.isHPHull_mob ht
  have hG : IsMapOut B G := isMapOut_mapOut hB
  have hmK := h.bijOn_diff ht
  obtain ⟨a', b', c', d', hdet', hconj⟩ := exists_realMobius_conj hK hg
    ((differentiableOn_realMobius h.det).mono sdiff_subset) hmK hG.1
  obtain ⟨hPim, hPlim⟩ := bdryVal_spec h.continuous h.zero ht.1 h.pos (h.disjoint_t ht)
  set P : ℝ := (bdryVal W p t).re with hPdef
  have hPeq : (P : ℂ) = bdryVal W p t :=
    Complex.ext (by simp [hPdef]) (by rw [ofReal_im]; exact hPim.symm)
  have hr := h.pos
  have := nhdsWithin_neBot p
  have hev : ∀ᶠ z in 𝓝[H] (p : ℂ), z ∈ ball (p : ℂ) (r / 2) ∩ H := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (p : ℂ) (by linarith : (0 : ℝ) < r / 2))]
      with z hz1 hz2
    exact ⟨hz2, hz1⟩
  have hevK : ∀ᶠ z in 𝓝[H] (p : ℂ), z ∈ H \ K := hev.mono fun z hz =>
    ⟨hz.2, fun hzK => Set.disjoint_left.1 (h.disjoint_t ht)
      (ball_subset_ball (by linarith) hz.1) hzK⟩
  -- the normal form of `m`
  set α₀ : ℝ := a / c with hα₀
  set κ₀ : ℝ := (a * d - b * c) / c ^ 2 with hκ₀
  have hκ₀pos : 0 < κ₀ := div_pos h.det (pow_pos (abs_pos.2 h.c_ne) 2 |>.trans_eq (sq_abs c))
  have hmnf : ∀ z ∈ H, m z = nf α₀ κ₀ p z := fun z hz =>
    realMobius_eq_nf h.c_ne (sub_ofReal_ne_zero hz p)
  have hmα : ∀ z ∈ H, ‖m z - α₀‖ * ‖z - p‖ = κ₀ := fun z hz => by
    have hzp := sub_ofReal_ne_zero hz p
    rw [hmnf z hz, nf_sub_const, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ₀pos, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hzp)]
  -- `‖z − p‖ → 0⁺`
  have hdist : Tendsto (fun z : ℂ => ‖z - p‖) (𝓝[H] (p : ℂ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => ‖z - p‖) (𝓝 (p : ℂ)) (𝓝 ‖(p : ℂ) - p‖) :=
        ((continuous_id.sub continuous_const).norm).tendsto _
      rw [sub_self, norm_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact norm_pos_iff.2 (sub_ofReal_ne_zero hz p)
  have hdist0 : Tendsto (fun z : ℂ => ‖z - p‖) (𝓝[H] (p : ℂ)) (𝓝 0) :=
    hdist.mono_right nhdsWithin_le_nhds
  -- `‖m z‖ → ∞`
  have hmnorm : Tendsto (fun z : ℂ => ‖m z‖) (𝓝[H] (p : ℂ)) atTop := by
    have h1 : Tendsto (fun z : ℂ => κ₀ * ‖z - p‖⁻¹) (𝓝[H] (p : ℂ)) atTop :=
      (tendsto_inv_nhdsGT_zero.comp hdist).const_mul_atTop hκ₀pos
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-|α₀|) h1)
    filter_upwards [self_mem_nhdsWithin] with z hz
    have h2 := hmα z hz
    have hzp : 0 < ‖z - p‖ := norm_pos_iff.2 (sub_ofReal_ne_zero hz p)
    have h3 : ‖m z - α₀‖ = κ₀ * ‖z - p‖⁻¹ := by
      rw [← h2, mul_assoc, mul_inv_cancel₀ hzp.ne', mul_one]
    have h4 : ‖m z - α₀‖ ≤ ‖m z‖ + |α₀| := by
      calc ‖m z - α₀‖ ≤ ‖m z‖ + ‖(α₀ : ℂ)‖ := norm_sub_le _ _
        _ = ‖m z‖ + |α₀| := by rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hmcob : Tendsto m (𝓝[H] (p : ℂ)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ B)) :=
    tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 hmnorm,
      tendsto_principal.2 (hevK.mono fun z hz => hmK.mapsTo hz)⟩
  have hGm : Tendsto (fun z : ℂ => G (m z) - m z) (𝓝[H] (p : ℂ)) (𝓝 0) := hG.2.comp hmcob
  have hGnorm : Tendsto (fun z : ℂ => ‖G (m z)‖) (𝓝[H] (p : ℂ)) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-1) hmnorm)
    filter_upwards [hGm.norm.eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ < 1 by simp))] with z hz
    have := norm_sub_norm_le (m z) (m z - G (m z))
    rw [sub_sub_cancel, norm_sub_rev (m z)] at this
    linarith
  -- the pole of the conjugated map is `P`
  have hP0 : c' * P + d' = 0 := by
    by_contra hne
    have hne' : (c' : ℂ) * P + d' ≠ 0 := by exact_mod_cast hne
    have hlim : Tendsto (fun z : ℂ => realMobius a' b' c' d' (gmap W t z)) (𝓝[H] (p : ℂ))
        (𝓝 (realMobius a' b' c' d' P)) := by
      refine (continuousAt_realMobius hne').tendsto.comp ?_
      rw [hPeq]; exact hPlim
    have hlim' : Tendsto (fun z : ℂ => G (m z)) (𝓝[H] (p : ℂ)) (𝓝 (realMobius a' b' c' d' P)) :=
      hlim.congr' (hevK.mono fun z hz => (hconj z hz).symm)
    exact not_tendsto_nhds_of_tendsto_atTop hGnorm _ hlim'.norm
  have hc' := c_ne_zero_of_pole hdet' hP0
  set α' : ℝ := a' / c' with hα'
  set κ' : ℝ := (a' * d' - b' * c') / c' ^ 2 with hκ'
  have hκ'pos : 0 < κ' := div_pos hdet' (pow_pos (abs_pos.2 hc') 2 |>.trans_eq (sq_abs c'))
  have hGnf : ∀ z ∈ H \ K, G (m z) = nf α' κ' P (gmap W t z) := fun z hz => by
    rw [hconj z hz]
    exact realMobius_eq_nf_of_pole hc' hP0 (sub_ofReal_ne_zero (hg.1.2.mapsTo hz) P)
  refine ⟨α', κ', P, hκ'pos, ?_, hPeq, hGnf⟩
  -- the bound `κ' ≤ 48 κ₀`, comparing the residues at the pole
  have hF : Tendsto (fun z : ℂ => 48 * ‖z - p‖ * (‖G (m z) - m z‖ + |α₀| + |α'|) + 48 * κ₀)
      (𝓝[H] (p : ℂ)) (𝓝 (48 * 0 * (0 + |α₀| + |α'|) + 48 * κ₀)) := by
    have := hGm.norm
    rw [norm_zero] at this
    exact (((hdist0.const_mul 48).mul ((this.add_const _).add_const _)).add_const _)
  rw [mul_zero, zero_mul, zero_add] at hF
  refine ge_of_tendsto hF ?_
  filter_upwards [hev] with z hz
  have hzK : z ∈ H \ K := ⟨hz.2, fun hzK => Set.disjoint_left.1 (h.disjoint_t ht)
    (ball_subset_ball (by linarith) hz.1) hzK⟩
  have hgH : gmap W t z ∈ H := hg.1.2.mapsTo hzK
  have hgP := sub_ofReal_ne_zero hgH P
  have hκid : κ' = ‖G (m z) - α'‖ * ‖gmap W t z - P‖ := by
    rw [hGnf z hzK, nf_sub_const, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ'pos, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hgP)]
  have h48 : ‖gmap W t z - P‖ ≤ 48 * ‖z - p‖ := by
    rw [hPeq]
    exact norm_gmap_sub_bdryVal_le h.continuous h.zero ht.1 (h.disjoint_t ht) hz
  have htri : ‖G (m z) - α'‖ ≤ ‖G (m z) - m z‖ + ‖m z - α₀‖ + |α₀| + |α'| := by
    have e : G (m z) - α' = (G (m z) - m z) + (m z - α₀) + α₀ - α' := by ring
    rw [e]
    calc ‖(G (m z) - m z) + (m z - α₀) + α₀ - α'‖
        ≤ ‖(G (m z) - m z) + (m z - α₀) + α₀‖ + ‖(α' : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖G (m z) - m z‖ + ‖m z - α₀‖ + ‖(α₀ : ℂ)‖ + ‖(α' : ℂ)‖ := by
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ = _ := by rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hmα' := hmα z hz.2
  have hzp : 0 ≤ ‖z - p‖ := norm_nonneg _
  rw [hκid]
  calc ‖G (m z) - α'‖ * ‖gmap W t z - P‖ ≤ ‖G (m z) - α'‖ * (48 * ‖z - p‖) := by gcongr
    _ ≤ (‖G (m z) - m z‖ + ‖m z - α₀‖ + |α₀| + |α'|) * (48 * ‖z - p‖) := by gcongr
    _ = 48 * ‖z - p‖ * (‖G (m z) - m z‖ + |α₀| + |α'|) + 48 * (‖m z - α₀‖ * ‖z - p‖) := by
        ring
    _ = 48 * ‖z - p‖ * (‖G (m z) - m z‖ + |α₀| + |α'|) + 48 * κ₀ := by rw [hmα']

/-- **Uniform clearance of the pole's image from the driver**: `|g_t(p) − W_t| ≥ ρ > 0` on `[0, T]`
(continuity of the boundary value, and `g_t(p) ≠ W_t` because `p` is not swallowed). -/
theorem exists_clearance (h : MobHyp W a b c d T r) :
    ∃ ρ > 0, ∀ t ∈ Icc (0 : ℝ) T, ρ ≤ ‖bdryVal W (mobPole c d) t - W t‖ := by
  set ψ : ℝ → ℝ := fun t => ‖bdryVal W (mobPole c d) t - W t‖ with hψ
  have hψc : ContinuousOn ψ (Icc 0 T) :=
    ((continuousOn_bdryVal h.continuous h.zero h.nonneg h.pos h.disjoint).sub
      (continuous_ofReal.comp h.continuous).continuousOn).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 h.nonneg) hψc
  have hψ0 : 0 < ψ t₀ := norm_pos_iff.2 (sub_ne_zero.2 (bdryVal_ne h.continuous h.zero h.pos
    h.disjoint h.pole_ne ht₀))
  exact ⟨ψ t₀, hψ0, fun t ht => hmin ht⟩

end MobHyp

/-! ### The image family is continuously growing -/

/-- Normal-form data `(α_t, κ_t, P_t)` of the conjugated maps `g_{m(K_t)} ∘ m ∘ g_t⁻¹` on `[0, T]`. -/
structure NFData (W : ℝ → ℝ) (a b c d T : ℝ) (α κ P : ℝ → ℝ) : Prop where
  pos : ∀ t ∈ Icc (0 : ℝ) T, 0 < κ t
  le : ∀ t ∈ Icc (0 : ℝ) T, κ t ≤ 48 * ((a * d - b * c) / c ^ 2)
  pole : ∀ t ∈ Icc (0 : ℝ) T, (P t : ℂ) = bdryVal W (mobPole c d) t
  conj : ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ H \ QuantumZipper.fwdHull W t,
    mapOut (mobHull W a b c d t) (realMobius a b c d z) = nf (α t) (κ t) (P t) (gmap W t z)

/-- The driver of the image chain: `t ↦ α_t − κ_t/(W_t − P_t)`, the boundary value of the conjugated map at
`W_t`. -/
def mobDriver (α κ P W : ℝ → ℝ) (t : ℝ) : ℝ := α t - κ t / (W t - P t)

/-- The Lipschitz constant `2 · 48 (ad − bc)/c² / ρ²`. -/
def lipConst (a b c d ρ : ℝ) : ℝ := 2 * (48 * ((a * d - b * c) / c ^ 2)) / ρ ^ 2

namespace MobHyp

variable {W : ℝ → ℝ} {a b c d T r : ℝ} {α κ P : ℝ → ℝ}

theorem exists_nfData (h : MobHyp W a b c d T r) : ∃ α κ P : ℝ → ℝ, NFData W a b c d T α κ P := by
  have := fun t (ht : t ∈ Icc (0 : ℝ) T) => h.exists_nf ht
  choose! α κ P hpos hle hP hconj using this
  exact ⟨α, κ, P, ⟨hpos, hle, hP, hconj⟩⟩

theorem lipConst_nonneg (h : MobHyp W a b c d T r) (ρ : ℝ) : 0 ≤ lipConst a b c d ρ := by
  have : 0 < (a * d - b * c) / c ^ 2 :=
    div_pos h.det (pow_pos (abs_pos.2 h.c_ne) 2 |>.trans_eq (sq_abs c))
  clear h
  unfold lipConst
  positivity

/-- **Lipschitz bound of the conjugated map** near the driver. -/
theorem norm_nf_sub_driver_le (hn : NFData W a b c d T α κ P) {ρ : ℝ}
    (hρ : 0 < ρ) (hcl : ∀ t ∈ Icc (0 : ℝ) T, ρ ≤ ‖bdryVal W (mobPole c d) t - W t‖) {t : ℝ}
    (ht : t ∈ Icc 0 T) {w : ℂ} (hw : ‖w - W t‖ ≤ ρ / 2) :
    ‖nf (α t) (κ t) (P t) w - (mobDriver α κ P W t : ℂ)‖ ≤ lipConst a b c d ρ * ‖w - W t‖ := by
  have hWP : ρ ≤ ‖(W t : ℂ) - P t‖ := by
    rw [hn.pole t ht, norm_sub_rev]; exact hcl t ht
  have hwP : ρ / 2 ≤ ‖w - P t‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub (W t : ℂ) w (P t)
    rw [norm_sub_rev (W t : ℂ) w] at this
    linarith
  have hnf : nf (α t) (κ t) (P t) (W t) = (mobDriver α κ P W t : ℂ) := by
    rw [nf_ofReal, mobDriver]
  rw [← hnf]
  refine (norm_nf_sub_le (hn.pos t ht).le hρ hwP hWP).trans ?_
  unfold lipConst
  gcongr
  exact hn.le t ht

theorem mobHull_diff (h : MobHyp W a b c d T r) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    mobHull W a b c d t \ mobHull W a b c d s =
      realMobius a b c d '' (QuantumZipper.fwdHull W t \ QuantumZipper.fwdHull W s) := by
  ext y
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hy⟩
    exact ⟨z, ⟨hz, fun hzs => hy ⟨z, hzs, rfl⟩⟩, rfl⟩
  · rintro ⟨z, ⟨hzt, hzs⟩, rfl⟩
    refine ⟨⟨z, hzt, rfl⟩, ?_⟩
    rintro ⟨z', hz', hzz'⟩
    exact hzs ((QuantumZipper.CA.bijOn_realMobius_H h.det).injOn ((h.isHPHull_K hs).1 hz')
      ((h.isHPHull_K ht).1 hzt) hzz' ▸ hz')

/-- **Local growth of the image chain** at the driver `α_s − κ_s/(W_s − P_s)`. -/
theorem growth (h : MobHyp W a b c d T r) (hn : NFData W a b c d T α κ P) {ρ : ℝ} (hρ : 0 < ρ)
    (hcl : ∀ t ∈ Icc (0 : ℝ) T, ρ ≤ ‖bdryVal W (mobPole c d) t - W t‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → t - s ≤ δ →
      mapOut (mobHull W a b c d s) '' (mobHull W a b c d t \ mobHull W a b c d s) ⊆
        closedBall (mobDriver α κ P W s : ℂ) ε := by
  set L := lipConst a b c d ρ with hL
  have hL0 : 0 ≤ L := h.lipConst_nonneg ρ
  set η := min (ρ / 2) (ε / (L + 1)) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  obtain ⟨δ, hδ, hg⟩ := (imageHyp_empty h.continuous h.zero h.nonneg).exists_gmap_diff_subset hη
  refine ⟨δ, hδ, fun s hs t ht hst hd => ?_⟩
  rw [h.mobHull_diff hs ht, image_image]
  rintro _ ⟨z, hz, rfl⟩
  have hzs : z ∈ H \ QuantumZipper.fwdHull W s := ⟨(h.isHPHull_K ht).1 hz.1, hz.2⟩
  show mapOut (mobHull W a b c d s) (realMobius a b c d z) ∈ _
  rw [hn.conj s hs z hzs]
  have hζ := hg s hs t ht hst hd ⟨z, hz, rfl⟩
  rw [mem_closedBall, dist_eq_norm] at hζ
  have hb := norm_nf_sub_driver_le hn hρ hcl hs (hζ.trans (min_le_left _ _))
  rw [mem_closedBall, dist_eq_norm]
  have h1 : L * ‖gmap W s z - W s‖ ≤ L * η := mul_le_mul_of_nonneg_left hζ hL0
  have h2 : L * η ≤ ε := by
    have : η ≤ ε / (L + 1) := min_le_right _ _
    calc L * η ≤ (L + 1) * η := by nlinarith
      _ ≤ (L + 1) * (ε / (L + 1)) := by gcongr
      _ = ε := by field_simp
  linarith

theorem isHPHull_inc (h : MobHyp W a b c d T r) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hst : s ≤ t) : IsHPHull (inc (mobHull W a b c d) s t) :=
  (isMapOut_mapOut (h.isHPHull_mob hs)).isHPHull_image (h.isHPHull_mob hs) (h.isHPHull_mob ht)
    (image_mono ((QuantumZipper.fwdHull_mono (W := W)).1 hst))

theorem eqOn_mapOut_mob (h : MobHyp W a b c d T r) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    EqOn (mapOut (mobHull W a b c d t))
      (mapOut (inc (mobHull W a b c d) s t) ∘ mapOut (mobHull W a b c d s))
      (H \ mobHull W a b c d t) :=
  (isMapOut_mapOut (h.isHPHull_mob ht)).eqOn (h.isHPHull_mob ht)
    ((isMapOut_mapOut (h.isHPHull_mob hs)).comp (h.isHPHull_mob hs) (h.isHPHull_mob ht)
      (image_mono ((QuantumZipper.fwdHull_mono (W := W)).1 hst))
      (isMapOut_mapOut (h.isHPHull_inc hs ht hst)))

/-- **Uniform continuity of the image driver** (the argument of `ImageHyp.abs_bdryDriver_sub_le`): compare the
conjugated map at `s'` at the point `W_{s'} + iη` with `g_L ∘ (conjugated map at s) ∘ g_s ∘ g_{s'}⁻¹`, `L` the
image increment. -/
theorem abs_driver_sub_le (h : MobHyp W a b c d T r) (hn : NFData W a b c d T α κ P) {ρ : ℝ}
    (hρ : 0 < ρ) (hcl : ∀ t ∈ Icc (0 : ℝ) T, ρ ≤ ‖bdryVal W (mobPole c d) t - W t‖) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc 0 T, ∀ s' ∈ Icc 0 T, s ≤ s' → s' - s ≤ δ →
      |mobDriver α κ P W s' - mobDriver α κ P W s| ≤ ε := by
  set L := lipConst a b c d ρ with hLdef
  have hL0 : 0 ≤ L := h.lipConst_nonneg ρ
  set M := L + 1 with hMdef
  have hM : 0 < M := by linarith
  set ε₁ := ε / 20 with hε₁
  obtain ⟨δk, hδk, hk⟩ := h.growth hn hρ hcl (show 0 < ε₁ by positivity)
  set μ := min (ε / (96 * M)) (ρ / 192) with hμ
  have hμpos : 0 < μ := lt_min (by positivity) (by linarith)
  obtain ⟨δW, hδW, hW⟩ := (imageHyp_empty h.continuous h.zero h.nonneg).exists_uniform hμpos
  set q := min (ε / (32 * M)) (ρ / 64) with hq
  have hqpos : 0 < q := lt_min (by positivity) (by linarith)
  refine ⟨min δk (min δW (q ^ 2)), lt_min hδk (lt_min hδW (by positivity)), ?_⟩
  intro s hs s' hs' hss' hd
  rcases eq_or_lt_of_le hss' with heq | hlt
  · subst heq; simp [hε.le]
  set hh := s' - s with hhh
  have hhpos : 0 < hh := sub_pos.2 hlt
  set η := min (ρ / 8) (ε / (8 * M)) with hηdef
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
  have hζW : ‖ζ - W s'‖ = η := by
    rw [hζ, add_sub_cancel_left, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hηpos]
  have hzs : z ∉ QuantumZipper.fwdHull W s := fun hz' =>
    hzK.2 ((QuantumZipper.fwdHull_mono (W := W)).1 hss' hz')
  have hzKs : z ∈ H \ QuantumZipper.fwdHull W s := ⟨hzK.1, hzs⟩
  -- the image point `m z`
  have hmz : realMobius a b c d z ∈ H \ mobHull W a b c d s' := (h.bijOn_diff hs').mapsTo hzK
  have hid1 := hn.conj s' hs' z hzK
  have hid2 := h.eqOn_mapOut_mob hs hs' hss' hmz
  have hid3 := hn.conj s hs z hzKs
  simp only [Function.comp_apply] at hid2
  rw [hgz] at hid1
  set v := mapOut (mobHull W a b c d s) (realMobius a b c d z) with hv
  -- bound (1): at `s'`
  have hb1 := norm_nf_sub_driver_le hn hρ hcl hs'
    (show ‖ζ - W s'‖ ≤ ρ / 2 by rw [hζW]; linarith [min_le_left (ρ / 8) (ε / (8 * M))])
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
  have hgsH : gmap W s z ∈ H := (h.isMapOut_g hs).1.2.mapsTo hzKs
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
  have hξρ : ‖ξ‖ ≤ ρ / 2 := by
    linarith [min_le_left (ρ / 8) (ε / (8 * M)), min_le_right (ε / (96 * M)) (ρ / 192),
      min_le_right (ε / (32 * M)) (ρ / 64)]
  have hb3 := norm_nf_sub_driver_le hn hρ hcl hs (show ‖gmap W s z - W s‖ ≤ ρ / 2 by
    rw [hgξ]; exact hξρ)
  rw [hgξ, ← hid3] at hb3
  -- bound (4): the increment hull
  have hLsub := hk s hs s' hs' hss' (by linarith [min_le_left δk (min δW (q ^ 2))])
  have hvL : v ∈ H \ inc (mobHull W a b c d) s s' := by
    have hG := isMapOut_mapOut (h.isHPHull_mob hs)
    have hmzs : realMobius a b c d z ∈ H \ mobHull W a b c d s := (h.bijOn_diff hs).mapsTo hzKs
    refine ⟨hG.1.2.mapsTo hmzs, ?_⟩
    rintro ⟨y, hy, hyz⟩
    have := hG.1.2.injOn ⟨(h.isHPHull_mob hs').1 hy.1, hy.2⟩ hmzs hyz
    exact hmz.2 (this ▸ hy.1)
  have hb4 := (isMapOut_mapOut (h.isHPHull_inc hs hs' hss')).norm_sub_center_le
    (h.isHPHull_inc hs hs' hss') (show 0 < ε₁ by positivity) hLsub hvL
  -- combine
  have hcomb : mapOut (inc (mobHull W a b c d) s s') v = nf (α s') (κ s') (P s') ζ := by
    rw [← hid1, hid2]
  rw [hcomb] at hb4
  have hLη : L * η ≤ ε / 8 := by
    have : η ≤ ε / (8 * M) := min_le_right _ _
    calc L * η ≤ M * η := by nlinarith
      _ ≤ M * (ε / (8 * M)) := by gcongr
      _ = ε / 8 := by field_simp
  have hLμ : L * μ ≤ ε / 96 := by
    have : μ ≤ ε / (96 * M) := min_le_left _ _
    calc L * μ ≤ M * μ := by nlinarith
      _ ≤ M * (ε / (96 * M)) := by gcongr
      _ = ε / 96 := by field_simp
  have hLq : L * q ≤ ε / 32 := by
    have : q ≤ ε / (32 * M) := min_le_left _ _
    calc L * q ≤ M * q := by nlinarith
      _ ≤ M * (ε / (32 * M)) := by gcongr
      _ = ε / 32 := by field_simp
  have hLξ : L * ‖ξ‖ ≤ L * (η + 24 * μ + 8 * q) := mul_le_mul_of_nonneg_left hξn hL0
  have hfinal : ‖((mobDriver α κ P W s' : ℝ) : ℂ) - (mobDriver α κ P W s : ℝ)‖ ≤ ε := by
    calc ‖((mobDriver α κ P W s' : ℝ) : ℂ) - (mobDriver α κ P W s : ℝ)‖
        = ‖((mobDriver α κ P W s' : ℂ) - nf (α s') (κ s') (P s') ζ) +
            (nf (α s') (κ s') (P s') ζ - mobDriver α κ P W s)‖ := by ring_nf
      _ ≤ ‖(mobDriver α κ P W s' : ℂ) - nf (α s') (κ s') (P s') ζ‖ +
            ‖nf (α s') (κ s') (P s') ζ - mobDriver α κ P W s‖ := norm_add_le _ _
      _ ≤ L * η + (L * ‖ξ‖ + 5 * ε₁) := by
          rw [← norm_neg, neg_sub]
          exact add_le_add hb1 (hb4.trans (by linarith))
      _ ≤ ε := by
          rw [hε₁]
          nlinarith
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hfinal
  exact hfinal

theorem continuousOn_driver (h : MobHyp W a b c d T r) (hn : NFData W a b c d T α κ P) {ρ : ℝ}
    (hρ : 0 < ρ) (hcl : ∀ t ∈ Icc (0 : ℝ) T, ρ ≤ ‖bdryVal W (mobPole c d) t - W t‖) :
    ContinuousOn (mobDriver α κ P W) (Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hd⟩ := h.abs_driver_sub_le hn hρ hcl (half_pos hε)
  refine ⟨δ, hδ, fun s hs hst => ?_⟩
  rw [Real.dist_eq] at hst ⊢
  rcases le_total t s with hle | hle
  · have := hd t ht s hs hle (by linarith [le_abs_self (s - t)])
    linarith
  · have := hd s hs t ht hle (by linarith [neg_abs_le (s - t)])
    rw [abs_sub_comm]
    linarith

/-- **The image family `t ↦ m(K_t)` is continuously growing**, with driver `t ↦ α_t − κ_t/(W_t − P_t)`. -/
theorem isContinuouslyGrowing (h : MobHyp W a b c d T r) (hn : NFData W a b c d T α κ P) :
    IsContinuouslyGrowing (mobHull W a b c d) (mobDriver α κ P W) T := by
  obtain ⟨ρ, hρ, hcl⟩ := h.exists_clearance
  have hE := imageHyp_empty h.continuous h.zero h.nonneg
  exact
  { isHPHull := fun _ ht => h.isHPHull_mob ht
    zero := by simp [mobHull, hE.K_zero]
    mono := fun _ _ _ _ hst => image_mono ((QuantumZipper.fwdHull_mono (W := W)).1 hst)
    strict := fun _ hs _ ht hst => by
      rw [h.mobHull_diff hs ht]
      exact (hE.diff_nonempty hs ht hst).image _
    continuousOn := h.continuousOn_driver hn hρ hcl
    growth := fun _ hε => h.growth hn hρ hcl hε }

end MobHyp

namespace MobHyp

variable {W : ℝ → ℝ} {a b c d T r : ℝ} {α κ P : ℝ → ℝ}

/-- **The image driver starts at `m(0) = b/d`**: at time `0` the conjugated map is `m` itself on `ℍ`, and both
sides are continuous at `0`. -/
theorem mobDriver_zero (h : MobHyp W a b c d T r) (hn : NFData W a b c d T α κ P) :
    mobDriver α κ P W 0 = b / d := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.nonneg⟩
  have hE := imageHyp_empty h.continuous h.zero h.nonneg
  have hK0 : QuantumZipper.fwdHull W 0 = ∅ := hE.K_zero
  have hB0 : mobHull W a b c d 0 = ∅ := by simp [mobHull, hK0]
  have hid : EqOn (mapOut (mobHull W a b c d 0)) id H := by
    rw [hB0]
    have := (isMapOut_mapOut isHPHull_empty).eqOn isHPHull_empty isMapOut_empty_id
    simpa using this
  have hP0 : P 0 = mobPole c d := by
    have := hn.pole 0 h0T
    rw [bdryVal_zero h.continuous h.zero] at this
    exact_mod_cast this
  have hd : d ≠ 0 := by
    intro hd0
    apply h.pole_ne
    simp [mobPole, hd0]
  have heq : ∀ z ∈ H, realMobius a b c d z = nf (α 0) (κ 0) (P 0) z := fun z hz => by
    have hzK : z ∈ H \ QuantumZipper.fwdHull W 0 := ⟨hz, by rw [hK0]; exact Set.notMem_empty z⟩
    have h1 := hn.conj 0 h0T z hzK
    have hg0 : gmap W 0 z = z := by
      simp [gmap, fwdMap_zero_eq h.continuous h.zero (le_refl 0) hzK, h.zero]
    rw [hg0, hid (QuantumZipper.CA.bijOn_realMobius_H h.det |>.mapsTo hz)] at h1
    exact h1
  have := MobHyp.nhdsWithin_neBot 0
  have hm : Tendsto (realMobius a b c d) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (realMobius a b c d 0)) :=
    (continuousAt_realMobius (by simpa using hd)).tendsto.mono_left nhdsWithin_le_nhds
  have hnf0 : ((0 : ℂ) - P 0) ≠ 0 := by
    rw [hP0, zero_sub, neg_ne_zero]; exact_mod_cast h.pole_ne
  have hnfc : ContinuousAt (nf (α 0) (κ 0) (P 0)) 0 := by
    unfold nf
    exact continuousAt_const.sub (continuousAt_const.div (by fun_prop) hnf0)
  have hnf : Tendsto (nf (α 0) (κ 0) (P 0)) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (nf (α 0) (κ 0) (P 0) 0)) := by
    simpa using hnfc.tendsto.mono_left nhdsWithin_le_nhds
  have hm' : Tendsto (realMobius a b c d) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (nf (α 0) (κ 0) (P 0) 0)) :=
    hnf.congr' (eventually_nhdsWithin_of_forall fun z hz => (heq z hz).symm)
  have hval := tendsto_nhds_unique hm hm'
  have hb : realMobius a b c d 0 = ((b / d : ℝ) : ℂ) := by simp [realMobius]
  have hdrv : nf (α 0) (κ 0) (P 0) 0 = ((mobDriver α κ P W 0 : ℝ) : ℂ) := by
    rw [mobDriver, h.zero]
    simp [nf]
  rw [hb, hdrv] at hval
  exact_mod_cast hval.symm

end MobHyp

/-! ### The main theorem -/

/-- **The image of a Loewner chain under a real Möbius map that moves `∞`** (target change of hulls; [Law05] §4.6,
[SW05]). Let `W` be continuous with `W 0 = 0`, `T ≥ 0`, and `m(z) = (az + b)/(cz + d)` with `ad − bc > 0`, `c ≠ 0`,
whose pole `p = −d/c ≠ 0` keeps distance `≥ r > 0` from `K_T`. Then with the capacity clock
`σ(t) = ½ hcap(m(K_t))` (continuous, strictly increasing on `[0, T]`, `σ 0 = 0`) there is a continuous driver `W̃`
starting at `W̃(0) = m(0) = b/d` such that for every `t ∈ [0, T]`:
* `m(K_t)` is the Loewner hull of `W̃` at time `σ(t)`;
* `g̃_{σ(t)} ∘ m = (w ↦ α_t − κ_t/(w − P_t)) ∘ g_t` on `ℍ \ K_t`, with `κ_t > 0` and `P_t = g_t(p)` the boundary
  value of `g_t` at the pole;
* `W̃(σ(t)) = α_t − κ_t/(W_t − P_t)`. -/
theorem exists_loewner_mobius_image {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {a b c d : ℝ} (hdet : 0 < a * d - b * c) (hc : c ≠ 0) (hp : mobPole c d ≠ 0)
    {r : ℝ} (hr : 0 < r) (hd : Disjoint (ball (mobPole c d : ℂ) r) (QuantumZipper.fwdHull W T)) :
    ∃ (σ W' α κ P : ℝ → ℝ), Continuous W' ∧ W' 0 = b / d ∧ σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 T) ∧
      ContinuousOn σ (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        σ t = hcapSet (realMobius a b c d '' QuantumZipper.fwdHull W t) / 2 ∧
        QuantumZipper.fwdHull W' (σ t) = realMobius a b c d '' QuantumZipper.fwdHull W t ∧
        W' (σ t) = α t - κ t / (W t - P t) ∧ 0 < κ t ∧ (P t : ℂ) = bdryVal W (mobPole c d) t ∧
        ∀ z ∈ H \ QuantumZipper.fwdHull W t,
          gmap W' (σ t) (realMobius a b c d z) = nf (α t) (κ t) (P t) (gmap W t z) := by
  have h : MobHyp W a b c d T r := ⟨hW, hW0, hT, hdet, hc, hr, hd, hp⟩
  obtain ⟨α, κ, P, hn⟩ := h.exists_nfData
  have hg := h.isContinuouslyGrowing hn
  refine ⟨cap (mobHull W a b c d), IsContinuouslyGrowing.drv (mobHull W a b c d) (mobDriver α κ P W) T,
    α, κ, P, hg.continuous_drv hT, ?_, hg.cap_zero hT, hg.strictMonoOn_cap, hg.continuousOn_cap,
    fun t ht => ?_⟩
  · have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have := (hg.loewner hT h0T).1
    rw [hg.cap_zero hT] at this
    rw [this, h.mobDriver_zero hn]
  obtain ⟨hdrv, hhull, hmap⟩ := hg.loewner hT ht
  refine ⟨rfl, hhull, hdrv, hn.pos t ht, hn.pole t ht, fun z hz => ?_⟩
  rw [gmap, hmap _ ((h.bijOn_diff ht).mapsTo hz)]
  exact hn.conj t ht z hz

end CrossRestart

end Sec5

end InteractingSLE
