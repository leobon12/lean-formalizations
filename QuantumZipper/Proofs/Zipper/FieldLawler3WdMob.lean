import QuantumZipper.Proofs.Zipper.FieldLawler3WdCar
import QuantumZipper.Proofs.Zipper.FieldLawler3UnifC
import QuantumZipper.Proofs.Zipper.FieldLawler3SymHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-WD (Möb): `FL3Unif` for the image of a bounded Jordan-type domain under `z ↦ 1/(z - p)`

A bounded domain carries no `FL3Unif` (`fl3Wd_not_FL3Unif_of_bounded`). For a bounded
Jordan-type domain `D` (hypotheses of `fl3Wd_unif_of_car`) and `p ∈ ∂D`, the Möbius image
`T(D)`, `T z = 1/(z - p)`, is unbounded with `T(p) = ∞`, and `fl3Wd_FL3Unif_of_car` gives
`F` with `FL3Unif (T '' D) F` (together with its inverse `Φ`, as in `fl3u_FL3Unif_exists`).
The second symmetry `fl3Sym_excR_symm'` can then be applied in `T(D)` with the charts `T ∘ ψ`
and the harmonic measures `ω ∘ T⁻¹`.

Source: Carathéodory's theorem (Pommerenke 1992, Thm 2.6, p. 24) via `fl3Wd_unif_of_car`;
the Möbius transport is routine (own elementary argument, as `fl3u_frD_inv` in
FieldLawler3UnifA.lean for `M z = 1/(z + i)`).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

/-- The Möbius map `T_p z = 1/(z - p)`, sending `p` to `∞`. -/
def fl3WdT (p z : ℂ) : ℂ := (z - p)⁻¹

/-- Its inverse `w ↦ p + 1/w`. -/
def fl3WdTi (p w : ℂ) : ℂ := p + w⁻¹

section Mob

variable {p : ℂ}

lemma fl3WdTi_T {z : ℂ} (_hz : z ≠ p) : fl3WdTi p (fl3WdT p z) = z := by
  simp [fl3WdT, fl3WdTi]

lemma fl3WdT_Ti {w : ℂ} (_hw : w ≠ 0) : fl3WdT p (fl3WdTi p w) = w := by
  simp [fl3WdT, fl3WdTi]

lemma fl3WdT_ne_zero {z : ℂ} (hz : z ≠ p) : fl3WdT p z ≠ 0 :=
  inv_ne_zero (sub_ne_zero.2 hz)

lemma fl3WdTi_ne {w : ℂ} (hw : w ≠ 0) : fl3WdTi p w ≠ p := by
  simp [fl3WdTi, hw]

lemma fl3WdT_inj {z z' : ℂ} (hz : z ≠ p) (hz' : z' ≠ p) (h : fl3WdT p z = fl3WdT p z') :
    z = z' := by
  rw [← fl3WdTi_T hz, h, fl3WdTi_T hz']

lemma fl3WdT_contAt {z : ℂ} (hz : z ≠ p) : ContinuousAt (fl3WdT p) z :=
  (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hz)

lemma fl3WdTi_contAt {w : ℂ} (hw : w ≠ 0) : ContinuousAt (fl3WdTi p) w :=
  continuousAt_const.add (continuousAt_id.inv₀ hw)

variable {D : Set ℂ}

lemma fl3Wd_memT (hpD : p ∉ D) (w : ℂ) : w ∈ fl3WdT p '' D ↔ w ≠ 0 ∧ fl3WdTi p w ∈ D := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzp : z ≠ p := fun h => hpD (h ▸ hz)
    exact ⟨fl3WdT_ne_zero hzp, by rwa [fl3WdTi_T hzp]⟩
  · rintro ⟨hw, hD⟩
    exact ⟨_, hD, fl3WdT_Ti hw⟩

lemma fl3Wd_isOpenT (hDo : IsOpen D) (hpD : p ∉ D) : IsOpen (fl3WdT p '' D) := by
  have : fl3WdT p '' D = {w : ℂ | w ≠ 0} ∩ fl3WdTi p ⁻¹' D := by
    ext w; rw [fl3Wd_memT hpD]; rfl
  rw [this]
  exact ContinuousOn.isOpen_inter_preimage (fun w hw => (fl3WdTi_contAt hw).continuousWithinAt)
    isOpen_ne hDo

lemma fl3Wd_zero_not_closure {R₀ : ℝ} (hDb : D ⊆ ball 0 R₀) (hne : D.Nonempty) (hpD : p ∉ D) :
    (0 : ℂ) ∉ closure (fl3WdT p '' D) := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hR : 0 < R₀ := by have := hDb hz₀; rw [mem_ball] at this; linarith [dist_nonneg (x := z₀) (y := 0)]
  set c : ℝ := (R₀ + ‖p‖)⁻¹
  have hc : 0 < c := inv_pos.2 (by positivity)
  have hsub : fl3WdT p '' D ⊆ {w : ℂ | c ≤ ‖w‖} := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' := hDb hz
    rw [mem_ball, dist_zero_right] at hz'
    have h1 : ‖z - p‖ < R₀ + ‖p‖ := (norm_sub_le z p).trans_lt (by linarith)
    have hzp : z - p ≠ 0 := sub_ne_zero.2 (show z ≠ p from fun e => hpD (e ▸ hz))
    show c ≤ ‖fl3WdT p z‖
    rw [show ‖fl3WdT p z‖ = ‖z - p‖⁻¹ by simp [fl3WdT]]
    exact inv_anti₀ (norm_pos_iff.2 hzp) h1.le
  intro h0
  have := closure_minimal hsub (isClosed_le continuous_const continuous_norm) h0
  simp only [mem_ofPred_eq, norm_zero] at this
  linarith

/-- The frontier of `T_p(D)` is `T_p(∂D \ {p})`. -/
lemma fl3Wd_frontierT {R₀ : ℝ} (hDo : IsOpen D) (hDb : D ⊆ ball 0 R₀) (hne : D.Nonempty)
    (hpD : p ∉ D) : frontier (fl3WdT p '' D) = fl3WdT p '' (frontier D \ {p}) := by
  have hOo := fl3Wd_isOpenT hDo hpD
  rw [hOo.frontier_eq, hDo.frontier_eq]
  ext w
  constructor
  · rintro ⟨hwc, hwO⟩
    have hw0 : w ≠ 0 := fun h => fl3Wd_zero_not_closure hDb hne hpD (h ▸ hwc)
    refine ⟨fl3WdTi p w, ⟨⟨?_, fun hD => hwO ((fl3Wd_memT hpD w).2 ⟨hw0, hD⟩)⟩,
      fl3WdTi_ne hw0⟩, fl3WdT_Ti hw0⟩
    have h1 := mem_closure_image (fl3WdTi_contAt (p := p) hw0) hwc
    refine closure_mono ?_ h1
    rintro _ ⟨v, hv, rfl⟩
    exact ((fl3Wd_memT hpD v).1 hv).2
  · rintro ⟨z, ⟨⟨hzc, hzD⟩, hzp⟩, rfl⟩
    refine ⟨mem_closure_image (fl3WdT_contAt hzp) hzc, ?_⟩
    rintro ⟨z', hz', he⟩
    exact hzD (fl3WdT_inj (show z' ≠ p from fun e => hpD (e ▸ hz')) hzp he ▸ hz')

end Mob

/-- **`FL3Unif` on the Möbius image of a bounded Jordan-type domain.** -/
theorem fl3Wd_FL3Unif_of_car {D E : Set ℂ} {R₀ : ℝ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hDne : D.Nonempty)
    (hcomp : ∀ a ∉ D, ¬ Bornology.IsBounded (connectedComponentIn Dᶜ a))
    (hDb : D ⊆ ball 0 R₀) (hEc : IsClosed E) (hfr : frontier D ⊆ E) (hEsub : E ⊆ Dᶜ)
    (hEb : E ⊆ closedBall 0 R₀) (hulc : Topo.ULC E) (hE : ∀ q, IsPreconnected (E \ {q}))
    {p : ℂ} (hp : p ∈ frontier D) :
    ∃ F Φ : ℂ → ℂ, FL3Unif (fl3WdT p '' D) F ∧ BijOn F (fl3WdT p '' D) H ∧
      (∀ q ∈ closure (fl3WdT p '' D), F q ∈ Hbar ∧ Φ (F q) = q) ∧
      (∀ z ∈ Hbar, F (Φ z) = z) ∧ ContinuousOn Φ Hbar ∧
      range (fun x : ℝ => Φ x) = frontier (fl3WdT p '' D) := by
  obtain ⟨Φ, hd, hbij, hc, hinj, hrange, hinf⟩ :=
    fl3Wd_unif_of_car hDo hDc hDne hcomp hDb hEc hfr hEsub hEb hulc hE hp
  have hpD : p ∉ D := fun h => by rw [hDo.frontier_eq] at hp; exact hp.2 h
  have hΦne : ∀ z ∈ Hbar, Φ z ≠ p := by
    intro z hz
    rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with hpos | hzero
    · exact fun h => hpD (h ▸ hbij.mapsTo hpos)
    · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have : Φ z ∈ range (fun x : ℝ => Φ x) := ⟨z.re, by show Φ (z.re : ℂ) = Φ z; rw [← hzr]⟩
      rw [hrange] at this
      exact this.2
  set Ω := fl3WdT p '' D with hΩ
  set Φ' : ℂ → ℂ := fun z => fl3WdT p (Φ z) with hΦ'
  have hd' : DifferentiableOn ℂ Φ' H := fun z hz =>
    ((hd z hz).sub_const p).inv (sub_ne_zero.2 (hΦne z (H_subset_Hbar hz)))
  have hinjT : InjOn (fl3WdT p) D := fun z hz z' hz' h =>
    fl3WdT_inj (show z ≠ p from fun e => hpD (e ▸ hz)) (show z' ≠ p from fun e => hpD (e ▸ hz')) h
  have hbij' : BijOn Φ' H Ω := hinjT.bijOn_image.comp hbij
  have hc' : ContinuousOn Φ' Hbar := fun z hz =>
    (fl3WdT_contAt (hΦne z hz)).comp_continuousWithinAt (hc z hz)
  have hRH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hinj' : Function.Injective (fun x : ℝ => Φ' x) := fun x y h =>
    hinj (fl3WdT_inj (hΦne _ (hRH x)) (hΦne _ (hRH y)) h)
  have hrange' : range (fun x : ℝ => Φ' x) = frontier Ω := by
    rw [hΩ, fl3Wd_frontierT hDo hDb hDne hpD, ← hrange, ← range_comp]
    rfl
  have hinf' : Tendsto Φ' (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) := by
    have h0 : Tendsto (fun z => Φ z - p) (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨by simpa using hinf.sub_const p, ?_⟩
      exact eventually_inf_principal.2 (Eventually.of_forall fun z hz =>
        sub_ne_zero.2 (hΦne z hz))
    exact tendsto_inv₀_nhdsNE_zero.comp h0
  obtain ⟨F, h1, h2, h3, h4, h5, h6, h7⟩ :=
    fl3u_inverse (fl3Wd_isOpenT hDo hpD) hd' hbij' hc' hinj' hrange' hinf'
  refine ⟨F, Φ', ⟨fl3Wd_isOpenT hDo hpD, h2, h1.mapsTo, h3, h6, ?_, h7⟩, h1, h4, h5, hc',
    hrange'⟩
  intro q hq r hr h
  rw [← (h4 q (frontier_subset_closure hq)).2, ← (h4 r (frontier_subset_closure hr)).2, h]

end FieldLawler
end QuantumZipper
