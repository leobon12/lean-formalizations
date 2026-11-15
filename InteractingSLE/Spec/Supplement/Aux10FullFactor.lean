/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux10Proof

/-!
# Aux. lemma 10: the factorization through a compact hull, with the hull named

Packet PROVE-T14-BR9. Specification Aux. lemma 10, proof (pp. 69–71). A conformal map `F` of an open `Ω ⊆ ℍ` onto `ℍ`
whose complement `ℍ \ Ω` keeps a positive distance from a real point `x` factors as `F = M ∘ g_A ∘ m` on `Ω`, where
`m(z) = −1/(z − x)`, `A = m(ℍ \ Ω)` is a compact `ℍ`-hull, `g_A` its mapping-out function and `M` a real Möbius map.

`Aux10.exists_protected_factorization` (PROVE-T14-BR8) proves the factorization with the hull existentially
quantified; the proof of Aux. lemma 10 needs the hull itself (`A = m(ℍ \ Ω)`, `ℍ \ A = m(Ω)`) and the sign of the
determinant of `M`. `exists_factorization` gives them; its proof is BR8's.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE

namespace Aux10

open Sec5.CrossRestart

/-- The Möbius map `m_x(z) = −1/(z − x)` sending the real point `x` to `∞`. -/
abbrev mobAt (x : ℝ) : ℂ → ℂ := realMobius 0 (-1) 1 (-x)

theorem mobAt_apply (x : ℝ) (z : ℂ) : mobAt x z = -(z - x)⁻¹ := by
  simp [mobAt, realMobius, sub_eq_add_neg, div_eq_mul_inv]

theorem mobAt_det (x : ℝ) : (0 : ℝ) < 0 * (-x) - (-1) * 1 := by norm_num

/-- The inverse `n_x(w) = x − 1/w` of `m_x`. -/
abbrev mobAtInv (x : ℝ) : ℂ → ℂ := realMobius (-x) 1 (-1) 0

theorem mobAtInv_mobAt (x : ℝ) {z : ℂ} (hz : z ∈ H) : mobAtInv x (mobAt x z) = z := by
  simpa [mobAt, mobAtInv] using QuantumZipper.CA.realMobius_inv_apply (mobAt_det x) hz

theorem mobAt_mobAtInv (x : ℝ) {w : ℂ} (hw : w ∈ H) : mobAt x (mobAtInv x w) = w := by
  simpa [mobAt, mobAtInv] using realMobius_mobInv (mobAt_det x) hw

theorem bijOn_mobAt (x : ℝ) : BijOn (mobAt x) H H := QuantumZipper.CA.bijOn_realMobius_H (mobAt_det x)

/-- **The factorization with the hull named.** Let `Ω ⊆ ℍ` be open and `F` holomorphic and injective on `Ω` with
`F(Ω) = ℍ`, and let the real point `x` keep a distance `δ > 0` from `ℍ \ Ω`. Then `A = m_x(ℍ \ Ω)` is a compact
`ℍ`-hull with `ℍ \ A = m_x(Ω)`, and `F = M ∘ g_A ∘ m_x` on `Ω` for a mapping-out function `g_A` and a real Möbius
map `M` of positive determinant. -/
theorem exists_factorization {Ω : Set ℂ} {F : ℂ → ℂ} {x : ℝ}
    (hΩo : IsOpen Ω) (hΩH : Ω ⊆ H) (hFd : DifferentiableOn ℂ F Ω) (hFinj : InjOn F Ω)
    (hFim : F '' Ω = H) {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ z ∈ H \ Ω, δ ≤ ‖z - (x : ℂ)‖) :
    IsHPHull (mobAt x '' (H \ Ω)) ∧ H \ mobAt x '' (H \ Ω) = mobAt x '' Ω ∧
      ∃ (g : ℂ → ℂ) (a b c d : ℝ), IsMapOut (mobAt x '' (H \ Ω)) g ∧ 0 < a * d - b * c ∧
        ∀ z ∈ Ω, F z = realMobius a b c d (g (mobAt x z)) := by
  set m := mobAt x with hm
  set n := mobAtInv x with hn
  set A : Set ℂ := m '' (H \ Ω) with hAdef
  have hdetn : (0 : ℝ) < (-x) * 0 - 1 * (-1) := by norm_num
  have hbijm : BijOn m H H := bijOn_mobAt x
  have hbijn : BijOn n H H := QuantumZipper.CA.bijOn_realMobius_H hdetn
  have hmd : DifferentiableOn ℂ m H := differentiableOn_realMobius (mobAt_det x)
  have hnd : DifferentiableOn ℂ n H := differentiableOn_realMobius hdetn
  have hcompl : H \ A = m '' Ω := by
    ext w
    constructor
    · rintro ⟨hw, hwA⟩
      obtain ⟨z, hz, rfl⟩ := hbijm.surjOn hw
      refine ⟨z, ?_, rfl⟩
      by_contra hzD
      exact hwA ⟨z, ⟨hz, hzD⟩, rfl⟩
    · rintro ⟨z, hzD, rfl⟩
      refine ⟨hbijm.mapsTo (hΩH hzD), ?_⟩
      rintro ⟨z', hz', hmz⟩
      have heq := hbijm.injOn (hΩH hzD) hz'.1 hmz.symm
      exact hz'.2 (heq ▸ hzD)
  have hD1open : IsOpen (H \ A) := by
    rw [hcompl]
    exact QuantumZipper.CA.isOpen_image_of_injOn QuantumZipper.isOpen_H hmd hbijm.injOn hΩo hΩH
  have hFbij : BijOn F Ω H := by
    refine ⟨fun z hz => ?_, hFinj, fun w hw => ?_⟩
    · rw [← hFim]; exact ⟨z, hz, rfl⟩
    · rw [← hFim] at hw; exact hw
  have hDsc : IsSimplyConnected Ω := by
    let e := QuantumZipper.CA.univalentOPH hΩo hFd hFinj
    have hψd : DifferentiableOn ℂ e.symm H := by
      rw [← hFim]
      exact QuantumZipper.CA.differentiableOn_univalentOPH_symm hΩo hFd hFinj
    have hψmaps : ∀ w ∈ H, e.symm w ∈ Ω := by
      intro w hw
      have hw' : w ∈ e.target := by
        rw [QuantumZipper.CA.univalentOPH_target, hFim]
        exact hw
      exact e.map_target hw'
    have hψinj : InjOn e.symm H := by
      intro w hw w' hw' heq
      have h1 := QuantumZipper.CA.univalentOPH_apply_symm_apply hΩo hFd hFinj (hFim.symm ▸ hw)
      have h2 := QuantumZipper.CA.univalentOPH_apply_symm_apply hΩo hFd hFinj (hFim.symm ▸ hw')
      calc w = F (e.symm w) := h1.symm
        _ = F (e.symm w') := by rw [heq]
        _ = w' := h2
    have hψb : BijOn e.symm H Ω :=
      ⟨hψmaps, hψinj, fun z hz => ⟨F z, hFbij.mapsTo hz,
        QuantumZipper.CA.univalentOPH_symm_apply_apply hΩo hFd hFinj hz⟩⟩
    exact isSimplyConnected_of_isConformalBijection QuantumZipper.isOpen_H ⟨hψd, hψb⟩ isSimplyConnected_H
  have hD1sc : IsSimplyConnected (H \ A) := by
    rw [hcompl]
    have hmconf : IsConformalBijection m Ω (m '' Ω) :=
      ⟨hmd.mono hΩH, ⟨fun z hz => ⟨z, hz, rfl⟩, hbijm.injOn.mono hΩH,
        fun w hw => by rcases hw with ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩⟩⟩
    exact isSimplyConnected_of_isConformalBijection hΩo hmconf hDsc
  have hAbdd : Bornology.IsBounded A := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨1 / δ, ?_⟩
    rintro w ⟨z, hz, rfl⟩
    rw [hm, mobAt_apply, norm_neg, norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hδ (hsep z hz)
  have hA : IsHPHull A := by
    refine ⟨?_, hAbdd, hD1open, hD1sc⟩
    rintro w ⟨z, hz, rfl⟩
    exact hbijm.mapsTo hz.1
  obtain ⟨g, hg⟩ := hA.exists_isMapOut
  have hnmap : MapsTo n (H \ A) Ω := by
    intro w hw
    have hw' : w ∈ H \ A := hw
    rw [hcompl] at hw'
    obtain ⟨z, hzD, hwz⟩ := hw'
    have : m z = m (n w) := by rw [hwz, hn, hm, mobAt_mobAtInv x hw.1]
    have hzn : z = n w := hbijm.injOn (hΩH hzD) (hbijn.mapsTo hw.1) this
    exact hzn ▸ hzD
  have hφ₁d : DifferentiableOn ℂ (F ∘ n) (H \ A) := hFd.comp (hnd.mono sdiff_subset) hnmap
  have hφ₁bij : BijOn (F ∘ n) (H \ A) H := by
    refine ⟨fun w hw => hFbij.mapsTo (hnmap hw), fun w hw w' hw' heq => ?_, fun y hy => ?_⟩
    · exact hbijn.injOn hw.1 hw'.1 (hFinj (hnmap hw) (hnmap hw') heq)
    · obtain ⟨z, hzD, hφz⟩ := hFbij.surjOn hy
      refine ⟨m z, by rw [hcompl]; exact ⟨z, hzD, rfl⟩, ?_⟩
      change F (n (m z)) = y
      rw [hn, hm, mobAtInv_mobAt x (hΩH hzD), hφz]
  have hid : IsConformalBijection id (H \ ∅) H := by
    rw [sdiff_empty]
    exact ⟨differentiableOn_id, fun z hz => hz, fun _ _ _ _ h => h, fun z hz => ⟨z, hz, rfl⟩⟩
  obtain ⟨a, b, c, d, hdet, hconj⟩ :=
    exists_realMobius_conj (A := A) (B := ∅) (g := g) (G := id) (φ := F ∘ n) hA hg hφ₁d
      (by rw [sdiff_empty]; exact hφ₁bij) hid
  refine ⟨hA, hcompl, g, a, b, c, d, hg, hdet, fun z hz => ?_⟩
  have hmzA : m z ∈ H \ A := by rw [hcompl]; exact ⟨z, hz, rfl⟩
  have h := hconj (m z) hmzA
  change F (n (m z)) = realMobius a b c d (g (m z)) at h
  rwa [hn, hm, mobAtInv_mobAt x (hΩH hz)] at h

end Aux10

end InteractingSLE
