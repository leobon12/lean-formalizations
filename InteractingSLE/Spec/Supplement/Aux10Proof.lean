/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux10
import InteractingSLE.Foundations.Loewner.ConformalImageFull
import InteractingSLE.Foundations.Topology.PathComplement
import InteractingSLE.Spec.Sec5.CrossRestartMobius

/-!
# Proof tools for Aux. lemma 10

Specification pp. 69–71. This file begins with the factorization of a protected
conformal domain change into a real Möbius map, a hydrodynamic map, and another
real Möbius map. The Loewner image theorems for the individual factors are in
`ConformalImageFull` and `Sec5.CrossRestart`.
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

/-- Factor a conformal map from a protected domain through a compact half-plane
hull. The point `x` is a real boundary point outside the domain complement; the
separation hypothesis is what makes the Möbius image of that complement
bounded. -/
theorem exists_protected_factorization {D : Set ℂ} {φ : ℂ → ℂ} {x : ℝ}
    (hDopen : IsOpen D) (hDH : D ⊆ H)
    (hφd : DifferentiableOn ℂ φ D) (hφinj : InjOn φ D)
    (hφimage : φ '' D = H)
    (hsep : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ H \ D, δ ≤ ‖z - (x : ℂ)‖) :
    ∃ (A : Set ℂ) (g : ℂ → ℂ) (a b c d : ℝ), IsHPHull A ∧ IsMapOut A g ∧
      ∀ z ∈ D, φ z = realMobius a b c d (g (realMobius 0 (-1) 1 (-x) z)) := by
  obtain ⟨δ, hδ, hsep⟩ := hsep
  let m : ℂ → ℂ := realMobius 0 (-1) 1 (-x)
  let n : ℂ → ℂ := realMobius (-x) 1 (-1) 0
  let A : Set ℂ := m '' (H \ D)
  have hdetm : (0 : ℝ) < 0 * (-x) - (-1) * 1 := by norm_num
  have hdetn : (0 : ℝ) < (-x) * 0 - 1 * (-1) := by norm_num
  have hbijm : BijOn m H H := QuantumZipper.CA.bijOn_realMobius_H hdetm
  have hbijn : BijOn n H H := QuantumZipper.CA.bijOn_realMobius_H hdetn
  have hmd : DifferentiableOn ℂ m H := differentiableOn_realMobius hdetm
  have hnd : DifferentiableOn ℂ n H := differentiableOn_realMobius hdetn
  have hn_m (z : ℂ) (hz : z ∈ H) : n (m z) = z := by
    change realMobius (-x) 1 (-1) 0 (realMobius 0 (-1) 1 (-x) z) = z
    simpa [m, n] using QuantumZipper.CA.realMobius_inv_apply hdetm hz
  have hm_n (z : ℂ) (hz : z ∈ H) : m (n z) = z := by
    change realMobius 0 (-1) 1 (-x) (realMobius (-x) 1 (-1) 0 z) = z
    simpa [m, n] using realMobius_mobInv hdetm hz
  have hcompl : H \ A = m '' D := by
    ext w
    constructor
    · rintro ⟨hw, hwA⟩
      obtain ⟨z, hz, rfl⟩ := hbijm.surjOn hw
      refine ⟨z, ?_, rfl⟩
      by_contra hzD
      exact hwA ⟨z, ⟨hz, hzD⟩, rfl⟩
    · rintro ⟨z, hzD, rfl⟩
      refine ⟨hbijm.mapsTo (hDH hzD), ?_⟩
      rintro ⟨z', hz', hmz⟩
      have heq := hbijm.injOn (hDH hzD) hz'.1 hmz.symm
      exact hz'.2 (heq ▸ hzD)
  have hD1open : IsOpen (H \ A) := by
    rw [hcompl]
    exact QuantumZipper.CA.isOpen_image_of_injOn QuantumZipper.isOpen_H hmd
      hbijm.injOn hDopen hDH
  have hφbij : BijOn φ D H := by
    refine ⟨?_, hφinj, ?_⟩
    · intro z hz
      rw [← hφimage]
      exact ⟨z, hz, rfl⟩
    · intro w hw
      rw [← hφimage] at hw
      exact hw
  have hDsc : IsSimplyConnected D := by
    let e := QuantumZipper.CA.univalentOPH hDopen hφd hφinj
    have hψd : DifferentiableOn ℂ e.symm H := by
      rw [← hφimage]
      exact QuantumZipper.CA.differentiableOn_univalentOPH_symm hDopen hφd hφinj
    have hψmaps : ∀ w ∈ H, e.symm w ∈ D := by
      intro w hw
      have hw' : w ∈ e.target := by
        rw [QuantumZipper.CA.univalentOPH_target, hφimage]
        exact hw
      exact e.map_target hw'
    have hψinj : InjOn e.symm H := by
      intro w hw w' hw' heq
      have h1 := QuantumZipper.CA.univalentOPH_apply_symm_apply hDopen hφd hφinj
        (hφimage.symm ▸ hw)
      have h2 := QuantumZipper.CA.univalentOPH_apply_symm_apply hDopen hφd hφinj
        (hφimage.symm ▸ hw')
      calc
        w = φ (e.symm w) := h1.symm
        _ = φ (e.symm w') := by rw [heq]
        _ = w' := h2
    have hψb : BijOn e.symm H D := by
      refine ⟨hψmaps, hψinj, fun z hz => ?_⟩
      refine ⟨φ z, hφbij.mapsTo hz, ?_⟩
      exact QuantumZipper.CA.univalentOPH_symm_apply_apply hDopen hφd hφinj hz
    exact isSimplyConnected_of_isConformalBijection QuantumZipper.isOpen_H
      ⟨hψd, hψb⟩ isSimplyConnected_H
  have hD1sc : IsSimplyConnected (H \ A) := by
    rw [hcompl]
    have hmconformal : IsConformalBijection m D (m '' D) :=
      ⟨hmd.mono hDH, ⟨fun z hz => ⟨z, hz, rfl⟩, hbijm.injOn.mono hDH,
        fun w hw => by
          rcases hw with ⟨z, hz, rfl⟩
          exact ⟨z, hz, rfl⟩⟩⟩
    exact isSimplyConnected_of_isConformalBijection hDopen hmconformal hDsc
  have hAbdd : Bornology.IsBounded A := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨1 / δ, ?_⟩
    rintro w ⟨z, hz, rfl⟩
    have hmz : m z = -((z - (x : ℂ))⁻¹) := by
      simp [m, realMobius, sub_eq_add_neg, div_eq_mul_inv]
    have hnorm : ‖m z‖ = 1 / ‖z - (x : ℂ)‖ := by
      rw [hmz, norm_neg, norm_inv]
      simp [one_div]
    rw [hnorm]
    exact one_div_le_one_div_of_le hδ (hsep z hz)
  have hA : IsHPHull A := by
    refine ⟨?_, hAbdd, hD1open, hD1sc⟩
    rintro w ⟨z, hz, rfl⟩
    exact hbijm.mapsTo hz.1
  obtain ⟨g, hg⟩ := hA.exists_isMapOut
  let φ₁ : ℂ → ℂ := φ ∘ n
  have hnmap : MapsTo n (H \ A) D := by
    intro w hw
    have hwH : w ∈ H := hw.1
    have hw' : w ∈ H \ A := hw
    rw [hcompl] at hw'
    obtain ⟨z, hzD, hwz⟩ := hw'
    have hmw : m (n w) = w := hm_n w hwH
    have : m z = m (n w) := by rw [hwz, hmw]
    have hzn : z = n w := hbijm.injOn (hDH hzD) (hbijn.mapsTo hwH) this
    exact hzn ▸ hzD
  have hφ₁d : DifferentiableOn ℂ φ₁ (H \ A) := by
    exact hφd.comp (hnd.mono sdiff_subset) hnmap
  have hφ₁bij : BijOn φ₁ (H \ A) H := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      exact hφbij.mapsTo (hnmap hw)
    · intro w hw w' hw' heq
      have hnn : n w = n w' := hφinj (hnmap hw) (hnmap hw') heq
      exact hbijn.injOn hw.1 hw'.1 hnn
    · intro y hy
      obtain ⟨z, hzD, hφz⟩ := hφbij.surjOn hy
      refine ⟨m z, ?_, ?_⟩
      · rw [hcompl]
        exact ⟨z, hzD, rfl⟩
      · change φ (n (m z)) = y
        rw [hn_m z (hDH hzD), hφz]
  have hid0 : IsConformalBijection id H H := by
    constructor
    · fun_prop
    · exact ⟨fun z hz => hz, fun _ _ _ _ h => h, fun z hz => ⟨z, hz, rfl⟩⟩
  have hid : IsConformalBijection id (H \ ∅) H := by
    simpa using hid0
  obtain ⟨a, b, c, d, hdet, hconj⟩ :=
    exists_realMobius_conj (A := A) (B := ∅) (g := g) (G := id) (φ := φ₁)
      hA hg hφ₁d (by simpa using hφ₁bij) hid
  refine ⟨A, g, a, b, c, d, hA, hg, fun z hz => ?_⟩
  have hmzH : m z ∈ H := hbijm.mapsTo (hDH hz)
  have hmzA : m z ∈ H \ A := by
    rw [hcompl]
    exact ⟨z, hz, rfl⟩
  have h := hconj (m z) hmzA
  change φ (n (m z)) = realMobius a b c d (g (m z)) at h
  rw [hn_m z (hDH hz)] at h
  exact h

end Aux10

end InteractingSLE
