/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CollarBoundary
import InteractingSLE.Foundations.Loewner.ConformalImageFullAux8

/-!
# Two-time Loewner calculus: the time derivatives behind (D1)

Packet PROVE-ZHAN-GT4-A3. Source: Astra, *Follow-up proofs and dependency audit*, Part A.1.1
(`source/external/AstraIG1/ig1_followup_proofs.txt` L245–L275, ruling R38): "For disjoint hulls `K₁(s)`, `K₂(t)`, let
`g_j` be the individual hydrodynamic maps and `G` the map of their union. Put `h_j = G ∘ g_j⁻¹` … For fixed `t_k`,
differentiation of `G = h_j ∘ g_j`, with the image-capacity derivative `A²_{j,1}`, gives (D1)
`∂_{t_j} h_j(z) = 2A²_{j,1}/(h_j(z) − A_{j,0}) − 2h_j'(z)/(z − W_j)`."

This file proves the two time derivatives that (D1) is obtained from, with the other hull `A = K_k(t_k)` frozen:

* `hasDerivWithinAt_gmap`: the Loewner equation `∂_s g_s(w) = 2/(g_s(w) − W_s)` for the uncentred map of a point alive
  on `[0, T]` (from the integral equation of `IsForwardSol` and the fundamental theorem of calculus);
* `exists_union_chain`: the union map in the moving chart, `G_s(w) = g̃_{a(s)}(φ(w)) = h_s(g_s(w))` (Specification
  Aux. lemma 8, (HD3), landed as `exists_loewner_image_rate_of_pos`), satisfies
  `∂_s G_s(w) = 2 h_s'(W_s)² / (G_s(w) − h_s(W_s))`: the image chain runs at capacity rate `ȧ(s) = h_s'(W_s)²`
  (`A²_{j,1}`) with driver `W̃(a(s)) = h_s(W_s)` (`A_{j,0}`).

Here `h_s = R` is any mapping-out function of the image `g_s(A)` of the frozen hull, `h_s'(W_s)` is the derivative at
`W_s` of its holomorphic extension across the real line, and `φ = g_A`. (D1) itself, the partial derivative of
`s ↦ h_s(z)` at a fixed `z`, follows from these two identities by the chain rule `G_s = h_s ∘ g_s` once
`(s, z) ↦ h_s(z)` is known to be jointly `C¹` near `(s, g_s(w))`; that joint regularity is not proved here.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper QuantumZipper.RS

/-- **The Loewner equation in time for the uncentred map**: for a point `z` alive on `[0, T]`,
`∂_s g_s(z) = 2/(g_s(z) − W_s)` within `[0, T]` (`g_s = f_s + W_s`, `f_s = fwdMap W s`). -/
theorem hasDerivWithinAt_gmap {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => fwdMap W s z + W s) (2 / fwdMap W t z) (Icc 0 T) t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  set v : ℝ → ℂ := fun r => 2 / u (projIcc 0 T hT r) with hv
  have hvc : Continuous v := by
    refine continuous_const.div (hu.1.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun r => (projIcc 0 T hT r).2) fun r => (hu.2 _ (projIcc 0 T hT r).2).1
  have hint : ∀ s ∈ Icc 0 T, fwdMap W s z + W s = z + ∫ r in (0 : ℝ)..s, v r := by
    intro s hs
    rw [fwdMap_eq_of_isForwardSol hW hu hs, (hu.2 s hs).2]
    have : ∫ r in (0 : ℝ)..s, 2 / u r = ∫ r in (0 : ℝ)..s, v r := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      simp only [hv, projIcc_of_mem hT ⟨hr.1, hr.2.trans hs.2⟩]
    rw [this]
    ring
  have hd : HasDerivAt (fun s => z + ∫ r in (0 : ℝ)..s, v r) (v t) t :=
    ((hvc.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add z
  have hvt : v t = 2 / fwdMap W t z := by
    simp only [hv, projIcc_of_mem hT ht, fwdMap_eq_of_isForwardSol hW hu ht]
  rw [← hvt]
  exact hd.hasDerivWithinAt.congr (fun s hs => hint s hs) (hint t ht)

/-- **The union map in the moving chart and its time derivative** (the input of (D1)). Let `W` be continuous,
`T > 0`, `A` a compact `ℍ`-hull with mapping-out function `φ`, and `closure A ∩ closure K_T = ∅`. There are a
capacity clock `a` (`a 0 = 0`, strictly increasing) and a continuous image driver `W̃` such that, for every
`t ∈ [0, T]`, every mapping-out function `h = R` of `g_t(A)` and every holomorphic extension `R̂` of `R` across the
real line near `W_t`, and every `w ∈ ℍ \ (A ∪ K_T)`:
`G_s(w) = g̃_{a(s)}(φ(w))` equals `h(g_t(w))` at `s = t` and has derivative
`2 R̂'(W_t)² / (G_t(w) − W̃(a(t)))` within `[0, T]` at `t`. (`W̃(a(t))` is the boundary value of `h` at `W_t`.) -/
theorem exists_union_chain {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (fwdHull W T))) :
    ∃ (a : ℝ → ℝ) (W' : ℝ → ℝ), Continuous W' ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 T) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ R : ℂ → ℂ, IsMapOut ((fun z => fwdMap W t z + W t) '' A) R →
        Tendsto R (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) ∧
        ∀ δ > (0 : ℝ), ∀ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) →
          EqOn Rext R (ball (W t : ℂ) δ ∩ H) →
          0 < (deriv Rext (W t)).re ∧ (deriv Rext (W t)).im = 0 ∧
          ∀ w ∈ H \ (A ∪ fwdHull W T),
            fwdMap W' (a t) (φ w) + W' (a t) = R (fwdMap W t w + W t) ∧
            HasDerivWithinAt (fun s => fwdMap W' (a s) (φ w) + W' (a s))
              (2 * ((deriv Rext (W t)).re : ℂ) ^ 2 / (R (fwdMap W t w + W t) - W' (a t))) (Icc 0 T) t := by
  obtain ⟨a, W', hW'c, ha0, hamono, -, hmain⟩ := ConformalImageFull.exists_loewner_image_rate_of_pos hW hT hA hφ hd
  refine ⟨a, W', hW'c, ha0, hamono, fun t ht R hRm => ?_⟩
  obtain ⟨-, -, hR⟩ := hmain t ht
  obtain ⟨h1, h2, -, hrate⟩ := hR R hRm
  refine ⟨h2, fun δ hδ Rext hRd hRe => ?_⟩
  obtain ⟨hpos, him, hder⟩ := hrate δ hδ Rext hRd hRe
  refine ⟨hpos, him, fun w hw => ?_⟩
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hwA : w ∉ A := fun h => hw.2 (Or.inl h)
  have hwK : w ∉ fwdHull W T := fun h => hw.2 (Or.inr h)
  have hwKt : w ∉ fwdHull W t := fun h => hwK (fwdHull_mono.1 ht.2 h)
  have heq := h1 w ⟨hw.1, fun h => h.elim hwA hwKt⟩
  refine ⟨heq, ?_⟩
  -- `φ(w)` is alive for the image chain up to `a(T)`
  have haT : 0 ≤ a T := by
    rw [← ha0]; exact hamono.monotoneOn ⟨le_rfl, hT.le⟩ hTmem hT.le
  have hφw : φ w ∈ H := hφ.1.2.mapsTo ⟨hw.1, hwA⟩
  have hφK : φ w ∉ fwdHull W' (a T) := by
    rw [(hmain T hTmem).2.1]
    rintro ⟨k, hk, hkw⟩
    have hkA : k ∉ A := fun hkA =>
      Set.disjoint_left.1 hd (subset_closure hkA) (subset_closure hk)
    have hkH : k ∈ H := (fwdHull_mono.2 T) hk
    exact hwK (hφ.1.2.injOn ⟨hkH, hkA⟩ ⟨hw.1, hwA⟩ hkw ▸ hk)
  obtain ⟨u', hu'⟩ := exists_isForwardSol_of_not_mem_fwdHull haT hφw hφK
  have hat : a t ∈ Icc 0 (a T) := by
    refine ⟨?_, hamono.monotoneOn ht hTmem ht.2⟩
    rw [← ha0]; exact hamono.monotoneOn ⟨le_rfl, hT.le⟩ ht ht.1
  have hmaps : MapsTo a (Icc 0 T) (Icc 0 (a T)) := fun s hs => by
    refine ⟨?_, hamono.monotoneOn hs hTmem hs.2⟩
    rw [← ha0]; exact hamono.monotoneOn ⟨le_rfl, hT.le⟩ hs hs.1
  have hg := hasDerivWithinAt_gmap hW'c hu' hat
  have hcomp := hg.scomp t hder hmaps
  refine hcomp.congr_deriv ?_
  have hfw : fwdMap W' (a t) (φ w) = R (fwdMap W t w + W t) - W' (a t) := by
    rw [← heq]; ring
  rw [hfw, real_smul]
  push_cast
  ring

end InteractingSLE.ZhanGT4
