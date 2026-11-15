import InteractingSLE.Spec.Sec5.Aux61RestartCollar
import InteractingSLE.Spec.Sec5.Aux61RestartPrimeEnd
import InteractingSLE.Foundations.Loewner.ConformalImageReflect
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# Reading the current access through nested mapping-out functions

Packet PROVE-AUX61-R1; ruling R71. In a coordinate retaining the original target
at infinity, let `A ⊆ B` be the own prefix hull and the filled retained hull.
A free half-disc of the own inverse chart inside `ℍ \ B` gives a real boundary
limit of the additional mapping-out function. This supplies the seed access
without assuming a boundary extension theorem for the old kissing set.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

/-- At a fresh own-time restart, the old centered forward map sends the
continuation to zero in the open half-plane. Only an eventual pre-contact
segment is used; no unbounded continuation in the retained component is assumed.
-/
theorem tendsto_own_chart_at_restart {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (hr : 0 ≤ r)
    (hnew : ∀ᶠ t in 𝓝[>] r, η t ∈ H \ QuantumZipper.fwdHull W r) :
    Tendsto (fun t => QuantumZipper.fwdMap W r (η t)) (𝓝[>] r) (𝓝[H] 0) := by
  let γ := loewnerTip (QuantumZipper.RS.shiftDrive W r)
  have hclock : Tendsto (fun t : ℝ => t - r) (𝓝[>] r) (𝓝[Ici 0] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hsub : Tendsto (fun t : ℝ => t - r) (𝓝 r) (𝓝 (r - r)) :=
        (continuous_id.sub continuous_const).tendsto r
      simpa only [sub_self] using hsub.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_nonneg.2 (show r < t from ht).le
  have hγlim : Tendsto (fun t => γ (t - r)) (𝓝[>] r) (𝓝 0) := by
    have h := (hη.continuousWithinAt_shift_Ici hW hW0 hr (le_refl (0 : ℝ))).tendsto.comp hclock
    have hγ0 : γ 0 = 0 := loewnerTip_shiftDrive_zero hW r
    change Tendsto (fun t => γ (t - r)) (𝓝[>] r) (𝓝 (γ 0)) at h
    rw [hγ0] at h
    exact h
  have heq : (fun t => γ (t - r)) =ᶠ[𝓝[>] r]
      fun t => QuantumZipper.fwdMap W r (η t) := by
    filter_upwards [self_mem_nhdsWithin, hnew] with t ht hηt
    have ht' : r < t := ht
    obtain ⟨hγbar, hFγ, _⟩ := hη.extendFrom_shift_tip hW hW0 hr (sub_nonneg.2 ht'.le)
    rw [add_sub_cancel] at hFγ
    have hγH : γ (t - r) ∈ H := by
      by_contra hnot
      have hreal : (γ (t - r)).im = 0 :=
        le_antisymm (not_lt.1 hnot) hγbar
      exact hη.extendFrom_not_mem hW hW0 hr hreal (hFγ ▸ hηt)
    have hFcont := (isConformalBijection_fwdMapInv hW hW0 hr).1.continuousOn
    rw [extendFrom_H_eq hFcont hγH] at hFγ
    have hG := QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hr hγH
    rw [hFγ] at hG
    exact hG.symm
  refine tendsto_nhdsWithin_iff.2 ⟨hγlim.congr' heq, ?_⟩
  exact hnew.mono fun t ht => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr ht

/-- The own-chart collar supplies a real access in the chart of the larger
retained hull. The target remains the hydrodynamic infinity of `B`.
The real number `a` is the current driver in the uncentered own map. -/
theorem exists_chart_access_of_nested_hulls {A B : Set ℂ} (hA : IsHPHull A)
    (hB : IsHPHull B) (hAB : A ⊆ B) {g F : ℂ → ℂ} (hg : IsMapOut A g) {a : ℝ}
    (hF : MapsTo F H (H \ A)) (hinv : ∀ w ∈ H, g (F w) = w + (a : ℂ))
    (hcollar : ∃ δ > 0, MapsTo F (ball 0 δ ∩ H) (H \ B)) :
    ∃ (ψ : HChart (H \ B)) (x : ℝ), IsMapOut B ψ.1 ∧
      Tendsto (ψ.1 ∘ F) (𝓝[H] 0) (PrimeEnd.approachH (x : OnePoint ℝ)) := by
  obtain ⟨δ, hδ, hfree⟩ := hcollar
  let E := g '' (B \ A)
  have hE : IsHPHull E := hg.isHPHull_image hA hB hAB
  obtain ⟨G, hG⟩ := hE.exists_isMapOut
  have hdisj : Disjoint (ball (a : ℂ) δ) E := by
    rw [Set.disjoint_left]
    rintro z hz ⟨y, hy, hgy⟩
    have hzH : z ∈ H := hgy ▸ hg.1.2.mapsTo ⟨hB.1 hy.1, hy.2⟩
    have hwH : z - (a : ℂ) ∈ H := by
      change 0 < (z - (a : ℂ)).im
      simpa only [sub_im, ofReal_im, sub_zero] using (show 0 < z.im from hzH)
    have hwball : z - (a : ℂ) ∈ ball 0 δ := by
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
    have hFy := hfree ⟨hwball, hwH⟩
    have heq : F (z - (a : ℂ)) = y := hg.1.2.injOn (hF hwH)
      ⟨hB.1 hy.1, hy.2⟩ (by rw [hinv _ hwH, sub_add_cancel, hgy])
    exact hFy.2 (heq ▸ hy.1)
  obtain ⟨L, hLreal, hL⟩ := hG.exists_tendsto_of_disjoint hE hdisj
    (mem_ball_self (half_pos hδ)) (ofReal_im a)
  have hshift : Tendsto (fun w : ℂ => w + (a : ℂ)) (𝓝[H] 0)
      (𝓝[ball (a : ℂ) (δ / 2) ∩ H] (a : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hshift0 : Tendsto (fun w : ℂ => w + (a : ℂ)) (𝓝 0) (𝓝 (0 + (a : ℂ))) :=
        (continuous_id.add continuous_const).tendsto (0 : ℂ)
      simpa only [zero_add] using hshift0.mono_left (nhdsWithin_le_nhds (s := H))
    · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) (half_pos hδ))] with w hwH hwball
      refine ⟨?_, ?_⟩
      · simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hwball
      · change 0 < (w + (a : ℂ)).im
        simpa only [add_im, ofReal_im, add_zero] using (show 0 < w.im from hwH)
  let ψ : HChart (H \ B) := ⟨G ∘ g, (hg.comp hA hB hAB hG).1⟩
  have hlim : Tendsto (ψ.1 ∘ F) (𝓝[H] 0) (𝓝 L) := by
    refine (hL.comp hshift).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [ψ, Function.comp_apply, hinv w hw]
  have hmaps : ∀ᶠ w in 𝓝[H] 0, ψ.1 (F w) ∈ H := by
    filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) hδ)] with w hwH hwball
    exact ψ.mapsTo (hfree ⟨hwball, hwH⟩)
  have hLre : (L.re : ℂ) = L := Complex.ext rfl (by simpa only [ofReal_im] using hLreal.symm)
  refine ⟨ψ, L.re, hg.comp hA hB hAB hG, ?_⟩
  exact tendsto_nhdsWithin_iff.2 ⟨hLre ▸ hlim, hmaps⟩

end InteractingSLE.Sec5.Aux61Restart
