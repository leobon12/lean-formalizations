/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetSepChart

/-!
# G8: strict order follows from closed hull separation

Packet PROVE-G8-DET. The seed is the inverse image of the first tip.
A surviving real point below a swallowed right mark must precede the seed,
by monotonicity of the real Loewner flow.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull IsForwardSol)

namespace InteractingSLE.RLC.G8Det.Late

/-- At an active interior cut, the original cut map tends to its driver
from the joint domain, with values in the upper half-plane. -/
theorem cutMap_tip {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hi : Function.Injective α)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a r : ℝ≥0} (haH : α a ∈ H) :
    Tendsto (cutMap α a) (𝓝[activeDomain α a β r] (α a)) (𝓝[H] (cutDrive w a 0 : ℂ)) := by
  have h := (tendsto_own_tip hi hw hw0 hgen haH).mono_left
    (nhdsWithin_mono _ (domain_subset_own hcα hcβ a r))
  have hl := h.add_const (w a : ℂ)
  rw [zero_add] at hl
  have he := cutMap_eq_original hcα hw hw0 hgen a
  have hv : cutDrive w a 0 = w a := by simp only [cutDrive, add_zero, Real.toNNReal_coe]
  rw [hv]
  refine tendsto_nhdsWithin_iff.2 ⟨hl.congr'
    (eventually_mem_nhdsWithin.mono fun z hz => (he (domain_subset_own hcα hcβ a r hz)).symm), ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with z hz
  exact (ConformalImage.isMapOut_mapOut (isHPHull_ownHull hcα hgen.1 a)).1.2.mapsTo
    (domain_subset_own hcα hcβ a r hz)

/-- The canonical seed has the first physical tip as its inverse image. -/
theorem inv_seed {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a σ r : ℝ≥0} (haσ : a < σ) (haH : α a ∈ H)
    (haD : α a ∈ closure (activeDomain α a β r))
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)))) (d : InitialChart α β a r) :
    d.inv (seedMark α β w a r) = α a := by
  have hcα := hcop.1
  have hcβ := hcop.2.2.2.2.1
  have hl := (seed_limit_of_clearance hcα hcβ hα0 hβ0 hw haσ hd).comp
    (cutMap_tip hcα hcβ hcop.2.1 hw hw0 hgen haH (r := r))
  have hlH : Tendsto (obstacleMap α β a r ∘ cutMap α a)
      (𝓝[activeDomain α a β r] (α a)) (𝓝[H] (seedMark α β w a r : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hl, eventually_mem_nhdsWithin.mono fun z hz => d.maps_fwd hz⟩
  have hbar : (seedMark α β w a r : ℂ) ∈ Hbar := by
    change 0 ≤ (seedMark α β w a r : ℂ).im; simp only [ofReal_im, le_refl]
  have hlim := ((d.continuous_inv _ hbar).mono QuantumZipper.H_subset_Hbar).tendsto.comp hlH
  have hlim' := hlim.congr' (eventually_mem_nhdsWithin.mono fun z hz => d.inv_fwd z hz)
  have : (𝓝[activeDomain α a β r] (α a)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 haD
  exact tendsto_nhds_unique hlim' (tendsto_id.mono_left nhdsWithin_le_nhds)

/-- A real point that survives below a swallowed right point lies left of
the initial driver. This is the landed real-flow monotonicity theorem. -/
theorem lt_driver_of_survives {W : ℝ → ℝ} (hW : Continuous W) {T l b : ℝ}
    (hT : 0 ≤ T) (hl : l ≠ W 0) (hlb : l < b)
    (halive : ∃ v, IsForwardSol W (l : ℂ) T v)
    (hdead : ¬ ∃ v, IsForwardSol W (b : ℂ) T v) : l < W 0 := by
  by_contra h
  have hlt : W 0 < l := lt_of_le_of_ne (not_lt.1 h) hl.symm
  obtain ⟨v, hv⟩ := halive
  exact hdead (QuantumZipper.RS.exists_isForwardSol_of_lt hW hT hlt hlb hv)

end InteractingSLE.RLC.G8Det.Late
