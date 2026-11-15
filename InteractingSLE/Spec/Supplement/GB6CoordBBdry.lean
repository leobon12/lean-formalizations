/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3RelGB6Chart
import InteractingSLE.Spec.Supplement.GB6Version
import Mathlib.Topology.ExtendFrom

/-!
# GB6's relative map at real boundary visits

The landing theorem in `Q3RelGB6Chart` supplies the boundary values. Their
continuous extension is used here on the closed upper half-plane away from
the closed inverted flow hull. Its values are limits along a fixed vertical
sequence, so measurability can be obtained from the mapping-out functions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex MeasureTheory
open QuantumZipper (H Hbar)

namespace InteractingSLE.Supp8.GB6.CoordB

open Q3Rel (invHull)

/-- The open domain of the relative chart. -/
def relDomain (U : ℝ → ℝ) (s : ℝ) : Set ℂ := H \ invHull U s

/-- Points of the closed upper half-plane away from the retained hull. -/
def relSafe (U : ℝ → ℝ) (s : ℝ) : Set ℂ := Hbar \ closure (invHull U s)

/-- The relative map extended through the real boundary off the retained hull. -/
def relBdry (U : ℝ → ℝ) (s : ℝ) : ℂ → ℂ := extendFrom (relDomain U s) (relMap U s)

/-- A fixed vertical sequence for reading the boundary value. -/
def vert (n : ℕ) (z : ℂ) : ℂ := z + (1 / ((n : ℝ) + 1) : ℝ) * I

theorem tendsto_vert (z : ℂ) : Tendsto (fun n => vert n z) atTop (𝓝 z) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [vert, Function.comp_apply, Complex.ofReal_zero, zero_mul, add_zero] using
    (tendsto_const_nhds (x := z)).add (h.mul_const I)

theorem vert_mem_H {z : ℂ} (hz : z ∈ Hbar) (n : ℕ) : vert n z ∈ H := by
  change 0 < (vert n z).im
  have hz' : 0 ≤ z.im := hz
  simp only [vert, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
    add_zero]
  exact add_pos_of_nonneg_of_pos hz' (by positivity)

theorem tendsto_vert_relDomain {U : ℝ → ℝ} {s : ℝ} {z : ℂ} (hz : z ∈ relSafe U s) :
    Tendsto (fun n => vert n z) atTop (𝓝[relDomain U s] z) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_vert z, ?_⟩
  have hev : ∀ᶠ n in atTop, vert n z ∉ closure (invHull U s) :=
    (tendsto_vert z).eventually (isClosed_closure.isOpen_compl.mem_nhds hz.2)
  filter_upwards [hev] with n hn
  exact ⟨vert_mem_H hz.1 n, fun h => hn (subset_closure h)⟩

theorem relSafe_subset_closure_relDomain (U : ℝ → ℝ) (s : ℝ) :
    relSafe U s ⊆ closure (relDomain U s) := by
  intro z hz
  have ht := tendsto_vert_relDomain hz
  exact mem_closure_of_tendsto (tendsto_vert z) (tendsto_principal.1 (ht.mono_right inf_le_right))

theorem exists_tendsto_relMap {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ relSafe U s) :
    ∃ v, Tendsto (relMap U s) (𝓝[relDomain U s] z) (𝓝 v) := by
  by_cases hzH : z ∈ H
  · have hK : -z⁻¹ ∉ QuantumZipper.fwdHull U s := by
      intro h
      exact hz.2 (subset_closure ⟨-z⁻¹, h, neg_inv_neg_inv z⟩)
    exact ⟨relMap U s z, (continuousAt_relMap hU hs hzH hK).tendsto.mono_left nhdsWithin_le_nhds⟩
  · have him : z.im = 0 := le_antisymm (not_lt.1 hzH) hz.1
    have he : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [ofReal_im] using him
    obtain ⟨v, hv⟩ := Q3Rel.tendsto_relMap hU hU0 hs (y := z.re) (he ▸ hz.2)
    exact ⟨v, he ▸ hv⟩

/-- The extension is continuous at both interior and real boundary points
away from the closed retained hull. -/
theorem continuousOn_relBdry {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) : ContinuousOn (relBdry U s) (relSafe U s) :=
  continuousOn_extendFrom (relSafe_subset_closure_relDomain U s)
    (fun _ hz => exists_tendsto_relMap hU hU0 hs hz)

theorem tendsto_relMap_relBdry {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ relSafe U s) :
    Tendsto (relMap U s) (𝓝[relDomain U s] z) (𝓝 (relBdry U s z)) :=
  tendsto_extendFrom (exists_tendsto_relMap hU hU0 hs hz)

/-- On the interior the extension is the original chart. -/
theorem relBdry_eq {U : ℝ → ℝ} (hU : Continuous U) {s : ℝ} (hs : 0 ≤ s)
    {z : ℂ} (hz : z ∈ H) (hzA : z ∉ closure (invHull U s)) :
    relBdry U s z = relMap U s z := by
  have hK : -z⁻¹ ∉ QuantumZipper.fwdHull U s := by
    intro h
    exact hzA (subset_closure ⟨-z⁻¹, h, neg_inv_neg_inv z⟩)
  exact extendFrom_eq (subset_closure ⟨hz, fun h => hzA (subset_closure h)⟩)
    ((continuousAt_relMap hU hs hz hK).tendsto.mono_left nhdsWithin_le_nhds)

/-- A countable vertical formula for the boundary value. -/
theorem tendsto_relMap_vert {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ relSafe U s) :
    Tendsto (fun n => relMap U s (vert n z)) atTop (𝓝 (relBdry U s z)) :=
  (tendsto_relMap_relBdry hU hU0 hs hz).comp (tendsto_vert_relDomain hz)

theorem relBdry_eq_limUnder {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ relSafe U s) :
    relBdry U s z = limUnder atTop (fun n => relMap U s (vert n z)) :=
  (tendsto_relMap_vert hU hU0 hs hz).limUnder_eq.symm

/-- Composing the boundary extension with a physical curve preserves
continuity, including at its real visits. -/
theorem continuousOn_relBdry_comp {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {γ : ℝ → ℂ} {P : Set ℝ} (hc : ContinuousOn γ P)
    (hγ : MapsTo γ P (relSafe U s)) : ContinuousOn (fun t => relBdry U s (γ t)) P :=
  (continuousOn_relBdry hU hU0 hs).comp hc hγ

end InteractingSLE.Supp8.GB6.CoordB
