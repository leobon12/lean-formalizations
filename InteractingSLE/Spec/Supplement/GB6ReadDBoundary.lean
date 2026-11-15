/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBCurve

/-!
# Inverse boundary read-back for the relative chart

The retained chart already lands off its finite exceptional set. Extending
that inverse from the half-plane recovers safe physical points, including
real visits, whenever their chart images avoid the exceptional set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open QuantumZipper (H Hbar)

namespace InteractingSLE.Supp8.GB6.ReadD

/-- Interior points and the nonexceptional real boundary. -/
def invGood (S : Finset ℝ) : Set ℂ := H ∪ {z | z.im = 0 ∧ z.re ∉ S}

/-- The boundary extension of an inverse chart. -/
def invExt (F : ℂ → ℂ) : ℂ → ℂ := extendFrom H F

theorem invGood_subset_closure (S : Finset ℝ) : invGood S ⊆ closure H := by
  intro z hz
  rw [closure_H]
  rcases hz with hz | ⟨hz, -⟩
  · exact (show 0 < z.im from hz).le
  · exact hz.ge

section Retained

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {S : Finset ℝ}
  (hΨ : Q3Rel.IsRetainedChartOff A Ψ Ψi LΨ S)

include hΨ

theorem exists_tendsto_inv {z : ℂ} (hz : z ∈ invGood S) :
    ∃ p, Tendsto Ψi (𝓝[H] z) (𝓝 p) := by
  rcases hz with hz | ⟨him, hS⟩
  · exact ⟨Ψi z, (hΨ.diff_inv.continuousOn z hz).tendsto⟩
  · have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
    rw [he]
    exact hΨ.inv_lands z.re hS

theorem tendsto_invExt {z : ℂ} (hz : z ∈ invGood S) :
    Tendsto Ψi (𝓝[H] z) (𝓝 (invExt Ψi z)) :=
  tendsto_extendFrom (exists_tendsto_inv hΨ hz)

theorem continuousOn_invExt : ContinuousOn (invExt Ψi) (invGood S) :=
  continuousOn_extendFrom (invGood_subset_closure S) (fun _ hz => exists_tendsto_inv hΨ hz)

theorem invExt_eq {z : ℂ} (hz : z ∈ H) : invExt Ψi z = Ψi z :=
  extendFrom_eq (subset_closure hz) ((hΨ.diff_inv.continuousOn z hz).tendsto)

/-- The extended inverse recovers a physical point from its forward limit.
The physical point may lie on the real boundary. -/
theorem invExt_of_forward_limit {z y : ℂ} (hz : z ∈ closure (H \ A))
    (hy : y ∈ invGood S) (hf : Tendsto Ψ (𝓝[H \ A] z) (𝓝 y)) : invExt Ψi y = z := by
  have : (𝓝[H \ A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
  have hfH : Tendsto Ψ (𝓝[H \ A] z) (𝓝[H] y) :=
    tendsto_nhdsWithin_iff.2 ⟨hf, eventually_nhdsWithin_of_forall fun v hv => hΨ.conf.2.mapsTo hv⟩
  have hlim := (tendsto_invExt hΨ hy).comp hfH
  have hid : Tendsto (fun v => Ψi (Ψ v)) (𝓝[H \ A] z) (𝓝 z) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun v hv => (hΨ.inv_fwd hv).symm)
  exact tendsto_nhds_unique hlim hid

end Retained

/-- Specialization to GB6's forward extension on safe physical points. -/
theorem invExt_relBdry {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hΨ : Q3Rel.IsRetainedChartOff (Q3Rel.invHull U s) (relMap U s) (relInv U s)
      (Q3Rel.relLog U s) (Q3Rel.relBad U s))
    {z : ℂ} (hz : z ∈ CoordB.relSafe U s)
    (hy : CoordB.relBdry U s z ∈ invGood (Q3Rel.relBad U s)) :
    invExt (relInv U s) (CoordB.relBdry U s z) = z :=
  invExt_of_forward_limit hΨ (CoordB.relSafe_subset_closure_relDomain U s hz) hy
    (CoordB.tendsto_relMap_relBdry hU hU0 hs hz)

/-- A closed relative hull avoiding the exceptional points lies in the
landing domain of the inverse chart. -/
theorem mem_invGood_of_mem_closure {S : Finset ℝ} {K : Set ℂ} (hK : K ⊆ H)
    (hS : ∀ b ∈ S, (b : ℂ) ∉ closure K) {z : ℂ} (hz : z ∈ closure K) : z ∈ invGood S := by
  have hb : z ∈ Hbar := by
    rw [← closure_H]
    exact closure_mono hK hz
  rcases eq_or_lt_of_le (show 0 ≤ z.im from hb) with him | him
  · refine Or.inr ⟨him.symm, fun h => ?_⟩
    have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him.symm)
    exact hS z.re h (he ▸ hz)
  · exact Or.inl him

end InteractingSLE.Supp8.GB6.ReadD
