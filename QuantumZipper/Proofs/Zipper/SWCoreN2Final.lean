import QuantumZipper.Proofs.Zipper.SWCoreN2Raw
import QuantumZipper.Proofs.Zipper.SWCoreN2IdMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2 (7): the boundary distortion core for finite-parameter families of class maps

**Restricted form of `SWCore.BdryDistClassStmt`** (orchestrator's allowance, `handoff/SW-CORE.md`
§3: the consumers' maps are finite-parameter families). For a family `q ↦ Ψ q` of maps of one
boundary class `BdryClass a b ρ M m` (`a < b`, `ρ, m > 0`), indexed by a bounded set `K ⊂ ℝⁿ` that
admits a Lipschitz retraction (e.g. a box), Lipschitz in `q` in sup norm on the `ρ`-thickening,
the free boundary GFF satisfies almost surely `BdryDistFamGood γ (X ω) Ψ K a b`: for every
`η > 0`, eventually in `k`, for all `q ∈ K`, `t ∈ [a,b]`,

  `|avgReg (coordChange x (Ψ q) Q) k t − Q cc(Ψ q, t, r_k) − evalReg x (fc(Ψ_q(t), r_k ‖Ψ_q'(t)‖))| ≤ η`

(`swcn2_bdryDistFam`), i.e. exactly the inequality of `BdryDistClassGood`, uniformly over the
family. Proof: pathwise identification `swcN2_id` (the helper's SWC-N2-ID: (i) the circle average
of `x∘Ψ_q + Q log|Ψ_q'|` is `evalReg` of the pushed semicircle plus `Q cc`, (ii) continuity in
`(q,t)`, (iii) `evalReg` = raw value a.s. per point), the raw smallness on a countable dense set
(`swcn2_family_raw`), and density + continuity.
Sheffield–Wang, arXiv:1605.06171, Lemmas 3.4–3.5 (pp. 15–16), pathwise. Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

/-- **Distortion, uniformly over a finite-parameter family** (one field sample). -/
def BdryDistFamGood (γ : ℝ) (x : FieldSample) {n : ℕ} (Ψ : (Fin n → ℝ) → ℂ → ℂ)
    (K : Set (Fin n → ℝ)) (a b : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ K, ∀ t ∈ Icc a b,
    |avgReg (coordChange x (Ψ q) (Qc γ)) k (t : ℂ) - Qc γ * CoordChange.cc (Ψ q) t (radius k) -
      evalReg x (foldedCircle (((Ψ q t).re : ℝ) : ℂ) (radius k * ‖deriv (Ψ q) t‖))| ≤ η

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- A continuous function bounded by `η` on a dense subset is bounded by `η`. -/
theorem swcn2_le_of_dense {α : Type*} [TopologicalSpace α] {S D : Set α} {f : α → ℝ}
    (hf : ContinuousOn f S) (hDS : D ⊆ S) (hSD : S ⊆ closure D) {η : ℝ}
    (hD : ∀ x ∈ D, |f x| ≤ η) : ∀ x ∈ S, |f x| ≤ η := by
  intro x hx
  have hne : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hSD hx)
  have ht : Tendsto f (𝓝[D] x) (𝓝 (f x)) :=
    (hf x hx).tendsto.mono_left (nhdsWithin_mono x hDS)
  exact le_of_tendsto ht.abs (eventually_nhdsWithin_of_forall hD)

/-- **SWC-N2: the boundary distortion core for finite-parameter families.** -/
theorem swcn2_bdryDistFam (hX : IsFreeGFFModConstH X P) (γ : ℝ) {n : ℕ}
    (Ψ : (Fin n → ℝ) → ℂ → ℂ) (K : Set (Fin n → ℝ)) {a b ρ M m L R : ℝ} {Kπ : ℝ≥0}
    {π : (Fin n → ℝ) → Fin n → ℝ} (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    (hR : 0 ≤ R) (hKR : ∀ q ∈ K, ‖q‖ ≤ R) :
    ∀ᵐ ω ∂P, BdryDistFamGood γ (X ω) Ψ K a b := by
  obtain ⟨k₀, hid, hraw⟩ := swcN2_id (Ψ := Ψ) (K := K) hab hρ hm hcl hL hlip hπ hπK hπid
    (Qc γ) hX
  set S : Set ((Fin n → ℝ) × ℝ) := K ×ˢ Icc a b with hS
  obtain ⟨D, hDS, hDc, hSD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hsmall := swcn2_family_raw hX Ψ K hab hρ hm hL hcl hlip hR hKR hDc hDS
    (P := P)
  -- a.s. identification of `evalReg` with the raw values on `D`, for all `k ≥ k₀`
  have hDc' : (D ×ˢ (univ : Set ℕ)).Countable := hDc.prod (Set.to_countable _)
  have hev : ∀ᵐ ω ∂P, ∀ p ∈ D ×ˢ (univ : Set ℕ), k₀ ≤ p.2 →
      evalReg (X ω) ((foldedCircle (p.1.2 : ℂ) (radius p.2)).map (Ψ p.1.1)) =
          X ω ((foldedCircle (p.1.2 : ℂ) (radius p.2)).map (Ψ p.1.1)) ∧
        evalReg (X ω) (foldedCircle (((Ψ p.1.1 p.1.2).re : ℝ) : ℂ)
            (radius p.2 * ‖deriv (Ψ p.1.1) p.1.2‖)) =
          X ω (foldedCircle (((Ψ p.1.1 p.1.2).re : ℝ) : ℂ)
            (radius p.2 * ‖deriv (Ψ p.1.1) p.1.2‖)) := by
    rw [ae_ball_iff hDc']
    intro p hp
    by_cases hk : k₀ ≤ p.2
    · have hpS := hDS hp.1
      obtain ⟨h1, h2⟩ := hraw p.2 hk p.1.1 hpS.1 p.1.2 hpS.2
      filter_upwards [h1, h2] with ω e1 e2 _
      exact ⟨e1, e2⟩
    · exact Eventually.of_forall fun ω h => absurd h hk
  filter_upwards [hid, hsmall, hev] with ω hid' hsm hev' η hη
  filter_upwards [hsm η hη, eventually_ge_atTop k₀] with k hk hkk q hq t ht
  obtain ⟨hiden, hc1, hc2⟩ := hid' k hkk
  set f : (Fin n → ℝ) × ℝ → ℝ := fun x =>
    evalReg (X ω) ((foldedCircle (x.2 : ℂ) (radius k)).map (Ψ x.1)) -
      evalReg (X ω) (foldedCircle (((Ψ x.1 (x.2 : ℂ)).re : ℝ) : ℂ)
        (radius k * ‖deriv (Ψ x.1) (x.2 : ℂ)‖)) with hf
  have hfc : ContinuousOn f S := hc1.sub hc2
  have hfD : ∀ x ∈ D, |f x| ≤ η := by
    intro x hx
    obtain ⟨e1, e2⟩ := hev' (x, k) ⟨hx, mem_univ _⟩ hkk
    simp only [hf]
    rw [e1, e2]
    exact hk x hx
  have hq' : (q, t) ∈ S := ⟨hq, ht⟩
  have hbound := swcn2_le_of_dense hfc hDS hSD hfD (q, t) hq'
  rw [hiden q hq t ht]
  simp only [hf] at hbound
  have e : evalReg (X ω) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) +
      Qc γ * CoordChange.cc (Ψ q) t (radius k) - Qc γ * CoordChange.cc (Ψ q) t (radius k) -
      evalReg (X ω) (foldedCircle (((Ψ q t).re : ℝ) : ℂ) (radius k * ‖deriv (Ψ q) t‖)) =
      evalReg (X ω) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) -
      evalReg (X ω) (foldedCircle (((Ψ q t).re : ℝ) : ℂ) (radius k * ‖deriv (Ψ q) t‖)) := by
    ring
  rw [e]
  exact hbound

end SWCore
end QuantumZipper
