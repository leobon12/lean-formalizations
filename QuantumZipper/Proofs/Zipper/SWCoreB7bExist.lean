import QuantumZipper.Proofs.Zipper.SWCoreN2IdPush

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b (3): existence of the pushed regularized limits over a family (for the `𝔥₀` add-on)

Decision D64 / D59. For a finite-parameter Lipschitz family of class maps, almost surely, for
every small radius `r`, every map of the family and every real centre `t ∈ [a − r, b + r]`, the
regularized pairings `∫ avgReg x j d(fc(t,r).map (Ψ q))` **converge** (to `evalReg`), not only
have a `limUnder` value. This is what adding a continuous function to the field needs
(`evalReg (x + φ) ν = evalReg x ν + ∫ φ dν`, `Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3`).

* `swcB7_push_tendsto`: the statement; proof = the uniform convergence of the smoothed family
  (`swcNA2_tendstoUniformlyOn_avgReg`) for the pushed family of `swcN2_push_bounds`, read at the
  singleton parameter `(q,t)` and transported by `swcN2_push_eq` (exactly the construction inside
  `swcN2_push_ae`, which only exported continuity and the raw identification).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1; Sheffield–Wang,
arXiv:1605.06171, Lemma 3.5; through the repository nodes cited. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open Thm18Asm.G1RC

variable {n : ℕ} {a b ρ M m L : ℝ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)}
  {Kπ : ℝ≥0} {pr : (Fin n → ℝ) → Fin n → ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **Existence of the pushed regularized limits over a family.** -/
theorem swcB7_push_tendsto (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hL0 : 0 ≤ L)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ pr) (hπK : ∀ q, pr q ∈ K) (hπid : ∀ q ∈ K, pr q = q)
    (hX : IsFreeGFFModConstH X P) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ r ∈ Ioo 0 r₂, ∀ᵐ ω ∂P, ∀ q ∈ K, ∀ t ∈ Icc (a - r) (b + r),
      Tendsto (fun j => ∫ u, avgReg (X ω) j u ∂((foldedCircle (t : ℂ) r).map (Ψ q))) atTop
        (𝓝 (evalReg (X ω) ((foldedCircle (t : ℂ) r).map (Ψ q)))) := by
  obtain ⟨r₂, hr₂, h⟩ := swcN2_push_bounds hab hρ hm hΨ hL0 hL hπ hπK
  refine ⟨min r₂ (ρ / 3), lt_min hr₂ (by linarith), fun r hr => ?_⟩
  have hr' : r ∈ Ioo 0 r₂ := ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
  have hrρ : 3 * r < ρ := by have := lt_of_lt_of_le hr.2 (min_le_right _ _); linarith
  obtain ⟨hc, hH, hb⟩ := h r hr'
  obtain ⟨β, hβ, hB⟩ := swcNA2_familyBounds hc hH one_pos le_rfl one_pos le_rfl hb
  obtain ⟨Y₀, -, -, hU⟩ := swcNA2_tendstoUniformlyOn_avgReg (m := circM)
    (S := Icc 0 (2 * Real.pi)) hc hH isCompact_Icc circM_compl hβ hB hX
  filter_upwards [hU] with ω hω q hq t ht
  have hT : Tendsto (fun j => ∫ u, avgReg (X ω) j u ∂(circM.map
      (swcN2PushΦ Ψ pr a b r (Fin.snoc q t : Fin (n + 1) → ℝ)))) atTop
      (𝓝 (Y₀ (Fin.snoc q t) ω)) :=
    (hω {Fin.snoc q t} isCompact_singleton).tendsto_at (mem_singleton _)
  rw [swcN2_push_eq hab.le hr.1 hrρ hΨ hπid hq ht] at hT
  have he : evalReg (X ω) ((foldedCircle (t : ℂ) r).map (Ψ q)) = Y₀ (Fin.snoc q t) ω :=
    hT.limUnder_eq
  rw [he]
  exact hT

end SWCore
end QuantumZipper
