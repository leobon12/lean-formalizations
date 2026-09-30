import QuantumZipper.Proofs.Thm18.G1RCCircle

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR2 (3): the free-field part of the pushed-circle pairings is jointly continuous up to `t = 0`

Theorem 1.8, G1 zoom, toward `G1SidePushUCRepStmt` (G1SSR2Meas.lean). Variant of
`G1RC.exists_smoothing_limit` (G1RCEval.lean) that keeps the joint continuity: almost surely the
smoothed pairings `(q, t) ↦ ∫ G(u, t) d(m.map (Φ q))(u)` (`t > 0`) agree with a function
continuous on all of `ℝⁿ⁺¹` (the continuous modification of Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1, with Revuz–Yor I.(2.1)). On compact parameter boxes this gives the uniform
Cauchy condition as `t → 0⁺` needed by `G1SSR2.UCond`. Same proof as the source lemma.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open KolmD KolmG CircleFubini WedgeTK

variable {n : ℕ} {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
variable {m : Measure Θ} [IsProbabilityMeasure m] {Φ : (Fin n → ℝ) → Θ → ℂ} {S : Set Θ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

/-- **Joint continuity of the smoothed pairings up to `t = 0`, a.s.** -/
theorem exists_smoothing_joint (hΦ : Continuous (uncurry Φ)) (hΦH : ∀ q θ, Φ q θ ∈ Hbar)
    (hS : IsCompact S) (hmS : m Sᶜ = 0)
    {β : ℝ} (hβ : 0 < β) (hB : FamilyBounds (smoothFam m Φ) β) (hX : IsFreeGFFModConstH X P)
    (hG : IsRegVersion X P G) :
    ∃ Y : (Fin (n + 1) → ℝ) → Ω → ℝ, (∀ ω, Continuous fun p => Y p ω) ∧
      ∀ᵐ ω ∂P, ∀ q : Fin n → ℝ, ∀ t : ℝ, 0 < t →
        ∫ u, G ω (u, t) ∂(m.map (Φ q)) = Y (Fin.snoc q t) ω := by
  obtain ⟨Y, hYc, hYV, -⟩ := exists_modification_family hβ hB hX
  refine ⟨Y, hYc, ?_⟩
  set U : Set (Fin (n + 1) → ℝ) := {p | 0 < p (Fin.last n)} with hU
  set L : Ω → (Fin (n + 1) → ℝ) → ℝ := fun ω p =>
    ∫ θ, G ω (Φ (Fin.init p) θ, p (Fin.last n)) ∂m with hL
  obtain ⟨D, hDc, hDU, hUD⟩ := TopologicalSpace.exists_countable_dense_subset U
  have hpt : ∀ p ∈ D, ∀ᵐ ω ∂P, L ω p = Y p ω := by
    intro p hp
    have hp' : 0 < p (Fin.last n) := hDU hp
    have hc := continuous_Phi hΦ (Fin.init p)
    have hsub : Φ (Fin.init p) '' S ⊆ Hbar := by rintro _ ⟨θ, -, rfl⟩; exact hΦH _ θ
    filter_upwards [ae_integral_G_eq hX hG hp' (m.map (Φ (Fin.init p))) (hS.image hc)
      hsub (map_compl_image hΦ hS hmS _), hYV p] with ω h1 h2
    simp only [L]
    rw [← integral_map_Phi hΦ hΦH hS hmS _ (hG.continuousOn_slice ω hp'), h1, h2,
      smoothFam_of_pos m Φ hp']
  have hall : ∀ᵐ ω ∂P, ∀ p ∈ D, L ω p = Y p ω :=
    (eventually_countable_ball hDc).2 hpt
  filter_upwards [hall] with ω hω q t ht
  have hEq : EqOn (L ω) (fun p => Y p ω) U :=
    Set.EqOn.of_subset_closure hω (continuousOn_smoothed hΦ hΦH hS hmS hG ω)
      (hYc ω).continuousOn hDU hUD
  have htU : (Fin.snoc q t : Fin (n + 1) → ℝ) ∈ U := by simp [U, ht]
  have := hEq htU
  simp only [L, Fin.init_snoc, Fin.snoc_last] at this
  rw [integral_map_Phi hΦ hΦH hS hmS q (hG.continuousOn_slice ω ht)]
  exact this

/-- **Pushed folded circles**: a.s. the pairings `∫ G(u, t) d((s ψ)_* fc(d, r))` (`t > 0`) agree
with a function jointly continuous in `(d, log r, log s, t) ∈ ℝ⁵`. -/
theorem exists_pushed_joint {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψc : ContinuousOn ψ Hbar)
    (hψH : MapsTo ψ Hbar Hbar) {β : ℝ} (hβ : 0 < β) (hB : PushFamBounds ψ β)
    (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G) :
    ∃ Y : (Fin 5 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun p => Y p ω) ∧
      ∀ᵐ ω ∂P, ∀ (d : ℂ) (r s t : ℝ), 0 < r → 0 < s → 0 < t →
        ∫ u, G ω (u, t) ∂((foldedCircle d r).map fun z => (s : ℂ) * ψ z) =
          Y (Fin.snoc (qOf d r s) t) ω := by
  obtain ⟨Y, hYc, hY⟩ := exists_smoothing_joint (continuous_pushPhi hψc)
    (pushPhi_mem_Hbar hψH) isCompact_Icc circM_compl hβ hB hX hG
  refine ⟨Y, hYc, ?_⟩
  filter_upwards [hY] with ω h d r s t hr hs ht
  rw [map_foldedCircle_eq ψ hψm d hr hs]
  exact h _ t ht

end G1RC
end Thm18Asm
end QuantumZipper
