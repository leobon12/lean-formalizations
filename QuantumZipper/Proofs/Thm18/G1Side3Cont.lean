import QuantumZipper.Proofs.Thm18.G1Side3AS
import QuantumZipper.Proofs.Zipper.SWCoreNA2Unif

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (11): continuum smoothing limits on the pushed circles of a uniform area family

For a uniform family `SwcNA2Unif F c a …` and a regular version `G` of the free field, almost
surely, for every dyadic level `k ≥ k₁` and every parameter `q`, the smoothed pairings
`σ ↦ ∫ G(u, σ) d((fc(c q, a q 2^{-k})).map (F q))` converge as `σ → 0⁺`
(`ae_family_continuum`). The Kolmogorov bounds of the smoothed pushed family are those built
inside `SWCore.swcNA2I_primed` (`swcNA2_familyBounds` with the scale facts `swcNA2F_scale`); the
uniform limit is `SWCore.swcNA2_tendstoUniformlyOn_smoothing`. Sheffield–Wang arXiv:1605.06171
Lemmas 3.4–3.5 (pathwise); Hu–Miller–Peres 2010 Prop. 2.1. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore Thm18Asm.G1RC

variable {n : ℕ} {F : (Fin n → ℝ) → ℂ → ℂ} {c : (Fin n → ℝ) → ℂ} {a : (Fin n → ℝ) → ℝ}
  {x₁ x₂ y₁ y₂ ρ M m H : ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

/-- **Continuum smoothing limits on the pushed circles, a.s.** -/
theorem ae_family_continuum (hX : IsFreeGFFModConstH X P) (hG : WedgeTK.IsRegVersion X P G)
    (h : SwcNA2Unif F c a x₁ x₂ y₁ y₂ ρ M m H) :
    ∃ k₁ : ℕ, ∀ᵐ ω ∂P, ∀ k ≥ k₁, ∀ q : Fin n → ℝ, ∃ Y : ℝ,
      Tendsto (fun σ => ∫ u, G ω (u, σ) ∂((foldedCircle (c q) (a q * radius k)).map (F q)))
        (𝓝[>] 0) (𝓝 Y) := by
  have hρ := h.rho_pos
  have hm := h.m_pos
  obtain ⟨k₁, K, hK, hsc⟩ := swcNA2F_scale h
  refine ⟨k₁, ?_⟩
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂P, k₁ ≤ k → ∀ q : Fin n → ℝ, ∃ Y : ℝ,
      Tendsto (fun σ => ∫ u, G ω (u, σ) ∂((foldedCircle (c q) (a q * radius k)).map (F q)))
        (𝓝[>] 0) (𝓝 Y) := by
    intro k
    by_cases hk1 : k₁ ≤ k
    swap
    · exact ae_of_all _ fun ω h' => absurd h' hk1
    have hmem : ∀ q θ, circleMap (c q) (a q * radius k) θ ∈ thickening ρ (rectC x₁ x₂ y₁ y₂) :=
      fun q θ => swcNA2I_mem_thick (h.cen q) (swcNA2I_circ_norm _ (hsc k hk1 q).1.le θ).le
        (hsc k hk1 q).2.1
    have hcμ : Continuous (uncurry (swcPhiPush F c a k)) := by
      have hu : Continuous fun p : (Fin n → ℝ) × ℝ =>
          circleMap (c p.1) (a p.1 * radius k) p.2 := by
        have hcC : Continuous c := swcNA2F_cont_of_lip h.H_nonneg h.c_lip
        have haC : Continuous a := swcNA2F_cont_of_lip h.H_nonneg fun q q' => by
          rw [Real.norm_eq_abs]; exact h.a_lip q q'
        simp only [circleMap]; fun_prop
      exact swcNA2F_joint (G := F) (fun q => (h.cls q).1.continuousOn) h.F_lip hu
        (fun p => hmem p.1 p.2)
    have hHμ : ∀ q θ, swcPhiPush F c a k q θ ∈ Hbar := fun q θ => by
      show 0 ≤ (F q (circleMap (c q) (a q * radius k) θ)).im
      linarith [((h.cls q).2.2.1 _ (hmem q θ)).2]
    have hnμ : ∀ q θ, ‖swcPhiPush F c a k q θ‖ ≤ |M| := fun q θ =>
      ((h.cls q).2.2.1 _ (hmem q θ)).1.trans (le_abs_self M)
    have hr := swcNA2I_radius_pos k
    obtain ⟨β, hβ, hB⟩ := swcNA2_familyBounds hcμ hHμ one_pos le_rfl one_pos le_rfl fun R =>
      ⟨|M|, 24 / (m * radius k), K, abs_nonneg _, by positivity, hK, fun q _ =>
        ⟨hnμ q, (hsc k hk1 q).2.2.2.2.2.1, fun q' _ θ => by
          rw [Real.rpow_one]; exact (hsc k hk1 q).2.2.2.2.2.2.2.1 q' θ⟩⟩
    obtain ⟨Y₀, -, -, hU⟩ := swcNA2_tendstoUniformlyOn_smoothing (m := circM)
      (S := Icc 0 (2 * Real.pi)) hcμ hHμ isCompact_Icc circM_compl hβ hB hX hG
    filter_upwards [hU] with ω hω _ q
    refine ⟨Y₀ q ω, ?_⟩
    have ht := (hω {q} isCompact_singleton).tendsto_at (mem_singleton q)
    have e : circM.map (swcPhiPush F c a k q) = (foldedCircle (c q) (a q * radius k)).map (F q) :=
      swcNA2I_map_push (h.cls q) (h.cen q) (hsc k hk1 q).1 (hsc k hk1 q).2.1 (hsc k hk1 q).2.2.1
    rw [← e]
    exact ht
  rw [← ae_all_iff] at hk
  filter_upwards [hk] with ω hω k hk1 q
  exact hω k hk1 q

end G1Side
end QuantumZipper
