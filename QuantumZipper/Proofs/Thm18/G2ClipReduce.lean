import QuantumZipper.Proofs.Thm18.G2LenSmoothRNode
import QuantumZipper.Proofs.Thm18.G2ClipFrozen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 clipped-shift nodes from the rooted bump disintegration

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66) proves the clipped-shift claims
(`G2RootXClipSmoothStmt`, `G2RootRClipSmoothStmt`) by conditioning on `h₀` in `h = α φ + h₀`:
given `h₀` and the root, the length is a smooth increasing function of the Gaussian `α`, the
clipped length is the same function shifted by an `α`-independent amount in `[0, ρ]`, and the
zoom and the outside event do not see `α`.

This file isolates the *structural* part as the nodes `G2RootXDisintStmt` / `G2RootRDisintStmt`:
the rooted measures of the unclipped and of the clipped events are, up to `ε` (the zoom-locality
error, small for large `C`), the `Q ⊗ N`-measures of `{(ξ, f ξ α) ∈ S}` and of
`{(ξ, f ξ α − min(gap ξ, ρ)) ∈ S}`, with the *same* event `S` and a gap `≥ 0` independent of `α`.
Here `ξ = (h₀, root)` with `Q(dh₀, dx) = P(dh₀) ν_{h₀}(dx)` on the margin (the rooted measure is
unchanged by the bump there: `ν_{h₀ + αφ} = e^{γαφ/2} ν_{h₀}` equals `ν_{h₀}` off `supp φ`), `N` is
the Gaussian law of `α` (`G2BumpDecompStmt`, `G2ClipNodes.lean`), and `f ξ` is the length as a
function of `α`.

The analytic part — the density argument — is proved: `g2clip_frozen` (`G2ClipFrozen.lean`).
`g2RootXClipSmoothStmt_of_disint` and `g2RootRClipSmoothStmt_of_disint` assemble the two
(own elementary bookkeeping, AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **Node (rooted bump disintegration, `x` side; Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66).** See the module docstring. -/
def G2RootXDisintStmt (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∃ ρ₀ > 0, ∀ ε > 0,
    ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (Q : Measure Ξ) (_ : IsFiniteMeasure Q)
      (N : Measure ℝ) (_ : IsProbabilityMeasure N) (f : Ξ → ℝ → ℝ),
      N ≪ volume ∧ Measurable (Function.uncurry f) ∧ (∀ ξ, Differentiable ℝ (f ξ)) ∧
      (∀ ξ a, 0 < deriv (f ξ) a) ∧
      ∀ κ ∈ Ioo 0 ρ₀, ∃ gap : Ξ → ℝ, Measurable gap ∧ (∀ ξ, 0 ≤ gap ξ) ∧
        ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
          ∀ G : Set (gffBase.Ω × ℝ),
          MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
          ∃ S : Set (Ξ × ℝ), MeasurableSet S ∧
            |(g3RootInt γ i ((g3RootEvX γ i s m G).indicator 1)).toReal -
              (Q.prod N).real {p | (p.1, f p.1 p.2) ∈ S}| ≤ ε ∧
            ∀ ρ > 0, |(g3RootInt γ i ((g3RootEvXclip γ i s m κ ρ G).indicator 1)).toReal -
              (Q.prod N).real {p | (p.1, f p.1 p.2 - min (gap p.1) ρ) ∈ S}| ≤ ε

/-- **Node (rooted bump disintegration, `R` side; bump in region 2 between `0` and `y − κ`;
Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 66, and of Thm. 1.8, p. 71).** -/
def G2RootRDisintStmt (γ : ℝ) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∃ ρ₀ > 0, ∀ ε > 0,
    ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (Q : Measure Ξ) (_ : IsFiniteMeasure Q)
      (N : Measure ℝ) (_ : IsProbabilityMeasure N) (f : Ξ → ℝ → ℝ),
      N ≪ volume ∧ Measurable (Function.uncurry f) ∧ (∀ ξ, Differentiable ℝ (f ξ)) ∧
      (∀ ξ a, 0 < deriv (f ξ) a) ∧
      ∀ κ ∈ Ioo 0 ρ₀, ∃ gap : Ξ → ℝ, Measurable gap ∧ (∀ ξ, 0 ≤ gap ξ) ∧
        ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
          ∀ G : Set (gffBase.Ω × ℝ),
          MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
          ∃ S : Set (Ξ × ℝ), MeasurableSet S ∧
            |(g3RootIntR γ i ((g3RootEvR γ i t m G ∩ g3TM γ i).indicator 1)).toReal -
              (Q.prod N).real {p | (p.1, f p.1 p.2) ∈ S}| ≤ ε ∧
            ∀ ρ > 0, |(g3RootIntR γ i ((g3RootEvRclip γ i t m κ ρ G).indicator 1)).toReal -
              (Q.prod N).real {p | (p.1, f p.1 p.2 - min (gap p.1) ρ) ∈ S}| ≤ ε

/-- The common assembly: three `ε/3` estimates. -/
theorem g2clip_three {A B q₁ q₂ ε : ℝ} (h1 : |A - q₁| ≤ ε / 3) (h2 : |q₁ - q₂| ≤ ε / 3)
    (h3 : |B - q₂| ≤ ε / 3) : |A - B| ≤ ε := by
  have a := abs_sub_le A q₁ B
  have b := abs_sub_le q₁ q₂ B
  rw [abs_sub_comm B q₂] at h3
  linarith

theorem g2clip_shift_bound {gap : ℝ} (hg : 0 ≤ gap) {ρ ρ₁ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ < ρ₁) :
    |-min gap ρ| < ρ₁ := by
  rw [abs_neg, abs_of_nonneg (le_min hg hρ.le)]
  exact (min_le_right _ _).trans_lt hρ₁

/-- **`G2RootXClipSmoothStmt` from the rooted bump disintegration** and the proved
frozen-coefficient estimate `g2clip_frozen`. -/
theorem g2RootXClipSmoothStmt_of_disint {γ : ℝ} (hX : G2RootXDisintStmt γ) :
    G2RootXClipSmoothStmt γ := by
  intro s hs δ η m hm ε hε
  obtain ⟨ρ₀, hρ₀, hD⟩ := hX s hs δ η m hm
  obtain ⟨Ξ, _, Q, _, N, _, f, hN, hfm, hf, hpos, hK⟩ := hD (ε / 3) (by positivity)
  obtain ⟨ρ₁, hρ₁, hfr⟩ := g2clip_frozen Q hN f hfm hf hpos (ε := ε / 3) (by positivity)
  have hmin : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
  refine ⟨min ρ₀ ρ₁ / 2, by positivity, fun κ hκ => ?_⟩
  have hκ0 : κ ∈ Ioo 0 ρ₀ := ⟨hκ.1, hκ.2.trans_le (by linarith [min_le_left ρ₀ ρ₁])⟩
  obtain ⟨gap, hgm, hg0, hev⟩ := hK κ hκ0
  filter_upwards [hev] with C hC i hi G hG
  obtain ⟨S, hS, h1, h2⟩ := hC i hi G hG
  have h2' := h2 (min ρ₀ ρ₁ / 2) (by positivity)
  have h3 := hfr S hS (fun ξ => -min (gap ξ) (min ρ₀ ρ₁ / 2)) (hgm.min measurable_const).neg
    (fun ξ => g2clip_shift_bound (hg0 ξ) (by positivity)
      (by linarith [min_le_right ρ₀ ρ₁]))
  simp only [← sub_eq_add_neg] at h3
  exact g2clip_three h1 h3 h2'

/-- **`G2RootRClipSmoothStmt` from the rooted bump disintegration** (`R` side). -/
theorem g2RootRClipSmoothStmt_of_disint {γ : ℝ} (hR : G2RootRDisintStmt γ) :
    G2RootRClipSmoothStmt γ := by
  intro t ht δ η m hm ε hε
  obtain ⟨ρ₀, hρ₀, hD⟩ := hR t ht δ η m hm
  obtain ⟨Ξ, _, Q, _, N, _, f, hN, hfm, hf, hpos, hK⟩ := hD (ε / 3) (by positivity)
  obtain ⟨ρ₁, hρ₁, hfr⟩ := g2clip_frozen Q hN f hfm hf hpos (ε := ε / 3) (by positivity)
  have hmin : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
  refine ⟨min ρ₀ ρ₁ / 2, by positivity, fun κ hκ => ?_⟩
  have hκ0 : κ ∈ Ioo 0 ρ₀ := ⟨hκ.1, hκ.2.trans_le (by linarith [min_le_left ρ₀ ρ₁])⟩
  obtain ⟨gap, hgm, hg0, hev⟩ := hK κ hκ0
  filter_upwards [hev] with C hC i hi G hG
  obtain ⟨S, hS, h1, h2⟩ := hC i hi G hG
  have h2' := h2 (min ρ₀ ρ₁ / 2) (by positivity)
  have h3 := hfr S hS (fun ξ => -min (gap ξ) (min ρ₀ ρ₁ / 2)) (hgm.min measurable_const).neg
    (fun ξ => g2clip_shift_bound (hg0 ξ) (by positivity)
      (by linarith [min_le_right ρ₀ ρ₁]))
  simp only [← sub_eq_add_neg] at h3
  exact g2clip_three h1 h3 h2'

/-- **Both G2 length-smoothing nodes from the two rooted bump disintegrations.** -/
theorem g2RootLenSmooth_of_disint {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : G2RootXDisintStmt γ) (hR : G2RootRDisintStmt γ) :
    G2RootXLenSmoothStmt γ ∧ G2RootRLenSmoothStmt γ :=
  g2RootLenSmooth_of_clip hγ hγ2 (g2RootXClipSmoothStmt_of_disint hX)
    (g2RootRClipSmoothStmt_of_disint hR)

end Thm18Asm
end QuantumZipper
