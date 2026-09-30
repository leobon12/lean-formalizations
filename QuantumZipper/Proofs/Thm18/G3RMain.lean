import QuantumZipper.Proofs.Thm18.G3RCore2
import QuantumZipper.Proofs.Thm18.R18G3TXSide4
import QuantumZipper.Proofs.Thm18.R18G3TRSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): the `R(x)`-side of `B → C` from the region-1 tail node

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, pp. 71–72 and Remark 5.7 (D85 update 18:30).
`g3TCutToProfRStmt_of_tail : G3TRegion1TailStmt → G3TCutToProfRStmt`.

* The tail node gives `F > 0` everywhere a.s. (`ae_g3F_pos`), hence the truncation error of the
  change of measure vanishes (`tendsto_g3T`).
* The mixing body of `B` (full zooms) passes to region zooms off the area-failure event
  (`g3p_symmDiff_subset_area₂`, `g3TCutAreaStmt_holds`), then through the shift `Ψ` to the sets of
  `rside_core`; the result passes back to full zooms of `C` (`g3TProfAreaStmt_holds`).

Own bookkeeping (AGENT_GUIDE cost rule); the pattern is `R18G3TXSide4`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- **The conditional tail is positive everywhere, a.s.** (from the tail node). -/
theorem ae_g3F_pos (hT : G3TRegion1TailStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    ∀ᵐ ω ∂gffBase.P, ∀ v, 0 < g3F γ i ω v := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂gffBase.P, 0 < g3F γ i ω q := fun q => by
    have e := rcdTail_ae_eq_condExp (P := gffBase.P) (outsideSigma2_le gffBase.gff i.t₁ i.r₁ i.t₂ i.r₂)
      (measurable_g3Y' γ i) (q : ℝ)
    have hset : {ω' : Ω₀ | ENNReal.ofReal (q : ℝ) ≤
        g3pν₁ γ (g3wProf γ) i ω' (Icc (-i.δ) 0)} = {x | (q : ℝ) ≤ g3Y γ i x} := by
      ext ω'
      have hfin : g3pν₁ γ (g3wProf γ) i ω' (Icc (-i.δ) 0) ≠ ⊤ :=
        ne_top_of_le_ne_top (g3pm_Icc_lt_top γ (g3wProf γ) i ω' (-i.δ) 0).ne
          (by rw [Measure.add_apply]; exact le_self_add)
      simp only [mem_setOf_eq, g3Y]
      exact ENNReal.ofReal_le_iff_le_toReal hfin
    have ht := hT γ hγ hγ2 i q
    rw [hset] at ht
    filter_upwards [ht, e] with ω h1 h2
    have h3 : 0 < (g3F γ i ω q).toReal := by
      have : (g3F γ i ω q).toReal = (rcdTail (g3O i) gffBase.P (g3Y γ i) ω q).toReal := rfl
      rw [this, h2]; exact h1
    exact ENNReal.toReal_pos_iff.1 h3 |>.1
  filter_upwards [ae_all_iff.2 hq] with ω hω v
  obtain ⟨q, hq⟩ := exists_rat_gt v
  refine (hω q).trans_le ?_
  exact measure_mono (Ici_subset_Ici.2 hq.le)

/-- `T` only depends on `δ, η` (not on the zoom level). -/
theorem g3T_congr {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1)
    (m : ℝ) (K : ℝ≥0∞) :
    g3T γ i {p | |g3pR γ (g3wProf γ) i p - i.t₂| + m < i.r₂} K =
      g3T γ i' {p | |g3pR γ (g3wProf γ) i' p - i'.t₂| + m < i'.r₂} K := by
  obtain ⟨⟨a, b, c⟩, hp⟩ := i
  obtain ⟨⟨a', b', c'⟩, hp'⟩ := i'
  simp only at h₁ h₂
  subst h₁ h₂
  rfl

end R18
end QuantumZipper
