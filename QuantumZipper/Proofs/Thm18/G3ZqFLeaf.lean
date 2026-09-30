import QuantumZipper.Proofs.Thm18.G3ZqFFix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-FIX: the two fixed-point map leaves `G3ZqFixXStmt` and `G3ZqFixRStmt`

At a fixed Palm point `x` of region 1 (`x < 0`, the side half-line of the local map on the left)
and at a fixed partner point `y` of region 2 (`y > 0`, the right side), the zoom of the Palm field
`normField γ (xPalm γ x)` through the local map of the good path `a` is asymptotically independent
of the conditioning variables of the G2 engine (outside coordinates, cut length, truncation
mass), with the `γ`-wedge law as limit. Both are instances of `fixCore` (G3ZqFFix), with the
conditioning maps of the plain engine (`G2RootXCondStmt`, `G2RootRCondStmt`, proved from the
locality of the cut lengths, `g2RootXCutLocStmt_holds`, `g2RootRCutLenLocStmt_holds`).

Sheffield, arXiv:1012.4797, Prop. 1.6 (pp. 24–25) and proof of Prop. 5.5 (pp. 65–66), through
the local maps (proof of Thm. 1.8, p. 71). Own bookkeeping, following `g2RootXFixStmt_of_model`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqF

/-- **`G3ZqFixXStmt` holds.** -/
theorem g3ZqFixXStmt_holds : G3Zq.G3ZqFixXStmt := by
  intro γ hγ hγ2 Ψ hsel a ha Ω' _ P' _ Y' hW
  intro s hs δ η m κ hκ hκm x ε hε
  by_cases hx : ∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η ∧ |x - i₀.t₁| + m < i₀.r₁
  swap
  · refine Eventually.of_forall fun C i hi G' hG' => ?_
    have hmi : ¬ |x - i.t₁| + m < i.r₁ := fun h => hx ⟨i, by rw [hi], by rw [hi], h⟩
    have he : ∀ s', g3RootXPalmEvZ (G3Zq.g3zMapZ γ Ψ true a) γ i s' m κ G' x = ∅ := fun s' =>
      eq_empty_of_forall_notMem fun ω hω => hmi hω.2.1
    rw [he, he, measure_empty]
    simpa using hε.le
  obtain ⟨i₀, hδ₀, hη₀, hx₀⟩ := hx
  have h1 := i₀.hη; have h2 := i₀.hηδ; have h3 := i₀.hδ
  have hlt : |x - i₀.t₁| < i₀.r₁ - m := by linarith
  rw [abs_lt] at hlt
  unfold G3Idx.t₁ G3Idx.r₁ at hlt
  have hxneg : x < 0 := by linarith
  have hxa : |x| = -x := abs_of_neg hxneg
  have hxr : κ / 2 < |x| := by rw [hxa]; linarith
  have hx1 : |x| + κ / 2 < 1 := by rw [hxa]; linarith
  have hxs : x ∈ g1SideHalf true := by
    simp only [g1SideHalf, if_true, mem_Iio]; exact hxneg
  have hCX := g2RootXCondStmt_of_cutLoc (g2RootXCutLocStmt_holds hγ hγ2)
  filter_upwards [fixCore hγ hγ2 hsel ha P' Y' hW hs hκ hxs hxr hx1 hε] with C hC i hi G' hG'
  obtain ⟨ht, hr⟩ := G3Idx.t₁_r₁_congr (i := i) (i' := i₀) (by rw [hi, hδ₀]) (by rw [hi, hη₀])
  have hmi : |x - i.t₁| + m < i.r₁ := by rw [ht, hr]; exact hx₀
  have hiC : i.C = C := by rw [G3Idx.C, hi]
  obtain ⟨V, hVm, hVae⟩ := hCX i m κ x hκ hκm hmi
  have e1 : g3RootXPalmEvZ (G3Zq.g3zMapZ γ Ψ true a) γ i s m κ G' x =
      {ω | G3Z2b2.g1zM γ C Ψ true ((normField γ (xPalm γ x) ω, a), x) ∈ s} ∩
        (g3PalmCond γ i κ x) ⁻¹' G' := by
    ext ω
    simp only [g3RootXPalmEvZ, G3Zq.g3zMapZ, if_pos hxs, hiC, hmi, true_and, mem_inter_iff,
      mem_setOf_eq, mem_preimage, g3PalmCond]
  have e2 : g3RootXPalmEvZ (G3Zq.g3zMapZ γ Ψ true a) γ i univ m κ G' x =
      (g3PalmCond γ i κ x) ⁻¹' G' := by
    ext ω
    simp only [g3RootXPalmEvZ, mem_univ, hmi, true_and, mem_setOf_eq, mem_preimage, g3PalmCond]
  rw [e1, e2]
  exact hC (g3PalmCond γ i κ x) ⟨V, hVm, hVae.mono fun ω h => h⟩ G' hG'

/-- **`G3ZqFixRStmt` holds.** -/
theorem g3ZqFixRStmt_holds : G3Zq.G3ZqFixRStmt := by
  intro γ hγ hγ2 Ψ hsel a ha Ω' _ P' _ Y' hW
  intro s hs δ η m κ hκ hκm x ε hε
  by_cases hx : ∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η ∧ |x - i₀.t₂| + m < i₀.r₂
  swap
  · refine Eventually.of_forall fun C i hi G' hG' => ?_
    have hmi : ¬ |x - i.t₂| + m < i.r₂ := fun h => hx ⟨i, by rw [hi], by rw [hi], h⟩
    have he : ∀ s', g3PalmEvRZ (G3Zq.g3zMapZ γ Ψ false a) γ i s' m κ G' x = ∅ := fun s' =>
      eq_empty_of_forall_notMem fun ω hω => hmi hω.2.1
    rw [he, he, measure_empty]
    simpa using hε.le
  obtain ⟨i₀, hδ₀, hη₀, hx₀⟩ := hx
  have h1 := i₀.hη; have h2 := i₀.hηδ; have h3 := i₀.hδ
  have hlt : |x - i₀.t₂| < i₀.r₂ - m := by linarith
  rw [abs_lt] at hlt
  unfold G3Idx.t₂ G3Idx.r₂ at hlt
  have hxpos : 0 < x := by linarith
  have hxa : |x| = x := abs_of_pos hxpos
  have hxr : κ / 2 < |x| := by rw [hxa]; linarith
  have hx1 : |x| + κ / 2 < 1 := by rw [hxa]; linarith
  have hxs : x ∈ g1SideHalf false := by
    simp only [g1SideHalf, Bool.false_eq_true, if_false, mem_Ioi]; exact hxpos
  have hCR := g2RootRCondStmt_of_loc (g2RootRCutLocStmt_of_len (g2RootRCutLenLocStmt_holds hγ hγ2))
  filter_upwards [fixCore hγ hγ2 hsel ha P' Y' hW hs hκ hxs hxr hx1 hε] with C hC i hi G' hG'
  obtain ⟨ht, hr⟩ := G3Idx.t₂_r₂_congr (i := i) (i' := i₀) (by rw [hi, hη₀])
  have hmi : |x - i.t₂| + m < i.r₂ := by rw [ht, hr]; exact hx₀
  have hiC : i.C = C := by rw [G3Idx.C, hi]
  obtain ⟨V, hVm, hVae⟩ := hCR i m κ x hκ hκm hmi
  have e1 : g3PalmEvRZ (G3Zq.g3zMapZ γ Ψ false a) γ i s m κ G' x =
      {ω | G3Z2b2.g1zM γ C Ψ false ((normField γ (xPalm γ x) ω, a), x) ∈ s} ∩
        (g3PalmCondR γ i κ x) ⁻¹' G' := by
    ext ω
    simp only [g3PalmEvRZ, G3Zq.g3zMapZ, if_pos hxs, hiC, hmi, true_and, mem_inter_iff,
      mem_setOf_eq, mem_preimage]
  have e2 : g3PalmEvRZ (G3Zq.g3zMapZ γ Ψ false a) γ i univ m κ G' x =
      (g3PalmCondR γ i κ x) ⁻¹' G' := by
    ext ω
    simp only [g3PalmEvRZ, mem_univ, hmi, true_and, mem_setOf_eq, mem_preimage]
  rw [e1, e2]
  exact hC (g3PalmCondR γ i κ x) ⟨V, hVm, hVae.mono fun ω h => h⟩ G' hG'

end G3ZqF
end Thm18Asm
end QuantumZipper
