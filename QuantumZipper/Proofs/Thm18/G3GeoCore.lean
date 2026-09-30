import QuantumZipper.Proofs.Thm18.G3Fid2Main
import QuantumZipper.Proofs.Thm18.G3HonestFin1

/-!
# G3-GEO, part 1: geometry of the Palm point

`handoff/G3.md` / `G3G2Scale.lean`: the geometric input `G3GeoStmt γ` of the locality of the zoom
(Sheffield, arXiv:1012.4797, proof of Theorem 1.8, §5.4, pp. 70–71, Figure 1.7). The concrete
scheme (`G3Concrete.lean`) samples the Palm point by length: `x = lenLeft (ν₁ + ν₀) ℓ` with
`(ω, ℓ)` of law `w · (P₀ ⊗ Exp 1)`, `w ∝ e^ℓ 1{0 < ℓ ≤ (ν₁+ν₀)[−δ,0]}`; since `Exp 1` has
density `e^{−ℓ}`, `(ω, ℓ)` has density `1{0 < ℓ ≤ m[−δ,0]}` against `P₀ ⊗ dℓ`, so **`ℓ` is
uniform on `(0, m[−δ,0])`** and `x` is `(ν₁+ν₀)|[−δ,0]`-uniform.

Contents (own elementary arguments, AGENT_GUIDE cost rule):

* `lenLevel`, `le_lenLeft_of_mass_le`: `ℓ ≤ m[−δ,0]` with `δ > 0` forces `−δ ≤ lenLeft m ℓ`
  (the Palm point lies in `[−δ, 0]`);
* `ofReal_le_mass_Icc_of_lenLeft`: **deterministic tail estimate**: if `ℓ ≤ m[−δ,0]` and
  `−a ≤ lenLeft m ℓ`, then `ℓ ≤ m[−a,0]` (continuity from above of `m` on a finite interval);
* `g3Bad_imp_ge`: the elementary geometry `r₁ ≤ |x − t₁| + m'` with `x ≥ −δ` and `m' < η/4`
  forces `x ≥ −(3η/4 + m')` — leaving the half-disc means reaching the level `−(3η/4+m')`;
* `g3Bad_subset_mass`: the Palm "bad" event is contained in that mass condition.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-! ## The level set of `lenLeft` -/

/-- The level set whose infimum is `lenLeft`: the points `y > 0` with `ℓ ≤ m[−y, 0]`. -/
def lenLevel (m : Measure ℝ) (ℓ : ℝ) : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc (-y) 0)}

theorem lenLeft_eq_neg_sInf (m : Measure ℝ) (ℓ : ℝ) :
    lenLeft m ℓ = -sInf (lenLevel m ℓ) := rfl

theorem exists_lt_of_sInf_lt {s : Set ℝ} {b : ℝ} (hne : s.Nonempty) (h : sInf s < b) :
    ∃ y ∈ s, y < b := by
  by_contra hc
  push_neg at hc
  exact absurd (le_csInf hne hc) (not_le.2 h)

/-- **The Palm point lies in `[−δ, 0]`**: `ℓ ≤ m[−δ, 0]` puts `δ` in the level set. -/
theorem le_lenLeft_of_mass_le {m : Measure ℝ} {ℓ δ : ℝ} (hδ : 0 < δ)
    (h : ENNReal.ofReal ℓ ≤ m (Icc (-δ) 0)) : -δ ≤ lenLeft m ℓ := by
  have hmem : δ ∈ lenLevel m ℓ := ⟨hδ, h⟩
  have hs : sInf (lenLevel m ℓ) ≤ δ := csInf_le ⟨0, fun y hy => hy.1.le⟩ hmem
  rw [lenLeft_eq_neg_sInf]; linarith

theorem lenLevel_nonempty {m : Measure ℝ} {ℓ δ : ℝ} (hδ : 0 < δ)
    (h : ENNReal.ofReal ℓ ≤ m (Icc (-δ) 0)) : (lenLevel m ℓ).Nonempty := ⟨δ, hδ, h⟩

/-- **Deterministic tail estimate.** If the length `ℓ` is at most the mass of `[−δ, 0]` and the
Palm point has reached the level `−a`, then `ℓ` is at most the mass of `[−a, 0]`: the reverse
implication would put an element of the level set below `r` for every `r > a`, hence a mass above
`m[−r,0]`, and `r ↓ a` with continuity from above (finiteness of `m` on `[−a−1, 0]`). -/
theorem ofReal_le_mass_Icc_of_lenLeft {m : Measure ℝ} {ℓ a δ : ℝ} (hδ : 0 < δ)
    (hℓ : ENNReal.ofReal ℓ ≤ m (Icc (-δ) 0)) (hfin : m (Icc (-(a + 1)) 0) ≠ ⊤)
    (hx : -a ≤ lenLeft m ℓ) : ENNReal.ofReal ℓ ≤ m (Icc (-a) 0) := by
  rw [lenLeft_eq_neg_sInf] at hx
  have ha_le : sInf (lenLevel m ℓ) ≤ a := by linarith
  have htend := tendsto_measure_biInter_gt (μ := m) (a := a) (s := fun r : ℝ => Icc (-r) 0)
    (fun r _ => measurableSet_Icc.nullMeasurableSet)
    (fun r r' hr hrr => Icc_subset_Icc_left (by linarith))
    ⟨a + 1, by linarith, hfin⟩
  have hge : ENNReal.ofReal ℓ ≤ m (⋂ r > a, Icc (-r) (0 : ℝ)) := by
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_sInf_lt (lenLevel_nonempty hδ hℓ)
      (lt_of_le_of_lt ha_le hr)
    exact hy.2.trans (measure_mono (Icc_subset_Icc_left (by linarith [hylt.le])))
  refine hge.trans (measure_mono fun z hz => ?_)
  have hmem' : z ∈ Icc (-(a + 1)) (0 : ℝ) :=
    (mem_iInter.1 (mem_iInter.1 hz (a + 1))) (by linarith)
  refine ⟨?_, hmem'.2⟩
  refine le_of_forall_pos_le_add fun e he => ?_
  have hlow : -(a + e) ≤ z :=
    ((mem_iInter.1 (mem_iInter.1 hz (a + e))) (by linarith)).1
  linarith

/-! ## The geometry of the bad event -/

/-- **Leaving the half-disc means reaching a level.** If `x = g3X` is in `[−δ, 0]` and
`r₁ ≤ |x − t₁| + m'` with `m' < η/4`, then `x ≥ −(3η/4 + m')`: in the branch `x ≥ t₁` the
inequality is exactly this level, and in the branch `x < t₁` it would force `x < −δ`. -/
theorem g3Bad_imp_ge (i : G3Idx) {m' : ℝ} (hmη : m' < i.η / 4) {x : ℝ}
    (hbad : i.r₁ ≤ |x - i.t₁| + m') (hx : -(i.δ) ≤ x) : -(3 * i.η / 4 + m') ≤ x := by
  by_cases h : i.t₁ ≤ x
  · have habs : |x - i.t₁| = x - i.t₁ := abs_of_nonneg (sub_nonneg.2 h)
    rw [habs] at hbad
    have he : i.r₁ + i.t₁ - m' = -(3 * i.η / 4 + m') := by
      unfold G3Idx.r₁ G3Idx.t₁; ring
    have h1 : i.r₁ + i.t₁ - m' ≤ x := by linarith
    rw [he] at h1
    exact h1
  · push_neg at h
    have habs : |x - i.t₁| = -(x - i.t₁) := abs_of_nonpos (sub_nonpos.2 h.le)
    rw [habs] at hbad
    have he : i.t₁ - i.r₁ = -i.δ - i.η / 4 := by unfold G3Idx.t₁ G3Idx.r₁; ring
    have h1 : x ≤ i.t₁ - i.r₁ + m' := by linarith
    rw [he] at h1
    linarith

/-- **The bad event is a mass condition.** On the support of the Palm weight (`ℓ ≤ ν[−δ,0]`),
the event that the Palm point `x` has left the half-disc of region 1 by a margin `m' < η/4` is
contained in the event `ℓ ≤ (ν₁+ν₀)[−(3η/4+m'), 0]`. -/
theorem g3Bad_subset_mass (γ : ℝ) (i : G3Idx) {m' : ℝ} (hmη : m' < i.η / 4) :
    {p : Ω₀ × ℝ | i.r₁ ≤ |g3X γ i p - i.t₁| + m'} ∩
        {p : Ω₀ × ℝ | ENNReal.ofReal p.2 ≤ g3Mass γ i p.1} ⊆
      {p : Ω₀ × ℝ | ENNReal.ofReal p.2 ≤
        (g3ν₁ γ i p.1 + g3ν₀ γ i p.1) (Icc (-(3 * i.η / 4 + m')) 0)} := by
  intro p hp
  obtain ⟨hbad, hℓM⟩ := hp
  have hδ : 0 < i.δ := i.hη.trans i.hηδ
  have hℓ : ENNReal.ofReal p.2 ≤ (g3ν₁ γ i p.1 + g3ν₀ γ i p.1) (Icc (-i.δ) 0) := hℓM
  have hx : -(i.δ) ≤ g3X γ i p := le_lenLeft_of_mass_le hδ hℓ
  have hfin : (g3ν₁ γ i p.1 + g3ν₀ γ i p.1) (Icc (-((3 * i.η / 4 + m') + 1)) 0) ≠ ⊤ := by
    have h1 := bdryM_le_qBoundaryMeasure γ (regionField γ i.t₁ i.r₁ X₀ p.1)
      (Icc (-((3 * i.η / 4 + m') + 1)) 0)
    have h2 := bdryM_le_qBoundaryMeasure γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ X₀ p.1)
      (Icc (-((3 * i.η / 4 + m') + 1)) 0)
    have hsum : (g3ν₁ γ i p.1 + g3ν₀ γ i p.1) (Icc (-((3 * i.η / 4 + m') + 1)) 0) ≤
        qBoundaryMeasure γ (regionField γ i.t₁ i.r₁ X₀ p.1) (Icc (-((3 * i.η / 4 + m') + 1)) 0) +
        qBoundaryMeasure γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ X₀ p.1)
          (Icc (-((3 * i.η / 4 + m') + 1)) 0) := by
      rw [show g3ν₁ γ i p.1 + g3ν₀ γ i p.1 =
          bdryM γ (regionField γ i.t₁ i.r₁ X₀ p.1) +
            bdryM γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ X₀ p.1) from rfl, Measure.add_apply]
      exact add_le_add h1 h2
    have hlt : (g3ν₁ γ i p.1 + g3ν₀ γ i p.1) (Icc (-((3 * i.η / 4 + m') + 1)) 0) < ⊤ :=
      lt_of_le_of_lt hsum (ENNReal.add_lt_top.2
        ⟨qBoundaryMeasure_Icc_lt_top γ
            (regionField γ i.t₁ i.r₁ X₀ p.1) (-((3 * i.η / 4 + m') + 1)) 0,
          qBoundaryMeasure_Icc_lt_top γ
            (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ X₀ p.1) (-((3 * i.η / 4 + m') + 1)) 0⟩)
    exact hlt.ne
  exact ofReal_le_mass_Icc_of_lenLeft hδ hℓ hfin (g3Bad_imp_ge i hmη hbad hx)

end Thm18Asm
end QuantumZipper
