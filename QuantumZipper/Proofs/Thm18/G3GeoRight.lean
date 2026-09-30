import QuantumZipper.Proofs.Thm18.G3GeoPalm

/-!
# G3-GEO, part 3: a general Palm bound, and the geometry of the length partner `R(x)`

Concrete G3 scheme (`G3Concrete.lean`): under the Palm law, `ℓ` is uniform on `(0, M)` with
`M = (ν₁+ν₀)[−δ,0]` (weight `Z⁻¹ e^ℓ 1{0 < ℓ ≤ M}` against `P₀ ⊗ Exp 1`), and the length partner
is `R = lenRight (ν₀+ν₂) ℓ`.

* `g3PalmLaw_le_of_len`: **general Palm bound.** If every point `(ω, ℓ)` of a measurable set `S`
  with `0 < ℓ ≤ M(ω)` has `ℓ ≤ c(ω)`, then `P_Palm(S) ≤ Z⁻¹ E[min(c, M)]`.
* `g3BadR_subset`: **geometry of `R`.** Leaving the region-2 half-disc by a margin `m' < η/4`
  forces `ℓ ≤ (ν₀+ν₂)[0, η]` (too close to the gap) or `(ν₀+ν₂)[0, 1/2] < ℓ` (beyond the right
  end of region 2, `1/2 + η/4`).

Own elementary arguments (AGENT_GUIDE cost rule). The corresponding step of Sheffield,
arXiv:1012.4797, proof of Theorem 1.8 (§5.4, p. 71) is the sentence "we may choose δ small enough
so that with high probability `R(x) ∈ B₁(0)`".
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- **General Palm bound.** For `0 < g3Z < ⊤`, a measurable set `S` and a measurable cutoff `c`
such that every `(ω, ℓ) ∈ S` in the support of the Palm weight has `ℓ ≤ c(ω)`,
`P_Palm(S) ≤ Z⁻¹ · E[min(c, M)]`, `M = (ν₁+ν₀)[−δ,0]`. -/
theorem g3PalmLaw_le_of_len (γ : ℝ) (i : G3Idx) (hZ : 0 < g3Z γ i ∧ g3Z γ i < ⊤)
    {S : Set (Ω₀ × ℝ)} (hS : MeasurableSet S) {c : Ω₀ → ℝ≥0∞} (hc : Measurable c)
    (hSc : ∀ p ∈ S, 0 < p.2 → ENNReal.ofReal p.2 ≤ g3Mass γ i p.1 →
      ENNReal.ofReal p.2 ≤ c p.1) :
    g3PalmLaw γ i S ≤ (g3Z γ i)⁻¹ * ∫⁻ ω, min (c ω) (g3Mass γ i ω) ∂gffBase.P := by
  haveI : IsProbabilityMeasure gffBase.P := gffBase.prob
  set F : Ω₀ × ℝ → ℝ≥0∞ := fun p => if 0 < p.2 ∧ ENNReal.ofReal p.2 ≤ min (c p.1)
    (g3Mass γ i p.1) then ENNReal.ofReal (Real.exp p.2) else 0 with hFdef
  have hFm : Measurable F := by
    refine Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd)
        ((hc.comp measurable_fst).min ((measurable_g3Mass γ i).comp measurable_fst))))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_snd)) measurable_const
  have hpt : ∀ p ∈ S, (g3W γ i p : ℝ≥0∞) ≤ (g3Z γ i)⁻¹ * F p := by
    intro p hp
    have hcoe : ((g3W γ i p : ℝ≥0) : ℝ≥0∞) = (g3Z γ i)⁻¹ * g3W0 γ i p := by
      unfold g3W; rw [if_pos hZ]
      exact ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ.1.ne')
        (g3W0_ne_top γ i p))
    rw [hcoe]
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    unfold g3W0
    split_ifs with h1
    · rw [hFdef]; dsimp only
      rw [if_pos ⟨h1.1, le_min (hSc p hp h1.1 h1.2) h1.2⟩]
    · exact bot_le
  have hinner : ∀ ω, ∫⁻ ℓ, F (ω, ℓ) ∂L₀ = min (c ω) (g3Mass γ i ω) := fun ω => by
    rw [hFdef]
    exact lintegral_expMeasure_palmKernel (min (c ω) (g3Mass γ i ω))
  calc g3PalmLaw γ i S
      = ∫⁻ p in S, (g3W γ i p : ℝ≥0∞) ∂(gffBase.P.prod L₀) := by
        rw [g3PalmLaw, withDensity_apply _ hS]
    _ ≤ ∫⁻ p in S, (g3Z γ i)⁻¹ * F p ∂(gffBase.P.prod L₀) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hS] with p hp
        exact hpt p hp
    _ ≤ ∫⁻ p, (g3Z γ i)⁻¹ * F p ∂(gffBase.P.prod L₀) := by
        simpa only [Measure.restrict_univ] using lintegral_mono_set (Set.subset_univ S)
    _ = (g3Z γ i)⁻¹ * ∫⁻ p, F p ∂(gffBase.P.prod L₀) := lintegral_const_mul _ hFm
    _ = (g3Z γ i)⁻¹ * ∫⁻ ω, min (c ω) (g3Mass γ i ω) ∂gffBase.P := by
        rw [lintegral_prod _ hFm.aemeasurable]
        simp only [hinner]

/-- **Geometry of the length partner.** If `R = lenRight (ν₀+ν₂) ℓ` leaves the region-2 half-disc
by a margin `m' < η/4`, then `ℓ ≤ (ν₀+ν₂)[0, η]` or `(ν₀+ν₂)[0, 1/2] < ℓ`. -/
theorem g3BadR_subset (γ : ℝ) (i : G3Idx) {m' : ℝ} (hmη : m' < i.η / 4) :
    {p : Ω₀ × ℝ | i.r₂ ≤ |g3R γ i p - i.t₂| + m'} ⊆
      {p : Ω₀ × ℝ | ENNReal.ofReal p.2 ≤ (g3ν₀ γ i p.1 + g3ν₂ γ i p.1) (Icc 0 i.η)} ∪
      {p : Ω₀ × ℝ | (g3ν₀ γ i p.1 + g3ν₂ γ i p.1) (Icc 0 (1 / 2)) < ENNReal.ofReal p.2} := by
  intro p hp
  set m := g3ν₀ γ i p.1 + g3ν₂ γ i p.1 with hm
  by_cases h : ENNReal.ofReal p.2 ≤ m (Icc 0 (1 / 2))
  · left
    set L : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal p.2 ≤ m (Icc 0 y)} with hL
    have hR : g3R γ i p = sInf L := rfl
    have hne : L.Nonempty := ⟨1 / 2, by norm_num, h⟩
    have hbdd : BddBelow L := ⟨0, fun y hy => hy.1.le⟩
    have hR12 : g3R γ i p ≤ 1 / 2 := hR ▸ csInf_le hbdd ⟨by norm_num, h⟩
    have hbad : i.r₂ ≤ |g3R γ i p - i.t₂| + m' := hp
    have ht : i.t₂ + i.r₂ = 1 / 2 + i.η / 4 := by unfold G3Idx.t₂ G3Idx.r₂; ring
    have ht' : i.t₂ - i.r₂ = 3 * i.η / 4 := by unfold G3Idx.t₂ G3Idx.r₂; ring
    have hRlt : g3R γ i p < i.η := by
      rcases le_or_gt i.t₂ (g3R γ i p) with h2 | h2
      · rw [abs_of_nonneg (sub_nonneg.2 h2)] at hbad; linarith
      · rw [abs_of_neg (sub_neg.2 h2)] at hbad; linarith
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_sInf_lt hne (hR ▸ hRlt)
    exact hy.2.trans (measure_mono (Icc_subset_Icc_right hylt.le))
  · right
    exact not_le.1 h

end Thm18Asm
end QuantumZipper
