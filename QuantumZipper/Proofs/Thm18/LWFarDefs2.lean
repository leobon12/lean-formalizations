import QuantumZipper.Proofs.Thm18.LWFarBdryHit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LW-FAR, node LWF-6 restated: covering form of the deep-pocket image

Task LW-FAR (plan `handoff/LW-FAR.md`, §4). `LWFarDefs.DeepPocketImageStmt` (all deep points of
a pocket map near the single real point `Re Z_t(z)`) is false: a pocket can have several deep
lobes that `Z_t` sends near different real points (LWF-6 prover). It is replaced by the covering
form `DeepPocketCoverStmt'`: the deep part of the pocket is mapped by `Z_t` into countably many
disks `B(cᵢ, rᵢ)` with real centres, `2 rᵢ ≤ |cᵢ|` and `Σ rᵢ/|cᵢ| ≤ C (ρ/R)^{1/2}`. This is the
content of Lawler–Werness, *Multi-point Green's functions for SLE and an estimate of Beffara*,
Ann. Probab. 41 (2013), Lemmas 4.3–4.5 (pp. 23–25): the excursion measure between the neck and
the deep arcs is `≤ C (ρ/R)^{1/2}` (Lemma 4.4, Beurling), it is additive over the deep arcs, and a
crosscut with small excursion measure lies in a disk of relative radius `≲` that measure
(Lemma 4.3 and the proof of Lemma 4.5); one disk per deep arc.

The downstream nodes `FjordDeepStmt`, `FjordStmt`, `PocketProdStmt` and the assembly LWF-9 are
unchanged (they never mention the image). The step "cover ⇒ `FjordDeepStmt`" is the union bound
`prob_hit_cover_le` below (proved here from `bdryHitStmt_holds`, LW Prop 2.6) applied to the
restarted curve (strong Markov at `σ`, as in LWF-1/LWF-3), using `(8/κ − 1) ≥ 1`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- `Σ xᵢ^α ≤ (Σ xᵢ)^α` for `xᵢ ≥ 0` summable and `α ≥ 1` (termwise `xᵢ^α ≤ xᵢ S^{α−1}`). -/
theorem tsum_rpow_le_rpow_tsum {x : ℕ → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hxs : Summable x) {α : ℝ}
    (hα : 1 ≤ α) :
    Summable (fun i => x i ^ α) ∧ ∑' i, x i ^ α ≤ (∑' i, x i) ^ α := by
  set S := ∑' i, x i with hS
  have hxS : ∀ i, x i ≤ S := fun i => hxs.le_tsum i (fun j _ => hx0 j)
  have hS0 : 0 ≤ S := tsum_nonneg hx0
  have hterm : ∀ i, x i ^ α ≤ x i * S ^ (α - 1) := by
    intro i
    calc x i ^ α = x i * x i ^ (α - 1) := by
          rcases eq_or_lt_of_le (hx0 i) with h | h
          · rw [← h, Real.zero_rpow (by linarith), zero_mul]
          · rw [← Real.rpow_one_add' h.le (by linarith)]; congr 1; ring
      _ ≤ x i * S ^ (α - 1) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hx0 i) (hxS i) (by linarith)) (hx0 i)
  have hsum : Summable (fun i => x i ^ α) :=
    Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (hx0 i) _) hterm
      (hxs.mul_right _)
  refine ⟨hsum, ?_⟩
  calc ∑' i, x i ^ α ≤ ∑' i, x i * S ^ (α - 1) := hsum.tsum_le_tsum hterm (hxs.mul_right _)
    _ = S * S ^ (α - 1) := by rw [tsum_mul_right]
    _ = S ^ α := by
        rcases eq_or_lt_of_le hS0 with h | h
        · rw [← h, zero_mul, Real.zero_rpow (by linarith)]
        · rw [← Real.rpow_one_add' h.le (by linarith)]; congr 1; ring

/-- **Hitting a covering by boundary disks** (union bound over LW Prop 2.6,
`bdryHitStmt_holds`): the SLE_κ trace (`0 < κ < 4`) hits `⋃ B(cᵢ, rᵢ)`, `cᵢ` real,
`2 rᵢ ≤ |cᵢ|`, with probability `≤ C (Σ rᵢ/|cᵢ|)^{8/κ−1}`. This is the step
"`DeepPocketCoverStmt'` ⇒ `FjordDeepStmt`" for the restarted curve. -/
theorem prob_hit_cover_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ c r : ℕ → ℝ,
      (∀ i, 0 < r i ∧ 2 * r i ≤ |c i|) → Summable (fun i => r i / |c i|) →
      P {ω | ∃ t : ℝ, 0 ≤ t ∧ ∃ i, ‖sleTrace κ B ω t - c i‖ < r i} ≤
        ENNReal.ofReal (C * (∑' i, r i / |c i|) ^ (8 / κ - 1)) := by
  obtain ⟨C, hC0, hC⟩ := bdryHitStmt_holds hκ hκ4
  refine ⟨C, hC0, ?_⟩
  intro Ω _ P _ B hB c r hcr hsum
  have hα : 1 ≤ 8 / κ - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hκ]; linarith
  have hx0 : ∀ i, 0 ≤ r i / |c i| := fun i => div_nonneg (hcr i).1.le (abs_nonneg _)
  obtain ⟨hps, hple⟩ := tsum_rpow_le_rpow_tsum hx0 hsum hα
  have hsub : {ω | ∃ t : ℝ, 0 ≤ t ∧ ∃ i, ‖sleTrace κ B ω t - c i‖ < r i} ⊆
      ⋃ i, {ω | ∃ t : ℝ, 0 ≤ t ∧ ‖sleTrace κ B ω t - (c i : ℂ)‖ < r i} := by
    rintro ω ⟨t, ht, i, hi⟩
    exact mem_iUnion.2 ⟨i, t, ht, hi⟩
  calc P {ω | ∃ t : ℝ, 0 ≤ t ∧ ∃ i, ‖sleTrace κ B ω t - c i‖ < r i}
      ≤ ∑' i, P {ω | ∃ t : ℝ, 0 ≤ t ∧ ‖sleTrace κ B ω t - (c i : ℂ)‖ < r i} :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' i, ENNReal.ofReal (C * (r i / |c i|) ^ (8 / κ - 1)) :=
        ENNReal.tsum_le_tsum fun i => hC P B hB (c i) (r i) (hcr i).1 (hcr i).2
    _ = ENNReal.ofReal (∑' i, C * (r i / |c i|) ^ (8 / κ - 1)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg hC0 (Real.rpow_nonneg (hx0 i) _))
          (hps.mul_left C)).symm
    _ ≤ ENNReal.ofReal (C * (∑' i, r i / |c i|) ^ (8 / κ - 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hple hC0

end LWFar
end Thm18Asm
end QuantumZipper
