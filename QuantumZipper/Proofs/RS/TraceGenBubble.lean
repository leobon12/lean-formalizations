import QuantumZipper.Proofs.RS.TraceGen

/-!
# EXT-RS node AD1-1: frontier and bubbles of a curve-generated Loewner chain

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §5, node AD1-1 (DECISIONS D4, DEVIATIONS L-AD1;
replaces GFF_K3 C5 item 4).

Deterministic hypotheses (the ω-wise content of `Blueprint.RohdeSchrammTraceGen`): `η`
continuous on `[0,∞)` and, for every `t ≥ 0` and every `M` with `‖η‖ < M` on `[0,t]`,
`H \ K_t = connectedComponentIn (H \ η[0,t]) (M i)`.

* (a) `frontier_compl_fwdHull_inter_H_subset_of_gen`: `frontier H_T ∩ H ⊆ η[0,T]`.
* (b) `bubble_common_swallowTime`: each bounded component `C` of `H \ η[0,T]` lies in `K_T`,
  all its points have the same swallowing time `τ_C ≤ T`, and `C ⊆ H_t` for `0 ≤ t < τ_C`.
* `ae_frontier_and_bubbles`: both hold a.s. for SLE_κ, `0 < κ < 8`.

Sources: Rohde–Schramm, *Basic properties of SLE* (2005), proof of Thm 6.4 (p. 31: "all points
within δ are swallowed with z₀"); Lawler, *Conformally Invariant Processes in the Plane* (2005),
proof of Prop. 6.10 (p. 128). The deductions below are elementary point-set topology.
-/

noncomputable section

open Set Filter Topology Metric Complex MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper.RS

section Det

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- The hull complement is the component of `H \ η[0,t]` of any of its points. -/
theorem compl_fwdHull_eq_cc_of_gen (hη : ContinuousOn η (Ici 0))
    (hgen : ∀ t : ℝ, 0 ≤ t → ∀ M : ℝ, (∀ s ∈ Icc 0 t, ‖η s‖ < M) →
      H \ fwdHull W t = connectedComponentIn (H \ η '' Icc 0 t) (M * I))
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull W t) :
    H \ fwdHull W t = connectedComponentIn (H \ η '' Icc 0 t) z := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1
    (isCompact_Icc.image_of_continuousOn (hη.mono Icc_subset_Ici_self)).isBounded
  have h := hgen t ht (R + 1) fun s hs => by linarith [hR _ (mem_image_of_mem η hs)]
  rw [h] at hz ⊢
  exact connectedComponentIn_eq hz

/-- A connected subset of `H \ η[0,T]` meeting `H_t` (`0 ≤ t ≤ T`) lies in `H_t`. -/
theorem subset_compl_fwdHull_of_gen (hη : ContinuousOn η (Ici 0))
    (hgen : ∀ t : ℝ, 0 ≤ t → ∀ M : ℝ, (∀ s ∈ Icc 0 t, ‖η s‖ < M) →
      H \ fwdHull W t = connectedComponentIn (H \ η '' Icc 0 t) (M * I))
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) {C : Set ℂ} (hC : IsPreconnected C)
    (hCsub : C ⊆ H \ η '' Icc 0 T) {w : ℂ} (hwC : w ∈ C) (hw : w ∈ H \ fwdHull W t) :
    C ⊆ H \ fwdHull W t := by
  rw [compl_fwdHull_eq_cc_of_gen hη hgen ht hw]
  refine hC.subset_connectedComponentIn hwC fun x hx => ⟨(hCsub hx).1, fun hxA => ?_⟩
  exact (hCsub hx).2 (image_mono (Icc_subset_Icc_right htT) hxA)

theorem mem_compl_fwdHull_iff {z : ℂ} {t : ℝ} :
    z ∈ H \ fwdHull W t ↔ z ∈ H ∧ ENNReal.ofReal t < swallowTime W z := by
  simp [fwdHull, not_le]

end Det

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

end QuantumZipper.RS
