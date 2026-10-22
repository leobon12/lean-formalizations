import HigherDimLQGMetric.Sharp.TightLower
import HigherDimLQGMetric.Sharp.TightUpper
import HigherDimLQGMetric.Sharp.TightSphereDet

/-!
# Tight shell functionals of a family of length metrics

The generic part of MA6 P2. It uses only `TightOver` and almost-sure length,
before normalizer and Gaussian field transfer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {G : ℝ → Ω → ContMetric d} {S : Set ℝ}

theorem unit_sphere_subset_ann :
    sphere (0 : Rd d) 1 ⊆ ann 0 (1 / 2) 2 := by
  intro u hu
  have hnorm : ‖u - (0 : Rd d)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hu
  show 1 / 2 < ‖u - (0 : Rd d)‖ ∧ ‖u - (0 : Rd d)‖ < 2
  rw [hnorm]
  norm_num

theorem compact_frontier_unit_ann :
    IsCompact (frontier (ann (0 : Rd d) (1 / 2) 2)) := by
  let V : Set (Rd d) := ann 0 (1 / 2) 2
  have hsub : frontier V ⊆ closedBall (0 : Rd d) 2 := by
    intro v hv
    have hcl : v ∈ annCl (0 : Rd d) (1 / 2) 2 :=
      closure_minimal (ann_subset_annCl _ _ _) (isClosed_annCl _ _ _)
        (frontier_subset_closure hv)
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hcl.2
  exact (isCompact_closedBall _ _).of_isClosed_subset isClosed_frontier hsub

theorem sphere_frontier_offDiag (p : Rd d × Rd d)
    (hp : p ∈ sphere (0 : Rd d) 1 ×ˢ frontier (ann (0 : Rd d) (1 / 2) 2)) :
    p.1 ≠ p.2 := by
  intro heq
  have hmem : p.1 ∈ ann (0 : Rd d) (1 / 2) 2 ∩
      frontier (ann (0 : Rd d) (1 / 2) 2) :=
    ⟨unit_sphere_subset_ann hp.1, heq ▸ hp.2⟩
  rw [(isOpen_ann (0 : Rd d) (1 / 2) 2).inter_frontier_eq] at hmem
  exact hmem

/-- The across distance between the half- and unit-spheres stays uniformly positive. -/
theorem TightOver.across_lower
    (hT : TightOver P (fun r ω => (G r ω).1) S)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ S,
      P {ω | acrossDist (G r ω) 0 (1 / 2) 1 < ENNReal.ofReal a} < ε := by
  have hOff : ∀ p : Rd d × Rd d,
      p ∈ sphere (0 : Rd d) (1 / 2) ×ˢ sphere (0 : Rd d) 1 → p.1 ≠ p.2 := by
    intro p hp heq
    have h1 : dist p.1 (0 : Rd d) = 1 / 2 := by
      simpa only [Metric.mem_sphere] using hp.1
    have h2 : dist p.2 (0 : Rd d) = 1 := by
      simpa only [Metric.mem_sphere] using hp.2
    rw [heq] at h1
    linarith
  obtain ⟨a, ha, H⟩ := hT.lower_offDiag
    ((isCompact_sphere (0 : Rd d) (1 / 2)).prod (isCompact_sphere 0 1)) hOff hε
  refine ⟨a, ha, fun r hr => ?_⟩
  refine lt_of_le_of_lt (measure_mono ?_) (H r hr)
  intro ω hbad hgood
  have hle : ENNReal.ofReal a ≤ acrossDist (G r ω) 0 (1 / 2) 1 := by
    unfold acrossDist
    refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
    exact ENNReal.ofReal_le_ofReal (hgood (u, v) ⟨hu, hv⟩).le
  exact (not_lt_of_ge hle) hbad

/-- Internal diameter of the unit sphere is bounded in probability for a tight family of
continuous length metrics. -/
theorem TightOver.sphereDiam_upper (hd : 2 ≤ d)
    (hT : TightOver P (fun r ω => (G r ω).1) S)
    (hLen : ∀ r ∈ S, ∀ᵐ ω ∂P, (G r ω).IsLength)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ S,
      P {ω | ENNReal.ofReal C < sphereDiam (G r ω) 0 1} < ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  let K : Set (Rd d) := sphere 0 1
  let V : Set (Rd d) := ann 0 (1 / 2) 2
  obtain ⟨a, ha, Hsep⟩ := hT.lower_offDiag
    ((isCompact_sphere (0 : Rd d) 1).prod compact_frontier_unit_ann)
    sphere_frontier_offDiag hε2
  obtain ⟨b, hb, Hmod⟩ := hT.modulus (isCompact_sphere (0 : Rd d) 1) ha hε2
  obtain ⟨N, hN⟩ := compact_connected_chain_bound
    (isCompact_sphere (0 : Rd d) 1) (isConnected_unit_sphere hd) hb
  let C : ℝ := (N + 1) * a
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r hr
  have hgood (ω : Ω) (hl : (G r ω).IsLength)
      (hs : ∀ p ∈ K ×ˢ frontier V, a < (G r ω).1 p)
      (hm : ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → (G r ω).1 (u, v) < a) :
      sphereDiam (G r ω) 0 1 ≤ ENNReal.ofReal C := by
    have hsep' : ∀ u ∈ K, ∀ v ∈ frontier V, a < (G r ω).1 (u, v) :=
      fun u hu v hv => hs (u, v) ⟨hu, hv⟩
    have hdiam := sphereDiam_le_of_modulus N hN (G r ω) hl ha hsep' hm
    have hle : (N : ℝ≥0∞) * ENNReal.ofReal a ≤ ENNReal.ofReal C := by
      have hNa : (N : ℝ) * a ≤ C := by dsimp [C]; nlinarith
      calc
        (N : ℝ≥0∞) * ENNReal.ofReal a = ENNReal.ofReal ((N : ℝ) * a) := by
          rw [ENNReal.ofReal_mul (p := (N : ℝ)) (by positivity), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hNa
    exact hdiam.trans hle
  have hbad : P {ω | ENNReal.ofReal C < sphereDiam (G r ω) 0 1} ≤
      P ({ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < (G r ω).1 p} ∪
        {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → (G r ω).1 (u, v) < a}) := by
    refine measure_mono_ae ?_
    filter_upwards [hLen r hr] with ω hl hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
    exact (not_lt_of_ge (hgood ω hl hnot.1 hnot.2)) hω
  calc
    P {ω | ENNReal.ofReal C < sphereDiam (G r ω) 0 1} ≤ P _ := hbad
    _ ≤ P {ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < (G r ω).1 p} +
        P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → (G r ω).1 (u, v) < a} :=
      measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (Hsep r hr) (Hmod r hr)
    _ = ε := ENNReal.add_halves ε

end HigherDimLQGMetric
