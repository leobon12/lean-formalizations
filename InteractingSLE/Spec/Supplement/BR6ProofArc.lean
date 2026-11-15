/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR6Proof
import InteractingSLE.Spec.Supplement.GW2ConeArc

/-!
# GW2's forced arcs from the proved BR6 sufficiency

Packet PROVE-T14-BR4. `GW2Cone.gw2ForcedArcStatement_of_br6` (PROVE-T14-CONE) derives Lemma GW2's forced initial arcs
(p. 621: "For a boundary root `v`, BR6 forces the whole initial arc `[x, v]`") from the named statement
`BR6.BR6Statement`, of which it uses only the sufficiency direction, applied to the reflected counterflow word. That
word has its seed marks at `0` on both sides, so `BR6Proof.ae_visit_of_conditions` applies. Here the same argument
(copied, with the BR6 call replaced) gives `GW2ForcedArcStatement` from Theorem 1.3 alone (Lemma GW0's forward
implication is `BR3Ref.gw0ForwardStatement_of_theorem13`).

## Main results

* `GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13`;
* **`GW2Cone.gw2ForcedArcStatement_of_theorem13`**;
* `GW2Cone.gw2LightConeStatement_of_containments`: Lemma GW2 from Theorem 1.3, the two schedule containments and the
  exhaustion at interior tips (no BR6 or GW0 input left).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Cone

open Sec7.StripSysField

/-- **A point of the first low right arc is a physical point of the counterflow** (BR6 sufficiency, proved, applied to
the reflected counterflow word at `1/v'`): for `v ∈ lowerArcRoots κ b jumps` and `0 < v' ≤ v`, almost surely `v'` lies
in the completed counterflow range. -/
theorem ae_mem_counterflowCompletedRange_of_theorem13 (hT13 : Exist.Theorem13Statement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {v : ℝ} (hv : v ∈ lowerArcRoots κ b jumps) {v' : ℝ} (hv0 : 0 < v')
    (hvv : v' ≤ v) :
    ∀ᵐ ω ∂P, (v' : ℂ) ∈ counterflowCompletedRange (fun t => W' t ω) := by
  obtain ⟨h', -, hfl⟩ := isFlowLineDriver_counterflowData hκ hb hh hcf
  have hk : 0 < 16 / κ := by positivity
  have hk4 : 4 < 16 / κ := by
    rw [lt_div_iff₀ hκ]
    linarith
  obtain ⟨hadmL, hadmR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hfl hζ'
  have hγ := GW2aSingle.ae_chosenTrace hT13 hk hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hE := hC.1.reflect
  have hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W') t ω) (ζ' ω)
      (fun t => LP.reflectC (GW2aSingle.chosenTrace W' ζ' ω t)) := by
    filter_upwards [hγ] with ω hω
    exact LP.isGeneratingTrace_reflect hω.1
  have hword := Supp7.G12.isOrderedForceWord_reflect
    (Theorem15.isOrderedForceWord_flowLine (counterflowData κ b) (counterflowJumps jumps) 0)
  -- the reflected word has a left mark (the counterflow's right seed) and a right mark at `0 < 1/v'`
  have hseed : (-flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0) ⟨0, Nat.succ_pos _⟩ < v'⁻¹ := by
    change -(0 : ℝ) < v'⁻¹
    rw [neg_zero]
    exact inv_pos.2 hv0
  have hvis := BR6Proof.ae_visit_of_conditions hT13 hk4 (inv_pos.2 hv0) hword (Nat.succ_pos _) ⟨_, hseed⟩ hE hη
    (fun j _ => hadmR j) (fun m _ _ => hadmL m) (rightLowBeyond_counterflow hκ hb hv hv0 hvv)
  filter_upwards [hvis, hγ, hζ', hdrv] with ω hω hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  obtain ⟨t, -, ht⟩ := hω
  have hγt := eq_neg_of_reflectC_eq ht
  have hne : GW2aSingle.chosenTrace W' ζ' ω t ≠ 0 := by
    rw [hγt, neg_ne_zero, Complex.ofReal_ne_zero]
    exact (inv_pos.2 hv0).ne'
  unfold counterflowCompletedRange
  rw [CounterflowRange.tipSet_infinitySourceChart_top hγω.1 hWc hdω.1]
  refine Or.inl ⟨t, hne, ?_⟩
  rw [hγt, Complex.ofReal_inv, inv_neg, inv_inv, neg_neg]

/-- **GW2's forced arcs** (`GW2ForcedArcStatement`, p. 621: "For a boundary root `v`, BR6 forces the whole initial arc
`[x, v]`") from Theorem 1.3 (at the universe of the probability space and at universe `0`, the latter for Lemma GW0's
forward implication, `BR3Ref.gw0ForwardStatement_of_theorem13`). The argument of
`gw2ForcedArcStatement_of_br6`: every rational point of `(0, v]` is visited, and the completed range is closed. -/
theorem gw2ForcedArcStatement_of_theorem13 (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) : GW2ForcedArcStatement.{u} := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' v hv
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ v →
      (((q : ℝ) : ℂ)) ∈ counterflowCompletedRange (fun t => W' t ω) := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ v
    · filter_upwards [ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4 hb hh hcf hζ' hv hq.1 hq.2]
        with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hq
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hk : 0 < 16 / κ := by positivity
  have hγ := GW2aSingle.ae_chosenTrace hT13 hk hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  filter_upwards [hrat, hγ, hζ', hdrv] with ω hq hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  have hclosed := CounterflowRange.isClosed_counterflowCompletedRange hγω.1 hWc hdω.1 (hγω.2 rfl)
  rintro _ ⟨w, ⟨hw0, hwv⟩, rfl⟩
  rcases hw0.eq_or_lt with rfl | hw0
  · rw [Complex.ofReal_zero]
    exact Or.inr rfl
  rw [← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (w - ε) (w / 2) < w by
    exact max_lt (by linarith) (by linarith))
  have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_right _ _) hq1)
  refine ⟨((q : ℝ) : ℂ), hq q hq0 (hq2.le.trans hwv), ?_⟩
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith [le_max_left (w - ε) (w / 2)]

/-- **Lemma GW2 without the BR6 and GW0 inputs**: `Theorem14.GW2LightConeStatement` from Theorem 1.3, the two schedule
containments and the exhaustion at interior tips (`gw2LightConeStatement_of_inputs` with the forced arcs from
`gw2ForcedArcStatement_of_theorem13`). -/
theorem gw2LightConeStatement_of_containments (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hC0 : GW2ScheduleContainmentStatement.{u})
    (hCv : GW2ArcScheduleContainmentStatement.{u}) (hEx : GW2TipExhaustionStatement.{u}) :
    GW2LightConeStatement.{u} :=
  gw2LightConeStatement_of_inputs hT13 hC0 (gw2ForcedArcStatement_of_theorem13 hT13 hT13₀) hCv hEx

end GW2Cone

end Theorem14

end InteractingSLE
