/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513BridgeField
import InteractingSLE.Spec.Sec5.Prop513AsmWire
import InteractingSLE.Foundations.SLE.All
import InteractingSLE.Foundations.SLE.SpaceFilling.Swallow

/-!
# Proposition 5.13 in the parameter-field frame used by the pocket references

PROVE-PROP513-BRIDGE. The assembly concludes determination of the driving trace,
already in the counterflow capacity chart. A full-domain signed chart transport
identifies the sigma-algebra of its Fig. 5.1 input with the parameter field's.
Changing that field's deterministic mean gives precisely the consumers' `h513`.

The Fig. 5.1 field law and its transport to the actual parameter field remain
explicit frame hypotheses. Constructing that field from a particular strip system
requires identifying its boundary data, and is not asserted for arbitrary words.
No theorem of determination or continuity in full generality is used (R48).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal
universe u v

namespace InteractingSLE.Sec5.Prop513Bridge

open QuantumZipper LQGMetric Sec4 Prop59Stage Prop59System Prop513Schedule Prop513TreeExtract
  Prop513Target Prop513Asm Restart Exist Exist.Staged Exist.StagedLaw StripRevVisit
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- Restrict the consumers' real-time driver and trace to nonnegative time.
Negative driver values do not affect any forward hull. -/
theorem generatingTrace_of_loewner {W : ℝ → ℝ} {η : ℝ → ℂ}
    (htr : IsLoewnerTrace W η) :
    IsGeneratingTrace (fun t : ℝ≥0 => W t) ⊤ (fun t : ℝ≥0 => η t) := by
  have he : ∀ t : ℝ, 0 ≤ t → W t = W (t.toNNReal : ℝ) := by
    intro t ht
    rw [Real.coe_toNNReal t ht]
  exact ((InteractingSLE.isLoewnerTrace_congr_drive he).1 htr).isGeneratingTrace

/-- Proposition 5.13 for the actual parameter field. The four assembly inputs
are unchanged: first hits, regular histories, experiments, and their stage laws.
The additional displayed chart relation identifies the field frame only. -/
theorem prop513_comap_parameter_of_histExp_current
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Prop59StageLawStatement κ (P.prod Pa) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r))
    {hP : Ω → DistOn upperHalfPlaneOpens} {aP kP : ℝ}
    (hT : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * x₀)))
      (-1) aP kP (h ω) (hP ω)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ,
      (∀ t, StronglyMeasurable[MeasurableSpace.comap hP inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  obtain ⟨Γ', hm, he⟩ := prop513_comap_of_histExp_current
    h47 hA2 hA2' hFH hκ hκ4 hb hG hcf htr hE hR X₀ hL₀ X hL
  refine ⟨Γ', ?_, he⟩
  intro t
  rw [← comap_eq_strip_parameter (Real.exp_pos _) hT]
  exact hm t

/-- The literal `h513` field of `RefWireSide` and `RefWireAux131Side`:
the parameter field with its original mean removed and any deterministic mean
added. No equality of the two means is assumed. -/
theorem prop513_comap_centred_of_histExp_current
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Prop59StageLawStatement κ (P.prod Pa) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r))
    {hP : Ω → DistOn upperHalfPlaneOpens} {aP kP : ℝ}
    (hT : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * x₀)))
      (-1) aP kP (h ω) (hP ω))
    (u₀ u : ℂ → ℝ) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ,
      (∀ t, StronglyMeasurable[MeasurableSpace.comap
        (fun ω => WholeField.centredField hP u₀ ω + smoothDist upperHalfPlaneOpens u)
        inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  rw [comap_centredField_add]
  exact prop513_comap_parameter_of_histExp_current
    h47 hA2 hA2' hFH hκ hκ4 hb hG hcf htr hE hR X₀ hL₀ X hL hT

/-- The literal `h513` field of `StripPocketMarksInput`, `R7PocketStop`,
`RefWirePerQ` and Aux. 131, with the zero-boundary part denoted by `hP`. -/
theorem prop513_comap_pocket_of_histExp_current
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Prop59StageLawStatement κ (P.prod Pa) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r))
    {hP : Ω → DistOn upperHalfPlaneOpens} {aP kP : ℝ}
    (hT : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * x₀)))
      (-1) aP kP (h ω) (hP ω))
    (u : ℂ → ℝ) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ,
      (∀ t, StronglyMeasurable[MeasurableSpace.comap
        (fun ω => hP ω + smoothDist upperHalfPlaneOpens u)
        inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  have he : (fun ω => hP ω + smoothDist upperHalfPlaneOpens u) =
      fun ω => hP ω - (-smoothDist upperHalfPlaneOpens u) := by
    funext ω
    exact (sub_neg_eq_add _ _).symm
  rw [he, WholeField.comap_sub_dist]
  exact prop513_comap_parameter_of_histExp_current
    h47 hA2 hA2' hFH hκ hκ4 hb hG hcf htr hE hR X₀ hL₀ X hL hT

/-- Transfer from the actual parameter mean `uP` to the consumers' chosen
mean `u`, while keeping the same zero-boundary part. The two means need not agree. -/
theorem prop513_comap_remean_of_histExp_current
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Prop59StageLawStatement κ (P.prod Pa) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r))
    {hP : Ω → DistOn upperHalfPlaneOpens} {aP kP : ℝ} (uP : ℂ → ℝ)
    (hT : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * x₀)))
      (-1) aP kP (h ω) (hP ω + smoothDist upperHalfPlaneOpens uP))
    (u : ℂ → ℝ) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ,
      (∀ t, StronglyMeasurable[MeasurableSpace.comap
        (fun ω => hP ω + smoothDist upperHalfPlaneOpens u)
        inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  obtain ⟨Γ', hm, he⟩ := prop513_comap_parameter_of_histExp_current
    h47 hA2 hA2' hFH hκ hκ4 hb hG hcf htr hE hR X₀ hL₀ X hL hT
  refine ⟨Γ', ?_, he⟩
  intro t
  rw [comap_add_dist]
  rw [comap_add_dist] at hm
  exact hm t

end InteractingSLE.Sec5.Prop513Bridge
