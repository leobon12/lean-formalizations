/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalSeed
import InteractingSLE.Spec.Sec7.RelClockAnnounce

/-!
# Positive boundary contacts as uncapped Galmarino rules

Packet PROVE-RETPLUMB. Time zero is excluded by a countable union of closed
time-space sets. The resulting rule uses the landed first-hit construction,
not the minimum of a putative rule and the recorded lifetime. The final lemma
isolates the exact observable boundary-approach input for predictability.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open LawUnique FlowStopIdentG
variable {nL nR : ℕ}

/-- The `m`th closed piece of the positive-time real boundary. -/
def retPositiveRealPiece (m : ℕ) : Set (ℝ≥0 × ℂ) :=
  {p | (1 : ℝ≥0) / (m + 1) ≤ p.1 ∧ p.2.im = 0}

theorem isClosed_retPositiveRealPiece (m : ℕ) : IsClosed (retPositiveRealPiece m) :=
  (isClosed_le continuous_const continuous_fst).inter
    (isClosed_eq (Complex.continuous_im.comp continuous_snd) continuous_const)

/-- The trace reader together with the current time. -/
def retTimedTrace (γ : HistorySpace nL nR) (t : ℝ≥0) : ℝ≥0 × ℂ :=
  (t, histTrace 0 γ t)

theorem measurable_retTimedTrace (t : ℝ≥0) :
    Measurable fun γ : HistorySpace nL nR => retTimedTrace γ t :=
  measurable_const.prodMk (measurable_histTrace 0 t)

theorem isNonAnticipating_retTimedTrace :
    IsNonAnticipating (retTimedTrace (nL := nL) (nR := nR)) := by
  intro γ γ' p h
  exact Prod.ext rfl (isNonAnticipating_histTrace 0 γ γ' p h)

/-- The first detected positive-time real contact; `⊤` when no contact is
detected. In particular this rule is not capped by the record's lifetime. -/
def retPositiveRealRule : HistorySpace nL nR → ℝ≥0∞ :=
  hitRuleSeq retTimedTrace retPositiveRealPiece

theorem measurable_retPositiveRealRule :
    Measurable (retPositiveRealRule (nL := nL) (nR := nR)) :=
  measurable_hitRuleSeq (fun p => measurable_retTimedTrace (dyadicTime p)) _

theorem isStrongGalmarino_retPositiveRealRule :
    IsStrongGalmarino (retPositiveRealRule (nL := nL) (nR := nR)) :=
  isStrongGalmarino_hitRuleSeq isNonAnticipating_retTimedTrace _

/-- Every positive time belongs to one of the closed time cutoffs. -/
theorem exists_retPositiveRealPiece {t : ℝ≥0} (ht : 0 < t) {z : ℂ} (hz : z.im = 0) :
    ∃ m, (t, z) ∈ retPositiveRealPiece m := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (NNReal.coe_pos.2 ht)
  refine ⟨m, ?_, hz⟩
  exact_mod_cast hm.le

/-- The positive real-contact rule recovers a finite boundary lifetime from
the actual killed history, without an integrated-evolution assumption. -/
theorem retPositiveRealRule_killedHistory {Ω : Type*}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
    {γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T) (he : V ω = T)
    (hc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
      {t | (t : ℝ≥0∞) < V ω})
    (h0 : W 0 ω = 0) (hg : IsGeneratingTrace (fun t => W t ω) (V ω) γ)
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → γ t ∈ QuantumZipper.H)
    (hreal : (γ T).im = 0) :
    retPositiveRealRule (killedHistory W VL VR V ω) = V ω := by
  obtain ⟨m, hm⟩ := exists_retPositiveRealPiece hT hreal
  rw [he]
  apply hitRuleSeq_eq_of_hit isClosed_retPositiveRealPiece hT he
    (continuous_id.continuousOn.prodMk (hg.2.1.mono (fun t ht => by
      change (t : ℝ≥0∞) ≤ V ω
      rw [he]
      exact ENNReal.coe_le_coe.2 ht)))
  · intro m t ht hmem
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ≥0) < 1 / (m + 1)) hmem.1
    have hh := hH t ht0 (by rw [he]; exact ENNReal.coe_lt_coe.2 ht)
    exact (ne_of_gt (show 0 < (γ t).im from hh)) hmem.2
  · exact hm
  · intro p hp
    have hpV : (dyadicTime p : ℝ≥0∞) < V ω := by rwa [he]
    have hg' : IsGeneratingTrace (fun t => W t ω) (V ω) (fun t => γ t - (0 : ℝ)) := by
      simpa only [Complex.ofReal_zero, sub_zero] using hg
    exact Prod.ext rfl (histTrace_killedHistory hc h0 hg' hpV)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Exact remaining boundary-approach mathematics. A witness must be observable
from the killed driving history, continuous before the lifetime, and unbounded
before every finite lifetime. This is a named hypothesis, not an existence claim. -/
def RetBoundaryApproachObservable {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} (P : Measure Ω) (hX : IsMeasurableKilledDriving W VL VR V) : Prop :=
  ∃ B : ℝ≥0 → Ω → ℝ,
    (∀ t c, MeasurableSet[drivingFiltration P hX t]
      {ω | (t : WithTop ℝ≥0) < V ω ∧ c < B t ω}) ∧
    (∀ ω, ContinuousOn (B · ω) {t | (t : WithTop ℝ≥0) < V ω}) ∧
    ∀ᵐ ω ∂P, V ω ≠ ⊤ → ∀ c : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < V ω ∧ c < B t ω

/-- Observable continuous blowup supplies the required own-filtration
announcement, by the landed entrance-time construction. -/
theorem retDrivingLifetimePredictable_of_boundaryApproach
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {hX : IsMeasurableKilledDriving W VL VR V}
    (hB : RetBoundaryApproachObservable P hX) : RetDrivingLifetimePredictable P hX := by
  have : (drivingFiltration P hX).IsRightContinuous := by
    unfold drivingFiltration
    infer_instance
  obtain ⟨B, hBa, hBc, hunb⟩ := hB
  refine ⟨Sec7.RelClock.announce B V, Sec7.RelClock.isStoppingTime_announce hBa hBc,
    Sec7.RelClock.monotone_announce, ?_, ?_⟩
  · intro n
    filter_upwards [hunb] with ω hω
    exact Sec7.RelClock.announce_lt hω n
  · exact Eventually.of_forall fun ω t ht => Sec7.RelClock.exists_le_announce hBc ht

end InteractingSLE.Restart.RetAux79
