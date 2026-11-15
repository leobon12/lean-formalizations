/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CollarBoundary
import InteractingSLE.Spec.ZhanGT4.NoCluster

/-!
# Weaker Zhan inputs: deterministic-time collars and protected-ray clearance (R53)

Packet PROVE-ZHAN-GT4-A16, orchestrator note R53. Source: Astra, *Follow-up A–E*, Part B
(`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L260–L467).

* **(B.1)/(G5) at deterministic rational times** (L325–L330): `DetInverseBoundaryStatement κ` (the inverse-boundary
  assertion `f_q((c(q), d(q))) ⊂ ℍ` at every deterministic positive rational `q`) and `DetCollarStatement κ` (the real
  collar at those times). They follow from the stopping-time forms (`detInverseBoundaryStatement_of_stopping`,
  `detCollarStatement_of_stopping`), and the collar follows from the inverse boundary pathwise by Lemma 3.1
  (`detCollarStatement_of_detInverseBoundary`). Almost surely all rational collars hold at once
  (`ae_forall_rat_hasRealCollar`).
* **(B.3), the deferred collar** (L378–L398): on that simultaneous event, for any selected (not necessarily stopping)
  time `S` and compact `F` strictly between two points swallowed by `S`, some neighbourhood of `F` is excluded from
  `closure (ℍ \ K_t)` for all `t` after a rational `q > S` (`exists_ball_notMem_closure_of_deferredCollar`,
  `exists_deferredCollar_of_forall_rat`); in particular from every later trace point and every terminal cluster set.
* **(B.3)/(B.4), the clearance interface** (L400–L447): `SeparatedClearanceStatement κ` — the separated two-force law
  has infinite lifetime and its terminal hull keeps a positive distance from every compact subset of the protected
  rays — which is everything `NoCluster.ae_not_isTermCluster_mark` uses of A.5 (`SeparatedTwoForceStatement`): the two
  crosscut parametrizations are not used. `separatedClearanceStatement_of_separatedTwoForce` is the bridge, and
  `ae_not_isTermCluster_mark_of_clearance` is the mark exclusion from the weaker input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open QuantumZipper QuantumZipper.RS

/-! ### (B.1): the inverse boundary and the collar at deterministic rational times -/

/-- **(G5) at deterministic positive rational times** (R53, Part B.2/B.3): for ordinary chordal `SLE_κ` driven by a
Brownian motion and every deterministic rational `q > 0`, almost surely `f_q((c(q), d(q))) ⊂ ℍ`. -/
def DetInverseBoundaryStatement (κ : ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓕 B P →
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, HasInteriorInverseBoundary (drive κ B ω) q

/-- **(B.1): the real collar at deterministic positive rational times** (L325–L330): for ordinary chordal `SLE_κ` and
every deterministic rational `q > 0`, almost surely every real point strictly between two points swallowed by time `q`
has a relative upper-half-plane neighbourhood in `K_q`. -/
def DetCollarStatement (κ : ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓕 B P →
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, HasRealCollar (drive κ B ω) q

/-- A deterministic positive time as a positive stopping time. -/
theorem isStoppingTime_const_toNNReal {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (t : ℝ) :
    IsStoppingTime 𝓕 fun _ : Ω => ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) :=
  isStoppingTime_const 𝓕 _

/-- **The stopping-time (G5) gives (G5) at deterministic rational times** (constant stopping times). -/
theorem detInverseBoundaryStatement_of_stopping {κ : ℝ} (h : StoppingInverseBoundaryStatement.{u} κ) :
    DetInverseBoundaryStatement.{u} κ := by
  intro Ω mΩ P _ 𝓕 B hB q hq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  filter_upwards [h P 𝓕 B hB (fun _ => (q : ℝ).toNNReal) (isStoppingTime_const_toNNReal 𝓕 _)
    fun _ => Real.toNNReal_pos.2 hq'] with ω hω
  rwa [Real.coe_toNNReal _ hq'.le] at hω

/-- **The stopping-time collar (G7) gives (B.1).** -/
theorem detCollarStatement_of_stopping {κ : ℝ} (h : StoppingCollarStatement.{u} κ) : DetCollarStatement.{u} κ := by
  intro Ω mΩ P _ 𝓕 B hB q hq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  filter_upwards [h P 𝓕 B hB (fun _ => (q : ℝ).toNNReal) (isStoppingTime_const_toNNReal 𝓕 _)
    fun _ => Real.toNNReal_pos.2 hq'] with ω hω
  rw [Real.coe_toNNReal _ hq'.le] at hω
  exact hω.2

/-- **(B.1) from (G5) at deterministic rational times** (Lemma 3.1 of the shortcut note, R52 Q3, pathwise: ordinary
`SLE_κ` has a continuous trace, so the inverse boundary in `ℍ` gives the collar). -/
theorem detCollarStatement_of_detInverseBoundary {κ : ℝ} (hκ : 0 < κ) (h : DetInverseBoundaryStatement.{u} κ) :
    DetCollarStatement.{u} κ := by
  intro Ω mΩ P _ 𝓕 B hB q hq
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq.le
  filter_upwards [h P 𝓕 B hB q hq, ae_isLoewnerTrace_sleTrace hB.1 hκ, hB.1.cont,
    hB.1.eval_zero_ae_eq_zero] with ω h5 hη hc h0
  exact hasRealCollar_of_isLoewnerTrace hη (drive_continuous hc) (drive_zero h0) hq' h5

/-- **All rational collars at once** (L328: "Intersecting these countably many events gives one event for all such
`q`"). -/
theorem ae_forall_rat_hasRealCollar {κ : ℝ} (h : DetCollarStatement.{u} κ) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsFilteredBrownianReal 𝓕 B P) : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → HasRealCollar (drive κ B ω) q := by
  rw [ae_all_iff]
  intro q
  by_cases hq : 0 < q
  · filter_upwards [h P 𝓕 B hB q hq] with ω hω _ using hω
  · exact Eventually.of_forall fun _ h => absurd h hq

/-! ### (B.3): the deferred collar -/

/-- A real point swallowed by time `S` is swallowed by every later time. -/
theorem IsSwallowedBy.mono {W : ℝ → ℝ} {x S q : ℝ} (h : IsSwallowedBy W x S) (hS : 0 ≤ S) (hSq : S ≤ q) :
    IsSwallowedBy W x q :=
  fun ⟨v, hv⟩ => h ⟨v, Ito.isForwardSol_of_le hv hS hSq⟩

/-- **(B.3), the deferred collar, deterministically** (L380–L385): if the real collar holds at a time `q` after a
selected time `S`, and the compact `F ⊆ ℝ` lies strictly between two points swallowed by `S`, then a neighbourhood of
`F` meets no `closure (ℍ \ K_t)` for `t ≥ q` (hull monotonicity puts `F` between points swallowed at `q`; compactness
gives one collar width; every point of `ℍ` near `F` is in `K_q ⊆ K_t`). -/
theorem exists_ball_notMem_closure_of_deferredCollar {W : ℝ → ℝ} {x z S q : ℝ} (hS : 0 ≤ S) (hSq : S ≤ q)
    (hC : HasRealCollar W q) (hx : IsSwallowedBy W x S) (hz : IsSwallowedBy W z S) {F : Set ℝ} (hF : IsCompact F)
    (hFxz : F ⊆ Ioo x z) :
    ∃ ε > (0 : ℝ), ∀ t, q ≤ t → ∀ y ∈ F, ∀ w : ℂ, ‖w - y‖ < ε → w ∉ closure (H \ fwdHull W t) := by
  obtain ⟨ε, hε, hcol⟩ := hC.exists_uniform (hx.mono hS hSq) (hz.mono hS hSq) hF hFxz
  refine ⟨ε / 2, half_pos hε, fun t hqt y hy w hw hcl => ?_⟩
  obtain ⟨w', hw'K, hw'w⟩ := Metric.mem_closure_iff.1 hcl (ε / 2) (half_pos hε)
  have hw'y : ‖w' - y‖ < ε := by
    calc ‖w' - y‖ = ‖(w - y) - (w - w')‖ := by ring_nf
      _ ≤ ‖w - y‖ + ‖w - w'‖ := norm_sub_le _ _
      _ < ε / 2 + ε / 2 := by rw [← dist_eq_norm w w']; exact add_lt_add hw hw'w
      _ = ε := add_halves ε
  exact hw'K.2 ((QuantumZipper.fwdHull_mono).1 hqt (hcol y hy w' hw'K.1 hw'y))

/-- **(B.3) on the simultaneous rational event** (L380–L389: "This is a deterministic argument on the countable
simultaneous event; `S` need not be a stopping time"): for every selected time `S ≥ 0` and compact `F` strictly
between two points swallowed by `S`, there are a time `q > S` and a neighbourhood of `F` disjoint from
`closure (ℍ \ K_t)` for every `t ≥ q`. -/
theorem exists_deferredCollar_of_forall_rat {W : ℝ → ℝ} (hC : ∀ q : ℚ, 0 < q → HasRealCollar W q) {x z S : ℝ}
    (hS : 0 ≤ S) (hx : IsSwallowedBy W x S) (hz : IsSwallowedBy W z S) {F : Set ℝ} (hF : IsCompact F)
    (hFxz : F ⊆ Ioo x z) :
    ∃ q : ℝ, S < q ∧ ∃ ε > (0 : ℝ), ∀ t, q ≤ t → ∀ y ∈ F, ∀ w : ℂ, ‖w - y‖ < ε →
      w ∉ closure (H \ fwdHull W t) := by
  obtain ⟨q, hq⟩ := exists_rat_gt S
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hS.trans_lt hq
  exact ⟨q, hq, exists_ball_notMem_closure_of_deferredCollar hS hq.le (hC q hq0) hx hz hF hFxz⟩

/-! ### (B.3)/(B.4): the protected-ray clearance interface -/

/-- **(B.3)/(B.4), the protected-ray clearance interface for the separated two-force law** (L405–L412): for `κ > 4`,
marks `p_L < 0 < p_R` and weights `ρ_L, ρ_R ≥ κ/2 − 2`, almost surely the integrated `SLE_κ(ρ_L; ρ_R)` evolution lives
forever and its terminal hull has positive distance from every compact subset of `(−∞, p_L] ∪ [p_R, ∞)`. This is
`SeparatedTwoForceStatement κ` without the two crosscut parametrizations (B.4: "The two simple crosscut
parametrizations are not subsequently used"). -/
def SeparatedClearanceStatement (κ : ℝ) : Prop :=
  4 < κ → ∀ (pL pR ρL ρR : ℝ), pL < 0 → 0 < pR → κ / 2 - 2 ≤ ρL → κ / 2 - 2 ≤ ρR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![pL] ![pR] ![ρL] ![ρR] P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
          ∀ C : Set ℝ, IsCompact C → C ⊆ Iic pL ∪ Ici pR →
            ∃ δ > (0 : ℝ), ∀ z ∈ terminalHull (fun t => W t ω) (ζ ω), ∀ x ∈ C, δ ≤ ‖z - x‖

/-- **A.5 gives the clearance interface** (drop the crosscut conjunct). -/
theorem separatedClearanceStatement_of_separatedTwoForce {κ : ℝ} (h : SeparatedTwoForceStatement.{u} κ) :
    SeparatedClearanceStatement.{u} κ :=
  fun hκ pL pR ρL ρR hpL hpR hρL hρR _ _ P _ 𝓕 W VL VR B ζ hE =>
    (h hκ pL pR ρL ρR hpL hpR hρL hρR P 𝓕 W VL VR B ζ hE).mono fun _ hω => ⟨hω.1, hω.2.2⟩

/-- **No terminal cluster point at or beyond the marks, from the clearance interface** (the form of
`IsIntegratedSLEEvolution.ae_not_isTermCluster_mark` with A.5 weakened to (B.3), R53): the trace stays in the closure
of the hull, which keeps a positive distance from every compact subset of `(−∞, p_L] ∪ [p_R, ∞)`. -/
theorem ae_not_isTermCluster_mark_of_clearance {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ4 : 4 < κ)
    (hG2 : SeparatedClearanceStatement.{u} κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → ∀ x : ℝ, (x ≤ xL 0 ∨ xR 0 ≤ x) →
      ¬ IsTermCluster η x := by
  have e1 : (![xL 0] : Fin 1 → ℝ) = xL := by funext i; fin_cases i; rfl
  have e2 : (![xR 0] : Fin 1 → ℝ) = xR := by funext i; fin_cases i; rfl
  have e3 : (![ρL 0] : Fin 1 → ℝ) = ρL := by funext i; fin_cases i; rfl
  have e4 : (![ρR 0] : Fin 1 → ℝ) = ρR := by funext i; fin_cases i; rfl
  have hE' : IsIntegratedSLEEvolution κ ![xL 0] ![xR 0] ![ρL 0] ![ρR 0] P 𝓕 W VL VR B ζ := by
    rw [e1, e2, e3, e4]; exact hE
  filter_upwards [hG2 hκ4 (xL 0) (xR 0) (ρL 0) (ρR 0) hxL hxR hwL hwR P 𝓕 W VL VR B ζ hE', hE.2.2.2.2]
    with ω ⟨hζ, hdist⟩ hp η hη x hx
  obtain ⟨hw, -, -⟩ := continuous_state_of_top hζ hp
  have hWc : Continuous fun s : ℝ => W s.toNNReal ω := hw.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simpa using hp.1
  obtain ⟨δ, hδ, hfar⟩ := hdist {x} isCompact_singleton (by
    rintro y rfl
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h)
  rw [isTermCluster_iff_not, not_not]
  refine ⟨δ, hδ, (eventually_gt_atTop 0).mono fun t ht => ?_⟩
  have htip := hη.tendsto_fwdMapInv_tip hw.continuousOn hp.1 (t := t) ENNReal.coe_lt_top
  have hcl := YuanCorollary13.mem_closure_fwdHull_of_tendsto hWc hW0 (NNReal.coe_pos.2 ht) htip
  have hsub : fwdHull (fun s : ℝ => W s.toNNReal ω) t ⊆ {z : ℂ | δ ≤ ‖z - x‖} := fun z hz =>
    hfar z (mem_iUnion₂.2 ⟨t, by rw [hζ]; exact ENNReal.coe_lt_top, hz⟩) x rfl
  have hclosed : IsClosed {z : ℂ | δ ≤ ‖z - x‖} :=
    isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  exact hclosed.closure_subset_iff.2 hsub hcl

end InteractingSLE.ZhanGT4
