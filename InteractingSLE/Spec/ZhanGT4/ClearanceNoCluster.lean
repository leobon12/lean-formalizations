/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.NoCluster
import InteractingSLE.Spec.ZhanGT4.A5Det

/-! # Clearance-based consumers of the two-force no-cluster statements. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper

section Main

variable {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The band probabilities tend to zero**, given the separated clearance input. -/
theorem IsIntegratedSLEEvolution.tendsto_codeLaw_band_of_clearance [IsProbabilityMeasure P] (hκ4 : 4 < κ)
    (hG2 : SeparatedClearanceStatement.{u} κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    Tendsto (fun m : ℕ => codeLaw κ ρL ρR (bandCodeSet (1 / ((m : ℝ) + 1))) (xL, xR)) atTop (𝓝 0) := by
  have hκ : 0 < κ := by linarith
  have hxL' : ∀ i, xL i < 0 := fun i => by rw [Fin.fin_one_eq_zero i]; exact hxL
  have hxR' : ∀ j, 0 < xR j := fun j => by rw [Fin.fin_one_eq_zero j]; exact hxR
  have hsep : ∀ i j, xL i < xR j := fun i j => (hxL' i).trans (hxR' j)
  have hcong : ∀ (Φ : ℕ → (Fin 1 → ℝ) × (Fin 1 → ℝ) → (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop),
      (∀ k, ∀ (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞),
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) → Φ k s w τ → Φ k s w' τ) →
      ∀ (p : ℕ → Prop) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞),
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) → (∀ k, p k → Φ k s w τ) → ∀ k, p k → Φ k s w' τ :=
    fun Φ hΦ p s w w' τ h hk k hpk => hΦ k s w w' τ h (hk k hpk)
  -- the band probability is that of the bands for all fractions `1/(k+1)`, `k ≤ m`
  have heq : ∀ m : ℕ, codeLaw κ ρL ρR (bandCodeSet (1 / ((m : ℝ) + 1))) (xL, xR) =
      codeLaw κ ρL ρR (bandCodeSetLE m) (xL, xR) := by
    intro m
    rw [← measure_band_eq_codeLaw hκ hsep hE, ← measure_eventOf_eq_codeLawS hκ hsep hE
      (measurableSet_bandCodeSetLE m)
      (Φ := fun s w τ => ∀ k : ℕ, k ≤ m → BandEvent (1 / ((k : ℝ) + 1)) s w τ)
      (fun x _ _ => by simp only [bandCodeSetLE, mem_iInter]; rfl)
      (hcong (fun k s w τ => BandEvent (1 / ((k : ℝ) + 1)) s w τ) (fun k => bandEvent_congr _) _)]
    congr 1
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · intro h k hk
      refine bandEvent_mono hxL hxR (by positivity) ?_ h
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    · intro h; exact h m le_rfl
  simp_rw [heq]
  have hanti : Antitone bandCodeSetLE := fun m m' hmm' x hx => by
    simp only [bandCodeSetLE, mem_iInter] at hx ⊢
    exact fun k hk => hx k (hk.trans hmm')
  have hlim := tendsto_codeLaw_iInter (a := κ) (ρL := ρL) (ρR := ρR) measurableSet_bandCodeSetLE hanti (xL, xR)
  convert hlim using 2
  -- the intersection has canonical probability zero
  rw [← measure_eventOf_eq_codeLawS hκ hsep hE (MeasurableSet.iInter measurableSet_bandCodeSetLE)
    (Φ := fun s w τ => ∀ m k : ℕ, k ≤ m → BandEvent (1 / ((k : ℝ) + 1)) s w τ)
    (fun x _ _ => by simp only [bandCodeSetLE, mem_iInter]; rfl)
    (fun s w w' τ h hb m k hk => bandEvent_congr _ s w w' τ h (hb m k hk))]
  symm
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_not_isTermCluster_mark_of_clearance hκ4 hG2 hxL hxR hwL hwR hE,
    hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ (isOrderedForceWord_one hxL hxR)
      (hasAdmissiblePartialSums_one hwL hwR) hxL' hxR', hE.2.2.2.2] with ω hmark ⟨hζ, η, hη⟩ hp hall
  obtain ⟨hw, -, -⟩ := continuous_state_of_top hζ hp
  have hb : ∀ m : ℕ, RealBand (1 / ((m : ℝ) + 1)) (xL, xR) η := fun m => by
    have h := hall m m le_rfl
    rw [hζ] at h
    exact (bandEvent_top_iff hw hp.1 hη _ _).1 h
  rcases isTermCluster_of_forall_realBand (s := (xL, xR)) hxL hxR hb with h | h
  · exact hmark η hη (xL 0) (Or.inl le_rfl) h
  · exact hmark η hη (xR 0) (Or.inr le_rfl) h

/-- **Lemma 3.4 of the additional note (B.3 of the follow-up note), for `κ > 4`**: given Part A's (G5) at positive
stopping times of ordinary `SLE_κ` and the separated two-force confinement (G2), separated two-force laws with weights
`≥ κ/2 − 2` have no real terminal cluster point. -/
theorem separatedNoRealClusterStatement_of_clearance {κ : ℝ} (hκ4 : 4 < κ) (hG5 : StoppingInverseBoundaryStatement.{u} κ)
    (hG2 : SeparatedClearanceStatement.{u} κ) : SeparatedNoRealClusterStatement.{u} κ := by
  intro xL xR ρL ρR hxL hxR hwL hwR Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hκ : 0 < κ := by linarith
  set Cl : Set Ω := {ω | ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
      ∃ x : ℝ, xL 0 < x ∧ x < xR 0 ∧ IsTermCluster η x} with hCl
  have hCl0 : P Cl = 0 := by
    have hle : ∀ m : ℕ, P Cl ≤ codeLaw κ ρL ρR (bandCodeSet (1 / ((m : ℝ) + 1))) (xL, xR) := fun m =>
      IsIntegratedSLEEvolution.measure_cluster_le_band hκ hG5 hxL hxR hwL hwR hE (by positivity)
    exact le_antisymm (ge_of_tendsto (IsIntegratedSLEEvolution.tendsto_codeLaw_band_of_clearance hκ4 hG2 hxL hxR hwL hwR hE)
      (Eventually.of_forall hle)) bot_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hCl0,
    ae_not_isTermCluster_mark_of_clearance hκ4 hG2 hxL hxR hwL hwR hE] with ω hω hmark η hη x
  by_contra hcon
  have hcl : IsTermCluster η x := isTermCluster_iff_not.2 hcon
  rcases le_or_gt x (xL 0) with h1 | h1
  · exact hmark η hη x (Or.inl h1) hcl
  rcases le_or_gt (xR 0) x with h2 | h2
  · exact hmark η hη x (Or.inr h2) hcl
  exact hω ⟨η, hη, x, h1, h2, hcl⟩

/-- Lemma 3.4 from the full stopping-time collar (G7) (`StoppingCollarStatement`), which contains (G5). -/
theorem separatedNoRealClusterStatement_of_collar_of_clearance {κ : ℝ} (hκ4 : 4 < κ) (hG7 : StoppingCollarStatement.{u} κ)
    (hG2 : SeparatedClearanceStatement.{u} κ) : SeparatedNoRealClusterStatement.{u} κ :=
  separatedNoRealClusterStatement_of_clearance hκ4
    (fun P _ 𝓕 B hB T hT hT0 => (hG7 P 𝓕 B hB T hT hT0).mono fun _ h => h.1) hG2

/-! ### Consequences: the two-force bases for `κ > 4` -/

/-- **Two-seed transience for `κ > 4`** (B.3 L1260–L1264), given Part A's (G5) and clearance. -/
theorem twoSeedTransienceStatement_of_gt_four_of_clearance {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedClearanceStatement.{0} κ) :
    TwoSeedTransienceStatement.{u} κ :=
  twoSeedTransienceStatement_of_separatedNoCluster (by linarith)
    (separatedNoRealClusterStatement_of_clearance hκ4 hG5 hG2)

/-- **Separated two-force transience for `κ > 4`** (B.3 L1265–L1276: "This proves all two-force bases, including
equality at the nonhitting threshold"), given Part A's (G5) and clearance: marks `x_L < 0 < x_R`, weights `≥ κ/2 − 2`; almost
surely every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_gt_four_of_clearance {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedClearanceStatement.{0} κ)
    {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hxL : xL 0 < 0) (hxR : 0 < xR 0) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_of_noCluster (by linarith)
    (separatedNoRealClusterStatement_of_clearance hκ4 hG5 hG2) hxL hxR hadm hE

end Main

end InteractingSLE.ZhanGT4
