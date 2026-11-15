/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BhIdent
import InteractingSLE.Spec.Supplement.GW2BhStop
import InteractingSLE.Spec.Supplement.GW2SxTimeVer

/-!
# The physical-time rule along relative coordinates, and contact from a positive separation (S3)

Packet PROVE-GW2-BUF (S3, round 6; the same under every option of decision D3, which concerns the version cap only).
R115's stop is `min(ρ_ℓ, ρ_time(T+m+1))`. RELDET evaluates JOINTDET's physical-time rule `timeCapRule` along a
VERSION (`GW2Rd.ae_timeCap_sample`). This file evaluates it along ANY relative coordinates `(D, L)` of an explored
curve, which are continuous only before the first contact:

* `compactSeparation_le_value`, `compactSeparation_le_one`;
* **`lt_firstContactTime_of_compactSeparation_pos`**: a positive compact separation of two continuous traces on
  `[0, t] × [0, s]` puts `t` before their first contact;
* **`ae_min_timeCapRule_coord`**: almost surely on the record event, below the life `L` the rule is RELDET's
  `capClock` (the relative clock of `Δ` before the first contact, `⊤` after), at every physical time `Δ`;
* **`ae_timeCapRule_coord`**: hence `timeCapRule s Δ (gb6Rec, D) = gb6Clock Δ` before the first contact.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.GaugeE Supp8.GB6.ReadD Supp8.GB6.RelDrv Supp8.GB6.HullId
  GW2TipSystem GW2Rd GW2JDetR3

/-- A compact separation is below each of its values. -/
theorem compactSeparation_le_value (X A : ℝ≥0 → ℂ) {t s u w : ℝ≥0} (hu : u ≤ t) (hw : w ≤ s) :
    compactSeparation X A t s ≤ separationValue (X u) (A w) := by
  obtain ⟨y, hy⟩ := exists_unit_mul hu
  obtain ⟨y', hy'⟩ := exists_unit_mul hw
  unfold compactSeparation squareMin
  refine csInf_le ⟨0, ?_⟩ ⟨(y, y'), ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact separationValue_nonneg _ _
  · simp only [prefixIntegrand, hy, hy']

theorem compactSeparation_le_one (X A : ℝ≥0 → ℂ) (t s : ℝ≥0) : compactSeparation X A t s ≤ 1 :=
  (compactSeparation_le_value X A le_rfl le_rfl).trans (separationValue_le_one _ _)

/-- **A positive compact separation is before the first contact.** -/
theorem lt_firstContactTime_of_compactSeparation_pos {γ α : ℝ≥0 → ℂ} (hγ : Continuous γ) (hα : Continuous α)
    {t s : ℝ≥0} (hpos : 0 < compactSeparation γ α t s) :
    (t : ℝ≥0∞) < firstContactTime (fun u => sphereInv (γ u : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := by
  refine (Gm.lt_firstContactTime_iff_noncontact hγ hα t s).2 fun u hu w hw => ?_
  exact (separationValue_pos_iff _ _).1 (hpos.trans_le (compactSeparation_le_value γ α hu.2 hw.2))

/-- **The physical-time rule along relative coordinates**, below the coordinates' life, at every physical time. -/
theorem ae_min_timeCapRule_coord {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    {s : ℝ≥0} (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → ∀ Δ : ℝ≥0,
      min (L ω) (timeCapRule s Δ (gb6Rec s Wα ζα ω, fun u => D u ω)) =
        min (L ω) (capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ) := by
  filter_upwards [ae_driver_zero_continuousOn hF, hα, hW, hC.relative, ae_gb6RecGood hF hα s]
    with ω hfl hαω hWω hrel hgood hm Δ
  obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hgood).2 hm
  obtain ⟨h0, hc⟩ := hfl
  obtain ⟨hWc, hW0, hγ⟩ := hWω
  obtain ⟨hcov, hhull⟩ := hrel hs hsH
  have hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ⊤} := hWc.continuousOn
  have hTc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
      (t : ℝ≥0∞) < min (gb6Tc s γ α ω) ⊤ := fun t ht => lt_min ht ENNReal.coe_lt_top
  obtain ⟨-, -, ha0, hm', hcont, -, -⟩ :=
    exists_inverse_capacity_chain Wα ζα ω hαω hc h0 hs hsH hγ hw hW0 ENNReal.zero_lt_top
  have he : EqOn (rdrv (gb6Rec s Wα ζα ω)) (Ito.rpath (Wα · ω)) (Icc 0 s) := GaugeE.record_prefix_eq s h0 hc hs
  have hclock : (fun t : ℝ≥0 => relClock (rdrv (gb6Rec s Wα ζα ω)) s (Ito.rpath (W · ω)) t) =
      gb6Clock s W Wα ω := by
    funext t
    rw [relClock_eq_of_eqOn s.coe_nonneg he]
    rfl
  have ha0' : gb6Clock s W Wα ω 0 = 0 := by
    rw [← hclock]
    exact ha0
  have hm'' : StrictMonoOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} := by
    rw [← hclock]
    exact hm'.mono fun t ht => hTc t ht
  have hc' : ContinuousOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} := by
    rw [← hclock]
    exact hcont.mono fun t ht => hTc t ht
  -- the rational prefix capacities of the coordinates read the physical times
  have hread : ∀ (q : ℚ≥0) (t : ℝ≥0), (t : ℝ≥0∞) < gb6Tc s γ α ω → gb6Clock s W Wα ω t = ((q : ℝ≥0) : ℝ) →
      ((q : ℝ≥0) : ℝ≥0∞) ≤ L ω →
      prefixCapacity s q (gb6Rec s Wα ζα ω) (killedCode ((fun u => D u ω), ⊤)) = t := by
    intro q t ht hat _
    have hqL : ((q : ℝ≥0) : ℝ≥0∞) < L ω := by
      have h1 := (hhull t ht).2.1
      rwa [hat, ENNReal.ofReal_coe_nnreal] at h1
    have hK : QuantumZipper.fwdHull (Ito.rpath fun u => D u ω) ((q : ℝ≥0) : ℝ) =
        relMap (Ito.rpath (Wα · ω)) s '' QuantumZipper.fwdHull (Ito.rpath (W · ω)) t := by
      have h1 := (hhull t ht).2.2
      rw [hat] at h1
      exact h1
    have hmap : relMap (rdrv (gb6Rec s Wα ζα ω)) s = relMap (Ito.rpath (Wα · ω)) s :=
      GaugeE.record_relMap_eq s h0 hc hs
    have hinv : relInv (rdrv (gb6Rec s Wα ζα ω)) s '' QuantumZipper.fwdHull (Ito.rpath fun u => D u ω)
        ((q : ℝ≥0) : ℝ) = QuantumZipper.fwdHull (Ito.rpath (W · ω)) t := by
      rw [hK, ← hmap]
      exact relInv_image_relMap_before_contact Wα ζα ω hαω hc h0 hs hγ hw hW0 (hTc t ht)
    have hloc : prefixCapacity s q (gb6Rec s Wα ζα ω) (killedCode ((fun u => D u ω), ⊤)) =
        prefixCapacity s q (gb6Rec s Wα ζα ω) (killedCode ((fun u => D u ω), L ω)) := by
      refine prefixCapacity_local s q _ _ _ fun u hu => ?_
      have huL : (((u : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < L ω :=
        (ENNReal.coe_le_coe.2 (show ((u : ℚ≥0) : ℝ≥0) ≤ (q : ℝ≥0) by exact_mod_cast hu)).trans_lt hqL
      simp only [killedCode, huL, ENNReal.coe_lt_top, ↓reduceIte]
    rw [hloc]
    unfold prefixCapacity
    rw [GW2JDetR6.physicalCapacity_live_prefix s _ (e := ((fun u => D u ω), L ω)) (hC.continuous ω) (hC.zero ω)
      hqL le_rfl hγ hw hW0 ENNReal.coe_lt_top hinv, ENNReal.ofReal_coe_nnreal]
  exact min_timeCapRule ha0' hm'' hc' hread hcov Δ

/-- **The physical-time rule along relative coordinates** reads the relative clock before the first contact. -/
theorem ae_timeCapRule_coord {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    {s : ℝ≥0} (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → ∀ Δ : ℝ≥0, (Δ : ℝ≥0∞) < gb6Tc s γ α ω →
      timeCapRule s Δ (gb6Rec s Wα ζα ω, fun u => D u ω) = ENNReal.ofReal (gb6Clock s W Wα ω Δ) := by
  filter_upwards [ae_min_timeCapRule_coord hF hα hW hC, hC.relative, ae_gb6RecGood hF hα s]
    with ω hmin' hrel hgood hm Δ hΔ
  obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hgood).2 hm
  obtain ⟨-, hhull⟩ := hrel hs hsH
  have hmin := hmin' hm Δ
  have hlt : ENNReal.ofReal (gb6Clock s W Wα ω Δ) < L ω := (hhull Δ hΔ).2.1
  have hcap : capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ = ENNReal.ofReal (gb6Clock s W Wα ω Δ) := by
    simp only [capClock, hΔ, ↓reduceIte]
  rw [hcap, min_eq_right hlt.le] at hmin
  by_contra hne
  rcases le_total (L ω) (timeCapRule s Δ (gb6Rec s Wα ζα ω, fun u => D u ω)) with hle | hle
  · rw [min_eq_left hle] at hmin
    exact (lt_irrefl _) (hmin ▸ hlt)
  · exact hne (by rw [min_eq_right hle] at hmin; exact hmin)

end InteractingSLE.Theorem14.GW2Bh
