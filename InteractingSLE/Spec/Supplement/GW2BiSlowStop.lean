/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BiBridge
import InteractingSLE.Spec.Supplement.GW2BhKill
import InteractingSLE.Spec.Supplement.GW2SgDec
import InteractingSLE.Spec.Supplement.GW2StlThr

/-!
# The slow stop of decision D3: a lower cap of the version family as a stage stop (S3)

Packet PROVE-GW2-BUF (round 6). Decision D3's slow stage stop is "a cap of the family": on the instance of version
`n + 1`, the stop `V n − start`. This file builds it for any good instance `I` and any lower cap `Vlow`, given by a
measurable path rule `ρ` along the instance's own driver.

* `lowCapStop c l I Vlow ρ`: the stop `Vlow − start` on GB6's record event (`0` off it). Its rule reads the stage
  record and the killed stage path through RELDET's exact decoders (`GW2Rd.stageRule ρ (augσ N) augA augPre` on
  `GW2Bh.killPath`);
* **`lowCapStop_good`**: `StageStop.Good`. The inputs are: the good instance; the rule `ρ` measurable and a path
  rule; `Vlow` measurable; on the record event `Vlow = ρ (gb6Rec, I.R)` and `Vlow < I.V` (STRICT); and
  `Vlow ≤ I.V` a.s.

Strictness on the record event is used twice: for `stop_lt`, and for `stop_eq`, where the rule reads the path killed
at the cap. For RELDET's family it is the request recorded in the handoff (`V n < V (n+1)` on the record event).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv GW2Sde GW2Rd GW2KM2 GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.SchedRule

variable {Ω : Type u} [MeasurableSpace Ω]

open Classical in
/-- **A lower cap as a stage stop**: `Vlow − start` on GB6's record event, read by the stage rule of `ρ` on the killed
stage path. -/
def lowCapStop (c : SourceData Ω) (l : List (EntryIdx c.Θ c.Q)) (I : StageInst Ω)
    (Vlow : Ω → ℝ≥0∞) (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) : StageStop Ω where
  stop ω := if gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s then
    Vlow ω - (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0∞) else 0
  rule y e := if augσ ((entryList l).length + 1) y ∈ gb6TS c.s then
    stageRule ρ (augσ ((entryList l).length + 1)) augA augPre (y, killPath e) else 0

/-- A path whose concatenation agrees with the prefix: a rule value below the start gives the stage rule `0`. -/
theorem stageRule_eq_zero_of_le {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) {σ : RecData → RecData}
    {A : RecData → ℝ≥0} {pre : RecData → ℝ≥0 → ℝ} {x rec : RecData} {R : ℝ≥0 → ℝ} (hσ : σ x = rec)
    (hag : ∀ t ≤ A x, pre x t = R t) (hle : ρ (rec, R) ≤ A x) (w : ℝ≥0 → ℝ) :
    stageRule ρ σ A pre (x, w) = 0 := by
  have hcat : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ρ (rec, R) → R t = catAt (pre x) (A x) w t := by
    intro t ht
    have htA : t ≤ A x := ENNReal.coe_le_coe.1 (ht.trans hle)
    simp only [catAt, htA, ↓reduceIte, hag t htA]
  have h1 := hρ rec R (catAt (pre x) (A x) w) hcat
  simp only [stageRule, hσ]
  rw [h1]
  exact tsub_eq_zero_of_le hle

/-- **The lower cap is a good stage stop.** -/
theorem lowCapStop_good {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}
    {I : StageInst Ω} (hI : I.Good c r l) {Vlow : Ω → ℝ≥0∞} {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρm : Measurable ρ) (hρ : IsPathRule ρ) (hVm : Measurable Vlow) (hVfin : ∀ ω, I.V ω ≠ ⊤)
    (hVρ : ∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → Vlow ω = ρ (gb6Rec c.s c.W c.ζ ω, fun u => I.R u ω))
    (hle : ∀ᵐ ω ∂c.P, Vlow ω ≤ I.V ω)
    (hlt : ∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → Vlow ω < I.V ω) :
    (lowCapStop c l I Vlow ρ).Good I c r l := by
  classical
  set N := (entryList l).length + 1 with hN
  have hsρ : IsPathRule (stageRule ρ (augσ N) augA augPre) := isPathRule_stageRule hρ _ _ _
  have hsρm : Measurable (stageRule ρ (augσ N) augA augPre) :=
    measurable_stageRule hρm (measurable_augσ N) measurable_augA measurable_augPre
  have hstart : Measurable (stgStart c.s I.W c.W c.ζ I.GT I.V I.T) :=
    GW2Stl.measurable_stgStart_of_pre hI.measurable_pre
  have hrecm : Measurable (gb6Rec c.s c.W c.ζ) := measurable_gb6Rec_src c
  have hRc := hI.version.2.1
  have hR0 := hI.version.2.2.1
  -- the decoders of the stage record
  have hdec : ∀ ω, augσ N (I.srec c r l ω) = gb6Rec c.s c.W c.ζ ω ∧
      augA (I.srec c r l ω) = stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω ∧
      ∀ t ≤ augA (I.srec c r l ω), augPre (I.srec c r l ω) t = I.R t ω := fun ω =>
    augDec_spec (stgRecDec_stageEncRec c r l ω) (hRc ω) (hR0 ω)
  refine ⟨fun y t => ?_, ?_, ?_, ?_, ?_⟩
  · -- the rule is a stopping rule of the killed path
    by_cases hy : augσ N y ∈ gb6TS c.s
    · have he : {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (lowCapStop c l I Vlow ρ).rule y e ≤ (t : ℝ≥0∞)} =
          {e | stageRule ρ (augσ N) augA augPre (y, killPath e) ≤ (t : ℝ≥0∞)} := by
        ext e
        simp only [lowCapStop, ← hN, hy, ↓reduceIte, mem_ofPred_eq]
      rw [he]
      exact measurableSet_killPath_le hsρ hsρm y t
    · have he : {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (lowCapStop c l I Vlow ρ).rule y e ≤ (t : ℝ≥0∞)} = univ := by
        ext e
        simp only [lowCapStop, ← hN, hy, ↓reduceIte, mem_ofPred_eq, zero_le, mem_univ]
      rw [he]
      exact MeasurableSet.univ
  · -- the stop is measurable
    exact Measurable.ite ((measurableSet_gb6TS c.s).preimage hrecm)
      (hVm.sub (measurable_coe_nnreal_ennreal.comp hstart)) measurable_const
  · -- the stop is the rule read on the record and the killed stage path
    filter_upwards [hVρ, hlt] with ω hVρω hltω
    obtain ⟨hσ, hA, hpre⟩ := hdec ω
    by_cases hm : gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s
    · have hrule : (lowCapStop c l I Vlow ρ).rule (I.srec c r l ω) ((fun t => I.drv c t ω), I.cap c ω) =
          stageRule ρ (augσ N) augA augPre (I.srec c r l ω, killPath ((fun t => I.drv c t ω), I.cap c ω)) := by
        simp only [lowCapStop, ← hN, hσ, hm, ↓reduceIte]
      have hstop : (lowCapStop c l I Vlow ρ).stop ω =
          Vlow ω - (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0∞) := by
        simp only [lowCapStop, hm, ↓reduceIte]
      rw [hrule, hstop]
      have hpre' : ∀ t ≤ augA (I.srec c r l ω), augPre (I.srec c r l ω) t = (fun u => I.R u ω) t := hpre
      by_cases hVA : Vlow ω ≤ (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0∞)
      · -- a lower cap before the start: both sides are `0`
        rw [tsub_eq_zero_of_le hVA]
        refine (stageRule_eq_zero_of_le hρ hσ hpre' ?_ _).symm
        rw [← hVρω hm, hA]
        exact hVA
      · -- after the start: the killed path is read before the cap
        have hVA' : (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0∞) < Vlow ω := not_le.1 hVA
        have hdrv : stageRule ρ (augσ N) augA augPre (I.srec c r l ω, fun t => I.drv c t ω) =
            Vlow ω - (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0∞) := by
          have h1 := stageRule_stgDrv (ρ := ρ) (σ := augσ N) (A := augA) (pre := augPre)
            (x := I.srec c r l ω) (hRc ω) (continuous_augPre _) hσ hpre'
          rw [hA] at h1
          rw [← hVρω hm] at h1
          exact h1
        have hcapgt : stageRule ρ (augσ N) augA augPre (I.srec c r l ω, fun t => I.drv c t ω) < I.cap c ω := by
          rw [hdrv]
          change _ < I.V ω - _
          rw [lt_tsub_iff_left, add_tsub_cancel_of_le hVA'.le]
          exact hltω hm
        rw [rule_killPath_eq hsρ (I.srec c r l ω) ((fun t => I.drv c t ω), I.cap c ω) hcapgt]
        exact hdrv.symm
    · have hrule : (lowCapStop c l I Vlow ρ).rule (I.srec c r l ω) ((fun t => I.drv c t ω), I.cap c ω) = 0 := by
        simp only [lowCapStop, ← hN, hσ, hm, ↓reduceIte]
      have hstop : (lowCapStop c l I Vlow ρ).stop ω = 0 := by
        simp only [lowCapStop, hm, ↓reduceIte]
      rw [hrule, hstop]
  · -- the stop is below the cap
    filter_upwards [hle] with ω hleω _
    by_cases hm : gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s
    · simp only [lowCapStop, hm, ↓reduceIte]
      exact tsub_le_tsub_right hleω _
    · simp only [lowCapStop, hm, ↓reduceIte]
      exact zero_le
  · -- a finite stop is strictly below the cap on the record event
    filter_upwards [hlt, hI.E_good] with ω hltω hEω hE _
    obtain ⟨hm, hst⟩ := hEω hE
    have hstart' : (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0∞) < I.V ω := by
      have hfin : stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω ≠ ⊤ :=
        ne_top_of_le_ne_top (hVfin ω) (min_le_right _ _)
      change ((stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω).toNNReal : ℝ≥0∞) < I.V ω
      rw [ENNReal.coe_toNNReal hfin]
      exact hst
    simp only [lowCapStop, hm, ↓reduceIte]
    change _ < I.V ω - _
    by_cases hVA : Vlow ω ≤ (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0∞)
    · rw [tsub_eq_zero_of_le hVA]
      exact tsub_pos_of_lt hstart'
    · rw [lt_tsub_iff_left, add_tsub_cancel_of_le (not_le.1 hVA).le]
      exact hltω hm

/-! ### The lower cap of a version family on the next version's instance -/

/-- **Two versions agree up to the lower cap, endpoint included** (on the record event): below both caps by
`ae_version_eq`, at the lower cap by continuity. -/
theorem ae_version_eq_le {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω' → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω' → ℝ}
    {ζα : Ω' → ℝ≥0∞} {γ α : Ω' → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    {s : ℝ≥0} {R R' : ℝ≥0 → Ω' → ℝ} {V V' : Ω' → ℝ≥0∞}
    (hver : IsGB6RelVersion s P W Wα ζα γ α R V) (hver' : IsGB6RelVersion s P W Wα ζα γ α R' V')
    (hle : ∀ᵐ ω ∂P, V ω ≤ V' ω) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ QuantumZipper.H → ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ V ω → R u ω = R' u ω := by
  have hRc := hver.2.1
  have hRc' := hver'.2.1
  filter_upwards [ae_version_eq hF hα hW hver hver', hle] with ω hω hleω hs hsH u hu
  have hlt : ∀ c' : ℝ≥0, c' < u → R c' ω = R' c' ω := fun c' hc' => by
    have h1 : (c' : ℝ≥0∞) < V ω := (ENNReal.coe_lt_coe.2 hc').trans_le hu
    exact hω hs hsH c' h1 (h1.trans_le hleω)
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | hpos
  · rw [← h0, hver.2.2.1 ω, hver'.2.2.1 ω]
  · have heq : EqOn (fun t => R t ω) (fun t => R' t ω) (Iio u) := fun t ht => hlt t ht
    have hcl := heq.closure (hRc ω) (hRc' ω)
    rw [closure_Iio' (show (Iio u).Nonempty from ⟨0, hpos⟩)] at hcl
    exact hcl (le_refl u)

/-- **The lower cap read along the next version's driver** (on the record event). -/
theorem ae_lowCap_rule_eq {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω' → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω' → ℝ}
    {ζα : Ω' → ℝ≥0∞} {γ α : Ω' → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    {s : ℝ≥0} {R R' : ℝ≥0 → Ω' → ℝ} {V V' : Ω' → ℝ≥0∞}
    (hver : IsGB6RelVersionR s P W Wα ζα γ α R V) (hver' : IsGB6RelVersion s P W Wα ζα γ α R' V')
    (hle : ∀ᵐ ω ∂P, V ω ≤ V' ω) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ QuantumZipper.H →
      V ω = hver.2.choose (gb6Rec s Wα ζα ω, fun u => R' u ω) := by
  obtain ⟨-, hρ, hVρ⟩ := hver.2.choose_spec
  filter_upwards [ae_version_eq_le hF hα hW hver.1 hver' hle, hVρ] with ω hag hVω hs hsH
  rw [hVω]
  exact (hρ (gb6Rec s Wα ζα ω) (fun u => R u ω) (fun u => R' u ω) fun u hu =>
    hag hs hsH u (hu.trans_eq hVω.symm)).symm

end InteractingSLE.Theorem14.GW2Bh
