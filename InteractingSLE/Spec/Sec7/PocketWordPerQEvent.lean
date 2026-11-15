/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripPocketConfigEvent

/-!
# Strip pocket selection with a walls σ-algebra chosen at the selected seed

Packet PROVE-STRIPSYS-PERQ. Specification pp. 411–412 (`source/spec/p385-432.md`): the event `F_q` reads only the
final two incoming walls. We reuse the existing rational selection, then apply its contact-event measurability
lemma with `𝓦 q`. Every `𝓦 q` contains the null sets; no measurability of `Lr p` in `𝓦 q` for `p ≠ q` is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function MeasureTheory Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketWordPerQ

open WangWu Lemma71I PocketCoord PocketJordan PocketMeas StripPocketConfig

variable {Ω : Type*} {𝓦 : ℚ → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The selected contact event is measurable from the two walls at its own rational seed, up to null sets. -/
theorem exists_stripPocketEvent_perQ [IsProbabilityMeasure P] (h𝓦 : ∀ q, 𝓦 q ≤ mΩ) (hnull : ∀ q, Ito.nullSets P ≤ 𝓦 q)
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ q t, Measurable[𝓦 q] fun ω => R ω t) (hLm : ∀ q t, Measurable[𝓦 q] fun ω => Lr q ω t)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar)
    (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hlate : ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (R ω)) :
    ∃ q : ℚ, 0 < q ∧ ∃ G : Set Ω, MeasurableSet[𝓦 q] G ∧ 0 < P G ∧
      ∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q) ∧ IsWallReverseVisit (R ω) (η ω) ∧
        IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (R ω) (η ω) := by
  classical
  have hLall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → (IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q)) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · filter_upwards [hL q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  obtain ⟨G₀, hG₀m, hG₀ae, hG₀⟩ := exists_measurableSet_nullSets_ae (P := P) (hR.and (hβ.and hLall))
  have hG₀m' : MeasurableSet G₀ := Ito.nullSets_le P _ hG₀m
  have hcont : ∀ ω ∈ G₀, Continuous (discCf (η ω)) ∧ Continuous (discWall (R ω)) ∧
      Continuous (discWall (β ω)) := fun ω hω =>
    ⟨continuous_discCf (hηc ω) (hηH ω), continuous_discWall (hG₀ ω hω).1.1,
      continuous_discWall (hG₀ ω hω).2.1.1⟩
  have hmeas : ∀ q : ℚ, Measurable (fun ω => discCf (η ω) (StripSys.rt q)) ∧
      Measurable (fun ω => discWall (R ω) (StripSys.rt q)) ∧
      Measurable (fun ω => discWall (β ω) (StripSys.rt q)) := fun q =>
    ⟨(StripPocketConfig.measurable_cayley.comp (hηm _ (StripSys.rt q).coe_nonneg)).neg,
      StripPocketConfig.measurable_cayley.comp ((hRm 0 _).mono (h𝓦 0) le_rfl),
      StripPocketConfig.measurable_cayley.comp (hβm _)⟩
  have hsel : ∀ᵐ ω ∂P, StripSys.IsSelectionConfig (discCf (η ω)) (discWall (R ω)) (discWall (β ω)) 1 := by
    filter_upwards [hR, hβ, hnohit, hlate] with ω hRω hβω hnω hlω
    exact isSelectionConfig_disc hRω.1 hβω.1 (hηc ω) (hη0 ω) (hηH ω) hβω.2.1 hβω.2.2 hnω hlω
  set βr : ℚ → Ω → ℝ≥0 → ℂ := fun r ω => if 0 < r then discWall (Lr r ω) else discWall (R ω) with hβr
  have hchange : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, Continuous (βr r ω) ∧
      βr r ω (StripSys.rt r) = discWall (β ω) (StripSys.rt r) ∧
      (Antitone fun t => Aux130.firstVisit (discCf (η ω)) (βr r ω t)) ∧
      Antitone fun t => Aux130.firstVisit (discCf (η ω)) (discWall (R ω) t) := by
    intro r hr
    filter_upwards [hR, hL r hr] with ω hRω hLω
    simp only [hβr, hr, ↓reduceIte]
    refine ⟨continuous_discWall hLω.1, ?_, antitone_firstVisit_discWall hLω.1 (hηc ω) (hη0 ω) (hηH ω) hLω.2.1,
      antitone_firstVisit_discWall hRω.1 (hηc ω) (hη0 ω) (hηH ω) hRω.2.1⟩
    show cayley (Lr r ω (StripSys.rt r)) = cayley (β ω (StripSys.rt r))
    rw [hLω.2.2]
  obtain ⟨q, hq, hFpos'⟩ := StripSys.exists_rat_measure_contactEvent_pos (P := P)
    hG₀m' hcont hmeas hG₀ae hsel hchange
  have hc' : ∀ ω ∈ G₀, Continuous (discWall (R ω)) ∧ Continuous (βr q ω) := fun ω hω => by
    refine ⟨(hcont ω hω).2.1, ?_⟩
    simp only [hβr, hq, ↓reduceIte]
    exact continuous_discWall ((hG₀ ω hω).2.2 q hq).1
  have hm' : ∀ p : ℚ, Measurable[𝓦 q] (fun ω => discWall (R ω) (StripSys.rt p)) ∧
      Measurable[𝓦 q] (fun ω => βr q ω (StripSys.rt p)) := fun p => by
    refine ⟨StripPocketConfig.measurable_cayley.comp (hRm q _), ?_⟩
    simp only [hβr, hq, ↓reduceIte]
    exact StripPocketConfig.measurable_cayley.comp (hLm q _)
  have hFm : MeasurableSet[𝓦 q] (G₀ ∩ StripSys.contactEvent
      (fun ω => discWall (R ω)) (βr q) q) :=
    StripSys.measurableSet_inter_contactEvent (mΩ := 𝓦 q) (hnull q _ hG₀m) hc' hm' hq.le
  have hFpos : 0 < P (G₀ ∩ StripSys.contactEvent (fun ω => discWall (R ω)) (βr q) q) := by
    rw [inter_comm G₀, measure_inter_conull (ae_iff.1 hG₀ae)]
    exact hFpos'
  refine ⟨q, hq, _, hFm, hFpos, fun ω hω => ?_⟩
  obtain ⟨hω₀, hcp⟩ := hω
  obtain ⟨hRω, -, hLall'⟩ := hG₀ ω hω₀
  have hLω := hLall' q hq
  have hcp' : StripSys.IsContactPoint (discWall (R ω)) (discWall (Lr q ω)) q := by
    have : βr q ω = discWall (Lr q ω) := by simp only [hβr, hq, ↓reduceIte]
    rw [← this]
    exact hcp
  have hcpH := isContactPoint_of_disc hRω.1 (mem_Hbar_of_isSimpleProper hLω.1) hcp'
  have hpos : 0 < StripSys.rt q := Real.toNNReal_pos.2 (Rat.cast_pos.2 hq)
  have hconf := isChangeConfigInc_of_reverseVisit hRω.1 hLω.1 (hηc ω) (hη0 ω) hRω.2.1 hLω.2.1 hRω.2.2 hpos
    fun hmem => hcpH.1 (subset_closure hmem)
  exact ⟨hconf, discTime_one_lt_rightHi_of_isContactPoint hconf hcpH, hRω.2.1, hLω.2.1, hRω.2.2⟩

/-- **The per-seed event with further almost sure facts**: any family `Q q` of almost sure properties (for
instance the counterflow's remaining configuration facts at the change time `q`) also holds on the selected event,
after removing a null set. -/
theorem exists_stripPocketEvent_perQ_ae [IsProbabilityMeasure P] (h𝓦 : ∀ q, 𝓦 q ≤ mΩ)
    (hnull : ∀ q, Ito.nullSets P ≤ 𝓦 q)
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ q t, Measurable[𝓦 q] fun ω => R ω t) (hLm : ∀ q t, Measurable[𝓦 q] fun ω => Lr q ω t)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar)
    (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hlate : ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (R ω))
    {Q : ℚ → Ω → Prop} (hQ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Q q ω) :
    ∃ q : ℚ, 0 < q ∧ ∃ G : Set Ω, MeasurableSet[𝓦 q] G ∧ 0 < P G ∧
      ∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q) ∧ IsWallReverseVisit (R ω) (η ω) ∧
        IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (R ω) (η ω) ∧ Q q ω := by
  obtain ⟨q, hq, G, hGm, hPG, hG⟩ :=
    exists_stripPocketEvent_perQ (P := P) h𝓦 hnull hRm hLm hβm hηm hηc hηH hη0 hR hβ hL hnohit hlate
  obtain ⟨G₁, hG₁m, hG₁ae, hG₁⟩ := exists_measurableSet_nullSets_ae (P := P) (hQ q hq)
  refine ⟨q, hq, G ∩ G₁, hGm.inter (hnull q _ hG₁m), ?_, fun ω hω => ?_⟩
  · rwa [measure_inter_conull (ae_iff.1 hG₁ae)]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hG ω hω.1
    exact ⟨h1, h2, h3, h4, h5, hG₁ ω hω.2⟩


end InteractingSLE.Sec7.PocketWordPerQ
