/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfIntegrable

/-!
# The threshold obligation in GW2's relative safe law

Packet PROVE-GW2-SAFE. The two caps in `IsGW2RelVersion` together place every
relative time below the version stop before the actual end `min(ζα, T_c)`.
The threshold criterion below is exact and permits admissible collisions.
It does not prove the physical boundary correspondence needed to establish that
criterion for the relative word. In particular, no global admissibility of that
word is assumed or asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv GW2Rd GW2TipSystem
  Sec7.PocketTraversal Restart.FCDet Supp8.Q3Stop

/-- Both caps of a GW2 version hold simultaneously in physical time. -/
theorem ae_cofinal_gw2End_of_version {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ θ : ℝ} (hκ : 0 < κ)
    {h : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGW2RelVersion s P W Wα ζ ζα γ α R V) :
    ∀ᵐ ω ∂P, γ ω s ∈ H → ∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω →
      ∃ t : ℝ≥0, (t : ℝ≥0∞) < gw2End s ζα γ α ω ∧ (u : ℝ) < gw2Clock s W Wα ω t := by
  obtain ⟨⟨⟨⟨-, -, -, -, -, -, hlive⟩, -⟩, -⟩, hcap⟩ := hver
  filter_upwards [hlive, hcap, hζ, ae_extTr_spec hκ hfl hα s] with ω hl hc hz he hsH
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
  obtain ⟨hV0, ht, -⟩ := hl hs hsH
  obtain ⟨t₀, ht₀, -⟩ := hc hsH 0 hV0
  obtain ⟨-, -, hW, -, htr⟩ := he ((zero_le : (0 : ℝ≥0∞) ≤ t₀).trans_lt ht₀)
  intro u hu
  obtain ⟨t, htc, hut⟩ := ht u hu
  obtain ⟨v, hv, huv⟩ := hc hsH u hu
  have htc' : (t : ℝ≥0∞) < firstContactTime
      (fun r => (extTr s Wα ζα α ω r : OnePoint ℂ))
      ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) := by
    rw [gb6Tc, GW2JDetR4.firstContactTime_sphereInv] at htc
    exact htc
  obtain ⟨q, hqζ, hqc, hqu⟩ : ∃ q : ℝ≥0, (q : ℝ≥0∞) < ζα ω ∧
      (q : ℝ≥0∞) < firstContactTime (fun r => (extTr s Wα ζα α ω r : OnePoint ℂ))
        ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) ∧
      ((u : ℝ) < gb6Clock s (regW s Wα ζα) W ω q ∨ (u : ℝ) < gw2Clock s W Wα ω q) := by
    by_cases htζ : (t : ℝ≥0∞) < ζα ω
    · exact ⟨t, htζ, htc', Or.inl hut⟩
    · have hvt : (v : ℝ≥0∞) < t := hv.trans_le (le_of_not_gt htζ)
      exact ⟨v, hv, hvt.trans htc', Or.inr huv⟩
  obtain ⟨q₂, hqq₂, hq₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqζ
  have hqq₂' : q < q₂ := ENNReal.coe_lt_coe.1 hqq₂
  have hactual : (q : ℝ≥0∞) < firstContactTime (fun r => (α ω r : OnePoint ℂ))
      ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) :=
    GW2Fb.lt_firstContactTime_of_prefix hqq₂' (fun r hr =>
      congrArg (fun z : ℂ => (z : OnePoint ℂ))
        (htr r ((ENNReal.coe_le_coe.2 hr).trans hq₂ζ.le)).symm) hqc
  refine ⟨q, lt_min hqζ hactual, ?_⟩
  rcases hqu with hqu | hqu
  · have hclock := (hull_clock_contact_of_ext (w := fun t => W t ω) hW htr hqζ hactual).2.1
    simpa only [gb6Clock, gw2Clock, hclock] using hqu
  · exact hqu

/-- For geometric marks the threshold bound is exactly the absence of a
nonadmissible colliding group at every earlier time. -/
theorem le_thr_iff_no_threshold {Ω : Type*} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W t ω)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (V : Ω → ℝ≥0∞) (ω : Ω) :
    V ω ≤ thr ρL ρR W xL xR ω ↔
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω →
        ¬ ForceWord.ThresholdCondition ρL ρR (W t ω)
          (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω) := by
  constructor
  · intro h t ht
    exact MartChar.notMem_thresholdSet_of_lt (ht.trans_le h)
  · intro h
    by_contra hn
    have hlt : thr ρL ρR W xL xR ω < V ω := lt_of_not_ge hn
    have hfin : thr ρL ρR W xL xR ω ≠ ⊤ := ne_top_of_lt hlt
    have heq := ENNReal.coe_toNNReal hfin
    have hmem := MartChar.thresholdTime_mem_thresholdSet (hWc ω)
      (fun i => (isForcePath_geomLW hWc xL ω i).1)
      (fun j => (isForcePath_geomRW hWc xR ω j).1)
      (fun i j s t hst hij => geomLW_merge hWc xL ω i j s t hst hij)
      (fun i j s t hst hij => geomRW_merge hWc xR ω i j s t hst hij) heq.symm
    exact h _ (heq ▸ hlt) hmem

/-- Conditional threshold transfer for GW2. The hypothesis `hgroups` is the
remaining physical boundary correspondence, not a proved input: before the
physical end, no complete colliding group of the relative word has mass at most
`-2`. Admissible mergers are allowed. This lemma does not establish the safe law. -/
theorem ae_canonStp_le_thr_gw2_of_precontact_groups
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) {h h' Hc : Ω → DistOn upperHalfPlaneOpens}
    {b b' : ℝ → ℝ} {J J' : Finset ℝ} {W Wα : ℝ≥0 → Ω → ℝ}
    {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0) (hHcm : Measurable Hc) (c' : BoundaryWord)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGW2RelVersion s P W Wα ζ ζα γ α R V) (w : WordType)
    (hgroups : ∀ᵐ ω ∂P, γ ω s ∈ H → wordType κ (gw2Word κ θ c' (gb6Rec s W ζ ω)) = w →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < gw2End s ζα γ α ω →
        ∀ u : ℝ≥0, (u : ℝ) < gw2Clock s W Wα ω t →
          ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) (R u ω)
            (fun i => geomLW R (fun ω => typedXL κ w (gw2Word κ θ c' (gb6Rec s W ζ ω))) i u ω)
            (fun j => geomRW R (fun ω => typedXR κ w (gw2Word κ θ c' (gb6Rec s W ζ ω))) j u ω)) :
    ∀ᵐ y ∂((P.map fun ω => (gb6Rec s W ζ ω,
        relVar (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω)) R V ω))[|
          typeEvent κ w (gw2Word κ θ c') (gb6TS s)]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv
        (fun y => typedXL κ w (gw2Word κ θ c' y.1))
        (fun y => typedXR κ w (gw2Word κ θ c' y.1)) y := by
  have hcofinal := ae_cofinal_gw2End_of_version hκ hfl hα hζ s hver
  obtain ⟨⟨⟨⟨hRm, hRc, hR0, -, hVm, -, -⟩, -⟩, -⟩, -⟩ := hver
  have hrec : Measurable (gb6Rec s W ζ) := (measurable_recOf_cfE hcf s).2
  have hraised : Measurable fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω) :=
    (Exist.measurable_flowField 0 _).comp hHcm
  have hΦ := hrec.prodMk (measurable_relVar hraised hRm hVm)
  have hβ := measurable_gw2Word κ θ c'
  have hxL : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXL κ w (gw2Word κ θ c' y.1) :=
    (((measurable_typedXL κ w).comp hβ).comp measurable_fst_canonRec).mono
      (canonRec_le_canonFilt 0) le_rfl
  have hxR : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXR κ w (gw2Word κ θ c' y.1) :=
    (((measurable_typedXR κ w).comp hβ).comp measurable_fst_canonRec).mono
      (canonRec_le_canonFilt 0) le_rfl
  refine ae_cond_of_ae_comp hΦ (measurableSet_typeEvent hβ (measurableSet_gb6TS s))
    (measurableSet_le measurable_canonStp
      (measurable_thr continuous_canonDrv stronglyAdapted_canonDrv hxL hxR)) ?_
  filter_upwards [hcofinal, hgroups, ae_gb6RecGood hcf hγ s] with ω hc hg hr hm
  have hsH := ((mem_gb6TS_iff hr).2 hm.1).2
  have hbound : V ω ≤ thr (typedRhoL w) (typedRhoR w) R
      (fun ω => typedXL κ w (gw2Word κ θ c' (gb6Rec s W ζ ω)))
      (fun ω => typedXR κ w (gw2Word κ θ c' (gb6Rec s W ζ ω))) ω := by
    refine (le_thr_iff_no_threshold hRc _ _ V ω).2 fun u hu => ?_
    obtain ⟨t, ht, hut⟩ := hc hsH u hu
    exact hg hsH hm.2 t ht u hut
  have hd : ∀ t, canonDrv t (gb6Rec s W ζ ω,
      relVar (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω)) R V ω) = R t ω :=
    fun t => relDrv_relVar (hRc ω) (hR0 ω) t
  rw [thr_congr (W := R)
    (xL := fun ω => typedXL κ w (gw2Word κ θ c' (gb6Rec s W ζ ω)))
    (xR := fun ω => typedXR κ w (gw2Word κ θ c' (gb6Rec s W ζ ω))) hd rfl rfl]
  exact hbound

end InteractingSLE.Theorem14.GW2Sf
