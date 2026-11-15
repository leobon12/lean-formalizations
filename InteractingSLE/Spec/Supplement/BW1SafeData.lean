/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeRead
import InteractingSLE.Spec.Supplement.BW1SafeStmt

/-!
# BW1's good event and the versions in R-form

Packet PROVE-BW1-SAFELAW. In BW1's setting (with Theorem 1.3 for the traces), for a measurable record event `TS` of
the threshold event:

* **`exists_bw1_safe_data`**: a measurable continuous version `Wd` of the counterflow driver (almost surely equal to
  it at every time) and a measurable good event `GT ⊆ rec⁻¹ TS` containing almost all of `rec⁻¹ TS`, on which every
  sample is good (`BGood`), the counterflow driver is `Wd` and BW1's contact time is the first contact `bTc`
  (`BW1Ver.bw1_sample`, the proof of `BW1Ver.exists_bw1_data`);
* **`isBVer_of_version`**: every index of a version with hull identities (`IsBW1RelVersion`, `IsBW1VersionHulls`) is
  a version in R-form for `Wd` and `GT` (`IsBVer`);
* `measurableSet_goodSet_physFilt'`: the good event is an event of every physical σ-algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Safe

open Exist Exist.StagedLaw Exist.Staged Restart BW1Life Supp8.GB6 Supp8.GB6.ReadD Supp8.RelSafe
  Sec7.PocketTraversal BW1Ver

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **BW1's good event and the physical driver version.** -/
theorem exists_bw1_safe_data (h13 : Exist.Theorem13Statement.{u})
    (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) {r : Bool} {TS : Set RecData} (hTS : MeasurableSet TS)
    (hFTS : ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔ bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS) :
    ∃ (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω), (∀ s, Measurable (Wd s)) ∧ (∀ ω, Continuous (Wd · ω)) ∧
      (∀ ω, Wd 0 ω = 0) ∧ (∀ᵐ ω ∂P, ∀ s, Wd s ω = W' s ω) ∧ MeasurableSet GT ∧
      (∀ᵐ ω ∂P, bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS → ω ∈ GT) ∧
      ∀ ω ∈ GT, bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS ∧
        BGood (bwRec κ b jumps (bwSpec gw2 θ t rest) E) Wd ω ∧ (∀ s, W' s ω = Wd s ω) ∧
        bwContact κ b jumps (bwSpec gw2 θ t rest) W' E ω = bTc (bwRec κ b jumps (bwSpec gw2 θ t rest) E) Wd ω := by
  classical
  obtain ⟨hκ, hκ4, hb, hh, hcfW, hζ', -, hS⟩ := hset
  have hrec : Measurable (bwRec κ b jumps (bwSpec gw2 θ t rest) E) :=
    measurable_pastMap_one_last hb (StagedReg.measurable_regHist hS.1) fun j ω =>
      StagedReg.isRegularDriver_regHist j ω
  have hpiece := BW1Prop.ae_bw1_piece_hyps h13 hκ hκ4 hb hh hS
  have hW'tr := Sec7.StripSysPath.IsCenteredCounterflowDriver.ae_hasTrace h13 hκ hcfW
  obtain ⟨_, _, _, -, -, hflW⟩ := hcfW
  have hW'reg := ae_driver_zero_continuousOn hflW
  obtain ⟨_, 𝓕, _, _, _, _, hC⟩ := hflW
  have hcreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous (W' · ω) := by
    filter_upwards [hW'reg, hζ'] with ω hr hz
    refine ⟨hz, hr.1, continuousOn_univ.1 (hr.2.mono fun s _ => ?_)⟩
    rw [mem_ofPred_eq, hz]
    exact ENNReal.coe_lt_top
  obtain ⟨Wd, hWdm, hWdc, hWd0, hWdW⟩ := SourceC.exists_top_driver_version hC.1.2.1 hcreg
  have hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (Wd · ω) ⊤ (phTr Wd ω) ∧
      Tendsto (fun s => ‖phTr Wd ω s‖) atTop atTop := by
    filter_upwards [hW'tr, hWdW, hζ'] with ω htr hw hz
    obtain ⟨η, hη, hη'⟩ := htr
    rw [hz] at hη hη'
    have he : (Wd · ω) = (W' · ω) := funext hw
    have hηd : IsGeneratingTrace (Wd · ω) ⊤ η := he ▸ hη
    have hph : phTr Wd ω = η := funext fun v =>
      LP.traceAt_eq_of_isGeneratingTrace hηd (hWdc ω).continuousOn (hWd0 ω) ENNReal.coe_lt_top
    rw [hph]
    exact ⟨hηd, hη' rfl⟩
  let Good : Ω → Prop := fun ω => bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS →
    ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ∧ GW1P.PieceRegular (E 0 ω).1 (min t (E 0 ω).2) ∧
      (∀ α : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 (E 0 ω).2 α → ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < (E 0 ω).2 →
        α v ≠ 0) ∧
      (∀ s, W' s ω = Wd s ω) ∧ IsGeneratingTrace (Wd · ω) ⊤ (phTr Wd ω) ∧
        Tendsto (fun s => ‖phTr Wd ω s‖) atTop atTop
  have hGood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hFTS, hpiece, hWdW, hγ] with ω hF hp hw hg hT
    exact ⟨hF.2 hT, hp.1, hp.2, fun s => (hw s).symm, hg.1, hg.2⟩
  obtain ⟨G, hGm, hGae, hG⟩ := SourceC.exists_measurable_good hGood
  refine ⟨Wd, G ∩ bwRec κ b jumps (bwSpec gw2 θ t rest) E ⁻¹' TS, hWdm, hWdc, hWd0, hWdW, hGm.inter (hrec hTS),
    ?_, fun ω hω => ?_⟩
  · filter_upwards [hGae] with ω hω hT
    exact ⟨hω, hT⟩
  · obtain ⟨hF, hP, hNR, hw, hgen, htr⟩ := hG ω hω.1 hω.2
    have hW'e : (fun s => W' s ω) = (Wd · ω) := funext hw
    obtain ⟨hg, -, -, hct⟩ := bw1_sample (D := fun j => E j ω) hF hP hNR (hWdc ω) (hWd0 ω) hgen htr
    have hrecω : bwRec κ b jumps (bwSpec gw2 θ t rest) E ω = recOf t (StagedReg.regularize t (E 0 ω)) :=
      BW1In.bwRec_eq_recOf ω
    refine ⟨hω.2, ?_, hw, ?_⟩
    · show IsGoodSample (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)
        (fun v => recordTrace v (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) (Wd · ω) (phTr Wd ω)
      rw [hrecω]
      exact hg
    · unfold bwContact bTc
      rw [hW'e, hrecω]
      exact hct

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The good event is an event of every physical σ-algebra. -/
theorem measurableSet_goodSet_physFilt' {rec : Ω → RecData} (hrec : Measurable rec) {Wd : ℝ≥0 → Ω → ℝ}
    (hWm : ∀ r, Measurable (Wd r)) {GT : Set Ω} {TS : Set RecData} (hTS : MeasurableSet TS) (hGm : MeasurableSet GT)
    (hGsub : ∀ ω ∈ GT, rec ω ∈ TS) (hGae : ∀ᵐ ω ∂P, rec ω ∈ TS → ω ∈ GT) (s : ℝ≥0) :
    MeasurableSet[physFilt hrec hWm P s] GT := by
  refine measurableSet_of_ae_eq ((physFilt hrec hWm P).le s) (nullSets_le_physFilt hrec hWm P s) hGm
    (physSigma_le_physFilt hrec hWm P s _ (measurable_rec_physSigma _ Wd s hTS)) ?_
  filter_upwards [hGae] with ω hω
  exact propext ⟨fun h => hGsub ω h, fun h => hω h⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **A version with hull identities is, index by index, a version in R-form** for the physical driver version
`Wd` and the good event `GT`. -/
theorem isBVer_of_version {rec : Ω → RecData} {F : Set Ω} {c : Ω → Chart} {T : Ω → ℝ≥0∞}
    {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hver : IsBW1RelVersion P rec F c W' T R V ℓ) (hhull : IsBW1VersionHulls P rec F W' T R V)
    {Wd : ℝ≥0 → Ω → ℝ} {GT : Set Ω} (hGF : ∀ᵐ ω ∂P, ω ∈ GT → ω ∈ F)
    (hGW : ∀ ω ∈ GT, (∀ s, W' s ω = Wd s ω) ∧ T ω = bTc rec Wd ω) (m : ℕ) :
    IsBVer P rec Wd GT (R m) (V m) := by
  obtain ⟨hRm, hRc, hR0, hfr, hVm, -, hrule, hae⟩ := hver
  obtain ⟨ρ, -, hρm, hρ, hVρ, -⟩ := hrule m
  refine ⟨hRm m, hRc m, hR0 m, hfr m, hVm m, ⟨ρ, hρm, hρ, hVρ⟩, ?_⟩
  filter_upwards [hae, hhull m, hGF] with ω h1 h2 hG hωG
  have hωF := hG hωG
  obtain ⟨hW, hT⟩ := hGW ω hωG
  have hW'e : (fun u => W' u ω) = (Wd · ω) := funext hW
  obtain ⟨hrange, hK⟩ := h2 hωF
  rw [hT, hW'e] at hrange hK
  exact ⟨(h1 hωF).1 m, hrange, hK⟩

end InteractingSLE.Theorem14.BW1Safe
