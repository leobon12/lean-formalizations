/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfVer
import InteractingSLE.Spec.Supplement.SB2NfThr
import InteractingSLE.Spec.Supplement.SB2NfRelStmt
import InteractingSLE.Spec.Supplement.SB2CrVer

/-!
# F2b′'s root versions (CONDFIN's `Cr.RootVersionG/S`, D48/D51)

Packet PROVE-AUX61-NOJUMP (round 22, the root variant).

* **`exists_rootStop`**: the root's stop inputs, from the root objects, F3's word, D34's heights clause on the root
  event and the root's relative facts at a sample (`RootRelFactsStatement`, PROVE-T14-SB2LIFT's, D77);
* **`RootStop.ver`** (`Cr.RootVersionG`): the driver frozen at the `m`-th stop, the root clock in B's time (`0` up to
  the entrance), the strict time change, the stop as horizon; **`RootStop.versionS`** (`Cr.RootVersionS`);
* the statement's extra clauses: the clock vanishes up to the entrance (`ae_a_zero`), every B-time before B's
  lifetime is before some stop (`ae_cover`), the stops are below the thresholds (`ae_V_le_thr`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Vr Nd

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

/-- **The root's stop inputs**: the relative facts hold on a measurable conull event, for a `lineC0`-measurable stop
word equal almost surely to F3's word shifted by the entry value; at a finite relative lifetime the relative trace
converges to a bad relative point right of the seed. -/
theorem exists_rootStop (hrel : RootRelFactsStatement.{u}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (S : RootObj P κ b jumps E u l k ℓ) {A₁ : ℝ≥0 → Ω → Set ℂ}
    (hA₁ : ∀ᵐ ω ∂P, A₁ 0 ω = stageFill κ b jumps E u l k ℓ ω) {β₁ : Ω → BoundaryWord}
    (hβ : Measurable[LocalSets.aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] β₁) {types : Set WordType}
    (htypes : types.Countable)
    (hheight : ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ →
      Nb.HeightClause κ b jumps (A₁ 0 ω) ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) (β₁ ω))
    (hcover : ∀ᵐ ω ∂P, ω ∈ S.Eg → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (S.x₀ ω) (β₁ ω)) ∈ types) :
    ∃ T : RootStop P κ b jumps E u l k ℓ, T.S = S ∧
      (∀ᵐ ω ∂P, T.cw ω = BoundaryWord.shiftW (S.x₀ ω) (β₁ ω)) ∧ T.types = types ∧
      ∀ ω ∈ S.Eg ∩ T.Gr, capLife (S.ρM ω) ≠ ⊤ → ∃ y : ℝ, 0 < y ∧
        Tendsto (capTrace (S.ρM ω)) (𝓝[<] (capLife (S.ρM ω)).toNNReal) (𝓝 (y : ℂ)) ∧
        Vq.IsBadPoint (cellXL κ (-(Real.pi / 2)) T.cw (angleWordType κ (-(Real.pi / 2)) (T.cw ω)) ω)
          (cellXR κ (-(Real.pi / 2)) T.cw (angleWordType κ (-(Real.pi / 2)) (T.cw ω)) ω)
          (typedRhoL (angleWordType κ (-(Real.pi / 2)) (T.cw ω)))
          (typedRhoR (angleWordType κ (-(Real.pi / 2)) (T.cw ω))) (y : ℂ) := by
  classical
  obtain ⟨cw, hcwm, hcwe⟩ := Ne.exists_stopWord hb hE hER hlθ hℓ hwℓ S.hx₀ hβ
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hprog : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hRw : StagedPiecesRegular κ b jumps P w (StagedReg.regFam E w) :=
    WalkLaw.stagedPiecesRegular_regHist (hER _ hprog)
  have hPR : ∀ᵐ ω ∂P, (ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      GW1P.PieceRegular (StagedReg.regFam E w ℓ ω).1 (StagedReg.regFam E w ℓ ω).2 := by
    filter_upwards [GW1W.regLaunches_of_stagedPiecesRegular hRw] with ω hRLω hl
    exact pieceRegular_of_launch hRLω hl
  set Q : Ω → Prop := fun ω => ω ∈ S.Eg →
    RelFactsAt κ (-(Real.pi / 2)) cw types (S.ρM ω) ω ∧
      (capLife (S.ρM ω) ≠ ⊤ → ∃ y : ℝ, 0 < y ∧
        Tendsto (capTrace (S.ρM ω)) (𝓝[<] (capLife (S.ρM ω)).toNNReal) (𝓝 (y : ℂ)) ∧
        Vq.IsBadPoint (cellXL κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
          (cellXR κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
          (typedRhoL (angleWordType κ (-(Real.pi / 2)) (cw ω)))
          (typedRhoR (angleWordType κ (-(Real.pi / 2)) (cw ω))) (y : ℂ)) with hQ
  have hQae : ∀ᵐ ω ∂P, Q ω := by
    filter_upwards [hheight, hA₁, hcwe, hcover, hPR, Ne.ae_walk_phys h13₀ hκ hκ4 hb hh hcf hζ' hE hER ℓ,
      ae_walk_end_right h13₀ hκ hκ4 hb hh hcf hζ' hE hER ℓ] with ω hH hA hcwω hcov hPRω hph hend hω
    have hg := S.good₀ ω hω.1
    have G := S.geo hω
    have hlD : (ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [hg.runw (ℓ + 1)]; exact hg.stage.2
    have hRE := pieceRegular_of_launch hg.walk.reg hg.stage.2
    have hLeq := (Ne.pcPt_eq_of_runs hg.runw hlD (hPRω hlD) hRE).1
    have hpos : 0 < (E w ℓ ω).2 := pos_iff_ne_zero.2 hg.pos
    have hzD : 0 < (StagedReg.regFam E w ℓ ω).2 := by
      have : (StagedReg.regFam E w ℓ ω).2 = (E w ℓ ω).2 := hLeq
      rw [this]; exact hpos
    have hHω := hH (S.Eg_subset_rootEv hω)
    rw [hA, hg.stfill] at hHω
    have hr := hrel κ b jumps E u l k ℓ ω hκ hκ4 hb hg.walk hg.stage.2 (S.x₀ ω) G (β₁ ω) hHω cw types hcwω
      (by rw [hcwω]; exact hcov hω) (hPRω hlD) hg.runw (hph hlD hzD) (hend hlD hzD)
    have hρ : S.ρM ω = canonCurve (retX κ b jumps E u l k ℓ ω) (S.x₀ ω) (rPc κ b jumps E u l k ℓ ω)
        (rLife κ b jumps E u l k ℓ ω) := by
      rw [S.ρM_eq hω]; unfold rRel; rw [canonCurve_congr_fill hg.fill]
    rw [hρ]
    exact hr
  set Gr : Set Ω := (toMeasurable P {ω | ¬ Q ω})ᶜ with hGr
  have hGrm : MeasurableSet Gr := (measurableSet_toMeasurable P _).compl
  have hGrae : ∀ᵐ ω ∂P, ω ∈ Gr := by
    have h0 : P (toMeasurable P {ω | ¬ Q ω}) = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hQae
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω using hω
  have hQG : ∀ ω ∈ S.Eg ∩ Gr, Q ω := fun ω hω => by
    by_contra hn
    exact hω.2 (subset_toMeasurable P _ hn)
  exact ⟨⟨hb, S, cw, types, htypes, hcwm, Gr, hGrm, hGrae, fun ω hω => (hQG ω hω hω.1).1⟩, rfl, hcwe, rfl,
    fun ω hω => (hQG ω hω hω.1).2⟩

namespace RootStop

variable (T : RootStop P κ b jumps E u l k ℓ)
  (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
  (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
  (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
  (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
  (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
  {𝓖 : Filtration ℝ≥0 mΩ} (h𝓖 : ∀ t, 𝓖 t = lineSigmaT κ b jumps E u l k ℓ t)
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
  (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
    A₂ t ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω) ω)
  {β : Ω → BoundaryWord} (hβ : ∀ᵐ ω ∂P, T.cw ω = β ω) (types : Set WordType)

include hβ in
/-- **The stop is at most the threshold on the statement word's cells.** -/
theorem ae_V_le_thr (m : ℕ) (w : WordType) : ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ (-(Real.pi / 2)) β T.S.Eg w →
    T.toG.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (T.toG.W m) (cellXL κ (-(Real.pi / 2)) β w)
      (cellXR κ (-(Real.pi / 2)) β w) ω := by
  filter_upwards [T.toG.ae_mem_Gs, hβ] with ω hG hβω hc
  have hw : angleWordType κ (-(Real.pi / 2)) (T.toG.cw ω) = w := by
    show angleWordType κ (-(Real.pi / 2)) (T.cw ω) = w
    rw [hβω]; exact hc.2
  have hL : cellXL κ (-(Real.pi / 2)) T.toG.cw w ω = cellXL κ (-(Real.pi / 2)) β w ω := by
    show cellXL κ (-(Real.pi / 2)) T.cw w ω = _; simp only [cellXL, hβω]
  have hR : cellXR κ (-(Real.pi / 2)) T.toG.cw w ω = cellXR κ (-(Real.pi / 2)) β w ω := by
    show cellXR κ (-(Real.pi / 2)) T.cw w ω = _; simp only [cellXR, hβω]
  rw [← thr_congr _ _ _ hL hR]
  exact T.toG.V_le_thr_of_mem (hG hc.1) hw

include hE hER hlθ hℓ hwℓ h𝓖 hA hβ in
/-- **The `m`-th root version.** -/
def ver (m : ℕ) : Cr.RootVersionG κ (-(Real.pi / 2)) P T.S.Eg 𝓖 A₁ A₂
    (fun ω => Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)) β types (bPc κ b jumps E ℓ)
    (fun ω => (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal) (bLife b jumps E ℓ) where
  𝓗 := tcFiltS (lineFiltC P 𝓖) T.S.a (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖)
  W := T.toG.W m
  a := T.S.a
  Λ := fun _ => T.toG.V m
  marks_le := le_tcFiltS_zero fun t => (lineFiltC P 𝓖).mono (zero_le : (0 : ℝ≥0) ≤ t)
  root_meas := T.measurableSet_root_H0 hE hER hlθ hℓ hwℓ h𝓖
  W_zero := T.toG.W_zero m
  W_cont := T.toG.continuous_W m
  W_adapted := T.stronglyAdapted_W hE hER hlθ hℓ hwℓ h𝓖 m
  clock_cont := T.S.continuous_a
  clock_mono := T.S.monotone_a
  clock_zero := T.S.a_zero
  clock_meas := T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖
  clock_root := fun _ => Eventually.of_forall fun _ hω => T.S.mem_Eg_of_pos hω
  timeChange := fun q D' hD' t => tcFiltS_inter q D' hD' t
  reach := fun _ _ q => by
    filter_upwards [T.toG.ae_mem_Gs] with ω hG hc hq using T.reach_of_mem (hG hc.1.1) hq
  reg := fun w _ => by
    filter_upwards [T.ae_V_le_thr hβ m w] with ω hle hc using isForceReg_mono
      (Vh.reg_of_continuous (T.toG.W_zero m) (T.toG.continuous_W m) _ _ _ _ ω) (hle hc.1)
  safeS := fun _ _ _ t => T.measurableSet_safe_stop hE hER hlθ hℓ hwℓ h𝓖 m (isClosed_tsupport _) t
  safeL := fun _ _ Fb t => T.measurableSet_safe_stop hE hER hlθ hℓ hwℓ h𝓖 m
    (Set.Finite.isClosed_biUnion Fb.finite_toSet fun _ _ => isClosed_closedBall) t
  hull := fun _ _ t => by
    filter_upwards [T.toG.ae_mem_Gs, hA t] with ω hG hAω hc hlt using T.hull_of_mem (hG hc.1.1) hlt hAω.1 hAω.2
  trace := fun _ _ t => by
    filter_upwards [T.toG.ae_mem_Gs] with ω hG hc hlt using T.trace_of_mem (hG hc.1.1) hlt
  alive := fun _ _ t => by
    filter_upwards [T.toG.ae_mem_Gs] with ω hG hc hlt using T.lt_life_of_lt (hG hc.1.1) hlt
  Λ_le := fun w _ => by
    filter_upwards [T.ae_V_le_thr hβ m w] with ω hle hc using hle hc.1

include hE hER hlθ hℓ hwℓ h𝓖 hA hβ in
/-- **The root's versions at announced stops.** -/
def versionS : Cr.RootVersionS κ (-(Real.pi / 2)) P T.S.Eg 𝓖 A₁ A₂
    (fun ω => Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)) β types (bPc κ b jumps E ℓ)
    (fun ω => (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal) (bLife b jumps E ℓ) (fun ω => capLife (T.S.ρM ω)) where
  ver := T.ver hE hER hlθ hℓ hwℓ h𝓖 hA hβ types
  V := T.toG.V
  record := T.toG.record
  record_meas := fun _ => T.measurable_record_H0 hE hER hlθ hℓ hwℓ h𝓖
  ρ := stopRule
  ρs := annRules gaugeRead
  ρ_meas := measurable_stopRule
  ρ_rule := isPathRule_stopRule
  ρs_meas := measurable_annRules measurable_gaugeRead
  ρs_rule := isPathRule_annRules isCausal_gaugeRead
  ρs_fin := annRules_ne_top gaugeRead
  ρs_mono := monotone_annRules gaugeRead
  Λ_eq := fun _ _ => rfl
  V_eq := fun _ _ => rfl
  ann := fun _ => by
    filter_upwards [T.toG.ae_mem_Gs] with ω hG hF using T.toG.ann_of_mem (hG hF)
  V_lt := fun m => by
    filter_upwards [T.toG.ae_mem_Gs] with ω hG hF
    rw [T.toG.V_eq (hG hF)]
    exact T.toG.Vstop_lt (hG hF)
  V_mono := T.toG.V_mono
  V_sup := by
    filter_upwards [T.toG.ae_mem_Gs] with ω hG hF using T.toG.V_sup (hG hF)
  W_eq := fun m m' hmm' => by
    filter_upwards [T.toG.ae_mem_Gs] with ω hG hF t ht using T.toG.W_eq hmm' (hG hF) ht

/-- **The clock vanishes up to the entrance.** -/
theorem ae_a_zero (t : ℝ≥0) : ∀ᵐ ω ∂P, ω ∈ T.S.Eg → (t : ℝ≥0∞) ≤ Nd.entrR κ b jumps E u l k ℓ ω →
    T.S.a t ω = 0 := by
  refine Eventually.of_forall fun ω hω ht => T.S.a_eq_zero_of_le t ?_
  have hfin : Nd.entrR κ b jumps E u l k ℓ ω ≠ ⊤ := (T.S.entr_lt hω).ne_top
  unfold rSh
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
  exact ht

/-- **Every B-time before B's lifetime is before some stop.** -/
theorem ae_cover (t : ℝ≥0) : ∀ᵐ ω ∂P, ω ∈ T.S.Eg → (t : ℝ≥0∞) < bLife b jumps E ℓ ω →
    ∃ m, T.S.a t ω < T.toG.V m ω := by
  filter_upwards [T.toG.ae_mem_Gs] with ω hG hF ht
  have h1 := T.a_lt_capLife_of_lt hF ht
  rw [show capLife (T.S.ρM ω) = capLife (T.toG.ρ ω) from rfl, ← T.toG.V_sup (hG hF)] at h1
  exact lt_iSup_iff.1 h1

end RootStop

end InteractingSLE.Theorem14.SB.Nf
