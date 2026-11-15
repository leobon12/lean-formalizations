/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeFacts

/-!
# F2b′'s relative facts on the good event, and the stop inputs

Packet PROVE-AUX61-NOJUMP (round 22, component F).

* **`relFacts_of_good`** (one sample): on the good event of `Nc.StageObj`, D34's clause, the stop word, the cover and
  the physical facts of the regularized walk give `Nd.RelFactsAt`;
* **`exists_stopIn`**: F2b′'s stop inputs `Nd.StopIn` (the relative facts on a measurable conull event).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Ne

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM Exist Exist.Staged Exist.StagedLaw Dv Nc Nd Vs Vr Lv Supp8.Q3Stop
  GW1W Restart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

/-- **F2b′'s relative facts at a good sample.** -/
theorem relFacts_of_good (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hg : StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) {A : Set ℂ} (hA : A = fillH (retX κ b jumps E u l k ℓ ω))
    {β : BoundaryWord} (hH : Nb.HeightClause κ b jumps A (Nb.bSeed κ b jumps E ℓ ω) β)
    {cw : Ω → BoundaryWord} {types : Set WordType} (hcw : cw ω = BoundaryWord.shiftW (x₀ ω) β)
    (htype : angleWordType κ (-(Real.pi / 2)) (cw ω) ∈ types)
    (hRD : GW1P.PieceRegular (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).1
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)
    (hphys : stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) =
        stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) ∧
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) ∉
        closure (origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ))) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        ∀ x : ℝ, pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) t = x →
          stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) < x →
          x ∉ closure (origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)))) ∧
      ((StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≠ ⊤ →
        ∃ x : ℝ, pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2.toNNReal = x ∧
          x ∈ origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)))) :
    RelFactsAt κ (-(Real.pi / 2)) cw types (bRel κ b jumps E ℓ K x₀ ω) ω ∧
      (capLife (bRel κ b jumps E ℓ K x₀ ω) ≠ ⊤ → ∃ y : ℝ, 0 < y ∧
        Tendsto (capTrace (bRel κ b jumps E ℓ K x₀ ω)) (𝓝[<] (capLife (bRel κ b jumps E ℓ K x₀ ω)).toNNReal)
          (𝓝 (y : ℂ)) ∧
        Vq.IsBadPoint (cellXL κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
          (cellXR κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
          (typedRhoL (angleWordType κ (-(Real.pi / 2)) (cw ω)))
          (typedRhoR (angleWordType κ (-(Real.pi / 2)) (cw ω))) (y : ℂ)) := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => StagedReg.regFam E w j ω with hD
  set D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => E w j ω with hD'
  set X := retX κ b jumps E u l k ℓ ω with hX
  have hl := hg.stage.2
  have hlD : (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hg.runw (ℓ + 1)]; exact hl
  have hRE : GW1P.PieceRegular (D' ℓ).1 (D' ℓ).2 := pieceRegular_of_launch hg.walk.reg hl
  obtain ⟨hLeq, hpeq⟩ := pcPt_eq_of_runs hg.runw hlD hRD hRE
  have hrun := hg.runw ℓ
  obtain ⟨hpt, hRnot, hav, hend⟩ := hphys
  -- the seed point
  have hev := even_of_launch hl
  have hRmax : realMax X = stPt (ExplState.run κ b jumps w D' ℓ) := realMax_retX_eq hg.walk hl hg.off hev
  have hRrec : stRecR (ExplState.run κ b jumps w D ℓ) = realMax X := by
    rw [hRmax, ← hrun, hpt]
  rw [hRrec] at hRnot hav hend
  -- the extension of the inverse chart
  obtain ⟨pX, hpXc, hpX0, hpXH, hpXv, hpXe⟩ := exists_path_retX hg.walk hl
  obtain ⟨e₀, g, -, hgc, hgi, hgt, -, -⟩ := Dv.exists_canon_package_pinv hpXc hpX0 hpXH hpXv
  rw [hpXe] at hgi hgt
  obtain ⟨C, hC⟩ := Lk.hullChart_ext_bounded hg.hull hgt
  have hfree : ∀ x : ℝ, realMax X < x → ∃ r > 0, Disjoint (ball (x : ℂ) r) (fillH X) := fun x hx =>
    ball_disjoint_fillH_right hg.retc fun y hy => lt_of_le_of_lt (Lx.le_realMax_of_mem hg.retc hy) hx
  -- D34's clause through `g`
  have hseed : Nb.bSeed κ b jumps E ℓ ω = ((realMax X : ℝ) : ℂ) := by
    rw [hRmax]; exact pcPt_zero_launch hg.walk.reg hg.walk.chain hl hg.pos
  obtain ⟨e, he, hreal, hmono, ⟨Fy, hFy⟩, hleft⟩ := hH g hgc (by rw [hA]; exact hgi)
  rw [hseed] at he
  have hxe : x₀ ω = e := entry_eq hg.hull hgc hgi hg.entry hfree he hreal hmono
  rw [← hxe] at he hreal hmono hFy hleft
  -- the physical facts for B's own piece
  have hpc := continuousOn_bPc hg
  have hav' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < bLife b jumps E ℓ ω → ∀ x : ℝ, bPc κ b jumps E ℓ ω t = x →
      realMax X < x → x ∉ closure (origBadR κ b (realMax X)) := fun t ht x hx hRx =>
    hav t (by rw [hLeq]; exact ht) x (by rw [hpeq t (by rw [hLeq]; exact ht.le)]; exact hx) hRx
  have hend' : bLife b jumps E ℓ ω ≠ ⊤ → ∃ x : ℝ, bPc κ b jumps E ℓ ω (bLife b jumps E ℓ ω).toNNReal = x ∧
      x ∈ origBadR κ b (realMax X) := fun htop => by
    obtain ⟨x, hx, hxb⟩ := hend (by rw [hLeq]; exact htop)
    refine ⟨x, ?_, hxb⟩
    have hle : (((D ℓ).2.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (D ℓ).2 := ENNReal.coe_toNNReal_le_self
    have hLe : bLife b jumps E ℓ ω = (D ℓ).2 := hLeq.symm
    rw [hLe, show bPc κ b jumps E ℓ ω ((D ℓ).2.toNNReal) =
      pcPt (ExplState.run κ b jumps w D' ℓ) (D' ℓ) ((D ℓ).2.toNNReal) from rfl, ← hpeq _ hle]
    exact hx
  have hdr : IsDrivenCurve (canonCurve X (x₀ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω)) := by
    rw [← bRel_eq_retX hg]; exact hg.driven
  have hcap : bLife b jumps E ℓ ω = ⊤ → capLife (canonCurve X (x₀ ω) (bPc κ b jumps E ℓ ω)
      (bLife b jumps E ℓ ω)) = ⊤ := fun htop => by
    rw [← bRel_eq_retX hg]; exact capLife_top_of_good hg htop
  have hcell : ω ∈ wordTypeCell κ (-(Real.pi / 2)) cw univ (angleWordType κ (-(Real.pi / 2)) (cw ω)) :=
    ⟨trivial, rfl⟩
  have hft0 := Restart.FCDet.isFlowType_of_mem_typeSet (mem_typeSet_of_mem_wordTypeCell hcell)
  have hft : Restart.FCDet.IsFlowType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) β)
      (cellXL κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
      (cellXR κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
      (typedRhoL (angleWordType κ (-(Real.pi / 2)) (cw ω))) (typedRhoR (angleWordType κ (-(Real.pi / 2)) (cw ω))) := by
    rw [← hcw]; exact hft0
  rw [bRel_eq_retX hg]
  exact ⟨relFactsAt_of hκ hb hg.hull hg.pos hpc hdr hgc hgi hC he hreal hmono hFy hleft hfree hRnot hav' hend' hcap
    hcw htype, fun hfin => endpoint_bad hκ hb hg.hull hg.pos hpc hdr hgc hgi hC he hreal hmono hFy hft hfree hend'
    hcap hfin⟩


section Stop

variable {Ω' : Type u} [mΩ : MeasurableSpace Ω'] [StandardBorelSpace Ω'] {P : Measure Ω'} [IsProbabilityMeasure P]
  {h : Ω' → LQGMetric.DistOn upperHalfPlaneOpens} {E' : ExplSpec → ℕ → Ω' → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **F2b′'s stop inputs**: the relative facts hold on a measurable conull event, for a `lineC0`-measurable stop word
equal almost surely to F3's word shifted by the entry value. -/
theorem exists_stopIn (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω' → ℝ} {ζ' : Ω' → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E' spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E' spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (S : StageObj P κ b jumps E' u l k ℓ) {A₁ : ℝ≥0 → Ω' → Set ℂ}
    (hA₁ : ∀ᵐ ω ∂P, A₁ 0 ω = stageFill κ b jumps E' u l k ℓ ω) {β₁ : Ω' → BoundaryWord}
    (hβ : Measurable[LocalSets.aeSigma (Ms.stageMarks κ b jumps E' u l k ℓ) P] β₁) {types : Set WordType}
    (htypes : types.Countable)
    (hheight : ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E' u l k ℓ →
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E' u l k ω))
        (fun i => E' (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E' (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      Nb.HeightClause κ b jumps (A₁ 0 ω) (Nb.bSeed κ b jumps E' ℓ ω) (β₁ ω))
    (hcover : ∀ᵐ ω ∂P, ω ∈ S.F → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (S.x₀ ω) (β₁ ω)) ∈ types) :
    ∃ T : StopIn P κ b jumps E' u l k ℓ (-(Real.pi / 2)), T.S = S ∧
      (∀ᵐ ω ∂P, T.cw ω = BoundaryWord.shiftW (S.x₀ ω) (β₁ ω)) ∧
      ∀ ω ∈ S.Eg ∩ T.Gr, capLife (S.ρM ω) ≠ ⊤ → ∃ y : ℝ, 0 < y ∧
        Tendsto (capTrace (S.ρM ω)) (𝓝[<] (capLife (S.ρM ω)).toNNReal) (𝓝 (y : ℂ)) ∧
        Vq.IsBadPoint (cellXL κ (-(Real.pi / 2)) T.cw (angleWordType κ (-(Real.pi / 2)) (T.cw ω)) ω)
          (cellXR κ (-(Real.pi / 2)) T.cw (angleWordType κ (-(Real.pi / 2)) (T.cw ω)) ω)
          (typedRhoL (angleWordType κ (-(Real.pi / 2)) (T.cw ω)))
          (typedRhoR (angleWordType κ (-(Real.pi / 2)) (T.cw ω))) (y : ℂ) := by
  classical
  obtain ⟨cw, hcwm, hcwe⟩ := exists_stopWord hb hE hER hlθ hℓ hwℓ S.hx₀ hβ
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hprog : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hRw : StagedPiecesRegular κ b jumps P w (StagedReg.regFam E' w) :=
    WalkLaw.stagedPiecesRegular_regHist (hER _ hprog)
  have hPR : ∀ᵐ ω ∂P, (ExplState.run κ b jumps w (fun j => StagedReg.regFam E' w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      GW1P.PieceRegular (StagedReg.regFam E' w ℓ ω).1 (StagedReg.regFam E' w ℓ ω).2 := by
    filter_upwards [regLaunches_of_stagedPiecesRegular hRw] with ω hRLω hl
    exact pieceRegular_of_launch hRLω hl
  set Q : Ω' → Prop := fun ω => ω ∈ S.Eg →
    RelFactsAt κ (-(Real.pi / 2)) cw types (S.ρM ω) ω ∧
      (capLife (S.ρM ω) ≠ ⊤ → ∃ y : ℝ, 0 < y ∧
        Tendsto (capTrace (S.ρM ω)) (𝓝[<] (capLife (S.ρM ω)).toNNReal) (𝓝 (y : ℂ)) ∧
        Vq.IsBadPoint (cellXL κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
          (cellXR κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
          (typedRhoL (angleWordType κ (-(Real.pi / 2)) (cw ω)))
          (typedRhoR (angleWordType κ (-(Real.pi / 2)) (cw ω))) (y : ℂ)) with hQ
  have hQae : ∀ᵐ ω ∂P, Q ω := by
    filter_upwards [hheight, hA₁, hcwe, hcover, hPR, ae_walk_phys h13₀ hκ hκ4 hb hh hcf hζ' hE hER ℓ]
      with ω hH hA hcwω hcov hPRω hph hω
    have hg := S.good ω hω
    have hlD : (ExplState.run κ b jumps w (fun j => StagedReg.regFam E' w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [hg.runw (ℓ + 1)]; exact hg.stage.2
    have hRE := pieceRegular_of_launch hg.walk.reg hg.stage.2
    have hLeq := (pcPt_eq_of_runs hg.runw hlD (hPRω hlD) hRE).1
    have hpos : 0 < (E' w ℓ ω).2 := pos_iff_ne_zero.2 hg.pos
    have hzD : 0 < (StagedReg.regFam E' w ℓ ω).2 := by
      have : (StagedReg.regFam E' w ℓ ω).2 = (E' w ℓ ω).2 := hLeq
      rw [this]; exact hpos
    have hrel := relFacts_of_good hκ hb hg (hA.trans hg.stfill) (hH hg.stage hg.off hpos) hcwω
      (by rw [hcwω]; exact hcov (S.hEgF hω)) (hPRω hlD) (hph hlD hzD)
    rw [S.ρM_eq hω]
    exact hrel
  set Gr : Set Ω' := (toMeasurable P {ω | ¬ Q ω})ᶜ with hGr
  have hGrm : MeasurableSet Gr := (measurableSet_toMeasurable P _).compl
  have hGrae : ∀ᵐ ω ∂P, ω ∈ Gr := by
    have h0 : P (toMeasurable P {ω | ¬ Q ω}) = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hQae
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω using hω
  have hQG : ∀ ω ∈ S.Eg ∩ Gr, Q ω := fun ω hω => by
    by_contra hn
    exact hω.2 (subset_toMeasurable P _ hn)
  exact ⟨⟨hb, S, cw, types, htypes, hcwm, Gr, hGrm, hGrae, fun ω hω => (hQG ω hω hω.1).1⟩, rfl, hcwe,
    fun ω hω => (hQG ω hω hω.1).2⟩

end Stop

end InteractingSLE.Theorem14.SB.Ne
