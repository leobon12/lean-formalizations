/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvStage
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.SB2VfCmpl

/-!
# SB2(2)'s v6 measurability, almost surely: item (A) closed

Packet PROVE-GW2-GEOM2, round 10 (D28, item (A)). The actual family `E (boundaryWalkSpec b jumps (−π/2) true)` of
the SB2(2) setting is regular only at its launched instructions, almost surely. Its regularization
(`StagedReg.regHist`), redefined off a measurable conull set to be a fixed good sample, is measurable, regular, and has
regular launches at every sample (`exists_regular_version`). Almost surely it **agrees** with the actual family
(`AgreeAt`: same runs, lifetimes, launched traces). With LIFTSET's launch at `relOff` off a zero root
(`sb2LowerLaunchRelOff`), this gives:

* **`SB2LowerAdmV6Statement`**, PROVED (`sb2LowerAdmV6`): for each launch there is a measurable kernel-conull event
  `GA` such that for every measurable `Gd ⊆ GA`, every stage `j` and every relative family measurable and regular
  before `j`, drivenness of the v4 curve on the v6 mask gives `StageOK` of the v6 rule. These are the three
  measurability conjuncts of the v6 admissibility clause.
* **`SB2LowerGeomRestV6Statement`**: LIFTSET's remaining v6 input. Inside any measurable conull event there is a
  measurable `Gd` with:
  - drivenness on the mask for every admissible family;
  - `GeomAt4` and `Mn.StageFactsAS` for every admissible family.
* **`sb2LowerGeomFactsV6Statement_of_rest`**: the two give `SB2LowerGeomFactsV6Statement`;
  **`sb2LowerRelDriverStatementTR_of_rest`**: with SB2LIFT's item 4, D23's strengthened target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C LuM GW1W GW1Bookkeep FlowDilate

/-! ### Regular launches survive the regularization -/

/-- `PieceRegular` only sees the driver on `[0, S]`. -/
theorem pieceRegular_congr {W W' : ℝ≥0 → ℝ} {S : ℝ≥0∞} (h : GW1P.PieceRegular W S)
    (hww : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ S → W' s = W s) : GW1P.PieceRegular W' S := by
  obtain ⟨h0, hc, α, hα, htr⟩ := h
  refine ⟨by rw [hww 0 (by simp)]; exact h0, hc.congr fun s hs => hww s hs, α,
    Sec5.CrossRestart.isGeneratingTrace_congr_drive hα fun t ht => hww t ht.le, htr⟩

/-- **The regularized family has regular launches** when the family has, along the same runs. -/
theorem regLaunches_regularize {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {spec : ExplSpec} {D : ℕ → Drv}
    (hP : RegLaunches κ b J spec D)
    (hrun : ∀ n, ExplState.run κ b J spec (fun k => StagedReg.regularize (instrTime spec k) (D k)) n =
      ExplState.run κ b J spec D n) :
    RegLaunches κ b J spec fun k => StagedReg.regularize (instrTime spec k) (D k) := by
  intro k c θ' hl
  rw [hrun (k + 1)] at hl
  have h := hP k c θ' hl
  rw [StagedReg.regularize_snd]
  exact pieceRegular_congr h fun s hs => StagedReg.regularize_eq_of_le h.1 h.2.1 hs

/-- **A regularized family agrees with a family with regular launches along the same runs.** -/
theorem agreeAt_regularize {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → Drv}
    (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D)
    (hrun : ∀ n, ExplState.run κ b J (boundaryWalkSpec b J θ true)
      (fun k => StagedReg.regularize (instrTime (boundaryWalkSpec b J θ true) k) (D k)) n =
        ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) :
    AgreeAt κ θ b J D fun k => StagedReg.regularize (instrTime (boundaryWalkSpec b J θ true) k) (D k) := by
  refine ⟨fun n => (hrun n).symm, fun n => (StagedReg.regularize_snd _ _).symm, fun n hl => ?_⟩
  have hPR := pieceRegular_of_launch hP hl
  refine trOf_congr (StagedReg.regularize_snd _ _).symm fun t ht => ?_
  exact (StagedReg.regularize_eq_of_lt _ hPR.1
    (hPR.2.1.mono fun s (hs : (s : ℝ≥0∞) < (D n).2) => show (s : ℝ≥0∞) ≤ (D n).2 from le_of_lt hs) ht).symm

/-! ### A regular version of the actual family -/

/-- **A measurable version of a family, regular with regular launches at every sample**, equal to its regularization
on a measurable conull event. -/
theorem exists_regular_version {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {E : ℕ → Ω → Drv} (hEm : ∀ k, Measurable (E k))
    (hR : StagedPiecesRegular κ b J P (boundaryWalkSpec b J θ true) E) :
    ∃ (Ê : ℕ → Ω → Drv) (G : Set Ω), (∀ k, Measurable (Ê k)) ∧ (∀ k ω, IsRegularDriver (Ê k ω)) ∧
      (∀ ω, RegLaunches κ b J (boundaryWalkSpec b J θ true) fun k => Ê k ω) ∧ MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, AgreeAt κ θ b J (fun k => E k ω) fun k => Ê k ω := by
  classical
  set spec := boundaryWalkSpec b J θ true with hspec
  set Et := StagedReg.regHist spec E with hEt
  have hgood : ∀ᵐ ω ∂P, RegLaunches κ b J spec (fun k => E k ω) ∧
      ∀ n, ExplState.run κ b J spec (fun k => Et k ω) n = ExplState.run κ b J spec (fun k => E k ω) n :=
    (regLaunches_of_stagedPiecesRegular hR).and (StagedReg.ae_run_regHist hR)
  obtain ⟨G, hGm, hGn, hG⟩ := Vf.exists_measurable_conull hgood
  have hGne : G.Nonempty := by
    by_contra hE
    rw [not_nonempty_iff_eq_empty] at hE
    rw [hE, compl_empty, measure_univ] at hGn
    exact one_ne_zero hGn
  obtain ⟨ω₁, hω₁⟩ := hGne
  refine ⟨fun k ω => if ω ∈ G then Et k ω else Et k ω₁, G, fun k => ?_, fun k ω => ?_, fun ω => ?_, hGm, hGn,
    fun ω hω => ?_⟩
  · exact Measurable.ite hGm (StagedReg.measurable_regHist hEm k) measurable_const
  · by_cases h : ω ∈ G
    · simp only [h, ↓reduceIte]; exact StagedReg.isRegularDriver_regHist k ω
    · simp only [h, ↓reduceIte]; exact StagedReg.isRegularDriver_regHist k ω₁
  · by_cases h : ω ∈ G
    · simp only [h, ↓reduceIte]
      exact regLaunches_regularize (hG ω h).1 (hG ω h).2
    · simp only [h, ↓reduceIte]
      exact regLaunches_regularize (hG ω₁ hω₁).1 (hG ω₁ hω₁).2
  · simp only [hω, ↓reduceIte]
    exact agreeAt_regularize (hG ω hω).1 (hG ω hω).2

/-! ### Item (A) at the launch -/

open Supp9B Lx Lu Leaf Sec4 GW1P in
/-- **The measurability conjuncts of the v6 admissibility clause at a launch**: a measurable kernel-conull event `GA`
such that for every measurable `Gd ⊆ GA`, drivenness on the mask gives `StageOK` of the v6 rule. -/
def AdmV6At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, ∃ GA : Set Ω, MeasurableSet GA ∧
    condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀ GAᶜ = 0 ∧
    ∀ Gd : Set Ω, MeasurableSet Gd → Gd ⊆ GA → ∀ (j : ℕ) (F : ℕ → Ω → Drv),
      (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ ω ∈ lMask κ b jumps E u l k ω₀ c b' J' m Gd j F, IsDrivenCurve (lρ3 κ b jumps E u l k ω₀ c b' J' m j F ω)) →
      StageOK (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd j F) (lMask κ b jumps E u l k ω₀ c b' J' m Gd j F)
        (mZ Gd (lZ4 κ b jumps E u l k ω₀) j F)

/-- **Item (A): the measurability conjuncts of SB2(2)'s v6 admissibility clause.** -/
def SB2LowerAdmV6Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ => AdmV6At κ b jumps P E u l k ω₀ c b' J'

open Supp9B Lx Lu Leaf Sec4 GW1P in
/-- **Item (A) PROVED** (Theorems 1.2–1.3, through LIFTSET's launch at `relOff`). -/
theorem sb2LowerAdmV6 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) : SB2LowerAdmV6Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hs₁ := GW1X.isBoundaryContinuedProgram_walkR b jumps
  obtain ⟨Ê, G, hÊm, hÊreg, hÊP, hGm, hGn, hAg⟩ := exists_regular_version (θ := -(Real.pi / 2))
    (hE _ hs₁).1 (hER _ hs₁)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]; exact hGn
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hGae,
    sb2LowerLaunchRelOff h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hG₀ hL₀ hU₀
  intro c θ hlaunch b' J' h' hb' hT' hG' m
  have hcc := (hU₀ c θ hlaunch b' J' h' hb' hT' hG').1
  have hb₂ := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  obtain ⟨GA, hGAm, hGAn, hGA⟩ := Vf.exists_measurable_conull (hG₀.and (hL₀ c θ hlaunch b' J' h' hb' hT' hG'))
  refine ⟨GA, hGAm, hGAn, fun Gd hGdm hGdA j F hFm hFr hdrv => ?_⟩
  -- the actual family and its regular version agree on `Gd`
  have hAgd : ∀ ω ∈ Gd, AgreeAt κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω) (Dh Ê ω) :=
    fun ω hω => hAg ω (hGA ω (hGdA hω)).1
  have hGd₁ : ∀ ω ∈ Gd, ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
      (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
        (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
          (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none :=
    fun ω hω => (hGA ω (hGdA hω)).2
  have hGdh : ∀ ω ∈ Gd, ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (fun i => Ê i ω) →
      (wRun κ (-(Real.pi / 2)) b jumps (fun i => Ê i ω)
        (rO κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) Ê ω + 1)).2.2.2.1
          (rO κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) Ê ω) ≠ none := by
    intro ω hω hz
    have hA := hAgd ω hω
    have hz₁ : ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) :=
      fun h' => hz ((zeroRoot_congr hA.1).1 h')
    have h1 := hGd₁ ω hω hz₁
    have hr := relOff_eq_of_agree (R := lR κ b jumps E u l k ω₀) hA
    simp only [wRun] at h1 ⊢
    rw [hr, hA.1] at h1
    exact h1
  have hM := maskEv_eq_of_agree (b₂ := affData 1 m b') (J₂ := affJumps 1 m J') (c := c) (m := m) hAgd hGd₁ j F
  refine stageOK_of_agree hAgd hGd₁ (stageOK_dh hb hb₂ hcc hÊm hÊreg hÊP hGdm hGdh hFm hFr fun ω hω => ?_)
  have hω₁ : ω ∈ maskEv κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c
      m (lD₁ b jumps E) Gd j F := by
    rw [hM]; exact hω
  rw [← cρ3_eq_of_mask hAgd hGd₁ hω₁]
  exact hdrv ω hω₁

/-! ### LIFTSET's remaining v6 input and the assembly -/

open Supp9B Lx Lu Leaf Sec4 GW1P in
/-- **LIFTSET's remaining v6 input at a launch**: inside every measurable kernel-conull event, a measurable `Gd` on
which the v4 curves are driven on the v6 mask for every admissible family, and every admissible family has the
per-stage facts. -/
def GeomRestV6At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ G₀ : Set Ω, MeasurableSet G₀ →
    condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀ G₀ᶜ = 0 →
    ∃ Gd : Set Ω, MeasurableSet Gd ∧ Gd ⊆ G₀ ∧
    (∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ mZ Gd (lZ4 κ b jumps E u l k ω₀) i F, F i ω = Lk.zeroDrv) →
      (∀ i < j, ∀ ω ∈ lMask κ b jumps E u l k ω₀ c b' J' m Gd i F,
        (F i ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω))) →
      ∀ ω ∈ lMask κ b jumps E u l k ω₀ c b' J' m Gd j F, IsDrivenCurve (lρ3 κ b jumps E u l k ω₀ c b' J' m j F ω)) ∧
    ∀ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ mZ Gd (lZ4 κ b jumps E u l k ω₀) j EL, EL j ω = Lk.zeroDrv) →
      (∀ j, ∀ ω ∈ lMask κ b jumps E u l k ω₀ c b' J' m Gd j EL,
        (EL j ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt4 κ b jumps P E u l k ω₀ c b' J' m (fun j ω _ => ω ∈ lMask κ b jumps E u l k ω₀ c b' J' m Gd j EL) EL ∧
        Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL

/-- **LIFTSET's remaining v6 input** (drivenness on the mask, `GeomAt4`, `StageFactsAS`). -/
def SB2LowerGeomRestV6Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → GeomRestV6At κ b jumps P E u l k ω₀ c b' J'

/-- **The v6 half from item (A) and LIFTSET's remaining input** (Theorems 1.2–1.3). -/
theorem sb2LowerGeomFactsV6Statement_of_rest (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hR : SB2LowerGeomRestV6Statement.{u}) :
    SB2LowerGeomFactsV6Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAdmV6 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hR₀ hA₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨GA, hGAm, hGAn, hA⟩ := hA₀ c θ hlaunch b' J' h' hb' hT' hG' m
  obtain ⟨Gd, hGdm, hsub, hdrv, hfacts⟩ := hR₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm GA hGAm hGAn
  exact ⟨Gd, hGdm, fun j F h1 h2 h3 h4 => hA Gd hGdm hsub j F h1 h2 (hdrv j F h1 h2 h3 h4), hfacts⟩

/-- **D23's strengthened target from item (A), LIFTSET's remaining v6 input and SB2LIFT's item 4.** -/
theorem sb2LowerRelDriverStatementTR_of_rest (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hR : SB2LowerGeomRestV6Statement.{u})
    (hC : SB2LowerClauseOfLiftsV5Statement.{u}) : SB2LowerRelDriverStatementTR.{u} :=
  sb2LowerRelDriverStatementTR_of_v6 h12 h13 h12₀ h13₀ (sb2LowerGeomFactsV6Statement_of_rest h12 h13 h12₀ h13₀ hR) hC

end InteractingSLE.Theorem14.SB.Nv
