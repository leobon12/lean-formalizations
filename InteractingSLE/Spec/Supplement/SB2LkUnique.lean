/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.HullDetGenBR4a
import InteractingSLE.Spec.Supplement.GW2JDetCode
import InteractingSLE.Spec.Supplement.SBTail2RetainFreeze
import InteractingSLE.Spec.Supplement.WalkUnionLawMain
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Sec5.Lemma56Stages
import InteractingSLE.Spec.Supplement.GW2aContStepAux

/-!
# Uniqueness of staged histories of one field

Packet PROVE-T14-SB2LIFT (a library piece also for PROVE-T14-SB2DRV). Theorem 1.2 (determination) in the forms
needed to compare two candidate histories of the same field:

* **`ae_eq_of_isFlowLineDriver`**: two flow-line drivers of the same field at the same angle (with any two
  piecewise-constant representatives of its boundary data) have almost surely the same lifetime and agree before it
  (both are the decoded canonical driver code of the field, `GW2JDet.ae_flowLineDriver_eq_drvDec_theta`);
* `canonDrv_eq_of_agree`: two drivers with the same lifetime, agreeing before it, starting at `0` and continuous up to
  the stop, have the same retained datum;
* **`ae_pastMap_eq_of_isStagedHistory_reg`**, **`ae_run_eq_of_isStagedHistory`**: two regular staged histories of one
  field and one program run almost surely through the same states (induction over the instructions: the retained pasts
  agree, so the conditional laws agree, so the next launched pieces agree conditionally almost surely);
  `ae_physSet_eq_of_isStagedHistory`; the forms from Theorems 1.2–1.3 (`…_of_thm12_thm13`).

R48: Theorems 1.2–1.3 appear only as hypotheses (these results serve Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Restart

/-! ### Two flow-line drivers of one field -/

/-- **Two flow-line drivers of one field agree** (Theorem 1.2 through the canonical driver code): almost surely they
have the same lifetime and agree before it. The two boundary-data representatives may differ on a finite set. -/
theorem ae_eq_of_isFlowLineDriver (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) {κ θ : ℝ} (hκ : 0 < κ)
    {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} (hb₁ : IsPiecewiseConstantBoundaryData b₁ J₁)
    (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂) {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Ω → DistOn upperHalfPlaneOpens} {W₁ W₂ : ℝ≥0 → Ω → ℝ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (h₁ : IsFlowLineDriver κ b₁ J₁ θ Q X W₁ ζ₁) (h₂ : IsFlowLineDriver κ b₂ J₂ θ Q X W₂ ζ₂) :
    ∀ᵐ ω ∂Q, ζ₁ ω = ζ₂ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₁ ω → W₁ t ω = W₂ t ω := by
  have hX₁ := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb₁ h₁
  have hX₂ := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb₂ h₂
  have heq := eq_of_isGFFWithBoundaryData hb₁ hb₂ hX₁ hX₂
  have h₂' : IsFlowLineDriver κ b₁ J₁ θ Q X W₂ ζ₂ :=
    (isFlowLineDriver_congr_of_eqOn hb₁ hb₂ (J₁ ∪ J₂) fun y hy => (heq y hy).symm).1 h₂
  obtain ⟨c, hc, hcJ, hcb⟩ := Supp8.HullDetGen.exists_sorted_fn_eq hb₁
  have hc₁ := Supp8.HullDetGen.isFlowLineDriver_word hcJ hcb h₁
  have hc₂ := Supp8.HullDetGen.isFlowLineDriver_word hcJ hcb h₂'
  have hXc := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ
    (BoundaryWord.isPiecewiseConstantBoundaryData c) hc₁
  obtain ⟨F, hF⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ κ θ hκ
  filter_upwards [GW2JDet.ae_flowLineDriver_eq_drvDec_theta h12p h13 h12p₀ h13₀ hκ hF hc hXc hc₁,
    GW2JDet.ae_flowLineDriver_eq_drvDec_theta h12p h13 h12p₀ h13₀ hκ hF hc hXc hc₂] with ω h1 h2
  refine ⟨h1.1.trans h2.1.symm, fun t ht => ?_⟩
  have ht' : (t : ℝ≥0∞) < ζ₂ ω := by rw [h2.1, ← h1.1]; exact ht
  rw [h1.2 t ht, h2.2 t ht']

/-! ### Retained data of agreeing drivers -/

/-- **Two drivers with the same lifetime, agreeing before it, have the same retained datum** when both start at `0`
and are continuous up to the stop `min t ζ`. -/
theorem canonDrv_eq_of_agree {t : ℝ≥0∞} {D D' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h2 : D.2 = D'.2)
    (h1 : ∀ s : ℝ≥0, (s : ℝ≥0∞) < D.2 → D.1 s = D'.1 s) (h0 : D.1 0 = 0) (h0' : D'.1 0 = 0)
    (hc : ContinuousOn D.1 {s | (s : ℝ≥0∞) ≤ min t D.2})
    (hc' : ContinuousOn D'.1 {s | (s : ℝ≥0∞) ≤ min t D'.2}) : canonDrv t D = canonDrv t D' := by
  obtain ⟨W, ζ⟩ := D
  obtain ⟨W', ζ'⟩ := D'
  simp only at h2 h1 h0 h0' hc hc'
  subst h2
  unfold canonDrv
  refine Prod.ext (funext fun r => ?_) rfl
  simp only
  set s : ℝ≥0 := (min (r : ℝ≥0∞) (min t ζ)).toNNReal with hs
  have hne : min (r : ℝ≥0∞) (min t ζ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hsc : (s : ℝ≥0∞) = min (r : ℝ≥0∞) (min t ζ) := ENNReal.coe_toNNReal hne
  rcases lt_or_ge (s : ℝ≥0∞) ζ with hlt | hge
  · exact h1 s hlt
  · -- the stop is the lifetime itself: both drivers take their common left limit there
    have hsζ : (s : ℝ≥0∞) = ζ := le_antisymm (hsc ▸ (min_le_right _ _).trans (min_le_right _ _)) hge
    have hsS : (s : ℝ≥0∞) ≤ min t ζ := hsc ▸ min_le_right _ _
    rcases eq_or_ne s 0 with hs0 | hs0
    · rw [hs0, h0, h0']
    · have hpos : 0 < s := pos_iff_ne_zero.2 hs0
      have hmem : s ∈ {x : ℝ≥0 | (x : ℝ≥0∞) ≤ min t ζ} := hsS
      have hw : ContinuousWithinAt W (Iic s) s := (hc s hmem).mono fun x (hx : x ≤ s) =>
        (ENNReal.coe_le_coe.2 hx).trans hsS
      have hw' : ContinuousWithinAt W' (Iic s) s := (hc' s hmem).mono fun x (hx : x ≤ s) =>
        (ENNReal.coe_le_coe.2 hx).trans hsS
      have hagree : W =ᶠ[𝓝[<] s] W' := by
        filter_upwards [self_mem_nhdsWithin] with x (hx : x < s)
        exact h1 x (hsζ ▸ ENNReal.coe_lt_coe.2 hx)
      have hl : Tendsto W' (𝓝[<] s) (𝓝 (W s)) :=
        ((hw.mono Iio_subset_Iic_self).tendsto).congr' hagree
      exact (StagedReg.eq_of_tendsto_nhdsLT hpos hw' hl).symm

/-! ### Two staged histories of one field -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The retained past is measurable for the ambient σ-algebra. -/
theorem measurable_pastMap_of_isStagedHistory {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E) (n : ℕ) :
    Measurable (pastMap κ b jumps spec E n) :=
  measurable_iff_comap_le.2 (hE.2.1 n)

/-- **The induction step**: if the retained pasts of two regular staged histories of one field agree almost surely
before instruction `n`, they agree almost surely before `n + 1`. Under the common conditional law given the past, the
two histories launch the same piece in the same chart (or none), and the launched pieces are flow-line drivers of the
same conditional field, hence agree (`ae_eq_of_isFlowLineDriver`); the retained data then agree
(`canonDrv_eq_of_agree`), and the measurable event of agreement holds almost surely by the tower property. -/
theorem ae_pastMap_succ_eq (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω))
    (hE' : IsStagedHistory κ b jumps P h spec E') (hR' : StagedPiecesRegular κ b jumps P spec E')
    (hreg' : ∀ k ω, IsRegularDriver (E' k ω)) {n : ℕ}
    (hn : ∀ᵐ ω ∂P, pastMap κ b jumps spec E n ω = pastMap κ b jumps spec E' n ω) :
    ∀ᵐ ω ∂P, pastMap κ b jumps spec E (n + 1) ω = pastMap κ b jumps spec E' (n + 1) ω := by
  have hm𝒢 : pastSigma κ b jumps spec E n ≤ mΩ := hE.2.1 n
  have hmE := measurable_pastMap_of_isStagedHistory hE (n + 1)
  have hmE' := measurable_pastMap_of_isStagedHistory hE' (n + 1)
  set G : Set Ω := {ω | pastMap κ b jumps spec E (n + 1) ω (Fin.last n) =
    pastMap κ b jumps spec E' (n + 1) ω (Fin.last n)} with hGdef
  have hG : MeasurableSet G :=
    measurableSet_eq_fun ((measurable_pi_apply _).comp hmE) ((measurable_pi_apply _).comp hmE')
  have hGof : ∀ ω, ExplState.run κ b jumps spec (fun j => E j ω) (n + 1) =
      ExplState.run κ b jumps spec (fun j => E' j ω) (n + 1) → ω ∈ G := fun ω hω => by
    show pastMap κ b jumps spec E (n + 1) ω (Fin.last n) = pastMap κ b jumps spec E' (n + 1) ω (Fin.last n)
    unfold pastMap; rw [hω]
  have hK := StagedReg.ae_condExpKernel_eq_of_ae_eq (measurable_pastMap_of_isStagedHistory hE n)
    (measurable_pastMap_of_isStagedHistory hE' n) hn
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel hm𝒢 hG ?_
    filter_upwards [hn, hK, hE.2.2.2 n, hE'.2.2.2 n, Retain.ae_ae_run_eq spec hR hm𝒢 le_rfl,
      Retain.ae_ae_run_eq spec hR' (hE'.2.1 n) le_rfl,
      KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hR.ae_pieceRegular,
      KernelTower.ae_ae_condExpKernel_of_ae (hE'.2.1 n) hR'.ae_pieceRegular, hR.ae_pieceRegular]
      with ω₀ hn₀ hK₀ hst₀ hst₀' hrun₀ hrun₀' hpr₀ hpr₀' hreg₀
    have hK₀' : condExpKernel P (pastSigma κ b jumps spec E' n) ω₀ =
        condExpKernel P (pastSigma κ b jumps spec E n) ω₀ := hK₀.symm
    rw [hK₀'] at hrun₀' hpr₀'
    have hrun : ExplState.run κ b jumps spec (fun j => E j ω₀) n = ExplState.run κ b jumps spec (fun j => E' j ω₀) n :=
      run_eq_of_readRec_eq spec (fun j _ => hreg j ω₀) (fun j _ => hreg' j ω₀) fun i hi => congrFun hn₀ ⟨i, hi⟩
    rcases hL : (ExplState.run κ b jumps spec (fun j => E j ω₀) (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · filter_upwards [hrun₀, hrun₀'] with ω hω hω'
      have hrω := hω.trans (hrun.trans hω'.symm)
      have hLω : (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n = none := by
        rw [launches_run_succ_of_run_eq spec hω, hL]
      exact hGof ω (run_succ_eq_of_noLaunch spec hrω hLω)
    · have hL' : (ExplState.run κ b jumps spec (fun j => E' j ω₀) (n + 1)).2.2.2.1 n = some (c, θ) := by
        rw [← launches_run_succ_of_run_eq spec hrun, hL]
      obtain ⟨b₁, J₁, h₁, hb₁, hT₁, hfl₁⟩ := hst₀ c θ hL
      obtain ⟨b₂, J₂, h₂, hb₂, hT₂, hfl₂⟩ := hst₀' c θ hL'
      have hc : c = (ExplState.run κ b jumps spec (fun j => E j ω₀) n).2.2.2.2.1 :=
        (eq_launch_of_launches spec _ hL).2.2
      have hcc : c.IsConformal := by
        rw [hc]
        exact (GW2aCont.isConformal_runChart spec (fun j => E j ω₀) n fun j _ c' θ' hl' => hreg₀ j c' θ' hl').1
      have hh : h₂ = h₁ := funext fun ω => (hT₂ ω).unique hcc (hT₁ ω)
      subst hh
      have hfl₂' := hK₀' ▸ hfl₂
      filter_upwards [ae_eq_of_isFlowLineDriver h12p h13 h12p₀ h13₀ hκ hb₁ hb₂ hfl₁ hfl₂', hrun₀, hrun₀', hpr₀,
        hpr₀'] with ω hdrv hω hω' hprω hprω'
      have hrω := hω.trans (hrun.trans hω'.symm)
      have hLω : (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n = some (c, θ) := by
        rw [launches_run_succ_of_run_eq spec hω, hL]
      have hLω' : (ExplState.run κ b jumps spec (fun j => E' j ω) (n + 1)).2.2.2.1 n = some (c, θ) := by
        rw [launches_run_succ_of_run_eq spec hω', hL']
      obtain ⟨-, he, -⟩ := eq_launch_of_launches spec (fun j => E j ω) hLω
      obtain ⟨-, he', -⟩ := eq_launch_of_launches spec (fun j => E' j ω) hLω'
      obtain ⟨h0, hc0, -⟩ := hprω n c θ hLω
      obtain ⟨h0', hc0', -⟩ := hprω' n c θ hLω'
      have hcan : canonDrv (instrTime spec n) (E n ω) = canonDrv (instrTime spec n) (E' n ω) :=
        canonDrv_eq_of_agree hdrv.1 hdrv.2 h0 h0' hc0 hc0'
      refine hGof ω ?_
      rw [he, he', hrω, ← launch_canonDrv _ _ (E n ω), hcan, launch_canonDrv]
  filter_upwards [hn, hGae] with ω hnω hGω
  rw [pastMap_succ spec E n ω, pastMap_succ spec E' n ω, hnω]
  congr 1

/-- **Two staged histories of one field, regular at every sample, have almost surely the same retained past** before
every instruction. -/
theorem ae_pastMap_eq_of_isStagedHistory_reg (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω))
    (hE' : IsStagedHistory κ b jumps P h spec E') (hR' : StagedPiecesRegular κ b jumps P spec E')
    (hreg' : ∀ k ω, IsRegularDriver (E' k ω)) :
    ∀ n, ∀ᵐ ω ∂P, pastMap κ b jumps spec E n ω = pastMap κ b jumps spec E' n ω
  | 0 => Eventually.of_forall fun _ => funext fun i => i.elim0
  | n + 1 => ae_pastMap_succ_eq h12p h13 h12p₀ h13₀ hκ hE hR hreg hE' hR' hreg'
      (ae_pastMap_eq_of_isStagedHistory_reg h12p h13 h12p₀ h13₀ hκ hE hR hreg hE' hR' hreg' n)

/-- **Uniqueness of staged histories** (Theorem 1.2, piece by piece): two regular staged histories of one field and
one program run almost surely through the same states. Both are regularized (`StagedReg.regHist`, same runs almost
surely), and the regularized histories have almost surely equal retained pasts. -/
theorem ae_run_eq_of_isStagedHistory (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) (hR : StagedPiecesRegular κ b jumps P spec E)
    (hE' : IsStagedHistory κ b jumps P h spec E') (hR' : StagedPiecesRegular κ b jumps P spec E') :
    ∀ᵐ ω ∂P, ∀ k, ExplState.run κ b jumps spec (fun j => E j ω) k =
      ExplState.run κ b jumps spec (fun j => E' j ω) k := by
  have hp := ae_pastMap_eq_of_isStagedHistory_reg h12p h13 h12p₀ h13₀ hκ
    (StagedReg.isStagedHistory_regHist hb hE hR) (WalkLaw.stagedPiecesRegular_regHist hR)
    (StagedReg.isRegularDriver_regHist (spec := spec) (E := E))
    (StagedReg.isStagedHistory_regHist hb hE' hR') (WalkLaw.stagedPiecesRegular_regHist hR')
    (StagedReg.isRegularDriver_regHist (spec := spec) (E := E'))
  filter_upwards [ae_all_iff.2 hp, StagedReg.ae_run_regHist hR, StagedReg.ae_run_regHist hR'] with ω hpω h1 h2 k
  rw [← h1 k, ← h2 k]
  exact run_eq_of_readRec_eq spec (fun j _ => StagedReg.isRegularDriver_regHist j ω)
    (fun j _ => StagedReg.isRegularDriver_regHist j ω) fun i hi => congrFun (hpω k) ⟨i, hi⟩

/-- **Two regular staged histories of one field have almost surely the same physical set.** -/
theorem ae_physSet_eq_of_isStagedHistory (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) (hR : StagedPiecesRegular κ b jumps P spec E)
    (hE' : IsStagedHistory κ b jumps P h spec E') (hR' : StagedPiecesRegular κ b jumps P spec E') :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps spec (fun j => E j ω) =
      ExplState.physSet κ b jumps spec (fun j => E' j ω) := by
  filter_upwards [ae_run_eq_of_isStagedHistory h12p h13 h12p₀ h13₀ hκ hb hE hR hE' hR'] with ω hω
  exact StagedReg.physSet_eq_of_run_eq (hω spec.2.2.length)

/-- `ae_run_eq_of_isStagedHistory` from Theorems 1.2–1.3 (both universes). -/
theorem ae_run_eq_of_isStagedHistory_of_thm12_thm13 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) (hR : StagedPiecesRegular κ b jumps P spec E)
    (hE' : IsStagedHistory κ b jumps P h spec E') (hR' : StagedPiecesRegular κ b jumps P spec E') :
    ∀ᵐ ω ∂P, ∀ k, ExplState.run κ b jumps spec (fun j => E j ω) k =
      ExplState.run κ b jumps spec (fun j => E' j ω) k :=
  ae_run_eq_of_isStagedHistory (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
    (Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hκ hb hE hR hE' hR'

/-- `ae_eq_of_isFlowLineDriver` from Theorems 1.2–1.3 (both universes). -/
theorem ae_eq_of_isFlowLineDriver_of_thm12_thm13 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ θ : ℝ} (hκ : 0 < κ)
    {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} (hb₁ : IsPiecewiseConstantBoundaryData b₁ J₁)
    (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂) {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Ω → DistOn upperHalfPlaneOpens} {W₁ W₂ : ℝ≥0 → Ω → ℝ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (h₁ : IsFlowLineDriver κ b₁ J₁ θ Q X W₁ ζ₁) (h₂ : IsFlowLineDriver κ b₂ J₂ θ Q X W₂ ζ₂) :
    ∀ᵐ ω ∂Q, ζ₁ ω = ζ₂ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₁ ω → W₁ t ω = W₂ t ω :=
  ae_eq_of_isFlowLineDriver (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
    (Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hκ hb₁ hb₂ h₁ h₂

/-- `ae_physSet_eq_of_isStagedHistory` from Theorems 1.2–1.3 (both universes). -/
theorem ae_physSet_eq_of_isStagedHistory_of_thm12_thm13 (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) (hR : StagedPiecesRegular κ b jumps P spec E)
    (hE' : IsStagedHistory κ b jumps P h spec E') (hR' : StagedPiecesRegular κ b jumps P spec E') :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps spec (fun j => E j ω) =
      ExplState.physSet κ b jumps spec (fun j => E' j ω) :=
  ae_physSet_eq_of_isStagedHistory (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
    (Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hκ hb hE hR hE' hR'

end InteractingSLE.Theorem14.SB.Lk
