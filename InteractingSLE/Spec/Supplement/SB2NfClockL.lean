/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfRho
import InteractingSLE.Spec.Supplement.SB2NdClockL

/-!
# F2b′'s root clock is adapted to the completed line filtration

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). **`RootObj.measurable_a_line`**: the root's relative clock
`S.a t` is measurable for `mΩ ⊓ aeSigma (lineSigmaT t) P`. It is measurable (`RootObj.measurable_a`) and frozen under
the conditional laws given `lineSigmaT t`:

* the B-time-0 good event, the hull, the offset, the capped runs and the cap event are frozen (as at the tails,
  `Nd.ae_ae_frozenData`);
* B's entrance at `R` before `t` is frozen: `{rootTime ≤ r}` is an event of the completed capped past at `r ≤ t`
  (PROVE-SB2-CONDFIN's `Cn.measurableSet_aeSigma_rootTime_le`), so the entrance agrees when it is before `t`
  (`entr_eq_of_rat`);
* the clock at `t` vanishes if the entrance is not before `t`, and otherwise only sees B's piece on `[0, min t ζ]`
  (`piece_eq_of_frozen₀`, `Nc.clockOf_canonVal_congr` after `clockOf_shift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf WalkSide LocalSets Sec7.PocketTraversal Lk LuM Nc Dv Nd

theorem coe_toNNRat_eq_ofReal {q : ℚ} (hq0 : 0 ≤ q) : ((q.toNNRat : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  have h : ((q.toNNRat : ℚ) : ℝ) = (q : ℝ) := by rw [Rat.coe_toNNRat q hq0]
  rw [← h]
  norm_cast

/-- **Two times with the same rational events before `t`** agree when one is before `t`. -/
theorem entr_eq_of_rat {τ τ₀ : ℝ≥0∞} {t : ℝ≥0}
    (h : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t → (τ ≤ ((q : ℝ≥0) : ℝ≥0∞) ↔ τ₀ ≤ ((q : ℝ≥0) : ℝ≥0∞))) :
    (τ < t ↔ τ₀ < t) ∧ (τ₀ < t → τ = τ₀) := by
  have key : ∀ {a c : ℝ≥0∞}, (∀ q : ℚ≥0, (q : ℝ≥0) ≤ t → (a ≤ ((q : ℝ≥0) : ℝ≥0∞) → c ≤ ((q : ℝ≥0) : ℝ≥0∞))) →
      ∀ d : ℝ≥0∞, d ≤ t → a < d → c < d := by
    intro a c hac d hd had
    obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 had
    have hq1' : a < ((q.toNNRat : ℝ≥0) : ℝ≥0∞) := by rw [coe_toNNRat_eq_ofReal hq0]; exact hq1
    have hq2' : ((q.toNNRat : ℝ≥0) : ℝ≥0∞) < d := by rw [coe_toNNRat_eq_ofReal hq0]; exact hq2
    have hqt : (q.toNNRat : ℝ≥0) ≤ t := ENNReal.coe_le_coe.1 (hq2'.le.trans hd)
    exact lt_of_le_of_lt (hac q.toNNRat hqt hq1'.le) hq2'
  have h1 : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t → (τ ≤ ((q : ℝ≥0) : ℝ≥0∞) → τ₀ ≤ ((q : ℝ≥0) : ℝ≥0∞)) :=
    fun q hq => (h q hq).1
  have h2 : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t → (τ₀ ≤ ((q : ℝ≥0) : ℝ≥0∞) → τ ≤ ((q : ℝ≥0) : ℝ≥0∞)) :=
    fun q hq => (h q hq).2
  refine ⟨⟨key h1 t le_rfl, key h2 t le_rfl⟩, fun hτ₀ => ?_⟩
  have hτ : τ < t := key h2 t le_rfl hτ₀
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    exact lt_irrefl _ (key h2 τ hτ.le hlt)
  · by_contra hlt
    rw [not_le] at hlt
    exact lt_irrefl _ (key h1 τ₀ hτ₀.le hlt)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

/-- **Two B-time-0 good samples with the same frozen data at time `t`** (`Nd.piece_eq_of_frozen` for `Root0At`). -/
theorem piece_eq_of_frozen₀ (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω ω₀ : Ω}
    (G : Root0At κ b jumps E u l k ℓ K x₀ Ê ω) (G₀ : Root0At κ b jumps E u l k ℓ K x₀ Ê ω₀) (t : ℝ≥0)
    (e4 : ∀ n, n ≤ ℓ + 1 → ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
        ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) n)
    (e5 : ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ↔
        ω₀ ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t) :
    ((t : ℝ≥0∞) < bLife b jumps E ℓ ω ↔ (t : ℝ≥0∞) < bLife b jumps E ℓ ω₀) ∧
      min (t : ℝ≥0∞) (bLife b jumps E ℓ ω) = min (t : ℝ≥0∞) (bLife b jumps E ℓ ω₀) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ min (t : ℝ≥0∞) (bLife b jumps E ℓ ω) →
        bPc κ b jumps E ℓ ω s = bPc κ b jumps E ℓ ω₀ s := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hwdef
  set Ew := StagedReg.regFam E w with hEwdef
  have hreg : ∀ (ω' : Ω), Root0At κ b jumps E u l k ℓ K x₀ Ê ω' →
      RegLaunches κ b jumps w (fun j => Ew j ω') ∧
      (ExplState.run κ b jumps w (fun j => Ew j ω') (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
      bPc κ b jumps E ℓ ω' = pcPt (ExplState.run κ b jumps w (fun j => Ew j ω') ℓ) (Ew ℓ ω') ∧
      bLife b jumps E ℓ ω' = (Ew ℓ ω').2 := by
    intro ω' G'
    have hP : RegLaunches κ b jumps w (fun j => E w j ω') := G'.walk.reg
    have hrun : ∀ n, ExplState.run κ b jumps w
        (fun j => StagedReg.regularize (instrTime w j) (E w j ω')) n =
        ExplState.run κ b jumps w (fun j => E w j ω') n := G'.runw
    have hag := Nv.agreeAt_regularize (κ := κ) (θ := θ) (b := b) (J := jumps) hP hrun
    refine ⟨Nv.regLaunches_regularize hP hrun, ?_, ?_, (StagedReg.regularize_snd _ _).symm⟩
    · rw [show ExplState.run κ b jumps w (fun j => Ew j ω') (ℓ + 1) = _ from hrun (ℓ + 1)]
      exact G'.stage.2
    · unfold bPc
      rw [Nv.pcPt_congr _ (hag.2.2 ℓ G'.stage.2), hag.1 ℓ]
      rfl
  obtain ⟨hP, hl, hpc, hL⟩ := hreg ω G
  obtain ⟨hP₀, hl₀, hpc₀, hL₀⟩ := hreg ω₀ G₀
  obtain ⟨-, hmin, hpeq⟩ := pcPt_eq_of_capRun_eq (κ := κ) (b := b) (jumps := jumps) (θ := θ) hℓ.le hwℓ hP hP₀ hl
    hl₀ (t : ℝ≥0∞) e4
  refine ⟨?_, by rw [hL, hL₀]; exact hmin, fun s hs => ?_⟩
  · rw [hL, hL₀]
    have : ω ∈ capEvent κ b jumps w Ew ℓ t ↔ ω₀ ∈ capEvent κ b jumps w Ew ℓ t := e5
    simp only [capEvent, mem_ofPred_eq, hl, hl₀, ne_eq, not_false_eq_true, true_and] at this
    exact this
  · rw [hpc, hpc₀]
    exact hpeq s (by rw [← hL]; exact hs)

namespace RootObj

variable (S : RootObj P κ b jumps E u l k ℓ)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem rootTime_eq {ω : Ω} (hω : ω ∈ S.Eg₀) :
    Cm.rootTime κ b jumps E u l k ℓ ω = Nd.entrR κ b jumps E u l k ℓ ω := by
  unfold Cm.rootTime Nd.entrR
  rw [if_pos (S.good₀ ω hω).stage.2]

/-- **The frozen data at time `t`** for the root objects: as at the tails, and B's entrance before `t`. -/
theorem ae_ae_frozen (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (t : ℝ≥0) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (lineSigmaT κ b jumps E u l k ℓ t) ω₀),
      (ω ∈ S.Eg₀ ↔ ω₀ ∈ S.Eg₀) ∧ S.K ω = S.K ω₀ ∧ S.x₀ ω = S.x₀ ω₀ ∧
      (∀ n, n ≤ ℓ + 1 → ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
        ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) n) ∧
      (ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ↔
        ω₀ ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t) ∧
      ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t → (Cm.rootTime κ b jumps E u l k ℓ ω ≤ ((q : ℝ≥0) : ℝ≥0∞) ↔
        Cm.rootTime κ b jumps E u l k ℓ ω₀ ≤ ((q : ℝ≥0) : ℝ≥0∞)) := by
  obtain ⟨-, hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hwdef
  set Ew := StagedReg.regFam E w with hEwdef
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hEwm : ∀ j, Measurable (Ew j) := fun j => StagedReg.measurable_regHist (hE w hw).1 j
  have h𝒢 := lineSigmaT_le (u := u) (k := k) hb hE hER hlθ hℓ hwℓ t
  have hae0 : aeSigma (lineSigma0 κ b jumps E u l k ℓ) P ≤ aeSigma (lineSigmaT κ b jumps E u l k ℓ t) P :=
    WalkLaw.aeSigma_mono (lineSigma0_le_T (u := u) (l := l) (k := k) hb hE hER hℓ hwℓ t)
  have hEgf := ae_ae_mem_iff_of_aeSigma (P := P) h𝒢 (hae0 _ S.hEg₀.2)
  have hKf := ae_ae_eq_of_dyadicHit (P := P) h𝒢 (fun n q => hae0 _ (S.hK n q).2) fun ω => (S.hKc ω).isClosed
  have hxf := ae_ae_eq_of_measurable_aeSigma (P := P) h𝒢 (Z := S.x₀) fun B hB => hae0 _ (S.hx₀ hB).2
  have hrunf := ae_ae_run_eq_of_regular (P := P) (capSpec w ℓ θ (t : ℝ≥0∞)) (hreg' w) (k := ℓ + 1) h𝒢 le_sup_right
  have hcapm : MeasurableSet[lineSigmaT κ b jumps E u l k ℓ t] (capEvent κ b jumps w Ew ℓ t) :=
    le_sup_right (a := pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k) _
      (measurableSet_capEvent hb hEwm (hreg' w) hℓ.le hwℓ t)
  have hcapf := ae_ae_mem_iff (P := P) h𝒢 hcapm
  have hrtf : ∀ q : ℚ≥0, ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (lineSigmaT κ b jumps E u l k ℓ t) ω₀),
      (q : ℝ≥0) ≤ t → (Cm.rootTime κ b jumps E u l k ℓ ω ≤ ((q : ℝ≥0) : ℝ≥0∞) ↔
        Cm.rootTime κ b jumps E u l k ℓ ω₀ ≤ ((q : ℝ≥0) : ℝ≥0∞)) := by
    intro q
    by_cases hqt : (q : ℝ≥0) ≤ t
    · have hm := Cn.measurableSet_aeSigma_rootTime_le (P := P) (k := k) hb (hE _ hsu) (hER _ hsu) (hE w hw)
        (hER w hw) hℓ.le hwℓ (q : ℝ≥0)
      have hm' : MeasurableSet[aeSigma (lineSigmaT κ b jumps E u l k ℓ t) P]
          {ω | Cm.rootTime κ b jumps E u l k ℓ ω ≤ ((q : ℝ≥0) : ℝ≥0∞)} :=
        WalkLaw.aeSigma_mono (Cn.capPast_mono hℓ.le hwℓ hqt) _ hm
      filter_upwards [ae_ae_mem_iff_of_aeSigma (P := P) h𝒢 hm'] with ω₀ h0
      filter_upwards [h0] with ω hω _
      exact hω
    · exact Eventually.of_forall fun _ => Eventually.of_forall fun _ h' => absurd h' hqt
  filter_upwards [hEgf, hKf, hxf, hrunf, hcapf, ae_all_iff.2 hrtf] with ω₀ g1 g2 g3 g4 g5 g6
  filter_upwards [g1, g2, g3, g4, g5, ae_all_iff.2 g6] with ω e1 e2 e3 e4 e5 e6
  exact ⟨e1, e2, e3, e4, e5, e6⟩

/-- **Two B-time-0 good samples with the same frozen data at time `t` have the same root clock at `t`.** -/
theorem a_eq_of_frozen (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {ω ω₀ : Ω} (hω : ω ∈ S.Eg₀) (hω₀ : ω₀ ∈ S.Eg₀) (t : ℝ≥0)
    (e2 : S.K ω = S.K ω₀) (e3 : S.x₀ ω = S.x₀ ω₀)
    (e4 : ∀ n, n ≤ ℓ + 1 → ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
        ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) n)
    (e5 : ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ↔
        ω₀ ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t)
    (e6 : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t → (Cm.rootTime κ b jumps E u l k ℓ ω ≤ ((q : ℝ≥0) : ℝ≥0∞) ↔
        Cm.rootTime κ b jumps E u l k ℓ ω₀ ≤ ((q : ℝ≥0) : ℝ≥0∞))) :
    S.a t ω = S.a t ω₀ := by
  have G := S.good₀ ω hω
  have G₀ := S.good₀ ω₀ hω₀
  obtain ⟨htL, hmin, hp⟩ := piece_eq_of_frozen₀ hℓ hwℓ G G₀ t e4 e5
  rw [S.rootTime_eq hω, S.rootTime_eq hω₀] at e6
  obtain ⟨hlt, heq⟩ := entr_eq_of_rat e6
  set τ := Nd.entrR κ b jumps E u l k ℓ ω with hτ
  set τ₀ := Nd.entrR κ b jumps E u l k ℓ ω₀ with hτ₀
  have hEg : ∀ ω' ∈ S.Eg₀, (ω' ∈ S.Eg ↔ Nd.entrR κ b jumps E u l k ℓ ω' < bLife b jumps E ℓ ω') :=
    fun ω' h' => ⟨fun h'' => (S.ent ω' h').1 h''.2, fun h'' => ⟨h', (S.ent ω' h').2 h''⟩⟩
  -- a sample of the good event whose entrance is not before `t` has a zero clock
  have hzero : ∀ ω' ∈ S.Eg₀, ¬ Nd.entrR κ b jumps E u l k ℓ ω' < t → S.a t ω' = 0 := by
    intro ω' h' hn
    by_cases hE' : ω' ∈ S.Eg
    · refine S.a_eq_zero_of_le t ?_
      have hfin : Nd.entrR κ b jumps E u l k ℓ ω' ≠ ⊤ := (S.entr_lt hE').ne_top
      unfold rSh
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
      exact not_lt.1 hn
    · exact S.a_of_notMem hE' t
  by_cases hτt : τ₀ < t
  · have hττ : τ = τ₀ := heq hτt
    have hτfin : τ₀ ≠ ⊤ := ne_top_of_lt hτt
    have hmemL : τ < bLife b jumps E ℓ ω ↔ τ₀ < bLife b jumps E ℓ ω₀ := by
      rw [hττ]
      have h1 : ∀ L : ℝ≥0∞, τ₀ < L ↔ τ₀ < min (t : ℝ≥0∞) L := fun L => by
        rw [lt_min_iff]; exact ⟨fun h' => ⟨hτt, h'⟩, fun h' => h'.2⟩
      rw [h1, h1 (bLife b jumps E ℓ ω₀), hmin]
    have hsh : rSh κ b jumps E u l k ℓ ω = rSh κ b jumps E u l k ℓ ω₀ := by
      unfold rSh; rw [← hτ, ← hτ₀, hττ]
    by_cases hE₀ : ω₀ ∈ S.Eg
    · have hE : ω ∈ S.Eg := (hEg ω hω).2 (hmemL.2 ((hEg ω₀ hω₀).1 hE₀))
      rw [S.a_eq_shift hE, S.a_eq_shift hE₀, hsh]
      set sh := rSh κ b jumps E u l k ℓ ω₀ with hshdef
      have hshτ : (sh : ℝ≥0∞) = τ₀ := by rw [hshdef, rSh, ← hτ₀, ENNReal.coe_toNNReal hτfin]
      have hsht : sh ≤ t := by
        have := hτt.le; rw [← hshτ] at this; exact ENNReal.coe_le_coe.1 this
      have hshL : (sh : ℝ≥0∞) < bLife b jumps E ℓ ω₀ := by rw [hshτ]; exact S.entr_lt hE₀
      have hshL' : (sh : ℝ≥0∞) < bLife b jumps E ℓ ω := by rw [hshτ, ← hττ]; exact S.entr_lt hE
      have hd := S.driven_rRel hE
      have hd₀ := S.driven_rRel hE₀
      unfold rRel at hd hd₀
      unfold rLift
      rw [e3] at hd ⊢
      have hrPc : ∀ s : ℝ≥0, rPc κ b jumps E u l k ℓ ω s = bPc κ b jumps E ℓ ω (sh + s) := fun s => by
        simp only [rPc, hsh]
      have hrLife : rLife κ b jumps E u l k ℓ ω = bLife b jumps E ℓ ω - sh := by simp only [rLife, hsh]
      have hrLife₀ : rLife κ b jumps E u l k ℓ ω₀ = bLife b jumps E ℓ ω₀ - sh := rfl
      have hiff : ∀ L : ℝ≥0∞, (((t - sh : ℝ≥0)) : ℝ≥0∞) < L - sh ↔ (t : ℝ≥0∞) < L := fun L => by
        rw [lt_tsub_iff_left, ← ENNReal.coe_add, add_tsub_cancel_of_le hsht]
      refine clockOf_canonVal_congr (by rw [e2]) hd hd₀ (S.geo hE).pos (S.geo hE₀).pos (t - sh) ?_ ?_ ?_
      · rw [hrLife, hrLife₀, hiff, hiff]; exact htL
      · rw [hrLife, hrLife₀]
        by_cases htl : (t : ℝ≥0∞) < bLife b jumps E ℓ ω
        · rw [min_eq_left ((hiff _).2 htl).le, min_eq_left ((hiff _).2 (htL.1 htl)).le]
        · have hL : bLife b jumps E ℓ ω = bLife b jumps E ℓ ω₀ := by
            have h1 : min (t : ℝ≥0∞) (bLife b jumps E ℓ ω) = bLife b jumps E ℓ ω := min_eq_right (not_lt.1 htl)
            have h2 : min (t : ℝ≥0∞) (bLife b jumps E ℓ ω₀) = bLife b jumps E ℓ ω₀ :=
              min_eq_right (not_lt.1 fun h' => htl (htL.2 h'))
            rw [← h1, ← h2, hmin]
          rw [hL]
      · intro s hs
        rw [hrPc]
        have h1 : ((sh + s : ℝ≥0) : ℝ≥0∞) ≤ min (t : ℝ≥0∞) (bLife b jumps E ℓ ω) := by
          rw [hrLife] at hs
          refine le_min ?_ ?_
          · have := hs.trans (min_le_left _ _)
            rw [ENNReal.coe_le_coe] at this ⊢
            exact (le_tsub_iff_left hsht).1 this
          · have := hs.trans (min_le_right _ _)
            rw [ENNReal.coe_add]
            calc (sh : ℝ≥0∞) + s ≤ sh + (bLife b jumps E ℓ ω - sh) := add_le_add le_rfl this
              _ = bLife b jumps E ℓ ω := add_tsub_cancel_of_le hshL'.le
        rw [hp _ h1]
        rfl
    · have hE : ω ∉ S.Eg := fun h' => hE₀ ((hEg ω₀ hω₀).2 (hmemL.1 ((hEg ω hω).1 h')))
      rw [S.a_of_notMem hE, S.a_of_notMem hE₀]
  · rw [hzero ω₀ hω₀ hτt, hzero ω hω fun h' => hτt (hlt.1 h')]

/-- **The root clock is measurable for the completed line filtration at every time.** -/
theorem measurable_a_line (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (t : ℝ≥0) : Measurable[mΩ ⊓ aeSigma (lineSigmaT κ b jumps E u l k ℓ t) P] (S.a t) := by
  refine measurable_inf_aeSigma_of_frozen (lineSigmaT_le (u := u) (k := k) hb hE hER hlθ hℓ hwℓ t)
    (S.measurable_a hb t) ?_
  filter_upwards [S.ae_ae_frozen hb hE hER hlθ hℓ hwℓ t] with ω₀ h'
  filter_upwards [h'] with ω ⟨e1, e2, e3, e4, e5, e6⟩
  by_cases hω₀ : ω₀ ∈ S.Eg₀
  · exact S.a_eq_of_frozen hℓ hwℓ (e1.2 hω₀) hω₀ t e2 e3 e4 e5 e6
  · rw [S.a_of_notMem (fun h'' => hω₀ (e1.1 h''.1)), S.a_of_notMem (fun h'' => hω₀ h''.1)]

end RootObj

end InteractingSLE.Theorem14.SB.Nf
