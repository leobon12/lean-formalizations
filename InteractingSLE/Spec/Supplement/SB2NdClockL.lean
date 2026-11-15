/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NdRoot
import InteractingSLE.Spec.Supplement.SB2NcFrzK
import InteractingSLE.Spec.Supplement.SB2MjFilt

/-!
# F2b′'s relative clock is adapted to the completed line filtration

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B). The line family of F2b′ at time `t` is
`lineSigmaT t = upper past ⊔ B's past capped at its time t` (the statement's `𝓖 t`). **`measurable_a_line`**: the
relative clock `S.a t` of F2b′'s stage objects is measurable for `mΩ ⊓ aeSigma (lineSigmaT t) P` (`lineFiltC P 𝓖 t`).
It is measurable (`StageObj.measurable_a`) and frozen under the conditional laws given `lineSigmaT t`:

* the good event, the hull `K` (dyadic hits) and the offset `x₀` are completion-measurable at time `0`;
* the capped runs (cap `t`) of the regularized family are frozen (`ae_ae_run_eq_of_regular`), so B's piece on
  `[0, min t ζ]` and `min t ζ` are (`pcPt_eq_of_capRun_eq`); the cap event `{t < ζ}` is a capped-past event;
* the clock at `t` only sees these (`clockOf_canonVal_congr`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nd

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf WalkSide LocalSets Sec7.PocketTraversal Lk LuM Nc Dv

/-- **F2b′'s line σ-algebra at time `t`** (the statement's `𝓖 t`). -/
abbrev lineSigmaT {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (t : ℝ≥0) : MeasurableSpace Ω :=
  pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
    pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

theorem lineSigma0_le_T (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (t : ℝ≥0) : lineSigma0 κ b jumps E u l k ℓ ≤ lineSigmaT κ b jumps E u l k ℓ t := by
  obtain ⟨-, hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  exact sup_le_sup le_rfl (Mj.pastSigma_capSpec_mono_real (κ := κ) (b := b) (jumps := jumps)
    (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
    (hreg' (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) hℓ.le hwℓ (s := 0) (t := (t : ℝ≥0∞)) (by simp))

theorem lineSigmaT_le (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (t : ℝ≥0) : lineSigmaT κ b jumps E u l k ℓ t ≤ mΩ := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hq : (t : ℝ≥0∞) ≤ (((n : ℚ≥0) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]; simpa using hn
  have h1 := Mj.pastSigma_capSpec_mono_real (κ := κ) (b := b) (jumps := jumps)
    (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
    (hreg' (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) hℓ.le hwℓ hq
  have h2 := WalkSide.pastSigma_capSpec_le (κ := κ) (b := b) (jumps := jumps)
    (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) hℓ.le hwℓ (n : ℚ≥0)
  exact sup_le ((hE' _ hsu).2.1 k) (h1.trans (h2.trans ((hE' _ hw).2.1 (ℓ + 1))))

/-- **The frozen data at time `t`**: the good event, the hull, the offset, the capped runs of the regularized family
and the cap event are frozen under the conditional laws given `lineSigmaT t`. -/
theorem ae_ae_frozenData (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (S : StageObj P κ b jumps E u l k ℓ) (t : ℝ≥0) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (lineSigmaT κ b jumps E u l k ℓ t) ω₀),
      (ω ∈ S.Eg ↔ ω₀ ∈ S.Eg) ∧ S.K ω = S.K ω₀ ∧ S.x₀ ω = S.x₀ ω₀ ∧
      (∀ n, n ≤ ℓ + 1 → ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
        ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) n) ∧
      (ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ↔
        ω₀ ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t) := by
  obtain ⟨-, hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hwdef
  set Ew := StagedReg.regFam E w with hEwdef
  have hEwm : ∀ j, Measurable (Ew j) := fun j => StagedReg.measurable_regHist
    (hE w (isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true)).1 j
  have h𝒢 := lineSigmaT_le (u := u) (k := k) hb hE hER hlθ hℓ hwℓ t
  have hae0 : aeSigma (lineSigma0 κ b jumps E u l k ℓ) P ≤ aeSigma (lineSigmaT κ b jumps E u l k ℓ t) P :=
    WalkLaw.aeSigma_mono (lineSigma0_le_T (u := u) (l := l) (k := k) hb hE hER hℓ hwℓ t)
  have hEgf := ae_ae_mem_iff_of_aeSigma (P := P) h𝒢 (hae0 _ S.hEg.2)
  have hKf := ae_ae_eq_of_dyadicHit (P := P) h𝒢 (fun n q => hae0 _ (S.hK n q).2) fun ω => (S.hKc ω).isClosed
  have hxf := ae_ae_eq_of_measurable_aeSigma (P := P) h𝒢 (Z := S.x₀) fun B hB => hae0 _ (S.hx₀ hB).2
  have hrunf := ae_ae_run_eq_of_regular (P := P) (capSpec w ℓ θ (t : ℝ≥0∞)) (hreg' w) (k := ℓ + 1) h𝒢 le_sup_right
  have hcapm : MeasurableSet[lineSigmaT κ b jumps E u l k ℓ t] (capEvent κ b jumps w Ew ℓ t) :=
    le_sup_right (a := pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k) _
      (measurableSet_capEvent hb hEwm (hreg' w) hℓ.le hwℓ t)
  have hcapf := ae_ae_mem_iff (P := P) h𝒢 hcapm
  filter_upwards [hEgf, hKf, hxf, hrunf, hcapf] with ω₀ g1 g2 g3 g4 g5
  filter_upwards [g1, g2, g3, g4, g5] with ω e1 e2 e3 e4 e5
  exact ⟨e1, e2, e3, e4, e5⟩

/-- **Two good samples with the same frozen data at time `t`** have the same lifetime condition, the same
`min t ζ` and the same piece on `[0, min t ζ]`. -/
theorem piece_eq_of_frozen (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω ω₀ : Ω}
    (G : StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) (G₀ : StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω₀) (t : ℝ≥0)
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
  have hreg : ∀ (ω' : Ω), StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω' →
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

/-- **Two good samples with the same frozen data at time `t` have the same clock at `t`.** -/
theorem StageObj.a_eq_of_frozen (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (S : StageObj P κ b jumps E u l k ℓ) {ω ω₀ : Ω} (hω : ω ∈ S.Eg) (hω₀ : ω₀ ∈ S.Eg) (t : ℝ≥0)
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
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t) :
    S.a t ω = S.a t ω₀ := by
  have G := S.good ω hω
  have G₀ := S.good ω₀ hω₀
  obtain ⟨htL, hmin, hp⟩ := piece_eq_of_frozen hℓ hwℓ G G₀ t e4 e5
  rw [S.a_of_mem hω, S.a_of_mem hω₀]
  unfold bLift
  rw [e3]
  refine clockOf_canonVal_congr (by rw [e2]) ?_ G₀.driven G.pos G₀.pos t htL hmin hp
  have hd := G.driven
  unfold bRel at hd
  rw [e3] at hd
  exact hd

/-- **The relative clock is measurable for the completed line filtration at every time.** -/
theorem measurable_a_line (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (S : StageObj P κ b jumps E u l k ℓ) (t : ℝ≥0) :
    Measurable[mΩ ⊓ aeSigma (lineSigmaT κ b jumps E u l k ℓ t) P] (S.a t) := by
  refine measurable_inf_aeSigma_of_frozen (lineSigmaT_le (u := u) (k := k) hb hE hER hlθ hℓ hwℓ t)
    (S.measurable_a hb t) ?_
  filter_upwards [ae_ae_frozenData hb hE hER hlθ hℓ hwℓ S t] with ω₀ h
  filter_upwards [h] with ω ⟨e1, e2, e3, e4, e5⟩
  by_cases hω₀ : ω₀ ∈ S.Eg
  · exact StageObj.a_eq_of_frozen hℓ hwℓ S (e1.2 hω₀) hω₀ t e2 e3 e4 e5
  · rw [S.a_of_notMem (fun h' => hω₀ (e1.1 h')), S.a_of_notMem hω₀]

end

end InteractingSLE.Theorem14.SB.Nd
