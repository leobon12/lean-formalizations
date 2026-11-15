/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrWalk5
import InteractingSLE.Spec.Supplement.SB4RTrStaged

/-!
# The restarted lower walk is a staged history of the translated field

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). **`restartFam_spec`**: for the actual staged lower
walk `E` of `h` on its initial forced arc `[0, v]`, and any staged lower walk `E₀` of the translated field
`affField (−v) h` (data `b(· + v)`), the restarted family (`restartFam`: the regularized first driver of `E₀`, then the
regularized drivers of `E`) is a `StagedPiecesRegular` staged lower walk of the translated field, and almost surely
the translated lower walk of `E` is `[−v, 0]` together with it (`ae_lowerWalk_restart`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw FlowDilate
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

section Fam

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The restarted lower walk.** -/
theorem restartFam_spec (h13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b J P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b J P spec (E spec))
    {v : ℝ} (hv : 0 < v) (hlow0 : rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow : ∀ x ∈ jumpSet b J, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    {E₀ : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE₀ : IsStagedHistory κ (affData 1 (-v) b) (affJumps 1 (-v) J) P (fun ω => affField (-v) one_pos (h ω))
      (boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J) (-(Real.pi / 2)) true) E₀)
    (hE₀R : StagedPiecesRegular κ (affData 1 (-v) b) (affJumps 1 (-v) J) P
      (boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J) (-(Real.pi / 2)) true) E₀) :
    IsStagedHistory κ (affData 1 (-v) b) (affJumps 1 (-v) J) P (fun ω => affField (-v) one_pos (h ω))
        (boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J) (-(Real.pi / 2)) true)
        (restartFam (StagedReg.regHist (boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J) (-(Real.pi / 2)) true)
          E₀ 0) (StagedReg.regHist (boundaryWalkSpec b J (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b J (-(Real.pi / 2)) true)))) ∧
      StagedPiecesRegular κ (affData 1 (-v) b) (affJumps 1 (-v) J) P
        (boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J) (-(Real.pi / 2)) true)
        (restartFam (StagedReg.regHist (boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J) (-(Real.pi / 2)) true)
          E₀ 0) (StagedReg.regHist (boundaryWalkSpec b J (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b J (-(Real.pi / 2)) true)))) ∧
      ∀ᵐ ω ∂P, (fun z => z - (v : ℂ)) '' lowerWalkSet κ b J E ω =
        ((↑) : ℝ → ℂ) '' Icc (-v) 0 ∪ ExplState.physSet κ (affData 1 (-v) b) (affJumps 1 (-v) J)
          (boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J) (-(Real.pi / 2)) true)
          (fun j => restartFam (StagedReg.regHist (boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J)
            (-(Real.pi / 2)) true) E₀ 0) (StagedReg.regHist (boundaryWalkSpec b J (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b J (-(Real.pi / 2)) true))) j ω) := by
  set lw := boundaryWalkSpec b J (-(Real.pi / 2)) true with hlw
  set B := affData 1 (-v) b with hB
  set JB := affJumps 1 (-v) J with hJB
  set lwT := boundaryWalkSpec B JB (-(Real.pi / 2)) true with hlwT
  set D := StagedReg.regHist lw (E lw) with hDdef
  set D₀ := StagedReg.regHist lwT E₀ with hD₀def
  set F := restartFam (D₀ 0) D with hF
  have hprog : IsBoundaryContinuedProgram lw.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b J ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hbB : IsPiecewiseConstantBoundaryData B JB := isPiecewiseConstantBoundaryData_affData one_pos hb
  have hhT : IsGFFWithBoundaryData P (fun ω => affField (-v) one_pos (h ω)) B JB :=
    IsGFFWithBoundaryData.affine_finset (m := -v) one_pos hh
  have hD : IsStagedHistory κ b J P h lw D := StagedReg.isStagedHistory_regHist hb (hE lw hprog) (hER lw hprog)
  have hR : StagedPiecesRegular κ b J P lw D := WalkLaw.stagedPiecesRegular_regHist (hER lw hprog)
  have hreg : ∀ j ω, IsRegularDriver (D j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have hD₀S : IsStagedHistory κ B JB P (fun ω => affField (-v) one_pos (h ω)) lwT D₀ :=
    StagedReg.isStagedHistory_regHist hbB hE₀ hE₀R
  have hD₀R : StagedPiecesRegular κ B JB P lwT D₀ := WalkLaw.stagedPiecesRegular_regHist hE₀R
  have hreg₀ : ∀ j ω, IsRegularDriver (D₀ j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have hregF : ∀ j ω, IsRegularDriver (F j ω) := fun j ω => by
    show IsRegularDriver (if j = 0 then D₀ 0 ω else D j ω)
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte]; exact hreg₀ 0 ω
    · simp only [hj, ↓reduceIte]; exact hreg j ω
  have hFm : ∀ j, Measurable (F j) := fun j => by
    show Measurable (fun ω => if j = 0 then D₀ 0 ω else D j ω)
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte]; exact hD₀S.1 0
    · simp only [hj, ↓reduceIte]; exact hD.1 j
  have hF0 : ∀ ω, F 0 ω = D₀ 0 ω := fun ω => by simp [hF, restartFam]
  have hFk : ∀ k, k ≠ 0 → ∀ ω, F k ω = D k ω := fun k hk ω => by simp [hF, restartFam, hk]
  have hlow₁ : rightLim B (-v) - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
    rw [show -v = 0 - v by ring, hB, rightLim_trData hb v 0]; exact hlow0
  have hlow₂ : rightLim B 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
    rw [show (0 : ℝ) = v - v by ring, hB, rightLim_trData hb v v]; exact rightLim_low_of_arc hb hv hlow0 hlow
  have hmid : ∀ y ∈ jumpSet B JB, -v < y → y ≤ 0 → ¬ -sleLambda κ < rightLim B y + -(Real.pi / 2) * chiC κ := by
    intro y hy h1 h2 hlt
    rw [hB, hJB, jumpSet_trData hb] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    simp only [Equiv.coe_toEmbedding, Equiv.subRight_apply] at h1 h2 hlt
    rw [hB, rightLim_trData hb] at hlt
    have := hlow x hx (by linarith) (by linarith)
    linarith
  have hz₀ : ∀ᵐ ω ∂P, (D₀ 0 ω).2 = 0 :=
    ae_walk_zero_lifetime hκ hbB hhT hD₀S (not_admissible_of_low hlow₂)
  have hphys := ae_lowerWalk_restart h13₀ hκ hκ4 hb hh hcf hζ' hE hER hv hlow0 hlow (d₀ := D₀ 0)
    (fun ω => hreg₀ 0 ω) hz₀
  -- the restart facts, almost surely
  have hfacts : ∀ᵐ ω ∂P, (∀ k, ExplState.run κ B JB (-v, false, walkProg b J) (fun i => D i ω) k =
      trState v (ExplState.run κ b J lw (fun i => D i ω) k)) ∧
      (∀ k, (ExplState.run κ B JB (0, false, walkProg b J) (fun i => F i ω) k).2.2.1 =
        (ExplState.run κ B JB (-v, false, walkProg b J) (fun i => D i ω) k).2.2.1) ∧
      ∀ k, 1 ≤ k → ∀ (c₂ : Chart) (θ : ℝ),
        (ExplState.run κ B JB (0, false, walkProg b J) (fun i => F i ω) (k + 1)).2.2.2.1 k = some (c₂, θ) →
        ∃ c₁ : Chart, (ExplState.run κ B JB (-v, false, walkProg b J) (fun i => D i ω) (k + 1)).2.2.2.1 k =
          some (c₁, θ) ∧ ChartEqH c₁ c₂ := by
    filter_upwards [ae_run_trState (κ := κ) hb v hR hreg, ae_walk_rightExit h13₀ hκ hκ4 hb hh hcf hζ' hD hreg,
      ae_walk_zero_lifetime hκ hb hh hD (not_admissible_of_low hlow0), hz₀] with ω h2 h3 h4 h5
    rw [trSpec_walk] at h2
    refine ⟨h2, ?_⟩
    refine restart_retained_launches (walkProg b J) (walkProg_zero b J) (walkProg_one b J) (by linarith) rfl
      (show F 0 ω = D₀ 0 ω from hF0 ω) (hreg 0 ω) (hreg₀ 0 ω) h4 h5 hlow₁ hlow₂ hmid (fun j => hreg j ω)
      (fun j hj => hFk j (by omega) ω) ?_
    intro j _ θ t hj hfl
    rw [h2 j] at hfl ⊢
    rw [flowStep_eq_launch_trState_iff hb] at hfl
    obtain ⟨hg, hRx⟩ := h3 j θ t hj hfl
    exact ⟨hg, rightExit_trState v hRx⟩
  have hspec : lwT = (0, false, walkProg b J) := walkSpec_tr hb v
  -- the retained pasts
  have hpast : ∀ k, pastMap κ B JB lwT F k =ᵐ[P] pastMap κ b J lw D k := fun k => by
    filter_upwards [hfacts] with ω hω
    obtain ⟨hA, hret, -⟩ := hω
    funext i
    simp only [pastMap]
    rw [hspec, hret k, hA k, trState_retained]
  have hbB' := hbB
  have hpmF : ∀ k, Measurable (pastMap κ B JB lwT F k) := fun k =>
    measurable_pastMap runMeasStatement hbB lwT (fun j _ => hFm j) (fun j _ ω => hregF j ω) k le_rfl
  have hpmD : ∀ k, Measurable (pastMap κ b J lw D k) := fun k => Measurable.of_comap_le (hD.2.1 k)
  have hK : ∀ k, ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ B JB lwT F k) ω₀ =
      condExpKernel P (pastSigma κ b J lw D k) ω₀ := fun k => by
    filter_upwards [StagedReg.ae_condExpKernel_eq_of_ae_eq (hpmF k) (hpmD k) (hpast k)] with ω₀ h
    rw [pastSigma_eq_comap, h, ← pastSigma_eq_comap]
  have hrun1 : ∀ ω, ExplState.run κ B JB lwT (fun i => F i ω) 1 = ExplState.run κ B JB lwT (fun i => D₀ i ω) 1 :=
    fun ω => run_congr lwT fun j hj => by
      rw [show j = 0 by omega]; exact hF0 ω
  refine ⟨⟨hFm, fun k => (hpmF k).comap_le, fun k => Eventually.of_forall fun ω => (hregF k ω).2.2.2,
    fun k => ?_⟩, ?_, hphys⟩
  · by_cases hk0 : k = 0
    · subst hk0
      filter_upwards [hD₀S.2.2.2 0] with ω₀ h4 c θ hl
      rw [show (0 : ℕ) + 1 = 1 from rfl, hrun1] at hl
      obtain ⟨b', J', h', hb', htr, hfl⟩ := h4 c θ hl
      refine ⟨b', J', h', hb', htr, ?_⟩
      rw [GW1.pastSigma_zero_eq_bot] at hfl ⊢
      have e1 : (fun t ω => (F 0 ω).1 t) = fun t ω => (D₀ 0 ω).1 t := by funext t ω; rw [hF0]
      have e2 : (fun ω => (F 0 ω).2) = fun ω => (D₀ 0 ω).2 := by funext ω; rw [hF0]
      rw [e1, e2]
      exact hfl
    · filter_upwards [hD.2.2.2 k, hK k, hfacts] with ω₀ h4 hKω hω c₂ θ hl
      obtain ⟨hA, -, hlau⟩ := hω
      rw [hspec] at hl
      obtain ⟨c₁, hl₁, hc⟩ := hlau k (by omega) c₂ θ hl
      rw [hA (k + 1), trState_launches] at hl₁
      obtain ⟨⟨c, θ₀⟩, hlR, he⟩ := Option.map_eq_some_iff.1 hl₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨b', J', h', hb', htr, hfl⟩ := h4 c θ₀ hlR
      refine ⟨b', J', h', hb', fun ω => isChartTransport_of_chartEqH hc (isChartTransport_trChart (htr ω) v), ?_⟩
      rw [hKω]
      have e1 : (fun t ω => (F k ω).1 t) = fun t ω => (D k ω).1 t := by funext t ω; rw [hFk k hk0]
      have e2 : (fun ω => (F k ω).2) = fun ω => (D k ω).2 := by funext ω; rw [hFk k hk0]
      rw [e1, e2]
      exact hfl
  · filter_upwards [hD₀R, hR, hfacts] with ω h0' hR' hω
    obtain ⟨hA, -, hlau⟩ := hω
    intro k θ t c₂ hk hl
    by_cases hk0 : k = 0
    · subst hk0
      rw [show (0 : ℕ) + 1 = 1 from rfl, hrun1] at hl
      obtain ⟨hz, hc, η, hη, htop⟩ := h0' 0 θ t c₂ hk hl
      rw [hF0]
      exact ⟨hz, hc, η, hη, htop⟩
    · rw [hspec] at hl
      obtain ⟨c₁, hl₁, -⟩ := hlau k (by omega) c₂ θ hl
      rw [hA (k + 1), trState_launches] at hl₁
      obtain ⟨⟨c, θ₀⟩, hlR, he⟩ := Option.map_eq_some_iff.1 hl₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hk' : lw.2.2[k]? = some (.inl (θ₀, t)) := by
        rw [hspec] at hk; exact hk
      rw [hFk k hk0]
      exact hR' k θ₀ t c hk' hlR

end Fam

end InteractingSLE.Theorem14.SB.Lf
