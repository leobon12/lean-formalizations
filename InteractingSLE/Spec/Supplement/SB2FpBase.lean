/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FmBase
import InteractingSLE.Spec.Supplement.SB2FmSeed
import InteractingSLE.Spec.Supplement.SB2FpAdm
import InteractingSLE.Spec.Supplement.SB2FpEnt
import InteractingSLE.Spec.Supplement.SB2FpWord

/-!
# The base law with its word named, and the root facts of `hL`

Worker PROVE-SB2-F3LAW (round 4). `Fm.SB2LowerBaseLawMvStatement` (landed) chooses its word inside the line family.
Here the word `β` (the upper stage witness word read in the hull chart, `Fp.exists_hullLawW`) is chosen once, before
B's stage `ℓ` and the line family `(𝓖, A₁)`, and the conclusion adds the **root facts** on the law's event `G`:

* `A₁ 0` is a hull, free right of `R = realMax (upperPrefix …)`;
* **`LeftAdm κ β (entry (A₁ 0) R)`** — the base of D34's left heights `hL` (the step is `Fo.ae_leftAdm_succ_succ`);
* D55 in the corrected form: for every root object family `(G, K, x₀)`, the word `shiftW x₀ β` satisfies
  `Fp.RootWordAtX` (one constant data word of the relative field wherever the root chart identity holds,
  `Fp.rootWordAtX_of_hull`).

Proof of the root facts: on `G` the retained hull `A₁ 0` is the filled upper prefix `K₀` (head inclusion); SB2WORD's
root clause (`Lz.sb2LowerLeftWeightStatement_of_theorem13`) read on the stage witness `β₀` gives
`LeftAdm β₀ (upperEntry)` (`Fp.ae_leftAdm_witness`); the run chart's hull model of `K₀` with shift `s` gives
`upperEntry = entry K₀ R − s` (`Fp.rightEntry_eq_of_hullModel`), and `β = shiftW (−s) β₀`.

* `SB2LowerBaseWordStatement`, **`sb2LowerBaseWordStatement_of_head`**, **`sb2LowerBaseWordStatement_of_thms`**.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fp

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Supp9B Lx Lk Mf Ms Qt Fm

/-- **The base law with its word named before the stage and the line family, with the root facts** (statement). -/
def SB2LowerBaseWordStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
    ∃ β : Ω → BoundaryWord,
      Measurable[pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k] β ∧
      (∀ (G : Set Ω) (K : Ω → Set ℂ) (x₀ : Ω → ℝ), (∀ ω, IsCompact (K ω)) →
        (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) →
        RootWordAtX κ b jumps P h E u l k G K x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω))) ∧
      ∀ (ℓ : ℕ) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ),
        (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
          pastSigma κ b jumps
            (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
        (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
            WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
            WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
              (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
              ℓ ω) ω) →
        ∃ (K : Ω → Set ℂ) (G : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ),
          Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) K G Y β M ∧
          (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
            ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ G) ∧
          (∀ᵐ ω ∂P, ω ∈ G → IsHPHull (A₁ 0 ω) ∧ FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
            LeftAdm κ (β ω) (entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω))))

/-- **The base law with its word named, with the root facts**, from the head inclusion and Theorems 1.2–1.3. -/
theorem sb2LowerBaseWordStatement_of_head (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hhead : Qt.SB2LowerBaseHeadStatement.{u}) :
    SB2LowerBaseWordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hW' hζ' E hE hER u l k hu hl hlθ hL hleft
  classical
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hbc := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hup := hE' (Lu.upperSpec u l) hbc
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- the upper history in the canonical hull chart
  obtain ⟨K₀, G₁, K, Y, β, M, hK₀m, hK₀c, -, hG₁C, hG₁sub, hG₁ae, hKm, hKc, hKp, hG₁geo, hYm, hYt, hβm, hβs,
    hM0, hβb, hlawU, s, β₀, Y₀, -, hW₀, hβeq, hmodel⟩ := exists_hullLawW h12p h13 hκ hκ4 hb hh hup (hreg' _) k
  -- the root facts on `G₁`: free ray right of `R`, and the word admissible left of `R`'s entry
  have hroot : ∀ᵐ ω ∂P, ω ∈ G₁ → IsHPHull (K₀ ω) ∧
      FreeRight (K₀ ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      LeftAdm κ (β ω) (entry (K₀ ω) (realMax (upperPrefix κ b jumps E u l k ω))) := by
    have hadm := ae_leftAdm_witness h13₀ hκ hκ4 hb hh hW' hζ' hE hER hu hl hlθ hL hleft hW₀
    have hregL := GW1W.regLaunches_of_stagedPiecesRegular (WalkLaw.stagedPiecesRegular_regHist (hER _ hbc))
    filter_upwards [hadm, hregL, hrun _ hbc] with ω hadmω hregω hrω hωG
    obtain ⟨-, hK₀e, hHP⟩ := hG₁geo ω hωG
    have hF : ω ∈ Lu.upperLaunchSet κ b jumps (StagedReg.regFam E) u l k := hG₁sub hωG
    have hAc := Lu.isCompact_upperPrefix (E := StagedReg.regFam E) (fun j c θ' hl => hregω j c θ' hl) hF
    have hRe : realMax (upperPrefix κ b jumps E u l k ω) =
        realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω) := by
      congr 1
      show SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) k ∪ _ =
        SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) k ∪ _
      rw [Qx.prefixPhysSet_congr _ (hrω k)]
    have hfree : FreeRight (K₀ ω) (realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω)) := by
      intro x hx
      obtain ⟨r, hr, hd⟩ := freeRight_fillH_realMax hAc x hx
      refine ⟨r, hr, hd.mono_right ?_⟩
      rw [hK₀e]
      exact fillH_mono subset_union_left
    obtain ⟨Mh, hMh, -, hsM⟩ := hmodel ω hωG
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
    have hc := (eq_launch_of_launches _ _ hcθ).2.2
    have hUE : Lu.upperEntry κ b jumps (StagedReg.regFam E) u l k ω = Lx.rightEntry
        (ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) k).2.2.2.2.1
        (realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω)) := by
      unfold Lu.upperEntry
      rw [Lu.upperLaunchChart_eq hcθ, hc]
    have h1 := rightEntry_eq_of_hullModel Mh (hMh ▸ hfree)
    have h2 := leftAdm_shiftW (hadmω hF) (-(s ω))
    rw [hUE, h1, hMh, ← hsM, sub_neg_eq_add, sub_add_cancel] at h2
    rw [hRe, hβeq ω]
    exact ⟨hHP, hfree, h2⟩
  refine ⟨β, hβm, fun G K' x₀ hKc' hKp' => rootWordAtX_of_hull hb hE hER hlθ hW₀ hβeq hG₁ae
    (fun ω hω => by obtain ⟨Mh, -, -, hsM⟩ := hmodel ω hω; exact ⟨Mh, hsM⟩) G K' x₀ hKc' hKp',
    fun ℓ 𝓖 A₁ h𝓖 hA => ?_⟩
  have hm : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ≤ mΩ := hup.2.1 k
  have hmC : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ≤
      mΩ ⊓ aeSigma (pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k) P :=
    le_inf hm fun s hs => ⟨s, hs, EventuallyEq.rfl⟩
  have hℋdef : lineFiltC P 𝓖 0 = mΩ ⊓ aeSigma (𝓖 0) P := rfl
  have hℋ : lineFiltC P 𝓖 0 ≤ mΩ := inf_le_left
  have hCℋ : mΩ ⊓ aeSigma (pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k) P ≤
      lineFiltC P 𝓖 0 := by
    rw [hℋdef]
    refine inf_le_inf_left _ (WalkLaw.aeSigma_mono (P := P) ?_)
    rw [h𝓖 0]
    exact le_sup_left
  have hKℋ : @IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K := fun n j => hCℋ _ (hKm n j)
  have hβℋ : Measurable[lineFiltC P 𝓖 0] β := hβm.mono (hmC.trans hCℋ) le_rfl
  -- a stage that launches nothing: the stage event is empty
  by_cases hflow : ∃ (θ : ℝ) (t : ℝ≥0∞),
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (θ, t))
  swap
  · refine ⟨K, ∅, Y, M, ⟨hKℋ, hKc, hKp, @MeasurableSet.empty Ω (lineFiltC P 𝓖 0),
      Eventually.of_forall fun _ h' => absurd h' id,
      hYm, Eventually.of_forall fun ω _ => hYt ω, hβℋ, hβs, hM0, hβb,
      Eventually.of_forall fun _ h' => absurd h' id⟩, ?_, Eventually.of_forall fun _ h' => absurd h' id⟩
    refine Eventually.of_forall fun ω hω _ => absurd ?_ hflow
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω.2
    obtain ⟨hins, -, -⟩ := eq_launch_of_launches _ _ hcθ
    exact ⟨θ, _, hins⟩
  obtain ⟨θ, t, hwℓ⟩ := hflow
  obtain ⟨rfl, -⟩ := WalkLeaf.boundaryWalkSpec_inl hwℓ
  obtain ⟨hℓ, -⟩ := List.getElem?_eq_some_iff.1 hwℓ
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hcap := isStagedHistory_capSpec (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hb (hE' _ hw) (hreg' _) hℓ hwℓ
  -- the retained union at B-time `0`, marked local for the line filtration
  obtain ⟨hA1, ho1, -, hloc1⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _)
    hu₀ k (ℓ + 1)
  have h𝓜 : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤ mΩ :=
    sup_le (hup.2.1 k) (hcap.2.1 (ℓ + 1))
  obtain ⟨Bp, hBpm, hBpc, hBpae, hBploc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜⟩
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho1 hA1 hloc1
  obtain ⟨hÂm, hÂc, hÂloc, hÂl⟩ := fillVer_package hh0 h𝓜 hBpc hBpm hBploc
  have hÂmΩ : Measurable[mΩ, hittingSigma] (fillVer Bp) := hÂm.mono h𝓜 le_rfl
  have h𝓜ℋ : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤
      lineFiltC P 𝓖 0 := by
    rw [hℋdef, h𝓖 0]
    exact le_inf h𝓜 fun s hs => ⟨s, hs, EventuallyEq.rfl⟩
  have hÂℋ : IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) (fillVer Bp) (centredField h u₀) P := by
    have h1 := Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma (P := P) hÂloc
    rw [hℋdef, h𝓖 0]
    exact h1
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh0 hÂmΩ hÂl
  -- the event where the retained union is the filled upper history
  set G : Set Ω := G₁ ∩ {ω | fillVer Bp ω = K₀ ω} with hGdef
  have hGℋ : MeasurableSet[lineFiltC P 𝓖 0] G :=
    (hCℋ _ hG₁C).inter (h𝓜ℋ _ (measurableSet_eq_of_hitting hÂm (hK₀m.mono le_sup_left le_rfl) hÂc hK₀c))
  have hm₂ : germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0 ≤ mΩ :=
    sup_le (germSigma_le hÂmΩ hh0.measurable) hℋ
  have hGm₂ : MeasurableSet[germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0] G :=
    (le_sup_right : lineFiltC P 𝓖 0 ≤ _) _ hGℋ
  -- the canonical chart family and its data for the finer σ-algebra
  have hc := Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp
  have hKm₂ : @IsDyadicHitMeasurable Ω (germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0) K :=
    fun n j => (le_sup_right : lineFiltC P 𝓖 0 ≤ _) _ (hKℋ n j)
  obtain ⟨-, hliftc, -, hdomm, hfwdm, hliftm⟩ :=
    @Mt.hullChart_k2Inputs Ω (germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0) K (fun _ => 0)
      hKm₂ hKc hKp measurable_const
  have hYeq : ∀ ω, Y ω = Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω) := fun ω =>
    (hYt ω).unique (hc ω) (Chart.isChartTransport_chartTransport (hc ω) (Chart.locallyIntegrableOn_of_continuousOn
      (Mu.continuousOn_lift_inv_hullChart (Mo.isHPHull_fillH hKc hKp ω) 0)) 1 0 (chiC κ) (h ω))
  -- the conditional mean of the field off the retained union
  set Mf : Ω → DistOn upperHalfPlaneOpens := fun ω => g ω + (h ω - centredField h u₀ ω) with hMfdef
  have hMφ : ∀ ω φ, Mf ω φ = g ω φ + ∫ z, u₀ z * φ z := fun ω φ => by
    simp only [hMfdef, add_apply, sub_apply,
      WholeField.centredField_apply h hu₀.1 ω φ]
    ring
  have hMm : Measurable[germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0] Mf := by
    let _ : MeasurableSpace Ω := germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0
    refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
    have e : (fun ω => Mf ω φ) = fun ω => g ω φ + ∫ z, u₀ z * φ z := funext fun ω => hMφ ω φ
    rw [e]
    exact (((LQGMetric.measurable_distOn_apply φ).comp hg.1).mono le_sup_left le_rfl).add_const _
  -- the marked Gaussian kernel on the event, read on the chart domain
  have hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      tsupport φ ⊆ ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
        germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0] ω =
        Complex.exp (Complex.I * (Mf ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) φ φ : ℝ) : ℂ)) := by
    intro φ
    set cst : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hcst
    have hfun : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) =
        cst • fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, hcst, ← Complex.exp_add, WholeField.centredField_apply h hu₀.1 ω' φ]
      congr 1
      push_cast
      ring
    filter_upwards [Supp8.RelSafeS.ae_condExp_cexp_marked hh0 hÂmΩ hÂc hℋ hÂℋ hg φ,
      condExp_smul (m := germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0) (μ := P) cst
        (fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)))] with ω hω hsm hωG _
    have hdom : ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) = H \ fillVer Bp ω := by
      rw [Mo.coe_dom_hullChart (Mo.isHPHull_fillH hKc hKp ω) 0, (hG₁geo ω hωG.1).1, hωG.2]
    rw [hfun, hsm, Pi.smul_apply, hω, hdom, smul_eq_mul, hcst, hMφ, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the chart field's Gaussian law on the event, given the finer σ-algebra
  have hfine := fun ψ => Restart.ae_condExp_cexp_chartTransport_random_on hm₂ hc hdomm hfwdm hliftm hliftc hh.1
    (chiC κ) hGm₂ hcond ψ
  -- the nested identity
  set L : Set Ω := {ω | (ExplState.run κ b jumps (Lu.upperSpec u l)
    (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none} with hLdef
  have hLm : MeasurableSet[pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k] L :=
    Lv.measurableSet_launch_pastSigma hb hup.1 (hreg' _) k
  have hmm₂ : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ≤
      germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0 := (hmC.trans hCℋ).trans le_sup_right
  have hM' : ∀ ψ : TestOn upperHalfPlaneOpens,
      Measurable[germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0]
        fun ω => Chart.chartTransport (hc ω) 1 0 (chiC κ) (Mf ω) ψ := fun ψ =>
    (LQGMetric.measurable_distOn_apply ψ).comp
      (@Chart.measurable_chartTransport_random' Ω (germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0)
        _ hc hdomm hfwdm hliftm hliftc _ hMm 1 0 (chiC κ))
  have hcoarse := fun ψ => S3.ae_condExp_gaussCF_of_kernel hm hYm (Eventually.of_forall fun ω _ => hβs ω) hlawU ψ
  have hH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
  have hnest : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) |
        germSigma (fillVer Bp) (centredField h u₀) ⊔ lineFiltC P 𝓖 0] ω = gaussCF (β ω) ψ := by
    refine Qt.ae_condExp_cexp_eq_gaussCF_of_le_on hmm₂ hm₂ hYm hβm hM' hLm hGm₂
      (fun ω hω => hG₁sub hω.1) hcoarse (fun ψ => ?_)
    have hY' : (fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ))) =
        fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 0 (chiC κ) (h ω') ψ : ℂ)) := by
      funext ω'
      rw [hYeq ω']
    filter_upwards [hfine ψ] with ω hω hωG
    rw [hY', hω hωG, hH]
    congr 1
    push_cast
    ring
  -- the tower property down to the kernel half's marks
  have hgiven : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | lineFiltC P 𝓖 0] ω = gaussCF (β ω) ψ := fun ψ =>
    Restart.ae_condExp_eq_on_of_le le_sup_right hm₂
      (GFF.integrable_exp_I_mul (P := P) ((LQGMetric.measurable_distOn_apply ψ).comp hYm))
      ((Restart.measurable_gaussCF ψ).comp hβℋ).stronglyMeasurable (fun ω => Restart.norm_gaussCF_le _ ψ) hGℋ
      (hnest ψ)
  have hlaw := Exist.StagedLaw.ae_isGFFWithBoundaryData_condExpKernel hℋ (Eventually.of_forall fun ω _ => hβs ω)
    hYm hgiven
  have hAG : ∀ᵐ ω ∂P, ω ∈ G → fillH (K ω) = A₁ 0 ω := by
    -- the retained union on `G`
    filter_upwards [hA 0, hBpae] with ω hA0 hBpω hωG
    obtain ⟨hfK, hK₀e, hHP⟩ := hG₁geo ω hωG.1
    have hSF : fillH (closure (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω)) = K₀ ω := by
      rw [stageSet_eq_prefixPhysSet_inter_H, Mo.fillH_closure_inter_H, hK₀e]
    rw [hfK, hA0]
    refine (fillVer_union_of_le hHP.2.1 hSF ((Qr.fillVer_congr (B' := fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω)
      hBpω).symm.trans hωG.2) ?_).symm
    rw [WalkLaw.stageSet_succ]
    exact subset_union_left
  refine ⟨K, G, Y, M, ⟨hKℋ, hKc, hKp, hGℋ, hAG, hYm, Eventually.of_forall fun ω _ => hYt ω, hβℋ, hβs, hM0,
    hβb, hlaw⟩, ?_, ?_⟩
  · -- the base event lies in `G`
    filter_upwards [hhead κ hκ hκ4 b jumps hb P h hh W' ζ' hW' hζ' E hE hER u l k hu hl hlθ hL hleft ℓ, hG₁ae,
      hrun (Lu.upperSpec u l) hbc, hBpae] with ω hhω hG₁ω hrω hBpω hst hrel
    have hLω : ω ∈ L := by
      show (ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω)
        (k + 1)).2.2.2.1 k ≠ none
      rw [hrω (k + 1)]
      exact hst.1
    have hG₁' := hG₁ω hLω
    obtain ⟨-, hK₀e, hHP⟩ := hG₁geo ω hG₁'
    have hSp := hhω hst hrel
    rw [← hK₀e] at hSp
    have hSup : WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ⊆ K₀ ω := by
      intro z hz
      rw [hK₀e, stageSet_eq_prefixPhysSet_inter_H] at *
      exact mem_fillH_of_mem_closure hz.2 (subset_closure hz.1)
    have hSF : fillH (closure (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω)) = K₀ ω := by
      rw [stageSet_eq_prefixPhysSet_inter_H, Mo.fillH_closure_inter_H, hK₀e]
    have hbd : Bornology.IsBounded (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪ WalkLaw.stageSet κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω) :=
      hHP.2.1.subset (union_subset hSup hSp)
    refine ⟨hG₁', ?_⟩
    show fillVer Bp ω = K₀ ω
    rw [Qr.fillVer_congr (B' := fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω)
      hBpω, fillVer_of_bounded (B := fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω) hbd]
    exact fillH_closure_union_of_subset hHP hSF (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) hSp
  · -- the root facts on `G`
    filter_upwards [hroot, hAG] with ω hrω hAGω hωG
    rw [← hAGω hωG, (hG₁geo ω hωG.1).1]
    exact hrω hωG.1


/-- **The base law with its word named, with the root facts**, outright (Theorems 1.2–1.3). -/
theorem sb2LowerBaseWordStatement_of_thms (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    SB2LowerBaseWordStatement.{u} :=
  sb2LowerBaseWordStatement_of_head (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13 h13₀
    (Qu.sb2LowerBaseHeadStatement h12 h13 h12₀ h13₀)

end InteractingSLE.Theorem14.SB.Fp
