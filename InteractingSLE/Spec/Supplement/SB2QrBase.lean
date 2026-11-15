/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QrF3
import InteractingSLE.Spec.Supplement.SBS3TerminalSelect
import InteractingSLE.Spec.Supplement.SBLwChart
import InteractingSLE.Spec.Supplement.SB2HEntry
import InteractingSLE.Spec.Supplement.SB2MoRet
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun

/-!
# D5's F3 at the first stage of the lower walk: the filled history of one walk in its canonical hull chart

Worker REVIEW-FABLE-T14 (proving phase; orchestrator adjustment: D5's F3, `hind₁` of SB2(2)'s conditional half).

The base of the stage induction of F3, proved outright. Before the lower walk B has any piece, the retained union is
the filled history of the upper walk alone. For one staged history (regular at every sample), at a launching stage
`k`, the run chart is the canonical hull chart of the filled history up to a real shift
(`Lw.exists_hullModel_fill`, `WalkIntCanon.HullModel.lift_eq_canonDerivLog`), and the stage witness gives the kernel
law in the run chart. Hence the mean of the **filled** history, read in the canonical hull chart of offset `0`, is the
mean of the stage word shifted by the chart's shift.

* `tendsto_re_sub_fwd`: the shift of a hull model is `lim_n Re (n i − F(n i))` (hydrodynamic normalization), and
  `n i` is eventually in the chart domain; this makes the shift a measurable function of the retained past;
* **`exists_hullWord_mean`**: for a staged history regular at every sample and a stage `k`, there is a sorted word
  `β₁`, measurable for the retained past before `k`, such that for every hitting-measurable version `A₁` of the filled
  explored set `fillVer (stageSet k)` and every local-set mean of `A₁`, almost surely on the launch event of `k`,
  every harmonic representative `w₁` satisfies `w₁ + u₀ = β₁.mean ∘ g_{A₁} − χ · Im (canonDerivLog A₁)` on `ℍ ∖ A₁`;
* **`sb2LowerRetainedMean_zero`**: the body of `Ms.SB2LowerRetainedMeanStatement` at stage `ℓ = 0`, for every cap.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qr

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Sec4 Supp9B Lx

/-! ### The shift of a hull model -/

/-- **The shift of a hull model is read at `i∞`**: `Re (n i − F(n i)) → shift`, and `n i` is eventually in the chart
domain. -/
theorem tendsto_re_sub_fwd {c : Chart} (M : WalkIntCanon.HullModel c) :
    Tendsto (fun n : ℕ => ((n : ℂ) * Complex.I - c.1 ((n : ℂ) * Complex.I)).re) atTop (𝓝 M.shift) ∧
      ∀ᶠ n : ℕ in atTop, (n : ℂ) * Complex.I ∈ (c.dom : Set ℂ) := by
  obtain ⟨R, hR⟩ := M.isHull.2.1.exists_norm_le
  have hmem : ∀ᶠ n : ℕ in atTop, (n : ℂ) * Complex.I ∈ H \ M.hull := by
    filter_upwards [eventually_gt_atTop ⌈max R 0⌉₊] with n hn
    have hnR : max R 0 < (n : ℝ) := Nat.lt_of_ceil_lt hn
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right R 0) hnR
    refine ⟨?_, fun hz => ?_⟩
    · show 0 < ((n : ℂ) * Complex.I).im
      simpa using hn0
    · have hle := hR _ hz
      have hnorm : ‖(n : ℂ) * Complex.I‖ = n := by simp
      rw [hnorm] at hle
      exact absurd hle (not_le.2 (lt_of_le_of_lt (le_max_left R 0) hnR))
  have hcob : Tendsto (fun n : ℕ => (n : ℂ) * Complex.I) atTop (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    have hnorm : (fun n : ℕ => ‖(n : ℂ) * Complex.I‖) = fun n : ℕ => (n : ℝ) := by
      funext n
      simp
    rw [hnorm]
    exact tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun n : ℕ => (n : ℂ) * Complex.I) atTop (Bornology.cobounded ℂ ⊓ 𝓟 (H \ M.hull)) :=
    tendsto_inf.2 ⟨hcob, tendsto_principal.2 hmem⟩
  have hlim := M.mapOut.2.comp htend
  refine ⟨?_, ?_⟩
  · have h1 : Tendsto (fun n : ℕ => (M.shift : ℂ) -
        (c.1 ((n : ℂ) * Complex.I) + (M.shift : ℂ) - (n : ℂ) * Complex.I)) atTop (𝓝 ((M.shift : ℂ) - 0)) :=
      tendsto_const_nhds.sub hlim
    have h2 := (Complex.continuous_re.tendsto _).comp h1
    simp only [sub_zero, Complex.ofReal_re] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply]
    congr 1
    ring
  · filter_upwards [hmem] with n hn
    rw [M.dom_eq]
    exact hn

/-! ### One staged history: the filled explored set in its canonical hull chart -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The mean of the filled explored set of one staged history, in the canonical hull chart.** For a staged history
regular at every sample and a stage `k` there is a sorted word `β₁`, measurable for the retained past before `k`, such
that for every hitting-measurable version `A₁` of the filled explored set `fillVer (stageSet k)` and every local-set
mean `g₁` of `A₁` (centred field), almost surely on the launch event of `k`, every harmonic representative `w₁` of
`g₁` off `A₁` satisfies `w₁ + u₀ = (β₁ ω).mean ∘ g_{A₁} − χ(κ) · Im (canonDerivLog A₁)` on `ℍ ∖ A₁`. -/
theorem exists_hullWord_mean (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (k : ℕ) :
    ∃ β₁ : Ω → BoundaryWord, Measurable[pastSigma κ b jumps spec E k] β₁ ∧ (∀ ω, (β₁ ω).IsSorted) ∧
      ∀ A₁ : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A₁ →
        (∀ᵐ ω ∂P, A₁ ω = fillVer (WalkLaw.stageSet κ b jumps spec E k) ω) →
        ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₁ (centredField h u₀) P g₁ →
          ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
            ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
              EqOn (fun z => w₁ z + u₀ z)
                (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ ω) 0).2.2 z)
                (H \ A₁ ω) := by
  classical
  have hR : StagedPiecesRegular κ b jumps P spec E := stagedPiecesRegular_of_regular h13 hκ hb hS hreg
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨β, Y, hW, hSide⟩ := S3.exists_stageWitness_interiorStageSides hκ hb hh hS hR hreg k
  obtain ⟨c₀, hc₀, -, -⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hc₀s : c₀.IsSorted := fun i j hij hj => hc₀.monotoneOn (lt_of_le_of_lt hij hj) hj hij
  have hc : S3.RetainedChartData (pastSigma κ b jumps spec E k) (WalkInf.verChart κ b jumps spec E k) :=
    S3.retainedChartData_verChart hb hS.1 hreg k
  -- the shift, as a measurable function of the retained past
  obtain ⟨s, hsdef⟩ : ∃ s : Ω → ℝ, s = fun ω => limsup (fun n : ℕ => ((n : ℂ) * Complex.I -
      ({ω | (n : ℂ) * Complex.I ∈ (WalkInf.verChart κ b jumps spec E k ω).dom}.indicator
        (fun ω => (WalkInf.verChart κ b jumps spec E k ω).1 ((n : ℂ) * Complex.I)) ω)).re) atTop := ⟨_, rfl⟩
  have hsm : Measurable[pastSigma κ b jumps spec E k] s := by
    rw [hsdef]
    let _ : MeasurableSpace Ω := pastSigma κ b jumps spec E k
    exact Measurable.limsup fun n => Complex.measurable_re.comp (measurable_const.sub (hc.forward _))
  -- the word, sorted at every sample
  obtain ⟨β', hβ'def⟩ : ∃ β' : Ω → BoundaryWord, β' = fun ω => if (β ω).IsSorted then β ω else c₀ := ⟨_, rfl⟩
  have hβ'm : Measurable[pastSigma κ b jumps spec E k] β' := by
    rw [hβ'def]
    exact Measurable.ite (hW.1 BoundaryWord.measurableSet_isSorted) hW.1 measurable_const
  have hβ's : ∀ ω, (β' ω).IsSorted := fun ω => by
    rw [hβ'def]
    simp only
    split_ifs with hs
    exacts [hs, hc₀s]
  refine ⟨fun ω => BoundaryWord.shiftW (-(s ω)) (β' ω),
    BoundaryWord.measurable_shiftW.comp (hsm.neg.prodMk hβ'm),
    fun ω => BoundaryWord.isSorted_shiftW (hβ's ω) _, ?_⟩
  intro A₁ hA₁ hA₁e g₁ hg₁
  -- locality of `A₁` for the retained past
  obtain ⟨hA, ho, hlocS⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hS hreg hu₀ k
  obtain ⟨B₁, hB₁m, hB₁c, hB₁ae, hB₁loc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, hS.2.1 k⟩
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) ho hA hlocS
  obtain ⟨-, hFc, hFloc, -⟩ := fillVer_package hh0 (hS.2.1 k) hB₁c hB₁m hB₁loc
  have hAF : ∀ᵐ ω ∂P, fillVer B₁ ω = A₁ ω := by
    filter_upwards [hA₁e, hB₁ae] with ω h1 h2
    rw [h1]
    unfold fillVer
    rw [h2]
  have hmark := WalkLaw.isHistoryAvoidanceLocal_congr_ae hAF hFloc
  have hAc : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω) := by
    filter_upwards [hAF] with ω he
    rw [← he]
    exact hFc ω
  have hloc : IsLocalSet A₁ (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hA₁ hAc).out 4 1).2 hmark.isAvoidanceLocal
  -- the geometry at a launching sample: a normalized hull model of the run chart with hull `A₁`
  have hgeo : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ∃ M : WalkIntCanon.HullModel (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1,
        M.hull = A₁ ω ∧
        WalkIntCanon.IsNormalized (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 := by
    filter_upwards [hR.ae_pieceRegular, hA₁e] with ω hpr hAe hl
    obtain ⟨⟨c', θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    have hnd := WalkIntRunChron.not_done_of_launch spec (fun j => E j ω) hcθ
    have hreg' : ∀ (j : ℕ) (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2) := fun j c θ hlj => hpr j c θ hlj
    obtain ⟨M, hM⟩ := Lw.exists_hullModel_fill spec (fun j => E j ω) hreg' k hnd
    have hcpt := Lx.isCompact_prefixPhysSet_run spec (fun j => E j ω) hreg' k hnd
    have hSP : WalkLaw.stageSet κ b jumps spec E k ω =
        SB.prefixPhysSet κ b jumps spec (fun j => E j ω) k ∩ H := by
      ext z
      constructor
      · intro hz
        exact ⟨Or.inl (Or.inr hz.1), hz.2⟩
      · intro hz
        exact WalkLeaf.mem_stageSet_of_mem_prefixPhysSet spec E k ω hz.1 hz.2
    have hbd : Bornology.IsBounded (WalkLaw.stageSet κ b jumps spec E k ω) := by
      rw [hSP]
      exact hcpt.isBounded.subset inter_subset_left
    refine ⟨M, ?_, WalkIntCanon.isNormalized_runChart spec (fun j => E j ω) k fun j _ c θ hlj => hreg' j c θ hlj⟩
    rw [hM, hAe, fillVer_of_bounded hbd, hSP, Mo.fillH_closure_inter_H]
  have hver := Lv.ae_verChart_eq_runChart hR hreg k
  have htr : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsChartTransport (WalkInf.verChart κ b jumps spec E k ω) 1 0 (chiC κ) (h ω) (Y ω) := by
    filter_upwards [hver, hW.2.2.1] with ω hv ht hl
    rw [hv]
    exact (ht hl).2.2
  have hAD : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ((WalkInf.verChart κ b jumps spec E k ω).dom : Set ℂ) ⊆ H \ A₁ ω ∧
        IsOpen ((H \ A₁ ω) \ (WalkInf.verChart κ b jumps spec E k ω).dom) := by
    filter_upwards [hver, hgeo] with ω hv hg hl
    obtain ⟨M, hMA, -⟩ := hg hl
    have hd : ((WalkInf.verChart κ b jumps spec E k ω).dom : Set ℂ) = H \ A₁ ω := by
      rw [hv, ← hMA]
      exact M.dom_eq
    rw [hd]
    refine ⟨Subset.rfl, ?_⟩
    have e : (H \ A₁ ω) \ (H \ A₁ ω) = ∅ := by
      ext x
      simp only [Set.mem_sdiff, mem_empty_iff_false, iff_false]
      tauto
    rw [e]
    exact isOpen_empty
  have hm := S3.ae_eqOn_mean_of_kernelWord (hS.2.1 k) hc hh hu₀ hW.2.1
    (Lv.measurableSet_launch_pastSigma hb hS.1 hreg k) (hSide.mono fun _ hs hl => (hs hl).1) htr hW.2.2.2
    hA₁ hloc hmark hAD hg₁
  filter_upwards [hm, hver, hgeo, hSide] with ω hmω hv hg hsd hl w₁ hw₁ hrep z hz
  obtain ⟨M, hMA, hN⟩ := hg hl
  have he := hmω hl w₁ hw₁ hrep
  rw [hv] at he
  have he' : EqOn (fun z => w₁ z + u₀ z + chiC κ *
        (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2 z)
      (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 z))
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom := he
  have hzM : z ∈ H \ M.hull := by
    rw [hMA]
    exact hz
  have hzd : z ∈ ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom : Set ℂ) := by
    rw [M.dom_eq]
    exact hzM
  have hval := he' hzd
  simp only at hval
  have hfw := (ConformalImage.isMapOut_mapOut M.isHull).eqOn M.isHull M.mapOut hzM
  rw [hMA] at hfw
  have hlift := M.lift_eq_canonDerivLog hN hzM
  rw [hMA] at hlift
  -- the shift at `ω`
  have hsω : s ω = M.shift := by
    rw [hsdef]
    obtain ⟨ht, hev⟩ := tendsto_re_sub_fwd M
    refine Tendsto.limsup_eq (ht.congr' ?_)
    filter_upwards [hev] with n hn
    have hmem : (n : ℂ) * Complex.I ∈ (WalkInf.verChart κ b jumps spec E k ω).dom := by
      rw [hv]
      exact hn
    have hind : ({ω | (n : ℂ) * Complex.I ∈ (WalkInf.verChart κ b jumps spec E k ω).dom}.indicator
        (fun ω => (WalkInf.verChart κ b jumps spec E k ω).1 ((n : ℂ) * Complex.I)) ω) =
        (WalkInf.verChart κ b jumps spec E k ω).1 ((n : ℂ) * Complex.I) := Set.indicator_of_mem hmem _
    rw [hind, hv]
    rfl
  have hβω : β' ω = β ω := by
    simp only [hβ'def, (hsd hl).1, ↓reduceIte]
  simp only [Mo.hullChart_fwd, Mo.hullChart_lift]
  rw [RLC.OrdDet.mean_shiftW, hβω, hsω, hfw]
  have harg : (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 z + (M.shift : ℂ) -
      ((0 : ℝ) : ℂ) + ((-(M.shift) : ℝ) : ℂ) =
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 z := by
    push_cast
    ring
  rw [harg]
  rw [hlift] at hval
  linarith

/-! ### SB2(2): F3 at the first stage of the lower walk -/

omit mΩ [StandardBorelSpace Ω] in
/-- The filled version at a sample reads the set at that sample only. -/
theorem fillVer_congr {B B' : Ω → Set ℂ} {ω : Ω} (hBB' : B ω = B' ω) : fillVer B ω = fillVer B' ω := by
  unfold fillVer
  rw [hBB']

/-- **F3 at stage `0` of the lower walk** (the body of `Ms.SB2LowerRetainedMeanStatement` at `ℓ = 0`, for every cap;
Theorems 1.2–1.3). Before the lower walk has any piece the retained union is the filled history of the upper walk
through its instruction `k`: there is a sorted word `β₁`, measurable for the retained past, such that for every cap
`τ`, every hitting-measurable version `A₁` of the line family's retained set at stage `0` and every local-set mean of
`A₁`, almost surely on the stage event, every harmonic representative `w₁` satisfies
`w₁ + u₀ = (β₁ ω).mean ∘ g_{A₁} − χ(κ) · Im (canonDerivLog A₁)` on `ℍ ∖ A₁`. -/
theorem sb2LowerRetainedMean_zero (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k : ℕ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ β₁ : Ω → BoundaryWord,
      Measurable[aeSigma (Ms.stageMarks κ b jumps E u l k 0) P] β₁ ∧ Measurable β₁ ∧ (∀ ω, (β₁ ω).IsSorted) ∧
      ∀ (τ : ℝ≥0∞) (A₁ : Ω → Set ℂ), Measurable[mΩ, hittingSigma] A₁ →
        (∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0
            (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) 0 ω) ω) →
        ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₁ (centredField h u₀) P g₁ →
          ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k 0 →
            ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
              EqOn (fun z => w₁ z + u₀ z)
                (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ ω) 0).2.2 z)
                (H \ A₁ ω) := by
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hbc := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hup := hE' (Lu.upperSpec u l) hbc
  obtain ⟨β₁, hβm, hβs, hmean⟩ := exists_hullWord_mean h12p h13 hκ hκ4 hb hh hup (hreg' _) hu₀ k
  have hle : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ≤
      aeSigma (Ms.stageMarks κ b jumps E u l k 0) P :=
    le_sup_left.trans fun s hs => ⟨s, hs, Filter.EventuallyEq.rfl⟩
  refine ⟨β₁, hβm.mono hle le_rfl, hβm.mono (hup.2.1 k) le_rfl, hβs, fun τ A₁ hA₁ hA₁e g₁ hg₁ => ?_⟩
  have hA₁e' : ∀ᵐ ω ∂P, A₁ ω = fillVer (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k) ω := by
    filter_upwards [hA₁e] with ω he
    rw [he]
    exact fillVer_congr (by simp only [WalkLaw.stageSet_zero, union_empty])
  filter_upwards [hmean A₁ hA₁ hA₁e' g₁ hg₁, hrun (Lu.upperSpec u l) hbc] with ω hω hr hs
  refine hω ?_
  rw [hr (k + 1)]
  exact hs.1

end InteractingSLE.Theorem14.SB.Qr
