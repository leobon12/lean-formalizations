/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondMean
import InteractingSLE.WangWu.ReverseContactRevMean
import InteractingSLE.WangWu.PrefixLocalMean
import InteractingSLE.Spec.Sec7.PocketTraversalCoords
import InteractingSLE.Spec.Coupling.Assembly11Meas
import InteractingSLE.Spec.Sec7.Lemma71BStop

/-!
# The counterflow hull's mean as a Borel function of the history (item G2 of PROVE-GLUECOND)

Packet PROVE-GLUECOND2. Specification §4.2, proof of Lemma 4.7 (`source/spec/p097-144.md#lem-4.7-proof`, p. 118):
"the boundary conditions along `∂_U𝒮 ∪ η′([0, t])` agree with those of the conditional law of `h` given just
`η′|_{[0,t]}`". PROVE-GLUECOND identified the mean of the reflected counterflow hull `G = R(K′_t)` test function by test
function on the counterflow's own space. Here it is written **pathwise on the glued space, as an explicit function of
the counterflow history** (template: WangWu B13 `ReverseContactRevMean`), so that its boundary values can be read for
every glued sample.

* `cfStop t y` (the history stopped at `t`), `cfVLp`, `cfVRp` (the clamped force positions of the counterflow word,
  read geometrically from the regularized driver: `rightImg`), `cfU` (the word's bounded harmonic extension at those
  positions), and **`cfMeanQ u′ t y z = −𝔥′_t(R z) + u′(R z)`**, the explicit candidate, harmonic off `G` for **every**
  history (`harmonicOnNhd_cfMeanQ`).
* `cfTested`: a Borel functional of the history equal to `∫ cfMeanQ · φ` whenever `supp φ` misses `G`
  (`cfTested_eq`, `measurable_cfTested`), through the safe events of `Sec4` and `Coupling.measurable_stoppedPair`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull fwdMap)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.GlueCond

open WangWu hiding ratPt exists_ratPt_dist_lt continuousAt_negInv
open LawUnique Cond44Ref Sec7.StripSysField
open LocalSets (IsLocalSetMean)
open Sec4 (regPath regHull safeHist safeIdx safeUnion histStop)

/-! ### The counterflow word read from a history -/

section Hist

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)

/-- The history stopped at the constant time `t` (the stop used by `hullAt`). -/
abbrev cfStop (t : ℝ≥0) (y : HistorySpace 0 0) : HistorySpace 0 0 := Sec4.stopHistory (Aux50Hit.cstop t) y

theorem histStop_cfStop (t : ℝ≥0) (y : HistorySpace 0 0) : histStop (cfStop t y) = t :=
  Sec4.stopHistory_fst_toNNReal y

theorem measurable_cfStop (t : ℝ≥0) : Measurable (cfStop t) :=
  Sec4.measurable_stopHistory measurable_const

/-- **The clamped left force positions of the counterflow word on histories** (absolute): the regularized driver
plus the clamped centred geometric image of the initial mark. -/
def cfVLp (i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps jumps) 0)) (s : ℝ≥0)
    (γ : HistorySpace 0 0) : ℝ :=
  regPath γ s + min 0 (cfPosL κ b jumps (regPath γ) s i)

/-- **The clamped right force positions of the counterflow word on histories** (absolute). -/
def cfVRp (i : Fin (flowLineNR (counterflowData κ b) (counterflowJumps jumps) 0)) (s : ℝ≥0)
    (γ : HistorySpace 0 0) : ℝ :=
  regPath γ s + max 0 (cfPosR κ b jumps (regPath γ) s i)

theorem measurable_rightImg_regPath (sg : ℝ) (x : ℝ) (s : ℝ≥0) :
    Measurable fun γ : HistorySpace 0 0 =>
      MartChar.RealFlow.rightImg (fun r => sg * Ito.rpath (regPath γ) r) x s := by
  have h := Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable
    (𝓕 := Sec4.histFiltration (nL := 0) (nR := 0)) (W := fun r γ => sg * regPath γ r)
    (fun t => ((Sec4.measurable_regPath_apply t).const_mul sg).mono (Sec4.histFiltration_apply t).le le_rfl)
    (fun γ => (Sec4.continuous_regPath γ).const_smul sg) (x := fun _ => x) measurable_const s
  exact h.mono (Sec4.histFiltration_apply s).ge le_rfl

theorem measurable_cfPosL (s : ℝ≥0) (i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps jumps) 0)) :
    Measurable fun γ : HistorySpace 0 0 => cfPosL κ b jumps (regPath γ) s i := by
  have h := measurable_rightImg_regPath (-1) (-flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0 i) s
  simp only [neg_one_mul] at h
  exact h.neg.sub (Sec4.measurable_regPath_apply s)

theorem measurable_cfPosR (s : ℝ≥0) (i : Fin (flowLineNR (counterflowData κ b) (counterflowJumps jumps) 0)) :
    Measurable fun γ : HistorySpace 0 0 => cfPosR κ b jumps (regPath γ) s i := by
  have h := measurable_rightImg_regPath 1 (flowLineXR (counterflowData κ b) (counterflowJumps jumps) 0 i) s
  simp only [one_mul] at h
  exact h.sub (Sec4.measurable_regPath_apply s)

theorem measurable_cfVLp (i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps jumps) 0)) (s : ℝ≥0) :
    Measurable (cfVLp κ b jumps i s) :=
  (Sec4.measurable_regPath_apply s).add (measurable_const.min (measurable_cfPosL κ b jumps s i))

theorem measurable_cfVRp (i : Fin (flowLineNR (counterflowData κ b) (counterflowJumps jumps) 0)) (s : ℝ≥0) :
    Measurable (cfVRp κ b jumps i s) :=
  (Sec4.measurable_regPath_apply s).add (measurable_const.max (measurable_cfPosR κ b jumps s i))

theorem continuous_rightImg_regPath (sg : ℝ) (x : ℝ) (γ : HistorySpace 0 0) :
    Continuous fun s : ℝ≥0 => MartChar.RealFlow.rightImg (fun r => sg * Ito.rpath (regPath γ) r) x s :=
  (MartChar.RealFlow.continuousOn_rightImg ((Sec4.continuous_rpath_regPath γ).const_smul sg) x).comp_continuous
    NNReal.continuous_coe fun t => t.coe_nonneg

theorem continuous_cfPosL (i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps jumps) 0))
    (γ : HistorySpace 0 0) : Continuous fun s => cfPosL κ b jumps (regPath γ) s i := by
  have h := continuous_rightImg_regPath (-1) (-flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0 i) γ
  simp only [neg_one_mul] at h
  exact h.neg.sub (Sec4.continuous_regPath γ)

theorem continuous_cfPosR (i : Fin (flowLineNR (counterflowData κ b) (counterflowJumps jumps) 0))
    (γ : HistorySpace 0 0) : Continuous fun s => cfPosR κ b jumps (regPath γ) s i := by
  have h := continuous_rightImg_regPath 1 (flowLineXR (counterflowData κ b) (counterflowJumps jumps) 0 i) γ
  simp only [one_mul] at h
  exact h.sub (Sec4.continuous_regPath γ)

theorem continuous_cfVLp (i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps jumps) 0))
    (γ : HistorySpace 0 0) : Continuous fun s => cfVLp κ b jumps i s γ :=
  (Sec4.continuous_regPath γ).add (continuous_const.min (continuous_cfPosL κ b jumps i γ))

theorem continuous_cfVRp (i : Fin (flowLineNR (counterflowData κ b) (counterflowJumps jumps) 0))
    (γ : HistorySpace 0 0) : Continuous fun s => cfVRp κ b jumps i s γ :=
  (Sec4.continuous_regPath γ).add (continuous_const.max (continuous_cfPosR κ b jumps i γ))

end Hist

/-! ### The tested mean at the recorded stop, Borel in the history -/

section Pair

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)

/-- The tested canonical mean of the counterflow word and the energy at the recorded stop, along the regularized
driver with the geometric force positions. -/
def cfRegPair (φ : ℂ → ℝ) (γ : HistorySpace 0 0) : ℝ × ℝ :=
  ((∫ z, Coupling.meanCan (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps) (regPath γ)
      (fun i s => cfVLp κ b jumps i s γ) (fun i s => cfVRp κ b jumps i s γ) (histStop γ) z * φ z),
    loewnerGreenEnergy (Ito.rpath (regPath γ)) (histStop γ) φ)

open scoped Classical in
/-- The pair on the `n`-th safe event of `supp φ`, `(0, 0)` off it. -/
def cfSafePair (φ : ℂ → ℝ) (n : ℕ) (γ : HistorySpace 0 0) : ℝ × ℝ :=
  if γ ∈ safeHist (tsupport φ) (1 / ((n : ℝ) + 1)) n then cfRegPair κ b jumps φ γ else (0, 0)

/-- **On each safe event the tested counterflow mean at the stop is measurable** (`Sec4.measurable_safePair` with the
geometric force positions). -/
theorem measurable_cfSafePair {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφH : tsupport φ ⊆ H) (n : ℕ) : Measurable (cfSafePair κ b jumps φ n) := by
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have h := Coupling.measurable_stoppedPair (κ := 16 / κ) (ρL := cfRhoL κ b jumps) (ρR := cfRhoR κ b jumps)
    (𝓖 := Sec4.histFiltration (nL := 0) (nR := 0)) (ζ := fun _ => ⊤) (W := Sec4.regProc)
    (VL := cfVLp κ b jumps) (VR := cfVRp κ b jumps) (G := safeHist (tsupport φ) (1 / ((n : ℝ) + 1)) n)
    Sec4.adaptedBefore_regProc (fun i => Sec4.adaptedBefore_of_measurable (measurable_cfVLp κ b jumps i))
    (fun i => Sec4.adaptedBefore_of_measurable (measurable_cfVRp κ b jumps i))
    (fun γ _ => Sec4.continuousOn_regProc γ)
    (fun γ _ => ⟨fun i => (continuous_cfVLp κ b jumps i γ).continuousOn,
      fun i => (continuous_cfVRp κ b jumps i γ).continuousOn⟩)
    (Sec4.measurableSet_safeHist hφH hδ n) hφc hφs hφH hδ (ρ := histStop) Sec4.isStoppingTime_histStop
    (N := n) (σ₀ := fun _ => (n : ℝ≥0)) (fun γ hγ => Sec4.isSafeAt_of_mem_safeHist hφH hδ hγ)
  exact h.mono (Sec4.isStoppingTime_histStop.measurableSpace_le) le_rfl

/-- **The counterflow word's bounded harmonic extension at the positions read from the history at time `t`.** -/
def cfU (t : ℝ≥0) (γ : HistorySpace 0 0) : ℂ → ℝ :=
  Classical.choose (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
    (cfPosL κ b jumps (regPath γ) t) (cfPosR κ b jumps (regPath γ) t))

theorem isBoundedHarmonicExtension_cfU (t : ℝ≥0) (γ : HistorySpace 0 0) :
    IsBoundedHarmonicExtension (forceBoundaryData (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
      (cfPosL κ b jumps (regPath γ) t) (cfPosR κ b jumps (regPath γ) t))
      (forceJumpSet (cfPosL κ b jumps (regPath γ) t) (cfPosR κ b jumps (regPath γ) t)) (cfU κ b jumps t γ) :=
  Classical.choose_spec (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
    (cfPosL κ b jumps (regPath γ) t) (cfPosR κ b jumps (regPath γ) t))

/-- Off the hull the frozen coupling mean with `cfU` is the canonical mean with the clamped positions. -/
theorem couplingMean_cfU_eq_meanCan (t : ℝ≥0) (γ : HistorySpace 0 0) {z : ℂ}
    (hz : fwdMap (Ito.rpath (regPath γ)) t z ∈ H) :
    couplingMean (16 / κ) (Ito.rpath (regPath γ)) t (cfU κ b jumps t γ) z =
      Coupling.meanCan (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps) (regPath γ)
        (fun i s => cfVLp κ b jumps i s γ) (fun i s => cfVRp κ b jumps i s γ) t z := by
  rw [couplingMean, Coupling.meanCan,
    Sec4.eq_meanHarmonic_of_isBoundedHarmonicExtension _ _ _ (isBoundedHarmonicExtension_cfU κ b jumps t γ) hz]
  simp only [cfVLp, cfVRp, add_sub_cancel_left]

end Pair

/-! ### The explicit candidate and its Borel tested form -/

section Cand

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)

/-- **The explicit pathwise mean of the reflected counterflow hull**, read from the history:
`z ↦ −𝔥′_t(R z) + u′(R z)`, with `𝔥′_t` the frozen coupling mean of the counterflow word at `16/κ` along the
regularized driver stopped at `t`, at the positions read from that driver. -/
def cfMeanQ (u' : ℂ → ℝ) (t : ℝ≥0) (y : HistorySpace 0 0) (z : ℂ) : ℝ :=
  -couplingMean (16 / κ) (Ito.rpath (regPath (cfStop t y))) t (cfU κ b jumps t (cfStop t y)) (negInv z) +
    u' (negInv z)

theorem fwdHull_subset_hullAt (t : ℝ≥0) (y : HistorySpace 0 0) :
    fwdHull (Ito.rpath (regPath (cfStop t y))) t ⊆ hullAt t y := by
  intro z hz
  refine ⟨subset_closure ?_, hz.1⟩
  rw [histStop_cfStop]
  exact hz

/-- **The explicit candidate is harmonic off the reflected hull, for every history.** -/
theorem harmonicOnNhd_cfMeanQ {u' : ℂ → ℝ} (hu' : InnerProductSpace.HarmonicOnNhd u' H) (t : ℝ≥0)
    (y : HistorySpace 0 0) :
    InnerProductSpace.HarmonicOnNhd (cfMeanQ κ b jumps u' t y) (H \ cfHullQ t y) := by
  set F := fwdHull (Ito.rpath (regPath (cfStop t y))) t with hF
  have hw := Sec4.continuous_rpath_regPath (cfStop t y)
  have hO : IsOpen (H \ F) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw t.coe_nonneg
  have h1 := harmonicOnNhd_comp_negInv hO sdiff_subset
    (Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := 16 / κ) hw t.coe_nonneg
      (isBoundedHarmonicExtension_cfU κ b jumps t (cfStop t y)).1)
  have h2 := harmonicOnNhd_comp_negInv QuantumZipper.isOpen_H subset_rfl hu'
  have hsub : H \ cfHullQ t y ⊆ negInv '' (H \ F) := by
    rw [cfHullQ, H_diff_image_negInv]
    exact image_mono (sdiff_subset_sdiff_right (fwdHull_subset_hullAt t y))
  have hsub2 : negInv '' (H \ F) ⊆ negInv '' H := image_mono sdiff_subset
  intro z hz
  exact (h1 z (hsub hz)).neg.add (h2 z (hsub2 (hsub hz)))

/-- **The Borel tested candidate**: minus the tested counterflow mean at the first safe level of the pushed test
function, plus the pairing of `u′ ∘ R`. -/
def cfTested (u' : ℂ → ℝ) (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) (y : HistorySpace 0 0) : ℝ :=
  -(cfSafePair κ b jumps (retPush φ) (safeIdx (retPush φ) (cfStop t y)) (cfStop t y)).1 +
    ∫ z, u' (negInv z) * φ z

theorem measurable_cfTested (u' : ℂ → ℝ) (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    Measurable (cfTested κ b jumps u' t φ) := by
  set ψ := retPush φ
  have hψH : tsupport ψ ⊆ H := ψ.tsupport_subset
  have hF : Measurable fun q : HistorySpace 0 0 × ℕ => cfSafePair κ b jumps ψ q.2 q.1 :=
    measurable_from_prod_countable_left fun n =>
      measurable_cfSafePair κ b jumps ψ.continuous ψ.hasCompactSupport hψH n
  have hG : Measurable fun y : HistorySpace 0 0 => (cfStop t y, safeIdx (⇑ψ) (cfStop t y)) :=
    (measurable_cfStop t).prodMk ((Sec4.measurable_safeIdx hψH).comp (measurable_cfStop t))
  exact ((measurable_fst.comp (hF.comp hG)).neg).add_const _

/-- **The Borel tested candidate is the tested explicit mean** whenever `supp φ` misses the reflected hull. -/
theorem cfTested_eq {u' : ℂ → ℝ} (hu' : ContinuousOn u' H) (t : ℝ≥0) (y : HistorySpace 0 0)
    {φ : TestOn upperHalfPlaneOpens} (hdis : Disjoint (tsupport φ) (cfHullQ t y)) :
    cfTested κ b jumps u' t φ y = ∫ z, cfMeanQ κ b jumps u' t y z * φ z := by
  set y' := cfStop t y with hy'
  set ψ := retPush φ with hψ
  set F := fwdHull (Ito.rpath (regPath y')) t with hF
  set cM := couplingMean (16 / κ) (Ito.rpath (regPath y')) t (cfU κ b jumps t y') with hcM
  have hw := Sec4.continuous_rpath_regPath y'
  have hψH : tsupport ψ ⊆ H := ψ.tsupport_subset
  -- the pushed test function misses the hull
  have hnotF : ∀ w ∈ tsupport ψ, w ∉ F := by
    intro w hw' hwF
    obtain ⟨v, hv, rfl⟩ := tsupport_pushTest_return_subset φ hw'
    refine Set.disjoint_left.1 hdis hv ⟨negInv v, fwdHull_subset_hullAt t y hwF, Sec7.StripSysField.negInv_negInv v⟩
  have halive : ∀ z ∈ tsupport ψ, ∃ v, QuantumZipper.IsForwardSol (Ito.rpath (regPath y')) z (histStop y') v := by
    intro z hz
    rw [histStop_cfStop]
    exact QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull t.coe_nonneg (hψH hz) (hnotF z hz)
  have hU : y' ∈ safeUnion (⇑ψ) :=
    mem_iUnion.2 (Sec4.eventually_mem_safeHist ψ.hasCompactSupport hψH halive).exists
  have hmem := Sec4.mem_safeHist_safeIdx hU
  have hpair : (cfSafePair κ b jumps ψ (safeIdx (⇑ψ) y') y').1 = ∫ w, cM w * ψ w := by
    rw [cfSafePair]
    simp only [hmem, ↓reduceIte]
    rw [cfRegPair, histStop_cfStop]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    by_cases hwψ : ψ w = 0
    · simp only [hwψ, mul_zero]
    · have hws : w ∈ tsupport ψ := subset_tsupport _ hwψ
      simp only [hcM]
      rw [couplingMean_cfU_eq_meanCan κ b jumps t y'
        (QuantumZipper.FwdHolo.mapsTo_fwdMap hw t.coe_nonneg ⟨hψH hws, hnotF w hws⟩)]
  have hcv := Chart.integral_mul_pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ cM
  simp only [infinityReturnChart_inv_eq] at hcv
  -- integrability on the support of `φ`
  have hO : IsOpen (H \ F) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw t.coe_nonneg
  have h1 := harmonicOnNhd_comp_negInv hO sdiff_subset
    (Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := 16 / κ) hw t.coe_nonneg
      (isBoundedHarmonicExtension_cfU κ b jumps t y').1)
  have hφO : tsupport φ ⊆ negInv '' (H \ F) := by
    intro z hz
    have hzH : z ∈ H := φ.tsupport_subset hz
    refine ⟨negInv z, ⟨WangWu.negInv_mem_H hzH, fun hzF => ?_⟩, Sec7.StripSysField.negInv_negInv z⟩
    exact Set.disjoint_left.1 hdis hz ⟨negInv z, fwdHull_subset_hullAt t y hzF, Sec7.StripSysField.negInv_negInv z⟩
  have hc1 : ContinuousOn (fun z => cM (negInv z)) (negInv '' (H \ F)) :=
    fun z hz => (h1 z hz).1.continuousAt.continuousWithinAt
  have i1 := Coupling.MartMeans2.integrable_mul_test_of_continuousOn hc1 φ hφO
  have hc2 : ContinuousOn (fun z => u' (negInv z)) H := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => by
      rw [h] at hz
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)
    exact (hu' _ (WangWu.negInv_mem_H hz)).comp_of_eq
      (WangWu.continuousAt_negInv hz0).continuousWithinAt (fun w hw => WangWu.negInv_mem_H hw) rfl
  have i2 := Coupling.MartMeans2.integrable_mul_test_of_continuousOn hc2 φ φ.tsupport_subset
  have i1' : Integrable (fun z => -(cM (negInv z) * φ z)) := i1.neg
  rw [cfTested, hpair, hcv, ← integral_neg, ← integral_add i1' i2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [cfMeanQ, hcM]
  ring

end Cand

/-! ### On a good counterflow sample the history determines the counterflow mean -/

section Good

variable {Ω₂ : Type*} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞} {ω : Ω₂}

theorem regPath_cfStop_cfHistory (hζ : ζ₂ ω = ⊤) (hw0 : W₂ 0 ω = 0) (hw : Continuous fun t => W₂ t ω)
    (t : ℝ≥0) : regPath (cfStop t (cfHistory W₂ ζ₂ ω)) = fun s => W₂ (min s t) ω := by
  have hg : Aux50Hit.IsGoodPath W₂ (Fin.elim0 : Fin 0 → ℝ≥0 → Ω₂ → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω₂ → ℝ) ζ₂ ω :=
    ⟨hζ, hw0, hw.continuousOn, fun i => i.elim0, fun i => i.elim0⟩
  exact Aux50Hit.regPath_stopHistory hg (Aux50Hit.cstop t)

theorem eqOn_rpath_cfStop_cfHistory (hζ : ζ₂ ω = ⊤) (hw0 : W₂ 0 ω = 0) (hw : Continuous fun t => W₂ t ω)
    (t : ℝ≥0) : EqOn (Ito.rpath (regPath (cfStop t (cfHistory W₂ ζ₂ ω)))) (fun s : ℝ => W₂ s.toNNReal ω)
      (Icc 0 t) := by
  intro s hs
  simp only [Ito.rpath, regPath_cfStop_cfHistory hζ hw0 hw t]
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]

theorem cfPosL_cfStop_cfHistory (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (hζ : ζ₂ ω = ⊤) (hw0 : W₂ 0 ω = 0)
    (hw : Continuous fun t => W₂ t ω) (t : ℝ≥0) :
    cfPosL κ b jumps (regPath (cfStop t (cfHistory W₂ ζ₂ ω))) t = cfPosL κ b jumps (W₂ · ω) t := by
  have hE := eqOn_rpath_cfStop_cfHistory hζ hw0 hw t
  have hc : Continuous fun s : ℝ => -Ito.rpath (W₂ · ω) s := (hw.comp continuous_real_toNNReal).neg
  have ht : regPath (cfStop t (cfHistory W₂ ζ₂ ω)) t = W₂ t ω := by
    rw [regPath_cfStop_cfHistory hζ hw0 hw t]
    simp only [min_self]
  funext i
  simp only [cfPosL]
  rw [Sec7.Lemma71B.rightImg_congr hc t.coe_nonneg (fun s hs => by simp only [hE hs]; rfl), ht]

theorem cfPosR_cfStop_cfHistory (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (hζ : ζ₂ ω = ⊤) (hw0 : W₂ 0 ω = 0)
    (hw : Continuous fun t => W₂ t ω) (t : ℝ≥0) :
    cfPosR κ b jumps (regPath (cfStop t (cfHistory W₂ ζ₂ ω))) t = cfPosR κ b jumps (W₂ · ω) t := by
  have hE := eqOn_rpath_cfStop_cfHistory hζ hw0 hw t
  have hc : Continuous fun s : ℝ => Ito.rpath (W₂ · ω) s := hw.comp continuous_real_toNNReal
  have ht : regPath (cfStop t (cfHistory W₂ ζ₂ ω)) t = W₂ t ω := by
    rw [regPath_cfStop_cfHistory hζ hw0 hw t]
    simp only [min_self]
  funext i
  simp only [cfPosR]
  rw [Sec7.Lemma71B.rightImg_congr hc t.coe_nonneg (fun s hs => by simp only [hE hs]; rfl), ht]

/-- **On a good counterflow sample the explicit candidate read from the history is the counterflow mean**:
`−𝔥′_t(R z) + u′(R z)` along the actual driver, with any bounded harmonic extension `uG` at the actual positions, off
the reflected hull. -/
theorem cfMeanQ_cfHistory (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (u' : ℂ → ℝ) (hζ : ζ₂ ω = ⊤)
    (hw0 : W₂ 0 ω = 0) (hw : Continuous fun t => W₂ t ω) (t : ℝ≥0) {uG : ℂ → ℝ}
    (huG : IsBoundedHarmonicExtension (forceBoundaryData (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
        (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t))
      (forceJumpSet (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t)) uG)
    {z : ℂ} (hz : z ∈ H \ cfHullQ t (cfHistory W₂ ζ₂ ω)) :
    -couplingMean (16 / κ) (fun s : ℝ => W₂ s.toNNReal ω) t uG (negInv z) + u' (negInv z) =
      cfMeanQ κ b jumps u' t (cfHistory W₂ ζ₂ ω) z := by
  set y' := cfStop t (cfHistory W₂ ζ₂ ω) with hy'
  have hE := eqOn_rpath_cfStop_cfHistory hζ hw0 hw t
  have hWc : Continuous fun s : ℝ => W₂ s.toNNReal ω := hw.comp continuous_real_toNNReal
  -- `R z` is off the hull of the actual driver
  have hzH : z ∈ H := hz.1
  have hRz : negInv z ∈ H \ fwdHull (fun s : ℝ => W₂ s.toNNReal ω) t := by
    refine ⟨WangWu.negInv_mem_H hzH, fun hK => hz.2 ?_⟩
    rw [cfHullQ, hullAt_cfHistory hζ hw0 hw t]
    exact ⟨negInv z, hK, Sec7.StripSysField.negInv_negInv z⟩
  have ha := QuantumZipper.FwdHolo.mapsTo_fwdMap hWc t.coe_nonneg hRz
  have hu1 := Sec4.eq_meanHarmonic_of_isBoundedHarmonicExtension _ _ _ huG ha
  have hu2 := Sec4.eq_meanHarmonic_of_isBoundedHarmonicExtension _ _ _
    (isBoundedHarmonicExtension_cfU κ b jumps t y') ha
  rw [cfPosL_cfStop_cfHistory κ b jumps hζ hw0 hw t, cfPosR_cfStop_cfHistory κ b jumps hζ hw0 hw t] at hu2
  have hcm : couplingMean (16 / κ) (fun s : ℝ => W₂ s.toNNReal ω) t uG (negInv z) =
      couplingMean (16 / κ) (fun s : ℝ => W₂ s.toNNReal ω) t (cfU κ b jumps t y') (negInv z) := by
    simp only [couplingMean, hu1, hu2]
  rw [cfMeanQ, hcm, Sec7.Lemma71B.couplingMean_congr t.coe_nonneg hE]

end Good

/-! ### The counterflow hull's mean on the glued space, pathwise -/

section GluePath

open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

/-- **Item G2: the counterflow hull's mean on the glued space, pathwise in the history** (Lemma 4.7's "boundary
conditions along `∂_U𝒮 ∪ η′([0, t])` … of the conditional law of `h` given just `η′|_{[0,t]}`", chart `Q`). In the
setting of `isLocalSet_union_glue`, with `b = 𝔟_F − π/2 χ` the data of `h − π/2 χ` and `u′` the chart-`R` extension
of the counterflow word's data: the reflected counterflow hull `G = R(K′_t)` read from the history has a local-set mean
`g` for the centred field `h − 𝔥₀` on the glued space, and **almost surely, for every test function supported off
`G`, `g p φ = ∫ cfMeanQ u′ t p.2 · φ`**, with the explicit candidate `cfMeanQ` read from the counterflow history
alone. -/
theorem exists_isLocalSetMean_cfHullQ_path (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (t : ℝ≥0)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR)) u') :
    ∃ g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2) (fun p => cenT κ u₀ (cfField κ (h p.1)))
        (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) g ∧
      ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ t p.2 →
          g p φ = ∫ z, cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ))
            (forceJumpFinset xL xR) u' t p.2 z * φ z := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  set c : ℝ := -(π / 2 * chiC κ) with hc
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + c with hbdef
  set jumps := forceJumpFinset xL xR with hjumps
  have hb : IsPiecewiseConstantBoundaryData b jumps := isPiecewiseConstant_forceData κ ρL ρR xL xR c
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hh₂m := CfRegQ.measurable_of_isCenteredCounterflowDriver hcf
  have hDm := measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)
  have hhh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) := ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hhh c
  rw [← coe_forceJumpFinset] at hh'
  have hh₂ : IsGFFWithBoundaryData P₂ h₂ b jumps := CfRegQ.isGFFWithBoundaryData_of_map_eq hh' hh₂m hlaw
  have hu_b : IsBoundedHarmonicExtension b jumps (fun z => u₀ z + c) := by
    rw [hjumps, coe_forceJumpFinset]
    exact isBoundedHarmonicExtension_add_const hu₀ c
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hu'c : ContinuousOn u' H := fun z hz => (hu'.1 z hz).1.continuousAt.continuousWithinAt
  have hπ₂ : Measurable (cfProj.{u} h₂ W₂ ζ₂) := measurable_up.comp (hh₂m.prodMk hDm)
  set μ := P₂.map (cfProj.{u} h₂ W₂ ζ₂) with hμdef
  have hglue := glueMeasure_map_cfProj hXm hh₂m hDm hlaw hk
  set slit : CfSpace.{u} → Set ℂ := fun q => cfHullQ t q.down.2 with hslit
  set fld : CfSpace.{u} → DistOn upperHalfPlaneOpens := fun q => cenT κ u₀ q.down.1 with hfld
  have hslitm : Measurable[_, hittingSigma] slit := (measurable_cfHullQ t).comp (measurable_snd.comp measurable_down)
  have hfldm : Measurable fld := (measurable_cenT κ u₀).comp (measurable_fst.comp measurable_down)
  -- the counterflow hull is local on the canonical space, and the centred field is a zero-boundary GFF there
  have hG₂ := isLocalSet_cfHullQ_cenT hcf hreg₂ hu₀.1 t
  have hpairm : Measurable fun q : CfSpace.{u} => (slit q, fld q) := hslitm.prodMk hfldm
  have hloc : IsLocalSet slit fld μ := by
    refine IsLocalSet.of_map_eq hG₂ hpairm.aemeasurable (ae_of_all _ fun q => cfHullQ_relClosed t q.down.2) ?_
    rw [hμdef, Measure.map_map hpairm hπ₂]
    rfl
  have hZglue : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω × HistorySpace 0 0 => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) hXm) := by
    have e : (fun p : Ω × HistorySpace 0 0 => cenT κ u₀ (cfField κ (h p.1))) =
        fun p => WholeField.centredField h u₀ p.1 := funext fun p => cenT_cfField κ u₀ (h p.1)
    rw [e]
    exact isZeroBoundaryGFF_comp_of_map_eq (g := WholeField.centredField h u₀) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hXm) (WholeField.isZeroBoundaryGFF_centredField hC hu₀)
  have hZ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens fld μ := by
    refine ⟨hfldm, ?_⟩
    rw [hμdef, ← hglue]
    exact Restart.isZBGFFProcess_map (measurable_glueProjCf hXm)
      (fun φ => (LQGMetric.measurable_distOn_apply φ).comp hfldm) hZglue.process
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hZ hslitm hloc
  have hgm : Measurable g := hg.1.mono (LocalSets.germSigma_le hslitm hfldm) le_rfl
  -- the identification on the counterflow's space
  set uG : Ω₂ → ℂ → ℝ := fun ω => Classical.choose (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps)
    (cfRhoR κ b jumps) (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t)) with huGdef
  have huG : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
        (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t))
      (forceJumpSet (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t)) (uG ω) := fun ω =>
    Classical.choose_spec (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps)
      (cfRhoR κ b jumps) (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t))
  obtain ⟨g₂, hg₂, hid₂⟩ := exists_isLocalSetMean_cfHullQ hκ hb hh₂ hcf hreg₂ hu_b hu' t huG
  have hgc : IsLocalSetMean (fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) (fun ω => cenT κ u₀ (h₂ ω)) P₂
      (fun ω => g (cfProj h₂ W₂ ζ₂ ω)) :=
    IsLocalSetMean.comp hπ₂ rfl hslitm hfldm hg
  have e : (fun ω => cenT κ u₀ (h₂ ω)) = fun ω => h₂ ω - smoothDist upperHalfPlaneOpens (fun z => u₀ z + c) :=
    funext fun ω => cenT_eq_sub κ hu₀c (h₂ ω)
  rw [e] at hgc
  have hAm : Measurable[mΩ₂, hittingSigma] fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω) :=
    (measurable_cfHullQ t).comp hDm
  have hFm : Measurable fun ω => h₂ ω - smoothDist upperHalfPlaneOpens (fun z => u₀ z + c) :=
    (WholeField.measurable_sub_dist _).comp hh₂m
  -- test function by test function, the Borel tested candidate on the canonical space
  have hφ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ q ∂μ,
      Disjoint (tsupport φ) (slit q) → g q φ = cfTested κ b jumps u' t φ q.down.2 := by
    intro φ
    have hS : MeasurableSet {q : CfSpace.{u} |
        Disjoint (tsupport φ) (slit q) → g q φ = cfTested κ b jumps u' t φ q.down.2} := by
      have h1 : MeasurableSet {q : CfSpace.{u} | Disjoint (tsupport φ) (slit q)} :=
        measurableSet_disjoint_of_relClosed hslitm (fun q => cfHullQ_relClosed t q.down.2)
          φ.hasCompactSupport.isCompact φ.tsupport_subset
      have h2 : MeasurableSet {q : CfSpace.{u} | g q φ = cfTested κ b jumps u' t φ q.down.2} :=
        measurableSet_eq_fun ((LQGMetric.measurable_distOn_apply φ).comp hgm)
          ((measurable_cfTested κ b jumps u' t φ).comp (measurable_snd.comp measurable_down))
      have e2 : {q : CfSpace.{u} | Disjoint (tsupport φ) (slit q) → g q φ = cfTested κ b jumps u' t φ q.down.2} =
          {q | Disjoint (tsupport φ) (slit q)}ᶜ ∪ {q | g q φ = cfTested κ b jumps u' t φ q.down.2} := by
        ext q
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
      rw [e2]
      exact h1.compl.union h2
    rw [hμdef, ae_map_iff hπ₂.aemeasurable hS]
    filter_upwards [LocalSets.IsLocalSetMean.ae_apply_eq hAm hFm hgc hg₂ φ, hid₂, hreg₂] with ω e1 e2 hω hdis
    have hφs : tsupport φ ⊆ H \ cfHullQ t (cfHistory W₂ ζ₂ ω) := fun z hz =>
      ⟨φ.tsupport_subset hz, fun hzG => Set.disjoint_left.1 hdis hz hzG⟩
    show g (cfProj h₂ W₂ ζ₂ ω) φ = cfTested κ b jumps u' t φ (cfHistory W₂ ζ₂ ω)
    rw [e1, e2 φ hφs, cfTested_eq κ b jumps hu'c t (cfHistory W₂ ζ₂ ω) (φ := φ) hdis]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : φ z = 0
    · simp only [hz, mul_zero]
    · show (-couplingMean (16 / κ) (fun s : ℝ => W₂ s.toNNReal ω) t (uG ω) (negInv z) + u' (negInv z)) * φ z =
        cfMeanQ κ b jumps u' t (cfHistory W₂ ζ₂ ω) z * φ z
      rw [cfMeanQ_cfHistory κ b jumps u' hω.1 hω.2.1 hω.2.2 t (huG ω) (hφs (subset_tsupport _ hz))]
  -- all test functions at once, on the canonical space
  have hall : ∀ᵐ q ∂μ, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ slit q →
      g q φ = ∫ z, cfMeanQ κ b jumps u' t q.down.2 z * φ z := by
    refine ae_forall_apply_eq_of_forall_ae hg.2.1 (ae_of_all _ fun q => (cfHullQ_relClosed t q.down.2).2)
      (ae_of_all _ fun q => harmonicOnNhd_cfMeanQ κ b jumps hu'.1 t q.down.2) fun φ => ?_
    filter_upwards [hφ φ] with q hq hφs
    have hdis : Disjoint (tsupport φ) (slit q) := Set.disjoint_left.2 fun z hz hzG => (hφs hz).2 hzG
    rw [hq hdis, cfTested_eq κ b jumps hu'c t _ hdis]
  refine ⟨fun p => g (glueProjCf (fun ω => cfField κ (h ω)) p),
    IsLocalSetMean.comp (measurable_glueProjCf hXm) hglue hslitm hfldm hg, ?_⟩
  have hall' := hall
  rw [hμdef, ← hglue] at hall'
  exact ae_of_ae_map (measurable_glueProjCf hXm).aemeasurable hall'


/-- **The union mean of the two hulls on the glued space, with both single-curve means explicit** (Lemma 4.7, p. 118:
Propositions 3.7 and 3.8 "together tell us that the boundary data for the conditional law of `h` given both … agree
with those of the conditional law given just `η|_{[0,τ]}` (resp. `η′|_{[0,t]}`) alone"; the B13/B14 form). For every
local-set mean `g` of `A ∪ G` (`A = K_q` the flow hull read from the flow history, `G = R(K′_t)` the reflected
counterflow hull read from the counterflow history), almost surely `g` has a harmonic representative `w` off `A ∪ G`
with `w − (𝔥_q − 𝔥₀) → 0` near `A ∪ ℝ` away from `G`, and `w − cfMeanQ u′ t p.2 → 0` near `G ∪ ℝ` away from `A`. -/
theorem ae_union_mean_cfGlue (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR)) u')
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω))
      (forceJumpSet (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)) (u ω))
    {g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
      (fun p => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) g) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) → g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ hullAt q (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, cfHullQ t p.2 ∩ ball z₀ r ⊆ hullAt q (killedHistory W VL VR ζ p.1)) →
          Tendsto (fun z => w z - (couplingMean κ (fun s : ℝ => W s.toNNReal p.1) q (u p.1) z - u₀ z))
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ cfHullQ t p.2 ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, hullAt q (killedHistory W VL VR ζ p.1) ∩ ball z₀ r ⊆ cfHullQ t p.2) →
          Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ))
              (forceJumpFinset xL xR) u' t p.2 z)
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) := by
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  obtain ⟨gA, hgA, hidA⟩ := exists_isLocalSetMean_flowHull_glue (k := k) hC hκ hζ hu₀ q hu
  obtain ⟨gG, hgG, hidG⟩ := exists_isLocalSetMean_cfHullQ_path hC hκ hcf hreg₂ hlaw hk hu₀ t hu'
  -- the flow candidate is harmonic off the flow hull
  have hharmA : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd
      (fun z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (u ω) z - u₀ z)
      (H \ hullAt q (killedHistory W VL VR ζ ω)) := by
    filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hgω
    have hK : hullAt q (killedHistory W VL VR ζ ω) = fwdHull (Ito.rpath fun t => W t ω) q :=
      Aux50Hit.regHull_stopHistory_cstop hgω q
    rw [hK]
    have h1 := Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := κ) hgω.continuous_rpath q.coe_nonneg (hu ω).1
    intro z hz
    exact (h1 z hz).sub (hu₀.1 z hz.1)
  have hharmA' := ae_glue_fst (μ := P) k hXm hharmA
  filter_upwards [ae_union_boundary_cfGlue hC hζ hcf hreg₂ hlaw hk hu₀ q t hg hgA hgG, hidA, hidG, hharmA']
    with p hp hA hG hhA
  exact hp _ _ hhA hA (harmonicOnNhd_cfMeanQ _ _ _ hu'.1 t p.2) hG

end GluePath

end InteractingSLE.Sec5.GlueCond
