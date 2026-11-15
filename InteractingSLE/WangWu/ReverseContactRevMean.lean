/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactGood
import InteractingSLE.Spec.Exist.TransferHist

/-!
# The explicit reverse-slit mean on the glued space

Packet PROVE-WW-B13 (item N2 of PROVE-WW-B12). Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling
R31), proof of Proposition 4.18 (text dump L1609–1612). On the glued space `P ⊗ k(h)` the reverse curve is only known
through its history `p.2`. Its slit mean must be written as an explicit function of `p.2` before boundary values can
be read from the union boundary lemma.

* `histMean ρL ρR s y`: the conditional mean `meanAt` of the Loewner chain of the *regularized* driver of the history
  `y` stopped at `s` (`Sec4.regPath`, continuous for every history), with the clamped force positions
  (`Sec4.posLProc`, `Sec4.posRProc`). It is harmonic off the hull of that driver for **every** history
  (`harmonicOnNhd_histMean`), and at a good stop of a coupling it is the coupling's own `meanAt`
  (`histMean_killedHistory`).
* `revMean rL rR u₀ s y z = −histMean (R z) − u₀ z`, `R(z) = −1/z`: the reflected candidate.
* `revTested … φ y`: a Borel functional of the history (`Sec4.safePair` at the first safe level of the pushed test
  function) that equals `∫ revMean y · φ` whenever `supp φ` misses `R` of the hull (`revTested_eq`).
* `measurableSet_disjoint_of_relClosed`: avoidance events of compact sets are measurable for hitting-measurable random
  sets that are relatively closed in `ℍ`.
* **`ae_revSlitMean_glue`**: almost surely on the glued space, every local-set mean of the reflected reverse slit is,
  off that slit, `∫ revMean p.2 · φ`; and the hull of the regularized driver lies in the slit read from the
  history (`ae_regHull_subset_glue`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H fwdHull fwdMap)
open LQGMetric (DistOn TestOn)
open LocalSets (IsLocalSetMean germSigma)
open LawUnique
open Sec4 (regPath regHull posLProc posRProc safePair safeIdx safeUnion histStop)

universe u

/-! ### Avoidance events of relatively closed random sets -/

/-- **Compact avoidance events are measurable** for a hitting-measurable random set that is relatively closed in `ℍ`:
`K` misses `A` iff some open neighbourhood `K^{1/(m+1)} ∩ ℍ` of `K` misses `A`. -/
theorem measurableSet_disjoint_of_relClosed {X : Type*} [MeasurableSpace X] {A : X → Set ℂ}
    (hA : Measurable[_, hittingSigma] A) (hrel : ∀ x, A x ⊆ H ∧ IsOpen (H \ A x)) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) : MeasurableSet {x | Disjoint K (A x)} := by
  set U : ℕ → Set ℂ := fun m => thickening (1 / ((m : ℝ) + 1)) K ∩ H with hU
  have e : {x | Disjoint K (A x)} = ⋃ m : ℕ, (A ⁻¹' {S | (S ∩ U m).Nonempty})ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff, mem_preimage, not_nonempty_iff_eq_empty]
    constructor
    · intro hdis
      have hcl : K ⊆ (closure (A x))ᶜ := by
        intro z hzK hzc
        have hzA : z ∈ H \ A x := ⟨hKH hzK, Set.disjoint_left.1 hdis hzK⟩
        obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hzc _ (hrel x).2 hzA
        exact hw1.2 hw2
      obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open isClosed_closure.isOpen_compl hcl
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine ⟨m, eq_empty_of_forall_notMem fun z hz => ?_⟩
      exact hδK (thickening_mono hm.le K hz.2.1) (subset_closure hz.1)
    · rintro ⟨m, hm⟩
      refine Set.disjoint_left.2 fun z hzK hzA => ?_
      have : z ∈ A x ∩ U m := ⟨hzA, self_subset_thickening (by positivity) K hzK, hKH hzK⟩
      rw [hm] at this
      exact this
  rw [e]
  refine MeasurableSet.iUnion fun m => (hA ?_).compl
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨U m, isOpen_thickening.inter QuantumZipper.isOpen_H, inter_subset_right, rfl⟩

/-! ### The mean read from a history -/

section Mean

/-- The stopping time `s⁺` of a rational time. -/
def revStopT (s : ℚ) : ℝ≥0 := (s : ℝ).toNNReal

/-- The history stopped at `s`. -/
def revStop (s : ℚ) (y : HistorySpace 1 1) : HistorySpace 1 1 := Sec4.stopHistory (fun _ => revStopT s) y

theorem histStop_revStop (s : ℚ) (y : HistorySpace 1 1) : histStop (revStop s y) = revStopT s :=
  Sec4.stopHistory_fst_toNNReal y

theorem measurable_revStop (s : ℚ) : Measurable (revStop s) :=
  Sec4.measurable_stopHistory measurable_const

/-- **The mean read from a history**: `meanAt` of the regularized driver stopped at `s`, with the clamped force
positions. -/
def histMean (ρL ρR : Fin 1 → ℝ) (s : ℚ) (y : HistorySpace 1 1) (w : ℂ) : ℝ :=
  meanAt ρL ρR (regPath (revStop s y)) (fun i t => posLProc i t (revStop s y))
    (fun i t => posRProc i t (revStop s y)) (revStopT s) w

/-- **The reflected candidate mean**: `−histMean (R z) − u₀ z` for the reverse word `(r_R; r_L)`. -/
def revMean (rL rR : ℝ) (u₀ : ℂ → ℝ) (s : ℚ) (y : HistorySpace 1 1) (z : ℂ) : ℝ :=
  -histMean (fun _ => rR) (fun _ => rL) s y (negInv z) - u₀ z

/-- The test function pushed through `R`. -/
abbrev retPush (φ : TestOn upperHalfPlaneOpens) : TestOn upperHalfPlaneOpens :=
  Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ

/-- **The Borel tested mean**: minus the tested mean at the first safe level of the pushed test function, minus the
pairing of `u₀`. -/
def revTested (rL rR : ℝ) (u₀ : ℂ → ℝ) (s : ℚ) (φ : TestOn upperHalfPlaneOpens) (y : HistorySpace 1 1) : ℝ :=
  -(safePair 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (retPush φ) (safeIdx (retPush φ) (revStop s y))
    (revStop s y)).1 - ∫ z, u₀ z * φ z

theorem measurable_revTested (rL rR : ℝ) (u₀ : ℂ → ℝ) (s : ℚ) (φ : TestOn upperHalfPlaneOpens) :
    Measurable (revTested rL rR u₀ s φ) := by
  set ψ := retPush φ
  have hψH : tsupport ψ ⊆ H := ψ.tsupport_subset
  have hF : Measurable fun q : HistorySpace 1 1 × ℕ =>
      safePair 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) ψ q.2 q.1 :=
    measurable_from_prod_countable_left fun n =>
      Sec4.measurable_safePair 4 _ _ ψ.continuous ψ.hasCompactSupport hψH n
  have hG : Measurable fun y : HistorySpace 1 1 => (revStop s y, safeIdx (⇑ψ) (revStop s y)) :=
    (measurable_revStop s).prodMk ((Sec4.measurable_safeIdx hψH).comp (measurable_revStop s))
  exact ((measurable_fst.comp (hF.comp hG)).neg).sub_const _

/-- At `κ = 4` the canonical mean is `meanAt`. -/
theorem meanCan_four_eq_meanAt (ρL ρR : Fin 1 → ℝ) (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) :
    Coupling.meanCan 4 ρL ρR w vL vR t z = meanAt ρL ρR w vL vR t z := by
  rw [Coupling.meanCan, meanAt, condMean_eq_meanHarmonic, chiC_four, zero_mul, sub_zero]

/-- The first coordinate of the tested pair at the stop is the integral of `histMean`. -/
theorem regPair_revStop_fst (ρL ρR : Fin 1 → ℝ) (s : ℚ) (y : HistorySpace 1 1) (ψ : ℂ → ℝ) :
    (Sec4.regPair 4 ρL ρR ψ (revStop s y)).1 = ∫ w, histMean ρL ρR s y w * ψ w := by
  simp only [Sec4.regPair, histStop_revStop, meanCan_four_eq_meanAt, histMean]

/-- **`histMean` is harmonic off the hull of the regularized driver**, for every history (the clamped positions are
ordered). -/
theorem harmonicOnNhd_histMean (ρL ρR : Fin 1 → ℝ) (s : ℚ) (y : HistorySpace 1 1) :
    InnerProductSpace.HarmonicOnNhd (histMean ρL ρR s y)
      (H \ fwdHull (Ito.rpath (regPath (revStop s y))) (revStopT s)) := by
  set y' := revStop s y
  have hw := Sec4.continuous_rpath_regPath y'
  have hc := (isBoundedHarmonicExtension_condMean ρL ρR
    (vL := fun i => posLProc i (revStopT s) y' - regPath y' (revStopT s))
    (vR := fun i => posRProc i (revStopT s) y' - regPath y' (revStopT s))
    (fun i => by simp only [posLProc, add_sub_cancel_left]; exact min_le_left _ _)
    (fun i => by simp only [posRProc, add_sub_cancel_left]; exact le_max_left _ _)).1
  have hO := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw (revStopT s).coe_nonneg
  have hd := QuantumZipper.FwdHolo.differentiableOn_fwdMap hw (revStopT s).coe_nonneg
  intro z hz
  exact QuantumZipper.FieldLawler.fl_harmonicAt_comp (h := condMean ρL ρR
    (fun i => posLProc i (revStopT s) y' - regPath y' (revStopT s))
    (fun i => posRProc i (revStopT s) y' - regPath y' (revStopT s))) (hd.analyticAt (hO.mem_nhds hz))
    (hc _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hw (revStopT s).coe_nonneg hz))

theorem isOpen_H_diff_regFwdHull (s : ℚ) (y : HistorySpace 1 1) :
    IsOpen (H \ fwdHull (Ito.rpath (regPath (revStop s y))) (revStopT s)) :=
  QuantumZipper.FwdHolo.isOpen_compl_fwdHull (Sec4.continuous_rpath_regPath _) (revStopT s).coe_nonneg

theorem fwdHull_subset_regHull (s : ℚ) (y : HistorySpace 1 1) :
    fwdHull (Ito.rpath (regPath (revStop s y))) (revStopT s) ⊆ regHull (revStop s y) := by
  intro z hz
  refine ⟨subset_closure ?_, hz.1⟩
  rw [histStop_revStop]
  exact hz

/-- **The reflected candidate is harmonic off the reflected hull.** -/
theorem harmonicOnNhd_revMean (rL rR : ℝ) {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (s : ℚ)
    (y : HistorySpace 1 1) :
    InnerProductSpace.HarmonicOnNhd (revMean rL rR u₀ s y)
      (H \ negInv '' fwdHull (Ito.rpath (regPath (revStop s y))) (revStopT s)) := by
  rw [H_diff_image_negInv]
  have h1 := harmonicOnNhd_comp_negInv (isOpen_H_diff_regFwdHull s y) sdiff_subset
    (harmonicOnNhd_histMean (fun _ => rR) (fun _ => rL) s y)
  have h2 : InnerProductSpace.HarmonicOnNhd u₀
      (negInv '' (H \ fwdHull (Ito.rpath (regPath (revStop s y))) (revStopT s))) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hu₀ _ (negInv_mem_H hw.1)
  exact h1.neg.sub h2

/-- **The Borel tested mean is the tested candidate** whenever `supp φ` misses the reflected hull of the regularized
driver. -/
theorem revTested_eq (rL rR : ℝ) {u₀ : ℂ → ℝ} (hu₀ : ContinuousOn u₀ H) (s : ℚ) (y : HistorySpace 1 1)
    {φ : TestOn upperHalfPlaneOpens} (hdis : Disjoint (tsupport φ) (negInv '' regHull (revStop s y))) :
    revTested rL rR u₀ s φ y = ∫ z, revMean rL rR u₀ s y z * φ z := by
  set y' := revStop s y with hy'
  set ψ := retPush φ with hψ
  set F := fwdHull (Ito.rpath (regPath y')) (revStopT s) with hF
  have hFreg : F ⊆ regHull y' := fwdHull_subset_regHull s y
  have hψH : tsupport ψ ⊆ H := ψ.tsupport_subset
  -- the pushed test function misses the hull, so its support is alive at the stop
  have halive : ∀ z ∈ tsupport ψ, ∃ v, QuantumZipper.IsForwardSol (Ito.rpath (regPath y')) z (histStop y') v := by
    intro z hz
    refine QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull (histStop y').coe_nonneg (hψH hz) fun hzK => ?_
    obtain ⟨w, hw, rfl⟩ := tsupport_pushTest_return_subset φ hz
    refine Set.disjoint_left.1 hdis hw ⟨negInv w, ⟨subset_closure hzK, hψH hz⟩, negInv_negInv w⟩
  have hU : y' ∈ safeUnion (⇑ψ) :=
    mem_iUnion.2 (Sec4.eventually_mem_safeHist ψ.hasCompactSupport hψH halive).exists
  have hmem := Sec4.mem_safeHist_safeIdx hU
  have hpair : (safePair 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) ψ (safeIdx (⇑ψ) y') y').1 =
      ∫ w, histMean (fun _ => rR) (fun _ => rL) s y w * ψ w := by
    rw [Sec4.safePair]
    simp only [hmem, ↓reduceIte]
    rw [regPair_revStop_fst]
  have hcv := Chart.integral_mul_pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ
    (histMean (fun _ => rR) (fun _ => rL) s y)
  simp only [infinityReturnChart_inv_eq] at hcv
  -- integrability on the support of `φ`
  set O := H \ negInv '' F with hO
  have hOo : IsOpen O := by
    rw [hO, H_diff_image_negInv]
    exact isOpen_image_negInv (isOpen_H_diff_regFwdHull s y) sdiff_subset
  have hφO : tsupport φ ⊆ O := fun z hz =>
    ⟨φ.tsupport_subset hz, fun hzF => Set.disjoint_left.1 hdis hz (image_mono hFreg hzF)⟩
  have hhm : ContinuousOn (fun z => histMean (fun _ => rR) (fun _ => rL) s y (negInv z)) O := by
    have h1 := harmonicOnNhd_comp_negInv (isOpen_H_diff_regFwdHull s y) sdiff_subset
      (harmonicOnNhd_histMean (fun _ => rR) (fun _ => rL) s y)
    rw [← H_diff_image_negInv] at h1
    exact fun z hz => (h1 z hz).1.continuousAt.continuousWithinAt
  have i1 := LocalSets.integrable_mul_test hOo hhm φ hφO
  have i2 := LocalSets.integrable_mul_test QuantumZipper.isOpen_H hu₀ φ φ.tsupport_subset
  have i1' : Integrable (fun z => -(histMean (fun _ => rR) (fun _ => rL) s y (negInv z) * φ z)) := i1.neg
  rw [revTested, hpair, hcv, ← integral_neg, ← integral_sub i1' i2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [revMean]
  ring

end Mean

/-! ### At a good stop of a coupling -/

section Killed

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}

/-- At a good stop the hull of the regularized driver is the Loewner hull of the coupling. -/
theorem regHull_revStop_killedHistory {s : ℚ} (hg : Sec4.IsGoodStop (fun _ => revStopT s) W VL VR ζ ω) :
    regHull (revStop s (killedHistory W VL VR ζ ω)) = fwdHull (fun r : ℝ => W r.toNNReal ω) (revStopT s) :=
  (Sec4.isContHist_stopHistory hg).regHull_eq.trans (Exist.histHull_eq_fwdHull hg)

/-- **At a good stop with ordered positions, `histMean` is the coupling's `meanAt`.** -/
theorem histMean_killedHistory (ρL ρR : Fin 1 → ℝ) {s : ℚ}
    (hg : Sec4.IsGoodStop (fun _ => revStopT s) W VL VR ζ ω) (hL : VL 0 (revStopT s) ω ≤ W (revStopT s) ω)
    (hR : W (revStopT s) ω ≤ VR 0 (revStopT s) ω) (w : ℂ) :
    histMean ρL ρR s (killedHistory W VL VR ζ ω) w =
      meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (revStopT s) w := by
  have hC : Sec4.IsContHist (revStop s (killedHistory W VL VR ζ ω)) := Sec4.isContHist_stopHistory hg
  have hW : regPath (revStop s (killedHistory W VL VR ζ ω)) (revStopT s) = W (revStopT s) ω := by
    rw [hC.regPath_eq]
    exact (Sec4.histPath_stopHistory hg.1 hg.2.1 _).trans (by rw [min_self])
  have hstop : histStop (revStop s (killedHistory W VL VR ζ ω)) = revStopT s := histStop_revStop s _
  have hVL : Sec4.histVL (revStop s (killedHistory W VL VR ζ ω)) 0 = VL 0 (revStopT s) ω :=
    Sec4.histVL_stopHistory hg.1 hg.2.2.1 0
  have hVR : Sec4.histVR (revStop s (killedHistory W VL VR ζ ω)) 0 = VR 0 (revStopT s) ω :=
    Sec4.histVR_stopHistory hg.1 hg.2.2.2 0
  have hmap : fwdMap (Ito.rpath (regPath (revStop s (killedHistory W VL VR ζ ω)))) (revStopT s) w =
      fwdMap (Ito.rpath (W · ω)) (revStopT s) w := by
    rw [hC.rpath_regPath]
    exact Ito.fwdMap_congr_of_eqOn_of_le (Sec4.eqOn_histDrive hg).symm le_rfl
  simp only [histMean, meanAt, hmap]
  congr 1
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [posLProc, add_sub_cancel_left, hstop, hW, hVL]
    exact min_eq_right (sub_nonpos.2 hL)
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [posRProc, add_sub_cancel_left, hstop, hW, hVR]
    exact max_eq_right (sub_nonneg.2 hR)

end Killed

/-! ### The Borel set where the regularized hull lies in the slit -/

section RegSub

/-- A closed rational ball inside `ℍ ∖ B` around every point of `ℍ ∖ B`: inclusions of random sets are tested on
rational balls. -/
theorem subset_of_forall_ratBall {A B : Set ℂ} (hB : IsOpen (H \ B)) (hA : A ⊆ H)
    (h : ∀ i : ℚ × ℚ × ℚ, closedBall (ratPt i.1 i.2.1) i.2.2 ⊆ H →
      Disjoint (closedBall (ratPt i.1 i.2.1) (i.2.2 : ℝ)) B → Disjoint (closedBall (ratPt i.1 i.2.1) (i.2.2 : ℝ)) A) :
    A ⊆ B := by
  intro z hzA
  by_contra hzB
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hB z ⟨hA hzA, hzB⟩
  obtain ⟨a, b, hab⟩ := exists_ratPt_dist_lt z (show 0 < ε / 3 by positivity)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ε / 3 < 2 * ε / 3 by linarith)
  have hsub : closedBall (ratPt a b) (r : ℝ) ⊆ H \ B := fun w hw => hball (by
    rw [mem_ball]
    calc dist w z ≤ dist w (ratPt a b) + dist (ratPt a b) z := dist_triangle _ _ _
      _ < 2 * ε / 3 + ε / 3 := add_lt_add_of_le_of_lt ((mem_closedBall.1 hw).trans hr2.le) hab
      _ = ε := by ring)
  have hz : z ∈ closedBall (ratPt a b) (r : ℝ) := by
    rw [mem_closedBall, dist_comm]; exact hab.le.trans hr1.le
  exact Set.disjoint_left.1 (h (a, b, r) (fun w hw => (hsub hw).1)
    (Set.disjoint_left.2 fun w hw hwB => (hsub hw).2 hwB)) hz hzA

/-- The histories whose regularized hull at `s` lies in the slit read from the trace. -/
def RegSub (s : ℚ) : Set (HistorySpace 1 1) := {y | regHull (revStop s y) ⊆ histHull s y}

/-- **`RegSub s` is Borel.** -/
theorem measurableSet_regSub (s : ℚ) : MeasurableSet (RegSub s) := by
  have e : RegSub s = ⋂ i : ℚ × ℚ × ℚ, {y | closedBall (ratPt i.1 i.2.1) (i.2.2 : ℝ) ⊆ H →
      Disjoint (closedBall (ratPt i.1 i.2.1) (i.2.2 : ℝ)) (histHull s y) →
        Disjoint (closedBall (ratPt i.1 i.2.1) (i.2.2 : ℝ)) (regHull (revStop s y))} := by
    ext y
    simp only [RegSub, mem_ofPred_eq, mem_iInter]
    exact ⟨fun hy i _ hd => hd.mono_right hy, fun hy =>
      subset_of_forall_ratBall (histHull_relClosed s y).2 (fun z hz => hz.2) hy⟩
  rw [e]
  refine MeasurableSet.iInter fun i => ?_
  by_cases hK : closedBall (ratPt i.1 i.2.1) (i.2.2 : ℝ) ⊆ H
  · refine measurableSet_setOfPred.2 (Measurable.imp measurable_const (Measurable.imp ?_ ?_))
    · exact measurableSet_setOfPred.1 (measurableSet_disjoint_of_relClosed (measurable_histHull s)
        (histHull_relClosed s) (isCompact_closedBall _ _) hK)
    · exact measurableSet_setOfPred.1 ((measurable_revStop s)
        (Sec4.measurableSet_disjoint_regHull (isCompact_closedBall _ _)))
  · have : {y : HistorySpace 1 1 | closedBall (ratPt i.1 i.2.1) (i.2.2 : ℝ) ⊆ H →
        Disjoint (closedBall (ratPt i.1 i.2.1) (i.2.2 : ℝ)) (histHull s y) →
          Disjoint (closedBall (ratPt i.1 i.2.1) (i.2.2 : ℝ)) (regHull (revStop s y))} = univ :=
      eq_univ_of_forall fun y hK' => absurd hK' hK
    rw [this]
    exact MeasurableSet.univ

end RegSub

/-! ### On the glued space -/

section Glue

open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {rL rR : ℝ}
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- **The reverse coupling at the rational time `s`**: almost surely `s` is a good stop, the positions are ordered,
and the slit read from the history is the Loewner hull. -/
theorem ae_revStop_good (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hE : IsMarkedChain LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) {s : ℚ}
    (hs : 0 < s) :
    ∀ᵐ ω ∂P, Sec4.IsGoodStop (fun _ => revStopT s) W VL VR ζ ω ∧ VL 0 (revStopT s) ω ≤ W (revStopT s) ω ∧
      W (revStopT s) ω ≤ VR 0 (revStopT s) ω ∧
      histHull s (killedHistory W VL VR ζ ω) = fwdHull (fun r : ℝ => W r.toNNReal ω) (revStopT s) := by
  have hζ := IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hE
  have hlt : ∀ᵐ ω ∂P, (((fun _ : HistorySpace 1 1 => revStopT s) (killedHistory W VL VR ζ ω) : ℝ≥0) : ℝ≥0∞) <
      ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  filter_upwards [Sec4.ae_isGoodStop_of_evolution (s := fun _ : HistorySpace 1 1 => revStopT s) hE hlt, hE.2.2.2.2, ae_histHull_eq_fwdHull hL hR hE hs,
    hζ] with ω hg hp hH hω
  obtain ⟨-, -, -, -, -, -, -, hvLw, hwvR, -⟩ := id hp
  have hT : ((revStopT s : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hω.1]; exact ENNReal.coe_lt_top
  exact ⟨hg, hvLw _ hT 0, hwvR _ hT 0, hH⟩

/-- **The canonical reverse-slit mean** (PROVE-WW-B12's `exists_isLocalSetMean_revSlit_glue`, with the local-set mean
on the canonical space exported, so that it is measurable). -/
theorem exists_isLocalSetMean_revSlit_canon (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {s : ℚ} (hs : 0 < s) :
    ∃ g : RevSpace.{u} → DistOn upperHalfPlaneOpens, Measurable g ∧
      IsLocalSetMean (fun p : Ω × HistorySpace 1 1 => negInv '' histHull s p.2)
        (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k h hC.2.1) (fun p => g (glueProj h p)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P₂,
        tsupport φ ⊆ H \ negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) →
        g (revProj W₂ VL₂ VR₂ ζ₂ h₂ ω) φ =
          ∫ z, (-meanAt (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (W₂ · ω) (fun i => (VL₂ i · ω))
            (fun i => (VR₂ i · ω)) (Real.toNNReal s) (negInv z) - u₀ z) * φ z := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  set D := smoothDist upperHalfPlaneOpens u₀ with hD
  have hDh : IsHarmonicDistOn D H := WholeField.isHarmonicDistOn_smoothDist hu₀.1
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hh := hC.2.1
  have hh₂ := hC₂.2.1
  have hπ₂ := measurable_revProj hh₂ hX₂
  set μ := P₂.map (revProj W₂ VL₂ VR₂ ζ₂ h₂) with hμdef
  have hglue := glueMeasure_map_revProj hh hh₂ hX₂ hlaw k hk
  have hG₂ : IsLocalSet (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
      (fun ω => reflectField (h₂ ω) - D) P₂ :=
    WholeField.IsLocalSet.sub_dist (IsLocalSet.reflect (isLocalSet_histHull_twoSeed hR hL hC₂ hs)) hDh
  have hpairm : Measurable fun q : RevSpace.{u} => (revSlit s q, revField D q) :=
    (measurable_revSlit s).prodMk (measurable_revField D)
  have hloc : IsLocalSet (revSlit s) (revField D) μ := by
    refine IsLocalSet.of_map_eq hG₂ hpairm.aemeasurable (ae_of_all _ (revSlit_relClosed s)) ?_
    rw [hμdef, Measure.map_map hpairm hπ₂]
    rfl
  have hZglue : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω × HistorySpace 1 1 => WholeField.centredField h u₀ p.1) (glueMeasure P k h hh) :=
    isZeroBoundaryGFF_comp_of_map_eq (g := WholeField.centredField h u₀) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hh) (WholeField.isZeroBoundaryGFF_centredField hC hu₀)
  have hZ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (revField D) μ := by
    refine ⟨measurable_revField D, ?_⟩
    rw [hμdef, ← hglue]
    exact Restart.isZBGFFProcess_map (measurable_glueProj hh)
      (fun φ => (LQGMetric.measurable_distOn_apply φ).comp (measurable_revField D)) hZglue.process
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hZ (measurable_revSlit s) hloc
  have hgm : Measurable g := hg.1.mono (LocalSets.germSigma_le (measurable_revSlit s) (measurable_revField D)) le_rfl
  refine ⟨g, hgm, ?_, fun φ => ?_⟩
  · exact IsLocalSetMean.comp (measurable_glueProj hh) hglue (measurable_revSlit s) (measurable_revField D) hg
  · obtain ⟨g', hg', hid'⟩ := exists_isLocalSetMean_revSlit_twoSeed hL hR hC₂ hu₀ hs
    have hg₂ : IsLocalSetMean (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
        (fun ω => reflectField (h₂ ω) - D) P₂ (fun ω => g (revProj W₂ VL₂ VR₂ ζ₂ h₂ ω)) :=
      IsLocalSetMean.comp hπ₂ rfl (measurable_revSlit s) (measurable_revField D) hg
    have hAm : Measurable[mΩ₂, hittingSigma] fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
      fun t ht => hπ₂ (measurable_revSlit s ht)
    have hFm : Measurable fun ω => reflectField (h₂ ω) - D :=
      (WholeField.measurable_sub_dist D).comp (measurable_reflectField.comp hh₂)
    have heq := LocalSets.IsLocalSetMean.ae_apply_eq hAm hFm hg₂ hg' φ
    filter_upwards [heq, hid'] with ω e1 e2 hφ
    exact e1.trans (e2 φ hφ)

/-- **Item N2 of PROVE-WW-B12: the explicit reverse-slit mean on the glued space.** In the setting of
`ReverseTipContactStatement`, almost surely on the glued space the hull of the regularized driver of `p.2` lies in the
slit read from its trace, and every local-set mean `g_G` of the reflected reverse slit `R(β(0, s])` for the centred
field `h − u₀` is, off that slit, the explicit `revMean`: `g_G(φ) = ∫ (−histMean (R z) − u₀ z) φ(z) dz`. -/
theorem ae_revSlitMean_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {s : ℚ} (hs : 0 < s) {gG : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens}
    (hgG : IsLocalSetMean (fun p : Ω × HistorySpace 1 1 => negInv '' histHull s p.2)
      (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k h hC.2.1) gG) :
    (∀ᵐ p ∂(glueMeasure P k h hC.2.1), p.2 ∈ RegSub s) ∧
      ∀ᵐ p ∂(glueMeasure P k h hC.2.1), ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ negInv '' histHull s p.2 → gG p φ = ∫ z, revMean rL rR u₀ s p.2 z * φ z := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hh := hC.2.1
  have hh₂ := hC₂.2.1
  have hharm : InnerProductSpace.HarmonicOnNhd u₀ H := hu₀.1
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hharm z hz).1.continuousAt.continuousWithinAt
  have hgood₂ := ae_revStop_good hR hL hC₂.1 hs
  have hreg : ∀ᵐ p ∂(glueMeasure P k h hh), p.2 ∈ RegSub s := by
    refine ae_glue_snd (X₂ := fun ω => reflectField (h₂ ω)) (D₂ := killedHistory W₂ VL₂ VR₂ ζ₂) hh
      (measurable_reflectField.comp hh₂) (measurable_killedHistory hX₂) hlaw k hk (measurableSet_regSub s) ?_
    filter_upwards [hgood₂] with ω hω
    obtain ⟨hg, -, -, hH⟩ := hω
    show regHull (revStop s _) ⊆ histHull s _
    rw [regHull_revStop_killedHistory hg, hH]
  refine ⟨hreg, ?_⟩
  obtain ⟨g, hgm, hgl, hg₂⟩ := exists_isLocalSetMean_revSlit_canon hL hR hC hC₂ hlaw k hk hu₀ hs
  have hAm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 => negInv '' histHull s p.2 :=
    (measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd
  have hFm : Measurable fun p : Ω × HistorySpace 1 1 => WholeField.centredField h u₀ p.1 :=
    (WholeField.measurable_centredField hh u₀).comp measurable_fst
  refine ae_forall_apply_eq_of_forall_ae hgG.2.1
    (ae_of_all _ fun p => (image_negInv_relClosed (histHull_relClosed s p.2)).2) ?_ fun φ => ?_
  · filter_upwards [hreg] with p hp
    intro z hz
    refine harmonicOnNhd_revMean rL rR hharm s p.2 z ⟨hz.1, fun hzF => hz.2 ?_⟩
    obtain ⟨w, hw, hwz⟩ := hzF
    exact ⟨w, hp (fwdHull_subset_regHull s p.2 hw), hwz⟩
  · set Q : RevSpace.{u} → Prop := fun q =>
      Disjoint (tsupport φ) (revSlit s q) → g q φ = revTested rL rR u₀ s φ q.down.2 with hQdef
    have hQm : MeasurableSet {q | Q q} := by
      refine measurableSet_setOfPred.2 (Measurable.imp ?_ ?_)
      · exact measurableSet_setOfPred.1 (measurableSet_disjoint_of_relClosed (measurable_revSlit s)
          (revSlit_relClosed s) φ.hasCompactSupport φ.tsupport_subset)
      · exact measurableSet_setOfPred.1 (measurableSet_eq_fun ((LQGMetric.measurable_distOn_apply φ).comp hgm)
          ((measurable_revTested rL rR u₀ s φ).comp (measurable_snd.comp measurable_down)))
    have hQ₂ : ∀ᵐ ω ∂P₂, Q (revProj W₂ VL₂ VR₂ ζ₂ h₂ ω) := by
      filter_upwards [hg₂ φ, hgood₂] with ω hω hω' hdis
      obtain ⟨hg, hvL, hvR, hH⟩ := hω'
      have hsub : tsupport φ ⊆ H \ negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
        fun z hz => ⟨φ.tsupport_subset hz, Set.disjoint_left.1 hdis hz⟩
      rw [hω hsub]
      have hdis' : Disjoint (tsupport φ) (negInv '' regHull (revStop s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) := by
        rw [regHull_revStop_killedHistory hg, ← hH]
        exact hdis
      show _ = revTested rL rR u₀ s φ (killedHistory W₂ VL₂ VR₂ ζ₂ ω)
      rw [revTested_eq rL rR hu₀c s _ hdis']
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [revMean]
      rw [histMean_killedHistory _ _ hg hvL hvR]
      rfl
    have hQg := ae_glue_of_ae_revProj hh hh₂ hX₂ hlaw k hk hQm hQ₂
    have hagree := LocalSets.IsLocalSetMean.ae_apply_eq hAm hFm hgG hgl φ
    filter_upwards [hQg, hagree, hreg] with p hQp hap hp hφ
    have hdis : Disjoint (tsupport φ) (negInv '' histHull s p.2) :=
      Set.disjoint_left.2 fun z hz hz' => (hφ hz).2 hz'
    rw [hap, hQp hdis]
    exact revTested_eq rL rR hu₀c s p.2 (hdis.mono_right (image_mono hp))

end Glue

end InteractingSLE.WangWu
