/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndPass
import InteractingSLE.Spec.Sec5.CrossCondMartMarks

/-!
# Lemma 4.7 in the chart `Q`: the killed image word read from the two stopped histories

Packet PROVE-CFRESTART5, item D3 (marks; the Lemma 4.7 mirror of GLUECOND7's `CrossCondMartStop` and
`CrossCondMartMarksY`). The stopped data of a glued sample are the flow history stopped at the flow time `s` and the
counterflow history stopped at a rational counterflow time `t` (`stopD47`, measurable for the marks
`cfGlueMarks s t`). From them one reads the counterflow trace (`alphaD47`), the obstacle `R(K_s)` (`GD47`), the image
curve (`gammaD47`), the pre-contact times (`PcD47`, `PD47`) and the image marks (`gXLD47`, `gXRD47`); on good samples
they agree with the glued objects before `t`.

* `IsKilledCurve.inter_Iio`, `IsKilledCurve.congr`: restriction of a killed curve to the times before `t`, and
  congruence;
* `isKilledCurve_gammaD47_stopD`: the image curve read from the stopped data is a killed curve before `t`;
* `IsGoodD47`: good stopped data (no measurability claimed), and measurability of the killed word read from good
  stopped data (`measurable_kcW_gammaD47`, `measurable_kcVL_gammaD47`, `measurable_kcVR_gammaD47`, the killing events
  and the capacity clock at rational pre-contact times).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar.RealFlow LocalSets
open CrossCond.Word49 (psiL psiR junL junR measurable_snoc)

/-! ### Restriction and congruence of killed curves -/

namespace IsKilledCurve

variable {γ γ' : ℝ → ℂ} {P : Set ℝ}

/-- **A killed curve restricted to the times before `t > 0` is a killed curve.** -/
theorem inter_Iio (hγ : IsKilledCurve γ P) {t : ℝ} (ht : 0 < t) : IsKilledCurve γ (P ∩ Iio t) where
  zero_mem := ⟨hγ.zero_mem, ht⟩
  nonneg u hu := hγ.nonneg u hu.1
  icc S hS := fun u hu => ⟨hγ.icc S hS.1 hu, lt_of_le_of_lt hu.2 hS.2⟩
  exists_gt S hS := by
    have hSt : S < t := hS.2
    obtain ⟨S', hS'P, hSS'⟩ := hγ.exists_gt S hS.1
    have hS0 := hγ.nonneg S hS.1
    have h1 : S ≤ (S + t) / 2 := by linarith
    have h2 : S < (S + t) / 2 := by linarith
    have h3 : (S + t) / 2 < t := by linarith
    refine ⟨min S' ((S + t) / 2), ⟨hγ.icc S' hS'P ⟨le_trans hS0 (le_min hSS'.le h1), min_le_left _ _⟩,
      lt_of_le_of_lt (min_le_right _ _) h3⟩, lt_min hSS' h2⟩
  zero := hγ.zero
  cont := hγ.cont.mono inter_subset_left
  mem_H u hu hpos := hγ.mem_H u hu.1 hpos
  localDriver S hS hS0 := hγ.localDriver S hS.1 hS0

/-- **Congruence**: a curve agreeing with a killed curve on its pre-killing times is a killed curve. -/
theorem congr (hγ : IsKilledCurve γ P) (h : EqOn γ γ' P) : IsKilledCurve γ' P where
  zero_mem := hγ.zero_mem
  nonneg := hγ.nonneg
  icc := hγ.icc
  exists_gt := hγ.exists_gt
  zero := h hγ.zero_mem ▸ hγ.zero
  cont := hγ.cont.congr fun u hu => (h hu).symm
  mem_H u hu hpos := h hu ▸ hγ.mem_H u hu hpos
  localDriver S hS hS0 := by
    have hEq : EqOn γ γ' (Icc 0 S) := h.mono (hγ.icc S hS)
    have hcc : ∀ t ∈ Icc 0 S, capClock γ t = capClock γ' t := fun t ht =>
      WangWu.capClock_congr (hEq.mono (Icc_subset_Icc_right ht.2))
    have hcS : EqOn (capClock γ) (capClock γ') (Icc 0 S) := fun t ht => hcc t ht
    obtain ⟨W, hW, hW0, hc0, hm, hc, hK⟩ := hγ.localDriver S hS hS0
    refine ⟨W, hW, hW0, (hcc 0 ⟨le_rfl, hS0.le⟩) ▸ hc0, hm.congr hcS, hc.congr fun t ht => (hcS ht).symm,
      fun t ht => ?_⟩
    rw [← hcc t ht, ← image_congr (hEq.mono (Icc_subset_Icc_right ht.2))]
    exact hK t ht

end IsKilledCurve

namespace Kill47

/-! ### Stopped data -/

/-- The space of the two stopped histories (flow, counterflow). -/
abbrev Y47 (nL nR : ℕ) : Type := HistorySpace nL nR × HistorySpace 0 0

/-- **The two stopped histories** of a glued sample: the flow history stopped at `s`, the counterflow history stopped
at the rational time `t`. -/
def stopD47 {Ω : Type*} {nL nR : ℕ} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (t : ℚ) (p : Ω × HistorySpace 0 0) : Y47 nL nR :=
  (flowStop W VL VR ζ s p, cfStop (t : ℝ).toNNReal p.2)

section Defs

variable {nL nR : ℕ}

/-- The counterflow trace read from stopped data. -/
def alphaD47 (y : Y47 nL nR) (u : ℝ) : ℂ := LP.traceAt u.toNNReal (Sec4.regPath y.2)

/-- The obstacle `R(K_s)` read from stopped data. -/
def GD47 (s : ℝ≥0) (y : Y47 nL nR) : Set ℂ := negInv '' hullAt s y.1

/-- The image curve read from stopped data. -/
def gammaD47 (s : ℝ≥0) (y : Y47 nL nR) : ℝ → ℂ := imgCurve (regDrvH y.1) s (alphaD47 y)

/-- The pre-contact times read from stopped data. -/
def PcD47 (s : ℝ≥0) (y : Y47 nL nR) : Set ℝ := preContact (alphaD47 y) (GD47 s y)

/-- The pre-contact times before `t`, read from stopped data. -/
def PD47 (t : ℚ) (s : ℝ≥0) (y : Y47 nL nR) : Set ℝ := PcD47 s y ∩ Iio (t : ℝ)

/-- The left image marks read from stopped data. -/
def gXLD47 {m : ℕ} (x : Fin m → ℝ) (s : ℝ≥0) (y : Y47 nL nR) : Fin (m + 1) → ℝ :=
  Fin.snoc (fun i => psiL (regDrvH y.1) s (x i)) (junL (regDrvH y.1) s)

/-- The right image marks read from stopped data. -/
def gXRD47 {m : ℕ} (x : Fin m → ℝ) (s : ℝ≥0) (y : Y47 nL nR) : Fin (m + 1) → ℝ :=
  Fin.snoc (fun j => psiR (regDrvH y.1) s (x j)) (junR (regDrvH y.1) s)

end Defs

section StopData

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t : ℚ}

theorem measurable_stopD47 [MeasurableSpace Ω] (s : ℝ≥0) (t : ℚ) :
    Measurable[CrossCond.cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] (stopD47 W VL VR ζ s t) := by
  refine Measurable.prodMk ?_ ?_
  · have h : Measurable[MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1)
        (stopSigma s)] fun p : Ω × HistorySpace 0 0 => flowStop W VL VR ζ s p :=
      fun B hB => ⟨Sec4.stopHistory (fun _ => s) ⁻¹' B, ⟨B, hB, rfl⟩, rfl⟩
    exact h.mono le_sup_left le_rfl
  · have h : Measurable[MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => p.2) (stopSigma (t : ℝ).toNNReal)]
        fun p : Ω × HistorySpace 0 0 => cfStop (t : ℝ).toNNReal p.2 :=
      fun B hB => ⟨Sec4.stopHistory (fun _ => (t : ℝ).toNNReal) ⁻¹' B, ⟨B, hB, rfl⟩, rfl⟩
    exact h.mono le_sup_right le_rfl

variable {p : Ω × HistorySpace 0 0}

theorem regDrvH_stopD47 : regDrvH (stopD47 W VL VR ζ s t p).1 = fReg W VL VR ζ s p := rfl

theorem alphaD47_stopD (hg : IsGood47 W VL VR ζ p) {u : ℝ} (hu : u ≤ t) :
    alphaD47 (stopD47 W VL VR ζ s t p) u = histLine p.2 u := by
  have hy := hg.2.2.1.1
  rw [alphaD47, stopD47, regPath_cfStop_of_mem_goodCfSet hy, CfRegQ.histLine_eq_traceAt]
  refine LP.traceAt_congr fun r hr => ?_
  have hrt : r ≤ (t : ℝ).toNNReal := hr.trans (Real.toNNReal_le_toNNReal hu)
  simp only [min_eq_left hrt]

theorem hullAt_flowStop (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (p : Ω × HistorySpace 0 0) :
    hullAt s (flowStop W VL VR ζ s p) = hullAt s (killedHistory W VL VR ζ p.1) := by
  simp only [hullAt, flowStop]
  exact congrArg Sec4.regHull (CrossCond.stopHistory_const_stopHistory_const s _)

theorem GD47_stopD : GD47 s (stopD47 W VL VR ζ s t p) = qObs W VL VR ζ s p := by
  rw [GD47, stopD47, hullAt_flowStop, qObs]

theorem gammaD47_stopD (hp : p ∈ E) (hg : IsGood47 W VL VR ζ p) {u : ℝ} (hu : u ≤ t) :
    gammaD47 s (stopD47 W VL VR ζ s t p) u = qgCurve W s E p u := by
  rw [gammaD47, regDrvH_stopD47, imgCurve_fReg hg, qgCurve_of_mem hp, imgCurve, imgCurve]
  split_ifs
  · rfl
  · rw [alphaD47_stopD hg hu]

theorem mem_PcD47_stopD_iff (hp : p ∈ E) (hg : IsGood47 W VL VR ζ p) {u : ℝ} (hu : u ≤ t) :
    u ∈ PcD47 s (stopD47 W VL VR ζ s t p) ↔ u ∈ qgPre W VL VR ζ s E p := by
  rw [PcD47, qgPre_of_mem hp, GD47_stopD, preContact, preContact, mem_ofPred_eq, mem_ofPred_eq]
  refine and_congr_right fun _ => forall₂_congr fun v hv => ?_
  rw [alphaD47_stopD hg (hv.2.trans hu)]

theorem PD47_stopD (hp : p ∈ E) (hg : IsGood47 W VL VR ζ p) :
    PD47 t s (stopD47 W VL VR ζ s t p) = qgPre W VL VR ζ s E p ∩ Iio (t : ℝ) := by
  ext u
  simp only [PD47, mem_inter_iff, mem_Iio]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_PcD47_stopD_iff hp hg h2.le).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_PcD47_stopD_iff hp hg h2.le).2 h1, h2⟩

theorem isKilledCurve_gammaD47_stopD (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) :
    IsKilledCurve (gammaD47 s (stopD47 W VL VR ζ s t p)) (PD47 t s (stopD47 W VL VR ζ s t p)) := by
  have hg := hEg p hp
  rw [PD47_stopD hp hg]
  exact ((isKilledCurve_qgCurve hEg p).inter_Iio (by exact_mod_cast ht)).congr
    fun u hu => (gammaD47_stopD hp hg hu.2.le).symm

theorem gXLD47_stopD {m : ℕ} (x : Fin m → ℝ) (hp : p ∈ E) (hg : IsGood47 W VL VR ζ p) :
    gXLD47 x s (stopD47 W VL VR ζ s t p) = qgXL x W s E p := by
  simp only [gXLD47, qgXL, hp, ↓reduceIte, regDrvH_stopD47, psiL_fReg hg, junL_fReg hg]

theorem gXRD47_stopD {m : ℕ} (x : Fin m → ℝ) (hp : p ∈ E) (hg : IsGood47 W VL VR ζ p) :
    gXRD47 x s (stopD47 W VL VR ζ s t p) = qgXR x W s E p := by
  simp only [gXRD47, qgXR, hp, ↓reduceIte, regDrvH_stopD47, psiR_fReg hg, junR_fReg hg]

end StopData

/-! ### Good stopped data and measurability -/

section Defs2

variable {nL nR : ℕ}

/-- The rational pre-contact condition read from stopped data. -/
def RatD47 (s : ℝ≥0) (q : ℚ) : Set (Y47 nL nR) :=
  {y | ∃ m : ℕ, ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
    Disjoint (ball (alphaD47 y u) (1 / ((m : ℝ) + 1))) (GD47 s y)}

/-- The away condition of the announcing times, read from stopped data. -/
def IsAwayD47 (s : ℝ≥0) (n : ℕ) (y : Y47 nL nR) (q : ℚ) : Prop :=
  ((0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n) ∧ ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
    Disjoint (ball (alphaD47 y u) (1 / ((n : ℝ) + 1))) (GD47 s y)

/-- **Good stopped data** (no measurability claimed): the image curve is a killed curve before `t`, the rational
pre-contact times up to `t` are given by `RatD47`, and the image curve is continuous on each pre-contact prefix. -/
structure IsGoodD47 (s : ℝ≥0) (t : ℚ) (y : Y47 nL nR) : Prop where
  killed : IsKilledCurve (gammaD47 s y) (PD47 t s y)
  rat : ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) ≤ t → ((q : ℝ) ∈ PcD47 s y ↔ y ∈ RatD47 s q)
  cont : ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) ≤ t → (q : ℝ) ∈ PcD47 s y → ContinuousOn (gammaD47 s y) (Icc 0 q)

end Defs2

section Y

variable {nL nR : ℕ} {s : ℝ≥0} {t : ℚ}

theorem measurable_alphaD47 (u : ℝ) : Measurable fun y : Y47 nL nR => alphaD47 y u :=
  (LP.measurable_traceAt _).comp (measurable_pi_iff.2 fun r => (Sec4.measurable_regPath_apply r).comp measurable_snd)

theorem measurable_GD47 (s : ℝ≥0) : Measurable[_, hittingSigma] (GD47 (nL := nL) (nR := nR) s) :=
  measurable_image_negInv.comp ((measurable_hullAt s).comp measurable_fst)

theorem GD47_subset_H (y : Y47 nL nR) : GD47 s y ⊆ H :=
  fun _ ⟨_, hw, e⟩ => e ▸ WangWu.negInv_mem_H ((hullAt_relClosed s _).1 hw)

theorem measurable_gammaD47 (q : ℝ) : Measurable fun y : Y47 nL nR => gammaD47 s y q := by
  by_cases hq : q ≤ 0
  · simp only [gammaD47, imgCurve, hq, ↓reduceIte]
    exact measurable_const
  · simp only [gammaD47, imgCurve, hq, ↓reduceIte, revChart]
    have hy : Measurable fun y : Y47 nL nR => negInv (alphaD47 y q) := measurable_negInv.comp (measurable_alphaD47 q)
    have h := (Exist.StagedLaw.measurable_fwdMap_param (W := fun y : Y47 nL nR => regDrvH y.1)
      (fun y => continuous_regDrvH y.1) (fun u => (measurable_regDrvH_apply u).comp measurable_fst)
      (fun y => regDrvH_zero y.1) (τ := fun _ => (s : ℝ)) measurable_const (fun _ => s.coe_nonneg) hy).1
    exact measurable_negInv.comp h

theorem measurableSet_disjoint_ball_alphaD47 (u : ℝ) (ρ : ℝ) :
    MeasurableSet {y : Y47 nL nR | Disjoint (ball (alphaD47 y u) ρ) (GD47 s y)} :=
  CrossCond.Word49.measurableSet_disjoint_ball (measurable_alphaD47 u) (measurable_GD47 s) GD47_subset_H ρ

theorem measurableSet_RatD47 (q : ℚ) : MeasurableSet (RatD47 (nL := nL) (nR := nR) s q) := by
  have e : RatD47 (nL := nL) (nR := nR) s q = ⋃ m : ℕ, ⋂ u : ℚ, {y : Y47 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
      Disjoint (ball (alphaD47 y u) (1 / ((m : ℝ) + 1))) (GD47 s y)} := by
    ext y
    simp only [RatD47, mem_ofPred_eq, mem_iUnion, mem_iInter]
  rw [e]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun u => ?_
  by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q
  · simp only [hc.1, hc.2, forall_const]
    exact measurableSet_disjoint_ball_alphaD47 _ _
  · have e : {y : Y47 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
        Disjoint (ball (alphaD47 y u) (1 / ((m : ℝ) + 1))) (GD47 s y)} = univ := by
      ext y
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hc
    rw [e]
    exact MeasurableSet.univ

theorem measurableSet_isAwayD47 (n : ℕ) (q : ℚ) : MeasurableSet {y : Y47 nL nR | IsAwayD47 s n y q} := by
  have e : {y : Y47 nL nR | IsAwayD47 s n y q} = {_y | (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n} ∩ ⋂ u : ℚ,
      {y : Y47 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
        Disjoint (ball (alphaD47 y u) (1 / ((n : ℝ) + 1))) (GD47 s y)} := by
    ext y
    simp only [IsAwayD47, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [e]
  refine MeasurableSet.const _ |>.inter (MeasurableSet.iInter fun u => ?_)
  by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q
  · simp only [hc.1, hc.2, forall_const]
    exact measurableSet_disjoint_ball_alphaD47 _ _
  · have e : {y : Y47 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
        Disjoint (ball (alphaD47 y u) (1 / ((n : ℝ) + 1))) (GD47 s y)} = univ := by
      ext y
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hc
    rw [e]
    exact MeasurableSet.univ

/-- The real Loewner flow of `sg · regDrvH` is measurable in the history. -/
theorem measurable_rightImg_regDrvH (s : ℝ≥0) (sg x : ℝ) :
    Measurable fun y : HistorySpace nL nR => rightImg (fun r => sg * regDrvH y r) x s := by
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace (HistorySpace nL nR)) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have h := Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c)
    (W := fun r y => sg * regDrvH y r)
    (fun r => (measurable_regDrvH_apply r).const_mul sg)
    (fun y => ((continuous_regDrvH y).comp NNReal.continuous_coe).const_smul sg) (x := fun _ => x)
    measurable_const s
  have e : ∀ y : HistorySpace nL nR, Bessel.realPath (fun r y => sg * regDrvH y r) y =
      fun r => sg * regDrvH y r :=
    fun y => funext fun r => by simp only [Bessel.realPath, regDrvH_toNNReal]
  simp_rw [e] at h
  exact h

theorem measurable_psiL_regDrvH (s : ℝ≥0) (x : ℝ) :
    Measurable fun y : HistorySpace nL nR => psiL (regDrvH y) s x := by
  unfold psiL
  split_ifs
  · exact measurable_const
  · have h := measurable_rightImg_regDrvH (nL := nL) (nR := nR) s 1 (-1 / x)
    simp only [one_mul] at h
    exact measurable_const.div (h.sub (measurable_regDrvH_apply s))

theorem measurable_psiR_regDrvH (s : ℝ≥0) (x : ℝ) :
    Measurable fun y : HistorySpace nL nR => psiR (regDrvH y) s x := by
  unfold psiR
  split_ifs
  · exact measurable_const
  · have h := measurable_rightImg_regDrvH (nL := nL) (nR := nR) s (-1) (1 / x)
    simp only [neg_one_mul] at h
    exact measurable_const.div (h.neg.sub (measurable_regDrvH_apply s))

theorem measurable_junL_regDrvH (s : ℝ≥0) : Measurable fun y : HistorySpace nL nR => junL (regDrvH y) s := by
  have h := measurable_rightImg_regDrvH (nL := nL) (nR := nR) s 1 0
  simp only [one_mul] at h
  exact measurable_const.div (h.sub (measurable_regDrvH_apply s))

theorem measurable_junR_regDrvH (s : ℝ≥0) : Measurable fun y : HistorySpace nL nR => junR (regDrvH y) s := by
  have h := measurable_rightImg_regDrvH (nL := nL) (nR := nR) s (-1) 0
  simp only [neg_one_mul] at h
  exact measurable_const.div (h.neg.sub (measurable_regDrvH_apply s))

theorem measurable_gXLD47 {m : ℕ} (x : Fin m → ℝ) (s : ℝ≥0) : Measurable fun y : Y47 nL nR => gXLD47 x s y :=
  measurable_snoc (measurable_pi_iff.2 fun i => (measurable_psiL_regDrvH s (x i)).comp measurable_fst)
    ((measurable_junL_regDrvH s).comp measurable_fst)

theorem measurable_gXRD47 {m : ℕ} (x : Fin m → ℝ) (s : ℝ≥0) : Measurable fun y : Y47 nL nR => gXRD47 x s y :=
  measurable_snoc (measurable_pi_iff.2 fun j => (measurable_psiR_regDrvH s (x j)).comp measurable_fst)
    ((measurable_junR_regDrvH s).comp measurable_fst)

end Y

section Good

variable {nL nR : ℕ} {s : ℝ≥0} {t : ℚ}

theorem measurableSet_mem_PcD47 (q : ℚ) (hq0 : (0 : ℝ) ≤ q) (hqt : (q : ℝ) ≤ t) :
    MeasurableSet {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1} := by
  have e : {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1} = Subtype.val ⁻¹' RatD47 s q := by
    ext x
    exact x.2.rat q hq0 hqt
  rw [e]
  exact measurable_subtype_coe (measurableSet_RatD47 q)

theorem measurableSet_mem_PD47 (q : ℚ) :
    MeasurableSet {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PD47 t s x.1} := by
  by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) < t
  · have e : {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PD47 t s x.1} =
        {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1} := by
      ext x
      simp only [PD47, mem_ofPred_eq, mem_inter_iff, mem_Iio, hq.2, and_true]
    rw [e]
    exact measurableSet_mem_PcD47 q hq.1 hq.2.le
  · have e : {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PD47 t s x.1} = ∅ := by
      ext x
      simp only [PD47, PcD47, preContact, mem_ofPred_eq, mem_inter_iff, mem_Iio, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h0, -⟩, h1⟩
      exact hq ⟨h0, h1⟩
    rw [e]
    exact MeasurableSet.empty

/-- The capacity clock of good stopped data at a rational pre-contact time up to `t` is measurable. -/
theorem measurable_indicator_capClock_gammaD47 (q : ℚ) (hq0 : (0 : ℝ) ≤ q) (hqt : (q : ℝ) ≤ t) :
    Measurable ({x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1}.indicator
      fun x => capClock (gammaD47 s x.1) q) := by
  classical
  set A := {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1} with hAdef
  have hA : MeasurableSet A := measurableSet_mem_PcD47 q hq0 hqt
  set Γ : {y : Y47 nL nR // IsGoodD47 s t y} → ℝ≥0 → ℂ := fun x r =>
    if x ∈ A then gammaD47 s x.1 (min (r : ℝ) q) else 0 with hΓdef
  have hΓc : ∀ x, Continuous (Γ x) := by
    intro x
    by_cases hx : x ∈ A
    · simp only [hΓdef, hx, ↓reduceIte]
      exact (x.2.cont q hq0 hqt hx).comp_continuous (NNReal.continuous_coe.min continuous_const)
        fun r => ⟨le_min r.coe_nonneg hq0, min_le_right _ _⟩
    · simp only [hΓdef, hx, ↓reduceIte]
      exact continuous_const
  have hΓm : ∀ r, Measurable fun x => Γ x r := fun r =>
    Measurable.ite hA ((measurable_gammaD47 _).comp measurable_subtype_coe) measurable_const
  have hmeas := Restart.measurable_hcapHit_image hΓc hΓm (q : ℝ).toNNReal
  have heq : A.indicator (fun x => capClock (gammaD47 s x.1) q) =
      A.indicator fun x => (WholeField.hcapHit (Γ x '' Icc 0 (q : ℝ).toNNReal)).toReal / 2 := by
    refine indicator_congr fun x hx => ?_
    have himg : gammaD47 s x.1 '' Icc 0 q = Γ x '' Icc 0 (q : ℝ).toNNReal := by
      rw [Sec7.Lemma71E.image_Icc_real_eq hq0]
      refine image_congr fun r hr => ?_
      have hrq : (r : ℝ) ≤ q := by
        have := hr.2
        rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0] at this
      simp only [hΓdef, hx, ↓reduceIte, min_eq_left hrq]
    have h0 : (Γ x 0).im ≤ 0 := by
      simp only [hΓdef, hx, ↓reduceIte, NNReal.coe_zero, min_eq_left hq0, gammaD47, imgCurve, le_refl,
        Complex.zero_im]
    rw [Restart.hcapHit_image_eq (hΓc x).continuousOn h0, ← himg]
    have hnn : 0 ≤ ConformalImage.hcapSet (fillH (gammaD47 s x.1 '' Icc 0 q)) := by
      rw [himg, ConformalImage.hcapSet_eq (Restart.isHPHull_fillH_image (hΓc x).continuousOn h0)]
      exact HPHull.hcap_nonneg _
    rw [ENNReal.toReal_ofReal hnn, capClock]
  rw [heq]
  exact ((ENNReal.measurable_toReal.comp hmeas).div_const _).indicator hA

theorem measurable_indicator_capClock_gammaD47_PD (q : ℚ) :
    Measurable ({x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PD47 t s x.1}.indicator
      fun x => capClock (gammaD47 s x.1) q) := by
  by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) < t
  · have e : {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PD47 t s x.1} =
        {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1} := by
      ext x
      simp only [PD47, mem_ofPred_eq, mem_inter_iff, mem_Iio, hq.2, and_true]
    rw [e]
    exact measurable_indicator_capClock_gammaD47 q hq.1 hq.2.le
  · have e : {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PD47 t s x.1} = ∅ := by
      ext x
      simp only [PD47, PcD47, preContact, mem_ofPred_eq, mem_inter_iff, mem_Iio, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h0, -⟩, h1⟩
      exact hq ⟨h0, h1⟩
    rw [e, indicator_empty]
    exact measurable_const

theorem measurableSet_lt_kcLife_gammaD47 (r : ℝ≥0) :
    MeasurableSet {x : {y : Y47 nL nR // IsGoodD47 s t y} |
      (r : WithTop ℝ≥0) < kcLife (gammaD47 s x.1) (PD47 t s x.1)} :=
  measurableSet_lt_kcLife (fun x => x.2.killed) measurableSet_mem_PD47 measurable_indicator_capClock_gammaD47_PD r

/-- **The killed driver read from good stopped data is measurable.** -/
theorem measurable_kcW_gammaD47 (r : ℝ≥0) :
    Measurable fun x : {y : Y47 nL nR // IsGoodD47 s t y} => kcW (gammaD47 s x.1) (PD47 t s x.1) r :=
  measurable_kcW (fun x => x.2.killed) measurableSet_mem_PD47 measurable_indicator_capClock_gammaD47_PD
    (fun q => (measurable_gammaD47 q).comp measurable_subtype_coe) r

/-- **The images of the left marks read from good stopped data are measurable.** -/
theorem measurable_kcVL_gammaD47 {m : ℕ} (x : Fin m → ℝ) (i : Fin (m + 1)) (r : ℝ≥0) :
    Measurable fun y : {y : Y47 nL nR // IsGoodD47 s t y} =>
      kcVL (gammaD47 s y.1) (PD47 t s y.1) (gXLD47 x s y.1) i r :=
  measurable_kcVL (fun x => x.2.killed) measurableSet_mem_PD47 measurable_indicator_capClock_gammaD47_PD
    (fun q => (measurable_gammaD47 q).comp measurable_subtype_coe)
    ((measurable_gXLD47 x s).comp measurable_subtype_coe) i r

/-- **The images of the right marks read from good stopped data are measurable.** -/
theorem measurable_kcVR_gammaD47 {m : ℕ} (x : Fin m → ℝ) (j : Fin (m + 1)) (r : ℝ≥0) :
    Measurable fun y : {y : Y47 nL nR // IsGoodD47 s t y} =>
      kcVR (gammaD47 s y.1) (PD47 t s y.1) (gXRD47 x s y.1) j r :=
  measurable_kcVR (fun x => x.2.killed) measurableSet_mem_PD47 measurable_indicator_capClock_gammaD47_PD
    (fun q => (measurable_gammaD47 q).comp measurable_subtype_coe)
    ((measurable_gXRD47 x s).comp measurable_subtype_coe) j r

end Good

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
