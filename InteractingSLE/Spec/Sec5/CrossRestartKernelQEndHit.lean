/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndCode
import InteractingSLE.Spec.Wire.PartAClearanceRegularity
import InteractingSLE.Spec.Sec5.CrossRestartKernelQHit

/-!
# Lemma 4.7 in the chart `Q`: the unkilling of the counterflow's image word and the first hit (item E)

Packet PROVE-CFRESTART5, item E. The counterflow's killed image word (PROVE-CFRESTART4, D1; martingale clause D3 and
word entrance D4 in `CrossRestartKernelQEndMarks`) is restarted at a positive rational image time before its
killing (`Prop49Exit.ae_restart_code`, code event `avCode47`): the canonical solution from the restarted state has
infinite lifetime, a transient generating trace whose real values lie between the two seed marks, and it agrees with
the killed word before the killing. Gluing it to the killed trace (`Sec7.IsGeneratingTraceIcc.join`) gives a full
image trace on `[0, ∞)`, transient, never meeting `ℝ ∖ {0}` (on the hull's base interval the boundary values of the
inverse map are `0` or in `ℍ`, `outside_base_of_extendFrom_real_of_mem_H`). PROVE-CFRESTART3's deterministic
`isFirstHitQ_of_imgFull` then gives Lemma 4.7's first hit.

* **`fullTrace_of_restart`** (deterministic gluing);
* `kcVL_zero_eq`, `kcVR_zero_eq`, `not_threshold_q` (the image word at time `0` is below the continuation threshold);
* `qVL_seed_sub`, `qVR_seed_sub`, `extendFrom_base_q` (the restarted seed marks are the base points of the image hull,
  where the inverse map takes the value `0` or lies in `ℍ`);
* `prefix_iwL`, `prefix_iwR` (the image weights' prefix sums are at least `8/κ − 2`; the left total is exactly
  `8/κ − 2`, the right total `16/κ − 4`);
* **`ae_isFirstHitQ_of_clearance`**, **`lemma47QHitStatement_of_partA_of_clearance`**: Lemma 4.7 in the chart `Q`
  (`Prop411Q.Lemma47QHitStatement`) from Zhan's Part A inputs at `16/κ` (clearance form);
  `lemma47QHitStatement_of_inverseBoundary`: the same from (G5) at `16/κ` alone.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q

namespace Kill47

open Prop49Exit Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-! ### The deterministic gluing -/

section Glue

/-- **The full trace from a restart.** Let `γ` generate the chain of `w` (continuous before `T`, from `0`) before
`T`, in `ℍ` at positive times; let `c` be a continuous driver from `0` agreeing with the restarted driver
`w(q + ·) − w(q)` before `T − q` (`0 < q < T`), with a transient generating trace `η` on `[0, ∞)` whose real values lie
in `[eL, eR]`, and let `F̄_q` send `[eL, eR]` to `0` or into `ℍ`. Then there is a continuous transient curve on
`[0, ∞)` extending `γ` before `T` that never meets `ℝ ∖ {0}`. -/
theorem fullTrace_of_restart {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → Sec7.IsGeneratingTraceIcc w s γ)
    (hγH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T → γ t ∈ H) {q : ℝ≥0} (hq0 : 0 < q) (hqT : (q : ℝ≥0∞) < T)
    {c : ℝ≥0 → ℝ} (hcc : Continuous c) (hc0 : c 0 = 0)
    (hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T - q → c t = w (q + t) - w q)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace c ⊤ η) (hηtr : Tendsto (fun t => ‖η t‖) atTop atTop)
    {eL eR : ℝ} (hηR : ∀ t (x : ℝ), η t = x → eL ≤ x ∧ x ≤ eR)
    (hgeo : ∀ x : ℝ, eL ≤ x → x ≤ eR → extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) x = 0 ∨
      extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) x ∈ H) :
    ∃ Γ : ℝ≥0 → ℂ, Continuous Γ ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < T → Γ t = γ t) ∧
      (∀ (t : ℝ≥0) (x : ℝ), x ≠ 0 → Γ t ≠ x) ∧ Tendsto (fun t => ‖Γ t‖) atTop atTop := by
  set F := extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) with hFdef
  obtain ⟨t₂, hqt₂, ht₂T⟩ := exists_real_btwn_of_lt hqT
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg q).trans hqt₂.le
  have hwfz := continuous_frozenDrive_of_lt hwc ht₂T
  have hW0' : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  obtain ⟨hFeq, -, hEq, -, -, -, -⟩ := (hγ q hqT).extend_props hqt₂ hwfz hw0
  have hFH : ∀ v ∈ H, F v ∈ H := fun v hv => by
    rw [hFdef, hFeq, hEq hv]
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hwfz hW0' q.coe_nonneg hv).1
  -- the concatenation `X` of `w` before `q` and `c` after `q`
  set X : ℝ≥0 → ℝ := concatAt q w (w q) c with hXdef
  have hcq : w q + c 0 = w q := by rw [hc0, add_zero]
  have hXc : ContinuousOn X {s | (s : ℝ≥0∞) < (q : ℝ≥0∞) + ⊤} :=
    continuousOn_concatAt hqT hwc (τ₂ := ⊤) hcc.continuousOn hcq
  have hX0 : X 0 = 0 := by rw [hXdef, concatAt_of_lt hq0]; exact hw0
  have hXw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → X t = w t := by
    intro t ht
    rcases lt_or_ge t q with htq | htq
    · exact concatAt_of_lt htq
    · rw [hXdef, concatAt_of_le htq]
      have hlt : ((t - q : ℝ≥0) : ℝ≥0∞) < T - q := by
        rw [Assembly2.coe_lt_sub_iff, add_tsub_cancel_of_le htq]; exact ht
      rw [hagree _ hlt, add_tsub_cancel_of_le htq]
      ring
  have hshift : Sec7.shiftNN X q = c := by
    funext u
    simp only [Sec7.shiftNN, hXdef, concatAt_of_le (le_add_of_nonneg_right zero_le : q ≤ q + u),
      concatAt_of_le (le_refl q), add_tsub_cancel_left, tsub_self, hc0]
    ring
  have h₁ : Sec7.IsGeneratingTraceIcc X q γ :=
    WangWu.ImgDrv.IsGeneratingTraceIcc.congr_of_lt (hγ q hqT) hqT fun t ht => (hXw t ht).symm
  obtain ⟨hJ, hJtr⟩ := Sec7.IsGeneratingTraceIcc.join hXc hX0 h₁ (by rw [hshift]; exact hη)
  set Γ := Sec7.joinTrace X q γ η with hΓdef
  have htop : (q : ℝ≥0∞) + ⊤ = ⊤ := add_top _
  have hΓc : Continuous Γ := by
    rw [htop] at hJ
    exact continuousOn_univ.1 (hJ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hXc' : ContinuousOn X {s | (s : ℝ≥0∞) < ⊤} := by rw [← htop]; exact hXc
  have hJ' : IsGeneratingTrace X ⊤ Γ := by rw [← htop]; exact hJ
  -- the full trace agrees with `γ` before `T`
  have hΓγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → Γ t = γ t := by
    intro t ht
    have e1 : LP.traceAt t X = Γ t := LP.traceAt_eq_of_isGeneratingTrace hJ' hXc' hX0 ENNReal.coe_lt_top
    have e2 : LP.traceAt t X = LP.traceAt t w :=
      LP.traceAt_congr fun s hs => hXw s (lt_of_le_of_lt (by exact_mod_cast hs) ht)
    obtain ⟨s', hs'1, hs'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have e3 : LP.traceAt t w = γ t :=
      LP.traceAt_eq_of_isGeneratingTrace (hγ s' hs'2).1 (hwc.mono fun r hr => lt_trans hr hs'2) hw0 hs'1
    rw [← e1, e2, e3]
  have hfwd : fwdMapInv (fun s : ℝ => X s.toNNReal) q = fwdMapInv (fun s : ℝ => w s.toNNReal) q := by
    refine fwdMapInv_eq_of_eqOn q.coe_nonneg hqt₂ fun r hr => hXw _ ?_
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hr.2) ht₂T
  refine ⟨Γ, hΓc, hΓγ, fun t x hx => ?_, hJtr rfl hηtr⟩
  rcases le_or_gt t q with htq | htq
  · rw [hΓγ t (lt_of_le_of_lt (by exact_mod_cast htq) hqT)]
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
    · rw [← h0, (hγ q hqT).1.1]
      exact fun h => hx (by exact_mod_cast h.symm)
    · intro h
      have hH := hγH t hpos (lt_of_le_of_lt (by exact_mod_cast htq) hqT)
      rw [h] at hH
      exact lt_irrefl _ (show (0 : ℝ) < ((x : ℝ) : ℂ).im from hH |>.trans_eq (by simp))
  · rw [hΓdef, Sec7.joinTrace_of_lt htq, hfwd, ← hFdef]
    have hHb : η (t - q) ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hη hcc.continuousOn hc0
      (le_top : ((t - q : ℝ≥0) : ℝ≥0∞) ≤ ⊤)
    rcases (show (0 : ℝ) ≤ (η (t - q)).im from hHb).lt_or_eq with hpos | h0
    · intro h
      have hH := hFH _ hpos
      rw [h] at hH
      exact lt_irrefl _ (show (0 : ℝ) < ((x : ℝ) : ℂ).im from hH |>.trans_eq (by simp))
    · have hre : η (t - q) = (((η (t - q)).re : ℝ) : ℂ) := Complex.ext rfl (by simp [← h0])
      obtain ⟨h1, h2⟩ := hηR _ _ hre
      rw [hre]
      rcases hgeo _ h1 h2 with hz | hH
      · rw [hz]
        exact fun h => hx (by exact_mod_cast h.symm)
      · intro h
        rw [h] at hH
        exact lt_irrefl _ (show (0 : ℝ) < ((x : ℝ) : ℂ).im from hH |>.trans_eq (by simp))

end Glue

/-! ### The image word at time `0` and the image weights -/

section Zero

open MartChar.RealFlow

variable {γ : ℝ → ℂ} {P : Set ℝ}

/-- The killed left image of a mark `x ≤ 0` at time `0` is the mark. -/
theorem kcVL_zero_eq (hγ : IsKilledCurve γ P) {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, x i ≤ 0) (i : Fin n) :
    kcVL γ P x i 0 = x i := by
  obtain ⟨S, hS, hS0⟩ := hγ.exists_gt 0 hγ.zero_mem
  obtain ⟨Wd, hWd, hWd0, -, -, -, hK⟩ := hγ.localDriver S hS hS0
  have h1 := hγ.eqOn_kcPath_of_localDriver hS hS0 hWd hWd0 (fun u hu => (hK u hu).2)
  rw [kcVL_eq_neg_rightImg hWd h1 (by simpa using hγ.capClock_nonneg hS) hγ.zero_lt_kcLife, NNReal.coe_zero,
    rightImg_zero (show Continuous fun s => -Wd s from hWd.neg) (by simp [hWd0]) (neg_nonneg.2 (hx i))]
  ring

/-- The killed right image of a mark `x ≥ 0` at time `0` is the mark. -/
theorem kcVR_zero_eq (hγ : IsKilledCurve γ P) {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (j : Fin n) :
    kcVR γ P x j 0 = x j := by
  obtain ⟨S, hS, hS0⟩ := hγ.exists_gt 0 hγ.zero_mem
  obtain ⟨Wd, hWd, hWd0, -, -, -, hK⟩ := hγ.localDriver S hS hS0
  have h1 := hγ.eqOn_kcPath_of_localDriver hS hS0 hWd hWd0 (fun u hu => (hK u hu).2)
  rw [kcVR_eq_rightImg hWd h1 (by simpa using hγ.capClock_nonneg hS) hγ.zero_lt_kcLife, NNReal.coe_zero,
    rightImg_zero hWd hWd0 (hx j)]

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The counterflow word at `16/κ` has admissible partial sums** (Remark 4.8 (b), from (4.4)). -/
theorem hasAdmissiblePartialSums_q (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) :
    Sec4.HasAdmissiblePartialSums (16 / κ) (qρL κ ρL ρR xL xR) (qρR κ ρL ρR xL xR) (qxL κ ρL ρR xL xR)
      (qxR κ ρL ρR xL xR) := by
  have hk' : 0 < 16 / κ := by positivity
  have hb := Cond44Ref.isPiecewiseConstant_forceData κ ρL ρR xL xR (-(Real.pi / 2 * QuantumZipper.chiC κ))
  obtain ⟨hbL, hbR⟩ := Sec4.forceBoundaryData_bounds_of_cond44 hκ hκ4 hF h44
  have hbd := CfRegQ.counterflowData_bounds hκ
    (g := fun x => forceBoundaryData κ ρL ρR xL xR x + -(Real.pi / 2 * QuantumZipper.chiC κ))
    (fun x hx => by have := hbL x hx; linarith) (fun x hx => by have := hbR x hx.le; linarith)
  exact Sec4.hasAdmissiblePartialSums_flowLine hk' (Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hb)
    (fun x hx _ => hbd.1 x hx) (fun x hx _ => hbd.2 x hx)

theorem strictAnti_qxL (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    StrictAnti (qxL κ ρL ρR xL xR) := fun _ _ h => Theorem14.GW0.flowLineXL_lt _ _ 0 h

theorem strictMono_qxR (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    StrictMono (qxR κ ρL ρR xL xR) := fun _ _ h => Theorem14.GW0.flowLineXR_lt _ _ 0 h

open Finset in
/-- The counterflow word's left prefix sums are at least `8/κ − 2`. -/
theorem prefix_qρL (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) :
    ∀ m : ℕ, 1 ≤ m → m ≤ flowLineNL (Sec7.StripSysField.counterflowData κ (GlueImg.bData ρL ρR xL xR κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0 →
      16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin _ => i.val < m), qρL κ ρL ρR xL xR i :=
  prefixL_of_hasAdmissiblePartialSums (hasAdmissiblePartialSums_q hκ hκ4 hF h44) (strictAnti_qxL κ ρL ρR xL xR)
    (fun i => Theorem14.GW3Word.flowLineXL_nonpos _ _ i)

open Finset in
/-- The counterflow word's right prefix sums are at least `8/κ − 2`. -/
theorem prefix_qρR (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) :
    ∀ m : ℕ, 1 ≤ m → m ≤ flowLineNR (Sec7.StripSysField.counterflowData κ (GlueImg.bData ρL ρR xL xR κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0 →
      16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin _ => i.val < m), qρR κ ρL ρR xL xR i :=
  prefixR_of_hasAdmissiblePartialSums (hasAdmissiblePartialSums_q hκ hκ4 hF h44) (strictMono_qxR κ ρL ρR xL xR)
    (fun i => Theorem14.GW3Word.flowLineXR_nonneg _ _ i)

open Finset in
/-- **The image word's left prefix sums are at least `8/κ − 2`** (the total is exactly `8/κ − 2`). -/
theorem prefix_iwL (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) :
    ∀ m : ℕ, 1 ≤ m → m ≤ flowLineNL (Sec7.StripSysField.counterflowData κ (GlueImg.bData ρL ρR xL xR κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0 + 1 →
      16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin _ => i.val < m), iwL κ ρL ρR xL xR i := by
  refine prefix_snoc (prefix_qρL hκ hκ4 hF h44) (le_of_eq ?_)
  rw [CrossRestart.slitJunctionL_eq]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

open Finset in
/-- **The image word's right prefix sums are at least `8/κ − 2`** (the total is `16/κ − 4`). -/
theorem prefix_iwR (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) :
    ∀ m : ℕ, 1 ≤ m → m ≤ flowLineNR (Sec7.StripSysField.counterflowData κ (GlueImg.bData ρL ρR xL xR κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0 + 1 →
      16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin _ => i.val < m), iwR κ ρL ρR xL xR i := by
  refine prefix_snoc (prefix_qρR hκ hκ4 hF h44) ?_
  have e : CrossRestart.slitJunctionR κ (Real.pi / 2) (∑ j, qρR κ ρL ρR xL xR j) =
      2 * (16 / κ / 2 - 2) - ∑ j, qρR κ ρL ρR xL xR j := by
    simp only [CrossRestart.slitJunctionR, CrossCond.Theta.cLT]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [e]
  have h8 : 0 ≤ 16 / κ / 2 - 2 := by
    rw [sub_nonneg, div_div, le_div_iff₀ (by positivity)]
    linarith
  linarith

end Zero

/-! ### The seed marks, the threshold at `0`, and the inverse map on the base interval -/

section Seed

open MartChar.RealFlow
open CrossCond.Word49 (psiL psiR junL junR)

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)} {p : Ω × HistorySpace 0 0}

/-- **The restarted left seed mark is the left base point of the image hull.** -/
theorem qVL_seed_sub (hp : p ∈ E) {m : ℕ} {x : Fin m → ℝ} {i₀ : Fin m} (hi₀ : x i₀ = 0) {r : ℝ≥0}
    (hlt : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p) {V : ℝ → ℝ} (hV : Continuous V) {c : ℝ}
    (hEq : EqOn (kcPath (qgCurve W s E p) (qgPre W VL VR ζ s E p)) V (Icc 0 c)) (hrc : (r : ℝ) ≤ c) :
    qVL x W VL VR ζ s E (Fin.castSucc i₀) r p - qW W VL VR ζ s E r p = chartAL V r := by
  rw [qVL, kcVL_eq_neg_rightImg hV hEq hrc hlt, qW, kcW_eq_of_eqOn hEq hrc]
  simp only [qgXL, hp, ↓reduceIte, Fin.snoc_castSucc, hi₀, psiL, ↓reduceIte, neg_zero, chartAL]

/-- **The restarted right seed mark is the right base point of the image hull.** -/
theorem qVR_seed_sub (hp : p ∈ E) {m : ℕ} {x : Fin m → ℝ} {i₀ : Fin m} (hi₀ : x i₀ = 0) {r : ℝ≥0}
    (hlt : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p) {V : ℝ → ℝ} (hV : Continuous V) {c : ℝ}
    (hEq : EqOn (kcPath (qgCurve W s E p) (qgPre W VL VR ζ s E p)) V (Icc 0 c)) (hrc : (r : ℝ) ≤ c) :
    qVR x W VL VR ζ s E (Fin.castSucc i₀) r p - qW W VL VR ζ s E r p = chartAR V r := by
  rw [qVR, kcVR_eq_rightImg hV hEq hrc hlt, qW, kcW_eq_of_eqOn hEq hrc]
  simp only [qgXR, hp, ↓reduceIte, Fin.snoc_castSucc, hi₀, psiR, ↓reduceIte, chartAR]

/-- **On the base interval of the image hull the inverse map takes the value `0` or lies in `ℍ`** (a frozen trace of
the killed word in `ℍ` at positive times). -/
theorem extendFrom_base_q {r : ℝ≥0} {c : ℝ} (hrc : (r : ℝ) < c) {V : ℝ → ℝ} {α' : ℝ → ℂ} (hV : Continuous V)
    (hV0 : V 0 = 0) (hα' : IsLoewnerTrace V α') (hα'H : ∀ u ∈ Ioc (0 : ℝ) r, α' u ∈ H)
    (hEq : EqOn (kcPath (qgCurve W s E p) (qgPre W VL VR ζ s E p)) V (Icc 0 c)) (x : ℝ)
    (hxL : chartAL V r ≤ x) (hxR : x ≤ chartAR V r) :
    extendFrom H (fwdMapInv (fun t : ℝ => qW W VL VR ζ s E t.toNNReal p) r) x = 0 ∨
      extendFrom H (fwdMapInv (fun t : ℝ => qW W VL VR ζ s E t.toNNReal p) r) x ∈ H := by
  have e : fwdMapInv (fun t : ℝ => qW W VL VR ζ s E t.toNNReal p) r = fwdMapInv V r :=
    fwdMapInv_eq_of_eqOn r.coe_nonneg hrc fun t ht => hEq ht
  rw [e]
  rcases (GlueImg.extendFrom_im_nonneg hα' hV hV0 r.coe_nonneg x).lt_or_eq with hpos | h0
  · exact Or.inr hpos
  · left
    set z := extendFrom H (fwdMapInv V r) x with hzdef
    have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [← h0])
    by_contra hne
    have hr0 : z.re ≠ 0 := fun h => hne (by rw [hz, h, Complex.ofReal_zero])
    rcases CrossRestart.outside_base_of_extendFrom_real_of_mem_H hα' hα'H hV hV0 r.coe_nonneg hr0 hz with
      ⟨-, h⟩ | ⟨-, h⟩
    · linarith
    · linarith

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The image word is below the continuation threshold at time `0`** on good samples: the marks at `0` are the
images of the counterflow word's seed marks, a prefix of each side whose weights sum to at least `8/κ − 2 > −2`; the
junctions are not at `0`. -/
theorem not_threshold_q (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) (hs : 0 < s) :
    ¬ ForceWord.ThresholdCondition (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR) (qW W VL VR ζ s E 0 p)
      (fun i => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E i 0 p)
      (fun j => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E j 0 p) := by
  have hg := hEg p hp
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  have hxo := isOrderedForceWord_qx κ ρL ρR xL xR
  have hw := continuous_fDrv hg
  obtain ⟨hjL, hjR⟩ := junction_gaps hg hs
  have hW0 : qW W VL VR ζ s E 0 p = 0 := hγ.kcW_zero
  have hVL : ∀ i, qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E i 0 p = qgXL (qxL κ ρL ρR xL xR) W s E p i :=
    fun i => kcVL_zero_eq hγ _ (qgXL_nonpos hxo.2.1 hEg hs p) i
  have hVR : ∀ j, qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E j 0 p = qgXR (qxR κ ρL ρR xL xR) W s E p j :=
    fun j => kcVR_zero_eq hγ _ (qgXR_nonneg hxo.2.2.2 hEg hs p) j
  have hjL0 : junL (fDrv W p) s ≠ 0 := div_ne_zero (by norm_num) hjL.ne'
  have hjR0 : junR (fDrv W p) s ≠ 0 := div_ne_zero (by norm_num) hjR.ne
  simp only [hW0, hVL, hVR, qgXL, qgXR, hp, ↓reduceIte, ForceWord.ThresholdCondition, not_or, not_le, iwL, iwR,
    CrossRestart.slitRhoL, CrossRestart.slitRhoR]
  rw [Prop49Exit.sum_filter_snoc_eq_zero _ _ _ _ hjL0, Prop49Exit.sum_filter_snoc_eq_zero _ _ _ _ hjR0]
  have eL : (Finset.univ.filter fun i => psiL (fDrv W p) s (qxL κ ρL ρR xL xR i) = 0) =
      Finset.univ.filter fun i => qxL κ ρL ρR xL xR i = 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => Prop49Exit.psiL_ne_zero hw s.coe_nonneg hjL (hxo.2.1 i) h0 h,
      fun h => ?_⟩
    simp [psiL, h]
  have eR : (Finset.univ.filter fun j => psiR (fDrv W p) s (qxR κ ρL ρR xL xR j) = 0) =
      Finset.univ.filter fun j => qxR κ ρL ρR xL xR j = 0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => Prop49Exit.psiR_ne_zero hw s.coe_nonneg hjR (hxo.2.2.2 j) h0 h,
      fun h => ?_⟩
    simp [psiR, h]
  rw [eL, eR]
  have hc : -2 < 16 / κ / 2 - 2 := by have : 0 < 16 / κ / 2 := by positivity
                                      linarith
  refine ⟨Prop49Exit.neg_two_lt_sum_filter_zero hc (fun i i' hii h => ?_) (prefix_qρL hκ hκ4 hF h44),
    Prop49Exit.neg_two_lt_sum_filter_zero hc (fun j j' hjj h => ?_) (prefix_qρR hκ hκ4 hF h44)⟩
  · exact le_antisymm (hxo.2.1 i') (h ▸ hxo.1 hii)
  · exact le_antisymm (h ▸ hxo.2.2.1 hjj) (hxo.2.2.2 j')

end Seed

/-! ### Lemma 4.7 in the chart `Q` -/

section Main

open LQGMetric (DistOn TestOn)

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **Lemma 4.7 at a flow time `s > 0`, in the chart `Q`**: almost surely on the glued space the counterflow first
hits `η((0, s])` at `η(s)` (`Prop411Q.IsFirstHitQ`), given Zhan's Part A inputs at `16/κ` (clearance form). -/
theorem ae_isFirstHitQ_of_clearance (hA : Sec5.PartAInputsSixteenDivOfClearance) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      IsFirstHitQ (seedLine ζ W p.1) (histLine p.2) s := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood47 μ W VL VR ζ with hEdef
  have hNR := CfNoReturn.Route.counterflowNoReturnAdmStatement_of_partA_of_clearance.{u} hA
  have hae := ae_isGood47 hNR hκ hκ4 hF h44 hC hcf hlaw k hk
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  have hX := hC.2.2.2.1
  have hxo := isOrderedForceWord_qx κ ρL ρR xL xR
  obtain ⟨-, hK, hWa, hVLa, hVRa, -, -, -, -, hζq⟩ :=
    filtClauses47 (μ := μ) (s := s) hX hxo.2.1 hxo.1 hxo.2.2.2 hxo.2.2.1 hs hae
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, Bi, hB, hBc, hEnt⟩ := exists_isWordEntrance_q hκ hκ4 hF h44 hC hcf hlaw k hk hae hs
  set 𝓖 := qFilt μ (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s E with h𝓖
  have hTq' : ∀ q : ℝ≥0, MeasurableSet[WholeField.prodFiltration 𝓖 𝓦 q]
      {p : (Ω × HistorySpace 0 0) × Ω₀ | (q : ℝ≥0∞) < (qT W VL VR ζ s E p.1 : ℝ≥0∞)} := fun q =>
    WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hζq q, rfl⟩
  have hthr : ∀ᵐ p ∂(μ.prod P₀), ¬ ForceWord.ThresholdCondition (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
      (qW W VL VR ζ s E 0 p.1) (fun i => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E i 0 p.1)
      (fun j => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E j 0 p.1) := by
    have h1 : ∀ᵐ p ∂μ, ¬ ForceWord.ThresholdCondition (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
        (qW W VL VR ζ s E 0 p) (fun i => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E i 0 p)
        (fun j => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E j 0 p) := by
      filter_upwards [ae_mem_glueGood47 hae] with p hp
      exact not_threshold_q hκ hκ4 hF h44 hEg hp hs
    exact Measure.quasiMeasurePreserving_fst.ae h1
  -- the seed marks `0⁻`, `0⁺` of the counterflow word
  set i₀L : Fin (flowLineNL (Sec7.StripSysField.counterflowData κ (GlueImg.bData ρL ρR xL xR κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0) := ⟨0, Nat.succ_pos _⟩ with hi₀L
  set i₀R : Fin (flowLineNR (Sec7.StripSysField.counterflowData κ (GlueImg.bData ρL ρR xL xR κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0) := ⟨0, Nat.succ_pos _⟩ with hi₀R
  have hx₀L : qxL κ ρL ρR xL xR i₀L = 0 := rfl
  have hx₀R : qxR κ ρL ρR xL xR i₀R = 0 := rfl
  have hk' : 0 < 16 / κ := by positivity
  have hR := Prop49Exit.ae_restart_code (P := μ.prod P₀) (𝓘 := WholeField.prodFiltration 𝓖 𝓦) hk' hB hBc
    (W := fun t p => qW W VL VR ζ s E t p.1) (VL := fun i t p => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E i t p.1)
    (VR := fun j t p => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E j t p.1)
    (Sec7.PhaseSelFull.stronglyAdapted_fst hWa) (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
    (fun j => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa j)) (T := fun p => (qT W VL VR ζ s E p.1 : ℝ≥0∞)) hTq'
    (fun p => (isKilledCurve_qgCurve hEg p.1).zero_lt_kcLife)
    (measurableSet_avCode47 (Fin.castSucc i₀L) (Fin.castSucc i₀R))
    (fun st hsep hFo => codeLaw_compl_avCode47_eq_zero hA hκ hκ4 (prefix_iwL hκ hκ4 hF h44)
      (prefix_iwR hκ hκ4 hF h44) _ _ st hsep hFo)
    hEnt (fun p t ht htT i => hK.sepL p.1 t ht htT i) (fun p t ht htT j => hK.sepR p.1 t ht htT j) hthr
  have h2 := Measure.ae_ae_of_ae_prod hR
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hadmF := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadmF hC.1)
  have htrans := GlueCond.cfGlueAE_mem_goodTransSet_of_clearance.{u} hA κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B
    ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  filter_upwards [h2, ae_mem_glueGood47 hae, hline, htrans] with p hpR hpE ⟨_, _, hβp⟩ hpT
  obtain ⟨ω₀, hpω⟩ := hpR.exists
  have hg := hEg p hpE
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  -- a positive rational image time before the killing
  obtain ⟨S, hSP, hS0⟩ := hγ.exists_gt 0 hγ.zero_mem
  have hcS : 0 < capClock (qgCurve W s E p) S := by
    rw [← hγ.capClock_zero]; exact hγ.strictMonoOn_capClock hγ.zero_mem hSP hS0
  obtain ⟨q', hq'0, hq'S⟩ := exists_rat_btwn hcS
  have hq'0' : (0 : ℚ) < q' := by exact_mod_cast hq'0
  set r : ℝ≥0 := (q' : ℝ).toNNReal with hrdef
  have hr0 : 0 < r := Real.toNNReal_pos.2 hq'0
  have hrT : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hq'S.le)) (hγ.lt_kcLife hSP)
  obtain ⟨x, hxC, hxS, -, hxag⟩ := hpω q' hq'0' hrT
  -- the restarted canonical solution: a transient trace with real values between the seed marks
  obtain ⟨hxF, -⟩ := mem_cRelF_iff.2 hxC
  obtain ⟨hcwc, hcw0⟩ := Prop49Exit.cw_props_of_mem_cRelF hxF
  obtain ⟨hζx, htrSet, hAvQ⟩ := (mem_avCode47_iff hxC).1 hxS
  rw [hζx] at hcwc
  have hcwc' : Continuous (cw x) := continuousOn_univ.1 (hcwc.mono fun t _ => ENNReal.coe_lt_top)
  obtain ⟨η, hη, hηtr⟩ := (mem_traceSet_iff hcwc'.continuousOn hcw0 (fun _ h => absurd h (lt_irrefl _))).1 htrSet
  have heqη : ∀ t, LP.traceAt t (cw x) = η t := fun t =>
    LP.traceAt_eq_of_isGeneratingTrace hη hcwc'.continuousOn hcw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have htrc : Continuous fun t => LP.traceAt t (cw x) := by
    have e : (fun t => LP.traceAt t (cw x)) = η := funext heqη
    rw [e]; exact hηc
  -- a frozen trace of the killed word beyond `r`
  obtain ⟨S', hS'P, hrS'⟩ := hγ.lt_kcLife_iff_exists.1 hrT
  have hcS'0 : 0 ≤ capClock (qgCurve W s E p) S' := hγ.capClock_nonneg hS'P
  obtain ⟨V, α', hV, hV0, hα', hEqV, hα'H⟩ := hγ.exists_frozenTrace (hγ.lt_kcLife hS'P)
  rw [Real.coe_toNNReal _ hcS'0] at hEqV hα'H
  have hL := qVL_seed_sub (x := qxL κ ρL ρR xL xR) hpE hx₀L hrT hV hEqV hrS'.le
  have hR' := qVR_seed_sub (x := qxR κ ρL ρR xL xR) hpE hx₀R hrT hV hEqV hrS'.le
  have hηR : ∀ t (y : ℝ), η t = y → chartAL V r ≤ y ∧ y ≤ chartAR V r := by
    intro t y hy
    have := avoid_of_avQ47 hAvQ htrc t y (by rw [heqη]; exact hy)
    simp only [stAt] at this
    rw [hL, hR'] at this
    exact this
  -- the full image trace
  have hwc := hK.contW p
  have hw0 := hK.w_zero p
  obtain ⟨Γ, hΓc, hΓγ, hΓR, hΓtr⟩ := fullTrace_of_restart (T := (qT W VL VR ζ s E p : ℝ≥0∞)) hwc hw0
    (γ := qTr W VL VR ζ s E p) (fun s' hs' => by
      obtain ⟨T', hs'T', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs'
      exact Sec7.IsGeneratingTrace.isGeneratingTraceIcc (isGeneratingTrace_qTr hEg p hT')
        (hwc.mono fun t ht => lt_trans ht hT') hw0 hs'T')
    (fun t ht0 ht => hγ.kcTr_mem_H ht0 ht) hr0 hrT hcwc' hcw0 (fun t ht => (hxag t ht).1) hη (hηtr rfl) hηR
    (fun y h1 h2 => extendFrom_base_q (c := capClock (qgCurve W s E p) S') hrS' hV hV0 hα'
      (fun u hu => hα'H u ⟨hu.1, hu.2.trans hrS'.le⟩) hEqV y h1 h2)
  -- the deterministic first hit
  have hpre : preContact (histLine p.2) (negInv '' fwdHull (fDrv W p) s) = qgPre W VL VR ζ s E p := by
    rw [qgPre_of_mem hpE, qObs_of_good hg]
  have hGc : IsClosed (negInv '' fwdHull (fDrv W p) s) := by
    rw [← qObs_of_good (q := s) hg]; exact isClosed_qObs hg
  refine isFirstHitQ_of_imgFull (exists_flowTrace hg).1 hβp (continuous_fDrv hg) (fDrv_zero hg)
    (NNReal.coe_pos.2 hs) hGc
    ((Prop49Exit.continuous_traceAt_of_mem_goodCfSet hg.2.2.1.1).comp continuous_real_toNNReal)
    (histLine_zero hg) (fun v hv => histLine_mem_H hg hv) (GlueCond.tendsto_histLine_of_mem_goodTransSet hpT)
    (a := fun u => (capClock (qgCurve W s E p) u).toNNReal) ?_ hΓc hΓR hΓtr ?_
  · rw [hpre]
    intro u hu v hv huv
    exact Real.toNNReal_le_toNNReal (hγ.strictMonoOn_capClock.monotoneOn hu hv huv)
  · rw [hpre]
    intro u hu hu0
    rw [hΓγ _ (hγ.lt_kcLife hu), qTr_capClock hEg hpE hu, imgCurve_of_pos hu0]

end Main

end Kill47

/-- **Lemma 4.7 in the chart `Q` at every positive rational flow time** (`Prop411Q.Lemma47QHitStatement`), from Zhan's
Part A inputs at `16/κ` (clearance form). -/
theorem lemma47QHitStatement_of_partA_of_clearance (hA : Sec5.PartAInputsSixteenDivOfClearance) :
    Prop411Q.Lemma47QHitStatement.{u} := by
  intro q hq κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have := Kill47.ae_isFirstHitQ_of_clearance hA hκ hκ4 hF h44 hC hcf hlaw k hk (s := (q : ℝ).toNNReal)
    (Real.toNNReal_pos.2 hq')
  simpa only [Real.coe_toNNReal _ hq'.le] using this

/-- **Lemma 4.7 in the chart `Q` from Zhan's (G5) at `16/κ` alone** (protected-ray clearance is proved:
`Sec5.partAInputsSixteenDivOfClearance_of_inverseBoundary`). -/
theorem lemma47QHitStatement_of_inverseBoundary
    (hG5 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ)) :
    Prop411Q.Lemma47QHitStatement.{u} :=
  lemma47QHitStatement_of_partA_of_clearance (Sec5.partAInputsSixteenDivOfClearance_of_inverseBoundary hG5)

end InteractingSLE.Sec5.CrossRestart.KernelQ
