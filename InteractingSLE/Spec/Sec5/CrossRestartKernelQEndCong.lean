/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndChart

/-!
# Lemma 4.7 in the chart `Q`: the killed image word's hulls, its local drivers, and the image setup (item D2)

Packet PROVE-CFRESTART5, item D2. For the non-simple killed chain of PROVE-CFRESTART4 (`IsKilledCurve`, `kcW`):

* `IsKilledCurve.eqOn_kcPath_of_localDriver`: the killed driver **is** every local driver of the curve on
  `[0, capClock S]` (the canonical driver formula recovers local drivers, `IsDrivenCurve.segDrv_eq`, through the time
  change); hence `fwdHull_kcPath_capClock` (the killed chain's hull at the capacity time of `u` is the filled prefix
  `fill γ([0, u])`) and the congruences `eqOn_kcPath_of_eqOn`, `kcVR_eq_rightImg`, `kcVL_eq_neg_rightImg`;
* `fillH_imgCurve_eq`: before contact, the filled image prefix is the image of the counterflow hull,
  `fill(Ψ ∘ α([0, u])) = Ψ(K′_u)` (Aux. lemma 8, `Aux8Inf.exists_loewner_revChart_trace`);
* on the glued space: `fillH_qgCurve_eq`, `fwdHull_rpath_qW_capClock`, `fChart_inv_image_eq` (the chart of the field
  pulls the remaining domain of the image word at `σ(t)` back to `ℍ ∖ (A_s ∪ G_t)`);
* **`exists_isCfImgSetup_q`**: on good samples, at a counterflow time `t > 0` before contact, PROVE-CFRESTART2's
  deterministic image setup `IsCfImgSetup` holds for a frozen driver of the killed word agreeing with it beyond `σ(t)`;
* **`meanCan_q_eq`**: the explicit mean of the killed image word at `σ(t)` is the coupling mean of such a driver with
  the flowed image marks (the bridge of PROVE-CFRESTART3's "What remains" D2).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock capLife segDrv segDriver)
open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord (kImg kImg_eq)
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar.RealFlow

/-! ### The killed driver is every local driver -/

section Local

variable {γ γ' : ℝ → ℂ} {P P' : Set ℝ}

namespace IsKilledCurve

/-- **The killed driver agrees with every local driver** of the curve on `[0, capClock S]`. -/
theorem eqOn_kcPath_of_localDriver (hγ : IsKilledCurve γ P) {S : ℝ} (hS : S ∈ P) (hS0 : 0 < S) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0)
    (hK : ∀ t ∈ Icc 0 S, fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t)) :
    EqOn (kcPath γ P) W (Icc 0 (capClock γ S)) := by
  intro r hr
  obtain ⟨t₀, ht₀, hS'⟩ := hγ.exists_kcTime_eq hS
  have ht₀pos : 0 < t₀ := by
    rcases ht₀.eq_or_lt with h | h
    · rw [← h, kcTime_zero] at hS'
      linarith
    · exact h
  have hD := hγ.isDrivenCurve
  have hK' : ∀ t ∈ Icc 0 t₀, fwdHull W (capClock (kcCurve γ P) t) = fillH (kcCurve γ P '' Icc 0 t) := by
    intro t ht
    have hkt : kcTime P t ∈ Icc 0 S := ⟨hγ.kcTime_nonneg ht.1,
      hS' ▸ hγ.strictMonoOn_kcTime.monotoneOn (mem_Ici.2 ht.1) (mem_Ici.2 ht₀) ht.2⟩
    rw [hγ.capClock_kcCurve ht.1, hγ.image_kcCurve_Icc ht.1]
    exact hK _ hkt
  have hcap : capClock (kcCurve γ P) t₀ = capClock γ S := by rw [hγ.capClock_kcCurve ht₀, hS']
  have hlt : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kcLife γ P := by
    obtain ⟨S', hS'P, hSS'⟩ := hγ.exists_gt S hS
    refine hγ.lt_kcLife_iff_exists.2 ⟨S', hS'P, ?_⟩
    rw [Real.coe_toNNReal _ hr.1]
    exact lt_of_le_of_lt hr.2 (hγ.strictMonoOn_capClock hS hS'P hSS')
  show kcW γ P r.toNNReal = W r
  rw [kcW_of_lt hlt]
  show segDrv (kcCurve γ P) (r.toNNReal : ℝ) = W r
  rw [Real.coe_toNNReal _ hr.1]
  exact hD.segDrv_eq ht₀pos hW hW0 hK' hr.1 (hcap ▸ hr.2)

/-- **The killed chain's hull at the capacity time of `u` is the filled prefix** `fill γ([0, u])`. -/
theorem fwdHull_kcPath_capClock (hγ : IsKilledCurve γ P) {u : ℝ} (hu : u ∈ P) :
    fwdHull (kcPath γ P) (capClock γ u) = fillH (γ '' Icc 0 u) := by
  obtain ⟨S, hSP, huS⟩ := hγ.exists_gt u hu
  have hS0 : 0 < S := lt_of_le_of_lt (hγ.nonneg u hu) huS
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver S hSP hS0
  have hEq := hγ.eqOn_kcPath_of_localDriver hSP hS0 hW hW0 (fun t ht => (hK t ht).2)
  have hcu := hγ.capClock_nonneg hu
  have hlt := hγ.strictMonoOn_capClock hu hSP huS
  rw [fwdHull_eq_of_eqOn hcu hlt fun r hr => hEq hr]
  exact (hK u ⟨hγ.nonneg u hu, huS.le⟩).2

/-- **Congruence of killed chains**: two killed curves agreeing on `[0, S]` (`S` before both killings) have the same
killed driver on `[0, capClock S]`. -/
theorem eqOn_kcPath_of_eqOn (hγ : IsKilledCurve γ P) (hγ' : IsKilledCurve γ' P') {S : ℝ} (hS : S ∈ P)
    (hS' : S ∈ P') (hS0 : 0 < S) (hEq : EqOn γ γ' (Icc 0 S)) :
    EqOn (kcPath γ P) (kcPath γ' P') (Icc 0 (capClock γ S)) := by
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver S hS hS0
  have h1 := hγ.eqOn_kcPath_of_localDriver hS hS0 hW hW0 (fun t ht => (hK t ht).2)
  have hcc : ∀ t ∈ Icc 0 S, capClock γ t = capClock γ' t := fun t ht =>
    WangWu.capClock_congr (hEq.mono (Icc_subset_Icc_right ht.2))
  have himg : ∀ t ∈ Icc 0 S, γ '' Icc 0 t = γ' '' Icc 0 t := fun t ht =>
    image_congr (hEq.mono (Icc_subset_Icc_right ht.2))
  have h2 := hγ'.eqOn_kcPath_of_localDriver hS' hS0 hW hW0 (fun t ht => by
    rw [← hcc t ht, ← himg t ht]
    exact (hK t ht).2)
  intro r hr
  rw [h1 hr, h2 (by rwa [← hcc S ⟨hS0.le, le_rfl⟩])]

end IsKilledCurve

/-- The right mark images read through a continuous driver agreeing with the killed driver. -/
theorem kcVR_eq_rightImg {W : ℝ → ℝ} (hW : Continuous W) {c : ℝ} (hEq : EqOn (kcPath γ P) W (Icc 0 c))
    {r : ℝ≥0} (hr : (r : ℝ) ≤ c) (hlt : (r : WithTop ℝ≥0) < kcLife γ P) {n : ℕ} (xR : Fin n → ℝ) (j : Fin n) :
    kcVR γ P xR j r = rightImg W (xR j) r := by
  rw [kcVR_of_lt _ _ hlt, kcVRr, kImg_eq hW hEq hr]

/-- The left mark images read through a continuous driver agreeing with the killed driver. -/
theorem kcVL_eq_neg_rightImg {W : ℝ → ℝ} (hW : Continuous W) {c : ℝ} (hEq : EqOn (kcPath γ P) W (Icc 0 c))
    {r : ℝ≥0} (hr : (r : ℝ) ≤ c) (hlt : (r : WithTop ℝ≥0) < kcLife γ P) {n : ℕ} (xL : Fin n → ℝ) (i : Fin n) :
    kcVL γ P xL i r = -rightImg (fun s => -W s) (-xL i) r := by
  rw [kcVL_of_lt _ _ hlt, kcVLr, kImg_eq (show Continuous fun s => -W s from hW.neg)
    (fun s hs => by simp only [hEq hs]) hr]

theorem kcW_eq_of_eqOn {W : ℝ → ℝ} {c : ℝ} (hEq : EqOn (kcPath γ P) W (Icc 0 c)) {r : ℝ≥0} (hr : (r : ℝ) ≤ c) :
    kcW γ P r = W r := by
  rw [← kcPath_coe]
  exact hEq ⟨r.coe_nonneg, hr⟩

end Local

/-! ### The filled image prefixes are the images of the counterflow hulls -/

section Fill

variable {Wf Wc : ℝ → ℝ} {q : ℝ} {α : ℝ → ℂ}

/-- **Before contact, the filled image prefix is the image of the counterflow hull** (Aux. lemma 8). -/
theorem fillH_imgCurve_eq (hWf : Continuous Wf) (hWf0 : Wf 0 = 0) (hq : 0 ≤ q)
    (hG : IsClosed (negInv '' fwdHull Wf q)) (hKq : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wf q))
    (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (hα : IsLoewnerTrace Wc α) (hαH : ∀ u, 0 < u → α u ∈ H)
    (hdis : ∀ S ∈ preContact α (negInv '' fwdHull Wf q),
      Disjoint (closure (fwdHull Wc S)) (closure (negInv '' fwdHull Wf q)))
    {u : ℝ} (hu : u ∈ preContact α (negInv '' fwdHull Wf q)) :
    fillH (imgCurve Wf q α '' Icc 0 u) = revChart Wf q '' fwdHull Wc u := by
  have hα0 : α 0 = 0 := hα.1
  have hαc : ContinuousOn α (Ici 0) := hα.2.1
  have hkc := isKilledCurve_imgCurve hWf hWf0 hq hG hKq hWc hWc0 hα hαH hdis
  rcases hu.1.eq_or_lt with h0 | hpos
  · rw [← h0, Icc_self, image_singleton, imgCurve_zero, fillH_singleton_zero, hα.2.2 0 le_rfl, Icc_self,
      image_singleton, hα0, fillH_singleton_zero, image_empty]
  obtain ⟨τ, W', -, -, -, -, -, hK, hfill, -⟩ :=
    Aux8Inf.exists_loewner_revChart_trace (Wα := Wf) (Wβ := Wc) hWf hWf0 hq hKq hWc hWc0 hu.1 (hdis u hu)
      hα0 (hαc.mono Icc_subset_Ici_self) (fun t ht => Or.inl (hαH t ht.1)) fun t ht => by
        rw [hα.2.2 t ht.1.le]
        exact isFilling_fillH (isCompact_Icc.image_of_continuousOn (hαc.mono fun v hv => hv.1))
  have himg : imgCurve Wf q α '' Icc 0 u = insert 0 (revChart Wf q '' (α '' Icc 0 u ∩ H)) := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hv.1.eq_or_lt with hv0 | hvpos
      · rw [← hv0, imgCurve_zero]; exact mem_insert _ _
      · rw [imgCurve_of_pos hvpos]
        exact mem_insert_of_mem _ ⟨α v, ⟨⟨v, hv, rfl⟩, hαH v hvpos⟩, rfl⟩
    · rintro (rfl | ⟨w, ⟨⟨v, hv, rfl⟩, hwH⟩, rfl⟩)
      · exact ⟨0, ⟨le_rfl, hu.1⟩, imgCurve_zero⟩
      · rcases hv.1.eq_or_lt with hv0 | hvpos
        · rw [← hv0, hα0] at hwH
          exact absurd (show (0 : ℝ) < (0 : ℂ).im from hwH) (lt_irrefl _)
        · exact ⟨v, hv, imgCurve_of_pos hvpos⟩
  have hcpt : IsCompact (imgCurve Wf q α '' Icc 0 u) :=
    isCompact_Icc.image_of_continuousOn (hkc.cont.mono (hkc.icc u hu))
  have hF : IsFilling (fwdHull W' (τ u)) (imgCurve Wf q α '' Icc 0 u) := by
    have h := hfill u ⟨hpos, le_rfl⟩
    unfold IsFilling at h ⊢
    rwa [himg, H_diff_insert_zero]
  have h2 := (isFilling_iff_inter_H_eq_fillH hcpt.isBounded hcpt.isClosed).1 hF
  rw [← h2, inter_eq_left.2 (fun z hz => hz.1), (hK u ⟨hu.1, le_rfl⟩).2]

/-- `fillH_imgCurve_eq` from generating traces (the hypotheses of `isKilledCurve_imgCurve_of_traces`). -/
theorem fillH_imgCurve_eq_of_traces {wf wc : ℝ≥0 → ℝ} {ηf ηc : ℝ≥0 → ℂ} (hwf : Continuous wf)
    (hwf0 : wf 0 = 0) (hηf : IsGeneratingTrace wf ⊤ ηf) (hηfH : ∀ t : ℝ≥0, 0 < t → ηf t ∈ H)
    (hwc : Continuous wc) (hwc0 : wc 0 = 0) (hηc : IsGeneratingTrace wc ⊤ ηc)
    (hηcH : ∀ t : ℝ≥0, 0 < t → ηc t ∈ H) (q : ℝ≥0) {u : ℝ}
    (hu : u ∈ preContact (fun s : ℝ => ηc s.toNNReal) (negInv '' fwdHull (fun r : ℝ => wf r.toNNReal) q)) :
    fillH (imgCurve (fun r : ℝ => wf r.toNNReal) q (fun s : ℝ => ηc s.toNNReal) '' Icc 0 u) =
      revChart (fun r : ℝ => wf r.toNNReal) q '' fwdHull (fun r : ℝ => wc r.toNNReal) u := by
  have hWf : Continuous fun r : ℝ => wf r.toNNReal := hwf.comp continuous_real_toNNReal
  have hWc : Continuous fun r : ℝ => wc r.toNNReal := hwc.comp continuous_real_toNNReal
  have hqT : ((q : ℝ≥0) : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have hH : ∀ r : ℝ≥0, 0 < r → r ≤ q → ηf r ∈ H := fun r hr _ => hηfH r hr
  refine fillH_imgCurve_eq hWf (by simpa using hwf0) q.coe_nonneg
    (GlueCond.isClosed_image_negInv_fwdHull hWf hηf hqT hH)
    (fun x hx => GlueCond.ofReal_notMem_closure_fwdHull hWf hηf hqT hH hx) hWc (by simpa using hwc0)
    (isLoewnerTrace_of_isGeneratingTrace hηc) (fun u hu => hηcH _ (Real.toNNReal_pos.2 hu)) (fun S hS => ?_) hu
  have hS0 : 0 ≤ S := hS.1
  have hsep : ∀ t ∈ Icc (0 : ℝ≥0) q, ηf t ≠ 0 → -(ηf t)⁻¹ ∉ ηc '' Icc 0 S.toNNReal := by
    rintro t ht hne ⟨u, hu, hue⟩
    have ht0 : 0 < t := by
      refine pos_iff_ne_zero.2 fun h => hne ?_
      rw [h, hηf.1]
    have hmemK : ηf t ∈ fwdHull (fun r : ℝ => wf r.toNNReal) q :=
      CrossRestart.inter_H_subset_of_isFilling (hηf.2.2 q hqT) ⟨⟨t, ht, rfl⟩, hηfH t ht0⟩
    have huS : (u : ℝ) ≤ S := by
      have := NNReal.coe_le_coe.2 hu.2
      rwa [Real.coe_toNNReal _ hS0] at this
    refine hS.2 u ⟨u.coe_nonneg, huS⟩ ⟨ηf t, hmemK, ?_⟩
    show -(ηf t)⁻¹ = ηc (u : ℝ).toNNReal
    rw [Real.toNNReal_coe, hue]
  have h := Supp8.GB6.disjoint_closure_fwdHull_inv_image hηc hwc.continuousOn hwc0 hηf hwf.continuousOn hwf0
    (s := S.toNNReal) ENNReal.coe_lt_top hqT hsep
  rwa [Real.coe_toNNReal _ hS0] at h

end Fill

/-! ### The glued image curve -/

namespace Kill47

section Glue

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)} {p : Ω × HistorySpace 0 0}

theorem hullAt_flow_of_good (hg : IsGood47 W VL VR ζ p) :
    hullAt s (killedHistory W VL VR ζ p.1) = fwdHull (fDrv W p) s := by
  rw [hullAt, Aux50Hit.regHull_stopHistory_cstop hg.1 s]
  rfl

/-- **The filled image prefix is the image of the counterflow hull** (good sample, before contact). -/
theorem fillH_qgCurve_eq (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) {u : ℝ}
    (hu : u ∈ qgPre W VL VR ζ s E p) :
    fillH (qgCurve W s E p '' Icc 0 u) = revChart (fDrv W p) s '' fwdHull (cfDrv p.2) u := by
  have hg := hEg p hp
  rw [qgPre_of_mem hp, qObs_of_good hg] at hu
  rw [qgCurve_of_mem hp]
  obtain ⟨hgp, ⟨η, hη, hηH, -⟩, hy, -⟩ := id hg
  obtain ⟨⟨-, hcd⟩, -⟩ := id hy.1
  exact fillH_imgCurve_eq_of_traces (continuous_flow hg) hgp.2.1 hη hηH hcd.continuous hcd.zero
    (GlueCond.isGeneratingTrace_of_mem_goodCfSet hy.1) (fun t ht => by
      have := histLine_mem_H hg (u := t) ht
      rw [CfRegQ.histLine_eq_traceAt] at this
      simpa only [Real.toNNReal_coe] using this) s hu

/-- **The image hull at `σ(u)` is the image of the counterflow hull.** -/
theorem fwdHull_rpath_qW_capClock (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) {u : ℝ}
    (hu : u ∈ qgPre W VL VR ζ s E p) :
    fwdHull (Ito.rpath fun r => qW W VL VR ζ s E r p) (capClock (qgCurve W s E p) u) =
      revChart (fDrv W p) s '' fwdHull (cfDrv p.2) u := by
  rw [← fillH_qgCurve_eq hEg hp hu]
  exact (isKilledCurve_qgCurve hEg p).fwdHull_kcPath_capClock hu

/-- Before contact, the closures of the counterflow hull and of `G = R(K_s)` are disjoint (good sample). -/
theorem disjoint_closure_cf_flow (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) {u : ℝ}
    (hu : u ∈ qgPre W VL VR ζ s E p) :
    Disjoint (closure (fwdHull (cfDrv p.2) u)) (closure (negInv '' fwdHull (fDrv W p) s)) := by
  have hg := hEg p hp
  rw [qgPre_of_mem hp, qObs_of_good hg] at hu
  obtain ⟨hgp, ⟨ηf, hηf, hηfH, -⟩, hy, -⟩ := id hg
  obtain ⟨⟨-, hcd⟩, -⟩ := id hy.1
  have hηc := GlueCond.isGeneratingTrace_of_mem_goodCfSet hy.1
  have hS0 : 0 ≤ u := hu.1
  have hqT : ((s : ℝ≥0) : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have hsep : ∀ t ∈ Icc (0 : ℝ≥0) s, ηf t ≠ 0 →
      -(ηf t)⁻¹ ∉ (fun s => LP.traceAt s (hDrv p.2)) '' Icc 0 u.toNNReal := by
    rintro t ht hne ⟨v, hv, hve⟩
    have ht0 : 0 < t := by
      refine pos_iff_ne_zero.2 fun h => hne ?_
      rw [h, hηf.1]
    have hmemK : ηf t ∈ fwdHull (fDrv W p) s :=
      CrossRestart.inter_H_subset_of_isFilling (hηf.2.2 s hqT) ⟨⟨t, ht, rfl⟩, hηfH t ht0⟩
    have hvS : (v : ℝ) ≤ u := by
      have := NNReal.coe_le_coe.2 hv.2
      rwa [Real.coe_toNNReal _ hS0] at this
    refine hu.2 v ⟨v.coe_nonneg, hvS⟩ ⟨ηf t, hmemK, ?_⟩
    show -(ηf t)⁻¹ = LP.traceAt (v : ℝ).toNNReal (hDrv p.2)
    rw [Real.toNNReal_coe]
    exact hve.symm ▸ rfl
  have h := Supp8.GB6.disjoint_closure_fwdHull_inv_image hηc hcd.continuous.continuousOn hcd.zero hηf
    (continuous_flow hg).continuousOn hgp.2.1 (s := u.toNNReal) ENNReal.coe_lt_top hqT hsep
  rw [Real.coe_toNNReal _ hS0] at h
  exact h

/-- Before contact, the counterflow hull misses `G = R(K_s)`. -/
theorem disjoint_cf_flow (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) {u : ℝ}
    (hu : u ∈ qgPre W VL VR ζ s E p) :
    Disjoint (fwdHull (cfDrv p.2) u) (negInv '' fwdHull (fDrv W p) s) :=
  (disjoint_closure_cf_flow hEg hp hu).mono subset_closure subset_closure

/-- **The chart of the field pulls the remaining domain of the image word at `σ(u)` back to `ℍ ∖ (A_s ∪ G_u)`**
(good sample, `u` before contact). -/
theorem fChart_inv_image_eq (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) {u : ℝ≥0}
    (hu : (u : ℝ) ∈ qgPre W VL VR ζ s E p) :
    (fChart W VL VR ζ s p).2.1 '' (H \ fwdHull (Ito.rpath fun r => qW W VL VR ζ s E r p)
      (((capClock (qgCurve W s E p) u).toNNReal : ℝ≥0) : ℝ)) =
      H \ (hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ u p.2) := by
  have hg := hEg p hp
  obtain ⟨-, -, hy, -⟩ := id hg
  have hWf := continuous_fDrv hg
  have hWf0 := fDrv_zero hg
  have hcap0 : 0 ≤ capClock (qgCurve W s E p) u := (isKilledCurve_qgCurve hEg p).capClock_nonneg hu
  rw [Real.coe_toNNReal _ hcap0, fwdHull_rpath_qW_capClock hEg hp hu, hullAt_flow_of_good hg, cfHullQ,
    hullAt_eq_fwdHull_of_mem_goodCfSet hy.1 u]
  have hsub : fwdHull (cfDrv p.2) u ⊆ H \ negInv '' fwdHull (fDrv W p) s := fun z hz =>
    ⟨(isHPHull_fwdHull (reg_of_mem_goodCfSet hy.1).2.1 u.coe_nonneg).1 hz,
      fun h => disjoint_left.1 (disjoint_cf_flow hEg hp hu) hz h⟩
  have himg : (fChart W VL VR ζ s p).2.1 '' (H \ revChart (fDrv W p) s '' fwdHull (cfDrv p.2) u) =
      negInv '' (revChartInv (fDrv W p) s '' (H \ revChart (fDrv W p) s '' fwdHull (cfDrv p.2) u)) := by
    rw [image_image]
    refine image_congr fun w hw => ?_
    rw [fChart_inv_eq hg hw.1, revChartInv, WangWu.negInv_negInv]
  rw [himg, CrossCond.Word49.revChartInv_image_H_diff_union hWf hWf0 s.coe_nonneg hsub,
    negInv_image_H_diff_union, union_comm]

/-- **The deterministic image setup at a counterflow time `t > 0` before contact** (good sample): a frozen driver of
the killed image word, agreeing with it on `[0, c]` for some `c > σ(t)`, satisfies PROVE-CFRESTART2's `IsCfImgSetup`
with the image time `σ(t)`. -/
theorem exists_isCfImgSetup_q (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) (hs : 0 < s) {t : ℝ}
    (ht : 0 < t) (htP : t ∈ qgPre W VL VR ζ s E p) :
    ∃ (W' : ℝ → ℝ) (η' : ℝ → ℂ) (c : ℝ), IsCfImgSetup (cfDrv p.2) (histLine p.2) t (fDrv W p) s W' η'
      (capClock (qgCurve W s E p) t) ∧ capClock (qgCurve W s E p) t < c ∧
      EqOn (kcPath (qgCurve W s E p) (qgPre W VL VR ζ s E p)) W' (Icc 0 c) := by
  have hg := hEg p hp
  obtain ⟨-, -, hy, -⟩ := id hg
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  set γ := qgCurve W s E p with hγdef
  set P := qgPre W VL VR ζ s E p with hPdef
  obtain ⟨S, hSP, htS⟩ := hγ.exists_gt t htP
  obtain ⟨S₂, hS₂P, hSS₂⟩ := hγ.exists_gt S hSP
  have hS0 : 0 < S := ht.trans htS
  have hS₂0 : 0 < S₂ := hS0.trans hSS₂
  set T₂ := capClock γ S₂ with hT₂
  have hT₂0 : 0 ≤ T₂ := hγ.capClock_nonneg hS₂P
  obtain ⟨V, α', hV, hV0, hα', hEq, hα'H⟩ := hγ.exists_frozenTrace (hγ.lt_kcLife hS₂P)
  rw [Real.coe_toNNReal _ hT₂0] at hEq hα'H
  have hmono : ∀ {a b : ℝ}, a ∈ P → b ∈ P → a ≤ b → capClock γ a ≤ capClock γ b := fun ha hb hab =>
    hγ.strictMonoOn_capClock.monotoneOn ha hb hab
  have hlt : ∀ r ∈ Icc t S, capClock γ r < T₂ := fun r hr =>
    lt_of_le_of_lt (hmono (hγ.icc S hSP ⟨ht.le.trans hr.1, hr.2⟩) hSP hr.2) (hγ.strictMonoOn_capClock hSP hS₂P hSS₂)
  have hmemP : ∀ r ∈ Icc t S, r ∈ P := fun r hr => hγ.icc S hSP ⟨ht.le.trans hr.1, hr.2⟩
  have hhull : ∀ r ∈ Icc t S, fwdHull V (capClock γ r) = revChart (fDrv W p) s '' fwdHull (cfDrv p.2) r := by
    intro r hr
    rw [← fwdHull_eq_of_eqOn (hγ.capClock_nonneg (hmemP r hr)) (hlt r hr) fun x hx => hEq hx]
    exact fwdHull_rpath_qW_capClock hEg hp (hmemP r hr)
  have hT0 : 0 < capClock γ t := by
    rw [← hγ.capClock_zero]
    exact hγ.strictMonoOn_capClock hγ.zero_mem htP ht
  have htT : t ∈ Icc t S := ⟨le_rfl, htS.le⟩
  refine ⟨V, α', T₂, ?_, hlt t htT, hEq⟩
  have hWc := (reg_of_mem_goodCfSet hy.1).2.1
  have hWc0 := (reg_of_mem_goodCfSet hy.1).2.2.1
  obtain ⟨hfl, hflH⟩ := exists_flowTrace hg
  have hjg := junction_gaps hg hs
  have hGc : IsClosed (negInv '' fwdHull (fDrv W p) s) := by
    rw [← qObs_of_good (q := s) hg]
    exact isClosed_qObs hg
  have hKs : ∀ z ∈ closure (fwdHull (fDrv W p) s), z.im = 0 → z = 0 := by
    obtain ⟨-, ⟨ηf, hηf, hηfH, -⟩, -⟩ := id hg
    intro z hz hzi
    by_contra hz0
    have hre : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hzi])
    have hx : z.re ≠ 0 := fun h => hz0 (by rw [hre, h, Complex.ofReal_zero])
    exact GlueCond.ofReal_notMem_closure_fwdHull (continuous_fDrv hg) hηf ENNReal.coe_lt_top
      (fun r hr _ => hηfH r hr) hx (hre ▸ hz)
  have hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull (cfDrv p.2) t) := fun x hx hmem =>
    hx (by exact_mod_cast (isClosed_negInv_fwdHull_of_mem_goodHitSet hy ht.le).2 _ hmem (by simp))
  refine ⟨hWc, hWc0, ht, (reg_of_mem_goodCfSet hy.1).2.2.2, fun r hr => histLine_mem_H hg hr.1,
    continuous_fDrv hg, fDrv_zero hg, s.coe_nonneg, hfl.hasBdryLimits (continuous_fDrv hg) (fDrv_zero hg)
      s.coe_nonneg, hKs, hjg.1, hjg.2, hGc, disjoint_cf_flow hEg hp htP,
    CrossCond.Word49.disjoint_closure_fwdHull_negInv hWc ht.le hKt (continuous_fDrv hg) s.coe_nonneg
      (disjoint_cf_flow hEg hp htP), hV, hV0, hT0, hα', fun r hr => hα'H r ⟨hr.1, hr.2.trans (hlt t htT).le⟩,
    hhull t htT, ⟨capClock γ, S - t, by linarith, ?_, rfl, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩⟩
  · obtain ⟨-, -, -, -, -, hc, -⟩ := hγ.localDriver S₂ hS₂P hS₂0
    have hnhds : Icc 0 S₂ ∈ 𝓝[Ici t] t :=
      mem_nhdsWithin.2 ⟨Iio S₂, isOpen_Iio, htS.trans hSS₂, fun u hu => ⟨ht.le.trans hu.2, le_of_lt hu.1⟩⟩
    exact (hc t ⟨ht.le, (htS.trans hSS₂).le⟩).mono_of_mem_nhdsWithin hnhds
  · have hr' : r ∈ Icc t S := ⟨hr.1, by linarith [hr.2]⟩
    exact hmono htP (hmemP r hr') hr.1
  · have hr' : r ∈ Icc t S := ⟨hr.1, by linarith [hr.2]⟩
    exact disjoint_cf_flow hEg hp (hmemP r hr')
  · have hr' : r ∈ Icc t S := ⟨hr.1, by linarith [hr.2]⟩
    exact hhull r hr'

/-- **The explicit mean of the killed image word at an image time `T` is the coupling mean of any continuous driver
agreeing with the killed driver on `[0, c]`, `c ≥ T`**, with the flowed image marks (good sample). -/
theorem meanCan_q_eq {m₁ m₂ : ℕ} {xL : Fin m₁ → ℝ} {xR : Fin m₂ → ℝ} (hp : p ∈ E) {T c : ℝ} (hT : 0 ≤ T)
    (hTc : T ≤ c) (hlt : ((T.toNNReal : ℝ≥0) : WithTop ℝ≥0) < qT W VL VR ζ s E p) {W' : ℝ → ℝ}
    (hW' : Continuous W') (hEq : EqOn (kcPath (qgCurve W s E p) (qgPre W VL VR ζ s E p)) W' (Icc 0 c)) (a : ℝ)
    (ρL' : Fin (m₁ + 1) → ℝ) (ρR' : Fin (m₂ + 1) → ℝ) (y : ℂ) :
    Coupling.meanCan a ρL' ρR' (fun r => qW W VL VR ζ s E r p) (fun i r => qVL xL W VL VR ζ s E i r p)
        (fun j r => qVR xR W VL VR ζ s E j r p) T.toNNReal y =
      Ito.meanHarmonic a ρL' ρR'
        (fun i => -rightImg (fun r => -W' r) (-GlueImg.imgMarkL xL (fDrv W p) s i) T - W' T)
        (fun j => rightImg W' (GlueImg.imgMarkR xR (fDrv W p) s j) T - W' T) (fwdMap W' T y) -
        chiC a * (logDerivFwd W' T y).im := by
  have hT' : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal _ hT
  have hTc' : ((T.toNNReal : ℝ≥0) : ℝ) ≤ c := hT'.symm ▸ hTc
  have hWT : qW W VL VR ζ s E T.toNNReal p = W' T := by
    rw [qW, kcW_eq_of_eqOn hEq hTc', hT']
  have hXL : qgXL xL W s E p = GlueImg.imgMarkL xL (fDrv W p) s := by simp only [qgXL, hp, ↓reduceIte]
  have hXR : qgXR xR W s E p = GlueImg.imgMarkR xR (fDrv W p) s := by simp only [qgXR, hp, ↓reduceIte]
  have hVL : ∀ i, qVL xL W VL VR ζ s E i T.toNNReal p - qW W VL VR ζ s E T.toNNReal p =
      -rightImg (fun r => -W' r) (-GlueImg.imgMarkL xL (fDrv W p) s i) T - W' T := fun i => by
    rw [hWT, qVL, kcVL_eq_neg_rightImg hW' hEq hTc' hlt, hXL, hT']
  have hVR : ∀ j, qVR xR W VL VR ζ s E j T.toNNReal p - qW W VL VR ζ s E T.toNNReal p =
      rightImg W' (GlueImg.imgMarkR xR (fDrv W p) s j) T - W' T := fun j => by
    rw [hWT, qVR, kcVR_eq_rightImg hW' hEq hTc' hlt, hXR, hT']
  have hrp : EqOn (Ito.rpath fun r => qW W VL VR ζ s E r p) W' (Icc 0 T) := fun r hr =>
    hEq ⟨hr.1, hr.2.trans hTc⟩
  have hfwd : fwdMap (Ito.rpath fun r => qW W VL VR ζ s E r p) (T.toNNReal : ℝ) y = fwdMap W' T y := by
    rw [hT']
    exact Ito.fwdMap_congr_of_eqOn hrp
  have hlog : logDerivFwd (Ito.rpath fun r => qW W VL VR ζ s E r p) (T.toNNReal : ℝ) y = logDerivFwd W' T y := by
    rw [hT']
    exact Ito.logDerivFwd_congr_of_eqOn hrp hT le_rfl
  rw [Coupling.meanCan, hfwd, hlog]
  congr 2
  · funext i; exact hVL i
  · funext j; exact hVR j

end Glue

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
