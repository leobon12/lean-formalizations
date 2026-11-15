/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepImg
import InteractingSLE.Spec.Sec5.GlueCondUnionImgCf
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.Spec.Sec7.Lemma71BStop
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Supplement.LP3Flow

/-!
# Prop 5.9's root stage: the image start is strictly ordered

Packet PROVE-STAGED-REP. `exists_isKilledStageRep_img` asks for the strict order of the image start (the
representation's start must be a strictly ordered word). This file proves it almost surely on the glued space for a
strictly ordered flow word:

* `cfDrv0_eq_hDrv`, **`alive_cfDrv0_of_mem_goodHitSet`**: on a good hitting history the counterflow trace avoids
  `ℝ ∖ {0}`, so every nonzero real point is alive at time `s` for the stopped driver `cfDrv0 s y` (the landed
  `alive_of_trace_off`, for the negative points through the reflected trace);
* `psiL_lt_psiL`, `junL_lt_psiL`, `psiR_lt_psiR`, `psiR_lt_junR`: the chart images of real points are strictly
  ordered when all the relevant points are alive (`rightImg_lt_gImg_of_lt`);
* `strictAnti_snoc`, `strictMono_snoc`;
* **`ae_strict_imgStart`**: almost surely on the glued space the image start `(imgVL · 0, imgVR · 0)` is strictly
  ordered; **`exists_isKilledStageRep_img'`**: the root-stage representation without the hypothesis `hstr`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedRep

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond.Word49 MartChar.RealFlow Prop49Exit LawUnique Cond44Ref Prop411Q
open Prop59Stage Prop59Nodes StagedKill StagedKCand

/-! ### Every nonzero real point is alive for a good counterflow history -/

section Alive

/-- On a good history the stopped driver is the history's driver on `[0, s]`. -/
theorem cfDrv0_eq_hDrv {y : HistorySpace 0 0} (hy : y ∈ CfRegQ.goodCfSet) {s : ℝ≥0} {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) s) : cfDrv0 s y r = CfRegQ.hDrv y r.toNNReal := by
  have hrs : r.toNNReal ≤ s := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  have h0 : CfRegQ.hDrv y 0 = 0 := by
    obtain ⟨⟨_, hc⟩, _⟩ := hy
    exact hc.zero
  simp only [cfDrv0, Ito.rpath, GlueCond.regPath_cfStop_of_mem_goodCfSet hy, min_eq_left hrs,
    Real.toNNReal_zero, min_eq_left (zero_le : (0 : ℝ≥0) ≤ s), h0, sub_zero]

/-- **Every nonzero real point is alive** at time `s` for the stopped counterflow driver of a good hitting history
(its trace avoids `ℝ ∖ {0}`). -/
theorem alive_cfDrv0_of_mem_goodHitSet {y : HistorySpace 0 0} (hy : y ∈ GlueCond.goodHitSet) (s : ℝ≥0) {a : ℝ}
    (ha : 0 < a) : Alive (cfDrv0 s y) a s ∧ Alive (fun r => -cfDrv0 s y r) a s := by
  have hcf : y ∈ CfRegQ.goodCfSet := hy.1
  have hg := GlueCond.isGeneratingTrace_of_mem_goodCfSet hcf
  obtain ⟨⟨_, hc⟩, _⟩ := hcf
  have hw : Continuous (CfRegQ.hDrv y) := hc.continuous
  have hw0 : CfRegQ.hDrv y 0 = 0 := hc.zero
  have htr0 : LP.traceAt 0 (CfRegQ.hDrv y) = 0 := hg.1
  have ht₂ : ENNReal.ofReal ((s : ℝ) + 1) < ⊤ := ENNReal.ofReal_lt_top
  have hst : (s : ℝ) < s + 1 := by linarith
  have heq : ∀ (v : ℝ≥0 → ℝ) (sg : ℝ), (∀ r : ℝ≥0, v r = sg * CfRegQ.hDrv y r) →
      EqOn (frozenDrive v ((s : ℝ) + 1)) (fun r => sg * cfDrv0 s y r) (Icc 0 (s : ℝ)) := by
    intro v sg hv r hr
    rw [frozenDrive_eq ⟨hr.1, hr.2.trans hst.le⟩, hv]
    show sg * CfRegQ.hDrv y r.toNNReal = sg * cfDrv0 s y r
    rw [cfDrv0_eq_hDrv hy.1 hr]
  constructor
  · -- positive points: the trace avoids `[a, ∞)`
    have hoff : ∀ u ≤ s, ∀ r : ℝ, a ≤ r → LP.traceAt u (CfRegQ.hDrv y) ≠ r := by
      intro u _ r har
      rcases eq_zero_or_pos u with rfl | hu
      · rw [htr0]; exact_mod_cast (ha.trans_le har).ne
      · exact GlueCond.traceAt_ne_real_of_mem_goodHitSet hy hu (ha.trans_le har).ne'
    have h1 := Sec7.Lemma76E.alive_of_trace_off hg hw.continuousOn hw0 ht₂ hst ha hoff
    refine (Sec7.Lemma71B.alive_congr ?_).1 h1
    have := heq (CfRegQ.hDrv y) 1 (fun r => (one_mul _).symm)
    simpa only [one_mul] using this
  · -- negative points: through the reflected trace
    have hgr := LP.isGeneratingTrace_reflect hg
    have hoff : ∀ u ≤ s, ∀ r : ℝ, a ≤ r → LP.reflectC (LP.traceAt u (CfRegQ.hDrv y)) ≠ r := by
      intro u _ r har hre
      have hr0 : r ≠ 0 := (ha.trans_le har).ne'
      rcases eq_zero_or_pos u with rfl | hu
      · rw [htr0] at hre
        simp [LP.reflectC] at hre
        exact hr0 (by exact_mod_cast hre.symm)
      · have : LP.traceAt u (CfRegQ.hDrv y) = ((-r : ℝ) : ℂ) := by
          have h2 := congrArg LP.reflectC hre
          rw [LP.reflectC_reflectC] at h2
          rw [h2]
          simp [LP.reflectC]
        exact GlueCond.traceAt_ne_real_of_mem_goodHitSet hy hu (neg_ne_zero.2 hr0) this
    have h1 := Sec7.Lemma76E.alive_of_trace_off hgr (hw.neg).continuousOn (by simp [hw0]) ht₂ hst ha hoff
    refine (Sec7.Lemma71B.alive_congr ?_).1 h1
    have := heq (-CfRegQ.hDrv y) (-1) (fun r => by simp)
    simpa only [neg_one_mul] using this

end Alive

/-! ### Strictly ordered chart images -/

section Psi

variable {w : ℝ → ℝ} {s : ℝ}

theorem neg_one_div_lt_of_pos {A A' : ℝ} (hA : 0 < A) (h : A < A') : -1 / A < -1 / A' := by
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact one_div_lt_one_div_of_lt hA h

theorem neg_one_div_lt_of_neg {B B' : ℝ} (hB' : B' < 0) (h : B < B') : -1 / B < -1 / B' := by
  have hB : B < 0 := h.trans hB'
  rw [neg_div, neg_div, neg_lt_neg_iff, one_div, one_div]
  exact (inv_lt_inv_of_neg hB' hB).2 h

/-- **The chart images of left points are strictly ordered** when every positive point is alive. -/
theorem psiL_lt_psiL (hw : Continuous w) (hs : 0 ≤ s) (hal : ∀ y, 0 < y → Alive w y s)
    (hj : 0 < rightImg w 0 s - w s) {x x' : ℝ} (hxx : x < x') (hx' : x' ≤ 0) : psiL w s x < psiL w s x' := by
  have hx : x < 0 := hxx.trans_le hx'
  have hA : ∀ z, 0 ≤ z → 0 < rightImg w z s - w s := fun z hz =>
    lt_of_lt_of_le hj (sub_le_sub_right (rightImg_mono_index hw hs hz) _)
  have ha : 0 < -1 / x := div_pos_of_neg_of_neg (by norm_num) hx
  have hpx : psiL w s x = -1 / (rightImg w (-1 / x) s - w s) := by simp only [psiL, hx.ne, ↓reduceIte]
  rw [hpx]
  rcases hx'.lt_or_eq with hx'n | rfl
  · have hpx' : psiL w s x' = -1 / (rightImg w (-1 / x') s - w s) := by
      simp only [psiL, hx'n.ne, ↓reduceIte]
    rw [hpx']
    have ha' : -1 / x < -1 / x' := neg_one_div_lt_of_neg hx'n hxx
    have hlt : rightImg w (-1 / x) s < rightImg w (-1 / x') s := by
      have h1 := GlueImg.rightImg_lt_gImg_of_lt hw hs hal ha.le ha'
      rwa [← rightImg_eq_gImg hw hs (hal _ (ha.trans ha'))] at h1
    exact neg_one_div_lt_of_pos (hA _ ha.le) (by linarith)
  · have hp0 : psiL w s 0 = 0 := by simp [psiL]
    rw [hp0]
    exact div_neg_of_neg_of_pos (by norm_num) (hA _ ha.le)

/-- **The left junction lies strictly left of every left image** when every positive point is alive. -/
theorem junL_lt_psiL (hw : Continuous w) (hs : 0 ≤ s) (hal : ∀ y, 0 < y → Alive w y s)
    (hj : 0 < rightImg w 0 s - w s) {x : ℝ} (hx : x ≤ 0) : junL w s < psiL w s x := by
  rcases hx.lt_or_eq with hxn | rfl
  · have ha : 0 < -1 / x := div_pos_of_neg_of_neg (by norm_num) hxn
    have hpx : psiL w s x = -1 / (rightImg w (-1 / x) s - w s) := by simp only [psiL, hxn.ne, ↓reduceIte]
    rw [hpx, junL]
    have hlt : rightImg w 0 s < rightImg w (-1 / x) s := by
      have h1 := GlueImg.rightImg_lt_gImg_of_lt hw hs hal le_rfl ha
      rwa [← rightImg_eq_gImg hw hs (hal _ ha)] at h1
    exact neg_one_div_lt_of_pos hj (by linarith)
  · have hp0 : psiL w s 0 = 0 := by simp [psiL]
    rw [hp0, junL]
    exact div_neg_of_neg_of_pos (by norm_num) hj

/-- **The chart images of right points are strictly ordered** when every positive point is alive for the reflected
driver. -/
theorem psiR_lt_psiR (hw : Continuous w) (hs : 0 ≤ s) (hal : ∀ y, 0 < y → Alive (fun r => -w r) y s)
    (hj : -rightImg (fun r => -w r) 0 s - w s < 0) {x x' : ℝ} (hxx : x < x') (hx : 0 ≤ x) :
    psiR w s x < psiR w s x' := by
  have hw' : Continuous fun r => -w r := hw.neg
  have hx' : 0 < x' := hx.trans_lt hxx
  have hb' : 0 < 1 / x' := one_div_pos.2 hx'
  have hB : ∀ z, 0 ≤ z → -rightImg (fun r => -w r) z s - w s < 0 := fun z hz =>
    lt_of_le_of_lt (sub_le_sub_right (neg_le_neg (rightImg_mono_index hw' hs hz)) _) hj
  have hpx' : psiR w s x' = -1 / (-rightImg (fun r => -w r) (1 / x') s - w s) := by
    simp only [psiR, hx'.ne', ↓reduceIte]
  rw [hpx']
  rcases hx.lt_or_eq with hxp | rfl
  · have hpx : psiR w s x = -1 / (-rightImg (fun r => -w r) (1 / x) s - w s) := by
      simp only [psiR, hxp.ne', ↓reduceIte]
    rw [hpx]
    have hbb : 1 / x' < 1 / x := one_div_lt_one_div_of_lt hxp hxx
    have hlt : rightImg (fun r => -w r) (1 / x') s < rightImg (fun r => -w r) (1 / x) s := by
      have h1 := GlueImg.rightImg_lt_gImg_of_lt hw' hs hal hb'.le hbb
      rwa [← rightImg_eq_gImg hw' hs (hal _ (hb'.trans hbb))] at h1
    exact neg_one_div_lt_of_neg (hB _ hb'.le) (by linarith)
  · have hp0 : psiR w s 0 = 0 := by simp [psiR]
    rw [hp0]
    exact div_pos_of_neg_of_neg (by norm_num) (hB _ hb'.le)

/-- **The right junction lies strictly right of every right image** when every positive point is alive for the
reflected driver. -/
theorem psiR_lt_junR (hw : Continuous w) (hs : 0 ≤ s) (hal : ∀ y, 0 < y → Alive (fun r => -w r) y s)
    (hj : -rightImg (fun r => -w r) 0 s - w s < 0) {x : ℝ} (hx : 0 ≤ x) : psiR w s x < junR w s := by
  have hw' : Continuous fun r => -w r := hw.neg
  rcases hx.lt_or_eq with hxp | rfl
  · have hb : 0 < 1 / x := one_div_pos.2 hxp
    have hpx : psiR w s x = -1 / (-rightImg (fun r => -w r) (1 / x) s - w s) := by
      simp only [psiR, hxp.ne', ↓reduceIte]
    rw [hpx, junR]
    have hlt : rightImg (fun r => -w r) 0 s < rightImg (fun r => -w r) (1 / x) s := by
      have h1 := GlueImg.rightImg_lt_gImg_of_lt hw' hs hal le_rfl hb
      rwa [← rightImg_eq_gImg hw' hs (hal _ hb)] at h1
    exact neg_one_div_lt_of_neg hj (by linarith)
  · have hp0 : psiR w s 0 = 0 := by simp [psiR]
    rw [hp0, junR]
    exact div_pos_of_neg_of_neg (by norm_num) hj

end Psi

/-! ### Strictly ordered snoc words -/

section Snoc

theorem strictAnti_snoc {n : ℕ} {f : Fin n → ℝ} (hf : StrictAnti f) {x : ℝ} (hx : ∀ i, x < f i) :
    StrictAnti (Fin.snoc f x : Fin (n + 1) → ℝ) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      exact hf (Fin.castSucc_lt_castSucc_iff.1 hij)
    · exact absurd hij (not_lt.2 (Fin.castSucc_lt_last j').le)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx i'
    · exact absurd hij (lt_irrefl _)

theorem strictMono_snoc {n : ℕ} {f : Fin n → ℝ} (hf : StrictMono f) {x : ℝ} (hx : ∀ i, f i < x) :
    StrictMono (Fin.snoc f x : Fin (n + 1) → ℝ) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      exact hf (Fin.castSucc_lt_castSucc_iff.1 hij)
    · exact absurd hij (not_lt.2 (Fin.castSucc_lt_last j').le)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx i'
    · exact absurd hij (lt_irrefl _)

end Snoc

/-! ### The image start is strictly ordered; the root-stage representation -/

section ImgStrict

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The image start is strictly ordered** almost surely on the glued space, for a strictly ordered flow word: the
chart `Ψ` is strictly monotone on the real points the counterflow has not reached, and the counterflow trace avoids
`ℝ ∖ {0}`. -/
theorem ae_strict_imgStart (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hxLs : StrictAnti xL) (hxRs : StrictMono xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      StrictAnti (fun i => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W) i 0 p) ∧
      StrictMono (fun j => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W) j 0 p) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hcg := cfGlueAE_isGood49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [hcg] with p hp
    exact isGood49_of_mem hp.1 hp.2
  filter_upwards [hcg, ae_mem_glueGood hae] with p hp hpE
  have hy : p.2 ∈ GlueCond.goodHitSet := hp.2.1
  have hw := continuous_cfDrv0 s p.2
  have hal : ∀ a, 0 < a → Alive (cfDrv0 s p.2) a s := fun a ha =>
    (alive_cfDrv0_of_mem_goodHitSet hy s ha).1
  have hal' : ∀ a, 0 < a → Alive (fun r => -cfDrv0 s p.2 r) a s := fun a ha =>
    (alive_cfDrv0_of_mem_goodHitSet hy s ha).2
  obtain ⟨-, -, hjL, hjR, -⟩ := hEg p hpE
  have hVL0 : (fun i => imgVL xL s ζ W E i 0 p) = gXL xL s E p := funext fun i => imgVL_zero hF.2.1 hEg p i
  have hVR0 : (fun j => imgVR xR s ζ W E j 0 p) = gXR xR s E p := funext fun j => imgVR_zero hF.2.2.2 hEg p j
  rw [hVL0, hVR0, Word49.gXL_of_mem hpE, Word49.gXR_of_mem hpE]
  exact ⟨strictAnti_snoc (fun i i' hii => psiL_lt_psiL hw s.coe_nonneg hal hjL (hxLs hii) (hF.2.1 i))
      (fun i => junL_lt_psiL hw s.coe_nonneg hal hjL (hF.2.1 i)),
    strictMono_snoc (fun j j' hjj => psiR_lt_psiR hw s.coe_nonneg hal' hjR (hxRs hjj) (hF.2.2.2 j))
      (fun j => psiR_lt_junR hw s.coe_nonneg hal' hjR (hF.2.2.2 j))⟩

/-- **The stopped representation of Proposition 5.9's root stage on the glued space**, for a strictly ordered flow
word: `exists_isKilledStageRep_img` with its strictness hypothesis discharged (`ae_strict_imgStart`). The only named
input is the deterministic `KilledArcSwallowStatement`. -/
theorem exists_isKilledStageRep_img' (hsw : KilledArcSwallowStatement) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hxLs : StrictAnti xL) (hxRs : StrictMono xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (Bi : ℝ≥0 → (Ω × HistorySpace 0 0) × Ω₀ → ℝ),
      IsKilledStageRep κ ((glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)).prod P₀)
        (cfPast s Ω₀) univ (jwL cL6 κ ρL) (jwR cR6 κ ρR) (Fin.last nL) (Fin.last nR)
        (fun p => ((0 : ℝ), fun i => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) i 0 p.1,
          fun j => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) j 0 p.1))
        (fun t p => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) t p.1)
        (fun i t p => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) i t p.1)
        (fun j t p => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) j t p.1) Bi
        (fun p => (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) p.1 : ℝ≥0∞))
        (WholeField.prodFiltration (imgFilt (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W)) 𝓦) Bi :=
  exists_isKilledStageRep_img hsw hκ hκ4 hF h44 hC hcf hlaw k hk hs
    (ae_strict_imgStart hκ hκ4 hF h44 hxLs hxRs hC hcf hlaw k hk hs)

end ImgStrict

end InteractingSLE.Sec5.CrossCond.StagedRep
