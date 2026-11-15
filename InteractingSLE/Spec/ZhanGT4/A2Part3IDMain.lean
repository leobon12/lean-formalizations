/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3IDCode
import InteractingSLE.Spec.ZhanGT4.A2Part3Split
import InteractingSLE.WangWu.ReverseContactImgCont
import InteractingSLE.Spec.ZhanGT4.CrosscutRestart

/-!
# A.2 part 3, (I1): the random-word transfer and the pathwise dichotomy

Packet PROVE-ZHAN-A2P3-ID. Source: Astra, *Follow-up proofs*, §A.2 L572–L594
(`source/external/AstraIG1/ig1_followup_proofs.txt`; R38, R53).

* **`ae_exists_code_of_randomWord`** (pathwise uniqueness, source step 1): for a local evolution of an initially
  measurable random word (`Restart.StoppedK2.IsRandomWordEvolutionUpTo`) on an arbitrary probability space, and a
  Borel set `S` of solution codes containing, for every start in a Borel set `G` of separated starts, the canonical
  solution of Wiener-almost every driving path: almost surely on the live event (with the word in `G`) the local
  path agrees before its stop with a canonical solution code of the word in `S`, whose lifetime is at least the stop.
  The word is `𝓖₀`-measurable and the Brownian motion is a `𝓖`-Brownian motion, so the pair (word, Brownian path)
  has the law `(law of the word) ⊗ Wiener` on the live event (`WangWu.ImgDrv.joint_law_restart` at time `0`);
* **`dichotomy_of_code`** (source L586–L594): if that canonical code has `IdProp` (`A2Part3IDCode`), the hulls of the
  local path before its stop accumulate at the target, or are bounded with closure off the real half-line left of the
  nearest mark. Before the separation time the nearest mark is alive (`isBounded_and_notMem_of_mark`); from the
  separation time on, the infinite new horizon gives the accumulation (`mem_closure_iUnion_of_newHorizon_top`,
  reflected).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Bornology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2P3ID

open QuantumZipper (H fwdHull)
open Sec2.Assembly Sec7.RandRestart Zhan.Retarget Theorem14.BR3Ref

/-! ### The random-word transfer -/

section Transfer

variable {a : ℝ} {nL nR : ℕ} {Ω : Type*} {𝓔 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **A random-word local evolution agrees with a canonical solution code** in a code set of full canonical law. -/
theorem ae_exists_code_of_randomWord
    (h : Restart.StoppedK2.IsRandomWordEvolutionUpTo a P 𝓔 F ΘL ΘR ρL ρR 𝓖 W VL VR B ζ)
    {G : Set ((Fin nL → ℝ) × (Fin nR → ℝ))} (hGm : MeasurableSet G) (hGsep : ∀ s ∈ G, ∀ i j, s.1 i < s.2 j)
    (hΘG : ∀ᵐ ω ∂P, ω ∈ F → (ΘL ω, ΘR ω) ∈ G) {S : Set (XCode nL nR)} (hS : MeasurableSet S)
    (hlaw : ∀ s ∈ G, ∀ᵐ f ∂Sec2.Restart.wienerPath, (s, enc f) ∈ lawSetS a ρL ρR S) :
    ∀ᵐ ω ∂P, ω ∈ F → ∃ x ∈ CRel a (ΘL ω) (ΘR ω) ρL ρR, x ∈ S ∧ ζ ω ≤ cζ x ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
        W t ω = cw x t ∧ (∀ i, VL i t ω = cvL x i t) ∧ ∀ j, VR j t ω = cvR x j t := by
  obtain ⟨h0, hF, hΘL, hΘR, hB, -, -, -, hpath⟩ := h
  obtain ⟨Bv, -, hBvc, hBv0, hBvF, hBvae⟩ := ZhanGT4.exists_continuous_version_zero hB
  set st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω => (ΘL ω, ΘR ω) with hstdef
  have hle : 𝓔 ≤ usualAugmentation 𝓖 P 0 := h0.trans (Ito.le_usualAugmentation 𝓖 P 0)
  have hst : Measurable[usualAugmentation 𝓖 P 0] st := (hΘL.prodMk hΘR).mono hle le_rfl
  have hFm : MeasurableSet[usualAugmentation 𝓖 P 0] F := hle _ hF
  set E : Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℝ≥0 → ℝ)) :=
    (Prod.fst ⁻¹' G)ᶜ ∪ restartSetS a ρL ρR S with hEdef
  have hEm : MeasurableSet E := (hGm.preimage measurable_fst).compl.union (measurableSet_restartSetS hS)
  have hjl := WangWu.ImgDrv.joint_law_restart hBvF hBvc 0 hst hFm hEm.compl
  have hzero : ∀ s, Sec2.Restart.wienerPath (Prod.mk s ⁻¹' Eᶜ) = 0 := by
    intro s
    by_cases hs : s ∈ G
    · have hl := hlaw s hs
      rw [ae_iff] at hl
      refine le_antisymm (le_of_eq_of_le ?_ hl.le) bot_le
      congr 1
      ext f
      simp [hEdef, hs, restartSetS]
    · have e : Prod.mk s ⁻¹' Eᶜ = ∅ := by
        ext f
        simp [hEdef, hs]
      rw [e, measure_empty]
  simp only [hzero, lintegral_zero] at hjl
  have hae : ∀ᵐ ω ∂P, ω ∈ F → (st ω, QuantumZipper.StrongMarkov.smPath Bv (fun _ => 0) ω) ∈ E := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hjl
    simp only [mem_ofPred_eq, Classical.not_imp] at hω
    exact ⟨hω.1, hω.2⟩
  filter_upwards [hae, hpath, hΘG, hBvae] with ω hE hp hG hb hωF
  have hg : QuantumZipper.StrongMarkov.smPath Bv (fun _ => 0) ω = fun t => Bv t ω := by
    funext t
    simp [QuantumZipper.StrongMarkov.smPath, QuantumZipper.StrongMarkov.smShift, hBv0]
  have hmem := (hE hωF).resolve_left (by simpa using hG hωF)
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxeq⟩ := hmem
  simp only [Prod.mk.injEq] at hxeq
  have hxC : x ∈ CRel a (ΘL ω) (ΘR ω) ρL ρR := mem_cRelF_iff.1 ⟨hxF, hxeq.1⟩
  have hxp : IsIntegratedSLEPath a (ΘL ω) (ΘR ω) ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  have hcb : cb x = fun s => Bv s ω := by
    funext t
    show dec x.1 t = Bv t ω
    rw [hxeq.2, hg]
    exact dec_enc (hBvc ω).continuousWithinAt
  rw [hcb] at hxp
  have hp' : Sec2.IsSLEPathUpTo a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun s => Bv s ω) (ζ ω) := (hp hωF).congr_b fun t _ => hb t
  obtain ⟨hle', hag⟩ := Sec7.Band.le_lifetime_of_upTo (hGsep _ (hG hωF)) hp' hxp
  exact ⟨x, hxC, hxS, hle', hag⟩

end Transfer

/-! ### The pathwise dichotomy -/

section Dichotomy

open ZhanGT4.A2X.P3 (imgHulls)

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The image hulls depend on the driver only before the stop. -/
theorem imgHulls_congr {W' w : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → W' t = w t) :
    imgHulls W' ζ' = ⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ'), fwdHull (Strip.extPath w) t := by
  unfold imgHulls
  refine iUnion₂_congr fun t ht => ?_
  obtain ⟨t₂, htt₂, ht₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  refine fwdHull_eq_of_eqOn t.coe_nonneg (by exact_mod_cast htt₂) fun r hr => ?_
  simp only [Strip.extPath]
  exact hag _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht₂)

/-- The target change data of the reflected path `(−w, −v_k)` at its separation time. -/
theorem pullData_reflect (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (k : Fin nL) (hxk : xL k < 0) :
    PullData (fun t => -w t) (fun t => -vL k t) (-vL k 0) (sepTime (fun t => -w t) (fun t => -vL k t) ζ) := by
  have hfp := hp.isForcePath
  refine ⟨by rw [hfp.vL_zero]; linarith, by simp [hfp.w_zero],
    sepUpTo_reflect hfp.continuousOn_w (hfp.continuousOn_vL k), fun t ht => ?_⟩
  have htζ : (t : ℝ≥0∞) < ζ := ht.trans_le (sepTime_le _ _ _)
  have he := hfp.vL_eq htζ k
  have hint : (∫ s in (0 : ℝ)..t, 2 / (-vL k s.toNNReal - -w s.toNNReal)) =
      -∫ s in (0 : ℝ)..t, 2 / (vL k s.toNNReal - w s.toNNReal) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext s
    rw [show -vL k s.toNNReal - -w s.toNNReal = -(vL k s.toNNReal - w s.toNNReal) by ring, div_neg]
  show -vL k t = -vL k 0 + ∫ s in (0 : ℝ)..t, 2 / (-vL k s.toNNReal - -w s.toNNReal)
  rw [hint, he, hfp.vL_zero]
  ring

theorem continuousOn_comp_toNNReal {f : ℝ≥0 → ℝ} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < ζ}) {S : ℝ≥0}
    (hS : (S : ℝ≥0∞) < ζ) : ContinuousOn (fun s : ℝ => f s.toNNReal) (Icc 0 S) :=
  hf.comp continuous_real_toNNReal.continuousOn fun _ hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) hS

/-- **The pathwise dichotomy of (I1).** Let a canonical integrated path, whose target `k` and nearest mark `i₀` start
left of `0`, have `IdProp`, and let `W'` agree with its driver before `ζ'`. Then the hulls of `W'` before `ζ'`
accumulate at `x_k`, or they are bounded and their closure misses `(−∞, x_{i₀}]`. -/
theorem dichotomy_of_code (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (i₀ k : Fin nL)
    (hxk : xL k < 0) (hx0 : xL i₀ < 0) (hP : IdProp i₀ k w vL ζ) {W' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞}
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → W' t = w t) :
    (xL k : ℂ) ∈ closure (imgHulls W' ζ') ∨
      (IsBounded (imgHulls W' ζ') ∧ ∀ u : ℝ, u ≤ xL i₀ → (u : ℂ) ∉ closure (imgHulls W' ζ')) := by
  have hfp := hp.isForcePath
  rw [imgHulls_congr hag]
  set sep := sepTime (fun t => -w t) (fun t => -vL k t) ζ with hsep
  rcases le_or_gt sep ζ' with hsζ | hζs
  · left
    have hT := newHorizon_top_of_idProp hfp.continuousOn_w (hfp.continuousOn_vL k) hP
    have hacc := mem_closure_iUnion_of_newHorizon_top (pullData_reflect hp k hxk) hT
    rw [hfp.vL_zero] at hacc
    exact closure_mono (iUnion₂_mono' fun t ht => ⟨t, lt_of_lt_of_le ht hsζ, subset_rfl⟩)
      (mem_closure_of_reflect hacc)
  · right
    have hζ'top : ζ' ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hζs le_top)
    set T := ζ'.toNNReal with hTdef
    have hT : (T : ℝ≥0∞) = ζ' := ENNReal.coe_toNNReal hζ'top
    obtain ⟨q, hTq, hqs⟩ := exists_nnrat_btwn (show (T : ℝ≥0∞) < sep by rw [hT]; exact hζs)
    have hqζ : (((q : ℝ≥0) : ℝ≥0∞)) < ζ := hqs.trans_le (sepTime_le _ _ _)
    have hTζ : (T : ℝ≥0∞) < ζ := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hTq) hqζ.le
    have h := isBounded_and_notMem_of_mark (w := w) (v := vL i₀) (T := T) (T₂ := q) hTq
      (continuousOn_comp_toNNReal hfp.continuousOn_w hqζ)
      (continuousOn_comp_toNNReal (hfp.continuousOn_vL i₀) hTζ) hfp.w_zero
      (by rw [hfp.vL_zero]; exact hx0)
      (fun t ht => by
        rw [hfp.vL_zero]
        exact hfp.vL_eq (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hTζ) i₀)
      (fun t ht => gap_of_idProp hfp.continuousOn_w (hfp.continuousOn_vL k) (hfp.continuousOn_vL i₀) hP hqs
        (ht.trans hTq.le))
    rw [hT] at h
    exact ⟨h.1, fun u hu => h.2 u (by rw [hfp.vL_zero]; exact hu)⟩

end Dichotomy

/-! ### The canonical law of the code event for the two image words -/

section Law

open Sec4 in
/-- **(G3) The code event has full canonical law** from every strictly ordered image word with `x₀ < 0`. -/
theorem law_idSet_G3 {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {xL : Fin 4 → ℝ} (h0 : xL 0 < 0) (hsa : StrictAnti xL)
    (xR : Fin 0 → ℝ) :
    ∀ᵐ f ∂Sec2.Restart.wienerPath, ((xL, xR), enc f) ∈ lawSetS κ (ZhanGT4.A2X.largeG3ImgRhoL κ) ![] (idSet 0 2) := by
  have hκ0 : 0 < κ := by linarith
  have hxL0 : ∀ i, xL i ≤ 0 := fun i => (hsa.antitone (Fin.zero_le i)).trans h0.le
  have hF : IsOrderedForceWord xL xR := ⟨hsa.antitone, hxL0, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ0 hF (ρL := ZhanGT4.A2X.largeG3ImgRhoL κ) (ρR := ![])
  refine ae_mem_lawSetS_of_ae hκ0 (fun i j => j.elim0) hE (measurableSet_idSet 0 2)
    (Ψ := fun w vL _ τ => IdProp 0 2 w vL τ) (fun x _ _ => Iff.rfl)
    (fun w w' vL vL' vR vR' τ h hw => idProp_congr (fun t ht => ⟨(h t ht).1, (h t ht).2.1⟩) hw) ?_
  have hD : LP.IsDistinctForceWord (-xR) (-xL) :=
    ⟨⟨fun i => i.elim0, fun i => i.elim0, hsa.antitone.neg, fun i => by simp [hxL0 i]⟩, fun i => i.elim0,
      hsa.neg⟩
  have hres := ae_gap_and_newHorizon_top (j := 2) (m := 1) hκ0 hD (by norm_num) (by simpa using h0)
    (fun i hi => by
      fin_cases i <;> simp at hi <;>
        simp [Finset.sum_filter, Fin.sum_univ_four, ZhanGT4.A2X.largeG3ImgRhoL] <;> linarith)
    (fun j _ => by
      fin_cases j <;>
        simp [LP.retargetρL, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_four,
          ZhanGT4.A2X.largeG3ImgRhoL, Fin.append, Fin.addCases, Fin.subNat, Fin.cast] <;> linarith)
    (fun j _ => by
      fin_cases j <;>
        simp [LP.retargetρR, Finset.sum_filter, Fin.sum_univ_two, ZhanGT4.A2X.largeG3ImgRhoL] <;> linarith)
    hE.reflect
  filter_upwards [hres, hE.ae_isIntegratedSLEPath] with ω hω hp
  have hfp := hp.isForcePath
  have hk : (LP.retargetIdx 2 1 : Fin (2 + 1 + 1)) = (2 : Fin 4) := rfl
  refine idProp_of_gap hfp.continuousOn_w (hfp.continuousOn_vL 2) (hfp.continuousOn_vL 0)
    (by rw [hfp.vL_zero]; exact (hsa (by decide : (0 : Fin 4) < 2)).trans h0) (fun t ht => ?_) ?_
  · have := hω.1 t (by simpa [hk] using ht)
    simpa using this
  · have := hω.2
    simpa [Sec5.Aux22Strip.retargetHorizon, LP.retargetPos, hk, hfp.vL_zero] using this

open Sec4 in
/-- **(Eight) The code event has full canonical law** from every strictly ordered image word with `x₀ < 0`. -/
theorem law_idSet_eight {κ : ℝ} (hκ8 : 8 ≤ κ) {xL : Fin 3 → ℝ} (h0 : xL 0 < 0) (hsa : StrictAnti xL)
    (xR : Fin 0 → ℝ) :
    ∀ᵐ f ∂Sec2.Restart.wienerPath, ((xL, xR), enc f) ∈
      lawSetS κ (ZhanGT4.A2X.largeEightImgRhoL κ) ![] (idSet 0 1) := by
  have hκ0 : 0 < κ := by linarith
  have hxL0 : ∀ i, xL i ≤ 0 := fun i => (hsa.antitone (Fin.zero_le i)).trans h0.le
  have hF : IsOrderedForceWord xL xR := ⟨hsa.antitone, hxL0, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ0 hF (ρL := ZhanGT4.A2X.largeEightImgRhoL κ) (ρR := ![])
  refine ae_mem_lawSetS_of_ae hκ0 (fun i j => j.elim0) hE (measurableSet_idSet 0 1)
    (Ψ := fun w vL _ τ => IdProp 0 1 w vL τ) (fun x _ _ => Iff.rfl)
    (fun w w' vL vL' vR vR' τ h hw => idProp_congr (fun t ht => ⟨(h t ht).1, (h t ht).2.1⟩) hw) ?_
  have hD : LP.IsDistinctForceWord (-xR) (-xL) :=
    ⟨⟨fun i => i.elim0, fun i => i.elim0, hsa.antitone.neg, fun i => by simp [hxL0 i]⟩, fun i => i.elim0,
      hsa.neg⟩
  have hres := ae_gap_and_newHorizon_top (j := 1) (m := 1) hκ0 hD le_rfl (by simpa using h0)
    (fun i hi => by
      fin_cases i
      · simp [Finset.sum_filter, ZhanGT4.A2X.largeEightImgRhoL]; linarith
      · simp at hi
      · simp at hi)
    (fun j _ => by
      fin_cases j <;>
        simp [LP.retargetρL, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three,
          ZhanGT4.A2X.largeEightImgRhoL, Fin.append, Fin.addCases, Fin.subNat, Fin.cast] <;> linarith)
    (fun j _ => by
      fin_cases j
      simp [LP.retargetρR, ZhanGT4.A2X.largeEightImgRhoL]
      linarith)
    hE.reflect
  filter_upwards [hres, hE.ae_isIntegratedSLEPath] with ω hω hp
  have hfp := hp.isForcePath
  have hk : (LP.retargetIdx 1 1 : Fin (1 + 1 + 1)) = (1 : Fin 3) := rfl
  refine idProp_of_gap hfp.continuousOn_w (hfp.continuousOn_vL 1) (hfp.continuousOn_vL 0)
    (by rw [hfp.vL_zero]; exact (hsa (by decide : (0 : Fin 3) < 1)).trans h0) (fun t ht => ?_) ?_
  · have := hω.1 t (by simpa [hk] using ht)
    simpa using this
  · have := hω.2
    simpa [Sec5.Aux22Strip.retargetHorizon, LP.retargetPos, hk, hfp.vL_zero] using this

end Law

/-! ### (I1) for strictly ordered image words -/

section Statements

open ZhanGT4.A2X ZhanGT4.A2X.P3

universe u

/-- Strictly decreasing words with the nearest mark left of `0` form a Borel set. -/
theorem measurableSet_strictWord (n : ℕ) (i₀ : Fin n) :
    MeasurableSet {s : (Fin n → ℝ) × (Fin 0 → ℝ) | s.1 i₀ < 0 ∧ StrictAnti s.1} := by
  have e : {s : (Fin n → ℝ) × (Fin 0 → ℝ) | s.1 i₀ < 0 ∧ StrictAnti s.1} =
      {s | s.1 i₀ < 0} ∩ ⋂ i : Fin n, ⋂ j : Fin n, {s | i < j → s.1 j < s.1 i} := by
    ext s
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, StrictAnti]
  rw [e]
  refine (measurableSet_lt ((measurable_pi_apply i₀).comp measurable_fst) measurable_const).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  by_cases hij : i < j
  · simpa [hij] using measurableSet_lt ((measurable_pi_apply j).comp measurable_fst)
      ((measurable_pi_apply i).comp measurable_fst)
  · simp [hij]

/-- **(I1), (G3), strictly ordered image words**: `ImageDichotomyG3Statement` with the image word almost surely
strictly decreasing on the live event (as it is in the application: the marks `x`, `y⁺`, the small tip and `y⁻`
are distinct at positive times). -/
def ImageDichotomyG3StrictStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 →
    ∀ {Ω : Type u} (𝓔 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Set Ω) (ΘL : Ω → Fin 4 → ℝ) (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ)
      (VL' : Fin 4 → ℝ≥0 → Ω → ℝ) (VR' : Fin 0 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      Restart.StoppedK2.IsRandomWordEvolutionUpTo κ P 𝓔 F ΘL (fun _ => ![]) (largeG3ImgRhoL κ) ![] 𝓖 W' VL' VR'
          B' ζ' → (∀ᵐ ω ∂P, ω ∈ F → ΘL ω 0 < 0 ∧ StrictAnti (ΘL ω)) →
        ∀ᵐ ω ∂P, ω ∈ F → ((ΘL ω 2 : ℂ) ∈ closure (imgHulls (W' · ω) (ζ' ω)) ∨
          (IsBounded (imgHulls (W' · ω) (ζ' ω)) ∧
            ∀ u : ℝ, u ≤ ΘL ω 0 → (u : ℂ) ∉ closure (imgHulls (W' · ω) (ζ' ω))))

/-- **(I1), (Eight), strictly ordered image words.** -/
def ImageDichotomyEightStrictStatement (κ : ℝ) : Prop :=
  8 ≤ κ →
    ∀ {Ω : Type u} (𝓔 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Set Ω) (ΘL : Ω → Fin 3 → ℝ) (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ)
      (VL' : Fin 3 → ℝ≥0 → Ω → ℝ) (VR' : Fin 0 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      Restart.StoppedK2.IsRandomWordEvolutionUpTo κ P 𝓔 F ΘL (fun _ => ![]) (largeEightImgRhoL κ) ![] 𝓖 W' VL' VR'
          B' ζ' → (∀ᵐ ω ∂P, ω ∈ F → ΘL ω 0 < 0 ∧ StrictAnti (ΘL ω)) →
        ∀ᵐ ω ∂P, ω ∈ F → ((ΘL ω 1 : ℂ) ∈ closure (imgHulls (W' · ω) (ζ' ω)) ∨
          (IsBounded (imgHulls (W' · ω) (ζ' ω)) ∧
            ∀ u : ℝ, u ≤ ΘL ω 0 → (u : ℂ) ∉ closure (imgHulls (W' · ω) (ζ' ω))))

/-- **(I1), (G3), for strictly ordered image words, PROVED.** -/
theorem imageDichotomyG3StrictStatement (κ : ℝ) : ImageDichotomyG3StrictStatement.{u} κ := by
  intro hκ4 hκ8 Ω 𝓔 mΩ P hP F ΘL 𝓖 W' VL' VR' B' ζ' hE hstr
  have htr := ae_exists_code_of_randomWord hE (measurableSet_strictWord 4 0) (fun _ _ _ j => j.elim0) hstr
    (measurableSet_idSet 0 2) fun s hs => law_idSet_G3 hκ4 hκ8 hs.1 hs.2 s.2
  filter_upwards [htr, hstr] with ω hω hs hωF
  obtain ⟨x, hxC, hxS, -, hag⟩ := hω hωF
  exact dichotomy_of_code hxC.1.2.2 0 2 (((hs hωF).2 (by decide : (0 : Fin 4) < 2)).trans (hs hωF).1)
    (hs hωF).1 hxS fun t ht => (hag t ht).1

/-- **(I1), (Eight), for strictly ordered image words, PROVED.** -/
theorem imageDichotomyEightStrictStatement (κ : ℝ) : ImageDichotomyEightStrictStatement.{u} κ := by
  intro hκ8 Ω 𝓔 mΩ P hP F ΘL 𝓖 W' VL' VR' B' ζ' hE hstr
  have htr := ae_exists_code_of_randomWord hE (measurableSet_strictWord 3 0) (fun _ _ _ j => j.elim0) hstr
    (measurableSet_idSet 0 1) fun s hs => law_idSet_eight hκ8 hs.1 hs.2 s.2
  filter_upwards [htr, hstr] with ω hω hs hωF
  obtain ⟨x, hxC, hxS, -, hag⟩ := hω hωF
  exact dichotomy_of_code hxC.1.2.2 0 1 (((hs hωF).2 (by decide : (0 : Fin 3) < 1)).trans (hs hωF).1)
    (hs hωF).1 hxS fun t ht => (hag t ht).1

end Statements

end InteractingSLE.ZhanGT4.A2P3ID
