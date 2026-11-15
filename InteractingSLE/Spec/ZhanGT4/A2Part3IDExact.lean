/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3IDCoinc

/-!
# A.2 part 3, (I1) PROVED: `ImageDichotomyG3Statement` and `ImageDichotomyEightStatement`

Packet PROVE-ZHAN-A2P3-ID. Source: Astra, *Follow-up proofs*, §A.2 L572–L594
(`source/external/AstraIG1/ig1_followup_proofs.txt`; R38, R53).

The exact statements of A2P3 (`A2Part3Split`), for every image word whose nearest mark is left of the source; its
marks may coincide. On the live event with a positive stop the image word is decreasing (the local path's marks are
ordered at time `0`); every decreasing word with negative nearest mark has the code event of full canonical law
(`hasIdPropEvolution_G3_all`, `hasIdPropEvolution_eight_all`: strictly decreasing words directly, the others through
their merged word, `A2Part3IDCoinc`); `ae_exists_code_of_randomWord'` (the transfer of `A2Part3IDMain` on a `𝓖₀`-event
inside the live event) and `dichotomy_of_code` conclude. With a zero stop the hulls are empty.

* **`imageDichotomyG3Statement`** `: ImageDichotomyG3Statement κ` for every `κ`;
* **`imageDichotomyEightStatement`** `: ImageDichotomyEightStatement κ` for every `κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Bornology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2P3ID

open QuantumZipper (H fwdHull)
open Sec2.Assembly Sec7.RandRestart Zhan.Retarget Theorem14.BR3Ref

/-! ### The transfer on an event of `𝓖₀` inside the live event -/

section Transfer

variable {a : ℝ} {nL nR : ℕ} {Ω : Type*} {𝓔 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **`ae_exists_code_of_randomWord` on a `𝓖₀`-measurable part `A` of the live event.** -/
theorem ae_exists_code_of_randomWord'
    (h : Restart.StoppedK2.IsRandomWordEvolutionUpTo a P 𝓔 F ΘL ΘR ρL ρR 𝓖 W VL VR B ζ) {A : Set Ω}
    (hA : MeasurableSet[𝓖 0] A) (hAF : A ⊆ F)
    {G : Set ((Fin nL → ℝ) × (Fin nR → ℝ))} (hGm : MeasurableSet G) (hGsep : ∀ s ∈ G, ∀ i j, s.1 i < s.2 j)
    (hΘG : ∀ᵐ ω ∂P, ω ∈ A → (ΘL ω, ΘR ω) ∈ G) {S : Set (XCode nL nR)} (hS : MeasurableSet S)
    (hlaw : ∀ s ∈ G, ∀ᵐ f ∂Sec2.Restart.wienerPath, (s, enc f) ∈ lawSetS a ρL ρR S) :
    ∀ᵐ ω ∂P, ω ∈ A → ∃ x ∈ CRel a (ΘL ω) (ΘR ω) ρL ρR, x ∈ S ∧ ζ ω ≤ cζ x ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
        W t ω = cw x t ∧ (∀ i, VL i t ω = cvL x i t) ∧ ∀ j, VR j t ω = cvR x j t := by
  obtain ⟨h0, -, hΘL, hΘR, hB, -, -, -, hpath⟩ := h
  obtain ⟨Bv, -, hBvc, hBv0, hBvF, hBvae⟩ := ZhanGT4.exists_continuous_version_zero hB
  set st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω => (ΘL ω, ΘR ω) with hstdef
  have hle : 𝓔 ≤ usualAugmentation 𝓖 P 0 := h0.trans (Ito.le_usualAugmentation 𝓖 P 0)
  have hst : Measurable[usualAugmentation 𝓖 P 0] st := (hΘL.prodMk hΘR).mono hle le_rfl
  have hAm : MeasurableSet[usualAugmentation 𝓖 P 0] A := Ito.le_usualAugmentation 𝓖 P 0 _ hA
  set E : Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℝ≥0 → ℝ)) :=
    (Prod.fst ⁻¹' G)ᶜ ∪ restartSetS a ρL ρR S with hEdef
  have hEm : MeasurableSet E := (hGm.preimage measurable_fst).compl.union (measurableSet_restartSetS hS)
  have hjl := WangWu.ImgDrv.joint_law_restart hBvF hBvc 0 hst hAm hEm.compl
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
  have hae : ∀ᵐ ω ∂P, ω ∈ A → (st ω, QuantumZipper.StrongMarkov.smPath Bv (fun _ => 0) ω) ∈ E := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hjl
    simp only [mem_ofPred_eq, Classical.not_imp] at hω
    exact ⟨hω.1, hω.2⟩
  filter_upwards [hae, hpath, hΘG, hBvae] with ω hE hp hG hb hωA
  have hωF := hAF hωA
  have hg : QuantumZipper.StrongMarkov.smPath Bv (fun _ => 0) ω = fun t => Bv t ω := by
    funext t
    simp [QuantumZipper.StrongMarkov.smPath, QuantumZipper.StrongMarkov.smShift, hBv0]
  have hmem := (hE hωA).resolve_left (by simpa using hG hωA)
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
  obtain ⟨hle', hag⟩ := Sec7.Band.le_lifetime_of_upTo (hGsep _ (hG hωA)) hp' hxp
  exact ⟨x, hxC, hxS, hle', hag⟩

end Transfer

/-! ### Every decreasing image word -/

section All

open ZhanGT4.A2X

/-- **(G3) Every decreasing image word with negative nearest mark has an `IdProp` evolution.** -/
theorem hasIdPropEvolution_G3_all {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {xL : Fin 4 → ℝ} (xR : Fin 0 → ℝ)
    (h0 : xL 0 < 0) (hanti : Antitone xL) : HasIdPropEvolution κ xL (largeG3ImgRhoL κ) xR 0 2 := by
  have hκ0 : 0 < κ := by linarith
  have h01 : xL 1 ≤ xL 0 := hanti (by decide)
  have h12 : xL 2 ≤ xL 1 := hanti (by decide)
  have h23 : xL 3 ≤ xL 2 := hanti (by decide)
  rcases h01.lt_or_eq with l01 | e01 <;> rcases h12.lt_or_eq with l12 | e12 <;>
    rcases h23.lt_or_eq with l23 | e23
  · have hsa : StrictAnti xL := Fin.strictAnti_iff_succ_lt.2 fun i => by
      fin_cases i
      · exact l01
      · exact l12
      · exact l23
    exact hasIdPropEvolution_of_word (j := 2) (m := 1) hκ0 xR hsa h0 (by norm_num)
      (fun i hi => by
        fin_cases i <;> simp at hi <;>
          simp [Finset.sum_filter, Fin.sum_univ_four, largeG3ImgRhoL] <;> linarith)
      (fun j _ => by
        fin_cases j <;>
          simp [LP.retargetρL, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_four,
            largeG3ImgRhoL, Fin.append, Fin.addCases, Fin.subNat, Fin.cast] <;> linarith)
      (fun j _ => by
        fin_cases j <;>
          simp [LP.retargetρR, Finset.sum_filter, Fin.sum_univ_two, largeG3ImgRhoL] <;> linarith)
  · exact hasIdPropEvolution_G3_c23 hκ4 hκ8 xR h0 l01 l12 e23
  · exact hasIdPropEvolution_G3_c12 hκ4 hκ8 xR h0 l01 e12 l23
  · exact hasIdPropEvolution_G3_c12c23 hκ4 hκ8 xR h0 l01 e12 e23
  · exact hasIdPropEvolution_G3_c01 hκ4 hκ8 xR h0 e01 l12 l23
  · exact hasIdPropEvolution_G3_c01c23 hκ4 hκ8 xR h0 e01 l12 e23
  · exact hasIdPropEvolution_G3_c01c12 hκ4 hκ8 xR h0 e01 e12 l23
  · exact hasIdPropEvolution_G3_call hκ4 hκ8 xR h0 e01 e12 e23

/-- **(Eight) Every decreasing image word with negative nearest mark has an `IdProp` evolution.** -/
theorem hasIdPropEvolution_eight_all {κ : ℝ} (hκ8 : 8 ≤ κ) {xL : Fin 3 → ℝ} (xR : Fin 0 → ℝ) (h0 : xL 0 < 0)
    (hanti : Antitone xL) : HasIdPropEvolution κ xL (largeEightImgRhoL κ) xR 0 1 := by
  have hκ0 : 0 < κ := by linarith
  have h01 : xL 1 ≤ xL 0 := hanti (by decide)
  have h12 : xL 2 ≤ xL 1 := hanti (by decide)
  rcases h01.lt_or_eq with l01 | e01 <;> rcases h12.lt_or_eq with l12 | e12
  · have hsa : StrictAnti xL := Fin.strictAnti_iff_succ_lt.2 fun i => by
      fin_cases i
      · exact l01
      · exact l12
    exact hasIdPropEvolution_of_word (j := 1) (m := 1) hκ0 xR hsa h0 le_rfl
      (fun i hi => by
        fin_cases i
        · simp [Finset.sum_filter, largeEightImgRhoL]; linarith
        · simp at hi
        · simp at hi)
      (fun j _ => by
        fin_cases j <;>
          simp [LP.retargetρL, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three,
            largeEightImgRhoL, Fin.append, Fin.addCases, Fin.subNat, Fin.cast] <;> linarith)
      (fun j _ => by
        fin_cases j
        simp [LP.retargetρR, largeEightImgRhoL]
        linarith)
  · exact hasIdPropEvolution_Eight_c12 hκ8 xR h0 l01 e12
  · exact hasIdPropEvolution_Eight_c01 hκ8 xR h0 e01 l12
  · exact hasIdPropEvolution_Eight_call hκ8 xR h0 e01 e12

end All

/-! ### The statements -/

section Statements

open ZhanGT4.A2X ZhanGT4.A2X.P3

/-- Decreasing words with the nearest mark left of `0` form a Borel set. -/
theorem measurableSet_antiWord (n : ℕ) (i₀ : Fin n) :
    MeasurableSet {s : (Fin n → ℝ) × (Fin 0 → ℝ) | s.1 i₀ < 0 ∧ Antitone s.1} := by
  have e : {s : (Fin n → ℝ) × (Fin 0 → ℝ) | s.1 i₀ < 0 ∧ Antitone s.1} =
      {s | s.1 i₀ < 0} ∩ ⋂ i : Fin n, ⋂ j : Fin n, {s | i ≤ j → s.1 j ≤ s.1 i} := by
    ext s
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, Antitone]
  rw [e]
  refine (measurableSet_lt ((measurable_pi_apply i₀).comp measurable_fst) measurable_const).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  by_cases hij : i ≤ j
  · simpa [hij] using measurableSet_le ((measurable_pi_apply j).comp measurable_fst)
      ((measurable_pi_apply i).comp measurable_fst)
  · simp [hij]

/-- The hulls before a zero stop are empty. -/
theorem imgHulls_of_eq_zero {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hζ : ζ = 0) : imgHulls w ζ = ∅ := by
  rw [hζ]
  simp [imgHulls]

/-- **(I1) for a random-word local evolution of a word of `n` left marks, from the full canonical law of the code
event at every decreasing word with negative nearest mark.** -/
theorem dichotomy_of_law {κ : ℝ} {n : ℕ} {ρL : Fin n → ℝ} (i₀ k : Fin n) (hki : i₀ ≤ k)
    (hlaw : ∀ xL : Fin n → ℝ, ∀ xR : Fin 0 → ℝ, xL i₀ < 0 → Antitone xL →
      ∀ᵐ f ∂Sec2.Restart.wienerPath, ((xL, xR), enc f) ∈ lawSetS κ ρL ![] (idSet i₀ k))
    {Ω : Type*} (𝓔 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set Ω) (ΘL : Ω → Fin n → ℝ) (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ)
    (VL' : Fin n → ℝ≥0 → Ω → ℝ) (VR' : Fin 0 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (hE : Restart.StoppedK2.IsRandomWordEvolutionUpTo κ P 𝓔 F ΘL (fun _ => ![]) ρL ![] 𝓖 W' VL' VR' B' ζ')
    (hneg : ∀ᵐ ω ∂P, ω ∈ F → ΘL ω i₀ < 0) :
    ∀ᵐ ω ∂P, ω ∈ F → ((ΘL ω k : ℂ) ∈ closure (imgHulls (W' · ω) (ζ' ω)) ∨
      (IsBounded (imgHulls (W' · ω) (ζ' ω)) ∧
        ∀ u : ℝ, u ≤ ΘL ω i₀ → (u : ℂ) ∉ closure (imgHulls (W' · ω) (ζ' ω)))) := by
  set A : Set Ω := {ω | ω ∈ F ∧ (0 : ℝ≥0∞) < ζ' ω} with hAdef
  have hF0 : MeasurableSet[𝓖 0] F := hE.1 _ hE.2.1
  have hζ0 : MeasurableSet[𝓖 0] {ω | (0 : ℝ≥0∞) < ζ' ω} := by
    have := hE.2.2.2.2.2.1 0 univ MeasurableSet.univ
    simpa using this
  have hA : MeasurableSet[𝓖 0] A := hF0.inter hζ0
  have hΘG : ∀ᵐ ω ∂P, ω ∈ A → (ΘL ω, (fun _ => (![] : Fin 0 → ℝ)) ω) ∈
      {s : (Fin n → ℝ) × (Fin 0 → ℝ) | s.1 i₀ < 0 ∧ Antitone s.1} := by
    filter_upwards [hE.2.2.2.2.2.2.2.2, hneg] with ω hp hn hωA
    refine ⟨hn hωA.1, ?_⟩
    have hpa := (hp hωA.1).antitone_vL (t := 0) (by simpa using hωA.2)
    have e : (fun i => VL' i 0 ω) = ΘL ω := funext fun i => (hp hωA.1).vL_zero i
    simpa [e] using hpa
  have htr := ae_exists_code_of_randomWord' hE hA (fun ω h => h.1) (measurableSet_antiWord n i₀)
    (fun _ _ _ j => j.elim0) hΘG (measurableSet_idSet i₀ k) fun s hs => hlaw s.1 s.2 hs.1 hs.2
  filter_upwards [htr, hΘG] with ω hω hG hωF
  by_cases hz : (0 : ℝ≥0∞) < ζ' ω
  · obtain ⟨x, hxC, hxS, -, hag⟩ := hω ⟨hωF, hz⟩
    have hs := hG ⟨hωF, hz⟩
    exact dichotomy_of_code hxC.1.2.2 i₀ k ((hs.2 hki).trans_lt hs.1) hs.1 hxS fun t ht => (hag t ht).1
  · right
    have he : imgHulls (W' · ω) (ζ' ω) = ∅ := imgHulls_of_eq_zero (not_lt.1 hz |>.antisymm bot_le)
    rw [he]
    exact ⟨Bornology.isBounded_empty, fun u _ => by simp⟩

/-- **(I1), (G3), PROVED** (A2P3's `ImageDichotomyG3Statement`, exactly). -/
theorem imageDichotomyG3Statement (κ : ℝ) : ImageDichotomyG3Statement.{u} κ := by
  intro hκ4 hκ8 Ω 𝓔 mΩ P hP F ΘL 𝓖 W' VL' VR' B' ζ' hE hneg
  exact dichotomy_of_law (0 : Fin 4) 2 (by decide)
    (fun xL xR h0 hanti => law_of_hasIdPropEvolution (by linarith) (hasIdPropEvolution_G3_all hκ4 hκ8 xR h0 hanti))
    𝓔 P F ΘL 𝓖 W' VL' VR' B' ζ' hE hneg

/-- **(I1), (Eight), PROVED** (A2P3's `ImageDichotomyEightStatement`, exactly). -/
theorem imageDichotomyEightStatement (κ : ℝ) : ImageDichotomyEightStatement.{u} κ := by
  intro hκ8 Ω 𝓔 mΩ P hP F ΘL 𝓖 W' VL' VR' B' ζ' hE hneg
  exact dichotomy_of_law (0 : Fin 3) 1 (by decide)
    (fun xL xR h0 hanti => law_of_hasIdPropEvolution (by linarith) (hasIdPropEvolution_eight_all hκ8 xR h0 hanti))
    𝓔 P F ΘL 𝓖 W' VL' VR' B' ζ' hE hneg

/-- **A.2, part 3, (G3)** from (I2) through the exact (I1) (`P3.smallInHullG3Statement_of_split`). -/
theorem smallInHullG3Statement_of_pairContact' {κ : ℝ} (hC : PairContactG3Statement.{u} κ) :
    A2SmallInHullG3Statement.{u} κ :=
  smallInHullG3Statement_of_split (imageDichotomyG3Statement κ) hC

/-- **A.2, part 3, (Eight)** from (I2) through the exact (I1) (`P3.smallInHullEightStatement_of_split`). -/
theorem smallInHullEightStatement_of_pairContact' {κ : ℝ} (hC : PairContactEightStatement.{u} κ) :
    A2SmallInHullEightStatement.{u} κ :=
  smallInHullEightStatement_of_split (imageDichotomyEightStatement κ) hC

end Statements

end InteractingSLE.ZhanGT4.A2P3ID
