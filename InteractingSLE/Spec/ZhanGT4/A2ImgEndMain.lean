/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2ImgEndAssembly
import InteractingSLE.Spec.ZhanGT4.A2TipSepImage
import InteractingSLE.Spec.ZhanGT4.A2TipSepMain
import InteractingSLE.Spec.ZhanGT4.A2TipSepWire
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# The image endpoint, part 5: `ImageEndpointG3Statement` and `ImageEndpointEightStatement` PROVED

Packet PROVE-A2-IMGEND. Source: Astra, *Follow-up 5* §1.1–§1.2 and Lemma 1.2 (L66–L196,
`source/external/AstraIG1/ig1_followup5.txt`, R73). The two named statements of PROVE-ZHAN-A2TIPSEP
(`A2TipSep.ImageEndpointG3Statement`, `A2TipSep.ImageEndpointEightStatement`): every local evolution of the random
(G3) / (Eight) image word satisfies `ImageEndpointAlt` almost surely on its live event.

Proof: reflect (`isRandomWordEvolutionUpTo_reflect`) into A.2 part 1's chart; restart at every positive rational time
(`ae_restart_codes`) with the code event `goodSet` of full canonical law at every separated ordered start
(`codeLaw_compl_goodSet_eq_zero`, from A.2 part 1's `ae_noncollision_simpleTrace` and PROVE-GLUECOND9's strip endpoint
for the restarted words); pathwise, the local path extends to a simple crosscut beyond the large tip
(`exists_exit_trace_of_restarts`), whose truncation at the local stop is `ImageEndpointAlt`
(`A2TipSep.imageEndpointAlt_of_isSmallCrosscut`); `ImageEndpointAlt` only sees the driver before the stop
(`imageEndpointAlt_congr`). No conditioning on the word, so the probability space is arbitrary.

* **`imageEndpointG3Statement (κ : ℝ) : A2TipSep.ImageEndpointG3Statement κ`**;
* **`imageEndpointEightStatement (κ : ℝ) : A2TipSep.ImageEndpointEightStatement κ`**;
* consequences (PROVE-ZHAN-A2TIPSEP's wiring with its residual discharged): A.2 part 2 in R70's form
  (`a2TipSep{G3,Eight}AugStatement`, `a2HullInside{G3,Eight}AugStatement`, unconditional), and A.2/A.3 from R72's A.1
  target and A.2 part 3 alone (`fourForceCrosscutG3LifeStatement_of_refUA'`,
  `threeForceCrosscutEightStatement_of_refUA'`, `firstSwallowCrosscutStatement_of_refUA'`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2ImgEnd

open QuantumZipper (H fwdHull)
open Sec2 Sec2.Assembly Sec7.RandRestart

/-! ### The image endpoint alternative only sees the driver before the stop -/

section Congr

variable {f f' : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

theorem fwdHull_extPath_congr (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → f t = f' t) {t : ℝ} (ht : 0 ≤ t)
    (htτ : ENNReal.ofReal t < τ) : fwdHull (Strip.extPath f) t = fwdHull (Strip.extPath f') t := by
  obtain ⟨t₂, htt₂, ht₂τ⟩ := exists_real_btwn_of_lt (t := t.toNNReal) htτ
  have htt₂' : t < t₂ := by simpa [Real.coe_toNNReal _ ht] using htt₂
  refine fwdHull_eq_of_eqOn ht htt₂' fun r hr => ?_
  simp only [Strip.extPath]
  refine h _ (lt_of_le_of_lt ?_ ht₂τ)
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hr.1]
  exact ENNReal.ofReal_le_ofReal hr.2

theorem imgU_congr (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → f t = f' t) :
    A2TipSep.imgU (Strip.extPath f) τ = A2TipSep.imgU (Strip.extPath f') τ := by
  simp only [A2TipSep.imgU]
  refine iUnion_congr fun t => iUnion_congr_Prop Iff.rfl fun ht => ?_
  exact fwdHull_extPath_congr h t.coe_nonneg (by simpa using ht)

/-- **`ImageEndpointAlt` only sees the driver before the stop.** -/
theorem imageEndpointAlt_congr (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → f t = f' t) {b : ℝ}
    (hA : A2TipSep.ImageEndpointAlt (Strip.extPath f) τ b) : A2TipSep.ImageEndpointAlt (Strip.extPath f') τ b := by
  have hU := imgU_congr h
  rcases hA with ⟨γ, h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨γ, h1, h2, h3, by rw [← hU]; exact h4⟩
  · refine Or.inr ⟨by rw [← hU]; exact h1, by rw [← hU]; exact h2, fun t ht => ?_⟩
    by_cases htτ : ENNReal.ofReal t < τ
    · obtain ⟨δ, hδ, hsub⟩ := h3 t ht
      exact ⟨δ, hδ, by rw [← hU, ← fwdHull_extPath_congr h ht.le htτ]; exact hsub⟩
    · refine ⟨1, one_pos, fun z hz => ?_⟩
      obtain ⟨s, hs⟩ := mem_iUnion.1 hz.1
      obtain ⟨hsτ, hzs⟩ := mem_iUnion.1 hs
      refine (QuantumZipper.fwdHull_mono).1 ?_ hzs
      have : ((s : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal t := lt_of_lt_of_le hsτ (not_lt.1 htτ)
      rw [← ENNReal.ofReal_coe_nnreal] at this
      exact ((ENNReal.ofReal_lt_ofReal_iff ht).1 this).le

/-- With a zero stop the image hulls are empty and the premature alternative holds. -/
theorem imageEndpointAlt_zero (f : ℝ≥0 → ℝ) (b : ℝ) : A2TipSep.ImageEndpointAlt (Strip.extPath f) 0 b := by
  have hU : A2TipSep.imgU (Strip.extPath f) 0 = ∅ := by
    simp [A2TipSep.imgU]
  refine Or.inr ⟨by rw [hU]; exact Bornology.isBounded_empty, fun u hu => ?_, fun t _ => ⟨1, one_pos, ?_⟩⟩
  · rw [hU, closure_empty] at hu; exact absurd hu (notMem_empty _)
  · rw [hU, empty_inter]; exact empty_subset _

end Congr

/-! ### Reflection of a random-word local evolution -/

theorem isRandomWordEvolutionUpTo_reflect {a : ℝ} {nL nR : ℕ} {Ω : Type*} {𝓔 : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : Restart.StoppedK2.IsRandomWordEvolutionUpTo a P 𝓔 F ΘL ΘR ρL ρR 𝓖 W VL VR B ζ) :
    Restart.StoppedK2.IsRandomWordEvolutionUpTo a P 𝓔 F (fun ω => -ΘR ω) (fun ω => -ΘL ω) ρR ρL 𝓖 (-W)
      (fun i => -VR i) (fun i => -VL i) (-B) ζ := by
  obtain ⟨h0, hF, hΘL, hΘR, hB, hW, hVL, hVR, hpath⟩ := h
  refine ⟨h0, hF, hΘR.neg, hΘL.neg, hB.neg, hW.neg, fun i => (hVR i).neg, fun i => (hVL i).neg, ?_⟩
  filter_upwards [hpath] with ω hp hωF
  exact (hp hωF).reflect

/-! ### The reflected words -/

section Words

variable {k : ℝ}

/-- Admissibility (by positions) of the changed reflected (G3) word at every ordered start. -/
theorem g3_adm_all (hk2 : 2 ≤ k) (hk4 : k ≤ 4) (s : (Fin 3 → ℝ) × (Fin 1 → ℝ))
    (hs : IsOrderedForceWord s.1 s.2) :
    Sec4.HasAdmissiblePartialSums k ![2 - k / 2, k - 4, 0] ![3 * k / 2 - 4] s.1 s.2 := by
  have h01 : s.1 1 ≤ s.1 0 := hs.1 (show (0 : Fin 3) ≤ 1 by decide)
  have h12 : s.1 2 ≤ s.1 1 := hs.1 (show (1 : Fin 3) ≤ 2 by decide)
  refine ⟨fun z _ hex => ?_, fun z _ hex => ?_⟩
  · rw [Finset.sum_filter, Fin.sum_univ_three]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    obtain ⟨i, hi⟩ := hex
    fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hi <;>
      split_ifs <;> linarith
  · rw [Finset.sum_filter, Fin.sum_univ_one]
    obtain ⟨i, hi⟩ := hex
    rw [Subsingleton.elim i 0] at hi
    simp only [Fin.isValue, Matrix.cons_val_zero, hi, ↓reduceIte]
    linarith

/-- Admissibility (by positions) of the changed reflected (Eight) word at every ordered start. -/
theorem e8_adm_all (hk2 : k ≤ 2) (s : (Fin 2 → ℝ) × (Fin 1 → ℝ)) (hs : IsOrderedForceWord s.1 s.2) :
    Sec4.HasAdmissiblePartialSums k ![k / 2 - 2, 0] ![-(k / 2)] s.1 s.2 := by
  have h01 : s.1 1 ≤ s.1 0 := hs.1 (show (0 : Fin 2) ≤ 1 by decide)
  refine ⟨fun z _ hex => ?_, fun z _ hex => ?_⟩
  · rw [Finset.sum_filter, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    obtain ⟨i, hi⟩ := hex
    fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one] at hi <;> split_ifs <;> linarith
  · rw [Finset.sum_filter, Fin.sum_univ_one]
    obtain ⟨i, hi⟩ := hex
    rw [Subsingleton.elim i 0] at hi
    simp only [Fin.isValue, Matrix.cons_val_zero, hi, ↓reduceIte]
    linarith

end Words

/-! ### The two statements -/

open A2X in
/-- **The image endpoint theorem, (G3), PROVED** (follow-up 5 §1.1–§1.2): for `4 < κ < 8`, every local evolution of
the random (G3) image word satisfies `ImageEndpointAlt` almost surely on its live event. -/
theorem imageEndpointG3Statement (κ : ℝ) : A2TipSep.ImageEndpointG3Statement.{u} κ := by
  intro hκ4 hκ8 Ω 𝓔 mΩ P hP F ΘL ΘR 𝓖 W VL VR B ζ hE hw
  obtain ⟨hk2, hk4⟩ := kh_bounds_G3 hκ4 hκ8
  have hk0 : 0 < kh κ := by linarith
  have hEr := isRandomWordEvolutionUpTo_reflect hE
  have hS := codeLaw_compl_goodSet_eq_zero (k := kh κ) (ρL := smallG3RhoR κ) (ρR := smallG3RhoL κ)
    (ρL' := ![2 - kh κ / 2, kh κ - 4, 0]) hk0 hk4.le
    (fun i hi => by fin_cases i <;> first | rfl | exact absurd rfl hi) (g3_adm_all hk2.le hk4.le)
    (A2P1.g3_sum _) (A2P1.g3_preL hk0 hk4) (A2P1.one_preR (by linarith)) (A2P1.g3_pre hk2.le hk4.le)
    (A2P1.g3_q hk0 hk4)
  have hword : ∀ ω, ΘL ω 0 = 0 → ΘR ω 0 = 0 → 0 < ΘR ω 1 → ΘR ω 1 < ΘR ω 2 →
      StrictAnti (-ΘR ω) ∧ IsOrderedForceWord (-ΘR ω) (-ΘL ω) := by
    intro ω h0L h0R h1 h12
    have hsa : StrictAnti (-ΘR ω) := by
      rw [Fin.strictAnti_iff_succ_lt]
      intro i
      fin_cases i <;> simp <;> linarith
    refine ⟨hsa, hsa.antitone, fun i => ?_, fun a c _ => le_of_eq (by rw [Subsingleton.elim a c]),
      fun i => ?_⟩
    · fin_cases i <;> simp <;> linarith
    · rw [Subsingleton.elim i 0]; simp [h0L]
  have hord : ∀ᵐ ω ∂P, ω ∈ F → IsOrderedForceWord ((fun ω => -ΘR ω) ω) ((fun ω => -ΘL ω) ω) := by
    filter_upwards [hw] with ω hω hωF
    obtain ⟨h0L, h0R, h1, h12⟩ := hω hωF
    exact (hword ω h0L h0R h1 h12).2
  have hrest := ae_restart_codes hk0 hEr hord measurableSet_goodSet hS
  filter_upwards [hrest, hEr.2.2.2.2.2.2.2.2, hw] with ω hRω hpω hwω hωF
  obtain ⟨h0L, h0R, h1, h12⟩ := hwω hωF
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ ζ ω) with hζ0 | hζ0
  · rw [← hζ0]; exact imageEndpointAlt_zero _ _
  obtain ⟨hxL, hF⟩ := hword ω h0L h0R h1 h12
  obtain ⟨wG, ζG, η, hτζ, hag, hζG0, hζGt, hη, hinj, hH, x₀, hx₀, hend⟩ :=
    exists_exit_trace_of_restarts (hpω hωF) hF hxL (A2P1.g3_sum _) hζ0 (hRω hωF)
  have hη' : IsGeneratingTrace (fun t => -(fun t => -wG t) t) ζG η := by simpa only [neg_neg] using hη
  have hx₀' : x₀ < -ΘR ω 2 := by simpa using hx₀
  obtain ⟨γ, hγ⟩ := A2P1.exists_isSmallCrosscut_of_reflect (x₁ := -ΘR ω 2) hζG0 hζGt hη' hinj hH
    (by linarith) hend
  have hA := A2TipSep.imageEndpointAlt_of_isSmallCrosscut (by linarith) hγ hτζ
  rw [neg_neg] at hA
  refine imageEndpointAlt_congr (fun t ht => ?_) hA
  rw [hag t ht]; simp

open A2X in
/-- **The image endpoint theorem, (Eight), PROVED** (follow-up 5 §1.1–§1.2): for `κ ≥ 8`, every local evolution of the
random (Eight) image word satisfies `ImageEndpointAlt` almost surely on its live event. -/
theorem imageEndpointEightStatement (κ : ℝ) : A2TipSep.ImageEndpointEightStatement.{u} κ := by
  intro hκ8 Ω 𝓔 mΩ P hP F ΘL ΘR 𝓖 W VL VR B ζ hE hw
  obtain ⟨hk0, hk2⟩ := kh_bounds_eight hκ8
  have hEr := isRandomWordEvolutionUpTo_reflect hE
  have hS := codeLaw_compl_goodSet_eq_zero (k := kh κ) (ρL := smallEightRhoR κ) (ρR := smallEightRhoL κ)
    (ρL' := ![kh κ / 2 - 2, 0]) hk0 (by linarith)
    (fun i hi => by fin_cases i <;> first | rfl | exact absurd rfl hi) (e8_adm_all hk2)
    (A2P1.e8_sum _) (A2P1.e8_preL hk0) (A2P1.one_preR (by linarith)) (A2P1.e8_pre hk2)
    (A2P1.e8_q hk0 (by linarith))
  have hword : ∀ ω, ΘL ω 0 = 0 → ΘR ω 0 = 0 → 0 < ΘR ω 1 →
      StrictAnti (-ΘR ω) ∧ IsOrderedForceWord (-ΘR ω) (-ΘL ω) := by
    intro ω h0L h0R h1
    have hsa : StrictAnti (-ΘR ω) := by
      rw [Fin.strictAnti_iff_succ_lt]
      intro i
      fin_cases i; simp; linarith
    refine ⟨hsa, hsa.antitone, fun i => ?_, fun a c _ => le_of_eq (by rw [Subsingleton.elim a c]),
      fun i => ?_⟩
    · fin_cases i <;> simp <;> linarith
    · rw [Subsingleton.elim i 0]; simp [h0L]
  have hord : ∀ᵐ ω ∂P, ω ∈ F → IsOrderedForceWord ((fun ω => -ΘR ω) ω) ((fun ω => -ΘL ω) ω) := by
    filter_upwards [hw] with ω hω hωF
    obtain ⟨h0L, h0R, h1⟩ := hω hωF
    exact (hword ω h0L h0R h1).2
  have hrest := ae_restart_codes hk0 hEr hord measurableSet_goodSet hS
  filter_upwards [hrest, hEr.2.2.2.2.2.2.2.2, hw] with ω hRω hpω hwω hωF
  obtain ⟨h0L, h0R, h1⟩ := hwω hωF
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ ζ ω) with hζ0 | hζ0
  · rw [← hζ0]; exact imageEndpointAlt_zero _ _
  obtain ⟨hxL, hF⟩ := hword ω h0L h0R h1
  obtain ⟨wG, ζG, η, hτζ, hag, hζG0, hζGt, hη, hinj, hH, x₀, hx₀, hend⟩ :=
    exists_exit_trace_of_restarts (hpω hωF) hF hxL (A2P1.e8_sum _) hζ0 (hRω hωF)
  have hη' : IsGeneratingTrace (fun t => -(fun t => -wG t) t) ζG η := by simpa only [neg_neg] using hη
  have hx₀' : x₀ < -ΘR ω 1 := by simpa using hx₀
  obtain ⟨γ, hγ⟩ := A2P1.exists_isSmallCrosscut_of_reflect (x₁ := -ΘR ω 1) hζG0 hζGt hη' hinj hH
    (by linarith) hend
  have hA := A2TipSep.imageEndpointAlt_of_isSmallCrosscut (by linarith) hγ hτζ
  rw [neg_neg] at hA
  refine imageEndpointAlt_congr (fun t ht => ?_) hA
  rw [hag t ht]; simp

/-! ### Consequences: PROVE-ZHAN-A2TIPSEP's wiring with the image endpoint discharged -/

/-- **A.2, part 2, step 1, (G3), augmented** (R70), unconditional. -/
theorem a2TipSepG3AugStatement (κ : ℝ) : A2TipSep.A2TipSepG3AugStatement.{u} κ :=
  A2TipSep.a2TipSepG3AugStatement_of_imageEndpoint (imageEndpointG3Statement κ)

/-- **A.2, part 2, step 1, (Eight), augmented** (R70), unconditional. -/
theorem a2TipSepEightAugStatement (κ : ℝ) : A2TipSep.A2TipSepEightAugStatement.{u} κ :=
  A2TipSep.a2TipSepEightAugStatement_of_imageEndpoint (imageEndpointEightStatement κ)

/-- **A.2, part 2, (G3), augmented** (R70), unconditional. -/
theorem a2HullInsideG3AugStatement (κ : ℝ) : A2TipSep.A2HullInsideG3AugStatement.{u} κ :=
  A2TipSep.a2HullInsideG3AugStatement_of_imageEndpoint (imageEndpointG3Statement κ)

/-- **A.2, part 2, (Eight), augmented** (R70), unconditional. -/
theorem a2HullInsideEightAugStatement (κ : ℝ) : A2TipSep.A2HullInsideEightAugStatement.{u} κ :=
  A2TipSep.a2HullInsideEightAugStatement_of_imageEndpoint (imageEndpointEightStatement κ)

/-- **A.3's four-force crosscut, (G3)**, from R72's A.1 target and A.2 part 3 (A.2 parts 1–2 are proved). -/
theorem fourForceCrosscutG3LifeStatement_of_refUA' {κ : ℝ} (hA1 : A1Ref.A1DualCouplingG3RefUAStatement κ)
    (h3 : A2X.A2SmallInHullG3Statement.{u} κ) : A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  A2TipSep.fourForceCrosscutG3LifeStatement_of_refUA hA1 (A2P1.a2SmallCrosscutG3Statement κ)
    (imageEndpointG3Statement κ) h3

/-- **A.3's three-force crosscut, (Eight)**, from R72's A.1 target and A.2 part 3. -/
theorem threeForceCrosscutEightStatement_of_refUA' {κ : ℝ} (hA1 : A1Ref.A1DualCouplingEightRefUAStatement κ)
    (h3 : A2X.A2SmallInHullEightStatement.{u} κ) : A35.ThreeForceCrosscutEightStatement.{u} κ :=
  A2TipSep.threeForceCrosscutEightStatement_of_refUA hA1 (A2P1.a2SmallCrosscutEightStatement κ)
    (imageEndpointEightStatement κ) h3

/-- **A.3's first-swallow crosscut** from R72's A.1 targets and A.2 part 3. -/
theorem firstSwallowCrosscutStatement_of_refUA' {κ : ℝ} (hA1 : A1Ref.A1DualCouplingG3RefUAStatement κ)
    (h3 : A2X.A2SmallInHullG3Statement.{0} κ) (hA1' : A1Ref.A1DualCouplingEightRefUAStatement κ)
    (h3' : A2X.A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  A2TipSep.firstSwallowCrosscutStatement_of_refUA hA1 (A2P1.a2SmallCrosscutG3Statement κ)
    (imageEndpointG3Statement κ) h3 hA1' (A2P1.a2SmallCrosscutEightStatement κ) (imageEndpointEightStatement κ) h3'

end InteractingSLE.ZhanGT4.A2ImgEnd
