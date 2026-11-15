/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux97GermDet
import InteractingSLE.Spec.Sec7.Aux97GermSrc
import InteractingSLE.Spec.Sec7.LocalExtHExt
import InteractingSLE.Spec.Sec7.LocalExtBHist
import InteractingSLE.Spec.Sec7.Aux97ProofGerm
import InteractingSLE.Spec.Sec7.Lemma75Bridge

/-!
# Aux. lemma 97's germ identification: the extension through the local stop and the germ

Packet PROVE-AUX97G. Sources: Aux. lemma 54 (`source/spec/p241-288.md` L118–L132, p. 246: "Then the stopped coupling
extends to a full coupling with the original optional hull specification"), Aux. lemma 97's proof
(`source/spec/p289-336.md` L553–L576, p. 327).

* **`StoppedSeedExtendStatement κ`** (named input: **Aux. lemma 54 in the source's form**): every stopped seed coupling
  `(h, W_{·∧S}, V_{·∧S})` *extends* to a full two-seed coupling of its own field on an extension of its space: the
  merged two-seed history stopped at `S` is the extension's history stopped at its own local stop. PROVE-LOCEXT-F's
  `StoppedSeedExtensionStatement` recovers the stopped history only through an arbitrary Borel map of the field and the
  extension's history, and its reference field is an arbitrary Borel function of the field; Aux. lemma 97 needs that
  the drivers *agree* through `S`. Stated for words with a seed mark on each side (the flow-line words), where
  PROVE-LOCEXT-L's standard reference exists unconditionally.
  PROVE-LOCEXT-H/L's construction (`hasReferenceExtension_of_recordLaw(_L)`) produces exactly this form (field map `id`,
  recovery map `seedProj`).
* `ae_driver_eq_detDrv`: on a stopped seed coupling, with Aux. lemma 54 and Theorem 1.2 (word-measurable) and Theorem
  1.3, the driver agrees before `S`, at rational times, with the field-determined two-seed driver of the field, and `S`
  precedes the determined lifetime;
* `exists_germ_of_driver_eq` (pathwise): two generating traces whose continuous drivers agree at the rational times
  before a positive time `s` agree on `[0, s/2]`;
* **`aux97GermIdentStatement_of_extend`**: `Sec7.Aux97GermIdentStatement` from Theorem 1.2 (word-measurable form),
  Theorem 1.3 and `StoppedSeedExtendStatement κ` for `0 < κ < 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 LQGMetric

/-- **Named input: Aux. lemma 54 for a stopped seed coupling, in the source's form** (specification p. 246: "Then the
stopped coupling extends to a full coupling with the original optional hull specification. The extension preserves
the whole initial field"). For an ordered force word with a seed mark on each side (as every flow-line word from a
boundary point), admissible seed sums and a radius `r > 0`, every stopped seed
coupling through its local stop `S` extends: on an extension `Ω × C` of `(Ω, Q)` (first marginal `Q`) there is a full
coupling of the two-seed word with the seed sums as weights **whose field is the stopped coupling's field**, with a good
event `G'`, such that the merged two-seed history of the stopped coupling stopped at `S` **is** the history of the full
coupling stopped at its capped local stop of radius `r` (empty seed sides normalized, `seedProj`). -/
def StoppedSeedExtendStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ),
    IsOrderedForceWord xL xR → ((∃ i, xL i = 0) ∧ ∃ j, xR j = 0) → 0 < r → -2 < seedSumL xL ρL →
    -2 < seedSumR xR ρR →
    ∀ {Ω : Type u} {_ : MeasurableSpace Ω} (Q : Measure Ω) [IsProbabilityMeasure Q] (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h →
      ∃ (C : Type u) (_ : MeasurableSpace C) (E : Measure (Ω × C)) (_ : IsProbabilityMeasure E)
        (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × C))) (W' : ℝ≥0 → Ω × C → ℝ)
        (VL' VR' : Fin 1 → ℝ≥0 → Ω × C → ℝ) (B' : ℝ≥0 → Ω × C → ℝ) (ζ' : Ω × C → ℝ≥0∞),
        E.map Prod.fst = Q ∧
        IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR) E 𝓕'
          W' VL' VR' B' ζ' (fun p => h p.1) ∧
        ∃ G' : Set (Ω × C), MeasurableSet G' ∧ E G'ᶜ = 0 ∧
          (∀ p ∈ G', IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
            W' VL' VR' B' ζ' p) ∧
          ∀ᵐ p ∂E, twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S p.1) =
            seedProj xL xR (stoppedHistory (completedState W' VL' VR' ζ') (capStop r G' ζ' W') p)

end LocalExt

namespace Sec7

namespace Aux97G

open LocalExt LQGMetric

/-! ### Paths agreeing at rational times -/

/-- Two functions continuous on `[0, s)` that agree at the nonnegative rationals below `s` agree on `[0, s)`. -/
theorem eq_of_eq_nnrat_lt {f g : ℝ≥0 → ℝ} {s : ℝ≥0} (hf : ContinuousOn f (Iio s)) (hg : ContinuousOn g (Iio s))
    (h : ∀ q : ℚ≥0, (q : ℝ≥0) < s → f q = g q) {x : ℝ≥0} (hx : x < s) : f x = g x := by
  have key : ∀ n : ℕ, ∃ q : ℚ≥0, x < (q : ℝ≥0) ∧ (q : ℝ≥0) < s ∧ ((q : ℝ≥0) : ℝ) < x + 1 / ((n : ℝ) + 1) := by
    intro n
    have hx' : (x : ℝ) < s := hx
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hx' (show (x : ℝ) < x + 1 / ((n : ℝ) + 1) by linarith))
    have hq0 : 0 ≤ q := by
      have : (0 : ℝ) ≤ x := x.2
      exact_mod_cast (show (0 : ℝ) ≤ q by linarith)
    refine ⟨⟨q, hq0⟩, ?_, ?_, ?_⟩
    · rw [← NNReal.coe_lt_coe]; exact hq1
    · rw [← NNReal.coe_lt_coe]; exact hq2.trans_le (min_le_left _ _)
    · exact hq2.trans_le (min_le_right _ _)
  choose q hq1 hq2 hq3 using key
  have hlimR : Tendsto (fun n => ((q n : ℝ≥0) : ℝ)) atTop (𝓝 (x : ℝ)) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hup := (tendsto_const_nhds (x := (x : ℝ))).add h0
    rw [add_zero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (NNReal.coe_lt_coe.2 (hq1 n)).le) fun n => (hq3 n).le
  have hlim : Tendsto (fun n => (q n : ℝ≥0)) atTop (𝓝[Iio s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨NNReal.tendsto_coe.1 hlimR, Eventually.of_forall hq2⟩
  exact tendsto_nhds_unique (((hf x hx).tendsto.comp hlim).congr fun n => h _ (hq2 n))
    ((hg x hx).tendsto.comp hlim)

/-- **The germ, pathwise.** Two generating traces whose drivers (continuous before the lifetimes, `0` at `0`) agree at
the nonnegative rationals before a positive time `s ≤ ζ`, all of which precede the second lifetime `L`, agree on
`[0, s/2]`. -/
theorem exists_germ_of_driver_eq {W D : ℝ≥0 → ℝ} {ζ L : ℝ≥0∞} {η η' : ℝ≥0 → ℂ} {s : ℝ≥0}
    (hη : IsGeneratingTrace W ζ η) (hWc : ContinuousOn W {t | (t : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0)
    (hη' : IsGeneratingTrace D L η') (hDc : ContinuousOn D {t | (t : ℝ≥0∞) < L}) (hD0 : D 0 = 0)
    (hs0 : 0 < s) (hsζ : (s : ℝ≥0∞) ≤ ζ)
    (hag : ∀ q : ℚ≥0, (q : ℝ≥0) < s → ((q : ℝ≥0) : ℝ≥0∞) < L ∧ W q = D q) :
    ∃ δ : ℝ≥0, 0 < δ ∧ (δ : ℝ≥0∞) < ζ ∧ (δ : ℝ≥0∞) < L ∧ ∀ t ≤ δ, η t = η' t := by
  have hδs : s / 2 < s := NNReal.half_lt_self hs0.ne'
  have hltζ : ∀ {t : ℝ≥0}, t < s → (t : ℝ≥0∞) < ζ := fun ht => (ENNReal.coe_lt_coe.2 ht).trans_le hsζ
  have hltL : ∀ {t : ℝ≥0}, t < s → (t : ℝ≥0∞) < L := by
    intro t ht
    obtain ⟨q, hq1, hq2⟩ := LocalExt.exists_nnrat_btwn_withTop (WithTop.coe_lt_coe.2 ht)
    exact (ENNReal.coe_lt_coe.2 hq1).trans (hag q (WithTop.coe_lt_coe.1 hq2)).1
  have hWs : ContinuousOn W (Iio s) := hWc.mono fun t ht => hltζ ht
  have hDs : ContinuousOn D (Iio s) := hDc.mono fun t ht => hltL ht
  refine ⟨s / 2, half_pos hs0, hltζ hδs, hltL hδs, fun t ht => ?_⟩
  have hts : t < s := ht.trans_lt hδs
  have hWD : ∀ r ≤ t, W r = D r := fun r hr =>
    eq_of_eq_nnrat_lt hWs hDs (fun q hq => (hag q hq).2) (hr.trans_lt hts)
  rw [← LP.traceAt_eq_of_isGeneratingTrace hη hWc hW0 (hltζ hts),
    ← LP.traceAt_eq_of_isGeneratingTrace hη' hDc hD0 (hltL hts), LP.traceAt_congr hWD]

/-! ### The driver through the stop -/

theorem stopAt_eq_of_lt {Ω : Type*} {τ : Ω → WithTop ℝ≥0} {q : ℝ≥0} {ω : Ω} (h : (q : WithTop ℝ≥0) < τ ω) :
    stopAt τ q ω = q := by
  unfold stopAt
  cases hτ : τ ω with
  | top => simp
  | coe s =>
    rw [hτ] at h
    simp only [WithTop.untopD_coe]
    exact min_eq_left (WithTop.coe_lt_coe.1 h).le


/-- The field of a stopped seed coupling is a GFF with the two-seed data (clause (d)). -/
theorem isGFFWithBoundaryData_of_isStoppedSeedCoupling {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h₀) :
    IsGFFWithBoundaryData Q h₀ (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL)
      (fun _ : Fin 1 => seedSumR xR ρR) LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) := by
  obtain ⟨-, -, -, -, -, -, -, hhm, hgff, -⟩ := hc
  exact ⟨hhm, hgff⟩

section Agree

variable (h12p : Exist.Staged.Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ)

/-- **The driver through the stop is the field-determined driver.** On a stopped seed coupling through `S`, with Aux.
lemma 54 in the source's form, Theorem 1.2 (word-measurable form) and Theorem 1.3: almost surely, at every nonnegative
rational `q < S`, the field-determined two-seed driver of the field is alive at `q` and equals the driver. -/
theorem ae_driver_eq_detDrv (h13 : Exist.Theorem13Statement.{u}) (hext : StoppedSeedExtendStatement.{u} κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
    (hF : IsOrderedForceWord xL xR) (hseeds : (∃ i, xL i = 0) ∧ ∃ j, xR j = 0) (hr : 0 < r)
    (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h₀) :
    ∀ᵐ ω ∂Q, ∀ q : ℚ≥0, ((q : ℝ≥0) : WithTop ℝ≥0) < S ω →
      ((q : ℝ≥0) : ℝ≥0∞) < (detDrv h12p hκ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL)
        (fun _ => seedSumR xR ρR) (h₀ ω)).2 ∧
      W q ω = (detDrv h12p hκ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL)
        (fun _ => seedSumR xR ρR) (h₀ ω)).1 q := by
  set D := detDrv h12p hκ LP.twoSeedXL LP.twoSeedXR (fun _ : Fin 1 => seedSumL xL ρL)
    (fun _ : Fin 1 => seedSumR xR ρR) with hDdef
  have hDm : Measurable D := measurable_detDrv h12p hκ _ _ _ _
  have hh₀m : Measurable h₀ := (isGFFWithBoundaryData_of_isStoppedSeedCoupling hc).1
  obtain ⟨C, mC, E, hE, 𝓕', W', VL', VR', B', ζ', hEQ, hC', G', -, -, -, hagree⟩ :=
    hext xL xR ρL ρR r hF hseeds hr hL hR Q W VL VR S h₀ hc
  have hdet := ae_detDrv_eq h12p hκ h13 isOrderedForceWord_twoSeed' hC'
  set Y := stRecHist xL xR W VL VR S with hYdef
  have hYm : Measurable Y := hc.measurable_stRecHist
  have hYeq := hc.ae_stRecHist_eq hr
  set M : Set Ω := ⋂ q : ℚ≥0, ({ω | ((q : ℝ≥0) : WithTop ℝ≥0) < (Y ω).1}ᶜ ∪
    ({ω | ((q : ℝ≥0) : ℝ≥0∞) < (D (h₀ ω)).2} ∩ {ω | ((Y ω).2 q).1 = (D (h₀ ω)).1 q})) with hMdef
  have hMm : MeasurableSet M := by
    refine MeasurableSet.iInter fun q => ((measurableSet_lt measurable_const
      (measurable_fst.comp hYm)).compl).union ((measurableSet_lt measurable_const
      (measurable_snd.comp (hDm.comp hh₀m))).inter (measurableSet_eq_fun ?_ ?_))
    · exact measurable_fst.comp ((measurable_pi_apply q).comp (measurable_snd.comp hYm))
    · exact (measurable_pi_apply (q : ℝ≥0)).comp (measurable_fst.comp (hDm.comp hh₀m))
  have hYE : ∀ᵐ p ∂E, Y p.1 = twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S p.1) := by
    rw [← hEQ] at hYeq
    exact ae_of_ae_map measurable_fst.aemeasurable hYeq
  have hME : ∀ᵐ p ∂E, p.1 ∈ M := by
    filter_upwards [hYE, hagree, hdet] with p h1 h2 h3
    refine mem_iInter.2 fun q => ?_
    by_cases hq : ((q : ℝ≥0) : WithTop ℝ≥0) < (Y p.1).1
    · refine Or.inr ⟨?_, ?_⟩
      · rw [h1, h2] at hq
        have hq' : ((q : ℝ≥0) : WithTop ℝ≥0) < capStop r G' ζ' W' p := hq
        have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < ζ' p := lt_of_lt_of_le hq' (capStop_le r p)
        show ((q : ℝ≥0) : ℝ≥0∞) < (D (h₀ p.1)).2
        rw [h3.1]
        exact hqζ
      · show ((Y p.1).2 q).1 = (D (h₀ p.1)).1 q
        rw [h1, h2] at hq ⊢
        have hq' : ((q : ℝ≥0) : WithTop ℝ≥0) < capStop r G' ζ' W' p := hq
        have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < ζ' p := lt_of_lt_of_le hq' (capStop_le r p)
        show (completedState W' VL' VR' ζ' (stopAt (capStop r G' ζ' W') q p) p).1 = (D (h₀ p.1)).1 q
        rw [stopAt_eq_of_lt hq', h3.2 q hqζ]
        simp only [completedState, hqζ, ↓reduceIte, drivingState]
    · exact Or.inl hq
  have hMQ : ∀ᵐ ω ∂Q, ω ∈ M := by
    rw [← hEQ]
    exact (ae_map_iff measurable_fst.aemeasurable hMm).2 hME
  filter_upwards [hMQ, hYeq] with ω hM hY q hq
  have hYS : (Y ω).1 = S ω := by
    show (stRecHist xL xR W VL VR S ω).1 = S ω
    rw [hY]
    rfl
  have hq' : ((q : ℝ≥0) : WithTop ℝ≥0) < (Y ω).1 := hYS ▸ hq
  rcases mem_iInter.1 hM q with h | ⟨h1, h2⟩
  · exact absurd hq' h
  refine ⟨h1, ?_⟩
  have h2' : ((Y ω).2 q).1 = (D (h₀ ω)).1 q := h2
  rw [← h2']
  show W q ω = ((stRecHist xL xR W VL VR S ω).2 q).1
  rw [hY]
  show W q ω = W (stopAt S q ω) ω
  rw [stopAt_eq_of_lt hq]

end Agree

/-! ### Aux. lemma 97's germ identification -/

/-- **Aux. lemma 97's per-angle identification on a seed germ** (`Sec7.Aux97GermIdentStatement`), from Theorem 1.2 in
its word-measurable form (`Exist.Staged.Theorem12ParamStatement`, R44), Theorem 1.3 (`Exist.Theorem13Statement`) and
Aux. lemma 54 in the source's form (`StoppedSeedExtendStatement κ`, `0 < κ < 4`).

The proof (p. 327): if no non-threshold angle carries a flow line of `h`, take `Q = P` and `X` the two-height GFF
`h + (𝔥_{prop74} − 𝔥_b)`. Otherwise fix such an angle `θ₀` with its coupling and take Aux. lemma 55's Cameron–Martin
measure `Q = Z·P` and the recoded field `X = recode h` (HL3, HL8); both depend only on the distant marks, so they are
the same for every angle (`srcMeasure_eq_of_shift`, `recode_flowField`). For an angle `θ` and a flow line `η` of `h`,
the original coupling under `Q`, stopped at the capped local stop `S`, is a stopped seed coupling with field `X + θχ`
(`isStoppedSeedCoupling_srcMeasure`); `X` is a GFF with the data `prop74Data (−b₋) b₊`. The flow line `η'` of `X` is
the field-determined two-seed trace (`exists_coupling_detDrv`, `isFlowLine_prop74Data_iff`). Aux. lemma 54 extends the
stopped coupling; the driver of the extension is the field-determined driver (`ae_driver_eq_detDrv`), so `W` agrees
with the driver of `η'` before `S > 0`, and the traces agree on `[0, S/2]` (`exists_germ_of_driver_eq`). -/
theorem aux97GermIdentStatement_of_extend (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedSeedExtendStatement.{u} κ) :
    Aux97GermIdentStatement.{u} := by
  intro κ hκ hκ4 b J hb R bm bp hR hbm hbp Ω mΩ P hP h hh
  have hF : IsOrderedForceWord (flowLineXL b J 0) (flowLineXR b J 0) := Theorem15.isOrderedForceWord_flowLine b J 0
  have hr := isSeedRadius_seedRadius (flowLineXL b J 0) (flowLineXR b J 0)
  have hbl : PiecewiseConstantBoundaryData.leftLim b 0 = bm := Sec4.leftLim_eq_of_forall (neg_lt_zero.2 hR) hbm
  have hbr : PiecewiseConstantBoundaryData.rightLim b 0 = bp := Sec4.rightLim_eq_of_forall hR hbp
  have ewL : ∀ θ : ℝ, seedSumL (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ) =
      (-bm - θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := fun θ => by
    rw [seedSumL_flowLine, hbl]
    ring
  have ewR : ∀ θ : ℝ, seedSumR (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ) =
      (bp + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := fun θ => by
    rw [seedSumR_flowLine, hbr]
  by_cases hex : ∃ θ₀ : ℝ, ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ₀) (flowLineRhoR κ b J 0 θ₀) 0
      (flowLineXL b J 0) (flowLineXR b J 0) ∧ ∃ (η₀ : Ω → ℝ≥0 → ℂ) (ζ₀ : Ω → ℝ≥0∞), IsFlowLine κ b J 0 θ₀ P h η₀ ζ₀
  swap
  · obtain ⟨X, hX⟩ := exists_isGFFWithBoundaryData_prop74Data_of hb hh (-bm) bp
    exact ⟨P, X, hP, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl, hX,
      fun θ hT η ζ hη => absurd ⟨θ, hT, η, ζ, hη⟩ hex⟩
  obtain ⟨θ₀, hT₀, η₀, ζ₀, h'₀, 𝓕₀, W₀, VL₀, VR₀, B₀, htr₀, hC₀, -⟩ := hex
  have e₀ : h'₀ = fun ω => Exist.flowField 0 (θ₀ * QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr₀ ω)
  subst e₀
  set Q := srcMeasure κ (flowLineRhoL κ b J 0 θ₀) (flowLineRhoR κ b J 0 θ₀) P hF hr
    (fun ω => Exist.flowField 0 (θ₀ * QuantumZipper.chiC κ) (h ω)) with hQdef
  set X : Ω → DistOn upperHalfPlaneOpens := fun ω => recode κ (flowLineXL b J 0) (flowLineXR b J 0)
    (flowLineRhoL κ b J 0 θ₀) (flowLineRhoR κ b J 0 θ₀) (seedRadius (flowLineXL b J 0) (flowLineXR b J 0)) (h ω)
    with hXdef
  obtain ⟨hQ, hPQ, hQP⟩ := srcMeasure_isEquiv hκ hC₀ hF hr hT₀
  -- every flow-line coupling at a non-threshold angle is, under `Q`, a stopped seed coupling with field `X + θχ`
  have hstop : ∀ θ : ℝ, ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
      (flowLineXL b J 0) (flowLineXR b J 0) →
      ∀ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ)
        (VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
        (flowLineRhoR κ b J 0 θ) P 𝓕 W VL VR B ζ (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω)) →
      ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
        (∀ ω ∈ G, IsGoodNoisePath κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
          (flowLineRhoR κ b J 0 θ) W VL VR B ζ ω) ∧
        IsStoppedSeedCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
          (flowLineRhoR κ b J 0 θ) (seedRadius (flowLineXL b J 0) (flowLineXR b J 0)) Q W VL VR
          (capStop (seedRadius (flowLineXL b J 0) (flowLineXR b J 0)) G ζ W)
          (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (X ω)) := by
    intro θ hT 𝓕 W VL VR B ζ hC
    obtain ⟨G, -, hGm, hG0, hG⟩ := exists_goodNoise_subset hC.1 hκ MeasurableSet.univ (by simp)
    have hc := isStoppedSeedCoupling_srcMeasure hκ hC hF hr hT hGm hG0 hG
    have hQθ : srcMeasure κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) P hF hr
        (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω)) = Q := by
      refine srcMeasure_eq_of_shift hκ hC₀ hC hF hr hT₀ hT (qExt_flowLine θ₀ θ)
        (c := (θ - θ₀) * QuantumZipper.chiC κ) fun ω φ => ?_
      rw [flowField_zero_apply, flowField_zero_apply]
      ring
    have hfield : (fun ω => recode κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
        (flowLineRhoR κ b J 0 θ) (seedRadius (flowLineXL b J 0) (flowLineXR b J 0))
        (Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω))) =
        fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (X ω) := by
      funext ω
      rw [recode_congr (qExt_flowLine θ θ₀), recode_flowField hF hr]
    rw [hQθ, hfield] at hc
    exact ⟨G, hGm, hG0, hG, hc⟩
  -- the two-height GFF
  have hXm : Measurable X := measurable_recode.comp hh.1
  have hgffX : IsGFFWithBoundaryData Q X (prop74Data (-bm) bp) ({0} : Set ℝ) := by
    obtain ⟨_G, -, -, -, hc₀⟩ := hstop θ₀ hT₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hC₀
    have hg := isGFFWithBoundaryData_of_isStoppedSeedCoupling hc₀
    rw [ewL θ₀, ewR θ₀] at hg
    exact isGFFWithBoundaryData_prop74Data_of_flowField hκ hXm hg
  refine ⟨Q, X, hQ, hPQ, hQP, hgffX, fun θ hT η ζ hη => ?_⟩
  obtain ⟨h'θ, 𝓕, W, VL, VR, B, htr, hC, htrace⟩ := hη
  have eθ : h'θ = fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)
  subst eθ
  obtain ⟨G, hGm, hG0, hG, hc⟩ := hstop θ hT 𝓕 W VL VR B ζ hC
  obtain ⟨hsL, hsR⟩ := seedSum_gt_of_not_thresholdCondition hT
  have hseeds : (∃ i, flowLineXL b J 0 i = 0) ∧ ∃ j, flowLineXR b J 0 j = 0 :=
    ⟨⟨⟨0, Nat.succ_pos _⟩, rfl⟩, ⟨⟨0, Nat.succ_pos _⟩, rfl⟩⟩
  have hag := ae_driver_eq_detDrv h12p hκ h13 (hext κ hκ hκ4) hF hseeds hr.1 hsL hsR hc
  obtain ⟨𝓕c, VLc, VRc, Bc, hCc, htrc⟩ := exists_coupling_detDrv h12p hκ h13 isOrderedForceWord_twoSeed'
    (isGFFWithBoundaryData_of_isStoppedSeedCoupling hc)
  have hDreg : ∀ f, ContinuousOn (detDrv h12p hκ LP.twoSeedXL LP.twoSeedXR (fun _ : Fin 1 => seedSumL
      (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ)) (fun _ : Fin 1 => seedSumR (flowLineXR b J 0)
      (flowLineRhoR κ b J 0 θ)) f).1 {t | (t : ℝ≥0∞) < (detDrv h12p hκ LP.twoSeedXL LP.twoSeedXR
      (fun _ : Fin 1 => seedSumL (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ)) (fun _ : Fin 1 => seedSumR
      (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ)) f).2} ∧ (detDrv h12p hκ LP.twoSeedXL LP.twoSeedXR
      (fun _ : Fin 1 => seedSumL (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ)) (fun _ : Fin 1 => seedSumR
      (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ)) f).1 0 = 0 :=
    fun f => ⟨continuousOn_detDrv h12p hκ _ _ _ _ f, detDrv_zero h12p hκ _ _ _ _ f⟩
  generalize detDrv h12p hκ LP.twoSeedXL LP.twoSeedXR (fun _ : Fin 1 => seedSumL (flowLineXL b J 0)
    (flowLineRhoL κ b J 0 θ)) (fun _ : Fin 1 => seedSumR (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ)) = D
    at hag hCc htrc hDreg
  generalize detTrace h12p hκ LP.twoSeedXL LP.twoSeedXR (fun _ : Fin 1 => seedSumL (flowLineXL b J 0)
    (flowLineRhoL κ b J 0 θ)) (fun _ : Fin 1 => seedSumR (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ)) = T at htrc
  refine ⟨fun ω => T (Exist.flowField 0 (θ * QuantumZipper.chiC κ) (X ω)),
    fun ω => (D (Exist.flowField 0 (θ * QuantumZipper.chiC κ) (X ω))).2, ?_, ?_⟩
  · refine (isFlowLine_prop74Data_iff (a := -bm) (b := bp)).2 ⟨fun ω => Exist.flowField 0
      (θ * QuantumZipper.chiC κ) (X ω), 𝓕c, fun t ω => (D (Exist.flowField 0 (θ * QuantumZipper.chiC κ) (X ω))).1 t,
      VLc, VRc, Bc, fun ω => Exist.isTranslateAddConst_flowField 0 _ (X ω), ?_, ?_⟩
    · rw [ewL θ, ewR θ] at hCc
      exact hCc
    · filter_upwards [htrc] with ω hω
      have e : (fun t => T (Exist.flowField 0 (θ * QuantumZipper.chiC κ) (X ω)) t - ((0 : ℝ) : ℂ)) =
          T (Exist.flowField 0 (θ * QuantumZipper.chiC κ) (X ω)) := funext fun t => by
        rw [Complex.ofReal_zero, sub_zero]
      rw [e]
      exact hω
  · -- the germ
    have hGp : ∀ ω ∈ G, IsGoodPath κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
        (flowLineRhoR κ b J 0 θ) W VL VR B ζ ω := fun ω hω => (hG ω hω).1
    filter_upwards [hag, hQP.ae_le htrace, hQP.ae_le (mem_ae_iff.2 hG0 : ∀ᵐ ω ∂P, ω ∈ G), htrc]
      with ω hagω htrω hGω htrcω _
    have hgp := hGp ω hGω
    have hcap := capStop_eq_localStop hGp hF hr hT hGω
    have hpos : 0 < capStop (seedRadius (flowLineXL b J 0) (flowLineXR b J 0)) G ζ W ω :=
      hcap ▸ localStop_pos hGp hT hr.1 ω
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1
      (show capStop (seedRadius (flowLineXL b J 0) (flowLineXR b J 0)) G ζ W ω ≠ ⊤ from hcap ▸ localStop_ne_top)
    have hs0 : 0 < s := by
      rw [← hs] at hpos
      exact WithTop.coe_pos.1 hpos
    have hsζ : (s : ℝ≥0∞) ≤ ζ ω := by
      have h1 := capStop_le (seedRadius (flowLineXL b J 0) (flowLineXR b J 0)) ω (G := G) (ζ := ζ) (W := W)
      rw [← hs] at h1
      exact h1
    obtain ⟨δ, hδ0, hδζ, hδL, hδ⟩ := exists_germ_of_driver_eq htrω hgp.continuousOn_W hgp.W_zero htrcω
      (hDreg _).1 (hDreg _).2 hs0 hsζ fun q hq => hagω q (by rw [← hs]; exact WithTop.coe_lt_coe.2 hq)
    refine ⟨δ, hδ0, hδζ, hδL, fun t ht => ?_⟩
    have e := hδ t ht
    rw [Complex.ofReal_zero, sub_zero] at e
    exact e

end Aux97G

end Sec7

end InteractingSLE
