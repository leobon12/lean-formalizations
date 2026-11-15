/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Aux25Term
import InteractingSLE.Spec.Sec4.Aux25Prob
import InteractingSLE.Spec.Sec7.ContinuityProb10Close

/-!
# Restricting an integrated path to a contact time

Packet PROVE-STAGED9 (ruling R78). The killed comparison premise `CompPremiseFarK` supplies a generating trace only up
to the first far contact. The landed pathwise trace lemmas (Aux. lemma 25, Lemma G12, Lemma GB7a) are stated for an
integrated path and a trace on the same interval. This file makes them available on `[0, T]` for a contact time
`T < ζ` of a right mark `k`, without any new probability:

* **`isIntegratedSLEPath_restrict`**: an integrated path restricted to `[0, T)`, `0 < T < ζ`, is again an integrated
  path of Definition 2.1 with lifetime `T`, for any weights `(ρL'; ρR')` whose continuation threshold fails before `T`
  and holds at `T` — the driving equation holds with the recomputed path `restrictB` (Definition 2.1 is pathwise; the
  Brownian property lives in the evolution);
* `contactWeightR`, **`thresholdCondition_contactWeightR_iff`**: the weights `(0; −2 · 1_k)`, whose threshold is
  exactly "the mark `k` is at the driver";
* **`isIntegratedSLEPath_contact`**: the restriction at the first contact of the mark `k`;
* **`injOn_le_of_contact`**: Aux. lemma 25 on `[0, T]` for a trace on `[0, T]` only (the localization and the
  endpoint exclusion are path properties on `[0, ζ)`, restricted to `[0, T)`; the contact time by
  `Sec2.IsForcePath.trace_ne_trace_terminal` for the restricted path, whose limit state is a threshold state).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

open QuantumZipper (fwdHull)

namespace InteractingSLE.Sec5.CrossCond.StagedK2

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-! ### Restriction with new weights -/

/-- The driving noise of a path for the weights `(ρL; ρR)`: `(w − Σ ρ ∫ ds/(w − v))/√κ`. -/
def restrictB (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (w t - ((∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal)) +
    (∑ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal)))) / Real.sqrt κ

/-- The state at `T` is the limit of the state from the left, for a path continuous at `T < ζ`. -/
theorem tendsto_state_of_lt (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {T : ℝ≥0}
    (hTζ : (T : ℝ≥0∞) < ζ) :
    Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
      (𝓝 (w T, fun i => vL i T, fun i => vR i T)) := by
  have hF := hp.isForcePath
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hn := hopen.mem_nhds hTζ
  have hc : ContinuousAt (fun t => (w t, fun i => vL i t, fun i => vR i t)) T :=
    (hF.continuousOn_w.continuousAt hn).prodMk ((continuousAt_pi.2 fun i =>
      (hF.continuousOn_vL i).continuousAt hn).prodMk (continuousAt_pi.2 fun i =>
        (hF.continuousOn_vR i).continuousAt hn))
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-- **Restriction of an integrated path with new weights.** If `0 < T < ζ` and the continuation threshold of the
weights `(ρL'; ρR')` fails before `T` and holds at `T`, the path restricted to `[0, T)` is an integrated path of
Definition 2.1 with lifetime `T` for these weights, with the recomputed noise `restrictB κ ρL' ρR' w vL vR`. -/
theorem isIntegratedSLEPath_restrict (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hκ : 0 < κ)
    {T : ℝ≥0} (hT0 : 0 < T) (hTζ : (T : ℝ≥0∞) < ζ) {ρL' : Fin nL → ℝ} {ρR' : Fin nR → ℝ}
    (hnot : ∀ t : ℝ≥0, t < T →
      ¬ ForceWord.ThresholdCondition ρL' ρR' (w t) (fun i => vL i t) (fun i => vR i t))
    (hthr : ForceWord.ThresholdCondition ρL' ρR' (w T) (fun i => vL i T) (fun i => vR i T)) :
    IsIntegratedSLEPath κ xL xR ρL' ρR' w vL vR (restrictB κ ρL' ρR' w vL vR) T := by
  have hlim := tendsto_state_of_lt hp hTζ
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -, h13, h14, h15, h16, -, -, -⟩ := hp
  have hlt : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < T → (t : ℝ≥0∞) < ζ := fun ht => ht.trans hTζ
  have hsub : {t : ℝ≥0 | (t : ℝ≥0∞) < T} ⊆ {t | (t : ℝ≥0∞) < ζ} := fun t ht => hlt ht
  have hsq : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  refine ⟨h0, h1, h2, h3.mono hsub, fun i => (h4 i).mono hsub, fun i => (h5 i).mono hsub,
    fun t ht => h6 t (hlt ht), fun t ht => h7 t (hlt ht), fun t ht => h8 t (hlt ht),
    fun t ht => h9 t (hlt ht), fun t ht => h10 t (hlt ht), fun t ht => h11 t (hlt ht),
    fun t _ => ?_, fun t ht => h13 t (hlt ht), fun t ht => h14 t (hlt ht),
    fun i => measure_mono_null ?_ (h15 i), fun i => measure_mono_null ?_ (h16 i),
    fun t ht => hnot t (ENNReal.coe_lt_coe.1 ht), fun hT => ?_, fun T' hT' hT'T w₀ vL₀ vR₀ hl => ?_⟩
  · simp only [restrictB]
    rw [mul_div_cancel₀ _ hsq]
    ring
  · exact fun s ⟨hs0, hs, he⟩ => ⟨hs0, hlt hs, he⟩
  · exact fun s ⟨hs0, hs, he⟩ => ⟨hs0, hlt hs, he⟩
  · exact absurd (ENNReal.coe_eq_zero.1 hT) hT0.ne'
  · have hTT : T' = T := ENNReal.coe_injective hT'T
    subst hTT
    have : NeBot (𝓝[<] T') := nhdsLT_neBot_of_exists_lt ⟨0, hT'⟩
    have he := tendsto_nhds_unique hl hlim
    simp only [Prod.mk.injEq] at he
    obtain ⟨hw, hvL, hvR⟩ := he
    rw [hw, hvL, hvR]
    exact hthr

/-! ### The contact weights -/

/-- The weights `(0; −2 · 1_k)`: their continuation threshold is "the right mark `k` is at the driver". -/
def contactWeightR (k : Fin nR) : Fin nR → ℝ := fun j => if j = k then -2 else 0

theorem thresholdCondition_contactWeightR_iff (k : Fin nR) (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ) :
    ForceWord.ThresholdCondition (0 : Fin nL → ℝ) (contactWeightR k) w₀ vL₀ vR₀ ↔ vR₀ k = w₀ := by
  classical
  have hL : (∑ i ∈ univ.filter (fun i => vL₀ i = w₀), (0 : Fin nL → ℝ) i) = 0 := by simp
  have hR : (∑ j ∈ univ.filter (fun j => vR₀ j = w₀), contactWeightR k j) =
      if vR₀ k = w₀ then -2 else 0 := by
    by_cases h : vR₀ k = w₀
    · rw [Finset.sum_eq_single_of_mem k (by simp [h]) fun j _ hj => by simp [contactWeightR, hj]]
      simp [contactWeightR, h]
    · rw [Finset.sum_eq_zero fun j hj => ?_]
      · simp [h]
      · have hj' : vR₀ j = w₀ := (Finset.mem_filter.1 hj).2
        have hjk : j ≠ k := fun e => h (e ▸ hj')
        simp [contactWeightR, hjk]
  unfold ForceWord.ThresholdCondition
  rw [hL, hR]
  constructor
  · rintro (h | h)
    · norm_num at h
    · by_contra hne
      simp only [hne, ↓reduceIte] at h
      norm_num at h
  · intro h
    right
    simp only [h, ↓reduceIte, le_refl]

/-- **The restriction at the first contact of a right mark.** If the right mark `k` stays strictly right of the
driver on `[0, T)` and meets it at `T`, `0 < T < ζ`, the path restricted to `[0, T)` is an integrated path with the
contact weights, whose lifetime is `T`. -/
theorem isIntegratedSLEPath_contact (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hκ : 0 < κ)
    {T : ℝ≥0} (hT0 : 0 < T) (hTζ : (T : ℝ≥0∞) < ζ) {k : Fin nR} (hbefore : ∀ t < T, w t < vR k t)
    (hmeet : vR k T = w T) :
    IsIntegratedSLEPath κ xL xR 0 (contactWeightR k) w vL vR (restrictB κ 0 (contactWeightR k) w vL vR) T :=
  isIntegratedSLEPath_restrict hp hκ hT0 hTζ
    (fun t ht h => ((hbefore t ht).ne' ((thresholdCondition_contactWeightR_iff k _ _ _).1 h)))
    ((thresholdCondition_contactWeightR_iff k _ _ _).2 hmeet)

/-! ### Aux. lemma 25 up to a contact -/

open Aux25

theorem hasLocalization_mono {T : ℝ≥0∞} (h : HasLocalization w vL vR ζ) (hT : T ≤ ζ) :
    HasLocalization w vL vR T :=
  fun t₁ ht₁ => h t₁ (ht₁.trans_le hT)

theorem noRightEndpoint_mono {T : ℝ≥0∞} (h : NoRightEndpoint w vL vR ζ) (hT : T ≤ ζ) :
    NoRightEndpoint w vL vR T :=
  fun q k m σ hqσ hσ => h q k m σ hqσ (hσ.trans_le hT)

/-- **Aux. lemma 25 on `[0, T]` for a trace up to a contact.** For an integrated path with the localization and
endpoint exclusions of Aux. lemma 24/25 on `[0, ζ)`, and a first contact `T < ζ` of a right mark, every generating
trace on `[0, T]` is injective on `[0, T]`, the contact time included. -/
theorem injOn_le_of_contact (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hκ : 0 < κ)
    {T : ℝ≥0} (hT0 : 0 < T) (hTζ : (T : ℝ≥0∞) < ζ) {k : Fin nR} (hbefore : ∀ t < T, w t < vR k t)
    (hmeet : vR k T = w T) (hloc : HasLocalization w vL vR ζ) (hendR : NoRightEndpoint w vL vR ζ)
    (hendL : NoRightEndpoint (-w) (fun i => -vR i) (fun i => -vL i) ζ) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) : InjOn η {t | (t : ℝ≥0∞) ≤ T} := by
  have hp' := isIntegratedSLEPath_contact hp hκ hT0 hTζ hbefore hmeet
  have hlt := injOn_lt_of_noEndpoint hp' hη (hasLocalization_mono hloc hTζ.le)
    (noRightEndpoint_mono hendR hTζ.le) (noRightEndpoint_mono hendL hTζ.le)
  have hthr : ForceWord.ThresholdCondition (0 : Fin nL → ℝ) (contactWeightR k) (w T) (fun i => vL i T)
      (fun i => vR i T) := (thresholdCondition_contactWeightR_iff k _ _ _).2 hmeet
  have hne : ∀ {r : ℝ≥0}, r < T → η r ≠ η T := fun hr =>
    hp'.isForcePath.trace_ne_trace_terminal hη hT0 rfl (tendsto_state_of_lt hp hTζ) hthr hr
  intro s hs t ht hst
  rw [mem_ofPred_eq, ENNReal.coe_le_coe] at hs ht
  rcases hs.lt_or_eq with hsT | hsT <;> rcases ht.lt_or_eq with htT | htT
  · exact hlt (by rw [mem_ofPred_eq]; exact ENNReal.coe_lt_coe.2 hsT)
      (by rw [mem_ofPred_eq]; exact ENNReal.coe_lt_coe.2 htT) hst
  · exact absurd (htT ▸ hst) (hne hsT)
  · exact absurd (hsT ▸ hst.symm) (hne htT)
  · rw [hsT, htT]

end InteractingSLE.Sec5.CrossCond.StagedK2
