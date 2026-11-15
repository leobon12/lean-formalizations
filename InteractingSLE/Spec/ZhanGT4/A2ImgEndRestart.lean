/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2ImgEndCode
import InteractingSLE.Spec.ZhanGT4.A2Part3IDMain

/-!
# The image endpoint, part 3: the restarts of a local evolution of a random word

Packet PROVE-A2-IMGEND. Source: Astra, *Follow-up 5* §1.2 L180–L184 (`source/external/AstraIG1/ig1_followup5.txt`,
R73): "For source-coincident lower marks, restart at a positive rational own time before the lifetime. The supplied
high-force entrance gives positive gaps … Apply the generic-mark strip theorem under the restarted kernel and
integrate. Positive rational times cover every positive-lifetime entrance realization."

* **`ae_restart_codes`**: let `(W, V, B)` be a local evolution of an initially measurable random ordered word before
  `ζ` (`Restart.StoppedK2.IsRandomWordEvolutionUpTo`, on an arbitrary probability space), and `S` a Borel set of
  solution codes of full canonical law at every separated ordered start. Then almost surely on the live event, at
  every positive rational time `q < ζ`, the state `V_q − W_q` has a canonical solution code in `S`, driven by
  `B_{q+·} − B_q` (its decoded driving path), of lifetime at least `ζ − q`, which agrees with the local evolution
  restarted at `q` before `ζ − q`.

Proof: at a positive time before `ζ` the word seen from the driver is separated (`IsSLEPathUpTo.vL_lt_vR_of_pos`)
and ordered, deterministically; the restarted Brownian path has the law `(law of the state) ⊗ Wiener` on the
`𝓖_q`-event `F ∩ {q < ζ}` (`WangWu.ImgDrv.joint_law_restart`), so the bad pairs of `S`
(`Sec5.Prop49Exit.badSetS`) are avoided almost surely; separated local pathwise uniqueness
(`Sec7.Band.le_lifetime_of_upTo`) identifies the restarted local path with the canonical code.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2ImgEnd

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Restart Sec7.RandRestart

variable {a : ℝ} {nL nR : ℕ} {Ω : Type*} {𝓔 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The restarts of a random-word local evolution at the positive rational times.** -/
theorem ae_restart_codes (ha : 0 < a)
    (h : Restart.StoppedK2.IsRandomWordEvolutionUpTo a P 𝓔 F ΘL ΘR ρL ρR 𝓖 W VL VR B ζ)
    (hord : ∀ᵐ ω ∂P, ω ∈ F → IsOrderedForceWord (ΘL ω) (ΘR ω)) {S : Set (XCode nL nR)}
    (hSm : MeasurableSet S)
    (hS : ∀ s : (Fin nL → ℝ) × (Fin nR → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 → codeLaw a ρL ρR Sᶜ s = 0) :
    ∀ᵐ ω ∂P, ω ∈ F → ∀ q : ℚ≥0, 0 < q → ((q : ℝ≥0) : ℝ≥0∞) < ζ ω →
      ∃ x ∈ CRel a (fun i => VL i q ω - W q ω) (fun j => VR j q ω - W q ω) ρL ρR, x ∈ S ∧
        (∀ t, cb x t = B (q + t) ω - B q ω) ∧ ζ ω - (q : ℝ≥0) ≤ cζ x ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - (q : ℝ≥0) →
          cw x t = W (q + t) ω - W q ω ∧ (∀ i, cvL x i t = VL i (q + t) ω - W q ω) ∧
            ∀ j, cvR x j t = VR j (q + t) ω - W q ω := by
  obtain ⟨h0, hF, -, -, hB, hWa, hVLa, hVRa, hpath⟩ := h
  obtain ⟨Bv, -, hBvc, -, hBvF, hBvae⟩ := ZhanGT4.exists_continuous_version_zero hB
  have hall : ∀ q : ℚ≥0, ∀ᵐ ω ∂P, ω ∈ F → ((q : ℝ≥0) : ℝ≥0∞) < ζ ω →
      (((fun i => VL i q ω - W q ω), fun j => VR j q ω - W q ω),
        QuantumZipper.StrongMarkov.smPath Bv (fun _ => (q : ℝ≥0)) ω) ∉ Sec5.Prop49Exit.badSetS a ρL ρR S := by
    intro q
    set q' : ℝ≥0 := (q : ℝ≥0) with hq'
    have hle : 𝓖 q' ≤ usualAugmentation 𝓖 P q' := Ito.le_usualAugmentation 𝓖 P q'
    set st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω =>
      ((fun i => Girsanov.killed ζ (VL i) q' ω - Girsanov.killed ζ W q' ω),
        fun j => Girsanov.killed ζ (VR j) q' ω - Girsanov.killed ζ W q' ω) with hst
    have hstm : Measurable[usualAugmentation 𝓖 P q'] st := by
      have hw := (Girsanov.measurable_killed hWa q').mono hle le_rfl
      exact Measurable.prodMk ((@measurable_pi_iff Ω (Fin nL) _ (usualAugmentation 𝓖 P q') _ _).2 fun i =>
          ((Girsanov.measurable_killed (hVLa i) q').mono hle le_rfl).sub hw)
        ((@measurable_pi_iff Ω (Fin nR) _ (usualAugmentation 𝓖 P q') _ _).2 fun j =>
          ((Girsanov.measurable_killed (hVRa j) q').mono hle le_rfl).sub hw)
    have hlt : MeasurableSet[𝓖 q'] {ω | (q' : ℝ≥0∞) < ζ ω} := by
      simpa using hWa q' univ MeasurableSet.univ
    have hA : MeasurableSet[usualAugmentation 𝓖 P q'] (F ∩ {ω | (q' : ℝ≥0∞) < ζ ω}) :=
      hle _ ((𝓖.mono zero_le _ (h0 _ hF)).inter hlt)
    have hjl := WangWu.ImgDrv.joint_law_restart hBvF hBvc q' hstm hA
      (Sec5.Prop49Exit.measurableSet_badSetS (a := a) (ρL := ρL) (ρR := ρR) hSm)
    have hzero : ∀ ω, wienerPath (Prod.mk (st ω) ⁻¹' Sec5.Prop49Exit.badSetS a ρL ρR S) = 0 := fun ω =>
      Sec5.Prop49Exit.wienerPath_badSetS_eq_zero ha hS (st ω)
    simp only [hzero, lintegral_zero] at hjl
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hjl
    simp only [mem_ofPred_eq, Classical.not_imp, not_not] at hω
    obtain ⟨hωF, hqζ, hbad⟩ := hω
    refine ⟨⟨hωF, hqζ⟩, ?_⟩
    have e : st ω = ((fun i => VL i q' ω - W q' ω), fun j => VR j q' ω - W q' ω) := by
      rw [hst]
      simp only [Girsanov.killed_of_lt hqζ]
    rw [mem_preimage, e]
    exact hbad
  filter_upwards [ae_all_iff.2 hall, hpath, hord, hBvae] with ω hgood hp hF' hb hωF q hq0 hqζ
  set q' : ℝ≥0 := (q : ℝ≥0) with hq'
  have hq0' : 0 < q' := NNRat.cast_pos.2 hq0
  have hpω := (hp hωF).congr_b (b := fun t => Bv t ω) fun t _ => hb t
  have hFω := hF' hωF
  set st : (Fin nL → ℝ) × (Fin nR → ℝ) := ((fun i => VL i q ω - W q ω), fun j => VR j q ω - W q ω) with hst
  have hsep : SepStart st := fun i j => sub_lt_sub_right (hpω.vL_lt_vR_of_pos hFω hq0' hqζ i j) _
  have hordst : IsOrderedForceWord st.1 st.2 :=
    ⟨fun i i' hii' => sub_le_sub_right (hpω.antitone_vL hqζ hii') _, fun i => sub_nonpos.2 (hpω.vL_le_w hqζ i),
      fun j j' hjj' => sub_le_sub_right (hpω.monotone_vR hqζ hjj') _, fun j => sub_nonneg.2 (hpω.w_le_vR hqζ j)⟩
  have hnot := hgood q hωF hqζ
  have hmem : (st, enc (QuantumZipper.StrongMarkov.smPath Bv (fun _ => q') ω)) ∈ lawSetS a ρL ρR S := by
    by_contra hn
    exact hnot ⟨hsep, hordst, hn⟩
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxe⟩ := hmem
  simp only [Prod.mk.injEq] at hxe
  have hxC : x ∈ CRel a st.1 st.2 ρL ρR := mem_cRelF_iff.1 ⟨hxF, hxe.1⟩
  have hxp : IsIntegratedSLEPath a st.1 st.2 ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  have hgc : Continuous (QuantumZipper.StrongMarkov.smPath Bv (fun _ => q') ω) :=
    ((hBvc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hcb : cb x = shiftAt q' (fun t => Bv t ω) (Bv q' ω) := by
    funext t
    show dec x.1 t = _
    rw [hxe.2, dec_enc_of_continuous hgc]
    rfl
  rw [hcb] at hxp
  have hsh := hpω.shift hqζ
  obtain ⟨hle', hag⟩ := Sec7.Band.le_lifetime_of_upTo hsep hsh hxp
  refine ⟨x, hxC, hxS, fun t => by rw [hcb]; simp only [shiftAt, hb], hle', fun t ht => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hag t ht
  exact ⟨e1.symm, fun i => (e2 i).symm, fun j => (e3 j).symm⟩

end InteractingSLE.ZhanGT4.A2ImgEnd
