/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalPath
import InteractingSLE.Spec.Sec2.AddMarksPath
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# Deleting zero-weight marks from an integrated `SLE_a(ρ)` evolution (§4.1)

Packet PROVE-SEC4-A4, item (1) (`planning/handoffs/PROVE-SEC4-A3.md`, obstruction 4). The frozen flow-line force
word keeps its seed marks `0⁻`, `0⁺` even when their weight is `0` (`flowLineRhoL`: "The seed mark is kept even when
its weight is `0` (passive mark)"). The proofs of Lemma 4.3 and Lemma 4.5 (`source/spec/p097-144.md#lem-4.3-proof`)
use words without such marks: "In the basic figure the lower lists are empty." The equations of Definition 2.1 do not
involve a zero weight, so a mark of weight `0` can be deleted:

* `IsIntegratedSLEPath.compEmb` (**deletion, pathwise**): if every mark outside the images of order embeddings
  `eL : Fin mL ↪o Fin nL`, `eR : Fin mR ↪o Fin nR` has weight `0`, the sub-tuple `(w, v^L ∘ eL, v^R ∘ eR, b)` is an
  integrated path of the sub-word, with the same driver, driving path and lifetime;
* `IsIntegratedSLEEvolution.compEmb` (**deletion**): the same for evolutions (same filtration, `W`, `B`, `ζ`);
* `isIntegratedSLEPath_iff_compEmb` / `isIntegratedSLEEvolution_iff_compEmb` (**converse**): the full tuple is an
  integrated path (evolution) exactly when the sub-tuple is one and the full tuple satisfies the equations of
  Definition 2.1 before `ζ` (`Sec2.IsSLEPathUpTo`, and adaptedness of the deleted coordinates): the deleted marks
  never change the continuation threshold;
* `Sec2.IsForcePath.exists_tendsto_vL` / `exists_tendsto_vR`: at a finite lifetime every force coordinate has a
  left limit as soon as the driver has one (each coordinate is monotone, and the barrier `v_t ≥ min(x, m − 1) − 2t`
  bounds it). This is what makes the maximality clause of Definition 2.1 survive the deletion.

Only the maximality clause `threshold_of_tendsto` needs an argument: a limit of the sub-state at `ζ⁻` extends to a
limit of the full state (the deleted coordinates converge), whose threshold condition is that of the sub-state
(zero weights do not change the colliding sums).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec4

/-! ### Sums over a sub-word -/

/-- If `f` vanishes off the range of the embedding `e`, a filtered sum of `f` is the filtered sum over the
sub-word. -/
theorem sum_filter_comp_embedding {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → ℝ) (hf : ∀ i, i ∉ Set.range e → f i = 0) (p : Fin n → Prop) [DecidablePred p] :
    ∑ j ∈ Finset.univ.filter (fun j => p (e j)), f (e j) = ∑ i ∈ Finset.univ.filter p, f i := by
  have hmap := Finset.sum_map (Finset.univ.filter fun j => p (e j)) ⟨e, he⟩ f
  simp only [Function.Embedding.coeFn_mk] at hmap
  rw [← hmap]
  apply Finset.sum_subset
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hj).2⟩
  · intro i hi hni
    apply hf
    rintro ⟨j, rfl⟩
    exact hni (Finset.mem_map.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (Finset.mem_filter.1 hi).2⟩, rfl⟩)

/-- If `f` vanishes off the range of the embedding `e`, its sum is the sum over the sub-word. -/
theorem sum_comp_embedding {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → ℝ) (hf : ∀ i, i ∉ Set.range e → f i = 0) : ∑ j, f (e j) = ∑ i, f i := by
  have h := sum_filter_comp_embedding e he f hf (fun _ => True)
  simpa using h

/-- **Zero weights do not change the continuation threshold**: the threshold condition of the sub-word at the
sub-state is that of the full word at the full state. -/
theorem thresholdCondition_compEmb_iff {mL mR nL nR : ℕ} {eL : Fin mL → Fin nL}
    {eR : Fin mR → Fin nR} (heL : Function.Injective eL) (heR : Function.Injective eR)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hL : ∀ i, i ∉ Set.range eL → ρL i = 0) (hR : ∀ i, i ∉ Set.range eR → ρR i = 0) (w : ℝ)
    (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition (fun j => ρL (eL j)) (fun j => ρR (eR j)) w (fun j => vL (eL j))
        (fun j => vR (eR j)) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  unfold ForceWord.ThresholdCondition
  rw [sum_filter_comp_embedding eL heL ρL hL (fun i => vL i = w),
    sum_filter_comp_embedding eR heR ρR hR (fun i => vR i = w)]

end Sec4

/-! ### Limits of the force coordinates at a finite lifetime -/

namespace Sec2

/-- A function continuous on `[0, T)` with a left limit at `T > 0` is bounded below on `[0, T)`. -/
theorem bddBelow_image_Iio_of_tendsto {f : ℝ≥0 → ℝ} {T : ℝ≥0} (hT : 0 < T)
    (hf : ContinuousOn f (Iio T)) {l : ℝ} (hl : Tendsto f (𝓝[<] T) (𝓝 l)) :
    BddBelow (f '' Iio T) := by
  have hev : ∀ᶠ t in 𝓝[<] T, l - 1 < f t := hl.eventually (lt_mem_nhds (by linarith))
  obtain ⟨a, haT, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT).1 hev
  have hcont : ContinuousOn f (Icc 0 a) := hf.mono fun t ht => lt_of_le_of_lt ht.2 haT
  obtain ⟨m, hm⟩ := isCompact_Icc.bddBelow_image hcont
  refine ⟨min m (l - 1), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rcases le_or_gt t a with hta | hta
  · exact (min_le_left _ _).trans (hm ⟨t, ⟨zero_le, hta⟩, rfl⟩)
  · exact (min_le_right _ _).trans (hsub ⟨hta, ht⟩).le

namespace IsForcePath

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Barrier for a left force coordinate.** If the driver is at least `m` before `ζ`, then
`v^{i,L}_t ≥ min(x^{i,L}, m − 1) − 2t` for `t < ζ`: after the last time `s₀ ≤ t` at which `v ≥ min(x, m − 1)`, the
gap `w − v` exceeds `1`, so `v` decreases at rate at most `2`. -/
theorem le_vL_of_le_w (h : IsForcePath xL xR ρL ρR w vL vR ζ) {m : ℝ}
    (hm : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → m ≤ w t) (i : Fin nL) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : min (xL i) (m - 1) - 2 * t ≤ vL i t := by
  set c := min (xL i) (m - 1) with hc
  set S : Set ℝ≥0 := Icc 0 t ∩ vL i ⁻¹' Ici c with hS
  have hsub : Icc 0 t ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs.2) ht
  have hS0 : (0 : ℝ≥0) ∈ S :=
    ⟨⟨le_rfl, zero_le⟩, by simp only [mem_preimage, mem_Ici, h.vL_zero i, hc, min_le_left]⟩
  have hScl : IsClosed S :=
    ((h.continuousOn_vL i).mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
  set s₀ := sSup S with hs₀def
  have hs₀ : s₀ ∈ S := hSc.sSup_mem ⟨0, hS0⟩
  have hs₀t : s₀ ≤ t := hs₀.1.2
  have hgt : ∀ r ∈ Ioo (s₀ : ℝ) t, (fun _ : ℝ => (-2 : ℝ)) r ≤
      (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) r := by
    intro r hr
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg _).trans hr.1.le
    have hrt : r.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal r hr0]; exact hr.2.le
    have hrs : s₀ < r.toNNReal := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal r hr0]; exact hr.1
    have hnot : r.toNNReal ∉ S := fun hmem => not_le.2 hrs (le_csSup hSc.bddAbove hmem)
    have hv : vL i r.toNNReal < c := by
      by_contra hcon
      exact hnot ⟨⟨zero_le, hrt⟩, not_lt.1 hcon⟩
    have hw := hm _ (hsub ⟨zero_le, hrt⟩)
    have hcm : c ≤ m - 1 := min_le_right _ _
    have hgap : 1 < w r.toNNReal - vL i r.toNNReal := by linarith
    have hneg : vL i r.toNNReal - w r.toNNReal = -(w r.toNNReal - vL i r.toNNReal) := by ring
    have h2 : 2 / (w r.toNNReal - vL i r.toNNReal) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    show -2 ≤ 2 / (vL i r.toNNReal - w r.toNNReal)
    rw [hneg, div_neg]
    linarith
  have hint : IntervalIntegrable (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) volume s₀ t :=
    (h.intervalIntegrable_forceL ht i).mono_set (by
      rw [uIcc_of_le (by exact_mod_cast hs₀t), uIcc_of_le (NNReal.coe_nonneg t)]
      exact Icc_subset_Icc (NNReal.coe_nonneg s₀) le_rfl)
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
    (by exact_mod_cast hs₀t : (s₀ : ℝ) ≤ t) intervalIntegrable_const hint hgt
  rw [intervalIntegral.integral_const, ← h.vL_sub hs₀t ht i, smul_eq_mul] at hle
  have hc₀ : c ≤ vL i s₀ := hs₀.2
  have hs₀0 : (0 : ℝ) ≤ s₀ := NNReal.coe_nonneg _
  linarith

/-- **A left force coordinate has a limit at a finite lifetime** when the driver has one: it is nonincreasing
(`antitoneOn_vL`) and bounded below (`le_vL_of_le_w`). -/
theorem exists_tendsto_vL (h : IsForcePath xL xR ρL ρR w vL vR ζ) {T : ℝ≥0} (hT : 0 < T)
    (hTζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} (hw : Tendsto w (𝓝[<] T) (𝓝 w₀)) (i : Fin nL) :
    ∃ l, Tendsto (vL i) (𝓝[<] T) (𝓝 l) := by
  have hIio : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} = Iio T := by
    ext t
    show (t : ℝ≥0∞) < ζ ↔ t < T
    rw [← hTζ]
    exact ENNReal.coe_lt_coe
  have hwc : ContinuousOn w (Iio T) := hIio ▸ h.continuousOn_w
  obtain ⟨m, hm⟩ := bddBelow_image_Iio_of_tendsto hT hwc hw
  have hm' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → m ≤ w t := fun t ht =>
    hm ⟨t, by rw [← hIio]; exact ht, rfl⟩
  have hanti : AntitoneOn (vL i) (Iio T) := hIio ▸ h.antitoneOn_vL i
  have hbdd : BddBelow (vL i '' Iio T) := by
    refine ⟨min (xL i) (m - 1) - 2 * T, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have htζ : (t : ℝ≥0∞) < ζ := by rw [← hTζ]; exact_mod_cast ht
    have hle := h.le_vL_of_le_w hm' i htζ
    have htT : (t : ℝ) ≤ T := by exact_mod_cast (mem_Iio.1 ht).le
    linarith
  exact ⟨_, hanti.tendsto_nhdsLT hbdd⟩

/-- **A right force coordinate has a limit at a finite lifetime** when the driver has one (reflection of
`exists_tendsto_vL`). -/
theorem exists_tendsto_vR (h : IsForcePath xL xR ρL ρR w vL vR ζ) {T : ℝ≥0} (hT : 0 < T)
    (hTζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} (hw : Tendsto w (𝓝[<] T) (𝓝 w₀)) (i : Fin nR) :
    ∃ l, Tendsto (vR i) (𝓝[<] T) (𝓝 l) := by
  obtain ⟨l, hl⟩ := h.reflect.exists_tendsto_vL hT hTζ (w₀ := -w₀) hw.neg i
  refine ⟨-l, ?_⟩
  simpa only [Pi.neg_apply, neg_neg] using hl.neg

end IsForcePath

end Sec2

/-! ### Deleting zero-weight marks -/

open Sec4

section Deletion

variable {a : ℝ} {nL nR mL mR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- **Deleting zero-weight marks, pathwise.** If every left mark outside the image of the order embedding `eL` and
every right mark outside the image of `eR` has weight `0`, the sub-tuple is an integrated path of the sub-word with
the same driver, driving path and lifetime. The equations of Definition 2.1 do not involve a zero weight; at a finite
lifetime a limit of the sub-state extends to a limit of the full state (`exists_tendsto_vL`, `exists_tendsto_vR`),
whose threshold condition is the same. -/
theorem IsIntegratedSLEPath.compEmb {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (eL : Fin mL ↪o Fin nL) (eR : Fin mR ↪o Fin nR) (hL : ∀ i, i ∉ Set.range eL → ρL i = 0)
    (hR : ∀ i, i ∉ Set.range eR → ρR i = 0) :
    IsIntegratedSLEPath a (fun j => xL (eL j)) (fun j => xR (eR j)) (fun j => ρL (eL j))
      (fun j => ρR (eR j)) w (fun j => vL (eL j)) (fun j => vR (eR j)) b ζ := by
  have hfp := hp.isForcePath
  obtain ⟨hw0, hvL0, hvR0, hwc, hvLc, hvRc, hantiL, hvLw, hwvR, hmonoR, hgL, hgR, hweq, hvLeq,
    hvReq, hcolL, hcolR, hnt, hth0, hthT⟩ := hp
  refine ⟨hw0, fun j => hvL0 _, fun j => hvR0 _, hwc, fun j => hvLc _, fun j => hvRc _,
    fun t ht => (hantiL t ht).comp_monotone eL.monotone, fun t ht j => hvLw t ht _,
    fun t ht j => hwvR t ht _, fun t ht => (hmonoR t ht).comp eR.monotone,
    fun t ht j => hgL t ht _, fun t ht j => hgR t ht _, fun t ht => ?_, fun t ht j => hvLeq t ht _,
    fun t ht j => hvReq t ht _, fun j => hcolL _, fun j => hcolR _, fun t ht hth => ?_,
    fun h0 => ?_, fun T hT hTζ w₀ vL₀ vR₀ hlim => ?_⟩
  · have e1 := sum_comp_embedding eL eL.injective
      (fun i => ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      (fun i hi => by simp [hL i hi])
    have e2 := sum_comp_embedding eR eR.injective
      (fun i => ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal))
      (fun i hi => by simp [hR i hi])
    rw [hweq t ht, e1, e2]
  · exact hnt t ht ((thresholdCondition_compEmb_iff eL.injective eR.injective hL hR (w t)
      (fun i => vL i t) (fun i => vR i t)).1 hth)
  · exact (thresholdCondition_compEmb_iff eL.injective eR.injective hL hR 0 xL xR).2 (hth0 h0)
  · have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
    choose lL hlL using fun i => hfp.exists_tendsto_vL hT hTζ hw i
    choose lR hlR using fun i => hfp.exists_tendsto_vR hT hTζ hw i
    have hfull : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
        (𝓝 (w₀, lL, lR)) :=
      hw.prodMk_nhds ((tendsto_pi_nhds.2 hlL).prodMk_nhds (tendsto_pi_nhds.2 hlR))
    have hne : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
    have hL' : vL₀ = fun j => lL (eL j) := by
      funext j
      have h1 : Tendsto (fun t => vL (eL j) t) (𝓝[<] T) (𝓝 (vL₀ j)) :=
        ((continuous_apply j).tendsto _).comp
          (((continuous_fst.comp continuous_snd).tendsto _).comp hlim)
      exact tendsto_nhds_unique h1 (hlL (eL j))
    have hR' : vR₀ = fun j => lR (eR j) := by
      funext j
      have h1 : Tendsto (fun t => vR (eR j) t) (𝓝[<] T) (𝓝 (vR₀ j)) :=
        ((continuous_apply j).tendsto _).comp
          (((continuous_snd.comp continuous_snd).tendsto _).comp hlim)
      exact tendsto_nhds_unique h1 (hlR (eR j))
    rw [hL', hR']
    exact (thresholdCondition_compEmb_iff eL.injective eR.injective hL hR w₀ lL lR).2
      (hthT T hT hTζ w₀ lL lR hfull)

/-- **Converse of the deletion, pathwise.** The full tuple is an integrated path exactly when it satisfies the
equations of Definition 2.1 before `ζ` and the sub-tuple of the nonzero-weight marks is an integrated path (with its
maximality clauses): the zero-weight marks never change the continuation threshold. -/
theorem isIntegratedSLEPath_iff_compEmb {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (eL : Fin mL ↪o Fin nL)
    (eR : Fin mR ↪o Fin nR) (hL : ∀ i, i ∉ Set.range eL → ρL i = 0)
    (hR : ∀ i, i ∉ Set.range eR → ρR i = 0) :
    IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ ↔
      Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ ∧
        IsIntegratedSLEPath a (fun j => xL (eL j)) (fun j => xR (eR j)) (fun j => ρL (eL j))
          (fun j => ρR (eR j)) w (fun j => vL (eL j)) (fun j => vR (eR j)) b ζ := by
  refine ⟨fun hp => ⟨hp.isSLEPathUpTo le_rfl, hp.compEmb eL eR hL hR⟩, fun ⟨hu, hp'⟩ => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hth0, hthT⟩ := hp'
  have hcont : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
      (p.1, fun j => p.2.1 (eL j), fun j => p.2.2 (eR j)) := by fun_prop
  exact ⟨hu.w_zero, hu.vL_zero, hu.vR_zero, hu.continuousOn_w, hu.continuousOn_vL,
    hu.continuousOn_vR, fun t ht => hu.antitone_vL ht, fun t ht => hu.vL_le_w ht,
    fun t ht => hu.w_le_vR ht, fun t ht => hu.monotone_vR ht, fun t ht => hu.integrable_gapL ht,
    fun t ht => hu.integrable_gapR ht, fun t ht => hu.w_eq ht, fun t ht => hu.vL_eq ht,
    fun t ht => hu.vR_eq ht, hu.volume_collisionL, hu.volume_collisionR,
    fun t ht => hu.not_threshold ht,
    fun h0 => (thresholdCondition_compEmb_iff eL.injective eR.injective hL hR 0 xL xR).1 (hth0 h0),
    fun T hT hTζ w₀ vL₀ vR₀ hlim =>
      (thresholdCondition_compEmb_iff eL.injective eR.injective hL hR w₀ vL₀ vR₀).1
        (hthT T hT hTζ w₀ _ _ ((hcont.tendsto _).comp hlim))⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Deleting zero-weight marks from an evolution.** If every mark outside the images of the order embeddings
`eL`, `eR` has weight `0`, the sub-tuple is an integrated `SLE_a(ρ)` evolution of the sub-word on the same filtered
probability space, with the same driver `W`, Brownian motion `B` and lifetime `ζ`. -/
theorem IsIntegratedSLEEvolution.compEmb (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (eL : Fin mL ↪o Fin nL) (eR : Fin mR ↪o Fin nR) (hL : ∀ i, i ∉ Set.range eL → ρL i = 0)
    (hR : ∀ i, i ∉ Set.range eR → ρR i = 0) :
    IsIntegratedSLEEvolution a (fun j => xL (eL j)) (fun j => xR (eR j)) (fun j => ρL (eL j))
      (fun j => ρR (eR j)) P 𝓕 W (fun j => VL (eL j)) (fun j => VR (eR j)) B ζ := by
  refine ⟨h.1, h.2.1, fun j => h.2.2.1 _, fun j => h.2.2.2.1 _, ?_⟩
  filter_upwards [h.2.2.2.2] with ω hω
  exact hω.compEmb eL eR hL hR

/-- **Converse of the deletion for evolutions.** The full tuple is an integrated evolution exactly when the
sub-tuple of the nonzero-weight marks is one, the deleted coordinates are adapted before `ζ`, and almost surely the
full tuple satisfies the equations of Definition 2.1 before `ζ`. -/
theorem isIntegratedSLEEvolution_iff_compEmb (eL : Fin mL ↪o Fin nL) (eR : Fin mR ↪o Fin nR)
    (hL : ∀ i, i ∉ Set.range eL → ρL i = 0) (hR : ∀ i, i ∉ Set.range eR → ρR i = 0) :
    IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ ↔
      IsIntegratedSLEEvolution a (fun j => xL (eL j)) (fun j => xR (eR j)) (fun j => ρL (eL j))
          (fun j => ρR (eR j)) P 𝓕 W (fun j => VL (eL j)) (fun j => VR (eR j)) B ζ ∧
        (∀ i, AdaptedBefore 𝓕 ζ (VL i)) ∧ (∀ i, AdaptedBefore 𝓕 ζ (VR i)) ∧
        ∀ᵐ ω ∂P, Sec2.IsSLEPathUpTo a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) := by
  refine ⟨fun h => ⟨h.compEmb eL eR hL hR, h.2.2.1, h.2.2.2.1, ?_⟩, fun ⟨h', hVL, hVR, hu⟩ => ?_⟩
  · filter_upwards [h.2.2.2.2] with ω hω
    exact hω.isSLEPathUpTo le_rfl
  · refine ⟨h'.1, h'.2.1, hVL, hVR, ?_⟩
    filter_upwards [h'.2.2.2.2, hu] with ω hω hu
    exact (isIntegratedSLEPath_iff_compEmb eL eR hL hR).2 ⟨hu, hω⟩

/-- A sub-word of an ordered force word (along order embeddings) is ordered. -/
theorem IsOrderedForceWord.compEmb (hword : IsOrderedForceWord xL xR) (eL : Fin mL ↪o Fin nL)
    (eR : Fin mR ↪o Fin nR) : IsOrderedForceWord (fun j => xL (eL j)) (fun j => xR (eR j)) :=
  ⟨hword.1.comp_monotone eL.monotone, fun _ => hword.2.1 _, hword.2.2.1.comp eR.monotone,
    fun _ => hword.2.2.2 _⟩

end Deletion

/-! ### The nonzero-weight sub-word -/

namespace Sec4

/-- The marks of nonzero weight of one side, in increasing index order. -/
def nonzeroEmb {n : ℕ} (ρ : Fin n → ℝ) :
    Fin (Finset.univ.filter fun i => ρ i ≠ 0).card ↪o Fin n :=
  (Finset.univ.filter fun i => ρ i ≠ 0).orderEmbOfFin rfl

theorem range_nonzeroEmb {n : ℕ} (ρ : Fin n → ℝ) : Set.range (nonzeroEmb ρ) = {i | ρ i ≠ 0} := by
  rw [nonzeroEmb, Finset.range_orderEmbOfFin]
  ext i
  simp

theorem eq_zero_of_notMem_range_nonzeroEmb {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n}
    (hi : i ∉ Set.range (nonzeroEmb ρ)) : ρ i = 0 := by
  rw [range_nonzeroEmb] at hi
  simpa using hi

theorem nonzero_nonzeroEmb {n : ℕ} (ρ : Fin n → ℝ) (j : Fin (Finset.univ.filter fun i => ρ i ≠ 0).card) :
    ρ (nonzeroEmb ρ j) ≠ 0 := by
  have : nonzeroEmb ρ j ∈ Set.range (nonzeroEmb ρ) := ⟨j, rfl⟩
  rw [range_nonzeroEmb] at this
  exact this

theorem exists_nonzeroEmb_eq {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n} (hi : ρ i ≠ 0) :
    ∃ j, nonzeroEmb ρ j = i := by
  have : i ∈ Set.range (nonzeroEmb ρ) := by rw [range_nonzeroEmb]; exact hi
  exact this

end Sec4

/-- **Deleting every zero-weight mark** of an evolution: the marks of nonzero weight form an integrated evolution of
their sub-word, with the same `W`, `B` and `ζ`. -/
theorem IsIntegratedSLEEvolution.dropZero {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution a (fun j => xL (Sec4.nonzeroEmb ρL j)) (fun j => xR (Sec4.nonzeroEmb ρR j))
      (fun j => ρL (Sec4.nonzeroEmb ρL j)) (fun j => ρR (Sec4.nonzeroEmb ρR j)) P 𝓕 W
      (fun j => VL (Sec4.nonzeroEmb ρL j)) (fun j => VR (Sec4.nonzeroEmb ρR j)) B ζ :=
  h.compEmb _ _ (fun _ hi => Sec4.eq_zero_of_notMem_range_nonzeroEmb hi)
    (fun _ hi => Sec4.eq_zero_of_notMem_range_nonzeroEmb hi)

end InteractingSLE
