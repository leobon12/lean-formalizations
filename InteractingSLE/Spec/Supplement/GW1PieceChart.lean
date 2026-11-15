/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Sec7.ContinuityProb2Join

/-!
# GW1's properness, deterministic part: the tip set of a regular piece in a good chart is closed

Packet PROVE-T14-GW1P. Lemma GW1 (supplement p. 618: "a field-determined continuous injective proper curve `R`")
gives each ordinary piece of a boundary walk as a continuous proper curve; its physical set is then closed. On the
frozen carriers the physical points of a piece are the radial limits `Chart.tipSet`, read through the chart `c` of
the domain in which the piece was launched. This file proves the deterministic half:

* `PieceRegular W S` — the data Theorem 1.3 supplies for a piece run up to its stop `S`: `W 0 = 0`, `W` continuous
  on `[0, S]`, a continuous generating trace on `[0, S]`, transient when `S = ∞`;
* `HasProperBdryExt c` — the chart inverse `c.inv` has a limit from inside `ℍ` at every point of `ℍ̄`, and the
  limit map stays within bounded distance of the identity (so it is continuous on `ℍ̄` and proper);
* `hasProperBdryExt_recenter_id`, `HasProperBdryExt.recenter`, `HasProperBdryExt.loewner_stopped` — the charts of
  a staged history (identity, real recentring, the Loewner chart after a regular piece stopped at a finite time) are
  good; the Loewner step uses the trace-closure fact (`TraceClose.hasBdryLimits_of_isLoewnerTraceLT`) and the
  hydrodynamic bound `‖F_T(w) − w‖ ≤ C` (`exists_norm_fwdMapInv_sub_le`);
* **`isClosed_tipSet`** — the tip set of a regular piece in a good chart is closed: it is `f(α([0, S]))`
  (`CounterflowRange.tipSet_stopped_eq_of_tendsto`), compact for finite `S`, and for `S = ∞` closed because `α` is
  transient and `f` moves points by at most `C`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE

namespace Theorem14

namespace GW1P

open CounterflowRange

/-- **Regular data of an ordinary piece run up to its stop `S`** (what Theorem 1.3 and Aux. lemma 3 supply for a
flow-line driver): `W 0 = 0`, `W` continuous on `[0, S]`, and a continuous generating trace on `[0, S]`, transient
when `S = ∞`. -/
def PieceRegular (W : ℝ≥0 → ℝ) (S : ℝ≥0∞) : Prop :=
  W 0 = 0 ∧ ContinuousOn W {t | (t : ℝ≥0∞) ≤ S} ∧
    ∃ α : ℝ≥0 → ℂ, IsGeneratingTrace W S α ∧ (S = ⊤ → Tendsto (fun t => ‖α t‖) atTop atTop)

/-- **A good chart**: its inverse has a limit `f p` from inside `ℍ` at every `p ∈ ℍ̄`, and `f` stays within bounded
distance of the identity on `ℍ̄`. -/
def HasProperBdryExt (c : Chart) : Prop :=
  ∃ (f : ℂ → ℂ) (C : ℝ), (∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) ∧ ∀ p ∈ Hbar, ‖f p - p‖ ≤ C

/-- Points of `ℍ̄` are limits of `ℍ`. -/
theorem neBot_nhdsWithin_H {p : ℂ} (hp : p ∈ Hbar) : (𝓝[H] p).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hp)

/-- A boundary-limit map is continuous on `ℍ̄`. -/
theorem continuousOn_of_tendsto {g f : ℂ → ℂ} (hg : ∀ p ∈ Hbar, Tendsto g (𝓝[H] p) (𝓝 (f p))) :
    ContinuousOn f Hbar := by
  have hB : HasBdryLimits g := fun p hp => ⟨f p, hg p hp⟩
  refine hB.continuousOn.congr fun p hp => ?_
  have := neBot_nhdsWithin_H hp
  exact tendsto_nhds_unique (hg p hp) (hB.tendsto hp)

/-- A limit, from inside `ℍ`, of a map sending `ℍ` into `ℍ` lies in `ℍ̄`. -/
theorem mem_Hbar_of_tendsto {g : ℂ → ℂ} {p q : ℂ} (hp : p ∈ Hbar) (hgH : ∀ z ∈ H, g z ∈ H)
    (hg : Tendsto g (𝓝[H] p) (𝓝 q)) : q ∈ Hbar := by
  have := neBot_nhdsWithin_H hp
  refine QuantumZipper.isClosed_Hbar.mem_of_tendsto hg ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (show 0 < (g z).im from hgH z hz).le

/-! ### The charts of a staged history are good -/

/-- The recentred identity chart is good. -/
theorem hasProperBdryExt_recenter_id (x : ℝ) : HasProperBdryExt (Chart.id.recenter x) := by
  refine ⟨fun z => z + (x : ℂ), |x|, fun p _ => ?_, fun p _ => ?_⟩
  · rw [recenter_id_inv]
    exact ((continuous_id.add continuous_const).tendsto p).mono_left nhdsWithin_le_nhds
  · simp

/-- Real recentring keeps a chart good. -/
theorem HasProperBdryExt.recenter {c : Chart} (hc : HasProperBdryExt c) (a : ℝ) :
    HasProperBdryExt (c.recenter a) := by
  obtain ⟨f, C, hf, hC⟩ := hc
  have hmem : ∀ p ∈ Hbar, p + (a : ℂ) ∈ Hbar := fun p hp => by
    have hp' : 0 ≤ p.im := hp
    show 0 ≤ (p + (a : ℂ)).im
    simpa using hp'
  refine ⟨fun p => f (p + (a : ℂ)), C + |a|, fun p hp => ?_, fun p hp => ?_⟩
  · have hT : Tendsto (fun z : ℂ => z + (a : ℂ)) (𝓝[H] p) (𝓝[H] (p + (a : ℂ))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((continuous_id.add continuous_const).tendsto p).mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : 0 < z.im := hz
      show 0 < (z + (a : ℂ)).im
      simpa using hz'
    exact (hf _ (hmem p hp)).comp hT
  · calc ‖f (p + (a : ℂ)) - p‖ = ‖(f (p + (a : ℂ)) - (p + (a : ℂ))) + (a : ℂ)‖ := by ring_nf
      _ ≤ ‖f (p + (a : ℂ)) - (p + (a : ℂ))‖ + ‖(a : ℂ)‖ := norm_add_le _ _
      _ ≤ C + |a| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith [hC _ (hmem p hp)]

/-- **A Loewner step keeps a chart good** when `F_T` has boundary limits on `ℍ̄`. -/
theorem HasProperBdryExt.loewner {c : Chart} (hc : HasProperBdryExt c) {W : ℝ → ℝ} {T : ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (hT : 0 ≤ T) (hB : HasBdryLimits (fwdMapInv W T)) : HasProperBdryExt (c.loewner W T) := by
  obtain ⟨f, C, hf, hC⟩ := hc
  obtain ⟨CF, hCF⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hT
  set F : ℂ → ℂ := extendFrom H (fwdMapInv W T) with hFdef
  have hFH : ∀ z ∈ H, fwdMapInv W T z ∈ H := fun z hz => QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hT hz
  have hFmem : ∀ p ∈ Hbar, F p ∈ Hbar := fun p hp => mem_Hbar_of_tendsto hp hFH (hB.tendsto hp)
  refine ⟨fun p => f (F p), C + CF, fun p hp => ?_, fun p hp => ?_⟩
  · exact tendsto_loewner_inv hW hW0 hT (hB.tendsto hp) (hf _ (hFmem p hp))
  · have hle : ‖F p - p‖ ≤ CF := by
      have := neBot_nhdsWithin_H hp
      have hlim : Tendsto (fun z => ‖fwdMapInv W T z - z‖) (𝓝[H] p) (𝓝 ‖F p - p‖) :=
        ((hB.tendsto hp).sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm
      refine le_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hCF z hz
    calc ‖f (F p) - p‖ = ‖(f (F p) - F p) + (F p - p)‖ := by ring_nf
      _ ≤ ‖f (F p) - F p‖ + ‖F p - p‖ := norm_add_le _ _
      _ ≤ C + CF := add_le_add (hC _ (hFmem p hp)) hle

/-- The driver of a regular piece stopped at its stop, read on `ℝ`, is continuous and starts at `0`. -/
theorem PieceRegular.continuous_stoppedReal {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} (h : PieceRegular W S) :
    Continuous (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) ∧
      (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) 0 = 0 := by
  refine ⟨(continuous_stopped h.2.1).comp continuous_real_toNNReal, ?_⟩
  have h0 : W (min ((0 : ℝ≥0) : ℝ≥0∞) S).toNNReal = 0 := by
    rw [stopped_eq_of_lt (W := W) (t := 0) (by simp), h.1]
  simpa using h0

/-- **The inverse Loewner map after a regular piece stopped at a finite time has boundary limits on `ℍ̄`**
(trace closure, PROVE-TRACECLOSE; at a zero stop the map is the identity on `ℍ`). -/
theorem PieceRegular.hasBdryLimits {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} (h : PieceRegular W S) (hS : S ≠ ⊤) :
    HasBdryLimits (fwdMapInv (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal)
      ((S.toNNReal : ℝ≥0) : ℝ)) := by
  obtain ⟨hU, hU0⟩ := h.continuous_stoppedReal
  obtain ⟨-, hWc, α, hα, -⟩ := h
  set S' : ℝ≥0 := S.toNNReal with hS'
  have hSS : (S' : ℝ≥0∞) = S := ENNReal.coe_toNNReal hS
  rcases eq_or_ne S' 0 with h0 | hpos
  · intro p hp
    refine ⟨p, ?_⟩
    rw [h0, NNReal.coe_zero]
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (fwdMapInv_zero_time hU hU0 hz).symm
  · rw [← hSS] at hα hWc
    have hU' : (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) =
        fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (S' : ℝ≥0∞)).toNNReal := by
      rw [hSS]
    rw [hU'] at hU hU0 ⊢
    have hη := isLoewnerTraceLT_of_isGeneratingTrace (isGeneratingTrace_stopped hα)
    have hησ : ContinuousOn (fun s : ℝ => α s.toNNReal) (Icc 0 (S' : ℝ)) :=
      hα.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
        ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    exact TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hU hU0 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hpos))
      hησ

/-- **The chart after a regular piece stopped at a finite time is good.** -/
theorem HasProperBdryExt.loewner_stopped {c : Chart} (hc : HasProperBdryExt c) {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (h : PieceRegular W S) (hS : S ≠ ⊤) :
    HasProperBdryExt (c.loewner (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal)
      ((S.toNNReal : ℝ≥0) : ℝ)) :=
  hc.loewner h.continuous_stoppedReal.1 h.continuous_stoppedReal.2 (NNReal.coe_nonneg _) (h.hasBdryLimits hS)

/-! ### The tip set of a regular piece is closed -/

/-- **The tip set of a regular piece read in a good chart is closed**: it is `f(α([0, S]))`, compact for a finite
stop; for an infinite stop, the transient trace leaves every ball and `f` moves points by at most `C`, so near any
point only a compact time interval contributes. -/
theorem isClosed_tipSet {c : Chart} (hc : HasProperBdryExt c) {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} (h : PieceRegular W S) :
    IsClosed (c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S) := by
  obtain ⟨f, C, hf, hC⟩ := hc
  obtain ⟨hW0, hWc, α, hα, htr⟩ := h
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 ht
  rw [tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht)]
  have hfc : ContinuousOn f Hbar := continuousOn_of_tendsto hf
  -- the image of a compact time interval is compact
  have hcpt : ∀ T : ℝ≥0, (T : ℝ≥0∞) ≤ S → IsCompact (f '' (α '' Icc 0 T)) := fun T hT => by
    have hαc : ContinuousOn α (Icc 0 T) := hα.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hT
    refine (isCompact_Icc.image_of_continuousOn hαc).image_of_continuousOn (hfc.mono ?_)
    rintro _ ⟨s, hs, rfl⟩
    exact hαH s ((ENNReal.coe_le_coe.2 hs.2).trans hT)
  rcases eq_or_ne S ⊤ with hS | hS
  · subst hS
    have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ := eq_univ_of_forall fun t => (le_top : (t : ℝ≥0∞) ≤ ⊤)
    rw [hset]
    refine isClosed_of_closure_subset fun z hz => ?_
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((htr rfl).eventually_ge_atTop (‖z‖ + C + 1))
    have hsub : f '' (α '' univ) ⊆ f '' (α '' Icc 0 T₀) ∪ {w : ℂ | ‖z‖ + 1 ≤ ‖w‖} := by
      rintro _ ⟨_, ⟨t, -, rfl⟩, rfl⟩
      rcases le_total t T₀ with htT | htT
      · exact Or.inl ⟨α t, ⟨t, ⟨zero_le, htT⟩, rfl⟩, rfl⟩
      · right
        have h1 := hT₀ t htT
        have h2 := hC (α t) (hαH t le_top)
        have h3 := norm_sub_norm_le (α t) (f (α t))
        rw [norm_sub_rev] at h3
        show ‖z‖ + 1 ≤ ‖f (α t)‖
        linarith
    have hcl : IsClosed (f '' (α '' Icc 0 T₀) ∪ {w : ℂ | ‖z‖ + 1 ≤ ‖w‖}) :=
      (hcpt T₀ le_top).isClosed.union (isClosed_le continuous_const continuous_norm)
    rcases closure_minimal hsub hcl hz with hz' | hz'
    · exact image_mono (image_mono (subset_univ _)) hz'
    · exact absurd (show ‖z‖ + 1 ≤ ‖z‖ from hz') (by linarith)
  · have hSS : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) = S := ENNReal.coe_toNNReal hS
    have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} = Icc 0 S.toNNReal := by
      ext t
      constructor
      · intro ht
        refine ⟨zero_le, ?_⟩
        have ht' : (t : ℝ≥0∞) ≤ S := ht
        rwa [← hSS, ENNReal.coe_le_coe] at ht'
      · rintro ⟨-, ht⟩
        show (t : ℝ≥0∞) ≤ S
        rw [← hSS]
        exact ENNReal.coe_le_coe.2 ht
    rw [hset]
    exact (hcpt _ hSS.le).isClosed

/-- A closed set is relatively closed in `ℍ`. -/
theorem closure_inter_H_subset_of_isClosed {A : Set ℂ} (hA : IsClosed A) : closure A ∩ H ⊆ A := fun _ hz =>
  hA.closure_subset hz.1

end GW1P

end Theorem14

end InteractingSLE
