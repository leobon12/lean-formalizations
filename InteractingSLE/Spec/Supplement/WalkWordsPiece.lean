/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsAccess
import InteractingSLE.Spec.Sec7.ReverseArcModel
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Supplement.GB6Past
import InteractingSLE.Foundations.Loewner.YuanSimpleApproxTrans

/-!
# A recorded simple piece as a parametrized arc with a Loewner model

Packet PROVE-WALK-WORDS (the chronology-free fields of `WalkPairArcDataStatement`). `PieceData pc A f W α` bundles
the facts about a recorded piece `pc` that GW1's piece simplicity (`GW1Z.IsSimplePiece`) and the run's regularity give:
a conformal launch chart with a boundary-limit map `f`, a generating trace `α` of the (unstopped) driver `W` up to the
stop, the physical points `g(t) = f(α(t))` injective and off the old set `A` after time `0`, and the piece's stopped
driver. From it:

* `tipAt`, `tipSet_eq`: `g(t)` is the piece's physical point at own time `t`, and the piece is `g([0, S])`;
* `isClosed_image`: `g` maps closed time sets to closed sets (compactness, or properness for an infinite stop);
* `mem_H_of_mem_image`, `eq_of_mem_H`: `α(t) ∈ ℍ` exactly when `g(t)` lies in the launch domain (a landing at a
  real point is not a value on `ℍ`, `landing_notMem_image_H`), and then `g(t) = c⁻¹(α(t))`;
* `exists_mem_H_of_lt`: times with `α ∈ ℍ` are dense (cut times of a global model,
  `YuanSimpleApprox.exists_isCutTime_mem_Ioo`);
* `exists_model`: a global Loewner model `(W', η)` of the piece's driver on `[0, T']`, `T' > τ`, with `η = α` there
  (`Sec7.ReverseArc.exists_global_model`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.WalkWords

open WalkBdry

/-! ### Landings of a conformal chart -/

section Landing

variable {c : Chart}

/-- **A landing at a real point is not a value on `ℍ`.** -/
theorem landing_notMem_image_H (hc : c.IsConformal) {x v : ℂ} (hx : x.im = 0)
    (hv : Tendsto c.2.1 (𝓝[H] x) (𝓝 v)) : v ∉ c.2.1 '' H := by
  rintro ⟨w, hw, rfl⟩
  have hmem : c.2.1 w ∈ (c.dom : Set ℂ) := hc.inv_mem_dom hw
  have hcont : ContinuousAt c.1 (c.2.1 w) :=
    (hc.differentiableOn_fwd.differentiableAt (c.dom.isOpen.mem_nhds hmem)).continuousAt
  have h1 : Tendsto (fun z => c.1 (c.2.1 z)) (𝓝[H] x) (𝓝 (c.1 (c.2.1 w))) := hcont.tendsto.comp hv
  rw [hc.2.2 w hw] at h1
  have h2 : Tendsto (fun z => c.1 (c.2.1 z)) (𝓝[H] x) (𝓝 x) := by
    refine (tendsto_nhdsWithin_iff.1 tendsto_id).1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hc.2.2 z hz).symm
  have : (𝓝[H] x).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ x.im by rw [hx])
  have hwx := tendsto_nhds_unique h1 h2
  have hwH : (0 : ℝ) < w.im := hw
  rw [hwx, hx] at hwH
  exact lt_irrefl 0 hwH

/-- A landing at a point of `ℍ` is the value there. -/
theorem landing_eq_of_mem_H (hc : c.IsConformal) {z v : ℂ} (hz : z ∈ H) (hv : Tendsto c.2.1 (𝓝[H] z) (𝓝 v)) :
    v = c.2.1 z := by
  have : (𝓝[H] z).NeBot := GW1P.neBot_nhdsWithin_H (QuantumZipper.H_subset_Hbar hz)
  exact tendsto_nhds_unique hv
    ((hc.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)

end Landing

/-! ### The piece data -/

/-- **The data of a recorded simple piece** `pc` with old set `A`: boundary-limit map `f` of the launch chart, unstopped
driver `W`, generating trace `α` (see the module docstring). -/
structure PieceData (pc : Piece) (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ) : Prop where
  conf : pc.1.IsConformal
  land : ∀ p ∈ Hbar, Tendsto pc.1.2.1 (𝓝[H] p) (𝓝 (f p))
  bdd : ∃ C : ℝ, ∀ p ∈ Hbar, ‖f p - p‖ ≤ C
  zero : W 0 = 0
  cont : ContinuousOn W {t | (t : ℝ≥0∞) ≤ pc.2.2}
  gen : IsGeneratingTrace W pc.2.2 α
  trans : pc.2.2 = ⊤ → Tendsto (fun t => ‖α t‖) atTop atTop
  inj : InjOn (fun t => f (α t)) {t | (t : ℝ≥0∞) ≤ pc.2.2}
  avoid : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ pc.2.2 → f (α t) ∉ A
  drv : pc.2.1 = fun r : ℝ≥0 => W (min (r : ℝ≥0∞) pc.2.2).toNNReal

namespace PieceData

variable {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ} {W : ℝ≥0 → ℝ} {α : ℝ≥0 → ℂ} (h : PieceData pc A f W α)
include h

theorem contLt : ContinuousOn W {t | (t : ℝ≥0∞) < pc.2.2} :=
  h.cont.mono fun _ (ht : _ < pc.2.2) => (le_of_lt ht : _ ≤ pc.2.2)

theorem mem_Hbar {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pc.2.2) : α t ∈ Hbar :=
  Sec7.IsGeneratingTrace.mem_Hbar h.gen h.contLt h.zero ht

theorem continuousOn : ContinuousOn (fun t => f (α t)) {t | (t : ℝ≥0∞) ≤ pc.2.2} :=
  (GW1P.continuousOn_of_tendsto h.land).comp h.gen.2.1 fun _ ht => h.mem_Hbar ht

/-- `g(t)` is the physical point of the piece at own time `t`. -/
theorem tipAt {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pc.2.2) : pc.1.tipAt pc.2.1 t (f (α t)) := by
  have := CounterflowRange.tendsto_tip_stopped_of_tendsto h.gen h.cont h.zero ht (h.land _ (h.mem_Hbar ht))
  rw [Chart.tipAt, h.drv]
  exact this

/-- The piece is `g([0, S])`. -/
theorem tipSet_eq : pc.1.tipSet pc.2.1 pc.2.2 = (fun t => f (α t)) '' {t | (t : ℝ≥0∞) ≤ pc.2.2} := by
  rw [h.drv, CounterflowRange.tipSet_stopped_eq_of_tendsto h.gen h.cont h.zero fun t ht =>
    h.land _ (h.mem_Hbar ht), image_image]

/-- `g` maps closed time sets to closed sets. -/
theorem isClosed_image {F : Set ℝ≥0} (hF : IsClosed F) (hFS : F ⊆ {t | (t : ℝ≥0∞) ≤ pc.2.2}) :
    IsClosed ((fun t => f (α t)) '' F) := by
  rcases h.bdd with ⟨C, hC⟩
  cases hS : pc.2.2 with
  | top =>
    have hg : Continuous (fun t => f (α t)) := by
      have := h.continuousOn
      rw [hS] at this
      simpa only [le_top, Set.ofPred_true, continuousOn_univ] using this
    have hp : IsProperMap (fun t => f (α t)) := by
      rw [isProperMap_iff_tendsto_cocompact]
      refine ⟨hg, ?_⟩
      rw [cocompact_eq_atTop]
      refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
      have h1 : Tendsto (fun t => ‖α t‖ + -C) atTop atTop := tendsto_atTop_add_const_right _ (-C) (h.trans hS)
      refine tendsto_atTop_mono (fun t => ?_) h1
      have h2 := hC (α t) (h.mem_Hbar (by rw [hS]; exact le_top))
      have h3 := norm_sub_norm_le (α t) (f (α t))
      rw [norm_sub_rev] at h3
      simp only [dist_zero_right]
      linarith
    exact hp.isClosedMap F hF
  | coe s =>
    have hFc : IsCompact F := by
      refine (isCompact_Icc (a := (0 : ℝ≥0)) (b := s)).of_isClosed_subset hF fun t ht => ?_
      have h1 : (t : ℝ≥0∞) ≤ pc.2.2 := hFS ht
      rw [hS] at h1
      exact ⟨bot_le, ENNReal.coe_le_coe.1 h1⟩
    exact (hFc.image_of_continuousOn (h.continuousOn.mono hFS)).isClosed

/-- `α(t) ∈ ℍ` when `g(t)` lies in the launch domain. -/
theorem mem_H_of_mem_image {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pc.2.2) (hd : f (α t) ∈ pc.1.2.1 '' H) : α t ∈ H := by
  by_contra hH
  have h0 : (α t).im = 0 := le_antisymm (not_lt.1 hH) (h.mem_Hbar ht)
  exact landing_notMem_image_H h.conf h0 (h.land _ (h.mem_Hbar ht)) hd

theorem eq_of_mem_H {t : ℝ≥0} (hH : α t ∈ H) : f (α t) = pc.1.2.1 (α t) :=
  landing_eq_of_mem_H h.conf hH (h.land _ (QuantumZipper.H_subset_Hbar hH))

/-- **A global Loewner model of the piece's driver** on `[0, T']`, `T' > τ`, agreeing with `α`. -/
theorem exists_model {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < pc.2.2) :
    ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T' : ℝ), (τ : ℝ) < T' ∧ Continuous W' ∧ W' 0 = 0 ∧ IsLoewnerTrace W' η ∧
      ContinuousOn (pieceDrv pc) (Icc 0 T') ∧ EqOn (pieceDrv pc) W' (Icc 0 T') ∧
      ∀ r ∈ Icc (0 : ℝ) T', η r = α r.toNNReal := by
  obtain ⟨W', η, T₁, hτT, hWc, hW0, hη, hWeq, hηeq⟩ := Sec7.ReverseArc.exists_global_model h.gen h.contLt h.zero hτ
  -- a time `T'` in `(τ, T₁]` before the stop
  obtain ⟨T', hτT', hT'T, hT'S⟩ : ∃ T' : ℝ, (τ : ℝ) < T' ∧ T' ≤ T₁ ∧ ((T'.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ pc.2.2 := by
    cases hS : pc.2.2 with
    | top => exact ⟨T₁, hτT, le_rfl, le_top⟩
    | coe s =>
      rw [hS] at hτ
      have hτs : τ < s := ENNReal.coe_lt_coe.1 hτ
      refine ⟨min T₁ s, lt_min hτT (by exact_mod_cast hτs), min_le_left _ _, ENNReal.coe_le_coe.2 ?_⟩
      rw [Real.toNNReal_le_iff_le_coe]
      exact min_le_right _ _
  have hagree : EqOn (pieceDrv pc) W' (Icc 0 T') := by
    intro r hr
    have hrS : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ pc.2.2 :=
      le_trans (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.2)) hT'S
    change pc.2.1 r.toNNReal = W' r
    rw [h.drv, hWeq r ⟨hr.1, hr.2.trans hT'T⟩]
    simp only [min_eq_left hrS, ENNReal.toNNReal_coe]
  refine ⟨W', η, T', hτT', hWc, hW0, hη, (hWc.continuousOn).congr hagree, hagree, fun r hr => ?_⟩
  exact hηeq r ⟨hr.1, hr.2.trans hT'T⟩

/-- **Times with `α ∈ ℍ` are dense.** -/
theorem exists_mem_H_of_lt {a b : ℝ≥0} (hab : a < b) (hb : (b : ℝ≥0∞) ≤ pc.2.2) :
    ∃ t ∈ Ioo a b, α t ∈ H := by
  set q : ℝ≥0 := (a + b) / 2 with hq
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hqr : (q : ℝ) = ((a : ℝ) + b) / 2 := by rw [hq]; push_cast; ring
  have haq : a < q := by rw [← NNReal.coe_lt_coe, hqr]; linarith
  have hqb : q < b := by rw [← NNReal.coe_lt_coe, hqr]; linarith
  have hqS : (q : ℝ≥0∞) < pc.2.2 := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hqb) hb
  obtain ⟨W', η, T', hqT, hWc, hW0, hη, -, -, hηeq⟩ := h.exists_model hqS
  obtain ⟨t, ht, hcut⟩ := YuanSimpleApprox.exists_isCutTime_mem_Ioo hη hWc hW0 (a.coe_nonneg) (show (a : ℝ) < q by
    exact_mod_cast haq)
  have ht0 : 0 ≤ t := a.coe_nonneg.trans ht.1.le
  refine ⟨t.toNNReal, ⟨?_, ?_⟩, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal t ht0]; exact ht.1
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal t ht0]; exact ht.2.trans (by exact_mod_cast hqb)
  · rw [← hηeq t ⟨ht0, ht.2.le.trans hqT.le⟩]; exact hcut.1

/-- **Continuity window** of `g` at an own time. -/
theorem exists_window {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) ≤ pc.2.2) {V : Set ℂ} (hV : IsOpen V) (hgV : f (α t₀) ∈ V) :
    ∃ ε > 0, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ pc.2.2 → |(t : ℝ) - t₀| < ε → f (α t) ∈ V := by
  have hc := h.continuousOn t₀ ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hc.preimage_mem_nhdsWithin (hV.mem_nhds hgV))
  refine ⟨ε, hε, fun t ht hdt => hball ⟨?_, ht⟩⟩
  rw [mem_ball, NNReal.dist_eq]
  exact hdt

/-- **Times with `α ∈ ℍ` near any own time**: if the piece has a second time, every open set around `g(t₀)` contains
some `g(t)` with `α(t) ∈ ℍ`. -/
theorem exists_mem_H_near {t₀ t₁ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) ≤ pc.2.2) (ht₁ : (t₁ : ℝ≥0∞) ≤ pc.2.2) (h01 : t₀ ≠ t₁)
    {V : Set ℂ} (hV : IsOpen V) (hgV : f (α t₀) ∈ V) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ pc.2.2 ∧ α t ∈ H ∧ f (α t) ∈ V := by
  obtain ⟨ε, hε, hwin⟩ := h.exists_window ht₀ hV hgV
  set e : ℝ≥0 := ⟨ε / 2, by positivity⟩ with hedef
  have he : (e : ℝ) = ε / 2 := rfl
  rcases lt_or_gt_of_ne h01 with hlt | hgt
  · -- the interval `(t₀, min t₁ (t₀ + e))`
    have hlt' : t₀ < min t₁ (t₀ + e) := lt_min hlt (lt_add_of_pos_right _ (by rw [← NNReal.coe_pos, he]; positivity))
    have hb : ((min t₁ (t₀ + e) : ℝ≥0) : ℝ≥0∞) ≤ pc.2.2 := le_trans (ENNReal.coe_le_coe.2 (min_le_left _ _)) ht₁
    obtain ⟨t, ht, htH⟩ := h.exists_mem_H_of_lt hlt' hb
    have htS : (t : ℝ≥0∞) ≤ pc.2.2 := le_trans (ENNReal.coe_le_coe.2 ht.2.le) hb
    refine ⟨t, htS, htH, hwin t htS ?_⟩
    have h1 : (t₀ : ℝ) < t := by exact_mod_cast ht.1
    have h2 : (t : ℝ) < t₀ + ε / 2 := by
      have := (lt_min_iff.1 ht.2).2
      rw [← NNReal.coe_lt_coe, NNReal.coe_add, he] at this
      exact this
    rw [abs_lt]; constructor <;> linarith
  · -- the interval `(max t₁ (t₀ - e), t₀)`
    have hgt' : max t₁ (t₀ - e) < t₀ := max_lt hgt (tsub_lt_self (lt_of_le_of_lt bot_le hgt)
      (by rw [← NNReal.coe_pos, he]; positivity))
    obtain ⟨t, ht, htH⟩ := h.exists_mem_H_of_lt hgt' ht₀
    have htS : (t : ℝ≥0∞) ≤ pc.2.2 := le_trans (ENNReal.coe_le_coe.2 ht.2.le) ht₀
    refine ⟨t, htS, htH, hwin t htS ?_⟩
    have h1 : (t : ℝ) < t₀ := by exact_mod_cast ht.2
    have h2 : (t₀ : ℝ) - ε / 2 ≤ t := by
      have h3 := (max_lt_iff.1 ht.1).2
      have h4 : ((t₀ - e : ℝ≥0) : ℝ) < t := by exact_mod_cast h3
      have h5 : (t₀ : ℝ) - e ≤ ((t₀ - e : ℝ≥0) : ℝ) := by rw [NNReal.coe_sub_def]; exact le_max_left _ _
      rw [he] at h5
      linarith
    rw [abs_lt]; constructor <;> linarith

end PieceData

end InteractingSLE.Theorem14.WalkWords
