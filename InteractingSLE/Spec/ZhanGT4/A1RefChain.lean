/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA2Pair
import InteractingSLE.Foundations.Loewner.ConformalImageFull
import InteractingSLE.Foundations.Loewner.FiniteEndpoint
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# A.1 on one reference space: the canonical image chain up to contact

Packet PROVE-ZHAN-A1REF. Source: Astra, *Follow-up proofs*, §A.1 L183–L187 (R38): "curve `j`, mapped by the
hydrodynamic map of that prefix and stopped on first contact with it, has the corresponding force-point law, after
its capacity time change"; Specification Aux. lemma 8 ((HD1)–(HD3), [Law05] §4.6.1).

A2X's `IsImageChainUpTo xj wj ζj xk wk τ x' w' clk ζ'` asks for a capacity clock and an image driver such that,
before the contact time `c = contactTime xj wj ζj xk wk τ`, the image under `g_τ = physMap xk wk τ` of the hull of
curve `j` is the hull of the image driver after the clock. This file constructs both **canonically** from the two
drivers (no choice depending on a horizon), for continuous centred drivers and `τ ≥ 0`:

* `imgClk s = ½ hcap(g_τ(K_j(s)))` (the capacity clock);
* `imgDrv σ`: the value at `σ` of any image driver on any horizon `T < c` whose clock reaches `σ`; two image drivers
  agree where both are defined (`eqOn_of_isImgDrvOn`: same start, the boundary value of `g_τ` at `xj`; same hulls;
  `Sec6.eqOn_of_fwdHull_eq`);
* `imgLife = sup_{s < c} imgClk s`.

## Main results

* `exists_isImgDrvOn`: on every horizon `0 < T` with `T < c`, Aux. lemma 8 (`exists_loewner_image_of_pos`) gives an
  image driver; the clock is continuous, strictly increasing, `0` at `0`;
* `imgDrv_eqOn`: the canonical driver agrees with every image driver on `[0, imgClk T]`;
* **`isImageChainUpTo_canonical`**: `IsImageChainUpTo xj wj ζj xk wk τ x' (imgDrv − x') imgClk imgLife` for every
  image source `x'` (A1DUAL's "What remains" 1, the link `A2X.IsImageChainUpTo`, pathwise);
* `continuousOn_imgDrv`: the canonical driver is continuous before `imgLife`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Ref

open QuantumZipper (H)
open A2X ConformalImage

/-! ### Deterministic preliminaries -/

/-- The hull of a curve started at `x` with driver `w` is the hull of the uncentred driver `w + x`. -/
theorem physHull_eq_fwdHull (x : ℝ) (w : ℝ → ℝ) (s : ℝ) :
    physHull x w s = QuantumZipper.fwdHull (fun r => w r + x) s :=
  (ConformalImageFull.fwdHull_add_const w x s).symm

theorem physHull_eq_image_affHomeo (x : ℝ) (w : ℝ → ℝ) (s : ℝ) :
    physHull x w s = affHomeo 1 one_pos x '' QuantumZipper.fwdHull w s :=
  image_congr fun z _ => (ConformalImageFull.affHomeo_one_apply x z).symm

/-- `K_k(τ)` is a compact `ℍ`-hull. -/
theorem isHPHull_physHull {x : ℝ} {w : ℝ → ℝ} (hw : Continuous w) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsHPHull (physHull x w τ) := by
  rw [physHull_eq_image_affHomeo]
  exact (isHPHull_fwdHull hw hτ).image_affHomeo one_pos

/-- **`g_τ = physMap x w τ` maps out `K(τ) = physHull x w τ`** (a centred continuous driver). -/
theorem isMapOut_physMap {x : ℝ} {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsMapOut (physHull x w τ) (physMap x w τ) := by
  have h := (isMapOut_fwdMap hw hw0 hτ).comp_affHomeo one_pos (x := x)
  rw [physHull_eq_image_affHomeo]
  convert h using 1
  funext z
  rw [ConformalImageFull.affHomeo_one_apply, ConformalImageFull.affHomeo_one_symm_apply, physMap]
  ring

theorem hcapSet_empty : hcapSet (∅ : Set ℂ) = 0 := by
  unfold hcapSet
  split_ifs with h
  · exact HPHull.hcap_eq_zero_of_eq_empty _ rfl
  · rfl

/-- Stopping a driver at time `T`: `s ↦ w(max 0 (min s T))`. -/
def stopDrv (w : ℝ → ℝ) (T : ℝ) (s : ℝ) : ℝ := w (max 0 (min s T))

theorem continuous_stopDrv {w : ℝ → ℝ} {T : ℝ} (hw : ContinuousOn w (Icc 0 T)) (hT : 0 ≤ T) :
    Continuous (stopDrv w T) :=
  hw.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) fun _ =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem stopDrv_eqOn (w : ℝ → ℝ) (T : ℝ) : EqOn (stopDrv w T) w (Icc 0 T) := fun s hs => by
  simp only [stopDrv, min_eq_left hs.2, max_eq_right hs.1]

/-- The hull at `t` reads the driver on `[0, T]` only, `t < T`. -/
theorem physHull_congr {x : ℝ} {w w' : ℝ → ℝ} {t T : ℝ} (ht : 0 ≤ t) (htT : t < T) (h : EqOn w w' (Icc 0 T)) :
    physHull x w t = physHull x w' t := by
  rw [physHull_eq_fwdHull, physHull_eq_fwdHull]
  exact LocalExt.fwdHull_congr_of_eqOn_of_lt ht htT fun s hs => by simp only [h hs]

/-- `g_τ` reads the driver on `[0, τ]` only. -/
theorem physMap_congr {x : ℝ} {w w' : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ) (h : EqOn w w' (Icc 0 τ)) :
    physMap x w τ = physMap x w' τ := by
  funext z
  simp only [physMap, h ⟨hτ, le_rfl⟩, Ito.fwdMap_congr_of_eqOn h]

/-- `K_k(τ)` is a compact `ℍ`-hull (driver continuous slightly beyond `τ`). -/
theorem isHPHull_physHull_loc {x : ℝ} {w : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hw : ∃ τ', τ < τ' ∧ ContinuousOn w (Icc 0 τ')) : IsHPHull (physHull x w τ) := by
  obtain ⟨τ', hττ', hw⟩ := hw
  rw [physHull_congr hτ hττ' (stopDrv_eqOn w τ').symm]
  exact isHPHull_physHull (continuous_stopDrv hw (hτ.trans hττ'.le)) hτ

/-- `g_τ` maps out `K_k(τ)` (centred driver, continuous slightly beyond `τ`). -/
theorem isMapOut_physMap_loc {x : ℝ} {w : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hw : ∃ τ', τ < τ' ∧ ContinuousOn w (Icc 0 τ')) (hw0 : w 0 = 0) :
    IsMapOut (physHull x w τ) (physMap x w τ) := by
  obtain ⟨τ', hττ', hw⟩ := hw
  have hτ' : 0 ≤ τ' := hτ.trans hττ'.le
  have e : EqOn (stopDrv w τ') w (Icc 0 τ') := stopDrv_eqOn w τ'
  rw [physHull_congr hτ hττ' e.symm, physMap_congr hτ fun s hs => (e ⟨hs.1, hs.2.trans hττ'.le⟩).symm]
  exact isMapOut_physMap (continuous_stopDrv hw hτ') (by rw [e ⟨le_rfl, hτ'⟩, hw0]) hτ

section Chain

variable (xj : ℝ) (wj : ℝ → ℝ) (ζj : ℝ≥0∞) (xk : ℝ) (wk : ℝ → ℝ) (τ : ℝ)

/-- **The canonical capacity clock** `s ↦ ½ hcap(g_τ(K_j(s)))` (`0` at `s ≤ 0`). -/
def imgClk (s : ℝ) : ℝ := if 0 < s then hcapSet (physMap xk wk τ '' physHull xj wj s) / 2 else 0

/-- **An image driver on the horizon `T`**: continuous, started at the boundary value of `g_τ` at `xj`, and its hull
at `imgClk t` is `g_τ(K_j(t))` for every `t ∈ [0, T]`. -/
def IsImgDrvOn (T : ℝ) (W' : ℝ → ℝ) : Prop :=
  Continuous W' ∧ Tendsto (physMap xk wk τ) (𝓝[H] (xj : ℂ)) (𝓝 (W' 0 : ℂ)) ∧
    ∀ t ∈ Icc (0 : ℝ) T, QuantumZipper.fwdHull W' (imgClk xj wj xk wk τ t) = physMap xk wk τ '' physHull xj wj t

/-- A horizon strictly inside the pre-contact interval. -/
def IsGoodTime (T : ℝ) : Prop := 0 < T ∧ ENNReal.ofReal T < contactTime xj wj ζj xk wk τ

open scoped Classical in
/-- **The canonical image driver** (uncentred): the value at `σ` of an image driver on a good horizon whose clock
reaches `σ` (well defined by `eqOn_of_isImgDrvOn`); `0` if there is none. -/
def imgDrv (σ : ℝ) : ℝ :=
  if h : ∃ T : ℝ, IsGoodTime xj wj ζj xk wk τ T ∧ σ ≤ imgClk xj wj xk wk τ T ∧
      ∃ W' : ℝ → ℝ, IsImgDrvOn xj wj xk wk τ T W' then h.choose_spec.2.2.choose σ else 0

/-- **The canonical image lifetime**: the clock's limit at the contact time. -/
def imgLife : ℝ≥0∞ :=
  ⨆ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < contactTime xj wj ζj xk wk τ), ENNReal.ofReal (imgClk xj wj xk wk τ s)

variable {xj wj ζj xk wk τ}

theorem imgClk_zero : imgClk xj wj xk wk τ 0 = 0 := by simp [imgClk]

theorem contactTime_le : contactTime xj wj ζj xk wk τ ≤ ζj := min_le_left _ _

/-- Before the contact time the closed hulls are disjoint. -/
theorem disjoint_of_isGoodTime {T : ℝ} (hT : IsGoodTime xj wj ζj xk wk τ T) :
    Disjoint (closure (physHull xk wk τ)) (closure (physHull xj wj T)) := by
  rw [disjoint_comm]
  by_contra hnd
  rw [Set.not_disjoint_iff_nonempty_inter] at hnd
  have hT0 : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.1.le
  have hle : contactTime xj wj ζj xk wk τ ≤ ((T.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    min_le_of_right_le (iInf₂_le T.toNNReal (by rw [hT0]; exact hnd))
  exact absurd (hT.2.trans_le hle) (lt_irrefl _)

/-- Good horizons exist beyond every pre-contact time. -/
theorem exists_isGoodTime {s : ℝ} (hs0 : 0 ≤ s) (hs : ENNReal.ofReal s < contactTime xj wj ζj xk wk τ) :
    ∃ T, IsGoodTime xj wj ζj xk wk τ T ∧ s < T := by
  obtain ⟨r, hr0, hsr, hrc⟩ := ENNReal.lt_iff_exists_real_btwn.1 hs
  have hsr' : s < r := ((ENNReal.ofReal_lt_ofReal_iff').1 hsr).1
  exact ⟨r, ⟨hs0.trans_lt hsr', hrc⟩, hsr'⟩

variable (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
  (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ)
include hj hj0 hk hk0 hτ

/-- **Aux. lemma 8 on a good horizon**: an image driver exists, and the clock is strictly increasing and continuous
on `[0, T]`. Curve `j`'s driver is stopped at a later good horizon `T'` (continuous there, `T' < ζj`). -/
theorem exists_isImgDrvOn {T : ℝ} (hT : IsGoodTime xj wj ζj xk wk τ T) :
    (∃ W', IsImgDrvOn xj wj xk wk τ T W') ∧
      StrictMonoOn (imgClk xj wj xk wk τ) (Icc 0 T) ∧ ContinuousOn (imgClk xj wj xk wk τ) (Icc 0 T) := by
  obtain ⟨T', hT', hTT'⟩ := exists_isGoodTime hT.1.le hT.2
  have hT'0 : 0 ≤ T' := hT'.1.le
  set V := stopDrv wj T' with hVdef
  have hV : Continuous V := continuous_stopDrv (hj T' (hT'.2.trans_le contactTime_le)) hT'0
  have hVe : EqOn V wj (Icc 0 T') := stopDrv_eqOn wj T'
  have hV0 : V 0 = 0 := by rw [hVe ⟨le_rfl, hT'0⟩, hj0]
  have hPH : ∀ t ∈ Icc (0 : ℝ) T, physHull xj wj t = physHull xj V t := fun t ht =>
    physHull_congr ht.1 (ht.2.trans_lt hTT') hVe.symm
  have hU : Continuous fun r => V r + xj := hV.add continuous_const
  have hA := isHPHull_physHull_loc (x := xk) hτ hk
  have hφA := isMapOut_physMap_loc (x := xk) hτ hk hk0
  have hd := disjoint_of_isGoodTime hT
  rw [hPH T ⟨hT.1.le, le_rfl⟩, physHull_eq_fwdHull xj V T] at hd
  obtain ⟨a, W', hW'c, ha0, hamono, hacont, hmain⟩ :=
    ConformalImageFull.exists_loewner_image_of_pos hU hT.1 hA hφA hd
  have hEq : EqOn a (imgClk xj wj xk wk τ) (Icc 0 T) := fun t ht => by
    rcases ht.1.eq_or_lt with h0 | hpos
    · rw [← h0, ha0, imgClk_zero]
    obtain ⟨⟨hK, hat⟩, -, -⟩ := hmain t ht
    simp only [imgClk, hpos, ↓reduceIte]
    rw [hat, hPH t ht, physHull_eq_fwdHull, hcapSet_eq hK]
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.1.le⟩
  refine ⟨⟨W', hW'c, ?_, fun t ht => ?_⟩, fun s hs t ht hst => ?_, hacont.congr fun t ht => (hEq ht).symm⟩
  · -- the start: the boundary value of `g_τ` at `xj` (the clause at `t = 0`, with `R = g_τ`)
    obtain ⟨-, -, hR⟩ := hmain 0 h0mem
    have hE : (fun z => QuantumZipper.fwdMap (fun r => V r + xj) 0 z + (((V 0 + xj : ℝ)) : ℂ)) ''
        physHull xk wk τ = physHull xk wk τ := by
      conv_rhs => rw [← image_id (physHull xk wk τ)]
      refine image_congr fun z hz => ?_
      have hzH : z ∈ H := hA.1 hz
      have hz' : z - xj ∈ H := by simpa [QuantumZipper.H] using hzH
      have hz'' : z - xj ∈ H \ QuantumZipper.fwdHull V 0 := by
        rw [QuantumZipper.RS.fwdHull_zero_eq_empty hV, sdiff_empty]; exact hz'
      rw [ConformalImageFull.fwdMap_add_const, fwdMap_zero_eq hV hV0 (le_refl 0) hz'', hV0, id]
      push_cast
      ring
    have hφ : IsMapOut ((fun z => QuantumZipper.fwdMap (fun r => V r + xj) 0 z +
        (((V 0 + xj : ℝ)) : ℂ)) '' physHull xk wk τ) (physMap xk wk τ) := by
      rw [hE]; exact hφA
    have ht := (hR _ hφ).2
    rw [hV0, zero_add, ha0] at ht
    exact ht
  · obtain ⟨-, hhull, -⟩ := hmain t ht
    rw [← hEq ht, hhull, hPH t ht, physHull_eq_fwdHull]
  · rw [← hEq hs, ← hEq ht]
    exact hamono hs ht hst

omit hj hj0 hk hk0 hτ in
/-- **Two image drivers agree** on `[0, imgClk m]`, `m` below both horizons: same start (uniqueness of the boundary
limit of `g_τ` at `xj`) and the same hulls at every time `imgClk t`, `t ≤ m` (intermediate values of the clock). -/
theorem eqOn_of_isImgDrvOn {m T₁ T₂ : ℝ} (hm : 0 ≤ m) (hm₁ : m ≤ T₁) (hm₂ : m ≤ T₂)
    (hclk : ContinuousOn (imgClk xj wj xk wk τ) (Icc 0 m)) (hclk0 : imgClk xj wj xk wk τ 0 = 0)
    {W₁ W₂ : ℝ → ℝ} (h₁ : IsImgDrvOn xj wj xk wk τ T₁ W₁) (h₂ : IsImgDrvOn xj wj xk wk τ T₂ W₂) :
    EqOn W₁ W₂ (Icc 0 (imgClk xj wj xk wk τ m)) := by
  -- the same start
  have hne := FiniteEndpoint.neBot_nhdsWithin_H (z := (xj : ℂ)) (ofReal_im xj)
  have hb : W₁ 0 = W₂ 0 := ofReal_injective (tendsto_nhds_unique h₁.2.1 h₂.2.1)
  set b := W₁ 0 with hbdef
  -- the centred drivers have the same hulls
  have hW : ∀ W : ℝ → ℝ, (fun s => (W s - b) + b) = W := fun W => funext fun s => sub_add_cancel _ _
  by_cases hS : 0 ≤ imgClk xj wj xk wk τ m
  swap
  · intro σ hσ; exact absurd (hσ.1.trans hσ.2) hS
  have hhull : ∀ σ ∈ Icc (0 : ℝ) (imgClk xj wj xk wk τ m),
      QuantumZipper.fwdHull (fun s => W₁ s - b) σ = QuantumZipper.fwdHull (fun s => W₂ s - b) σ := by
    intro σ hσ
    have hσ' : σ ∈ Icc (imgClk xj wj xk wk τ 0) (imgClk xj wj xk wk τ m) := by rwa [hclk0]
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc hm hclk hσ'
    have e₁ := h₁.2.2 t ⟨ht.1, ht.2.trans hm₁⟩
    have e₂ := h₂.2.2 t ⟨ht.1, ht.2.trans hm₂⟩
    have key : (fun z : ℂ => z + b) '' QuantumZipper.fwdHull (fun s => W₁ s - b) (imgClk xj wj xk wk τ t) =
        (fun z : ℂ => z + b) '' QuantumZipper.fwdHull (fun s => W₂ s - b) (imgClk xj wj xk wk τ t) := by
      rw [← ConformalImageFull.fwdHull_add_const, ← ConformalImageFull.fwdHull_add_const, hW, hW, e₁, e₂]
    exact (Set.image_injective.2 (add_left_injective (b : ℂ))) key
  have h := Sec6.eqOn_of_fwdHull_eq (W := fun s => W₁ s - b) (W' := fun s => W₂ s - b)
    (h₁.1.sub continuous_const) (h₂.1.sub continuous_const) (sub_self _)
    (show W₂ 0 - b = 0 by rw [← hb, sub_self]) hS hhull
  intro σ hσ
  have := h hσ
  simpa using this

/-- **The canonical driver agrees with every image driver** on a good horizon, on `[0, imgClk T]`. -/
theorem imgDrv_eqOn {T : ℝ} (hT : IsGoodTime xj wj ζj xk wk τ T) {W' : ℝ → ℝ}
    (hW' : IsImgDrvOn xj wj xk wk τ T W') :
    EqOn (imgDrv xj wj ζj xk wk τ) W' (Icc 0 (imgClk xj wj xk wk τ T)) := by
  intro σ hσ
  have hex : ∃ T : ℝ, IsGoodTime xj wj ζj xk wk τ T ∧ σ ≤ imgClk xj wj xk wk τ T ∧
      ∃ W' : ℝ → ℝ, IsImgDrvOn xj wj xk wk τ T W' := ⟨T, hT, hσ.2, W', hW'⟩
  simp only [imgDrv, hex, dite_true]
  obtain ⟨hT₀, hσ₀, -⟩ := hex.choose_spec
  have hW₀ := hex.choose_spec.2.2.choose_spec
  set T₀ := hex.choose
  obtain ⟨-, -, hclkT⟩ := exists_isImgDrvOn hj hj0 hk hk0 hτ hT
  have hclk0 := imgClk_zero (xj := xj) (wj := wj) (xk := xk) (wk := wk) (τ := τ)
  have hm : 0 ≤ min T₀ T := le_min hT₀.1.le hT.1.le
  refine eqOn_of_isImgDrvOn hm (min_le_left _ _) (min_le_right _ _)
    (hclkT.mono (Icc_subset_Icc le_rfl (min_le_right _ _))) hclk0 hW₀ hW' ⟨hσ.1, ?_⟩
  rcases le_total T₀ T with h | h
  · rw [min_eq_left h]; exact hσ₀
  · rw [min_eq_right h]; exact hσ.2

/-- **The canonical image chain up to contact** (A2X's `IsImageChainUpTo`, pathwise): for continuous centred drivers
and `τ ≥ 0`, the canonical clock, the canonical driver shifted by any image source `x'`, and the canonical image
lifetime form an image chain up to the contact time. -/
theorem isImageChainUpTo_canonical (x' : ℝ) :
    IsImageChainUpTo xj wj ζj xk wk τ x' (fun σ => imgDrv xj wj ζj xk wk τ σ - x') (imgClk xj wj xk wk τ)
      (imgLife xj wj ζj xk wk τ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact imgClk_zero
  · intro s hs
    obtain ⟨T, hT, hsT⟩ := exists_isGoodTime hs.1 hs.2
    obtain ⟨-, -, hcont⟩ := exists_isImgDrvOn hj hj0 hk hk0 hτ hT
    refine (hcont s ⟨hs.1, hsT.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio T, isOpen_Iio, hsT, fun x hx => ⟨hx.2.1, le_of_lt hx.1⟩⟩
  · intro s hs t ht hst
    obtain ⟨T, hT, htT⟩ := exists_isGoodTime ht.1 ht.2
    obtain ⟨-, hmono, -⟩ := exists_isImgDrvOn hj hj0 hk hk0 hτ hT
    exact hmono ⟨hs.1, (hst.trans htT).le⟩ ⟨ht.1, htT.le⟩ hst
  · intro t
    simp only [imgLife, lt_iSup_iff, ENNReal.ofReal, ENNReal.coe_lt_coe, Real.lt_toNNReal_iff_coe_lt,
      exists_prop]
  · intro s hs
    have hs' : ENNReal.ofReal (s : ℝ) < contactTime xj wj ζj xk wk τ := by rwa [ENNReal.ofReal_coe_nnreal]
    obtain ⟨T, hT, hsT⟩ := exists_isGoodTime s.coe_nonneg hs'
    obtain ⟨⟨W', hW'⟩, hmono, -⟩ := exists_isImgDrvOn hj hj0 hk hk0 hτ hT
    have hclk0 := imgClk_zero (xj := xj) (wj := wj) (xk := xk) (wk := wk) (τ := τ)
    have hsI : (s : ℝ) ∈ Icc 0 T := ⟨s.coe_nonneg, hsT.le⟩
    have hTI : T ∈ Icc 0 T := ⟨hT.1.le, le_rfl⟩
    have hlt : imgClk xj wj xk wk τ s < imgClk xj wj xk wk τ T := hmono hsI hTI hsT
    have hnn : 0 ≤ imgClk xj wj xk wk τ s := by
      rw [← hclk0]; exact hmono.monotoneOn ⟨le_rfl, hT.1.le⟩ hsI s.coe_nonneg
    rw [physHull_eq_fwdHull x', show (fun r => imgDrv xj wj ζj xk wk τ r - x' + x') = imgDrv xj wj ζj xk wk τ
      from funext fun r => sub_add_cancel _ _,
      LocalExt.fwdHull_congr_of_eqOn_of_lt hnn hlt (imgDrv_eqOn hj hj0 hk hk0 hτ hT hW'), hW'.2.2 s hsI]

/-- **The canonical driver is continuous before the canonical image lifetime.** -/
theorem continuousOn_imgDrv :
    ContinuousOn (imgDrv xj wj ζj xk wk τ) {σ | 0 ≤ σ ∧ ENNReal.ofReal σ < imgLife xj wj ζj xk wk τ} := by
  intro σ hσ
  have hσ' : ENNReal.ofReal σ < imgLife xj wj ζj xk wk τ := hσ.2
  simp only [imgLife, lt_iSup_iff, exists_prop] at hσ'
  obtain ⟨s, hs, hσs⟩ := hσ'
  have hσs' : σ < imgClk xj wj xk wk τ s := (ENNReal.ofReal_lt_ofReal_iff'.1 hσs).1
  have hs' : ENNReal.ofReal (s : ℝ) < contactTime xj wj ζj xk wk τ := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨T, hT, hsT⟩ := exists_isGoodTime s.coe_nonneg hs'
  obtain ⟨⟨W', hW'⟩, hmono, -⟩ := exists_isImgDrvOn hj hj0 hk hk0 hτ hT
  have hlt : σ < imgClk xj wj xk wk τ T :=
    hσs'.trans (hmono ⟨s.coe_nonneg, hsT.le⟩ ⟨hT.1.le, le_rfl⟩ hsT)
  have heq := imgDrv_eqOn hj hj0 hk hk0 hτ hT hW'
  refine (hW'.1.continuousAt.continuousWithinAt).congr_of_eventuallyEq ?_ (heq ⟨hσ.1, hlt.le⟩)
  filter_upwards [inter_mem_nhdsWithin _ (Iio_mem_nhds hlt), self_mem_nhdsWithin] with x hx hxS
  exact heq ⟨hxS.1, le_of_lt hx.2⟩

end Chain

end InteractingSLE.ZhanGT4.A1Ref
