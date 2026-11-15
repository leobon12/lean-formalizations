/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RefCond
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# A.1 on one reference space: the pathwise regularity `ChainReg` from the marginal paths

Packet PROVE-ZHAN-A1REF. `A1RefCond.isCondImageLaw_of_canon` needs `ChainReg` almost surely. This file derives it
from integrated paths of the two curves:

* `imgDrv_zero_eq_of_tendsto`: when the contact time is positive, the canonical image source is the boundary value of
  `g_τ` at `xj`;
* **`tendsto_physMap_of_force`** (force points are boundary values, Specification (1.11), through
  `tendsto_fwdMap_of_isForwardSol_real`): a force process `v` of a path `w` (integrated force equation from `p`),
  separated from `w` on `[0, t]`, `t` before the lifetime, gives `g_t(x + p) = x + v(t)` as a boundary limit;
* **`chainReg_of_paths`**: `ChainReg` from continuity of the two drivers before their lifetimes, centred starts, live
  times before curve `k`'s lifetime, and the boundary-value identification of the image source.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Ref

open QuantumZipper (H)
open A2X

/-! ### The canonical image source is the boundary value of `g_τ` -/

section Src

variable {xj : ℝ} {wj : ℝ → ℝ} {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ : ℝ}

/-- **The canonical image source** is the boundary limit of `g_τ` at `xj` when the contact time is positive. -/
theorem imgDrv_zero_eq_of_tendsto (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T))
    (hj0 : wj 0 = 0) (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ)
    (hc : 0 < contactTime xj wj ζj xk wk τ) {s : ℝ}
    (h : Tendsto (physMap xk wk τ) (𝓝[H] (xj : ℂ)) (𝓝 (s : ℂ))) : imgDrv xj wj ζj xk wk τ 0 = s := by
  obtain ⟨T, hT, -⟩ := exists_isGoodTime (xj := xj) (wj := wj) (ζj := ζj) (xk := xk) (wk := wk) (τ := τ)
    le_rfl (by rwa [ENNReal.ofReal_zero])
  obtain ⟨⟨W', hW'⟩, hmono, -⟩ := exists_isImgDrvOn hj hj0 hk hk0 hτ hT
  have hnn : 0 ≤ imgClk xj wj xk wk τ T := by
    rw [← imgClk_zero (xj := xj) (wj := wj) (xk := xk) (wk := wk) (τ := τ)]
    exact hmono.monotoneOn ⟨le_rfl, hT.1.le⟩ ⟨hT.1.le, le_rfl⟩ hT.1.le
  rw [imgDrv_eqOn hj hj0 hk hk0 hτ hT hW' ⟨le_rfl, hnn⟩]
  have hne := FiniteEndpoint.neBot_nhdsWithin_H (z := (xj : ℂ)) (ofReal_im xj)
  exact ofReal_injective (tendsto_nhds_unique hW'.2.1 h)

end Src

/-! ### Force points are boundary values -/

/-- A path continuous before `ζ`, read on `ℝ`, is continuous on `[0, T]` for every real `T` before `ζ`. -/
theorem continuousOn_extPath_Icc {f : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < ζ}) {T : ℝ}
    (hT : ENNReal.ofReal T < ζ) : ContinuousOn (Strip.extPath f) (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT0 | hT0
  · rw [Icc_eq_empty (not_le.2 hT0)]; exact continuousOn_empty _
  · have h := Strip.continuousOn_extPath hf (s := T.toNNReal) hT
    rwa [Real.coe_toNNReal T hT0] at h

/-- A path continuous before `ζ` is continuous on `[0, τ']` for some `τ'` beyond each time `t < ζ`. -/
theorem exists_continuousOn_extPath_beyond {f : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : ∃ τ' : ℝ, (t : ℝ) < τ' ∧ ContinuousOn (Strip.extPath f) (Icc 0 τ') := by
  rw [← ENNReal.ofReal_coe_nnreal] at ht
  obtain ⟨r, -, htr, hrζ⟩ := ENNReal.lt_iff_exists_real_btwn.1 ht
  exact ⟨r, ((ENNReal.ofReal_lt_ofReal_iff').1 htr).1, continuousOn_extPath_Icc hf hrζ⟩

/-- **Force points are boundary values of `g_t`** (Specification (1.11)): let `w` be continuous before `ζ` with
`w 0 = 0`, and `v` a force process of `w` from `p` (`v t = p + ∫₀ᵗ 2/(v − w)` before `ζ`, continuous there),
separated from `w` on `[0, t]`, `t < ζ`. Then `g_t = physMap x w t` (the curve started at `x`) extends continuously to
the physical mark `x + p` with value `x + v(t)`. -/
theorem tendsto_physMap_of_force {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ t, v r ≠ w r) (x : ℝ) :
    Tendsto (physMap x (Strip.extPath w) t) (𝓝[H] ((x + p : ℝ) : ℂ)) (𝓝 ((x + v t : ℝ) : ℂ)) := by
  obtain ⟨τ', htτ', hcw⟩ := exists_continuousOn_extPath_beyond hw ht
  have hτ'0 : 0 ≤ τ' := t.coe_nonneg.trans htτ'.le
  set W := stopDrv (Strip.extPath w) τ' with hWdef
  have hWc : Continuous W := continuous_stopDrv hcw hτ'0
  have hWe : EqOn W (Strip.extPath w) (Icc 0 τ') := stopDrv_eqOn _ _
  have hW0 : W 0 = 0 := by rw [hWe ⟨le_rfl, hτ'0⟩]; simp [Strip.extPath, hw0]
  have hWt : ∀ s ∈ Icc (0 : ℝ) t, W s = w s.toNNReal := fun s hs => by
    rw [hWe ⟨hs.1, hs.2.trans htτ'.le⟩]; rfl
  have hmap : physMap x (Strip.extPath w) t = physMap x W t :=
    physMap_congr t.coe_nonneg fun s hs => (hWe ⟨hs.1, hs.2.trans htτ'.le⟩).symm
  -- the centred force process solves the forward flow from `p`
  set u : ℝ → ℂ := fun s => ((v s.toNNReal - W s : ℝ) : ℂ) with hudef
  have hlt : ∀ s ∈ Icc (0 : ℝ) t, ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) ht
  have hvc : ContinuousOn (Strip.extPath v) (Icc 0 (t : ℝ)) := Strip.continuousOn_extPath hv ht
  have hu : QuantumZipper.IsForwardSol W (p : ℂ) t u := by
    refine ⟨continuous_ofReal.comp_continuousOn (hvc.sub hWc.continuousOn), fun s hs => ⟨?_, ?_⟩⟩
    · simp only [hudef, ne_eq, ofReal_eq_zero, hWt s hs, sub_eq_zero]
      exact hsep _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
    · have hint : ∫ r in (0 : ℝ)..s, (2 : ℂ) / u r =
          ((∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal) : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le hs.1] at hr
        simp only [hudef, hWt r ⟨hr.1, hr.2.trans hs.2⟩]
        push_cast
        rfl
      have hve := hveq s.toNNReal (hlt s hs)
      rw [Real.coe_toNNReal s hs.1] at hve
      rw [hint, hudef]
      simp only [hWt s hs]
      rw [hve]
      push_cast
      ring
  have hT := tendsto_fwdMap_of_isForwardSol_real hWc hW0 t.coe_nonneg hu
  have hshift : Tendsto (fun z : ℂ => z - x) (𝓝[H] ((x + p : ℝ) : ℂ)) (𝓝[H] (p : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · have h1 : Tendsto (fun z : ℂ => z - x) (𝓝 ((x + p : ℝ) : ℂ)) (𝓝 (((x + p : ℝ) : ℂ) - x)) :=
        (continuous_id.sub continuous_const).tendsto _
      have h2 : ((x + p : ℝ) : ℂ) - x = p := by push_cast; ring
      rw [h2] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · have hz' : 0 < z.im := hz
      show 0 < (z - x).im
      simpa using hz'
  rw [hmap]
  have hlim := (hT.comp hshift).const_add ((x : ℂ) + (W t : ℂ))
  have hval : (x : ℂ) + (W t : ℂ) + u t = ((x + v t : ℝ) : ℂ) := by
    simp only [hudef, Real.toNNReal_coe]
    push_cast
    ring
  rw [hval] at hlim
  refine hlim.congr fun z => ?_
  simp only [Function.comp_apply, physMap]

/-! ### `ChainReg` from the marginal paths -/

section Reg

variable {Ω : Type*}

/-- **`ChainReg` from the two paths**: curve `j`'s driver is continuous before a lifetime `ζj' ≥ ζj`, curve `k`'s
before `ζk`, both start at `0`, live times are before `ζk`, and at every live time the image source is the boundary
value of `g_t` at `xj`. -/
theorem chainReg_of_paths {live : ℝ≥0 → Ω → Prop} {xj : ℝ} {Wj : ℝ≥0 → Ω → ℝ} {ζj ζj' : Ω → ℝ≥0∞} {xk : ℝ}
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} {src : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hj : ContinuousOn (Wj · ω) {t | (t : ℝ≥0∞) < ζj' ω}) (hjle : ζj ω ≤ ζj' ω) (hj0 : Wj 0 ω = 0)
    (hk : ContinuousOn (Wk · ω) {t | (t : ℝ≥0∞) < ζk ω}) (hk0 : Wk 0 ω = 0)
    (hlive : ∀ t, live t ω → (t : ℝ≥0∞) < ζk ω)
    (hsrc : ∀ t, live t ω → Tendsto (physMap xk (Strip.extPath (Wk · ω)) t) (𝓝[H] (xj : ℂ))
      (𝓝 (src t ω : ℂ))) :
    ChainReg live xj Wj ζj xk Wk src ω := by
  have hjc : ∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (Wj · ω)) (Icc 0 T) :=
    fun T hT => continuousOn_extPath_Icc hj (hT.trans_le hjle)
  refine ⟨hjc, hj0, hk0, fun t ht => ⟨exists_continuousOn_extPath_beyond hk (hlive t ht), fun hc => ?_⟩⟩
  exact (imgDrv_zero_eq_of_tendsto hjc (extPath_zero_of hj0) (exists_continuousOn_extPath_beyond hk (hlive t ht))
    (extPath_zero_of hk0) t.coe_nonneg hc (hsrc t ht)).symm

end Reg

end InteractingSLE.ZhanGT4.A1Ref
