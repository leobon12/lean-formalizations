/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessPullFlow
import InteractingSLE.Spec.Sec7.ContinuityTargetChange
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The hulls of the retargeted chain are the images of the original hulls

Packet PROVE-SEC7-C10 (step R6 of `planning/handoffs/PROVE-SEC7-C8.md`; Specification §7.3, pp. 378–379: "The
target-change identity for the force-point equations is used only until the old and new targets are separated";
supplement Lemma LP9, p. 486). Let `W` drive a Loewner chain with a force point `V` (the new target, started at
`x_k > 0`) strictly right of the driver before `T`. The new driver `W̃ = M(W) ∘ C⁻¹` (`newPath … (mobPath … w)`)
generates, at the new time `C(t)`, exactly the image of the original hull under the target change
`ψ(z) = z/(x_k − z)`:

  `K̃_{C(t)} = ψ(K_t)`  for `t < T`    (`fwdHull_newPath_eq`),

and `g̃_{C(t)} ∘ ψ = M_t ∘ g_t` off `K_t` (`gmap_newPath_targetChange`).

Proof: a point `z ∉ K_t` has a forward solution beyond `t`, which the retargeting family carries to a forward
solution of `W̃` from `ψ(z)` beyond `C(t)` (`isForwardSol_retarget`); conversely `g_t` maps `ℍ \ K_t` onto `ℍ`,
`M_t` maps `ℍ` onto `ℍ`, and `g̃_{C(t)}` is injective off `K̃_{C(t)}`, so every point off `K̃_{C(t)}` is such an
image. The drivers are extended continuously from `[0, t₂]` (`t < t₂ < T`) by projection.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H IsForwardSol fwdHull fwdMap)

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### Continuous extensions by projection -/

/-- A function on `[0, S]` extended to `ℝ` by projection onto `[0, S]`. -/
def projExt (f : ℝ → ℝ) (S : ℝ) (hS : 0 ≤ S) (s : ℝ) : ℝ := f (projIcc 0 S hS s)

theorem continuous_projExt {f : ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S) (hf : ContinuousOn f (Icc 0 S)) :
    Continuous (projExt f S hS) :=
  hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc 0 S hS s).2

theorem projExt_eq {f : ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S) {s : ℝ} (hs : s ∈ Icc 0 S) : projExt f S hS s = f s := by
  simp only [projExt, projIcc_of_mem hS hs]

/-! ### The image of a point -/

section Hull

variable {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} {xk : ℝ}

/-- `M_t` maps `ℍ` into `ℍ`. -/
theorem mobC_mem_H (hxk : 0 < xk) (t : ℝ) {ζ : ℂ} (hζ : ζ ∈ H) : mobC xk w vk t ζ ∈ H := by
  have hζ' : 0 < ζ.im := hζ
  show 0 < (mobC xk w vk t ζ).im
  have hne : ((vk t.toNNReal : ℝ) : ℂ) - ζ ≠ 0 := fun he => by
    have := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
    linarith
  simp only [mobC, Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_im, Complex.ofReal_re,
    Complex.sub_im, Complex.sub_re, zero_sub]
  have hns : 0 < Complex.normSq (((vk t.toNNReal : ℝ) : ℂ) - ζ) := Complex.normSq_pos.2 hne
  have hα := alpha_pos hxk w vk t
  have : 0 * (vk t.toNNReal - ζ.re) / Complex.normSq (((vk t.toNNReal : ℝ) : ℂ) - ζ) -
      alpha xk w vk t * -ζ.im / Complex.normSq (((vk t.toNNReal : ℝ) : ℂ) - ζ) =
      alpha xk w vk t * ζ.im / Complex.normSq (((vk t.toNNReal : ℝ) : ℂ) - ζ) := by ring
  rw [this]
  positivity

/-- `M_t` maps `ℍ` onto `ℍ`: `M_t(V_t − α_t/(a − β_t)) = a`. -/
theorem exists_mobC_eq (hxk : 0 < xk) (t : ℝ) {a : ℂ} (ha : a ∈ H) :
    ∃ ζ ∈ H, mobC xk w vk t ζ = a := by
  have ha' : 0 < a.im := ha
  have hne : a - (beta xk w vk t : ℂ) ≠ 0 := fun he => by
    have := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at this
    linarith
  have hα := alpha_pos hxk w vk t
  have hα' : (alpha xk w vk t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hα.ne'
  refine ⟨((vk t.toNNReal : ℝ) : ℂ) - (alpha xk w vk t : ℂ) / (a - beta xk w vk t), ?_, ?_⟩
  · show 0 < (((vk t.toNNReal : ℝ) : ℂ) - (alpha xk w vk t : ℂ) / (a - beta xk w vk t)).im
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.div_im, Complex.ofReal_re, sub_zero]
    have hns : 0 < Complex.normSq (a - (beta xk w vk t : ℂ)) := Complex.normSq_pos.2 hne
    have : -(0 * (a - (beta xk w vk t : ℂ)).re / Complex.normSq (a - (beta xk w vk t : ℂ)) -
        alpha xk w vk t * a.im / Complex.normSq (a - (beta xk w vk t : ℂ))) =
        alpha xk w vk t * a.im / Complex.normSq (a - (beta xk w vk t : ℂ)) := by ring
    rw [this]
    positivity
  · simp only [mobC]
    rw [sub_sub_cancel]
    field_simp
    ring

/-- `ψ(z) = M_0(z)`. -/
theorem targetChange_eq_mobC (h0 : vk 0 = xk) {z : ℂ} (hz : z ∈ H) :
    Sec7.targetChange xk z = mobC xk w vk 0 z := by
  have hne : (xk : ℂ) - z ≠ 0 := fun he => by
    have := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
    have hz' : 0 < z.im := hz
    linarith
  rw [mobC_zero h0 hne]
  rfl

end Hull

/-! ### The hull identity -/

/-- The original data used by the pullback: `x_k > 0`, `w 0 = 0`, and before `T` the target `V` is separated from
the driver and follows the Loewner flow. -/
structure PullData (w vk : ℝ≥0 → ℝ) (xk : ℝ) (T : ℝ≥0∞) : Prop where
  pos : 0 < xk
  w_zero : w 0 = 0
  sep : SepUpTo w vk T
  target : TargetEq w vk xk T

/-- The new driver `W̃ = M(W) ∘ C⁻¹` on `ℝ≥0`. -/
abbrev newDrv (xk : ℝ) (w vk : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := newPath xk w vk (mobPath xk w vk w)

section Main

variable {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} {xk : ℝ}

theorem PullData.vk_zero (hd : PullData w vk xk T) (hT : 0 < T) : vk 0 = xk := by
  have := hd.target 0 (by simpa using hT)
  simpa using this

/-- `M(W)` at time `0` is `0`. -/
theorem PullData.mobPath_zero (hd : PullData w vk xk T) (hT : 0 < T) : mobPath xk w vk w 0 = 0 := by
  simp only [mobPath, Real.toNNReal_zero, hd.w_zero]
  rw [mob_zero (hd.vk_zero hT) (by linarith [hd.pos])]
  simp

/-- The continuous extensions of the two drivers from `[0, S]` and `[0, C(S)]`, and the two local facts
(`A`: images of points off the hull; `B`: every point off the new hull is such an image). -/
theorem PullData.local_hull (hd : PullData w vk xk T) {S : ℝ≥0} (hST : (S : ℝ≥0∞) < T) :
    ∃ (W' Wn' : ℝ → ℝ), Continuous W' ∧ Continuous Wn' ∧ W' 0 = 0 ∧ Wn' 0 = 0 ∧
      (∀ s ∈ Icc (0 : ℝ) S, W' s = w s.toNNReal) ∧
      (∀ r ∈ Icc (0 : ℝ) (clk (rate xk w vk) S), Wn' r = newDrv xk w vk r.toNNReal) ∧
      ∀ t : ℝ≥0, t < S →
        (∀ z ∈ H \ fwdHull W' t, Sec7.targetChange xk z ∈ H \ fwdHull Wn' (clk (rate xk w vk) t) ∧
          fwdMap Wn' (clk (rate xk w vk) t) (Sec7.targetChange xk z) + Wn' (clk (rate xk w vk) t) =
            mobC xk w vk t (fwdMap W' t z + W' t)) ∧
        ∀ w' ∈ H \ fwdHull Wn' (clk (rate xk w vk) t), ∃ z ∈ H \ fwdHull W' t,
          Sec7.targetChange xk z = w' := by
  have hT0 : 0 < T := lt_of_le_of_lt bot_le hST
  have h := hd.sep.isSep_of_lt hST
  have hS : (0 : ℝ) ≤ S := S.coe_nonneg
  have hxk := hd.pos
  have hR := h.isRate hxk
  have hC : 0 ≤ clk (rate xk w vk) S := hR.clk_nonneg ⟨hS, le_rfl⟩
  have hk : ∀ s ∈ Icc 0 (S : ℝ), vk s.toNNReal = xk + ∫ u in (0 : ℝ)..s, 2 / (vk u.toNNReal - w u.toNNReal) :=
    hd.target.eq_real (by rwa [Real.toNNReal_coe])
  have hv0 := hd.vk_zero hT0
  set W' := projExt (fun s : ℝ => w s.toNNReal) S hS with hW'
  set Wn' := projExt (fun r => mobPath xk w vk w (invClk (rate xk w vk) r)) (clk (rate xk w vk) S) hC with hWn'
  have hW'c : Continuous W' := continuous_projExt hS h.cont_w
  have hWn'c : Continuous Wn' := continuous_projExt hC
    (h.continuousOn_mobPath_w.comp hR.continuousOn_invClk fun r hr => hR.invClk_mem hr)
  have hW'0 : W' 0 = 0 := by rw [hW', projExt_eq hS ⟨le_rfl, hS⟩]; simpa using hd.w_zero
  have hWn'0 : Wn' 0 = 0 := by
    rw [hWn', projExt_eq hC ⟨le_rfl, hC⟩, invClk_zero_eq]; exact hd.mobPath_zero hT0
  have hW'eq : ∀ s ∈ Icc (0 : ℝ) S, W' s = w s.toNNReal := fun s hs => projExt_eq hS hs
  have hWn'eq : ∀ r ∈ Icc (0 : ℝ) (clk (rate xk w vk) S),
      Wn' r = mobPath xk w vk w (invClk (rate xk w vk) r) := fun r hr => projExt_eq hC hr
  refine ⟨W', Wn', hW'c, hWn'c, hW'0, hWn'0, hW'eq, fun r hr => ?_, fun t htS => ?_⟩
  · rw [hWn'eq r hr]
    simp only [newDrv, newPath, Real.coe_toNNReal _ hr.1]
  have htS' : (t : ℝ) < S := by exact_mod_cast htS
  have htI : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.coe_nonneg, htS'.le⟩
  have hclkt : 0 ≤ clk (rate xk w vk) t := hR.clk_nonneg htI
  -- (A) images of points off the hull
  have hA : ∀ z ∈ H \ fwdHull W' t, Sec7.targetChange xk z ∈ H \ fwdHull Wn' (clk (rate xk w vk) t) ∧
      fwdMap Wn' (clk (rate xk w vk) t) (Sec7.targetChange xk z) + Wn' (clk (rate xk w vk) t) =
        mobC xk w vk t (fwdMap W' t z + W' t) := by
    intro z hz
    obtain ⟨hzim, T', hT't, u, hu⟩ := (QuantumZipper.FwdHolo.mem_compl_fwdHull_iff t.coe_nonneg).1 hz
    set T'' := min T' (S : ℝ) with hT''
    have hT''0 : 0 ≤ T'' := le_min (t.coe_nonneg.trans hT't.le) hS
    have htT'' : (t : ℝ) < T'' := lt_min hT't htS'
    have hu' : IsForwardSol (fun s : ℝ => w s.toNNReal) z T'' u :=
      QuantumZipper.isForwardSol_congr_drive (fun r hr => hW'eq r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩)
        (QuantumZipper.isForwardSol_restrict hu hT''0 (min_le_left _ _))
    have hT''I : T'' ∈ Icc 0 (S : ℝ) := ⟨hT''0, min_le_right _ _⟩
    have hclkS : clk (rate xk w vk) T'' ≤ clk (rate xk w vk) S :=
      hR.clk_le_clk hT''I ⟨hS, le_rfl⟩ |>.2 hT''I.2
    have hsol := isForwardSol_retarget (h.mono hT''0 hT''I.2) hxk
      (fun s hs => hk s ⟨hs.1, hs.2.trans hT''I.2⟩)
      (Wn := Wn') (fun r hr => hWn'eq r ⟨hr.1, hr.2.trans hclkS⟩) hzim hu'
    have hψ : Sec7.targetChange xk z = mobC xk w vk 0 z := targetChange_eq_mobC hv0 hz.1
    have hlt : clk (rate xk w vk) t < clk (rate xk w vk) T'' :=
      hR.clk_lt htI hT''I htT''
    have hψH : mobC xk w vk 0 z ∈ H := mobC_mem_H hxk 0 hz.1
    refine ⟨?_, ?_⟩
    · rw [hψ]
      exact (QuantumZipper.FwdHolo.mem_compl_fwdHull_iff hclkt).2
        ⟨hψH, _, hlt, _, hsol⟩
    · rw [hψ, QuantumZipper.fwdMap_eq hWn'c hψH hsol ⟨hclkt, hlt.le⟩,
        QuantumZipper.fwdMap_eq hW'c hzim hu ⟨t.coe_nonneg, hT't.le⟩]
      simp only [newFlow]
      rw [hR.invClk_clk htI, hWn'eq _ ⟨hclkt, (hR.clk_le_clk htI ⟨hS, le_rfl⟩).2 htS'.le⟩,
        hR.invClk_clk htI, hW'eq _ htI]
      ring
  refine ⟨hA, fun w' hw' => ?_⟩
  -- (B) every point off the new hull is an image
  have hmo' := isMapOut_fwdMap hWn'c hWn'0 hclkt
  have hmo := isMapOut_fwdMap hW'c hW'0 t.coe_nonneg
  have ha : fwdMap Wn' (clk (rate xk w vk) t) w' + Wn' (clk (rate xk w vk) t) ∈ H := hmo'.1.2.mapsTo hw'
  obtain ⟨ζ, hζH, hζ⟩ := exists_mobC_eq (w := w) (vk := vk) hxk t ha
  obtain ⟨z, hz, hzζ⟩ := hmo.1.2.surjOn hζH
  obtain ⟨hψz, hmap⟩ := hA z hz
  refine ⟨z, hz, hmo'.1.2.injOn hψz hw' ?_⟩
  simp only at hzζ ⊢
  rw [hmap, hzζ, hζ]

/-- **The hull identity** (R6): before the separation, the hull of the new driver at the new time `C(t)` is the
image of the original hull under `ψ(z) = z/(x_k − z)`. -/
theorem PullData.fwdHull_newDrv_eq (hd : PullData w vk xk T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    fwdHull (fun r : ℝ => newDrv xk w vk r.toNNReal) (clk (rate xk w vk) t) =
      Sec7.targetChange xk '' fwdHull (fun s : ℝ => w s.toNNReal) t := by
  obtain ⟨S, htS, hST⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htS' : t < S := ENNReal.coe_lt_coe.1 htS
  obtain ⟨W', Wn', -, -, -, -, hW'eq, hWn'eq, hloc⟩ := hd.local_hull hST
  obtain ⟨hA, hB⟩ := hloc t htS'
  have hR := (hd.sep.isSep_of_lt hST).isRate hd.pos
  have htI : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.coe_nonneg, by exact_mod_cast htS'.le⟩
  have hclk : clk (rate xk w vk) t < clk (rate xk w vk) S :=
    hR.clk_lt htI ⟨S.coe_nonneg, le_rfl⟩ (by exact_mod_cast htS')
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull W' t :=
    fwdHull_eq_of_eqOn t.coe_nonneg (by exact_mod_cast htS') fun r hr => (hW'eq r hr).symm
  have hK' : fwdHull (fun r : ℝ => newDrv xk w vk r.toNNReal) (clk (rate xk w vk) t) =
      fwdHull Wn' (clk (rate xk w vk) t) :=
    fwdHull_eq_of_eqOn (hR.clk_nonneg htI) hclk fun r hr => (hWn'eq r hr).symm
  have hbij := Sec7.bijOn_targetChange_H hd.pos
  rw [hK, hK']
  ext w'
  constructor
  · intro hw'
    have hw'H : w' ∈ H := (QuantumZipper.fwdHull_mono).2 _ hw'
    obtain ⟨z, hzH, rfl⟩ := hbij.surjOn hw'H
    refine ⟨z, ?_, rfl⟩
    by_contra hzK
    exact (hA z ⟨hzH, hzK⟩).1.2 hw'
  · rintro ⟨z, hzK, rfl⟩
    have hzH : z ∈ H := (QuantumZipper.fwdHull_mono).2 _ hzK
    by_contra hψ
    obtain ⟨z', hz', he⟩ := hB _ ⟨hbij.mapsTo hzH, hψ⟩
    exact hz'.2 (hbij.injOn hz'.1 hzH he ▸ hzK)

/-- **The conjugation** (R6): `g̃_{C(t)} ∘ ψ = M_t ∘ g_t` on `ℍ \ K_t` before the separation. -/
theorem PullData.gmap_newDrv_targetChange (hd : PullData w vk xk T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) {z : ℂ}
    (hz : z ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) t) :
    fwdMap (fun r : ℝ => newDrv xk w vk r.toNNReal) (clk (rate xk w vk) t) (Sec7.targetChange xk z) +
        newDrv xk w vk (clk (rate xk w vk) t).toNNReal =
      mobC xk w vk t (fwdMap (fun s : ℝ => w s.toNNReal) t z + w t) := by
  obtain ⟨S, htS, hST⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htS' : t < S := ENNReal.coe_lt_coe.1 htS
  obtain ⟨W', Wn', -, -, -, -, hW'eq, hWn'eq, hloc⟩ := hd.local_hull hST
  obtain ⟨hA, -⟩ := hloc t htS'
  have hR := (hd.sep.isSep_of_lt hST).isRate hd.pos
  have htI : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.coe_nonneg, by exact_mod_cast htS'.le⟩
  have hclkt := hR.clk_nonneg htI
  have hclkI : clk (rate xk w vk) t ∈ Icc 0 (clk (rate xk w vk) S) :=
    ⟨hclkt, (hR.clk_le_clk htI ⟨S.coe_nonneg, le_rfl⟩).2 htI.2⟩
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull W' t :=
    fwdHull_eq_of_eqOn t.coe_nonneg (by exact_mod_cast htS') fun r hr => (hW'eq r hr).symm
  rw [hK] at hz
  have h1 := (hA z hz).2
  rw [fwdMap_eq_of_eqOn hclkt fun r hr => (hWn'eq r ⟨hr.1, hr.2.trans hclkI.2⟩).symm,
    fwdMap_eq_of_eqOn t.coe_nonneg fun r hr => (hW'eq r ⟨hr.1, hr.2.trans htI.2⟩).symm,
    ← hWn'eq _ hclkI, h1, hW'eq _ htI]
  simp

end Main

end Retarget

end Zhan

end InteractingSLE
