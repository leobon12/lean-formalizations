/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartFilt2
import InteractingSLE.WangWu.ReverseContactMartFilt2Glue
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Spec.Sec7.Lemma71Capacity

/-!
# The fixed-image-time chart clause, step R1: B14's image chain is the explicit image word

Packet PROVE-WW-B19, step R1 of PROVE-WW-B18's plan (Astra's follow-up note, Part E.3: "the conditional mean is
exactly the bounded canonical Poisson mean of the finite boundary word in the two-slit complement"). The explicit
conditional law of the history-marked two-slit union (`ae_condExp_cexp_twoSlit_glue`, PROVE-WW-B18) is written with
**some** continuous driver `W'` of the image hull `Ψ(A_t)` (B14's `exists_imageTrace`). This file identifies it,
deterministically, with the explicit killed image word of PROVE-WW-B17:

* `image_Icc_subset_of_arc`: an initial piece of a second parametrization of a simple arc is an initial piece of the
  first (the inverse of a continuous injection of a compact interval is continuous);
* **`IsKilledArc.eqOn_chainDrv_of_fwdHull_eq`**: a continuous driver of a simple proper trace whose hull at time `T`
  is the prefix `γ((0, t])` of a killed arc has `T = σ(t)` (the capacity clock) and agrees with the glued driver
  `chainDrv γ P` on `[0, T]`;
* `rightImg_sub_eq_re_fwdMap`, `neg_rightImg_neg_sub_eq_re_fwdMap`: the geometric images of alive real points are the
  real parts of the forward map;
* **`meanCan_img_eq_chartMean`**: at `κ = 4`, the explicit mean `meanCan` of the image word at the image time `σ(t)` is
  B14's `chartMean` of `(W', T)` composed with `f'_T` (the four marks `0∓`, `Ψ(∞∓)` flow to `chartAL/AR/BL/BR`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open ImgWord LawUnique MartChar.RealFlow

/-! ### Initial pieces of a simple arc -/

/-- **Initial pieces of a simple arc.** If `f` is continuous and injective on `[0, a]`, `g` is continuous on `[0, b]`
with `g([0, b]) ⊆ f([0, a])` and `g 0 = f 0`, and `g c = f d`, then `f([0, d]) ⊆ g([0, c])`. -/
theorem image_Icc_subset_of_arc {f g : ℝ → ℂ} {a b c d : ℝ} (hf : ContinuousOn f (Icc 0 a))
    (hfi : InjOn f (Icc 0 a)) (hg : ContinuousOn g (Icc 0 b)) (hgf : g '' Icc 0 b ⊆ f '' Icc 0 a)
    (h0 : g 0 = f 0) (hc : c ∈ Icc 0 b) (hd : d ∈ Icc 0 a) (hcd : g c = f d) :
    f '' Icc 0 d ⊆ g '' Icc 0 c := by
  have he : Continuous ((Icc 0 a).domRestrict f) := hf.domRestrict
  have hei : Function.Injective ((Icc 0 a).domRestrict f) := fun x y h => Subtype.ext (hfi x.2 y.2 h)
  have : CompactSpace (Icc (0 : ℝ) a) := isCompact_iff_compactSpace.1 isCompact_Icc
  have hemb := he.isClosedEmbedding hei
  set S : Set (Icc (0 : ℝ) a) := (Icc 0 a).domRestrict f ⁻¹' (g '' Icc 0 c) with hS_def
  have hS : (Icc 0 a).domRestrict f '' S = g '' Icc 0 c := by
    refine image_preimage_eq_of_subset fun z hz => ?_
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨y, hy, hyx⟩ := hgf ⟨x, ⟨hx.1, hx.2.trans hc.2⟩, rfl⟩
    exact ⟨⟨y, hy⟩, hyx⟩
  have hconn : IsPreconnected (g '' Icc 0 c) :=
    isPreconnected_Icc.image g (hg.mono (Icc_subset_Icc_right hc.2))
  have hSc : IsPreconnected S := hemb.isInducing.isPreconnected_image.1 (hS ▸ hconn)
  have hSr : IsPreconnected (((↑) : Icc (0 : ℝ) a → ℝ) '' S) :=
    hSc.image _ continuous_subtype_val.continuousOn
  have h0S : (0 : ℝ) ∈ (((↑) : Icc (0 : ℝ) a → ℝ) '' S) :=
    ⟨⟨0, ⟨le_rfl, hd.1.trans hd.2⟩⟩, ⟨0, ⟨le_rfl, hc.1⟩, h0⟩, rfl⟩
  have hdS : d ∈ (((↑) : Icc (0 : ℝ) a → ℝ) '' S) := ⟨⟨d, hd⟩, ⟨c, ⟨hc.1, le_rfl⟩, hcd⟩, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hSr.Icc_subset h0S hdS hx
  rw [← hyx]
  exact hy

/-- The image of `(0, u]` is the image of `[0, u]` in `ℍ` when `f 0 = 0` and `f((0, u]) ⊆ ℍ`. -/
theorem image_Ioc_eq_inter_H {f : ℝ → ℂ} {u : ℝ} (h0 : f 0 = 0) (hH : ∀ x ∈ Ioc 0 u, f x ∈ H) :
    f '' Ioc 0 u = f '' Icc 0 u ∩ H := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, Ioc_subset_Icc_self hx, rfl⟩, hH x hx⟩
  · rintro ⟨⟨x, hx, rfl⟩, hzH⟩
    rcases hx.1.eq_or_lt with h | h
    · rw [← h, h0] at hzH
      exact absurd (show (0 : ℝ) < (0 : ℂ).im from hzH) (lt_irrefl _)
    · exact ⟨x, ⟨h, hx.2⟩, rfl⟩

/-! ### The glued driver from the final hull -/

variable {γ : ℝ → ℂ} {P : Set ℝ}

/-- **A driver of a simple trace with the hull `γ((0, t])` at time `T` is the glued driver**, and `T = σ(t)`. -/
theorem IsKilledArc.eqOn_chainDrv_of_fwdHull_eq (hγ : IsKilledArc γ P) {t : ℝ} (ht : t ∈ P) (ht0 : 0 < t)
    {W' : ℝ → ℝ} (hW' : Continuous W') (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') {T : ℝ} (hT : 0 < T) (hK : fwdHull W' T = γ '' Ioc 0 t) :
    T = capClock γ t ∧ EqOn W' (chainDrv γ P) (Icc 0 T) := by
  have hcapT : capClock γ t = T := by
    have h1 := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW' hW'0 hT.le (hK.trans (hγ.fillH_eq ht).symm)
    rw [capClock, h1]
    ring
  obtain ⟨Wl, hWl, hWl0, hEq, hKl⟩ := hγ.chainDrv_spec ht ht0
  have hsub := hγ.icc t ht
  have hγc : ContinuousOn γ (Icc 0 t) := hγ.cont.mono hsub
  have hγi : InjOn γ (Icc 0 t) := hγ.inj.mono hsub
  have hη'c : ContinuousOn η' (Icc 0 T) := hη'p.cont.mono Icc_subset_Ici_self
  have hη'i : InjOn η' (Icc 0 T) := hη'p.inj.mono Icc_subset_Ici_self
  have hIcc : η' '' Icc 0 T = γ '' Icc 0 t := by
    rw [← Set.Ioc_insert_left hT.le, ← Set.Ioc_insert_left ht0.le, image_insert_eq, image_insert_eq, hη'p.zero,
      hγ.zero, ← fwdHull_eq_image_Ioc hη' hη'p hT.le, hK]
  have h00 : η' 0 = γ 0 := by rw [hη'p.zero, hγ.zero]
  have hhull : ∀ u ∈ Icc 0 T, fwdHull W' u = fwdHull Wl u := by
    intro u hu
    obtain ⟨v, hv, hvu⟩ : η' u ∈ γ '' Icc 0 t := hIcc ▸ mem_image_of_mem η' hu
    have h1 := image_Icc_subset_of_arc hγc hγi hη'c hIcc.le h00 hu hv hvu.symm
    have h2 := image_Icc_subset_of_arc hη'c hη'i hγc hIcc.ge h00.symm hv hu hvu
    have heq : η' '' Icc 0 u = γ '' Icc 0 v := le_antisymm h2 h1
    have hIoc : η' '' Ioc 0 u = γ '' Ioc 0 v := by
      rw [image_Ioc_eq_inter_H hη'p.zero fun x hx => hη'p.mem_H x hx.1,
        image_Ioc_eq_inter_H hγ.zero fun x hx => hγ.mem_H x (hsub ⟨hx.1.le, hx.2.trans hv.2⟩) hx.1, heq]
    have hKu : fwdHull W' u = γ '' Ioc 0 v := (fwdHull_eq_image_Ioc hη' hη'p hu.1).trans hIoc
    have hKv := hKl v hv
    have hcap : capClock γ v = u := by
      have a1 := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW' hW'0 hu.1 hKu
      have a2 := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hWl hWl0 (hγ.capClock_nonneg (hsub hv)) hKv
      linarith
    rw [hKu, ← hKv, hcap]
  refine ⟨hcapT.symm, fun u hu => ?_⟩
  rw [Sec6.eqOn_of_fwdHull_eq hW' hWl hW'0 hWl0 hT.le hhull hu]
  exact (hEq ⟨hu.1, hcapT.symm ▸ hu.2⟩).symm

/-! ### Real points -/

section RealPoints

variable {W : ℝ → ℝ} {T : ℝ}

/-- The geometric image of an alive positive real point is the real part of the forward map. -/
theorem rightImg_sub_eq_re_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {y : ℝ} (hy : 0 < y)
    {v : ℝ → ℂ} (hv : QuantumZipper.IsForwardSol W (y : ℂ) T v) :
    rightImg W y T - W T = (fwdMap W T y).re := by
  have hX := isPosSol_of_isForwardSol hW hW0 hy hv
  rw [rightImg_eq_gImg hW hT ⟨_, hX⟩, gImg, cflow_eq_of_isPosSol hW hX ⟨hT, le_rfl⟩,
    fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩]
  ring

/-- The geometric image of an alive negative real point is the real part of the forward map. -/
theorem neg_rightImg_neg_sub_eq_re_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {y : ℝ} (hy : y < 0)
    {v : ℝ → ℂ} (hv : QuantumZipper.IsForwardSol W (y : ℂ) T v) :
    -rightImg (fun s => -W s) (-y) T - W T = (fwdMap W T y).re := by
  obtain ⟨v', hv'⟩ := (exists_isForwardSol_neg_iff (W := W) (x := y) (T := T)).2 ⟨v, hv⟩
  have h := rightImg_sub_eq_re_fwdMap (W := fun s => -W s) hW.neg (by simp [hW0]) hT (neg_pos.2 hy) hv'
  have e := fwdMap_neg_real hW hv ⟨hT, le_rfl⟩
  rw [e] at h
  simp only [neg_re] at h
  linarith

end RealPoints

/-! ### The explicit mean of the image word -/

section Img

variable {Ω : Type*} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

/-- **R1: at `κ = 4`, the explicit mean of the image word at `σ(t)` is B14's chart mean of any driver of the image
hull.** -/
theorem meanCan_img_eq_chartMean (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) {p : Ω × HistorySpace 1 1}
    (hp : p ∈ E) {t : ℝ} (ht : t ∈ gPre s ζ W E p) (ht0 : 0 < t) {W' : ℝ → ℝ} (hW' : Continuous W')
    (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') {T : ℝ} (hT : 0 < T)
    (hK : fwdHull W' T = gCurve s ζ W E p '' Ioc 0 t) (rL rR : ℝ) :
    T = capClock (gCurve s ζ W E p) t ∧ ∀ y : ℂ,
      Coupling.meanCan 4 (imgρ rL) (imgρ rR) (fun r => imgW s ζ W E r p) (fun i r => imgVL s ζ W E i r p)
        (fun j r => imgVR s ζ W E j r p) T.toNNReal y =
      chartMean rL rR W' T (frzVL s p.2) (frzVR s p.2) (fwdMap W' T y) := by
  set γ := gCurve s ζ W E p with hγdef
  set P := gPre s ζ W E p with hPdef
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hs hEg p
  obtain ⟨hTc, hEqW⟩ := hγ.eqOn_chainDrv_of_fwdHull_eq ht ht0 hW' hW'0 hη' hη'p hT hK
  refine ⟨hTc, fun y => ?_⟩
  have hT' : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal _ hT.le
  have hlt : ((T.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := by
    have := hγ.lt_kLife ht
    rwa [← hTc] at this
  obtain ⟨-, hkW⟩ := hγ.kW_eq_chainDrv ht
  -- the killed path is `W'` on `[0, T]`
  have hpath : EqOn (kPath γ P) W' (Icc 0 T) := fun r hr => by
    rw [kPath, hkW r (hTc ▸ hr), hEqW hr]
  have hpathn : EqOn (fun r => -kPath γ P r) (fun r => -W' r) (Icc 0 T) := fun r hr => by
    simp only [hpath hr]
  have hWT : imgW s ζ W E T.toNNReal p = W' T := by
    exact hpath ⟨hT.le, le_rfl⟩
  -- the marks at `σ(t)`
  obtain ⟨hgood, hβ, -⟩ := hEg p hp
  obtain ⟨-, -, -, -, -, hvL, hvR⟩ := trace_of_mem_betaSet hs hβ
  have hgXL1 : gXL s E p 1 = -1 / frzVR s p.2 := by simp [gXL, hp]
  have hgXR1 : gXR s E p 1 = -1 / frzVL s p.2 := by simp [gXR, hp]
  have hVL0 : imgVL s ζ W E 0 T.toNNReal p - imgW s ζ W E T.toNNReal p = chartAL W' T := by
    rw [imgVL, kVL_of_lt _ _ hlt, kVLr, kImg_eq hW'.neg hpathn hT'.le, hWT, hT', chartAL]
    simp only [gXL, Matrix.cons_val_zero, neg_zero]
    rfl
  have hVL1 : imgVL s ζ W E 1 T.toNNReal p - imgW s ζ W E T.toNNReal p = chartBL W' T (frzVR s p.2) := by
    rw [imgVL, kVL_of_lt _ _ hlt, kVLr, kImg_eq hW'.neg hpathn hT'.le, hWT, hT', chartBL, hgXL1]
    have hx : -(frzVR s p.2)⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hvR)
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hx.ne hT.le
    rw [← neg_rightImg_neg_sub_eq_re_fwdMap hW' hW'0 hT.le hx hv]
    congr 3
    ring
  have hVR0 : imgVR s ζ W E 0 T.toNNReal p - imgW s ζ W E T.toNNReal p = chartAR W' T := by
    rw [imgVR, kVR_of_lt _ _ hlt, kVRr, kImg_eq hW' hpath hT'.le, hWT, hT', chartAR]
    simp only [gXR, Matrix.cons_val_zero]
  have hVR1 : imgVR s ζ W E 1 T.toNNReal p - imgW s ζ W E T.toNNReal p = chartBR W' T (frzVL s p.2) := by
    rw [imgVR, kVR_of_lt _ _ hlt, kVRr, kImg_eq hW' hpath hT'.le, hWT, hT', chartBR, hgXR1]
    have hx : 0 < -(frzVL s p.2)⁻¹ := neg_pos.2 (inv_lt_zero.2 hvL)
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hx.ne' hT.le
    rw [← rightImg_sub_eq_re_fwdMap hW' hW'0 hT.le hx hv]
    congr 2
    ring
  have hfwd : fwdMap (Ito.rpath fun r => imgW s ζ W E r p) (T.toNNReal : ℝ) y = fwdMap W' T y := by
    rw [hT']
    exact Ito.fwdMap_congr_of_eqOn fun r hr => hpath hr
  rw [Coupling.meanCan, chiC_four, zero_mul, sub_zero, ← condMean_eq_meanHarmonic, hfwd, chartMean]
  congr 1
  · funext i
    fin_cases i
    · exact hVL0
    · exact hVL1
  · funext j
    fin_cases j
    · exact hVR0
    · exact hVR1

end Img

end InteractingSLE.WangWu
