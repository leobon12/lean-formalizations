/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenFinal
import InteractingSLE.Spec.Sec7.PocketTraversalCoords

/-!
# Geometric force coordinates through boundary collisions before killing

PROVE-CROSSCOND-GEN. The global geometric force-path and null-collision theorems
already apply to every continuous driver. Localize them before a finite lifetime.
This removes the strict-gap premise of the earlier killed-arc force-path adapter.
No new boundary classification or stochastic differential equation is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open Ito WangWu.ImgWord MartChar.RealFlow Sec7.PhaseSelAdapt

/-- A driver continuous before its lifetime has continuous compact extensions. -/
theorem isLocCont_rpath {w : ℝ≥0 → ℝ} {L : WithTop ℝ≥0}
    (hw : ContinuousOn w {t | (t : WithTop ℝ≥0) < L}) : IsLocCont (rpath w) L := by
  intro t ht
  obtain ⟨R, htR, hRL⟩ := WithTop.lt_iff_exists_coe_btwn.1 ht
  have htR' : (t : ℝ) < R := by exact_mod_cast htR
  have hc := continuous_clampDrv R.coe_nonneg (continuousOn_rpath hw hRL)
  exact ⟨R, htR', clampDrv (rpath w) R, hc, fun r hr => (clampDrv_eqOn hr).symm⟩

/-- The collision set of a locally continuous killed geometric coordinate is null.
Each collision has a neighborhood covered by the global null-collision theorem. -/
theorem volume_collision_kImg_of_locCont {p : ℝ → ℝ} {L : WithTop ℝ≥0}
    (hp : IsLocCont p L) (x : ℝ) :
    volume {u : ℝ | 0 ≤ u ∧ ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) < L ∧
      kImg p x u.toNNReal = p u} = 0 := by
  let C := {u : ℝ | 0 ≤ u ∧ ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) < L ∧
    kImg p x u.toNNReal = p u}
  refine measure_null_of_locally_null C fun u hu => ?_
  obtain ⟨c, huc, w, hw, h⟩ := hp u.toNNReal hu.2.1
  rw [Real.coe_toNNReal _ hu.1] at huc
  refine ⟨C ∩ Iio c, inter_mem_nhdsWithin C (Iio_mem_nhds huc), ?_⟩
  refine measure_mono_null (fun r hr => ?_) (volume_rightImg_eq_zero hw x)
  have hrc : ((r.toNNReal : ℝ≥0) : ℝ) ≤ c := by
    rw [Real.coe_toNNReal _ hr.1.1]
    exact hr.2.le
  have he := hr.1.2.2
  rw [kImg_eq hw h hrc, Real.coe_toNNReal _ hr.1.1, h ⟨hr.1.1, hr.2.le⟩] at he
  exact ⟨hr.1.1, he⟩

/-- A locally continuous killed geometric coordinate is a force path even at
allowed one-sided collisions. -/
theorem isForcePathBefore_kImg_of_locCont {p : ℝ → ℝ} {L : WithTop ℝ≥0}
    (hp : IsLocCont p L) (x : ℝ) :
    IsForcePathBefore (fun t : ℝ≥0 => p t) (kImg p x) L := by
  refine ⟨hp.continuousOn_kImg x, fun u hu huL hne => ?_, ?_⟩
  · have hcu := Real.coe_toNNReal u hu.le
    have hd := hp.hasDerivAt_kImg x hu huL (by simpa only [hcu] using hne)
    simpa only [hcu] using hd
  · refine measure_mono_null (fun u hu => ?_) (volume_collision_kImg_of_locCont hp x)
    exact ⟨hu.1, hu.2.1, by simpa only [Real.coe_toNNReal _ hu.1] using hu.2.2⟩

/-- Right labels are geometric images before the available lifetime and zero after. -/
def imageGeomR {Ω : Type*} {n : ℕ} (W : ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (x : Ω → Fin n → ℝ) : Fin n → ℝ≥0 → Ω → ℝ :=
  open scoped Classical in fun i t ω => if (t : WithTop ℝ≥0) < T ω then kImg (rpath (W · ω)) (x ω i) t else 0

/-- Left labels are the reflected geometric images, with the same killing rule. -/
def imageGeomL {Ω : Type*} {n : ℕ} (W : ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (x : Ω → Fin n → ℝ) : Fin n → ℝ≥0 → Ω → ℝ :=
  open scoped Classical in fun i t ω => if (t : WithTop ℝ≥0) < T ω then
    -kImg (fun r => -rpath (W · ω) r) (-x ω i) t else 0

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}
  {nL nR : ℕ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}

/-- Geometric force coordinates of any driver continuous before killing satisfy
all deterministic contact-word requirements. Earlier boundary hits are permitted. -/
theorem isContactWord_imageGeom
    (hW : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hW0 : ∀ ω, W 0 ω = 0) (hL : ∀ ω, Antitone (xL ω)) (hR : ∀ ω, Monotone (xR ω)) :
    IsContactWord W (imageGeomL W T xL) (imageGeomR W T xR) T := by
  have hp : ∀ ω, IsLocCont (rpath (W · ω)) (T ω) := fun ω => isLocCont_rpath (hW ω)
  have heW : ∀ ω (t : ℝ≥0), rpath (W · ω) t = W t ω := fun ω t => by
    simp only [rpath, Real.toNNReal_coe]
  refine ⟨hW0, hW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω t i ht
    have h := (hp ω).neg.le_kImg ht (-xL ω i)
    simpa only [imageGeomL, ht, ↓reduceIte, heW, neg_neg] using neg_le_neg h
  · intro ω t j ht
    simpa only [imageGeomR, ht, ↓reduceIte, heW] using (hp ω).le_kImg ht (xR ω j)
  · intro ω i
    have h := isForcePathBefore_neg (isForcePathBefore_kImg_of_locCont (hp ω).neg (-xL ω i))
    simp only [neg_neg, heW] at h
    exact isForcePathBefore_congr h fun t ht => by simp only [imageGeomL, ht, ↓reduceIte]
  · intro ω j
    have h := isForcePathBefore_kImg_of_locCont (hp ω) (xR ω j)
    simp only [heW] at h
    exact isForcePathBefore_congr h fun t ht => by simp only [imageGeomR, ht, ↓reduceIte]
  · intro ω i a ha b hb hab
    have ha' : (a : WithTop ℝ≥0) < T ω := ha
    have hb' : (b : WithTop ℝ≥0) < T ω := hb
    simpa only [imageGeomL, ha', hb', ↓reduceIte, neg_le_neg_iff] using
      (hp ω).neg.kImg_mono_time hb hab (-xL ω i)
  · intro ω j a ha b hb hab
    have ha' : (a : WithTop ℝ≥0) < T ω := ha
    have hb' : (b : WithTop ℝ≥0) < T ω := hb
    simpa only [imageGeomR, ha', hb', ↓reduceIte] using (hp ω).kImg_mono_time hb hab (xR ω j)
  · intro ω t ht i j hij
    simpa only [imageGeomL, ht, ↓reduceIte, neg_le_neg_iff] using
      (hp ω).neg.kImg_mono_index ht (neg_le_neg (hL ω hij))
  · intro ω t ht i j hij
    simpa only [imageGeomR, ht, ↓reduceIte] using (hp ω).kImg_mono_index ht (hR ω hij)
  · intro ω i j s t hst ht heq
    have hs := lt_of_le_of_lt (WithTop.coe_le_coe.2 hst) ht
    simp only [imageGeomL, hs, ht, ↓reduceIte, neg_inj] at heq ⊢
    exact (hp ω).neg.kImg_merge hst ht heq
  · intro ω i j s t hst ht heq
    have hs := lt_of_le_of_lt (WithTop.coe_le_coe.2 hst) ht
    simp only [imageGeomR, hs, ht, ↓reduceIte] at heq ⊢
    exact (hp ω).kImg_merge hst ht heq
  · intro ω t ht0 ht i j hli hri
    obtain ⟨c, htc, w, hw, he⟩ := hp ω t ht
    have hen : EqOn (fun r => -rpath (W · ω) r) (fun r => -w r) (Icc 0 c) :=
      fun r hr => congrArg Neg.neg (he hr)
    simp only [imageGeomL, imageGeomR, ht, ↓reduceIte,
      kImg_eq hw he htc.le, kImg_eq hw.neg hen htc.le] at hli hri
    change -rightImg (fun r => -w r) (-xL ω i) t = W t ω at hli
    have hsep := rightImg_add_rightImg_neg_ge hw (xR ω j) (-xL ω i) t.coe_nonneg
    have hpos : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast ht0)
    linarith

end InteractingSLE.Sec5.CrossCond.Gen
