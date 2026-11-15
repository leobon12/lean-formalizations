/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3Split
import InteractingSLE.Foundations.Loewner.YuanTrace
import InteractingSLE.Spec.Sec7.SideHeightGeom

/-!
# A.2 part 3: contact geometry in a fixed small-prefix chart

Packet PROVE-ZHAN-A2P3-PC. The no-contact case follows from capacity growth and
the bounded displacement of the inverse map. The finite-contact argument uses
boundary limits of the small-prefix inverse map.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Bornology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

/-- The first failure of strip life occurs no later than the original lifetime. -/
theorem lifeEnd_le_lifetime (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : lifeEnd w v ζ ≤ ζ := by
  by_cases hζ : ζ = ⊤
  · rw [hζ]
    exact le_top
  · have hn : ¬ Strip.IsStripLife w v ζ ζ.toNNReal := by
      intro h
      have hh := h.1
      rw [ENNReal.coe_toNNReal hζ] at hh
      exact (lt_irrefl ζ) hh
    calc
      lifeEnd w v ζ ≤ (ζ.toNNReal : ℝ≥0∞) := iInf₂_le ζ.toNNReal hn
      _ = ζ := ENNReal.coe_toNNReal hζ

/-- Infinite contact time forces infinite lifetime of the large marginal. -/
theorem lifetime_eq_top_of_contact_eq_top {x : ℝ} {w₁ w₂ v₂ : ℝ≥0 → ℝ}
    {ζ₂ : ℝ≥0∞} {q : ℝ≥0}
    (hc : contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂)
      x (Strip.extPath w₁) q = ⊤) : ζ₂ = ⊤ := by
  apply top_unique
  calc
    ⊤ = contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂)
        x (Strip.extPath w₁) q := hc.symm
    _ ≤ lifeEnd w₂ v₂ ζ₂ := min_le_left _ _
    _ ≤ ζ₂ := lifeEnd_le_lifetime _ _ _

/-- A bounded hydrodynamic image has bounded preimage off the old hull. -/
theorem isBounded_of_isBounded_physMap {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q) {x : ℝ} {A : Set ℂ}
    (hAH : A ⊆ H) (hd : Disjoint A (physHull x W q))
    (hb : IsBounded (physMap x W q '' A)) : IsBounded A := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hq
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  refine isBounded_iff_forall_norm_le.2 ⟨C + R + ‖(x : ℂ) + W q‖ + ‖(x : ℂ)‖,
    fun z hz => ?_⟩
  have hzK : z - x ∈ H \ fwdHull W q := by
    refine ⟨mem_H_sub_ofReal (hAH hz) x, fun hk => ?_⟩
    exact hd.ne_of_mem hz ⟨z - x, hk, sub_add_cancel z _⟩ rfl
  have hfH := FwdHolo.mapsTo_fwdMap hW hq hzK
  have hi := hC _ hfH
  rw [RS.fwdMapInv_fwdMap hW hW0 hq hzK] at hi
  have him : ‖physMap x W q z‖ ≤ R := hR _ ⟨z, hz, rfl⟩
  have he : fwdMap W q (z - x) = physMap x W q z - ((x : ℂ) + W q) := by
    simp only [physMap]
    ring
  have hf : ‖fwdMap W q (z - x)‖ ≤ R + ‖(x : ℂ) + W q‖ := by
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add him le_rfl)
  calc
    ‖z‖ = ‖(z - x - fwdMap W q (z - x)) + fwdMap W q (z - x) + x‖ := by
      congr 1
      ring
    _ ≤ ‖z - x - fwdMap W q (z - x)‖ + ‖fwdMap W q (z - x)‖ + ‖(x : ℂ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C + R + ‖(x : ℂ) + W q‖ + ‖(x : ℂ)‖ := by linarith only [hi, hf]

/-- Hulls over infinite capacity time cannot all lie in one bounded set. -/
theorem not_isBounded_preContactHulls_top {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) : ¬ IsBounded (preContactHulls W ⊤) := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℂ)
  let t : ℝ≥0 := (R ^ 2 / 2 + 1).toNNReal
  have ht : (t : ℝ) = R ^ 2 / 2 + 1 := Real.coe_toNNReal _ (by positivity)
  have hsub : fwdHull W t ⊆ closedBall ((0 : ℝ) : ℂ) R := by
    intro z hz
    apply hR
    simp only [preContactHulls, mem_iUnion, physHull_zero]
    exact ⟨t, ENNReal.coe_lt_top, hz⟩
  have hcap := HPHull.hcap_le_rad_sq
    ⟨fwdHull W t, isHPHull_fwdHull hW t.coe_nonneg⟩ hsub
  rw [hcap_fwdHull hW hW0 t.coe_nonneg, ht] at hcap
  linarith only [hcap]

/-- If the contact time is infinite, the mapped large hulls are unbounded. -/
theorem not_isBounded_preContactImage_of_contact_eq_top
    {x : ℝ} {w₁ w₂ v₂ : ℝ≥0 → ℝ} {ζ₁ ζ₂ : ℝ≥0∞} {q : ℝ≥0}
    (hw₁ : ContinuousOn w₁ {s | (s : ℝ≥0∞) < ζ₁}) (hw₁0 : w₁ 0 = 0)
    (hq : (q : ℝ≥0∞) < ζ₁) (hw₂ : Continuous w₂) (hw₂0 : w₂ 0 = 0)
    (hc : contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂)
      x (Strip.extPath w₁) q = ⊤) :
    ¬ IsBounded (preContactImage x w₁ w₂ v₂ ζ₂ q) := by
  intro hb
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  let V := frozenDrive w₁ t₂
  have hV : Continuous V := continuous_frozenDrive_of_lt hw₁ ht₂
  have hV0 : V 0 = 0 := by
    rw [show V = frozenDrive w₁ t₂ from rfl, frozenDrive_zero (q.coe_nonneg.trans hqt₂.le), hw₁0]
  have he : ∀ r ∈ Icc (0 : ℝ) t₂, Strip.extPath w₁ r = V r :=
    fun r hr => (frozenDrive_eq hr).symm
  have hK : physHull x (Strip.extPath w₁) q = physHull x V q := by
    rw [physHull, physHull, fwdHull_eq_of_eqOn q.coe_nonneg hqt₂ he]
  have hM : physMap x (Strip.extPath w₁) q = physMap x V q := by
    funext z
    dsimp only [physMap]
    rw [he q ⟨q.coe_nonneg, hqt₂.le⟩,
      fwdMap_eq_of_eqOn q.coe_nonneg (fun r hr => he r ⟨hr.1, hr.2.trans hqt₂.le⟩)]
  have hd := disjoint_preContactHulls (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂)
    x (Strip.extPath w₁) q
  rw [hc, hK] at hd
  change IsBounded (physMap x (Strip.extPath w₁) q ''
    preContactHulls (Strip.extPath w₂) (contactTime 0 (Strip.extPath w₂)
      (lifeEnd w₂ v₂ ζ₂) x (Strip.extPath w₁) q)) at hb
  rw [hc, hM] at hb
  have hW₂ : Continuous (Strip.extPath w₂) := hw₂.comp continuous_real_toNNReal
  have hW₂0 : Strip.extPath w₂ 0 = 0 := by simpa only [Strip.extPath, Real.toNNReal_zero] using hw₂0
  exact not_isBounded_preContactHulls_top hW₂ hW₂0
    (isBounded_of_isBounded_physMap hV hV0 q.coe_nonneg
      (preContactHulls_subset_H _ _) hd hb)

/-- A boundary contact of a set with bounded image has a real image cluster point.
The inverse map identifies that cluster point with the original contact. -/
theorem exists_real_mem_closure_fwdMap_image {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hB : HasBdryLimits (fwdMapInv W q)) {A : Set ℂ}
    (hA : A ⊆ H \ fwdHull W q) (hb : IsBounded (fwdMap W q '' A))
    {p : ℂ} (hp : p ∈ closure A) (hpK : p ∉ H \ fwdHull W q) :
    ∃ u : ℝ, (u : ℂ) ∈ closure (fwdMap W q '' A) ∧
      extendFrom H (fwdMapInv W q) u = p := by
  obtain ⟨z, hz, hzp⟩ := mem_closure_iff_seq_limit.1 hp
  obtain ⟨a, ha, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hb
    (fun n => show fwdMap W q (z n) ∈ fwdMap W q '' A from ⟨z n, hz n, rfl⟩)
  have haH : a ∈ Hbar := by
    rw [← closure_H]
    have hmaps : fwdMap W q '' A ⊆ H := by
      rintro _ ⟨b, hb, rfl⟩
      exact FwdHolo.mapsTo_fwdMap hW hq (hA hb)
    exact closure_mono hmaps ha
  have hpre : Tendsto (fun n => fwdMapInv W q (fwdMap W q (z (φ n))))
      atTop (𝓝 p) := by
    convert hzp.comp hφ.tendsto_atTop using 1
    funext n
    exact RS.fwdMapInv_fwdMap hW hW0 hq (hA (hz _))
  have haNot : a ∉ H := by
    intro haInt
    have hF := (continuousOn_fwdMapInv hW hW0 hq a haInt).continuousAt
      (isOpen_H.mem_nhds haInt)
    have hpa : fwdMapInv W q a = p := tendsto_nhds_unique (hF.tendsto.comp hlim) hpre
    exact hpK (hpa ▸ RS.fwdMapInv_mem_compl_fwdHull hW hW0 hq haInt)
  have hai : a.im = 0 := le_antisymm (not_lt.1 haNot) haH
  have hae : a = (a.re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact hai
  refine ⟨a.re, hae ▸ ha, ?_⟩
  have hlim' : Tendsto (fun n => fwdMap W q (z (φ n))) atTop (𝓝[Hbar] a) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n =>
      show 0 ≤ (fwdMap W q (z (φ n))).im from
        (FwdHolo.mapsTo_fwdMap hW hq (hA (hz _))).le⟩
  have hExt := (hB.continuousOn a haH).tendsto.comp hlim'
  have hExt' : Tendsto (fun n => fwdMapInv W q (fwdMap W q (z (φ n))))
      atTop (𝓝 (extendFrom H (fwdMapInv W q) a)) := by
    convert hExt using 1
    funext n
    exact (extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 hq)
      (FwdHolo.mapsTo_fwdMap hW hq (hA (hz _)))).symm
  rw [← hae]
  exact tendsto_nhds_unique hExt' hpre

open MartChar.RealFlow in
/-- Every point strictly above the geometric image of a right mark is the image
of an alive real point strictly to the right of that mark. -/
theorem exists_alive_gImg_eq_of_rightImg_lt {W : ℝ → ℝ} (hW : Continuous W)
    {q x u : ℝ} (hq : 0 ≤ q) (hu : rightImg W x q < u) :
    ∃ r : ℝ, x < r ∧ Alive W r q ∧ gImg W r q = u := by
  obtain ⟨r₀, hxr₀, hr₀, hr₀u⟩ := exists_lt_of_rightImg_lt hW hq hu
  let R := max r₀ u
  have hr₀R : r₀ ≤ R := le_max_left _ _
  have hcont : ContinuousOn (fun r => gImg W r q) (Icc r₀ R) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun a ha b hb => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_gImg_sub_le hW hq (hr₀.of_le hW hb.1 hq) (hr₀.of_le hW ha.1 hq)
  have hR : u ≤ gImg W R q :=
    (le_max_right r₀ u).trans ((hr₀.of_le hW hr₀R hq).le_gImg hW hq)
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hr₀R hcont ⟨hr₀u.le, hR⟩
  exact ⟨r, hxr₀.trans_le hr.1, hr₀.of_le hW hr.1 hq, he⟩

open MartChar.RealFlow in
/-- A real boundary value of the inverse lying at or left of `x` comes from
at or left of the geometric image of `x`. -/
theorem le_rightImg_sub_of_extendFrom_eq_real {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hB : HasBdryLimits (fwdMapInv W q)) {x u r : ℝ} (hr : r ≤ x)
    (he : extendFrom H (fwdMapInv W q) u = (r : ℂ)) :
    u ≤ rightImg W x q - W q := by
  by_contra hle
  obtain ⟨s, hxs, hs, hsu⟩ := exists_alive_gImg_eq_of_rightImg_lt hW hq
    (show rightImg W x q < u + W q by linarith only [not_le.1 hle])
  have hExt := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hW hW0 hq
    (show (s : ℂ) ∈ Hbar by simp only [Hbar, mem_ofPred_eq, ofReal_im, le_refl])
    (WangWu.isForwardSol_of_alive hW hs)
  have hc : (cflow W s q : ℂ) = (u : ℂ) := by
    have : cflow W s q = u := by
      dsimp only [gImg] at hsu
      linarith only [hsu]
    exact congrArg (fun a : ℝ => (a : ℂ)) this
  rw [hc, he] at hExt
  have : r = s := ofReal_injective hExt
  linarith only [hr, hxs, this]

open MartChar.RealFlow in
/-- Boundary contact in the interior of the old hull or to the left of a right
mark gives an image cluster point at or left of that mark's image. -/
theorem exists_real_le_mem_closure_fwdMap_image {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hB : HasBdryLimits (fwdMapInv W q)) {A : Set ℂ}
    (hA : A ⊆ H \ fwdHull W q) (hb : IsBounded (fwdMap W q '' A))
    {p : ℂ} (hp : p ∈ closure A) (hpK : p ∉ H \ fwdHull W q)
    {x : ℝ} (hx : 0 ≤ x) (hpSide : p ∈ H ∨ ∃ r : ℝ, r ≤ x ∧ p = (r : ℂ)) :
    ∃ u : ℝ, u ≤ rightImg W x q - W q ∧ (u : ℂ) ∈ closure (fwdMap W q '' A) := by
  obtain ⟨u, hu, he⟩ := exists_real_mem_closure_fwdMap_image hW hW0 hq hB hA hb hp hpK
  refine ⟨u, ?_, hu⟩
  rcases hpSide with hpH | ⟨r, hr, rfl⟩
  · have hlt := Sec7.SideHeight.lt_rightImg_sub_of_extendFrom_mem_H' hB hW hW0 hq
      (he ▸ hpH)
    exact hlt.le.trans (sub_le_sub_right (rightImg_mono_index hW hq hx) _)
  · exact le_rightImg_sub_of_extendFrom_eq_real hW hW0 hq hB hr he

/-- The preceding contact lemma in the physical chart of an integrated small
curve. This uses its generating trace only for boundary extension. -/
theorem exists_real_le_mem_closure_physMap_image
    {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) {x : ℝ} {A : Set ℂ}
    (hAH : A ⊆ H) (hd : Disjoint A (physHull x (Strip.extPath w) q))
    (hb : IsBounded (physMap x (Strip.extPath w) q '' A)) {i : Fin nR}
    (hxi : 0 ≤ xR i) {p : ℂ} (hpA : p ∈ closure A)
    (hpSide : (p ∈ H ∧ p ∈ closure (physHull x (Strip.extPath w) q)) ∨
      ∃ r : ℝ, r ≤ x + xR i ∧ p = (r : ℂ)) :
    ∃ u : ℝ, u ≤ x + vR i q ∧
      (u : ℂ) ∈ closure (physMap x (Strip.extPath w) q '' A) := by
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  let V := frozenDrive w t₂
  have hV : Continuous V := continuous_frozenDrive_of_lt hp.2.2.2.1 ht₂
  have hV0 : V 0 = 0 := by
    rw [show V = frozenDrive w t₂ from rfl, frozenDrive_zero (q.coe_nonneg.trans hqt₂.le), hp.1]
  have he : ∀ r ∈ Icc (0 : ℝ) t₂, Strip.extPath w r = V r :=
    fun r hr => (frozenDrive_eq hr).symm
  have hK : physHull x (Strip.extPath w) q = physHull x V q := by
    rw [physHull, physHull, fwdHull_eq_of_eqOn q.coe_nonneg hqt₂ he]
  have hM : physMap x (Strip.extPath w) q = physMap x V q := by
    funext z
    dsimp only [physMap]
    rw [he q ⟨q.coe_nonneg, hqt₂.le⟩,
      fwdMap_eq_of_eqOn q.coe_nonneg (fun r hr => he r ⟨hr.1, hr.2.trans hqt₂.le⟩)]
  rw [hM] at hb ⊢
  rw [hK] at hd hpSide
  let B := (fun z : ℂ => z - x) '' A
  have hBdom : B ⊆ H \ fwdHull V q := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨mem_H_sub_ofReal (hAH hz) x, fun hk => ?_⟩
    exact hd.ne_of_mem hz ⟨z - x, hk, sub_add_cancel z _⟩ rfl
  have himg : physMap x V q '' A =
      (fun z : ℂ => z + ((x : ℂ) + V q)) '' (fwdMap V q '' B) := by
    rw [image_image, show B = (fun z : ℂ => z - x) '' A from rfl, image_image]
    congr 1
    funext z
    dsimp only [Function.comp_def, physMap]
    ring
  have hBbdd : IsBounded (fwdMap V q '' B) := by
    have hh := isBounded_image_add hb (-((x : ℂ) + V q))
    rw [himg, image_image] at hh
    simpa only [add_neg_cancel_right, image_id'] using hh
  have htrans : Continuous (fun z : ℂ => z - x) := continuous_id.sub continuous_const
  have hpB : p - x ∈ closure B :=
    htrans.continuousAt.continuousWithinAt.mem_closure_image hpA
  have hpOut : p - x ∉ H \ fwdHull V q := by
    intro hnot
    rcases hpSide with ⟨-, hpc⟩ | ⟨r, -, hpr⟩
    · have hpc' := htrans.continuousAt.continuousWithinAt.mem_closure_image hpc
      simp only [physHull, image_image, add_sub_cancel_right, image_id'] at hpc'
      obtain ⟨z, hzK, hzD⟩ := mem_closure_iff.1 hpc' _
        (FwdHolo.isOpen_compl_fwdHull hV q.coe_nonneg) hnot
      exact hzK.2 hzD
    · have hpos : 0 < (p - x).im := hnot.1
      rw [hpr] at hpos
      simp only [sub_im, ofReal_im, sub_zero, lt_self_iff_false] at hpos
  have hpSide' : p - x ∈ H ∨ ∃ r : ℝ, r ≤ xR i ∧ p - x = (r : ℂ) := by
    rcases hpSide with ⟨hpH, -⟩ | ⟨r, hr, hpr⟩
    · exact Or.inl (mem_H_sub_ofReal hpH x)
    · exact Or.inr ⟨r - x, by linarith only [hr], by rw [hpr, ofReal_sub]⟩
  have hBdry := (hη.isLoewnerTraceLT ht₂).hasBdryLimits hV hV0 q.coe_nonneg hqt₂
  obtain ⟨u, hu, hucl⟩ := exists_real_le_mem_closure_fwdMap_image hV hV0 q.coe_nonneg
    hBdry hBdom hBbdd hpB hpOut hxi hpSide'
  have hv := Sec7.SideHeight.vR_eq_rightImg_frozenDrive hp ht₂ hqt₂.le i
  have hVq : V q = w q := by
    rw [show V = frozenDrive w t₂ from rfl, frozenDrive_eq ⟨q.coe_nonneg, hqt₂.le⟩,
      Real.toNNReal_coe]
  refine ⟨u + (x + w q), ?_, ?_⟩
  · rw [hv]
    rw [hVq] at hu
    linarith only [hu]
  · rw [himg, ofReal_add, ofReal_add, ← hVq, mem_closure_image_add_iff]
    exact hucl

end InteractingSLE.ZhanGT4.A2X.P3
