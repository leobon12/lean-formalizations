import InteractingSLE.Foundations.Topology.Jordan.ArcNonSep
import InteractingSLE.Foundations.Topology.Jordan.Brouwer
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Frozen.Spec.IsGeneratingTrace

/-!
# Section 4.2: simple slits — thin hulls and interior times

Packet PROVE-SEC4-B. Two deterministic Loewner-chain steps of §4.2 of the specification
(`source/spec/p097-144.md`):

* **Aux. lemma 23 proof** (p. 122): "A finite simple slit whose only real point is its seed does
  not disconnect an open pocket from infinity. Thus its filled hull and its trace range agree in
  `ℍ`: `K_S ∩ ℍ = η([0, S]) ∩ ℍ`." Here: `isPreconnected_H_diff_image` (the complement in `ℍ` of
  such a slit is connected; proof: the slit and its reflection form an arc, whose complement in
  `ℂ` is connected by the arc non-separation theorem `Foundations.Jordan.arc_not_separates`
  (the Jordan port of ruling R21, with Brouwer's theorem discharged); a path in that
  complement is folded into `ℍ̄` and lifted into `ℍ`), and
  `fwdHull_inter_H_eq_image_inter_H` (the thin-hull identity for a continuous generating trace).
* **Aux. lemma 25 proof** (p. 127): "Interior times are dense in every nonempty parameter
  interval: an interval on which the continuous trace lay only on `ℝ` would add no half-plane
  capacity, contrary to strict Loewner growth." Here: `exists_mem_Ioo_mem_H` (using
  `hcap(K_t) = 2t`, `hcap_fwdHull`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec4

/-! ### Arcs in `ℂ` -/

open Foundations.Jordan in
/-- **An arc does not separate `ℂ`** (the arc non-separation theorem of the copied Jordan
development, transported from `EuclideanSpace ℝ (Fin 2)` to `ℂ`). -/
theorem isConnected_compl_of_homeomorph_unitInterval {A : Set ℂ} (φ : A ≃ₜ unitInterval) :
    IsConnected Aᶜ := by
  set h : ℂ ≃ₜ Plane := Arcs.complexLIE.toHomeomorph
  have hB : IsConnected (h '' A)ᶜ :=
    arc_not_separates Brouwer.brouwerFPT ((h.image A).symm.trans φ)
  have hA : Aᶜ = h.symm '' (h '' A)ᶜ := by
    rw [image_compl_eq h.symm.bijective, image_image]
    simp
  rw [hA]
  exact hB.image _ h.symm.continuous.continuousOn

/-- The image of `[a, b]` (`a < b`) under a continuous map injective there, into a Hausdorff
space, is homeomorphic to `[0, 1]`. -/
theorem nonempty_homeomorph_unitInterval_image {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : ℝ → Y} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hinj : InjOn f (Icc a b)) : Nonempty ((f '' Icc a b) ≃ₜ unitInterval) := by
  have hc : Continuous (Equiv.Set.imageOfInjOn f (Icc a b) hinj) :=
    continuous_induced_rng.2 hf.domRestrict
  exact ⟨(hc.homeoOfEquivCompactToT2).symm.trans (iccHomeoI a b hab)⟩

/-! ### The fold `x + iy ↦ x + i|y|` and the reflected double of a slit -/

/-- The fold `x + iy ↦ x + i|y|` of `ℂ` onto `ℍ̄`. -/
def foldH (ζ : ℂ) : ℂ := (ζ.re : ℂ) + ((|ζ.im| : ℝ) : ℂ) * I

theorem continuous_foldH : Continuous foldH := by
  unfold foldH; fun_prop

theorem foldH_of_nonneg {ζ : ℂ} (h : 0 ≤ ζ.im) : foldH ζ = ζ := by
  apply Complex.ext <;> simp [foldH, abs_of_nonneg h]

theorem foldH_of_neg {ζ : ℂ} (h : ζ.im < 0) : foldH ζ = conj ζ := by
  apply Complex.ext <;> simp [foldH, abs_of_neg h]

theorem im_foldH (ζ : ℂ) : (foldH ζ).im = |ζ.im| := by simp [foldH]

/-- The reflected double of a path `γ` on `[0, S]`: `γ(t)` for `t ≥ 0` and `conj γ(−t)` for
`t < 0` (with `γ` extended constantly outside `[0, S]`). -/
def reflectDouble (γ : ℝ → ℂ) {S : ℝ} (hS : 0 ≤ S) (t : ℝ) : ℂ :=
  if (0 : ℝ) ≤ t then γ (projIcc 0 S hS t) else conj (γ (projIcc 0 S hS (-t)))

theorem continuous_reflectDouble {γ : ℝ → ℂ} {S : ℝ} (hS : 0 ≤ S)
    (hγ : ContinuousOn γ (Icc 0 S)) (h0 : (γ 0).im = 0) : Continuous (reflectDouble γ hS) := by
  have hc : Continuous fun t => γ (projIcc 0 S hS t) :=
    hγ.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun t =>
      (projIcc 0 S hS t).2
  refine Continuous.if_le hc ((Complex.continuous_conj.comp (hc.comp continuous_neg)))
    continuous_const continuous_id ?_
  intro t ht
  obtain rfl : t = 0 := by simpa using ht.symm
  simp only [neg_zero, projIcc_left]
  exact (Complex.conj_eq_iff_im.2 h0).symm

theorem reflectDouble_of_mem {γ : ℝ → ℂ} {S : ℝ} (hS : 0 ≤ S) {t : ℝ} (ht : t ∈ Icc 0 S) :
    reflectDouble γ hS t = γ t := by
  simp [reflectDouble, ht.1, projIcc_of_mem hS ht]

theorem reflectDouble_of_neg {γ : ℝ → ℂ} {S : ℝ} (hS : 0 ≤ S) {t : ℝ} (ht : t ∈ Icc (-S) 0)
    (htn : t < 0) : reflectDouble γ hS t = conj (γ (-t)) := by
  have hmem : -t ∈ Icc 0 S := ⟨by linarith, by linarith [ht.1]⟩
  simp [reflectDouble, not_le.2 htn, projIcc_of_mem hS hmem]

section Slit

variable {γ : ℝ → ℂ} {S : ℝ}

theorem im_nonneg_of_mem_Icc (h0 : (γ 0).im = 0) (hH : ∀ t ∈ Ioc 0 S, 0 < (γ t).im) {t : ℝ}
    (ht : t ∈ Icc 0 S) : 0 ≤ (γ t).im := by
  rcases ht.1.lt_or_eq with htp | rfl
  · exact (hH t ⟨htp, ht.2⟩).le
  · exact h0.ge

theorem injOn_reflectDouble (hS : 0 ≤ S) (hinj : InjOn γ (Icc 0 S)) (h0 : (γ 0).im = 0)
    (hH : ∀ t ∈ Ioc 0 S, 0 < (γ t).im) : InjOn (reflectDouble γ hS) (Icc (-S) S) := by
  -- values at negative times have negative imaginary part
  have hneg : ∀ t ∈ Icc (-S) S, t < 0 → (reflectDouble γ hS t).im < 0 := by
    intro t ht htn
    rw [reflectDouble_of_neg hS ⟨ht.1, htn.le⟩ htn, Complex.conj_im, neg_lt_zero]
    exact hH (-t) ⟨by linarith, by linarith [ht.1]⟩
  have hnn : ∀ t ∈ Icc (-S) S, 0 ≤ t → 0 ≤ (reflectDouble γ hS t).im := by
    intro t ht htn
    rw [reflectDouble_of_mem hS ⟨htn, ht.2⟩]
    exact im_nonneg_of_mem_Icc h0 hH ⟨htn, ht.2⟩
  intro s hs t ht hst
  rcases le_or_gt 0 s with hs0 | hs0 <;> rcases le_or_gt 0 t with ht0 | ht0
  · rw [reflectDouble_of_mem hS ⟨hs0, hs.2⟩, reflectDouble_of_mem hS ⟨ht0, ht.2⟩] at hst
    exact hinj ⟨hs0, hs.2⟩ ⟨ht0, ht.2⟩ hst
  · exact absurd (hst ▸ hnn s hs hs0) (not_le.2 (hneg t ht ht0))
  · exact absurd (hst.symm ▸ hnn t ht ht0) (not_le.2 (hneg s hs hs0))
  · rw [reflectDouble_of_neg hS ⟨hs.1, hs0.le⟩ hs0, reflectDouble_of_neg hS ⟨ht.1, ht0.le⟩ ht0]
      at hst
    have := hinj ⟨by linarith, by linarith [hs.1]⟩ ⟨by linarith, by linarith [ht.1]⟩
      (star_injective hst)
    linarith

/-- A point outside the reflected double folds to a point outside the slit. -/
theorem foldH_notMem_image (hS : 0 ≤ S) (h0 : (γ 0).im = 0) {ζ : ℂ}
    (hζ : ζ ∉ reflectDouble γ hS '' Icc (-S) S) : foldH ζ ∉ γ '' Icc 0 S := by
  rintro ⟨t, ht, hγt⟩
  rcases le_or_gt 0 ζ.im with hζ0 | hζ0
  · rw [foldH_of_nonneg hζ0] at hγt
    exact hζ ⟨t, ⟨by linarith [ht.1], ht.2⟩, by rw [reflectDouble_of_mem hS ht, hγt]⟩
  · rw [foldH_of_neg hζ0] at hγt
    rcases ht.1.lt_or_eq with htp | rfl
    · refine hζ ⟨-t, ⟨by linarith [ht.2], by linarith⟩, ?_⟩
      rw [reflectDouble_of_neg hS ⟨by linarith [ht.2], by linarith⟩ (by linarith), neg_neg, hγt,
        Complex.conj_conj]
    · have := congrArg Complex.im hγt
      rw [h0, Complex.conj_im] at this
      linarith

/-- **The complement in `ℍ` of a simple slit is connected** (Aux. lemma 23 proof, p. 122: "A
finite simple slit whose only real point is its seed does not disconnect an open pocket from
infinity"). Let `γ` be continuous and injective on `[0, S]`, with `γ 0 ∈ ℝ` and
`γ((0, S]) ⊆ ℍ`. Then `ℍ \ γ([0, S])` is preconnected. -/
theorem isPreconnected_H_diff_image (hγ : ContinuousOn γ (Icc 0 S)) (hinj : InjOn γ (Icc 0 S))
    (h0 : (γ 0).im = 0) (hH : ∀ t ∈ Ioc 0 S, 0 < (γ t).im) :
    IsPreconnected (H \ γ '' Icc 0 S) := by
  have hHc : IsPreconnected H :=
    (convex_halfSpace_gt Complex.imLm.isLinear (0 : ℝ)).isPreconnected
  rcases le_or_gt S 0 with hS | hS
  · convert hHc using 1
    refine sdiff_eq_left.2 (disjoint_left.2 ?_)
    rintro z hz ⟨t, ht, rfl⟩
    have ht0 : t = 0 := le_antisymm (ht.2.trans hS) ht.1
    subst ht0
    have hz' : 0 < (γ 0).im := hz
    rw [h0] at hz'
    exact lt_irrefl _ hz'
  set δ := reflectDouble γ hS.le with hδ
  have hδc : Continuous δ := continuous_reflectDouble hS.le hγ h0
  obtain ⟨φ⟩ := nonempty_homeomorph_unitInterval_image (by linarith : -S < S) hδc.continuousOn
    (injOn_reflectDouble hS.le hinj h0 hH)
  set U := (δ '' Icc (-S) S)ᶜ with hU
  have hUo : IsOpen U := (isCompact_Icc.image hδc).isClosed.isOpen_compl
  have hUp : IsPathConnected U :=
    hUo.isConnected_iff_isPathConnected.1 (isConnected_compl_of_homeomorph_unitInterval φ)
  have hAc : IsClosed (γ '' Icc 0 S) := (isCompact_Icc.image_of_continuousOn hγ).isClosed
  -- points of `ℍ` off the slit are off the double
  have hHU : ∀ z ∈ H \ γ '' Icc 0 S, z ∈ U := by
    rintro z ⟨hzH, hzA⟩ ⟨t, ht, hδt⟩
    rcases le_or_gt 0 t with ht0 | ht0
    · exact hzA ⟨t, ⟨ht0, ht.2⟩, by rw [← hδt, hδ, reflectDouble_of_mem hS.le ⟨ht0, ht.2⟩]⟩
    · have h1 : (δ t).im < 0 := by
        rw [hδ, reflectDouble_of_neg hS.le ⟨ht.1, ht0.le⟩ ht0, Complex.conj_im, neg_lt_zero]
        exact hH (-t) ⟨by linarith, by linarith [ht.1]⟩
      rw [hδt] at h1
      exact lt_asymm h1 hzH
  refine isPreconnected_of_forall_pair ?_
  intro z hz w hw
  obtain ⟨p, hp⟩ : ∃ p : Path z w, ∀ t, p t ∈ U :=
    ⟨(hUp.joinedIn z (hHU z hz) w (hHU w hw)).somePath,
      (hUp.joinedIn z (hHU z hz) w (hHU w hw)).somePath_mem⟩
  set P := range fun t => foldH (p t) with hP
  have hPc : IsCompact P := isCompact_range (continuous_foldH.comp p.continuous)
  have hPA : P ⊆ (γ '' Icc 0 S)ᶜ := by
    rintro _ ⟨t, rfl⟩
    exact foldH_notMem_image hS.le h0 (hp t)
  obtain ⟨d, hd, hthick⟩ := hPc.exists_thickening_subset_open hAc.isOpen_compl hPA
  set ε : ℝ := d / 2 with hε
  have hε0 : 0 < ε := half_pos hd
  have hεd : ε < d := half_lt_self hd
  have hzi : 0 < z.im := hz.1
  have hwi : 0 < w.im := hw.1
  have hfz : foldH z = z := foldH_of_nonneg hzi.le
  have hfw : foldH w = w := foldH_of_nonneg hwi.le
  have hzP : z ∈ P := ⟨0, by simp [hfz]⟩
  have hwP : w ∈ P := ⟨1, by simp [hfw]⟩
  have key : ∀ x y : ℂ, y ∈ P → dist x y < d → 0 < x.im → x ∈ H \ γ '' Icc 0 S :=
    fun x y hy hxy hx => ⟨hx, hthick (mem_thickening_iff.2 ⟨y, hy, hxy⟩)⟩
  have hdist : ∀ (x : ℂ) (s : ℝ), 0 ≤ s → dist (x + (s : ℂ) * I) x = s := by
    intro x s hs
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs]
  set C₁ := (fun s : ℝ => z + (s : ℂ) * I) '' Icc 0 ε with hC₁
  set C₂ := range fun t => foldH (p t) + (ε : ℂ) * I with hC₂
  set C₃ := (fun s : ℝ => w + (s : ℂ) * I) '' Icc 0 ε with hC₃
  refine ⟨C₁ ∪ C₂ ∪ C₃, ?_, Or.inl (Or.inl ⟨0, ⟨le_rfl, hε0.le⟩, by simp⟩),
    Or.inr ⟨0, ⟨le_rfl, hε0.le⟩, by simp⟩, ?_⟩
  · rintro x ((⟨s, hs, rfl⟩ | ⟨t, rfl⟩) | ⟨s, hs, rfl⟩)
    · refine key _ z hzP ((hdist z s hs.1).trans_lt (hs.2.trans_lt hεd)) ?_
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith [hs.1]
    · refine key _ (foldH (p t)) ⟨t, rfl⟩ ((hdist _ ε hε0.le).trans_lt hεd) ?_
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
        im_foldH]
      linarith [abs_nonneg (p t).im]
    · refine key _ w hwP ((hdist w s hs.1).trans_lt (hs.2.trans_lt hεd)) ?_
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith [hs.1]
  · have h₁ : IsPreconnected C₁ :=
      isPreconnected_Icc.image _ (by fun_prop : Continuous fun s : ℝ => z + (s : ℂ) * I).continuousOn
    have h₂ : IsPreconnected C₂ :=
      isPreconnected_range ((continuous_foldH.comp p.continuous).add continuous_const)
    have h₃ : IsPreconnected C₃ :=
      isPreconnected_Icc.image _ (by fun_prop : Continuous fun s : ℝ => w + (s : ℂ) * I).continuousOn
    have hz₁ : z + (ε : ℂ) * I ∈ C₁ := ⟨ε, ⟨hε0.le, le_rfl⟩, rfl⟩
    have hz₂ : z + (ε : ℂ) * I ∈ C₂ := ⟨0, by simp [hfz]⟩
    have hw₂ : w + (ε : ℂ) * I ∈ C₂ := ⟨1, by simp [hfw]⟩
    have hw₃ : w + (ε : ℂ) * I ∈ C₃ := ⟨ε, ⟨hε0.le, le_rfl⟩, rfl⟩
    exact IsPreconnected.union _ (Or.inr hw₂) hw₃ (IsPreconnected.union _ hz₁ hz₂ h₁ h₂) h₃

end Slit

/-! ### Loewner chains generated by a continuous trace -/

/-- `ℍ` is not bounded. -/
theorem not_isBounded_H : ¬ Bornology.IsBounded H := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hmem : ((|R| + 1 : ℝ) : ℂ) * I ∈ H := by
    show 0 < (((|R| + 1 : ℝ) : ℂ) * I).im
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    positivity
  have h := hR hmem
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at h
  linarith [le_abs_self R]

/-- If `ℍ \ A` is preconnected and `A` is bounded, the filling of `A` in `ℍ` is `A ∩ ℍ`. -/
theorem fillH_eq_inter_H_of_isPreconnected {A : Set ℂ} (hAb : Bornology.IsBounded A)
    (hAc : IsClosed A) (hpre : IsPreconnected (H \ A)) : fillH A = A ∩ H := by
  ext z
  simp only [fillH, mem_ofPred_eq, mem_inter_iff, hAc.closure_eq]
  constructor
  · rintro ⟨hzH, hzA | hb⟩
    · exact ⟨hzA, hzH⟩
    · by_contra hzA
      have hzA' : z ∉ A := fun h => hzA ⟨h, hzH⟩
      have hcc : H \ A ⊆ connectedComponentIn (H \ A) z :=
        hpre.subset_connectedComponentIn ⟨hzH, hzA'⟩ subset_rfl
      exact not_isBounded_H (((hb.subset hcc).union hAb).subset fun x hx => by
        by_cases hxA : x ∈ A
        · exact Or.inr hxA
        · exact Or.inl ⟨hx, hxA⟩)
  · rintro ⟨hzA, hzH⟩
    exact ⟨hzH, Or.inl hzA⟩

/-- **Thin hull of a simple slit** (Aux. lemma 23 proof, p. 122: "its filled hull and its trace
range agree in `ℍ`: `K_S ∩ ℍ = η([0, S]) ∩ ℍ`"). If `η` is a continuous generating trace of the
Loewner chain driven by `w` on `[0, T]`, `S < T`, and `η` is injective on `[0, S]` with
`η((0, S]) ⊆ ℍ`, then `K_S ∩ ℍ = η([0, S]) ∩ ℍ`. -/
theorem fwdHull_inter_H_eq_image_inter_H {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) {S : ℝ≥0} (hS : (S : ℝ≥0∞) < T)
    (hinj : InjOn η (Icc 0 S)) (hH : ∀ t ∈ Ioc 0 S, η t ∈ H) :
    QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) S ∩ H = η '' Icc 0 S ∩ H := by
  obtain ⟨h0, hcont, hfill⟩ := hη
  have hηc : ContinuousOn η (Icc 0 S) := hcont.mono fun t ht =>
    le_trans (by exact_mod_cast ht.2) hS.le
  have hAc : IsCompact (η '' Icc 0 S) := isCompact_Icc.image_of_continuousOn hηc
  rw [(isFilling_iff_inter_H_eq_fillH hAc.isBounded hAc.isClosed).1 (hfill S hS)]
  -- the real-parameter path `γ(t) = η(t⁺)`
  set γ : ℝ → ℂ := fun t => η t.toNNReal with hγ
  have hmaps : MapsTo Real.toNNReal (Icc 0 (S : ℝ)) (Icc 0 S) := fun t ht =>
    ⟨by simp, Real.toNNReal_le_iff_le_coe.2 ht.2⟩
  have hγA : γ '' Icc 0 (S : ℝ) = η '' Icc 0 S := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.toNNReal, hmaps ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(s : ℝ), ⟨s.2, by exact_mod_cast hs.2⟩, by simp [hγ]⟩
  have hγc : ContinuousOn γ (Icc 0 (S : ℝ)) :=
    hηc.comp continuous_real_toNNReal.continuousOn hmaps
  have hγinj : InjOn γ (Icc 0 (S : ℝ)) := by
    intro s hs t ht hst
    have := hinj (hmaps hs) (hmaps ht) hst
    exact (Real.toNNReal_eq_toNNReal_iff hs.1 ht.1).1 this
  have hγ0 : (γ 0).im = 0 := by simp [hγ, h0]
  have hγH : ∀ t ∈ Ioc 0 (S : ℝ), 0 < (γ t).im := fun t ht =>
    hH t.toNNReal ⟨Real.toNNReal_pos.2 ht.1, Real.toNNReal_le_iff_le_coe.2 ht.2⟩
  have hpre := isPreconnected_H_diff_image hγc hγinj hγ0 hγH
  rw [hγA] at hpre
  exact fillH_eq_inter_H_of_isPreconnected hAc.isBounded hAc.isClosed hpre

/-- **Interior times are dense** (Aux. lemma 25 proof, p. 127: "an interval on which the
continuous trace lay only on `ℝ` would add no half-plane capacity, contrary to strict Loewner
growth"). For a continuous generating trace `η` of the Loewner chain driven by a continuous `w`
with `w 0 = 0`, every nondegenerate interval `(a, c)` with `c < T` contains a time `t` with
`η(t) ∈ ℍ`. -/
theorem exists_mem_Ioo_mem_H {w : ℝ≥0 → ℝ} (hw : Continuous fun s : ℝ => w s.toNNReal)
    (hw0 : w 0 = 0) {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η) {a c : ℝ≥0}
    (hac : a < c) (hcT : (c : ℝ≥0∞) < T) : ∃ t, a < t ∧ t < c ∧ η t ∈ H := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hcont, hfill⟩ := hη
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  obtain ⟨b, hab, hbc⟩ := exists_between hac
  have hbT : (b : ℝ≥0∞) < T := lt_trans (by exact_mod_cast hbc) hcT
  have haT : (a : ℝ≥0∞) < T := lt_trans (by exact_mod_cast hab) hbT
  have hcompact : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → IsCompact (η '' Icc 0 t) := fun t ht =>
    isCompact_Icc.image_of_continuousOn (hcont.mono fun x hx =>
      le_trans (by exact_mod_cast hx.2) ht.le)
  -- the ranges through `a` and through `b` have the same points in `ℍ`
  have hsame : H \ η '' Icc 0 b = H \ η '' Icc 0 a := by
    ext z
    constructor
    · rintro ⟨hz, hzb⟩
      exact ⟨hz, fun hza => hzb (image_mono (Icc_subset_Icc_right hab.le) hza)⟩
    · rintro ⟨hz, hza⟩
      refine ⟨hz, ?_⟩
      rintro ⟨t, ht, rfl⟩
      rcases le_or_gt t a with hta | hta
      · exact hza ⟨t, ⟨ht.1, hta⟩, rfl⟩
      · exact hcon t hta (ht.2.trans_lt hbc) hz
  have hKb : IsFilling (QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) b)
      (η '' Icc 0 a) := by
    have h := hfill b hbT
    simp only [IsFilling] at h ⊢
    rw [hsame] at h
    exact h
  have hb1 := (isFilling_iff_inter_H_eq_fillH (hcompact a haT).isBounded
    (hcompact a haT).isClosed).1 hKb
  have ha1 := (isFilling_iff_inter_H_eq_fillH (hcompact a haT).isBounded
    (hcompact a haT).isClosed).1 (hfill a haT)
  have hbH := (isHPHull_fwdHull hw b.coe_nonneg).1
  have haH := (isHPHull_fwdHull hw a.coe_nonneg).1
  have heq : QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) b =
      QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) a := by
    calc QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) b
        = QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) b ∩ H := (inter_eq_left.2 hbH).symm
      _ = QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) a ∩ H := by rw [hb1, ha1]
      _ = QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) a := inter_eq_left.2 haH
  have e : (⟨QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) b, isHPHull_fwdHull hw b.coe_nonneg⟩ :
      HPHull) = ⟨QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) a, isHPHull_fwdHull hw a.coe_nonneg⟩ :=
    Subtype.ext heq
  have hcap := congrArg HPHull.hcap e
  have hcb := hcap_fwdHull hw hW0 b.coe_nonneg
  have hca := hcap_fwdHull hw hW0 a.coe_nonneg
  rw [hcb, hca] at hcap
  have : (a : ℝ) < b := hab
  linarith

/-- **Aux. lemma 25, deterministic reduction** (proof, p. 127, last paragraph: "Intersect this
conclusion over rational `q`. Interior times are dense in every nonempty parameter interval … If
two distinct times `s < t` had the same trace point, choose a rational interior time
`q ∈ (s, t)`"). Let `η` be a continuous generating trace of the Loewner chain driven by a
continuous `w` with `w 0 = 0` on `[0, T]`, let `T' ≤ T` be finite, and let `Q` be dense in
`ℝ≥0` (e.g. the rational times). If for every interior time `q ∈ Q` (`q < T'`, `η q ∈ ℍ`) the
trace after `q` never returns to the old trace (`η((q, T']) ∩ η([0, q]) = ∅`), then `η` is
injective on `[0, T']`, including the endpoint `T'`. -/
theorem injOn_Icc_of_forall_disjoint {w : ℝ≥0 → ℝ} (hw : Continuous fun s : ℝ => w s.toNNReal)
    (hw0 : w 0 = 0) {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η) {T' : ℝ≥0}
    (hT' : (T' : ℝ≥0∞) ≤ T) {Q : Set ℝ≥0} (hQ : Dense Q)
    (hret : ∀ q ∈ Q, q < T' → η q ∈ H → Disjoint (η '' Set.Ioc q T') (η '' Icc 0 q)) :
    InjOn η (Icc 0 T') := by
  have key : ∀ s t : ℝ≥0, t ≤ T' → s < t → η s ≠ η t := by
    intro s t htT hst heq
    obtain ⟨c, hsc, hct⟩ := exists_between hst
    have hcT : (c : ℝ≥0∞) < T := lt_of_lt_of_le (by exact_mod_cast hct.trans_le htT) hT'
    obtain ⟨t₁, hst₁, ht₁c, ht₁H⟩ := exists_mem_Ioo_mem_H hw hw0 hη hsc hcT
    -- `η` is continuous at `t₁`
    have hcont : ContinuousAt η t₁ := by
      refine (hη.2.1.mono fun x (hx : x < c) => ?_).continuousAt (isOpen_Iio.mem_nhds ht₁c)
      exact le_trans (by exact_mod_cast hx.le) hcT.le
    have hnhds : η ⁻¹' H ∩ Set.Ioo s c ∈ 𝓝 t₁ :=
      Filter.inter_mem (hcont.preimage_mem_nhds (QuantumZipper.isOpen_H.mem_nhds ht₁H))
        (isOpen_Ioo.mem_nhds ⟨hst₁, ht₁c⟩)
    obtain ⟨q, ⟨hqH, hsq, hqc⟩, hqQ⟩ := mem_closure_iff_nhds.1 (hQ t₁) _ hnhds
    have hdisj := hret q hqQ ((hqc.trans hct).trans_le htT) hqH
    exact disjoint_left.1 hdisj ⟨t, ⟨hqc.trans hct, htT⟩, rfl⟩
      ⟨s, ⟨zero_le, hsq.le⟩, heq⟩
  intro s hs t ht hst
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact (key s t ht.2 hlt hst).elim
  · exact heq
  · exact (key t s hs.2 hgt hst.symm).elim

end Sec4

end InteractingSLE
