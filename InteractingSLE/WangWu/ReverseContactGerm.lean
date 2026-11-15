/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactLocal
import InteractingSLE.GFF.LocalSets.GermApprox

/-!
# Local-set means along measure-preserving maps and under the reflection `R(z) = −1/z`

Packet PROVE-WW-B12. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of
Proposition 4.18 (text dump L1607–1614): "the independent-union lemma makes the two stopped slits a local set. The union
boundary lemma identifies its harmonic mean on every exposed open arc." On the glued space of the contact step, the
forward slit is read from the first coordinate and the reverse slit from the second; their local-set means are known on
the spaces of the forward and of the reverse coupling. This file moves local-set means between spaces
(PROVE-WW-B11's obstruction (S3a)):

* `condExp_comap_comp`: **conditional expectations pull back along a measure-preserving map**,
  `E_P[g ∘ π | π⁻¹𝒢] = E_μ[g | 𝒢] ∘ π`;
* `comap_iInf_of_antitone`: the preimage σ-algebra of a decreasing intersection of σ-algebras is the intersection of the
  preimages (no surjectivity is needed: a set `π⁻¹ Bₙ` for every `n` is `π⁻¹ (lim sup Bₙ)`);
* `germSigmaAt_comp`, **`germSigma_comp`**: the germ σ-algebra of `(Â ∘ π, F̂ ∘ π)` is the preimage of that of
  `(Â, F̂)`;
* **`IsLocalSetMean.comp`**: a local-set mean pulls back along a measure-preserving map;
* **`germSigma_reflect`**: `R` preserves germ σ-algebras (`germNbhd` neighbourhoods are mapped into each other at
  comparable scales);
* **`IsLocalSetMean.reflect`**: a local-set mean of `(A, h)` reflected by `R` is a local-set mean of
  `(R(A), −h ∘ R)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets (germSigma germSigmaAt germNbhd IsLocalSetMean)

/-! ### Conditional expectations along a measure-preserving map -/

section CondExp

variable {Ω S : Type*} {𝒢 : MeasurableSpace S} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S] {P : Measure Ω}
  {μ : Measure S} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Conditional expectations pull back along a measure-preserving map**: `E_P[g ∘ π | π⁻¹𝒢] = E_μ[g | 𝒢] ∘ π`. -/
theorem condExp_comap_comp [IsFiniteMeasure P] {π : Ω → S} (hπ : Measurable π) (hμ : P.map π = μ)
    (h𝒢 : 𝒢 ≤ mS) {g : S → E} (hg : Integrable g μ) :
    P[fun ω => g (π ω) | 𝒢.comap π] =ᵐ[P] fun ω => μ[g | 𝒢] (π ω) := by
  have hμf : IsFiniteMeasure μ := by rw [← hμ]; infer_instance
  have hle : 𝒢.comap π ≤ mΩ := (MeasurableSpace.comap_mono h𝒢).trans hπ.comap_le
  set c := μ[g | 𝒢] with hc
  have hgP : Integrable (fun ω => g (π ω)) P := by
    rw [← hμ] at hg; exact hg.comp_measurable hπ
  have hcm : StronglyMeasurable[𝒢] c := stronglyMeasurable_condExp
  have hcmS : StronglyMeasurable c := hcm.mono h𝒢
  have hcint : Integrable c μ := integrable_condExp
  have hcP : Integrable (fun ω => c (π ω)) P := by
    rw [← hμ] at hcint; exact hcint.comp_measurable hπ
  have hmeas : Measurable[𝒢.comap π, 𝒢] π := fun A hA => ⟨A, hA, rfl⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hgP (fun t _ _ => hcP.integrableOn)
    (fun t ht _ => ?_) (hcm.comp_measurable hmeas).aestronglyMeasurable).symm
  obtain ⟨t₀, ht₀, rfl⟩ := ht
  have ht₀m : MeasurableSet t₀ := h𝒢 _ ht₀
  have h1 := MeasureTheory.setIntegral_map (μ := P) (g := π) ht₀m (f := c)
    (by rw [hμ]; exact hcmS.aestronglyMeasurable) hπ.aemeasurable
  have h2 := MeasureTheory.setIntegral_map (μ := P) (g := π) ht₀m (f := g)
    (by rw [hμ]; exact hg.aestronglyMeasurable) hπ.aemeasurable
  rw [hμ] at h1 h2
  rw [← h1, ← h2, hc, setIntegral_condExp h𝒢 hg ht₀]

end CondExp

/-! ### Preimages of decreasing intersections of σ-algebras -/

/-- **The preimage of a decreasing intersection of σ-algebras is the intersection of the preimages.** A set that is
`π⁻¹ Bₙ` with `Bₙ ∈ mₙ` for every `n` is `π⁻¹ B` with `B = ⋂_N ⋃_{n ≥ N} Bₙ ∈ ⨅ mₙ`. -/
theorem comap_iInf_of_antitone {α β : Type*} (f : α → β) {m : ℕ → MeasurableSpace β} (hm : Antitone m) :
    (⨅ n, m n).comap f = ⨅ n, (m n).comap f := by
  refine le_antisymm (le_iInf fun n => MeasurableSpace.comap_mono (iInf_le _ n)) ?_
  intro E hE
  have hE' : ∀ n, MeasurableSet[(m n).comap f] E := fun n => (iInf_le (fun n => (m n).comap f) n) E hE
  choose B hB hBE using hE'
  refine ⟨⋂ N, ⋃ n ≥ N, B n, ?_, ?_⟩
  · -- `⋂_N ⋃_{n ≥ N} Bₙ` is measurable for every `m M`
    have hU : ∀ N M, M ≤ N → MeasurableSet[m M] (⋃ n ≥ N, B n) := fun N M hMN =>
      MeasurableSet.biUnion (to_countable _) fun n hn => hm (hMN.trans hn) _ (hB n)
    refine (MeasurableSpace.measurableSet_iInf).2 fun M => ?_
    have e : (⋂ N, ⋃ n ≥ N, B n) = ⋂ N, ⋃ n ≥ max N M, B n := by
      ext x
      simp only [mem_iInter, mem_iUnion, exists_prop]
      constructor
      · intro hx N; exact hx (max N M)
      · intro hx N
        obtain ⟨n, hn, hxn⟩ := hx N
        exact ⟨n, (le_max_left N M).trans hn, hxn⟩
    rw [e]
    exact MeasurableSet.iInter fun N => hU _ M (le_max_right N M)
  · ext x
    simp only [mem_preimage, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · intro hx
      obtain ⟨n, -, hxn⟩ := hx 0
      rw [← hBE n]; exact hxn
    · intro hx N
      exact ⟨N, le_rfl, by rw [← hBE N] at hx; exact hx⟩

/-! ### Germ σ-algebras along a map -/

section Germ

variable {Ω S : Type*}

/-- The germ σ-algebra at scale `δ` of `(Â ∘ π, F̂ ∘ π)` is the preimage of that of `(Â, F̂)`. -/
theorem germSigmaAt_comp (π : Ω → S) (A : S → Set ℂ) (h : S → DistOn upperHalfPlaneOpens) (δ : ℝ) :
    germSigmaAt (fun ω => A (π ω)) (fun ω => h (π ω)) δ = (germSigmaAt A h δ).comap π := by
  unfold germSigmaAt
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_generateFrom]
  congr 2
  ext E
  constructor
  · rintro ⟨φ, B, hB, rfl⟩
    exact ⟨_, ⟨φ, B, hB, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨φ, B, hB, rfl⟩, rfl⟩
    exact ⟨φ, B, hB, rfl⟩

/-- **The germ σ-algebra of `(Â ∘ π, F̂ ∘ π)` is the preimage of that of `(Â, F̂)`.** -/
theorem germSigma_comp (π : Ω → S) (A : S → Set ℂ) (h : S → DistOn upperHalfPlaneOpens) :
    germSigma (fun ω => A (π ω)) (fun ω => h (π ω)) = (germSigma A h).comap π := by
  unfold germSigma
  rw [comap_iInf_of_antitone π fun n n' hnn' => LocalSets.germSigmaAt_mono (by positivity)
    (one_div_le_one_div_of_le (by positivity)
      (by have := (Nat.cast_le (α := ℝ)).2 hnn'; linarith))]
  simp_rw [germSigmaAt_comp]

end Germ

/-! ### Local-set means along a measure-preserving map -/

section Comp

variable {Ω S : Type*} {𝒢 : MeasurableSpace S} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S] {P : Measure Ω}
  {μ : Measure S}

/-- **A conditional zero-boundary GFF pulls back along a measure-preserving map.** -/
theorem isCondZeroBoundaryGFF_comap [IsFiniteMeasure P] {π : Ω → S} (hπ : Measurable π) (hμ : P.map π = μ)
    (h𝒢 : 𝒢 ≤ mS) {U : S → Set ℂ} {X : S → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hc : IsCondZeroBoundaryGFF μ 𝒢 U X) :
    IsCondZeroBoundaryGFF P (𝒢.comap π) (fun ω => U (π ω)) (fun ω => X (π ω)) := by
  have hμf : IsFiniteMeasure μ := by rw [← hμ]; infer_instance
  intro φ
  have hXφ : Measurable fun s => X s φ := (LQGMetric.measurable_distOn_apply φ).comp hX
  have h1 := condExp_comap_comp hπ hμ h𝒢 (GFF.integrable_exp_I_mul (P := μ) hXφ)
  have h2 : ∀ᵐ s ∂(P.map π), μ[fun s => Complex.exp (Complex.I * (X s φ : ℂ)) | 𝒢] s =
      ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (U s) φ φ) : ℝ) : ℂ) := by
    rw [hμ]; exact hc φ
  filter_upwards [h1, ae_of_ae_map hπ.aemeasurable h2] with ω e1 e2
  rw [e1, e2]

/-- **A local-set mean pulls back along a measure-preserving map.** -/
theorem IsLocalSetMean.comp [IsFiniteMeasure P] {π : Ω → S} (hπ : Measurable π) (hμ : P.map π = μ)
    {A : S → Set ℂ} (hA : Measurable[mS, hittingSigma] A) {h : S → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {g : S → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h μ g) :
    IsLocalSetMean (fun ω => A (π ω)) (fun ω => h (π ω)) P (fun ω => g (π ω)) := by
  obtain ⟨hgm, hhar, hc⟩ := hg
  have hgm' : Measurable g := hgm.mono (LocalSets.germSigma_le hA hh) le_rfl
  have hsub : Measurable fun s => h s - g s := LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((LQGMetric.measurable_distOn_apply φ).comp hh).sub ((LQGMetric.measurable_distOn_apply φ).comp hgm')
  refine ⟨?_, ?_, ?_⟩
  · rw [germSigma_comp]
    intro s hs
    exact ⟨g ⁻¹' s, hgm hs, rfl⟩
  · have h2 : ∀ᵐ s ∂(P.map π), IsHarmonicDistOn (g s) (H \ A s) := by rw [hμ]; exact hhar
    exact ae_of_ae_map hπ.aemeasurable h2
  · rw [germSigma_comp]
    exact isCondZeroBoundaryGFF_comap (𝒢 := germSigma A h) (U := fun s => H \ A s)
      (X := fun s => h s - g s) hπ hμ (LocalSets.germSigma_le hA hh) hsub hc

end Comp

/-! ### Germ σ-algebras under `R` -/

section Reflect

theorem dist_negInv_negInv {z y : ℂ} (hz : z ≠ 0) (hy : y ≠ 0) :
    dist (negInv z) (negInv y) = ‖z - y‖ / (‖z‖ * ‖y‖) := by
  rw [dist_eq_norm, ← norm_mul, ← norm_div]
  congr 1
  simp only [negInv]
  field_simp
  ring

theorem im_negInv (z : ℂ) : (negInv z).im = z.im / Complex.normSq z := by
  simp only [negInv, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]

theorem dist_ofReal_re (w : ℂ) : dist w (w.re : ℂ) = |w.im| := by
  rw [dist_eq_norm]
  have : w - (w.re : ℂ) = (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **`R` maps the germ neighbourhood at scale `δ³/2` into the germ neighbourhood at scale `δ` of the image**
(`0 < δ ≤ 1`). Near `0` the image is near `∞`; elsewhere `R` is `2/δ²`-Lipschitz and preserves `ℍ` and `ℝ`. -/
theorem negInv_mem_germNbhd {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {S : Set ℂ} {z : ℂ}
    (hz : z ∈ germNbhd (δ ^ 3 / 2) S) : negInv z ∈ germNbhd δ (negInv '' S) := by
  obtain ⟨hzH, hz'⟩ := hz
  have hz0 : z ≠ 0 := ne_zero_of_mem_H hzH
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hδ3 : δ ^ 3 ≤ δ := by
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := by gcongr; exact pow_le_one₀ hδ.le hδ1
      _ = δ := mul_one δ
  refine ⟨negInv_mem_H hzH, ?_⟩
  by_cases hsmall : ‖z‖ < δ
  · right
    show 1 / δ < ‖negInv z‖
    rw [norm_negInv, one_div]
    exact inv_strictAnti₀ hzn hsmall
  · rw [not_lt] at hsmall
    left
    rcases hz' with hth | hfar
    · obtain ⟨y, hy, hdist⟩ := Metric.mem_thickening_iff.1 hth
      rw [dist_eq_norm] at hdist
      rcases hy with ⟨hyS, hyH⟩ | hyR
      · have hy0 : y ≠ 0 := ne_zero_of_mem_H hyH
        have hyn : δ / 2 ≤ ‖y‖ := by
          have := norm_sub_norm_le z y
          linarith
        refine Metric.mem_thickening_iff.2 ⟨negInv y, Or.inl ⟨⟨y, hyS, rfl⟩, negInv_mem_H hyH⟩, ?_⟩
        rw [dist_negInv_negInv hz0 hy0, div_lt_iff₀ (by positivity)]
        calc ‖z - y‖ < δ ^ 3 / 2 := hdist
          _ = δ * (δ * (δ / 2)) := by ring
          _ ≤ δ * (‖z‖ * ‖y‖) := by gcongr
      · have hyim : y.im = 0 := hyR
        have him : z.im < δ ^ 3 / 2 := by
          have h1 : |(z - y).im| ≤ ‖z - y‖ := Complex.abs_im_le_norm _
          rw [Complex.sub_im, hyim, sub_zero] at h1
          exact (le_abs_self _).trans_lt (h1.trans_lt hdist)
        refine Metric.mem_thickening_iff.2 ⟨((negInv z).re : ℂ), Or.inr (by simp), ?_⟩
        rw [dist_ofReal_re, im_negInv, Complex.normSq_eq_norm_sq]
        have hzim : 0 < z.im := hzH
        rw [abs_of_pos (by positivity), div_lt_iff₀ (by positivity)]
        calc z.im < δ ^ 3 / 2 := him
          _ ≤ δ * δ ^ 2 := by nlinarith [pow_pos hδ 3]
          _ ≤ δ * ‖z‖ ^ 2 := by gcongr
    · have hfar' : 2 / δ ^ 3 < ‖z‖ := by
        have : (1 : ℝ) / (δ ^ 3 / 2) = 2 / δ ^ 3 := by field_simp
        rw [← this]; exact hfar
      refine Metric.mem_thickening_iff.2 ⟨0, Or.inr (by simp), ?_⟩
      rw [dist_zero_right, norm_negInv]
      have h3 : ‖z‖⁻¹ < δ ^ 3 / 2 := by
        rw [inv_lt_comm₀ hzn (by positivity)]
        calc (δ ^ 3 / 2)⁻¹ = 2 / δ ^ 3 := by field_simp
          _ < ‖z‖ := hfar'
      linarith

/-- **`R` maps germ generators to germ generators**: the germ σ-algebra of `(A, h)` at scale `δ³/2` lies in that of
`(R(A), −h ∘ R)` at scale `δ`. -/
theorem germSigmaAt_le_reflect {Ω : Type*} (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    germSigmaAt A h (δ ^ 3 / 2) ≤
      germSigmaAt (fun ω => negInv '' A ω) (fun ω => reflectField (h ω)) δ := by
  have hcomap : MeasurableSpace.comap A hittingSigma =
      MeasurableSpace.comap (fun ω => negInv '' A ω) hittingSigma := by
    rw [show (fun ω => negInv '' A ω) = (fun S : Set ℂ => negInv '' S) ∘ A from rfl,
      ← MeasurableSpace.comap_comp, comap_eq_of_involutive measurable_image_negInv negInvImage_involutive]
  unfold germSigmaAt
  refine sup_le (hcomap ▸ le_sup_left) (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨φ, B, hB, rfl⟩
  set φ' := Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ with hφ'
  have e : {ω | tsupport φ ⊆ germNbhd (δ ^ 3 / 2) (A ω)} ∩ (fun ω => h ω φ) ⁻¹' B =
      {ω | tsupport φ ⊆ germNbhd (δ ^ 3 / 2) (A ω)} ∩
        ({ω | tsupport φ' ⊆ germNbhd δ (negInv '' A ω)} ∩
          (fun ω => reflectField (h ω) φ') ⁻¹' (Neg.neg ⁻¹' B)) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, reflectField_apply, hφ', pushTest_return_return,
      neg_neg]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, (tsupport_pushTest_return_subset φ).trans ?_, h2⟩
      rintro _ ⟨z, hz, rfl⟩
      exact negInv_mem_germNbhd hδ hδ1 (h1 hz)
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  rw [e]
  refine MeasurableSet.inter ?_ ?_
  · refine le_sup_left (b := MeasurableSpace.generateFrom _) _ ?_
    rw [← hcomap]
    exact ⟨_, LocalSets.measurableSet_subset_germNbhd φ.hasCompactSupport φ.tsupport_subset (by positivity), rfl⟩
  · exact le_sup_right (a := MeasurableSpace.comap _ hittingSigma) _
      (MeasurableSpace.measurableSet_generateFrom ⟨φ', Neg.neg ⁻¹' B, measurable_neg hB, rfl⟩)

theorem germSigma_le_reflect {Ω : Type*} (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    germSigma A h ≤ germSigma (fun ω => negInv '' A ω) (fun ω => reflectField (h ω)) := by
  refine le_iInf fun n => ?_
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hδ1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine (iInf_le _ (2 * (n + 1) ^ 3)).trans ((LocalSets.germSigmaAt_mono (by positivity) ?_).trans
    (germSigmaAt_le_reflect A h hδ hδ1))
  rw [div_pow, one_pow, div_div]
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  linarith

/-- **`R` preserves germ σ-algebras**: the germ σ-algebra of `(R(A), −h ∘ R)` is that of `(A, h)`. -/
theorem germSigma_reflect {Ω : Type*} (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    germSigma (fun ω => negInv '' A ω) (fun ω => reflectField (h ω)) = germSigma A h := by
  refine le_antisymm ?_ (germSigma_le_reflect A h)
  have := germSigma_le_reflect (fun ω => negInv '' A ω) (fun ω => reflectField (h ω))
  simp only [image_negInv_image_negInv, reflectField_reflectField] at this
  exact this

theorem reflectField_sub (f g : DistOn upperHalfPlaneOpens) :
    reflectField (f - g) = reflectField f - reflectField g := by
  have h1 : reflectField (f - g) + reflectField g = reflectField f := by
    rw [← reflectField_add, sub_add_cancel]
  rw [← h1, add_sub_cancel_right]

/-- **A local-set mean reflected by `R`** is a local-set mean of `(R(A), −h ∘ R)`. -/
theorem IsLocalSetMean.reflect {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A : Ω → Set ℂ}
    (hA : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) {h g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean A h P g) :
    IsLocalSetMean (fun ω => negInv '' A ω) (fun ω => reflectField (h ω)) P (fun ω => reflectField (g ω)) := by
  obtain ⟨hgm, hhar, hc⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · rw [germSigma_reflect]
    intro s hs
    exact hgm (measurable_reflectField hs)
  · filter_upwards [hhar] with ω hω
    rw [H_diff_image_negInv]
    exact isHarmonicDistOn_reflectField (hA ω).2 sdiff_subset hω
  · rw [germSigma_reflect]
    have := isCondZeroBoundaryGFF_reflect (𝒢 := germSigma A h) hA hc
    simpa only [reflectField_sub] using this

end Reflect

end InteractingSLE.WangWu
