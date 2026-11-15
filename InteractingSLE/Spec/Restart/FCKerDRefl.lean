/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerDMem1
import InteractingSLE.Spec.Sec7.Lemma76Reflect
import InteractingSLE.Foundations.Loewner.Reflect

/-!
# The reflected pair data of a first contact

Packet PROVE-T15-FCKER4. The second path's corrected first-contact kernels are obtained from the first path's
(`FCKerC.hasFCK2CapForwardKernel_path₁`, `FCKerD.hasFCK2CapForwardMembers_path₁`) applied to the reflected
configuration (specification p. 270: "Reflection and exchange of the path labels"): under `σ(z) = −z̄` the two flow
lines, exchanged, are again two flow lines (`Sec7.FlowReflect.IsFlowLine.reflect`: seeds `−x₂ > −x₁`, angles
`−θ₂ < −θ₁ + π`). This file builds the pair data of the reflected configuration and its first-contact objects:

* `reflPair d`: the paths `σ ∘ η₂`, `σ ∘ η₁` (lifetimes exchanged) on the same good event;
* `hasContact_refl`, `isFirstContact_refl`, `prefixSet_refl`, `activeDomain_refl`, `isChartGood_refl`,
  **`isMeasGood_reflPair`**;
* `E_reflPair`, `reflPair_s₀` (`= t₀`), `reflPair_t₀` (`= s₀`), `reflPair_K` (`σ(K)`), `reflPair_D`, `reflPair_p`;
* the retained histories: `reflKH`, `swapRefl` (measurable involution), **`reflPair_retHist`**,
  **`reflPair_retSigma`** (the same retained σ-algebra), `reflPair_meetBox`, `reflPair_meetSet`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerD

open LP (reflectC)

section Pair

variable {Ω : Type*}

/-- **The reflected pair**: the two paths exchanged and reflected by `σ(z) = −z̄`. -/
def reflPair (d : PairData Ω) : PairData Ω where
  G := d.G
  η₁ := fun ω t => reflectC (d.η₂ ω t)
  ζ₁ := d.ζ₂
  η₂ := fun ω t => reflectC (d.η₁ ω t)
  ζ₂ := d.ζ₁

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

theorem reflectC_mem_Hbar_iff {z : ℂ} : reflectC z ∈ Hbar ↔ z ∈ Hbar := by
  change 0 ≤ (reflectC z).im ↔ 0 ≤ z.im
  rw [LP.im_reflectC]

theorem hasContact_refl :
    HasContact (fun t => reflectC (η₂ t)) ζ₂ (fun t => reflectC (η₁ t)) ζ₁ ↔ HasContact η₁ ζ₁ η₂ ζ₂ := by
  constructor
  · rintro ⟨s, t, hs, ht, he⟩
    exact ⟨t, s, ht, hs, (LP.reflectC_injective he).symm⟩
  · rintro ⟨s, t, hs, ht, he⟩
    exact ⟨t, s, ht, hs, by simp only [he]⟩

theorem isFirstContact_refl {s₀ t₀ : ℝ≥0} :
    IsFirstContact (fun t => reflectC (η₂ t)) ζ₂ (fun t => reflectC (η₁ t)) ζ₁ t₀ s₀ ↔
      IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀ := by
  constructor
  · rintro ⟨ht, hs, he, hmin⟩
    refine ⟨hs, ht, (LP.reflectC_injective he).symm, fun s t hs' ht' he' => ?_⟩
    exact (hmin t s ht' hs' (by simp only [he'])).symm
  · rintro ⟨hs, ht, he, hmin⟩
    refine ⟨ht, hs, by simp only [he], fun t s ht' hs' he' => ?_⟩
    exact (hmin s t hs' ht' (LP.reflectC_injective he').symm).symm

theorem prefixSet_refl (s₀ t₀ : ℝ≥0) :
    prefixSet (fun t => reflectC (η₂ t)) t₀ (fun t => reflectC (η₁ t)) s₀ = reflectC '' prefixSet η₁ s₀ η₂ t₀ := by
  simp only [prefixSet, image_union, ← image_comp]
  exact union_comm _ _

theorem image_unboundedPart_reflectC (U : Set ℂ) : unboundedPart (reflectC '' U) = reflectC '' unboundedPart U := by
  ext z
  rw [← LP.reflectC_reflectC z, Sec7.FlowReflect.mem_unboundedPart_image_reflectC,
    Sec7.FlowReflect.mem_image_reflectC_iff]

theorem activeDomain_refl (s₀ t₀ : ℝ≥0) :
    activeDomain (fun t => reflectC (η₂ t)) t₀ (fun t => reflectC (η₁ t)) s₀ =
      reflectC '' activeDomain η₁ s₀ η₂ t₀ := by
  have e : H \ ((fun t => reflectC (η₂ t)) '' Icc 0 t₀ ∪ (fun t => reflectC (η₁ t)) '' Icc 0 s₀) =
      reflectC '' (H \ (η₁ '' Icc 0 s₀ ∪ η₂ '' Icc 0 t₀)) := by
    have h := prefixSet_refl (η₁ := η₁) (η₂ := η₂) s₀ t₀
    simp only [prefixSet] at h
    rw [h, LP.H_diff_reflectC_image]
  simp only [activeDomain]
  rw [e, image_unboundedPart_reflectC]

theorem isChartGood_refl (h : IsChartGood η₁ ζ₁ η₂ ζ₂) :
    IsChartGood (fun t => reflectC (η₂ t)) ζ₂ (fun t => reflectC (η₁ t)) ζ₁ := by
  obtain ⟨c₁, c₂, h₁, h₂, i₁, i₂, hfc⟩ := h
  refine ⟨LP.continuous_reflectC.comp_continuousOn c₂, LP.continuous_reflectC.comp_continuousOn c₁,
    fun t ht => reflectC_mem_Hbar_iff.2 (h₂ t ht), fun s hs => reflectC_mem_Hbar_iff.2 (h₁ s hs),
    by simp only [LP.im_reflectC, i₂], by simp only [LP.im_reflectC, i₁], fun hc => ?_⟩
  obtain ⟨s₀, t₀, hf, hcl⟩ := hfc (hasContact_refl.1 hc)
  refine ⟨t₀, s₀, isFirstContact_refl.2 hf, ?_⟩
  rw [activeDomain_refl, LP.closure_image_reflectC]
  show reflectC (η₂ t₀) ∈ _
  rw [← hf.2.2.1]
  exact mem_image_of_mem _ hcl

variable {d : PairData Ω}

theorem E_reflPair : (reflPair d).E = d.E := by
  ext ω
  change ω ∈ d.G ∧ HasContact (fun t => reflectC (d.η₂ ω t)) (d.ζ₂ ω) (fun t => reflectC (d.η₁ ω t)) (d.ζ₁ ω) ↔
    ω ∈ d.G ∧ HasContact (d.η₁ ω) (d.ζ₁ ω) (d.η₂ ω) (d.ζ₂ ω)
  rw [hasContact_refl]

variable [MeasurableSpace Ω]

theorem isMeasGood_reflPair (hd : d.IsMeasGood) : (reflPair d).IsMeasGood where
  measurableSet_G := hd.measurableSet_G
  meas₁ t := LP.continuous_reflectC.measurable.comp (hd.meas₂ t)
  meas₂ t := LP.continuous_reflectC.measurable.comp (hd.meas₁ t)
  measζ₁ := hd.measζ₂
  measζ₂ := hd.measζ₁
  good ω hω := isChartGood_refl (hd.good ω hω)

theorem reflPair_s₀ (hd : d.IsMeasGood) (ω : Ω) : (reflPair d).s₀ ω = d.t₀ ω := by
  by_cases hω : ω ∈ d.E
  · exact (PairData.eq_of_isFirstContact (d := reflPair d) hω.1
      (isFirstContact_refl.2 (hd.isFirstContact hω))).2.1
  · have hω' : ω ∉ (reflPair d).E := by rwa [E_reflPair]
    simp [PairData.s₀, PairData.t₀, hω, hω']

theorem reflPair_t₀ (hd : d.IsMeasGood) (ω : Ω) : (reflPair d).t₀ ω = d.s₀ ω := by
  by_cases hω : ω ∈ d.E
  · exact (PairData.eq_of_isFirstContact (d := reflPair d) hω.1
      (isFirstContact_refl.2 (hd.isFirstContact hω))).2.2
  · have hω' : ω ∉ (reflPair d).E := by rwa [E_reflPair]
    simp [PairData.s₀, PairData.t₀, hω, hω']

theorem reflPair_K (hd : d.IsMeasGood) (ω : Ω) : (reflPair d).K ω = reflectC '' d.K ω := by
  by_cases hω : ω ∈ d.E
  · have hω' : ω ∈ (reflPair d).E := by rwa [E_reflPair]
    rw [PairData.K_of_mem hω', PairData.K_of_mem hω, reflPair_s₀ hd, reflPair_t₀ hd]
    exact prefixSet_refl _ _
  · have hω' : ω ∉ (reflPair d).E := by rwa [E_reflPair]
    rw [PairData.K_of_notMem hω', PairData.K_of_notMem hω, image_empty]

theorem reflPair_D (hd : d.IsMeasGood) (ω : Ω) : (reflPair d).D ω = reflectC '' d.D ω := by
  rw [PairData.D, PairData.D, reflPair_K hd, LP.fillH_image_reflectC, LP.H_diff_reflectC_image]

theorem reflPair_p (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) : (reflPair d).p ω = reflectC (d.p ω) := by
  have hω' : ω ∈ (reflPair d).E := by rwa [E_reflPair]
  rw [PairData.p_of_mem hω', PairData.p_of_mem hω, reflPair_s₀ hd]
  change reflectC (d.η₂ ω (d.t₀ ω)) = _
  rw [← (hd.isFirstContact hω).2.2.1]

end Pair

section Hist

variable {Ω : Type*} {d : PairData Ω}

/-- The reflected killed history (coordinates reflected by `σ`). -/
def reflKH (k : KHist) : KHist := ((k.1.1, fun q => reflectC (k.1.2 q)), k.2)

/-- The two killed histories exchanged and reflected. -/
def swapRefl (y : KHist × KHist) : KHist × KHist := (reflKH y.2, reflKH y.1)

theorem reflKH_reflKH (k : KHist) : reflKH (reflKH k) = k := by
  simp only [reflKH, LP.reflectC_reflectC]

theorem swapRefl_swapRefl (y : KHist × KHist) : swapRefl (swapRefl y) = y := by
  simp only [swapRefl, reflKH_reflKH]

theorem measurable_reflKH : Measurable reflKH := by
  refine Measurable.prodMk (Measurable.prodMk (measurable_fst.comp measurable_fst) ?_) measurable_snd
  exact measurable_pi_iff.2 fun q => LP.continuous_reflectC.measurable.comp
    ((measurable_pi_apply q).comp (measurable_snd.comp measurable_fst))

theorem measurable_swapRefl : Measurable swapRefl :=
  (measurable_reflKH.comp measurable_snd).prodMk (measurable_reflKH.comp measurable_fst)

theorem khistOf_refl (c : ℚ≥0 → ℂ) (ζ T : ℝ≥0∞) :
    khistOf (fun q => reflectC (c q)) ζ T = reflKH (khistOf c ζ T) := by
  simp only [khistOf, Sec6.histOf, Sec6.stopCoord, reflKH]
  congr 2
  funext q
  split_ifs <;> simp [Sec6.stopCoord, *]

/-- A history map and its exchanged reflection generate the same σ-algebra. -/
theorem comap_swapRefl {R : Ω → KHist × KHist} :
    MeasurableSpace.comap (fun ω => swapRefl (R ω)) inferInstance = MeasurableSpace.comap R inferInstance := by
  refine le_antisymm (measurable_swapRefl.comp (comap_measurable R)).comap_le ?_
  have h := measurable_swapRefl.comp (comap_measurable (fun ω => swapRefl (R ω)))
  have e : (swapRefl ∘ fun ω => swapRefl (R ω)) = R := funext fun ω => swapRefl_swapRefl (R ω)
  rw [e] at h
  exact h.comap_le

theorem swapRefl_mem_boxSet {y : KHist × KHist} {m : ℝ≥0} : swapRefl y ∈ boxSet m ↔ y ∈ boxSet m := by
  simp only [boxSet, swapRefl, reflKH, mem_ofPred_eq]
  tauto

variable [MeasurableSpace Ω]

theorem reflPair_fcTime₁ (hd : d.IsMeasGood) (ω : Ω) : fcTime₁ (reflPair d) ω = fcTime₂ d ω := by
  simp only [fcTime₁, fcTime₂, reflPair_s₀ hd]
  by_cases hω : ω ∈ d.E
  · have h' : ω ∈ (reflPair d).E := by rwa [E_reflPair]
    simp only [h', hω, ↓reduceIte]
  · have h' : ω ∉ (reflPair d).E := by rwa [E_reflPair]
    simp only [h', hω, ↓reduceIte]

theorem reflPair_fcTime₂ (hd : d.IsMeasGood) (ω : Ω) : fcTime₂ (reflPair d) ω = fcTime₁ d ω := by
  simp only [fcTime₁, fcTime₂, reflPair_t₀ hd]
  by_cases hω : ω ∈ d.E
  · have h' : ω ∈ (reflPair d).E := by rwa [E_reflPair]
    simp only [h', hω, ↓reduceIte]
  · have h' : ω ∉ (reflPair d).E := by rwa [E_reflPair]
    simp only [h', hω, ↓reduceIte]

theorem reflPair_retHist (hd : d.IsMeasGood) (ω : Ω) : retHist (reflPair d) ω = swapRefl (retHist d ω) := by
  simp only [retHist, swapRefl, reflPair_fcTime₁ hd, reflPair_fcTime₂ hd]
  exact Prod.ext (khistOf_refl _ _ _) (khistOf_refl _ _ _)

theorem reflPair_retSigma (hd : d.IsMeasGood) (P : Measure Ω) : retSigma (reflPair d) P = retSigma d P := by
  have e : retHist (reflPair d) = fun ω => swapRefl (retHist d ω) := funext (reflPair_retHist hd)
  simp only [retSigma, e, comap_swapRefl]

theorem reflPair_meetBox (hd : d.IsMeasGood) (m : ℕ) : meetBox (reflPair d) m = meetBox d m := by
  ext ω
  simp only [meetBox, mem_preimage, reflPair_retHist hd, swapRefl_mem_boxSet]

theorem reflPair_meetSet (hd : d.IsMeasGood) : meetSet (reflPair d) = meetSet d := by
  simp only [meetSet, reflPair_meetBox hd]

end Hist

end InteractingSLE.Restart.FCPlumb.FCKerD
