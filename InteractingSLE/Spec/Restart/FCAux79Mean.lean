/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCAux79MeanChart
import InteractingSLE.Spec.Restart.DomainMarkovAux79FC
import InteractingSLE.Spec.Sec7.Lemma78MeanSide
import InteractingSLE.Spec.Sec7.LocalExtA2Cond
import InteractingSLE.Spec.Sec6.DrivingArgLift
import InteractingSLE.Spec.Restart.RetAux79

/-!
# Aux. 79 at the later first-contact lines: the mean identity

Packet PROVE-FCAUX79 (PROVE-FCDET §4.1 item 4; spec pp. 289–290, Aux. lemma 79: "The canonical finite-force expression
obtained by evolving the initial datum has these new-side heights, the inherited old boundary values, and the same
logarithmic derivative branch. … **Aux.** lemma 29, applied to this finite set of physical exceptional points, … proves
equality throughout the active component").

Setting: two flow lines as in `FirstContactKernelClockStatement`, measurable pair data `d`, Lemma 7.8's datum `β` with
its pointwise mean identification `IsBoxPointwiseMean` at the first-contact line (landed:
`Restart.isBoxPointwiseMean_word` with `Sec7.SideHeightBox.isBoxSideLimit_of_flowLines`). At the later line
`(s₀ + t, t₀)` let `g` be a version of the local-set mean of the shifted union `shUnion ηc₁ ηc₂ t 0` (capped versions;
the line kernel of `Restart.exists_shUnion_marked_of_isFlowLine`).

* `shUnion_facts`, `shUnion_eq_lineK`: the shifted union is a field-determined local set and is `lineK d t ω ∩ ℍ` on
  the box.
* `IsFCSideLimit`: the heights on the two sides of the new piece (the single-path comparison at rational own stops;
  `FCAux79Side*`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE

namespace Restart.FCAux79

open Sec7 Sec7.SideHeightBox Supp7 LocalSets Sec6

universe u

/-! ### The shifted union -/

section Union

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

omit mΩ in
theorem shUnion_congr {ηa₁ ηa₂ ηb₁ ηb₂ : Ω → ℝ≥0 → ℂ} {ω : Ω} (e₁ : ηa₁ ω = ηb₁ ω) (e₂ : ηa₂ ω = ηb₂ ω)
    (t₁ t₂ : ℝ≥0) : shUnion ηa₁ ηa₂ t₁ t₂ ω = shUnion ηb₁ ηb₂ t₁ t₂ ω := by
  rw [shUnion_eq, shUnion_eq]
  simp only [fullHist, e₁, e₂]

/-- **The shifted first-contact union is a field-determined local set** (for any capped versions): measurable for the
hitting σ-algebra, local, determined by the centred field up to null sets, and with unbounded lower union (the inputs of
Proposition 3.8, `SideHeightBox.ae_tendsto_sub_of_locals`). -/
theorem shUnion_facts (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (m t : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω)) (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s)
    (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s) (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) :
    Measurable[mΩ, hittingSigma] (shUnion ηc₁ ηc₂ t 0) ∧
    IsLocalSet (shUnion ηc₁ ηc₂ t 0) (WholeField.centredField h u₀) P ∧
    MeasurableSpace.comap (shUnion ηc₁ ηc₂ t 0) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
    ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (shUnion ηc₁ ηc₂ t 0 ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (shUnion ηc₁ ηc₂ t 0 ω)) z) := by
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- locality, for the versions of `exists_capped_version` (as in `exists_shUnion_marked_of_isFlowLine`)
  obtain ⟨η₁', hc₁', hm₁', h0₁', hfr₁', hag₁', hdet₁', hdetζ₁'⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨η₂', hc₂', hm₂', h0₂', hfr₂', hag₂', hdet₂', hdetζ₂'⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hloc₁ := hA56 κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ u₀ hu₀ m η₁' hc₁' hm₁' hag₁'
  have hloc₂ := hA56 κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ u₀ hu₀ m η₂' hc₂' hm₂' hag₂'
  have hζm₁ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₁)
  have hζm₂ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₂)
  have hfc : ∀ᵐ ω ∂P, (∃ s t : ℝ≥0, η₁' ω s = η₂' ω t) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁' ω) ⊤ (η₂' ω) ⊤ s₀ t₀ := by
    filter_upwards [hL77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂, hag₁', hag₂']
      with ω h77 ha₁ ha₂
    rintro ⟨s, t, hst⟩
    rw [ha₁, ha₂] at hst
    obtain ⟨s₀, t₀, hfc, -, -⟩ := h77 ⟨_, _, capTime_le m (ζ₁ ω) s, capTime_le m (ζ₂ ω) t, hst⟩
    obtain ⟨hs₀, ht₀⟩ := hfc.2.2.2 _ _ (capTime_le m (ζ₁ ω) s) (capTime_le m (ζ₂ ω) t) hst
    have hcs₀ : capTime m (ζ₁ ω) s₀ = s₀ := capTime_of_le m (ζ₁ ω)
      (le_min hfc.1 (ENNReal.coe_le_coe.2 (hs₀.trans (capTime_le_cap m (ζ₁ ω) s))))
    have hct₀ : capTime m (ζ₂ ω) t₀ = t₀ := capTime_of_le m (ζ₂ ω)
      (le_min hfc.2.1 (ENNReal.coe_le_coe.2 (ht₀.trans (capTime_le_cap m (ζ₂ ω) t))))
    refine ⟨s₀, t₀, le_top, le_top, ?_, fun s' t' _ _ he => ?_⟩
    · rw [ha₁, ha₂, hcs₀, hct₀]
      exact hfc.2.2.1
    · rw [ha₁, ha₂] at he
      obtain ⟨a, c⟩ := hfc.2.2.2 _ _ (capTime_le m (ζ₁ ω) s') (capTime_le m (ζ₂ ω) t') he
      exact ⟨a.trans (min_le_left _ _), c.trans (min_le_left _ _)⟩
  have hcl : ∀ᵐ ω ∂P, IsOpen (H \ shUnion η₁' η₂' t 0 ω) := by
    refine Eventually.of_forall fun ω => ?_
    have hK : IsCompact (η₁' ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ recFst (fullHist η₁' η₂' ω) + t} ∪
        η₂' ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ recSnd (fullHist η₁' η₂' ω) + (0 : ℝ≥0)}) :=
      (isCompact_image_of_const (hc₁' ω) (hfr₁' ω) _).union (isCompact_image_of_const (hc₂' ω) (hfr₂' ω) _)
    have e : H \ shUnion η₁' η₂' t 0 ω = H \ (η₁' ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ recFst (fullHist η₁' η₂' ω) + t} ∪
        η₂' ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ recSnd (fullHist η₁' η₂' ω) + (0 : ℝ≥0)}) := by
      rw [shUnion_eq]
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, not_and]
      exact ⟨fun ⟨hz, hn⟩ => ⟨hz, fun hu => hn hu hz⟩, fun ⟨hz, hn⟩ => ⟨hz, fun hu _ => hn hu⟩⟩
    rw [e]
    exact QuantumZipper.isOpen_H.sdiff hK.isClosed
  have hloc' := isLocalSet_shUnion (x₁ := (x₁ : ℂ)) (x₂ := (x₂ : ℂ)) (t₁ := t) (t₂ := 0) hh0.measurable hc₁' hc₂'
    h0₁' h0₂' hm₁' hm₂' hζm₁ hζm₂ hdet₁' hdet₂' hdetζ₁' hdetζ₂' hloc₁ hloc₂ hfc hh0 hcl
  have hae' : ∀ᵐ ω ∂P, shUnion ηc₁ ηc₂ t 0 ω = shUnion η₁' η₂' t 0 ω := by
    filter_upwards [hag₁, hag₂, hag₁', hag₂'] with ω h1 h2 h3 h4
    exact shUnion_congr (funext fun s => (h1 s).trans (h3 s).symm) (funext fun s => (h2 s).trans (h4 s).symm) t 0
  -- determination and the lower union, for the versions of `exists_twoHist_versions` (as in `fcUnion_facts`)
  obtain ⟨ηs, hc, h0, hηm, hdet, -, -, him, hs₁, hs₂⟩ :=
    exists_twoHist_versions hL75 hA56 hκ hκ4 hb hh hη₁ hη₂ hu₀ m
  refine ⟨measurable_shUnion hc₁ hc₂ hm₁ hm₂ t 0, Sec7.IsLocalSet.congr_ae hloc' hae', ?_, ?_⟩
  · have hηsm : ∀ i s, Measurable[aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P]
        fun ω => ηs i ω s := fun i s => by
      obtain ⟨f, hf, he⟩ := hdet i s
      exact measurable_aeSigma_of_ae_eq hf he
    have hmeas := @measurable_shUnion Ω (aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀)
      inferInstance) P) (ηs 0) (ηs 1) (hc 0) (hc 1) (hηsm 0) (hηsm 1) t 0
    have hae : shUnion ηc₁ ηc₂ t 0 =ᵐ[P] shUnion (ηs 0) (ηs 1) t 0 := by
      filter_upwards [hag₁, hag₂, hs₁, hs₂] with ω h1 h2 h3 h4
      exact shUnion_congr (funext fun s => (h1 s).trans (h3 s).symm) (funext fun s => (h2 s).trans (h4 s).symm) t 0
    exact SideHeight.comap_le_aeSigma_of_ae_eq hae hmeas.comap_le
  · filter_upwards [hag₁, hag₂, hs₁, hs₂, him] with ω h1 h2 h3 h4 h5
    have e1 : ηc₁ ω = ηs 0 ω := funext fun s => (h1 s).trans (h3 s).symm
    have e2 : ηc₂ ω = ηs 1 ω := funext fun s => (h2 s).trans (h4 s).symm
    refine not_isBounded_lowerUnion_explored (η := pairPath ηc₁ ηc₂) (τ := shLine ηc₁ ηc₂ t 0) (ω := ω)
      (fun i => ?_) (fun i => ?_) (fun i s => ?_)
    · fin_cases i
      exacts [hc₁ ω, hc₂ ω]
    · fin_cases i
      · show (ηc₁ ω 0).im = 0
        rw [e1, h0 0 ω]; simp
      · show (ηc₂ ω 0).im = 0
        rw [e2, h0 1 ω]; simp
    · fin_cases i
      · show 0 ≤ (ηc₁ ω s).im
        rw [e1]; exact h5 0 s
      · show 0 ≤ (ηc₂ ω s).im
        rw [e2]; exact h5 1 s

omit mΩ in
/-- **On the box the capped shifted union is the later line union** (the shifted copy of `fcUnion_eq_K_of_good`). -/
theorem shUnion_eq_lineK {d : PairData Ω} {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (m : ℕ) {ω : Ω} (t : ℝ≥0)
    (hbox : ω ∈ meetBox d m) (hst : d.s₀ ω + t < m) (hlife : ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) ≤ d.ζ₁ ω)
    (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s)
    (ha₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hc₁ : ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s)) (hc₂ : ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    (heq : retHist d ω = fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω) :
    shUnion ηc₁ ηc₂ t 0 ω = lineK d t ω ∩ H := by
  obtain ⟨hE, hs, ht, hsζ, htζ⟩ := mem_meetBox_iff.1 hbox
  have e₁ : recFst (fullHist ηc₁ ηc₂ ω) = d.s₀ ω := by
    have := congrArg (fun y : KHist × KHist => y.1.1.1) heq
    simp only [retHist, fcHist, khistOf, histOf, fcTime₁, hE, ↓reduceIte] at this
    exact this.symm
  have e₂ : recSnd (fullHist ηc₁ ηc₂ ω) = d.t₀ ω := by
    have := congrArg (fun y : KHist × KHist => y.2.1.1) heq
    simp only [retHist, fcHist, khistOf, histOf, fcTime₂, hE, ↓reduceIte] at this
    exact this.symm
  have i₁ : ηc₁ ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ (d.s₀ ω : ℝ≥0∞) + t} = d.η₁ ω '' Icc 0 (d.s₀ ω + t) := by
    have hset : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ (d.s₀ ω : ℝ≥0∞) + t} = Icc 0 (d.s₀ ω + t) := by
      ext s; simp [← ENNReal.coe_add, ENNReal.coe_le_coe]
    rw [hset]
    refine image_congr fun s hsI => ?_
    have hsle : (s : ℝ≥0∞) ≤ ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hsI.2
    have hsm : (s : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
      have : s < (m : ℝ≥0) := lt_of_le_of_lt hsI.2 (by exact_mod_cast hst)
      exact_mod_cast this.le
    rw [hc₁, capTime_of_le, ha₁ _ (hsle.trans hlife)]
    exact le_min (hsle.trans hlife) hsm
  have i₂ : ηc₂ ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ (d.t₀ ω : ℝ≥0∞) + (0 : ℝ≥0)} = d.η₂ ω '' Icc 0 (d.t₀ ω) := by
    have hset : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ (d.t₀ ω : ℝ≥0∞) + (0 : ℝ≥0)} = Icc 0 (d.t₀ ω) := by
      ext s; simp [ENNReal.coe_le_coe]
    rw [hset]
    refine image_congr fun s hsI => ?_
    have hsle : (s : ℝ≥0∞) ≤ d.t₀ ω := ENNReal.coe_le_coe.2 hsI.2
    rw [hc₂, capTime_of_le, ha₂ _ (hsle.trans htζ.le)]
    exact le_min (hsle.trans htζ.le) (ENNReal.coe_le_coe.2 (hsI.2.trans ht.le))
  rw [shUnion_eq, e₁, e₂, i₁, i₂, lineK, prefixSet]

end Union

/-! ### The old boundary: comparison with the first-contact line -/

section Old

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} {ω : Ω} {x₁ x₂ : ℝ} {t : ℝ≥0}
  {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}

/-- **The field mean in the composed chart** `Ξ = v ∘ ψ_t + 𝔥₀ ∘ ψ_t + χ Im L_{fill P} ∘ ψ_t`, `ψ_t = ψ ∘ f_Q⁻¹`, for a
harmonic representative `v` of the mean of the later union and the canonical derivative argument `L_{fill P}` of the
later hull. -/
def compMean (d : PairData Ω) (t : ℝ≥0) (W : ℝ≥0 → ℝ) (Q : ℝ≥0) (v u₀ : ℂ → ℝ) (κ : ℝ) (ω : Ω) (w : ℂ) : ℝ :=
  v (d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) + u₀ (d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) +
    QuantumZipper.chiC κ *
      (canonDerivLog (fillH (lineK d t ω)) (d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))).im

/-- **The first-contact chart is injective on `ℍ̄`** (bijective on `ℍ` onto `D`, real points off `D`, injective on
`ℝ` by `SideHeightBox.inv_injective_real`). -/
theorem inv_injOn_Hbar (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {w w' : ℂ} (hw : w ∈ Hbar)
    (hw' : w' ∈ Hbar) (he : d.inv ω w = d.inv ω w') : w = w' := by
  have hC := hl.chart hd
  have hE := hl.mem_E
  have hi₁ : InjOn (d.η₁ ω) (Icc 0 (d.s₀ ω)) := hl.injOn₁.mono (Icc_subset_Icc_right le_self_add)
  have hi₂ := hl.injOn₂ hd
  have hreal : ∀ z ∈ Hbar, z ∉ H → z = (z.re : ℂ) := fun z hz hzH => by
    have h0 : z.im = 0 := le_antisymm (not_lt.1 hzH) hz
    exact Complex.ext (by simp) (by simp [h0])
  by_cases h₁ : w ∈ H <;> by_cases h₂ : w' ∈ H
  · exact hC.2.1.injOn h₁ h₂ he
  · exact absurd (he ▸ hC.2.1.mapsTo h₁) (hC.2.2.2.1 w' h₂)
  · exact absurd (he.symm ▸ hC.2.1.mapsTo h₂) (hC.2.2.2.1 w h₁)
  · rw [hreal w hw h₁, hreal w' hw' h₂] at he ⊢
    exact_mod_cast (inv_injective_real hd hE hi₁ hi₂ he.symm).symm

/-- **The old boundary of the later domain** (spec p. 290: "the inherited old boundary values"). Let `v` be a harmonic
representative of the mean of the later union `A = lineK ∩ ℍ` and `v₀` one of the first-contact union `B = K ∩ ℍ`,
with Proposition 3.8's comparison `v − v₀ → 0` at the points where the two unions agree locally, and with the
first-contact chart boundary values `v₀ ∘ ψ + 𝔥₀ ∘ ψ + χ ℓ ∘ ψ → c.fn` off a finite set `E₀` (Lemma 7.8). At a real
`y` sent by the extended inverse `Φ` of `f_Q` to a real point `x ∉ E₀ ∪ c.jumps` with a forward solution up to `Q`,
the composed field mean `Ξ = v ∘ ψ_t + 𝔥₀ ∘ ψ_t + χ Im L_{fill P} ∘ ψ_t` tends to `c.fn x`. -/
theorem tendsto_old (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {κ : ℝ} {v v₀ u₀ : ℂ → ℝ}
    {c : BoundaryWord}
    (h38 : ∀ p : ℂ, p ∈ (lineK d t ω ∩ H) ∪ {z : ℂ | z.im = 0} → p ∈ (d.K ω ∩ H) ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, (d.K ω ∩ H) ∩ ball p r ⊆ lineK d t ω ∩ H) → (∃ r > 0, (lineK d t ω ∩ H) ∩ ball p r ⊆ d.K ω ∩ H) →
      Tendsto (fun z => v z - v₀ z) (𝓝[H \ ((lineK d t ω ∩ H) ∪ (d.K ω ∩ H))] p) (𝓝 0))
    {E₀ : Set ℝ} (h0 : ∀ w : ℝ, w ∉ E₀ → Tendsto (fun z => v₀ (d.inv ω z) + u₀ (d.inv ω z) +
      QuantumZipper.chiC κ * d.lift ω (d.inv ω z)) (𝓝[H] (w : ℂ)) (𝓝 (c.fn w)))
    {x y : ℝ} (hx : x ∉ E₀) (hxe : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) y = x) {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol (fun s : ℝ => W s.toNNReal) (x : ℂ) Q u) :
    Tendsto (compMean d t W Q v u₀ κ ω) (𝓝[H] (y : ℂ)) (𝓝 (c.fn x)) := by
  unfold compMean
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  set χ := QuantumZipper.chiC κ with hχ
  set ψ := d.inv ω with hψdef
  have hQr : (0 : ℝ) ≤ Q := Q.coe_nonneg
  have hC := hl.chart hd
  have hψc : ContinuousOn ψ Hbar := hC.2.2.2.2.2.2.2.1
  have hlim : Tendsto (fwdMapInv w' Q) (𝓝[H] (y : ℂ)) (𝓝[H \ fwdHull w' Q] (x : ℂ)) := by
    rw [← hxe]; exact hl.tendsto_fwdMapInv (ofReal_mem_Hbar y)
  have hlimH : Tendsto (fwdMapInv w' Q) (𝓝[H] (y : ℂ)) (𝓝[H] (x : ℂ)) :=
    hlim.mono_right (nhdsWithin_mono _ sdiff_subset)
  -- the three limits
  have h1 := (h0 x hx).comp hlimH
  have h2 := (Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real hl.continuous_rdrv hQr hu).comp hlimH
  set p := ψ x with hpdef
  have hxbar : (x : ℂ) ∈ Hbar := ofReal_mem_Hbar x
  have hpbar : p ∈ Hbar := by
    have h := (hl.isDomChart hd).inv_mem_closure hxbar
    rw [← closure_H]
    exact closure_mono sdiff_subset h
  have hpK : p ∈ (d.K ω ∩ H) ∪ {z : ℂ | z.im = 0} := by
    rcases hd.inv_mem_K_or hl.mem_E x with hK | ⟨hre, -, -⟩
    · rcases mem_H_or_im_eq_zero hpbar with h | h
      · exact Or.inl ⟨hK, h⟩
      · exact Or.inr h
    · exact Or.inr hre
  have hpA : p ∈ (lineK d t ω ∩ H) ∪ {z : ℂ | z.im = 0} := by
    rcases hpK with h | h
    · exact Or.inl ⟨hl.K_subset h.1, h.2⟩
    · exact Or.inr h
  -- `p` is off the new piece
  have hpN : p ∉ d.η₁ ω '' Icc (d.s₀ ω) (d.s₀ ω + t) := by
    rw [← hl.image_inv_γ]
    rintro ⟨_, ⟨s, hs, rfl⟩, he⟩
    have hγbar : γ s ∈ Hbar := hl.γ_mem_Hbar hs.2
    have := inv_injOn_Hbar hd hl hγbar hxbar he
    exact hl.notMem_γ_of_isForwardSol hu ⟨s, hs, this⟩
  have hNc : IsCompact (d.η₁ ω '' Icc (d.s₀ ω) (d.s₀ ω + t)) :=
    isCompact_Icc.image_of_continuousOn (hl.continuousOn₁.mono (Icc_subset_Icc_left zero_le))
  obtain ⟨r, hr, hrN⟩ : ∃ r > 0, ball p r ∩ d.η₁ ω '' Icc (d.s₀ ω) (d.s₀ ω + t) = ∅ := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hNc.isClosed.isOpen_compl p hpN
    exact ⟨r, hr, Set.eq_empty_iff_forall_notMem.2 fun z hz => hsub hz.1 hz.2⟩
  have hloc : ∃ r > 0, (lineK d t ω ∩ H) ∩ ball p r ⊆ d.K ω ∩ H := by
    refine ⟨r, hr, fun z ⟨⟨hzP, hzH⟩, hzb⟩ => ⟨?_, hzH⟩⟩
    rcases hl.lineK_subset hzP with h | h
    · exact h
    · rw [hl.image_inv_γ] at h
      exact absurd (show z ∈ ball p r ∩ _ from ⟨hzb, h⟩) (by rw [hrN]; exact Set.notMem_empty z)
  have h3 := h38 p hpA hpK ⟨1, one_pos, fun z hz => ⟨hl.K_subset hz.1.1, hz.1.2⟩⟩ hloc
  -- the composite tends to `p` within `ℍ \ (A ∪ B)`
  have hψt : Tendsto (fun w => ψ (fwdMapInv w' Q w)) (𝓝[H] (y : ℂ))
      (𝓝[H \ ((lineK d t ω ∩ H) ∪ (d.K ω ∩ H))] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((hψc x hxbar).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlimH.mono_right nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.H_subset_Hbar
          (QuantumZipper.RS.fwdMapInv_mem_H hl.continuous_rdrv hl.rdrv_zero hQr hw)⟩))
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hz := (hl.inv_mem hd hw).1
      refine ⟨hz.1, ?_⟩
      rintro (⟨hzP, -⟩ | ⟨hzK, -⟩)
      · exact hz.2 ⟨hz.1, Or.inl (subset_closure hzP)⟩
      · exact hz.2 ⟨hz.1, Or.inl (subset_closure (hl.K_subset hzK))⟩
  have h3' := h3.comp hψt
  -- assemble with the lift identity
  obtain ⟨cP, hcP⟩ := hl.mapOut_lift hd
  have hsum := h3'.add (h1.add (h2.const_mul χ))
  rw [zero_add, mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  obtain ⟨hz, hφz⟩ := hl.inv_mem hd hw
  have hL := (hcP _ hz).2
  simp only [Function.comp_apply]
  rw [hL, add_im, hφz]
  simp only [PairData.lift]
  ring

end Old

/-! ### The composed chart as a conformal chart of the later domain -/

section Comp

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} {ω : Ω} {x₁ x₂ : ℝ} {t : ℝ≥0}
  {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}

open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

theorem differentiableOn_compInv (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) :
    DifferentiableOn ℂ (fun v => d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q v)) H := by
  have hC := hl.chart hd
  exact hC.2.2.2.2.2.2.1.comp (QuantumZipper.RS.differentiableOn_fwdMapInv hl.continuous_rdrv hl.rdrv_zero
    Q.coe_nonneg) fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hl.continuous_rdrv hl.rdrv_zero Q.coe_nonneg hv

/-- **The composed forward chart `f_Q ∘ φ` is a conformal bijection of the later domain onto `ℍ`.** -/
theorem isConformalBijection_compFwd (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) :
    IsConformalBijection (fun z => fwdMap (fun s : ℝ => W s.toNNReal) Q (d.fwd ω z)) (H \ fillH (lineK d t ω))
      {w : ℂ | 0 < w.im} := by
  have hD := hl.isDomChart hd
  have hsubK : H \ fillH (lineK d t ω) ⊆ H \ fillH (d.K ω) := fun z hz => ⟨hz.1, fun h => hz.2 (hl.fillH_K_subset h)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (QuantumZipper.FwdHolo.differentiableOn_fwdMap hl.continuous_rdrv Q.coe_nonneg).comp
      (hD.differentiableOn_fwd.mono hsubK) fun z hz => hl.fwd_mem hd hz
  · exact fun z hz => hl.fwdMap_fwd_mem hd hz
  · intro z hz z' hz' he
    have h1 := QuantumZipper.FwdHolo.injOn_fwdMap hl.continuous_rdrv Q.coe_nonneg (hl.fwd_mem hd hz)
      (hl.fwd_mem hd hz') he
    exact hD.bijOn_fwd.injOn (hsubK hz) (hsubK hz') h1
  · intro w hw
    exact ⟨_, (hl.inv_mem hd hw).1, hl.fwd_comp_inv hd hw⟩

/-- **The composed inverse chart, precomposed with the Cayley map, is a Riemann map of the later domain.** -/
theorem isConformalBijection_compInv_cayleyInv (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) :
    IsConformalBijection ((fun v => d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q v)) ∘ cayleyInv)
      (ball 0 1) (H \ fillH (lineK d t ω)) :=
  isConformalBijection_comp ⟨differentiableOn_compInv hd hl, hl.bijOn_inv hd⟩ isConformalBijection_cayleyInv

/-- **The derivative argument of the composed forward chart is the canonical lift of the later hull.** -/
theorem deriv_compFwd (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {z : ℂ}
    (hz : z ∈ H \ fillH (lineK d t ω)) :
    deriv (fun z => fwdMap (fun s : ℝ => W s.toNNReal) Q (d.fwd ω z)) z =
      ‖deriv (fun z => fwdMap (fun s : ℝ => W s.toNNReal) Q (d.fwd ω z)) z‖ *
        exp (((canonDerivLog (fillH (lineK d t ω)) z).im : ℂ) * I) := by
  obtain ⟨c, hc⟩ := hl.mapOut_lift hd
  have hB := hl.isHPHull_lineK hd
  have hL := isCanonicalDerivLog_canonDerivLog hB
  have hO : IsOpen (H \ fillH (lineK d t ω)) := isOpen_H_diff_fillH (hl.isCompact_lineK hd).isBounded
  have he : (fun z => fwdMap (fun s : ℝ => W s.toNNReal) Q (d.fwd ω z)) =ᶠ[𝓝 z]
      fun z => ConformalImage.mapOut (fillH (lineK d t ω)) z - c :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hz) fun z' hz' => by
      rw [(hc z' hz').1]; ring
  rw [he.deriv_eq, deriv_sub_const, ← hL.1.2 z hz, mul_comm _ I]
  exact exp_eq_norm_mul_exp_im _

theorem continuousOn_lineLift (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) :
    ContinuousOn (fun z => (canonDerivLog (fillH (lineK d t ω)) z).im) (H \ fillH (lineK d t ω)) :=
  Complex.continuous_im.comp_continuousOn
    (isCanonicalDerivLog_canonDerivLog (hl.isHPHull_lineK hd)).1.1.continuousOn

/-- **The boundary hypothesis of Aux. 28 in the disc coordinate** (the composed-chart copy of
`tendsto_disk_of_chartBoundaryLimit`): if at every real `w` off `S` both the composed field mean `Ξ` and the candidate
`G` tend to the same value, then on the unit circle off `{1} ∪ cayley(S)` the difference of the field mean and
`G ∘ φ_t − χ L` tends to `0` along the disc. -/
theorem tendsto_disk_line (hd : d.IsMeasGood) (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {v u₀ : ℂ → ℝ} {κ : ℝ}
    {G : ℂ → ℝ} {g : ℝ → ℝ} {S : Set ℝ} (hG : ∀ w : ℝ, w ∉ S → Tendsto G (𝓝[H] (w : ℂ)) (𝓝 (g w)))
    (hlim : ∀ w : ℝ, w ∉ S → Tendsto (compMean d t W Q v u₀ κ ω) (𝓝[H] (w : ℂ)) (𝓝 (g w))) :
    ∀ q ∈ sphere (0 : ℂ) 1, q ∉ insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' S) →
      Tendsto (fun ζ => (v (((fun v => d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q v)) ∘ cayleyInv) ζ) +
          u₀ (((fun v => d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q v)) ∘ cayleyInv) ζ)) -
          (G ((fun z => fwdMap (fun s : ℝ => W s.toNNReal) Q (d.fwd ω z))
              (((fun v => d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q v)) ∘ cayleyInv) ζ)) -
            QuantumZipper.chiC κ * (fun z => (canonDerivLog (fillH (lineK d t ω)) z).im)
              (((fun v => d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q v)) ∘ cayleyInv) ζ)))
        (𝓝[ball 0 1] q) (𝓝 0) := by
  intro q hq hqE
  have hq1 : q ≠ 1 := fun h1 => hqE (Set.mem_insert_iff.2 (Or.inl h1))
  set w : ℝ := (cayleyInv q).re with hw
  have hqw : cayleyInv q = (w : ℂ) := cayleyInv_eq_ofReal_re hq
  have hwS : w ∉ S := by
    intro hmem
    refine hqE (mem_insert_of_mem _ ⟨w, hmem, ?_⟩)
    show cayley (w : ℂ) = q
    rw [← hqw]
    exact QuantumZipper.CA.cayley_cayleyInv hq1
  have hT : Tendsto cayleyInv (𝓝[ball 0 1] q) (𝓝[H] (w : ℂ)) := by
    rw [← hqw]; exact Sec6.tendsto_cayleyInv_nhdsWithin_ball hq1
  have h3 := ((hlim w hwS).comp hT).sub ((hG w hwS).comp hT)
  rw [sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  have hζH : cayleyInv ζ ∈ H := QuantumZipper.CA.cayleyInv_mem_H hζ
  simp only [Function.comp_apply, compMean, hl.fwd_comp_inv hd hζH]
  ring

end Comp

/-! ### Aux. 79 at the later line -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

/-- **The heights on the two sides of the new piece** (spec p. 290: "At any exposed side away from that vertex and the
finitely many tips, the two ranges have positive local distance. Nested boundary comparison consequently gives the
corresponding single-path height there"). For every cap `m`, every later line `t`, every pair of capped versions and
every version `g` of the conditional mean of the centred field given the germs of the shifted union at `(s₀ + t, t₀)`,
almost surely on the box (with `s₀ + t < m`), for every harmonic representative `v` and every reading `IsFCLine` of
the continuation in the first-contact chart: at every real `y` that the extended inverse `Φ` of `f_Q` sends onto the
open chart path `γ((0, Q))`, the composed field mean tends to `λ − θ₁χ` if `0 < y < R̃` (the right side of the new
piece) and to `−λ − θ₁χ` if `L̃ < y < 0` (its left side), `R̃ = rightImg W 0 Q − W_Q` and
`L̃ = −rightImg (−W) 0 Q − W_Q` the images of `0±` (the corners `L̃`, `0`, `R̃` are exceptional points of the
uniqueness lemma). -/
def IsFCSideLimit (κ θ₁ x₁ x₂ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) (d : PairData Ω) : Prop :=
  ∀ (m : ℕ) (t : ℝ≥0) (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
    (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ s, Measurable fun ω => ηc₁ ω s) →
    (∀ s, Measurable fun ω => ηc₂ ω s) → (∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s)) →
    (∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) →
    IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → d.s₀ ω + t < m →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ shUnion ηc₁ ηc₂ t 0 ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ shUnion ηc₁ ηc₂ t 0 ω → g ω φ = ∫ z, v z * φ z) →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsFCLine d ω x₁ x₂ t W γ ζc Q →
      ∀ y : ℝ, extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) y ∈ γ '' Ioo 0 Q →
        (0 < y → y < MartChar.RealFlow.rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q →
          Tendsto (compMean d t W Q v u₀ κ ω) (𝓝[H] (y : ℂ)) (𝓝 (sleLambda κ - θ₁ * QuantumZipper.chiC κ))) ∧
        (y < 0 → -MartChar.RealFlow.rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q < y →
          Tendsto (compMean d t W Q v u₀ κ ω) (𝓝[H] (y : ℂ)) (𝓝 (-sleLambda κ - θ₁ * QuantumZipper.chiC κ)))

/-- **Aux. lemma 79 at the later first-contact line, pointwise** (spec pp. 289–290). In the setting of
`FirstContactWordKernelStatement`, let `β` carry Lemma 7.8's chart boundary values at the first-contact line
(`IsBoxChartBoundaryLimit`, landed for the explicit word: `isBoxChartBoundaryLimit_word` with
`isBoxSideLimit_of_flowLines`) and assume the new-piece heights `IsFCSideLimit`. Then for every cap `m`, later line `t`
and version `g` of the mean of the shifted union, almost surely on the box (`s₀ + t < m`): for every harmonic
representative `v`, every reading `IsFCLine` of the continuation (driver `W`, chart path `γ`, capacity `Q`) and every
force word `(ρ, x^L ≤ 0 ≤ x^R)` whose datum is `β + θ₁χ` off a finite set (the flow-line word of `β` at angle `θ₁`),
on the later domain `ℍ \ fill(P)`

`v + 𝔥₀ = 𝔥⁰_Q ∘ f_Q ∘ φ − θ₁χ − χ Im L_{fill P}`,

where `𝔥⁰_Q = LocalExt.bheAt` of the flowed force data and `L_{fill P}` the canonical logarithm of the later hull. -/
theorem ae_eqOn_lineMean (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hβ : IsBoxChartBoundaryLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d β) (hside : IsFCSideLimit κ θ₁ x₁ x₂ P h η₁ η₂ ζ₁ ζ₂ u₀ d)
    (m : ℕ) (t : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → d.s₀ ω + t < m →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ shUnion ηc₁ ηc₂ t 0 ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ shUnion ηc₁ ηc₂ t 0 ω → g ω φ = ∫ z, v z * φ z) →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsFCLine d ω x₁ x₂ t W γ ζc Q →
      ∀ {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ),
      (∀ i, xL i ≤ 0) → (∀ j, 0 ≤ xR j) →
      (∃ S : Set ℝ, S.Finite ∧ ∀ x ∉ S,
        forceBoundaryData κ ρL ρR xL xR x = (β ω).fn x + θ₁ * QuantumZipper.chiC κ) →
      ∀ z ∈ H \ fillH (lineK d t ω), v z + u₀ z =
        LocalExt.bheAt κ ρL ρR (flowL W Q xL) (flowR W Q xR) (fwdMap (fun s : ℝ => W s.toNNReal) Q (d.fwd ω z)) -
          θ₁ * QuantumZipper.chiC κ - QuantumZipper.chiC κ * (canonDerivLog (fillH (lineK d t ω)) z).im := by
  subst hζ₁ hζ₂
  set χ := QuantumZipper.chiC κ with hχ
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hAm, hAloc, hAdet, hAunb⟩ :=
    shUnion_facts hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ m t hc₁ hc₂ hm₁ hm₂ hag₁ hag₂
  obtain ⟨hBm, hBloc, hBdet, hBunb⟩ :=
    fcUnion_facts hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ m hc₁ hc₂ hm₁ hm₂ hag₁ hag₂
  obtain ⟨g₀, hg₀⟩ := IsLocalSet.exists_isLocalSetMean hh0 hBm hBloc
  obtain ⟨hu₀h, ⟨M₀, hM₀⟩, -⟩ := hu₀
  have hid := Sec6.ae_eqOn_component_of_tendsto_global hh0 hAm hAloc hg hu₀h ⟨M₀, hM₀⟩ χ
  have h38 := ae_tendsto_sub_of_locals hh0 hAm hBm hAloc hBloc hAdet hBdet hAunb hBunb hg hg₀
  have h0 := hβ m ηc₁ ηc₂ g₀ hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg₀
  have hs := hside m t ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  have hcmp := ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂
  filter_upwards [hid, h38, h0, hs, hcmp, hae, hag₁, hag₂, hg₀.2.1] with ω hidω h38ω h0ω hsω hcmpω haeω hc₁' hc₂'
    ⟨v₀, hv₀, hv₀rep⟩ hbox hst v hv hvrep W γ ζc Q hl nL nR ρL ρR xL xR hxL hxR ⟨S, hSf, hdata⟩
  obtain ⟨-, heq⟩ := hcmpω
  obtain ⟨-, ha₁, ha₂⟩ := haeω
  have hU : shUnion ηc₁ ηc₂ t 0 ω = lineK d t ω ∩ H :=
    shUnion_eq_lineK m t hbox hst hl.le_life ha₁ ha₂ hc₁' hc₂' (heq hbox)
  have hU₀ : fcUnion ηc₁ ηc₂ ω = d.K ω ∩ H := fcUnion_eq_K_of_good m hbox ha₁ ha₂ hc₁' hc₂' (heq hbox)
  -- the later domain is the component
  set Dt := H \ fillH (lineK d t ω) with hDt
  have hPc := hl.isCompact_lineK hd
  obtain ⟨R, -, -, hEq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hPc.isClosed hPc.isBounded
  have hIH : (I : ℂ) ∈ H := show (0 : ℝ) < I.im by simp
  have hz₀ : d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q I) ∈ Dt := (hl.inv_mem hd hIH).1
  set z₀ := d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q I) with hz₀def
  have hcc : connectedComponentIn (H \ shUnion ηc₁ ηc₂ t 0 ω) z₀ = Dt := by
    rw [hU, H_diff_inter_H]
    have hz₀' := hz₀
    rw [hDt, hEq] at hz₀'
    rw [hDt, hEq]
    exact (connectedComponentIn_eq hz₀').symm
  have hz₀A : z₀ ∈ H \ shUnion ηc₁ ηc₂ t 0 ω := by
    rw [hU]
    exact ⟨hz₀.1, fun h' => hz₀.2 ⟨hz₀.1, Or.inl (subset_closure h'.1)⟩⟩
  -- the line-0 boundary values and the comparison at this `ω`
  obtain ⟨E₀, hE₀f, hE₀⟩ := h0ω hbox v₀ hv₀ hv₀rep
  have h38' := h38ω v v₀ hv hvrep hv₀ hv₀rep
  rw [hU, hU₀] at h38'
  -- the chart boundary values of the later line
  have hdata' : ∀ x ∉ S ∪ E₀, forceBoundaryData κ ρL ρR xL xR x = (β ω).fn x + θ₁ * χ :=
    fun x hx' => hdata x fun h' => hx' (Or.inl h')
  obtain ⟨E₁, hE₁f, hE₁⟩ := hl.exists_finite_tendsto hxL hxR (hSf.union hE₀f) hdata'
    (Ξ := compMean d t W Q v u₀ κ ω)
    (fun x hx' y u hxe hu _ => tendsto_old hd hl h38' hE₀ (fun h' => hx' (Or.inr h')) hxe hu)
    (fun y hy hpos hlt => (hsω hbox hst v hv hvrep W γ ζc Q hl y hy).1 hpos hlt)
    (fun y hy hneg hlt => by
      have := (hsω hbox hst v hv hvrep W γ ζc Q hl y hy).2 hneg hlt
      simpa only [sleLambda, neg_div] using this)
    hl.finite_fibre_seed hl.finite_fibre_tip
  -- the candidate
  have hbhe := LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR (flowL W Q xL) (flowR W Q xR)
  set G : ℂ → ℝ := fun w => LocalExt.bheAt κ ρL ρR (flowL W Q xL) (flowR W Q xR) w - θ₁ * χ with hGdef
  have hGh : InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} := fun w hw =>
    (hbhe.1 w hw).sub (InnerProductSpace.harmonicAt_const _)
  obtain ⟨CG, hCG⟩ := hbhe.2.1
  have hGb : ∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M :=
    ⟨CG + |θ₁ * χ|, fun w hw => by
      have := abs_sub (LocalExt.bheAt κ ρL ρR (flowL W Q xL) (flowR W Q xR) w) (θ₁ * χ)
      have := hCG w hw
      simp only [hGdef]; linarith⟩
  set J := forceJumpSet (flowL W Q xL) (flowR W Q xR) with hJdef
  have hJf : J.Finite := ((finite_range _).union (finite_range _)).insert 0
  have hGlim : ∀ w : ℝ, w ∉ E₁ ∪ J → Tendsto G (𝓝[H] (w : ℂ))
      (𝓝 (forceBoundaryData κ ρL ρR (flowL W Q xL) (flowR W Q xR) w - θ₁ * χ)) := fun w hw =>
    (hbhe.2.2 w fun h' => hw (Or.inr h')).sub_const _
  have hΞlim : ∀ w : ℝ, w ∉ E₁ ∪ J → Tendsto (compMean d t W Q v u₀ κ ω) (𝓝[H] (w : ℂ))
      (𝓝 (forceBoundaryData κ ρL ρR (flowL W Q xL) (flowR W Q xR) w - θ₁ * χ)) := fun w hw =>
    hE₁ w fun h' => hw (Or.inl h')
  have hEd : (insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' (E₁ ∪ J))).Finite :=
    ((hE₁f.union hJf).image _).insert 1
  have hf : IsConformalBijection ((fun v => d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q v)) ∘ cayleyInv)
      (ball 0 1) (connectedComponentIn (H \ shUnion ηc₁ ηc₂ t 0 ω) z₀) := by
    rw [hcc]; exact isConformalBijection_compInv_cayleyInv hd hl
  have hφc : IsConformalBijection (fun z => fwdMap (fun s : ℝ => W s.toNNReal) Q (d.fwd ω z))
      (connectedComponentIn (H \ shUnion ηc₁ ηc₂ t 0 ω) z₀) {w : ℂ | 0 < w.im} := by
    rw [hcc]; exact isConformalBijection_compFwd hd hl
  have hLc : ContinuousOn (fun z => (canonDerivLog (fillH (lineK d t ω)) z).im)
      (connectedComponentIn (H \ shUnion ηc₁ ηc₂ t 0 ω) z₀) := by
    rw [hcc]; exact continuousOn_lineLift hd hl
  have hder : ∀ z ∈ connectedComponentIn (H \ shUnion ηc₁ ηc₂ t 0 ω) z₀,
      deriv (fun z => fwdMap (fun s : ℝ => W s.toNNReal) Q (d.fwd ω z)) z =
        ‖deriv (fun z => fwdMap (fun s : ℝ => W s.toNNReal) Q (d.fwd ω z)) z‖ *
          exp (((canonDerivLog (fillH (lineK d t ω)) z).im : ℂ) * I) := by
    rw [hcc]; exact fun z hz => deriv_compFwd hd hl hz
  have hbd := tendsto_disk_line hd hl hGlim hΞlim
  have heqD := hidω z₀ hz₀A v hv hvrep _ _ G _ _ hf hφc hGh hGb hLc hder hEd hbd
  intro z hz
  rw [← hcc] at hz
  exact heqD z hz

/-- **Aux. lemma 79 at the later first-contact line, in the form of K2's line mean identity** (the hypothesis `hmean`
of `DomainMarkov.Aux79.hasSafeLaw_of_lineKernel`, PROVE-FCDET §4.1 item 4). Under the hypotheses of
`ae_eqOn_lineMean`, almost surely on the box (`s₀ + t < m`), for every reading `IsFCLine` of the continuation and
every force word carrying `β + θ₁χ` off a finite set: against every test function supported off the hull `K_Q` of the
chart driver, the conditional mean `g + 𝔥₀` read in the first-contact chart with height shift `θ₁χ` is the coupling
mean `𝔥_Q = 𝔥⁰_Q ∘ f_Q − χ arg f_Q′` of the flowed force data. -/
theorem ae_chartTransport_lineMean (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hβ : IsBoxChartBoundaryLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d β) (hside : IsFCSideLimit κ θ₁ x₁ x₂ P h η₁ η₂ ζ₁ ζ₂ u₀ d)
    (m : ℕ) (t : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → d.s₀ ω + t < m →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsFCLine d ω x₁ x₂ t W γ ζc Q →
      ∀ {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ),
      (∀ i, xL i ≤ 0) → (∀ j, 0 ≤ xR j) →
      (∃ S : Set ℝ, S.Finite ∧ ∀ x ∉ S,
        forceBoundaryData κ ρL ρR xL xR x = (β ω).fn x + θ₁ * QuantumZipper.chiC κ) →
      ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal) Q →
        Chart.chartTransport (hd.isConformal_chart ω) 1 (θ₁ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ)
            (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal) Q
            (LocalExt.bheAt κ ρL ρR (flowL W Q xL) (flowR W Q xR)) z * ψ z := by
  subst hζ₁ hζ₂
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  filter_upwards [ae_eqOn_lineMean hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl hae hu₀ hβ hside m t hc₁ hc₂
    hm₁ hm₂ hag₁ hag₂ hg, hg.2.1, ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂, hae, hag₁, hag₂]
    with ω hω ⟨v, hv, hvrep⟩ hcmpω haeω hc₁' hc₂' hbox hst W γ ζc Q hl nL nR ρL ρR xL xR hxL hxR hS ψ hψ
  have hpt := hω hbox hst v hv hvrep W γ ζc Q hl ρL ρR xL xR hxL hxR hS
  set χ := QuantumZipper.chiC κ with hχ
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  have hE := hl.mem_E
  obtain ⟨-, heq⟩ := hcmpω
  obtain ⟨-, ha₁, ha₂⟩ := haeω
  have hU : shUnion ηc₁ ηc₂ t 0 ω = lineK d t ω ∩ H :=
    shUnion_eq_lineK m t hbox hst hl.le_life ha₁ ha₂ hc₁' hc₂' (heq hbox)
  set Dt := H \ fillH (lineK d t ω) with hDt
  have hAo : IsOpen (H \ shUnion ηc₁ ηc₂ t 0 ω) := by
    rw [hU, H_diff_inter_H]; exact QuantumZipper.isOpen_H.sdiff (hl.isCompact_lineK hd).isClosed
  have hDtA : Dt ⊆ H \ shUnion ηc₁ ηc₂ t 0 ω := fun z hz => by
    rw [hU]; exact ⟨hz.1, fun h' => hz.2 ⟨hz.1, Or.inl (subset_closure h'.1)⟩⟩
  -- the line chart: the first-contact chart followed by `f_Q`
  set cₜ : Chart := (fun z => fwdMap w' Q (d.fwd ω z), fun w => d.inv ω (fwdMapInv w' Q w),
    fun z => (canonDerivLog (fillH (lineK d t ω)) z).im) with hcₜ
  have hₜ : cₜ.IsConformal :=
    ⟨differentiableOn_compInv hd hl, fun w hw => (hl.inv_mem hd hw).1.1, fun w hw => hl.fwd_comp_inv hd hw⟩
  have hdomₜ : (cₜ.dom : Set ℂ) = Dt := by
    rw [hₜ.coe_dom]; exact (hl.bijOn_inv hd).image_eq
  have hℓₜ : ContinuousOn cₜ.2.2 cₜ.dom := by rw [hdomₜ]; exact continuousOn_lineLift hd hl
  have h₀ := hd.isConformal_chart ω
  have hc₀ : d.chart ω = (d.fwd ω, d.inv ω, d.lift ω) := PairData.chart_of_mem hE
  have hℓ₀ : ContinuousOn (fun w => (d.chart ω).2.2 ((d.chart ω).2.1 w)) H :=
    h₀.continuousOn_lift_inv (hd.continuousOn_lift_chart ω)
  obtain ⟨cP, hcP⟩ := hl.mapOut_lift hd
  -- the candidate
  have hbhe := LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR (flowL W Q xL) (flowR W Q xR)
  set u := LocalExt.bheAt κ ρL ρR (flowL W Q xL) (flowR W Q xR) with hudef
  set mG : ℂ → ℝ := fun w => u w - θ₁ * χ with hmG
  have hmc : ContinuousOn mG H := fun w hw =>
    ((hbhe.1 w hw).1.continuousAt.continuousWithinAt).sub continuousWithinAt_const
  -- the identification in the line chart
  have hid : ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport hₜ 1 0 χ (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)
        φ = ∫ w, mG w * φ w := by
    refine chartTransport_eq_integral_of_eq_integral hₜ hℓₜ χ hmc fun φ hφ => ?_
    rw [hdomₜ] at hφ
    have hφA : tsupport φ ⊆ H \ shUnion ηc₁ ηc₂ t 0 ω := hφ.trans hDtA
    have hvc : ContinuousOn v (H \ shUnion ηc₁ ηc₂ t 0 ω) := fun z hz =>
      (hv z hz).1.continuousAt.continuousWithinAt
    have hi₁ : Integrable fun z => v z * φ z := LocalSets.integrable_mul_test hAo hvc φ hφA
    have hi₂ : Integrable fun z => u₀ z * φ z :=
      LocalSets.integrable_mul_test QuantumZipper.isOpen_H hu₀c φ φ.tsupport_subset
    rw [add_apply, hvrep φ hφA,
      SupercriticalConformalCovariance.GM24.smoothDist_apply (B := upperHalfPlaneOpens) hu₀c φ]
    have hi₂' : (∫ z, φ z * u₀ z) = ∫ z, u₀ z * φ z := by simp_rw [mul_comm]
    rw [hi₂', ← integral_add hi₁ hi₂]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show v z * φ z + u₀ z * φ z = (mG (cₜ.1 z) - χ * cₜ.2.2 z) * φ z
    by_cases hz : z ∈ tsupport φ
    · have := hpt z (hφ hz)
      simp only [hcₜ, hmG]
      rw [show v z * φ z + u₀ z * φ z = (v z + u₀ z) * φ z by ring, this]
    · rw [image_eq_zero_of_notMem_tsupport hz]
      ring
  have hinv : ∀ w ∈ H, cₜ.2.1 w = (d.chart ω).2.1 (fwdMapInv w' Q w) := fun w _ => by rw [hc₀]
  have hlift : ∀ w ∈ H, cₜ.2.2 (cₜ.2.1 w) =
      (logDerivFwd w' Q (fwdMapInv w' Q w)).im + (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv w' Q w)) := by
    intro w hw
    obtain ⟨hz, hφz⟩ := hl.inv_mem hd hw
    rw [hc₀]
    show (canonDerivLog (fillH (lineK d t ω)) (d.inv ω (fwdMapInv w' Q w))).im = _
    rw [(hcP _ hz).2, add_im, hφz]
    rfl
  exact RetAux79.chartTransport_eq_integral_couplingMean_of_trans κ h₀ hₜ hℓ₀ hl.continuous_rdrv hl.rdrv_zero
    Q.coe_nonneg hinv hlift hmc (θ₁ * χ) hid (fun w _ => by simp only [hmG]; ring) ψ hψ

end Main

end Restart.FCAux79

end InteractingSLE
