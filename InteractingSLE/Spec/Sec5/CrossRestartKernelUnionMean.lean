/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelUnionLaw
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfMean
import InteractingSLE.WangWu.ReverseContactUnion
import InteractingSLE.Spec.Sec5.GlueCondTopo

/-!
# Lemma 4.7's direction, item (A)(b)–(c): the strip union mean with both single-curve means explicit

Packet PROVE-CFRESTART2. Specification §4.2, proof of Lemma 4.7 (`source/spec/p097-144.md#lem-4.7-proof`, p. 118):
"Propositions 3.7 and 3.8 together tell us that the boundary data for the conditional law of `h` given both
`η|_{[0,τ]}` and `η′|_{[0,t]}` agree with those of the conditional law given just `η|_{[0,τ]}` (resp. `η′|_{[0,t]}`)
alone". In the strip setting of `exists_condLaw_union_strip` (one probability space, the hypothesis
`CondIndep σ(h) (⨆ σ(η t)) (⨆ σ(W′ t))`):

* `ae_union_boundary_of_condIndepEv` (generic, single space; the single-space form of WangWu's
  `ae_union_boundary_glue`): Proposition 3.8 with either hull as comparison set gives one harmonic representative `w`
  of the union mean with `w − w_A → 0` near `A ∪ ℝ` away from `G` and `w − w_G → 0` near `G ∪ ℝ` away from `A`;
* `isHPHull_fwdHull_rpath`, `not_isBounded_lowerUnion_add_image`, `not_isBounded_lowerUnion_stripInv_image`: the
  unbounded-component hypothesis of Proposition 3.8 for the translated flow hull and the read-back counterflow hull;
* **`ae_union_mean_strip`**: for every local-set mean `g` of the union `A₁ ∪ A₂` (flow hull `x + K_{τ₁}`, counterflow
  hull `M_q⁻¹(K′_{τ₂})`) for the centred strip field `h − u₀`, almost surely `g` has a harmonic representative `w` off
  the union with `w − (𝔥_{τ₁}(· − x) − c − u₀) → 0` at points of `A₁ ∪ ℝ` near which `A₂ ⊆ A₁`, and
  `w − (−𝔥′_{τ₂} ∘ M_q + a + k · lift − u₀) → 0` at points of `A₂ ∪ ℝ` near which `A₁ ⊆ A₂` (the two single means:
  `Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull` and `ae_apply_eq_of_isLocalSetMean_stripInvHull`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF CondIndepEv)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Sec5.CrossRestart

open Coupling LocalSets

/-! ### Proposition 3.8 with either hull as comparison set (single space) -/

section Generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The union boundary lemma on one probability space** (Proposition 3.8 with either set as comparison set). For
local sets `A`, `G` of a zero-boundary GFF `f`, conditionally independent given `f`, each with only unbounded
components in its lower union, and local-set means `g` of `A ∪ G`, `gA` of `A`, `gG` of `G`: almost surely, for all
harmonic representatives `wA` of `gA` off `A` and `wG` of `gG` off `G`, the union mean has a harmonic representative
`w` off `A ∪ G` with `w − wA → 0` at every point of `A ∪ ℝ` near which `G ⊆ A`, and `w − wG → 0` at every point of
`G ∪ ℝ` near which `A ⊆ G`. -/
theorem ae_union_boundary_of_condIndepEv {f : Ω → DistOn upperHalfPlaneOpens}
    (hf : IsZeroBoundaryGFF upperHalfPlaneOpens f P) {A G : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hGm : Measurable[mΩ, hittingSigma] G)
    (hci : CondIndepEv (MeasurableSpace.comap f inferInstance) (MeasurableSpace.comap A hittingSigma)
      (MeasurableSpace.comap G hittingSigma) P)
    (hA : IsLocalSet A f P) (hGl : IsLocalSet G f P)
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbG : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (G ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (G ω)) z))
    {g gA gG : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ G ω) f P g) (hgA : IsLocalSetMean A f P gA)
    (hgG : IsLocalSetMean G f P gG) :
    ∀ᵐ ω ∂P, ∀ wA wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd wA (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → gA ω φ = ∫ z, wA z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ G ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ G ω → gG ω φ = ∫ z, wG z * φ z) →
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (A ω ∪ G ω)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ G ω) → g ω φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ A ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, G ω ∩ ball z₀ r ⊆ A ω) →
          Tendsto (fun z => w z - wA z) (𝓝[H \ (A ω ∪ G ω)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ G ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A ω ∩ ball z₀ r ⊆ G ω) →
          Tendsto (fun z => w z - wG z) (𝓝[H \ (A ω ∪ G ω)] z₀) (𝓝 0)) := by
  -- comparison with `G`
  have h1 := IsLocalSetMean.ae_tendsto_sub_of_union hf hAm hGm hci hA hGl hunbG hg hgG
  -- comparison with `A`
  have hg' : IsLocalSetMean (fun ω => G ω ∪ A ω) f P g := by
    have e : (fun ω => G ω ∪ A ω) = fun ω => A ω ∪ G ω := funext fun ω => union_comm _ _
    rw [e]; exact hg
  have h2 := IsLocalSetMean.ae_tendsto_sub_of_union hf hGm hAm hci.symm hGl hA hunbA hg' hgA
  filter_upwards [h1, h2, hA.2.1, hGl.2.1] with ω ⟨uG, huG, hrepG, hlimG⟩ ⟨uA, huA, hrepA, hlimA⟩ hAc hGc
  intro wA wG hwA hrepA' hwG hrepG'
  set O := H \ (A ω ∪ G ω) with hO
  have hOo : IsOpen O := by
    have : O = (H \ A ω) ∩ (H \ G ω) := by
      ext z; simp only [hO, Set.mem_sdiff, mem_union, mem_inter_iff, not_or]; tauto
    rw [this]; exact hAc.2.inter hGc.2
  have hOA : O ⊆ H \ A ω := fun z hz => ⟨hz.1, fun h' => hz.2 (Or.inl h')⟩
  have hOG : O ⊆ H \ G ω := fun z hz => ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩
  have hOH : O ⊆ H := fun z hz => hz.1
  have hGA : O = H \ (G ω ∪ A ω) := by rw [hO, union_comm]
  have huA' : InnerProductSpace.HarmonicOnNhd uA O := by rw [hGA]; exact huA
  have hcont : ∀ {v : ℂ → ℝ} {U : Set ℂ}, InnerProductSpace.HarmonicOnNhd v U → ContinuousOn v U :=
    fun hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hsum : ∀ (u v : ℂ → ℝ) (U : Set ℂ), O ⊆ U → InnerProductSpace.HarmonicOnNhd u O →
      InnerProductSpace.HarmonicOnNhd v U → ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      ∫ z, (u z + v z) * φ z = (∫ z, u z * φ z) + ∫ z, v z * φ z := by
    intro u v U hOU hu hv φ hφ
    have i1 := LocalSets.integrable_mul_test hOo (hcont hu) φ hφ
    have i2 := LocalSets.integrable_mul_test hOo ((hcont hv).mono hOU) φ hφ
    rw [← integral_add i1 i2]
    congr 1; funext z; ring
  -- the two candidate representatives of `g` agree on `O`
  have heq : EqOn (fun z => uG z + wG z) (fun z => uA z + wA z) O := by
    refine Sec6.eqOn_of_integral_mul_eq hOo hOH (huG.add (fun z hz => hwG z (hOG hz)))
      (huA'.add (fun z hz => hwA z (hOA hz))) fun φ hφ => ?_
    rw [hsum uG wG _ hOG huG hwG φ hφ, hsum uA wA _ hOA huA' hwA φ hφ, ← hrepG φ hφ,
      ← hrepG' φ (hφ.trans hOG), ← hrepA φ (by rw [← hGA]; exact hφ), ← hrepA' φ (hφ.trans hOA)]
    ring
  refine ⟨fun z => uG z + wG z, huG.add (fun z hz => hwG z (hOG hz)), fun φ hφ => ?_, ?_, ?_⟩
  · rw [hsum uG wG _ hOG huG hwG φ hφ, ← hrepG φ hφ, ← hrepG' φ (hφ.trans hOG)]
    ring
  · intro z₀ hz₀ hloc
    have hl := hlimA z₀ hz₀ hloc
    rw [← hGA] at hl
    refine hl.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have := heq hz
    simp only at this
    rw [this]; ring
  · intro z₀ hz₀ hloc
    refine (hlimG z₀ hz₀ hloc).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    ring

end Generic

/-! ### The unbounded-component hypothesis for the two strip hulls -/

section Hulls

/-- **The hull of a driver continuous before its lifetime is a compact `ℍ`-hull** at every time `t < ζ`. -/
theorem isHPHull_fwdHull_rpath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : IsHPHull (fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  obtain ⟨t₂, htt₂, ht₂⟩ := exists_real_btwn_of_lt ht
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hwc ht₂
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull (frozenDrive w t₂) t :=
    fwdHull_eq_of_eqOn t.coe_nonneg htt₂ fun r hr => (frozenDrive_eq hr).symm
  rw [hK]
  exact isHPHull_fwdHull hW t.coe_nonneg

/-- Every component of `(x + K) ∪ {Im ≤ 0}` is unbounded for a compact `ℍ`-hull `K`. -/
theorem not_isBounded_lowerUnion_add_image {K : Set ℂ} (hK : IsHPHull K) (x : ℝ) :
    ∀ z ∈ lowerUnion ((fun z : ℂ => z + x) '' K),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion ((fun z : ℂ => z + x) '' K)) z) := by
  have e : (fun z : ℂ => z + x) '' K = affHomeo 1 one_pos x '' K :=
    image_congr fun z _ => by rw [coe_affHomeo]; push_cast; ring
  rw [e]
  exact GlueCond.not_isBounded_lowerUnion_of_isHPHull (hK.image_affHomeo one_pos)

/-- Every component of `M_q⁻¹(K) ∪ {Im ≤ 0}` is unbounded for a compact `ℍ`-hull `K`
(`M_q⁻¹(z) = R((z + 1)/(1 + q))`). -/
theorem not_isBounded_lowerUnion_stripInv_image {q : ℝ} (hq : 0 < q) {K : Set ℂ} (hK : IsHPHull K) :
    ∀ z ∈ lowerUnion ((Sec4.stripCounterflowChart q).2.1 '' K),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion ((Sec4.stripCounterflowChart q).2.1 '' K)) z) := by
  have hr := cfr_pos hq
  have e : (Sec4.stripCounterflowChart q).2.1 '' K =
      WangWu.negInv '' (affHomeo (1 / (1 + q)) hr (1 / (1 + q)) '' K) := by
    rw [image_image]
    refine image_congr fun z _ => ?_
    rw [← negInv_dil_add_one hq z, coe_affHomeo, Sec7.Lemma725RefFull.dil]
    congr 1
    push_cast
    ring
  rw [e]
  exact GlueCond.not_isBounded_lowerUnion_image_negInv (hK.image_affHomeo hr)

end Hulls

/-! ### The strip -/

section Strip

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The strip union mean with both single-curve means explicit** (Lemma 4.7, p. 118: Propositions 3.7 and 3.8).
Hypotheses as in `exists_condLaw_union_strip`, with bounded harmonic extensions `u₁ ω` of the flow word's data at `τ₁`
and `u₂ ω` of the counterflow word's data at `τ₂`. For every local-set mean `g` of `A₁ ∪ A₂` (`A₁ = x + K_{τ₁}`,
`A₂ = M_q⁻¹(K′_{τ₂})`) for the centred strip field `h − u₀`, almost surely `g` has a harmonic representative `w` off
`A₁ ∪ A₂` with `w − (𝔥_{τ₁}(· − x) − c − u₀) → 0` at every point of `A₁ ∪ ℝ` near which `A₂ ⊆ A₁`, and
`w − (−𝔥′_{τ₂} ∘ M_q + a + k · lift − u₀) → 0` at every point of `A₂ ∪ ℝ` near which `A₁ ⊆ A₂`. -/
theorem ae_union_mean_strip {κ κ' q x c a k : ℝ} (hκ : 0 < κ) (hκ' : 0 < κ') (hq : 0 < q)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ u₀' : ℂ → ℝ}
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    -- the flow line
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h₁ : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h₁)
    (htrans : ∀ ω, IsTranslateAddConst x c (h ω) (h₁ ω))
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hrel : EqOn u₀' (fun z => u₀ (z + x) + c) H) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {η : Ω → ℝ≥0 → ℂ} (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x))
    {τ₁ : Ω → WithTop ℝ≥0} (hτ₁ : IsStoppingTime (drivingFiltration P hX) τ₁)
    (hτ₁ζ : ∀ᵐ ω ∂P, (τ₁ ω : ℝ≥0∞) < ζ ω) {A₁ : Ω → Set ℂ} (hA₁ : Measurable[hτ₁.measurableSpace, hittingSigma] A₁)
    (hAK₁ : ∀ᵐ ω ∂P, A₁ ω =
      (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ₁ ω).untopD 0 : ℝ≥0))
    -- the counterflow
    {mL mR : ℕ} {yL : Fin mL → ℝ} {yR : Fin mR → ℝ} {σL : Fin mL → ℝ} {σR : Fin mR → ℝ}
    {𝓕' : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin mL → ℝ≥0 → Ω → ℝ} {VR' : Fin mR → ℝ≥0 → Ω → ℝ}
    {B' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {h₂ : Ω → DistOn upperHalfPlaneOpens}
    (hC' : IsOptionalHullCoupling κ' yL yR σL σR P 𝓕' W' VL' VR' B' ζ' h₂)
    (htr' : ∀ ω, IsChartTransport (Sec4.stripCounterflowChart q) (-1) a k (h ω) (h₂ ω))
    (hX' : IsMeasurableKilledDriving W' VL' VR' ζ')
    {τ₂ : Ω → WithTop ℝ≥0} (hτ₂ : IsStoppingTime (drivingFiltration P hX') τ₂)
    (hτ₂ζ : ∀ᵐ ω ∂P, (τ₂ ω : ℝ≥0∞) < ζ' ω) {A₂ : Ω → Set ℂ}
    (hA₂ : Measurable[hτ₂.measurableSpace, hittingSigma] A₂)
    (hAK₂ : ∀ᵐ ω ∂P, A₂ ω = (Sec4.stripCounterflowChart q).2.1 ''
      fwdHull (fun s : ℝ => W' s.toNNReal ω) ((τ₂ ω).untopD 0 : ℝ≥0))
    -- the strip hypothesis
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    -- the union mean and the two words' data
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) P g)
    {u₁ : Ω → ℂ → ℝ}
    (hu₁ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ₁ ω).untopD 0) ω - W ((τ₁ ω).untopD 0) ω)
        (fun i => VR i ((τ₁ ω).untopD 0) ω - W ((τ₁ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ₁ ω).untopD 0) ω - W ((τ₁ ω).untopD 0) ω)
        (fun i => VR i ((τ₁ ω).untopD 0) ω - W ((τ₁ ω).untopD 0) ω)) (u₁ ω))
    {u₂ : Ω → ℂ → ℝ}
    (hu₂ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ' σL σR (fun i => VL' i ((τ₂ ω).untopD 0) ω - W' ((τ₂ ω).untopD 0) ω)
        (fun i => VR' i ((τ₂ ω).untopD 0) ω - W' ((τ₂ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL' i ((τ₂ ω).untopD 0) ω - W' ((τ₂ ω).untopD 0) ω)
        (fun i => VR' i ((τ₂ ω).untopD 0) ω - W' ((τ₂ ω).untopD 0) ω)) (u₂ ω)) :
    ∀ᵐ ω ∂P, ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (A₁ ω ∪ A₂ ω)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) → g ω φ = ∫ z, w z * φ z) ∧
      (∀ z₀ ∈ A₁ ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A₂ ω ∩ ball z₀ r ⊆ A₁ ω) →
        Tendsto (fun z => w z - (couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ₁ ω).untopD 0 : ℝ≥0) (u₁ ω)
          (z - x) - c - u₀ z)) (𝓝[H \ (A₁ ω ∪ A₂ ω)] z₀) (𝓝 0)) ∧
      (∀ z₀ ∈ A₂ ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A₁ ω ∩ ball z₀ r ⊆ A₂ ω) →
        Tendsto (fun z => w z - (-couplingMean κ' (fun s : ℝ => W' s.toNNReal ω) ((τ₂ ω).untopD 0 : ℝ≥0) (u₂ ω)
          ((Sec4.stripCounterflowChart q).1 z) + cfShift q a k z - u₀ z)) (𝓝[H \ (A₁ ω ∪ A₂ ω)] z₀) (𝓝 0)) := by
  have hA₁m : Measurable[mΩ, hittingSigma] A₁ := hA₁.mono hτ₁.measurableSpace_le le_rfl
  have hA₂m : Measurable[mΩ, hittingSigma] A₂ := hA₂.mono hτ₂.measurableSpace_le le_rfl
  have hci' := condIndepEv_stopped_strip hκ hκ' hhm hC hX htr hτ₁ hC' hX' hτ₂ hci
  rw [← WholeField.comap_sub_dist h (smoothDist upperHalfPlaneOpens u₀)] at hci'
  have hciA : CondIndepEv (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P :=
    condIndepEv_mono hci' hA₁.comap_le hA₂.comap_le
  -- the two local sets and their means
  have hloc₁ : IsLocalSet A₁ (WholeField.centredField h u₀) P :=
    Coupling.IsLocalSet.congr_set (Sec7.SideHeight.isLocalSet_flowHull hC htrans hu₀ hu₀' hrel hX hτ₁ hτ₁ζ) hAK₁
  have hloc₂ : IsLocalSet A₂ (WholeField.centredField h u₀) P := by
    obtain ⟨-, -, -, hXc, hker⟩ := hC'
    have hK := (hker τ₂ hτ₂ hτ₂ζ).1
    exact Coupling.IsLocalSet.congr_set (WholeField.IsLocalSet.sub_dist (isLocalSet_stripInv_image hq hK htr')
      (WholeField.isHarmonicDistOn_smoothDist hu₀)) hAK₂
  obtain ⟨gA₁, hgA₁⟩ := IsLocalSet.exists_isLocalSetMean hh0 hA₁m hloc₁
  obtain ⟨gA₂, hgA₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 hA₂m hloc₂
  have hid₁ := Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull hC hκ htrans hh0 hu₀ hu₀' hrel hX hτ₁ hτ₁ζ
    hA₁m hAK₁ hgA₁ hu₁
  have hid₂ := ae_apply_eq_of_isLocalSetMean_stripInvHull hq hκ' hC' htr' hu₀ hh0 hX' hτ₂ hτ₂ζ hA₂m hAK₂ hgA₂ hu₂
  -- the candidates are harmonic off the hulls; the hulls have unbounded lower unions
  have hτ₁ζ' : ∀ᵐ ω ∂P, (((τ₁ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hτ₁ζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  have hτ₂ζ' : ∀ᵐ ω ∂P, (((τ₂ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ' ω :=
    hτ₂ζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  have hharm₁ : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd
      (fun z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ₁ ω).untopD 0 : ℝ≥0) (u₁ ω) (z - x) - c - u₀ z)
      (H \ A₁ ω) := by
    filter_upwards [hC.1.2.2.2.2, hτ₁ζ', hAK₁] with ω hp hlt hAω
    rw [hAω]
    exact Sec7.SideHeight.harmonicOnNhd_flowMean hp.2.2.2.1 hlt (hu₁ ω).1 x c hu₀
  have hharm₂ : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd
      (fun z => -couplingMean κ' (fun s : ℝ => W' s.toNNReal ω) ((τ₂ ω).untopD 0 : ℝ≥0) (u₂ ω)
        ((Sec4.stripCounterflowChart q).1 z) + cfShift q a k z - u₀ z) (H \ A₂ ω) := by
    filter_upwards [hC'.1.2.2.2.2, hτ₂ζ', hAK₂] with ω hp hlt hAω
    rw [hAω]
    exact harmonicOnNhd_cfMean hq a k (Sec7.SideHeight.harmonicOnNhd_couplingMean_rpath hp.2.2.2.1 hlt (hu₂ ω).1)
      hu₀
  have hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z) := by
    filter_upwards [hC.1.2.2.2.2, hτ₁ζ', hAK₁] with ω hp hlt hAω
    rw [hAω]
    exact not_isBounded_lowerUnion_add_image (isHPHull_fwdHull_rpath hp.2.2.2.1 hlt) x
  have hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z) := by
    filter_upwards [hC'.1.2.2.2.2, hτ₂ζ', hAK₂] with ω hp hlt hAω
    rw [hAω]
    exact not_isBounded_lowerUnion_stripInv_image hq (isHPHull_fwdHull_rpath hp.2.2.2.1 hlt)
  filter_upwards [ae_union_boundary_of_condIndepEv hh0 hA₁m hA₂m hciA hloc₁ hloc₂ hunb₁ hunb₂ hg hgA₁ hgA₂,
    hid₁, hid₂, hharm₁, hharm₂] with ω hω h1 h2 hh1 hh2
  exact hω _ _ hh1 h1 hh2 h2

end Strip

end InteractingSLE.Sec5.CrossRestart
