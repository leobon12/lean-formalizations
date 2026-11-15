/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSafeConst
import InteractingSLE.Spec.Sec7.Aux37AssemblyCfGerm
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofStrip

/-!
# The constant-angle strip system: the counterflow hull's germ and the flat clock of the strip exploration

Packet PROVE-STRIPSYS-SAFE. Ports to `StripSafe.IsConstStripSystem` (same statements with the strip-system hypothesis
weakened, same proofs) of PROVE-AUX37-WALLS' / PROVE-FLATCLOCK's strip-system lemmas, which use the strip system only
through its field, data and counterflow:

* `ae_cfGerm_strip`, `ae_cfGerm_union_strip` (from `Aux37Assembly`, file `Aux37AssemblyCfGerm.lean`): (G2) the
  counterflow hull's own germ, for the hull and for its union with two walls;
* `stripExpl_markedLaw`, `flatClockStatement_stripExpl_of_walls`, `exists_isLocalSetMean_stripExpl_of_walls` (from
  `FlatClockProof`, file `Aux37FlatClockProofStrip.lean`): the marked law and the flat clock of the strip exploration
  `m⁻¹(K′_t) ∪ α ∪ β`.

R48: no Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Sec7.StripSafe

/-! ### (G2) the counterflow hull's own germ -/

section Germ

open MeasureTheory Set Metric Filter Topology Bornology Function Complex
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar chiC fwdHull fwdMap logDerivFwd)
open WangWu (negInv revChart)
open LocalSets Aux119Nested Aux37Germ Aux37Assembly

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

open Sec5.GlueCond Sec7.StripSysField in
/-- (Port to `IsConstStripSystem`.)
**(G2) the counterflow hull's own germ, almost surely** (Aux. lemma 36, "Boundary data on the exposed counterflow
part", p. 196). For the strip system and the bounded harmonic extension `u₀` of its data `b`, at a deterministic time
`s`, the counterflow hull `cfHull W′ ζ′ s` has a mean `gA` for `h − u₀` with, almost surely, a harmonic representative
`wA` such that: along every approach `F` that eventually stays off the hull and on which `f_s ∘ m` (the counterflow's
centred Loewner map read in the flow chart) tends to a real `y` off the force word's jumps, `wA + u₀ + χ Im L_Ψ` tends
to `λ′ − πχ` if `y < 0` lies right of every left force position, and to `−λ′ + πχ` if `y > 0` lies left of every right
force position (`λ′ = λ(16/κ)`, `L_Ψ` the derivative lift of the counterflow chart `Ψ = m ∘ f_s ∘ m`). -/
theorem ae_cfGerm_strip {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsConstStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (s : ℝ≥0) :
    ∃ gA : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (cfHull W' ζ' s) (WholeField.centredField h u₀) P gA ∧
      ∀ᵐ ω ∂P, ∃ wA : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wA (H \ cfHull W' ζ' s ω) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHull W' ζ' s ω → gA ω φ = ∫ z, wA z * φ z) ∧
        ∀ F : Filter ℂ, (∀ᶠ z in F, z ∈ H \ cfHull W' ζ' s ω) → ∀ y : ℝ,
          Tendsto (fun z => fwdMap (fun r : ℝ => W' r.toNNReal ω) s (negInv z)) F (𝓝 (y : ℂ)) →
          y ∉ forceJumpSet (cfPosL κ b jumps (W' · ω) s) (cfPosR κ b jumps (W' · ω) s) →
          (y < 0 → (∀ i, cfPosL κ b jumps (W' · ω) s i ≤ y) →
            Tendsto (fun z => wA z + u₀ z +
                chiC κ * (Sec5.GlueImg.logDerivPsi (fun r : ℝ => W' r.toNNReal ω) s z).im) F
              (𝓝 (sleLambda (16 / κ) - π * chiC κ))) ∧
          (0 < y → (∀ i, y ≤ cfPosR κ b jumps (W' · ω) s i) →
            Tendsto (fun z => wA z + u₀ z +
                chiC κ * (Sec5.GlueImg.logDerivPsi (fun r : ℝ => W' r.toNNReal ω) s z).im) F
              (𝓝 (-sleLambda (16 / κ) + π * chiC κ))) := by
  have hκ := hS.kappa_pos
  have hb := hS.boundaryData
  have hreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous fun t => W' t ω := by
    filter_upwards [StripSafe.ae_counterflow_trace hS hcumL hcumR] with ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.1⟩
  obtain ⟨u', hu'⟩ : ∃ u' : ℂ → ℝ, IsBoundedHarmonicExtension (cfWordData κ b jumps) (cfWordJumps κ b jumps) u' := by
    obtain ⟨u', hu'⟩ := WholeField.exists_bhe (16 / κ)
      (flowLineRhoL (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0)
      (flowLineRhoR (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0)
      (flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0)
      (flowLineXR (counterflowData κ b) (counterflowJumps jumps) 0)
    refine ⟨u', ?_⟩
    simp only [cfWordData, cfWordJumps, Sec5.Cond44Ref.coe_forceJumpFinset]
    exact hu'
  set uG : Ω → ℂ → ℝ := fun ω => Classical.choose (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps)
    (cfRhoR κ b jumps) (cfPosL κ b jumps (W' · ω) s) (cfPosR κ b jumps (W' · ω) s)) with huGdef
  have huG : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
        (cfPosL κ b jumps (W' · ω) s) (cfPosR κ b jumps (W' · ω) s))
      (forceJumpSet (cfPosL κ b jumps (W' · ω) s) (cfPosR κ b jumps (W' · ω) s)) (uG ω) := fun ω =>
    Classical.choose_spec (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps)
      (cfRhoR κ b jumps) (cfPosL κ b jumps (W' · ω) s) (cfPosR κ b jumps (W' · ω) s))
  obtain ⟨g, hg, hid⟩ := exists_isLocalSetMean_cfHullQ hκ hb hS.gff hS.counterflow hreg hu₀ hu' s huG
  refine ⟨g, hg, ?_⟩
  filter_upwards [hid, hreg] with ω hidω hω
  set w : ℝ → ℝ := fun r : ℝ => W' r.toNNReal ω with hwdef
  have hw : Continuous w := hω.2.2.comp continuous_real_toNNReal
  have hK : cfHull W' ζ' s ω = negInv '' fwdHull w s := by
    simp only [cfHull, cfHullQ]
    rw [hullAt_cfHistory hω.1 hω.2.1 hω.2.2]
  have hO : IsOpen (H \ fwdHull w s) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw s.coe_nonneg
  refine ⟨fun z => -couplingMean (16 / κ) w s (uG ω) (negInv z) + u' (negInv z), ?_, hidω, ?_⟩
  · have h1 := WangWu.harmonicOnNhd_comp_negInv hO sdiff_subset
      (Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := 16 / κ) hw s.coe_nonneg (huG ω).1)
    have h2 := WangWu.harmonicOnNhd_comp_negInv QuantumZipper.isOpen_H subset_rfl hu'.1
    intro z hz
    rw [hK, WangWu.H_diff_image_negInv] at hz
    exact (h1 z hz).neg.add (h2 z (image_mono sdiff_subset hz))
  · intro F hFH y hy hyJ
    have hFH' : ∀ᶠ z in F, z ∈ H \ negInv '' fwdHull w s := by rw [← hK]; exact hFH
    have hfH : ∀ᶠ z in F, fwdMap w s (negInv z) ∈ H := hFH'.mono fun z hz =>
      QuantumZipper.FwdHolo.mapsTo_fwdMap hw s.coe_nonneg (WangWu.negInv_notMem_fwdHull hz)
    have heq : (fun z => -(uG ω) (fwdMap w s (negInv z)) + 2 * chiC κ * arg (negInv (fwdMap w s (negInv z))) -
        π * chiC κ) =ᶠ[F] fun z => (-couplingMean (16 / κ) w s (uG ω) (negInv z) + u' (negInv z)) + u₀ z +
          chiC κ * (Sec5.GlueImg.logDerivPsi w s z).im := by
      filter_upwards [hFH'] with z hz
      exact (explicit_add_eq hκ hb hu₀ hu' hw s.coe_nonneg (uG ω) hz).symm
    obtain ⟨hneg, hpos⟩ := tendsto_cfGerm (χ := chiC κ) (huG ω) hfH hy hyJ
    exact ⟨fun h1 h2 => (hneg h1 h2).congr' heq, fun h1 h2 => (hpos h1 h2).congr' heq⟩

open Sec5.GlueCond Sec7.StripSysField in
/-- (Port to `IsConstStripSystem`.)
**(G2) for the union**: for the strip system, two transient walls `Lw`, `Rw` with Lemma 6.2's inputs, a version
`g` of the mean of `stripExpl W′ ζ′ Lw Rw s = cfHull s ∪ walls`: almost surely, every harmonic representative `v` of
`g` has, at every hull point `z₀` near which the walls lie in the hull, along every approach `F` from off the union on
which `f_s ∘ m` tends to a real non-jump `y` of the counterflow word, the germ `λ′ − πχ` (`y < 0` in the first left
interval) or `−λ′ + πχ` (`y > 0` in the first right interval) of `v + u₀ + χ Im L_Ψ`. -/
theorem ae_cfGerm_union_strip {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsConstStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {Lw Rw : Ω → ℝ≥0 → ℂ}
    (hLc : ∀ ω, Continuous (Lw ω)) (hL0 : ∀ ω, Lw ω 0 = 0) (hLm : ∀ t, Measurable fun ω => Lw ω t)
    (hLdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Lw ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hLloc : Sec6.IsEntranceHistoryLocal Lw (WholeField.centredField h u₀) P)
    (hRc : ∀ ω, Continuous (Rw ω)) (hR0 : ∀ ω, Rw ω 0 = 0) (hRm : ∀ t, Measurable fun ω => Rw ω t)
    (hRdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Rw ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hRloc : Sec6.IsEntranceHistoryLocal Rw (WholeField.centredField h u₀) P)
    (htr : ∀ᵐ ω ∂P, Tendsto (Lw ω) atTop (cobounded ℂ) ∧ Tendsto (Rw ω) atTop (cobounded ℂ)) (s : ℝ≥0)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (stripExpl W' ζ' Lw Rw s) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ stripExpl W' ζ' Lw Rw s ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ stripExpl W' ζ' Lw Rw s ω → g ω φ = ∫ z, v z * φ z) →
      ∀ z₀ ∈ cfHull W' ζ' s ω, (∃ ε > 0, wallUnion Lw Rw ω ∩ ball z₀ ε ⊆ cfHull W' ζ' s ω) →
      ∀ F : Filter ℂ, F ≤ 𝓝[H \ stripExpl W' ζ' Lw Rw s ω] z₀ → ∀ y : ℝ,
        Tendsto (fun z => fwdMap (fun r : ℝ => W' r.toNNReal ω) s (negInv z)) F (𝓝 (y : ℂ)) →
        y ∉ forceJumpSet (cfPosL κ b jumps (W' · ω) s) (cfPosR κ b jumps (W' · ω) s) →
        (y < 0 → (∀ i, cfPosL κ b jumps (W' · ω) s i ≤ y) →
          Tendsto (fun z => v z + u₀ z +
              chiC κ * (Sec5.GlueImg.logDerivPsi (fun r : ℝ => W' r.toNNReal ω) s z).im) F
            (𝓝 (sleLambda (16 / κ) - π * chiC κ))) ∧
        (0 < y → (∀ i, y ≤ cfPosR κ b jumps (W' · ω) s i) →
          Tendsto (fun z => v z + u₀ z +
              chiC κ * (Sec5.GlueImg.logDerivPsi (fun r : ℝ => W' r.toNNReal ω) s z).im) F
            (𝓝 (-sleLambda (16 / κ) + π * chiC κ))) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  obtain ⟨gA, hgA, hae⟩ := StripSafe.ae_cfGerm_strip hS hcumL hcumR hu₀ s
  have hsub := ae_tendsto_sub_hull hX hLc hL0 hLm hLdet hLloc hRc hR0 hRm hRdet hRloc htr
    (measurable_cfHull hS.counterflow s) (StripSafe.isLocalSet_cfHull hS hcumL hcumR u₀ hu₀.1 s)
    (Eventually.of_forall (not_isBounded_lowerUnion_cfHull W' ζ' s)) hg hgA
  filter_upwards [hsub, hae] with ω hsubω ⟨wA, hwA, hwAr, hgerm⟩ v hv hvr z₀ hz₀ hε F hF y hy hyJ
  have hd := (hsubω v wA hv hvr hwA hwAr z₀ hz₀ hε).mono_left hF
  have hFA : ∀ᶠ z in F, z ∈ H \ cfHull W' ζ' s ω := by
    have h1 : ∀ᶠ z in F, z ∈ H \ stripExpl W' ζ' Lw Rw s ω := hF self_mem_nhdsWithin
    exact h1.mono fun z hz => ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  obtain ⟨hneg, hpos⟩ := hgerm F hFA y hy hyJ
  have e : ∀ z, v z + u₀ z + chiC κ * (Sec5.GlueImg.logDerivPsi (fun r : ℝ => W' r.toNNReal ω) s z).im =
      (v z - wA z) + (wA z + u₀ z +
        chiC κ * (Sec5.GlueImg.logDerivPsi (fun r : ℝ => W' r.toNNReal ω) s z).im) := fun z => by ring
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · have := hd.add (hneg h1 h2)
    rw [zero_add] at this
    simpa only [← e] using this
  · have := hd.add (hpos h1 h2)
    rw [zero_add] at this
    simpa only [← e] using this


end Germ

/-! ### The flat clock of the strip exploration -/

section Clock

open MeasureTheory ProbabilityTheory Filter Set Topology Bornology
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open WangWu (negInv reflectField)
open LocalSets Aux119Nested Aux37Germ FlatClockProof
open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (Port to `IsConstStripSystem`.)
**The marked law of the strip exploration** (Aux. lemma 37, pp. 197–198: "its marked filtration and its Gaussian
kernels"): for the strip system's counterflow and two complete walls `β`, `α` with Lemma 6.2's inputs there are marks
`ℋ_t ≤ mΩ`, increasing in `t` (here `σ(walls' full histories) ∨ 𝓕′_t`), such that at every time `t` the exploration
`E_t = stripExpl W′ ζ′ β α t` is a history-marked local set of the centred field with marks `ℋ_t`; `E_r` is recorded by
`σ(E_s) ∨ ℋ_s` up to null sets for `r ≤ s`; `E_t` is hitting-measurable and almost surely relatively closed in `ℍ`;
and `E_r ⊆ E_s` almost surely for `r ≤ s`. -/
theorem stripExpl_markedLaw {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsConstStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β α : Ω → ℝ≥0 → ℂ}
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ)) :
    ∃ ℋ : ℝ≥0 → MeasurableSpace Ω, (∀ t, ℋ t ≤ mΩ) ∧ (∀ r s : ℝ≥0, r ≤ s → ℋ r ≤ ℋ s) ∧
      (∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P) ∧
      (∀ r s : ℝ≥0, r ≤ s → MeasurableSpace.comap (stripExpl W' ζ' β α r) hittingSigma ≤
        aeSigma (MeasurableSpace.comap (stripExpl W' ζ' β α s) hittingSigma ⊔ ℋ s) P) ∧
      (∀ t, Measurable[mΩ, hittingSigma] (stripExpl W' ζ' β α t)) ∧
      (∀ t, ∀ᵐ ω ∂P, stripExpl W' ζ' β α t ω ⊆ H ∧ IsOpen (H \ stripExpl W' ζ' β α t ω)) ∧
      (∀ r s : ℝ≥0, r ≤ s → ∀ᵐ ω ∂P, stripExpl W' ζ' β α r ω ⊆ stripExpl W' ζ' β α s ω) := by
  have hκ := hS.kappa_pos
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hXm := hX.measurable
  /- the walls -/
  set η : Fin 2 → Ω → ℝ≥0 → ℂ := ![β, α] with hη
  have hc : ∀ i ω, Continuous (η i ω) := fun i ω => by
    fin_cases i
    · exact hβc ω
    · exact hαc ω
  have h0 : ∀ i ω, η i ω 0 = (fun _ => (0 : ℂ)) i := fun i ω => by
    fin_cases i
    · exact hβ0 ω
    · exact hα0 ω
  have hm : ∀ i t, Measurable fun ω => η i ω t := fun i t => by
    fin_cases i
    · exact hβm t
    · exact hαm t
  have hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω) := fun i t => by
    fin_cases i
    · exact hβdet t
    · exact hαdet t
  have hloc : ∀ i, Sec6.IsEntranceHistoryLocal (η i) (WholeField.centredField h u₀) P := fun i => by
    fin_cases i
    · exact hβloc
    · exact hαloc
  have hΓeq : ∀ ω, (⋃ i, range (η i ω)) ∩ H = wallUnion β α ω := fun ω => by
    rw [wallUnion_eq_explored, PocketStopWalls.explored_top]
  have hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G → GFF.IsMarkovDecomposition U upperHalfPlaneOpens
        (WholeField.centredField h u₀) (fun ω => G (WholeField.centredField h u₀ ω)) P →
      ∀ B : Set (Fin 2 → Sec6.Hist), MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (wallUnion β α ω) U} ∩ PocketStopWalls.fullHist η ⁻¹' B =ᵐ[P]
          (fun ω => markovCompl G (WholeField.centredField h u₀ ω)) ⁻¹' B' := by
    intro U G hUH hG hd B hB
    obtain ⟨B', hB', he⟩ := PocketStopWalls.walls_determinedLocal hXm hc h0 hm hdet hloc U G hUH hG hd B hB
    refine ⟨B', hB', ?_⟩
    simpa only [hΓeq] using he
  obtain ⟨hΓm, hΓloc, -⟩ := isLocalSet_wallUnion hX hβc hβ0 hβm hβdet hβloc hαc hα0 hαm hαdet hαloc htr
  have hΓX := measurable_wallUnion_fullHist hβc hαc
  have hXfm : Measurable (PocketStopWalls.fullHist η) := PocketStopWalls.measurable_fullHist hm
  /- the counterflow -/
  have hreg := StripSafe.ae_counterflow_trace hS hcumL hcumR
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ := hreg.mono fun ω hω => hω.1
  obtain ⟨b', J', h', -, htrc, hfl⟩ := hS.counterflow
  obtain ⟨h'', 𝓕c, VL, VR, B, htac, hC⟩ := hfl
  have e : h'' = h' := funext fun ω =>
    Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
  subst e
  have hXc := hC.2.2.2.1
  have hκ' : (0 : ℝ) < 16 / κ := by positivity
  set 𝓕 := drivingFiltration P hXc with h𝓕
  have : 𝓕.IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  -- the centred field read in the counterflow chart
  set D : DistOn upperHalfPlaneOpens :=
    Sec5.CrossCond.cfShiftDist κ u₀ + smoothDist upperHalfPlaneOpens (fun _ => π / 2 * chiC κ) with hD
  have hDh : IsHarmonicDistOn D H :=
    Coupling.IsHarmonicDistOn.add' QuantumZipper.isOpen_H (Sec5.CrossCond.isHarmonicDistOn_cfShiftDist κ hu₀.1)
      (WholeField.isHarmonicDistOn_smoothDist fun _ _ => InnerProductSpace.harmonicAt_const _)
  have hfield : WholeField.centredField h u₀ = fun ω => reflectField (h'' ω) - D := by
    funext ω
    have e1 := Sec5.CrossCond.cenT_eq_reflectField_sub κ u₀ (htrc ω)
    rw [Sec5.GlueCond.cenT_eq_add_sub] at e1
    rw [hD, sub_add_eq_sub_sub, ← e1]
    simp only [WholeField.centredField]
    abel
  -- the hull process in the flow chart
  set K : ℝ≥0 → Ω → Set ℂ := fun t ω => negInv '' PocketStopWallsFin.regHull W' ζ' t ω with hK
  have hKmono : ∀ ω, Monotone fun t => K t ω := fun ω _ _ hst =>
    image_mono (PocketStopWallsFin.regHull_mono W' ζ' ω hst)
  have hKdisj : ∀ (S : Set ℂ) (U : Set ℂ), U ⊆ H → (Disjoint (negInv '' S) U ↔ Disjoint S (negInv '' U)) :=
    fun S U hUH => by
      rw [PocketStopWallsFin.disjoint_image_negInv_iff hUH]
      exact disjoint_inter_H_iff (image_subset_iff.2 fun z hz => WangWu.negInv_mem_H (hUH hz))
  have hKad : ∀ (t : ℝ≥0) (U : Set ℂ), IsOpen U → U ⊆ H → MeasurableSet[𝓕 t] {ω | Disjoint (K t ω) U} := by
    intro t U hUo hUH
    have hU' : negInv '' U ⊆ H := image_subset_iff.2 fun z hz => WangWu.negInv_mem_H (hUH hz)
    have e : {ω | Disjoint (K t ω) U} = {ω | Disjoint (PocketStopWallsFin.regHull W' ζ' t ω) (negInv '' U)} := by
      ext ω
      exact hKdisj _ U hUH
    rw [e]
    exact PocketStopWallsFin.measurableSet_disjoint_regHull hC hκ' hXc hζ t (negInv '' U)
      (WangWu.isOpen_image_negInv hUo hUH) hU'
  have hKst : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) → ∀ U : Set ℂ, IsOpen U →
      U ⊆ H → MeasurableSet[hτ.measurableSpace] {ω | Disjoint (K ((τ ω).untopD 0) ω) U} := by
    intro τ hτ hfin U hUo hUH
    have hU' : negInv '' U ⊆ H := image_subset_iff.2 fun z hz => WangWu.negInv_mem_H (hUH hz)
    have e : {ω | Disjoint (K ((τ ω).untopD 0) ω) U} =
        {ω | Disjoint (PocketStopWallsFin.regHull W' ζ' ((τ ω).untopD 0) ω) (negInv '' U)} := by
      ext ω
      exact hKdisj _ U hUH
    rw [e]
    exact PocketStopWallsFin.measurableSet_disjoint_regHull_stopping hC hκ' hXc hζ τ hτ hfin (negInv '' U)
      (WangWu.isOpen_image_negInv hUo hUH) hU'
  have hlocK : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) →
      WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace (fun ω => K ((τ ω).untopD 0) ω)
        (WholeField.centredField h u₀) P := by
    intro τ hτ hfin
    have hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ' ω := by
      filter_upwards [hζ] with ω hω
      rw [hω]
      exact lt_top_iff_ne_top.2 (by exact_mod_cast hfin ω)
    have hA : Measurable[mΩ, hittingSigma] fun ω => K ((τ ω).untopD 0) ω :=
      WangWu.measurable_image_negInv.comp (PocketStopWallsFin.measurable_regHull hXc
        (PocketStopWallsFin.measurable_untopD_of_isStoppingTime hτ hfin))
    have hAK : ∀ᵐ ω ∂P, K ((τ ω).untopD 0) ω =
        negInv '' fwdHull (fun s : ℝ => W' s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := by
      filter_upwards [PocketStopWallsFin.ae_regHull_eq hC hζ] with ω hω
      simp only [hK, hω]
    have hl := WangWu.isHistoryAvoidanceLocal_reflect_hull hC hκ' hDh hXc hτ hτζ hA hAK
    rwa [← hfield] at hl
  /- the union law of the version `ℍ ∩ (walls ∪ K_t)` at every time -/
  set ℋ : ℝ≥0 → MeasurableSpace Ω := fun t =>
    MeasurableSpace.comap (PocketStopWalls.fullHist η) inferInstance ⊔ 𝓕 t with hℋ
  have hlaw : ∀ t : ℝ≥0, WholeField.IsHistoryAvoidanceLocal (ℋ t)
      (PocketStopWalls.wallsHullAt (wallUnion β α) K fun _ => ((t : WithTop ℝ≥0) : ℝ≥0∞))
      (WholeField.centredField h u₀) P := by
    intro t
    have hl := PocketStopWalls.isHistoryAvoidanceLocal_walls_hull_stoppingTime hXm hXfm hΓm hW hKmono hKad hKst
      hlocK (isStoppingTime_const 𝓕 t)
    rwa [IsStoppingTime.measurableSpace_const] at hl
  /- the version equals the exploration almost surely -/
  have hKeq : ∀ᵐ ω ∂P, ∀ t, cfHull W' ζ' t ω = K t ω := by
    filter_upwards [hreg, PocketStopWallsFin.ae_regHull_eq hC hζ] with ω hω hω' t
    simp only [Aux37Germ.cfHull, Sec5.GlueCond.cfHullQ, hK, Sec5.GlueCond.hullAt_cfHistory hω.1 hω.2.2.1 hω.2.1,
      hω' t]
  have hstrip : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, stripExpl W' ζ' β α t ω = H ∩ (wallUnion β α ω ∪ K t ω) := by
    filter_upwards [hKeq] with ω hω t
    have hWH : wallUnion β α ω ⊆ H := inter_subset_right
    rw [stripExpl, ← hω t, inter_eq_right.2 (union_subset hWH (cfHull_subset_H W' ζ' t ω)), union_comm]
  have hver : ∀ (t : ℝ≥0) (ω : Ω), PocketStopWalls.wallsHullAt (wallUnion β α) K
      (fun _ => ((t : WithTop ℝ≥0) : ℝ≥0∞)) ω = H ∩ (wallUnion β α ω ∪ K t ω) := by
    intro t ω
    simp [PocketStopWalls.wallsHullAt]
  /- the inputs of the nested comparison -/
  have hlocE : ∀ t : ℝ≥0, WholeField.IsHistoryAvoidanceLocal (ℋ t) (stripExpl W' ζ' β α t)
      (WholeField.centredField h u₀) P := by
    intro t
    refine Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae ?_ (hlaw t)
    filter_upwards [hstrip] with ω hω
    rw [hver, hω t]
  have hAm : ∀ t : ℝ≥0, Measurable[mΩ, hittingSigma] (stripExpl W' ζ' β α t) := fun t =>
    FlatClockProof.measurable_union_hitting (measurable_cfHull hS.counterflow t) hΓm
  have hAc : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, stripExpl W' ζ' β α t ω ⊆ H ∧ IsOpen (H \ stripExpl W' ζ' β α t ω) := by
    intro t
    filter_upwards [(StripSafe.isLocalSet_cfHull hS hcumL hcumR u₀ hu₀.1 t).2.1, hΓloc.2.1] with ω h1 h2
    refine ⟨union_subset h1.1 h2.1, ?_⟩
    have e : H \ stripExpl W' ζ' β α t ω = (H \ cfHull W' ζ' t ω) ∩ (H \ wallUnion β α ω) := by
      ext z
      simp only [stripExpl, Set.mem_sdiff, mem_union, mem_inter_iff]
      tauto
    rw [e]
    exact h1.2.inter h2.2
  have hsub : ∀ r s : ℝ≥0, r ≤ s → ∀ᵐ ω ∂P, stripExpl W' ζ' β α r ω ⊆ stripExpl W' ζ' β α s ω := by
    intro r s hrs
    filter_upwards [hstrip] with ω hω
    rw [hω r, hω s]
    exact inter_subset_inter_right _ (union_subset_union_right _ (hKmono ω hrs))
  have hℋle : ∀ t, ℋ t ≤ mΩ := fun t => sup_le hXfm.comap_le (𝓕.le t)
  have hℋmono : ∀ r s : ℝ≥0, r ≤ s → ℋ r ≤ ℋ s := fun r s hrs => sup_le_sup_left (𝓕.mono hrs) _
  have hVm : ∀ t : ℝ≥0, Measurable[ℋ t, hittingSigma] fun ω => H ∩ (wallUnion β α ω ∪ K t ω) := by
    intro t
    refine @measurable_generateFrom Ω (Set ℂ) (ℋ t) _ _ ?_
    rintro _ ⟨U, hUo, hUH, rfl⟩
    have e : (fun ω => H ∩ (wallUnion β α ω ∪ K t ω)) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
        wallUnion β α ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} ∪ {ω | Disjoint (K t ω) U}ᶜ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
      constructor
      · rintro ⟨z, ⟨-, hz | hz⟩, hzU⟩
        · exact Or.inl ⟨z, hz, hzU⟩
        · exact Or.inr ⟨z, hz, hzU⟩
      · rintro (⟨z, hz, hzU⟩ | ⟨z, hz, hzU⟩)
        · exact ⟨z, ⟨hUH hzU, Or.inl hz⟩, hzU⟩
        · exact ⟨z, ⟨hUH hzU, Or.inr hz⟩, hzU⟩
    rw [e]
    exact ((le_sup_left : MeasurableSpace.comap (PocketStopWalls.fullHist η) inferInstance ≤ ℋ t) _
      (hΓX (measurableSet_hitting hUo hUH))).union ((le_sup_right : 𝓕 t ≤ ℋ t) _ (hKad t U hUo hUH)).compl
  have hrec : ∀ r s : ℝ≥0, r ≤ s → MeasurableSpace.comap (stripExpl W' ζ' β α r) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (stripExpl W' ζ' β α s) hittingSigma ⊔ ℋ s) P := by
    intro r s hrs
    rintro _ ⟨B, hB, rfl⟩
    refine ⟨(fun ω => H ∩ (wallUnion β α ω ∪ K r ω)) ⁻¹' B, ?_, ?_⟩
    · exact (le_sup_right : ℋ s ≤ _) _ (hℋmono r s hrs _ (hVm r hB))
    · filter_upwards [hstrip] with ω hω
      change (stripExpl W' ζ' β α r ω ∈ B) = (H ∩ (wallUnion β α ω ∪ K r ω) ∈ B)
      rw [hω r]
  exact ⟨ℋ, hℋle, hℋmono, hlocE, hrec, hAm, hAc, hsub⟩

/-- (Port to `IsConstStripSystem`.)
**The flat clock for the strip exploration** (Aux. lemma 37, p. 198): for the strip system's counterflow and two
complete walls `β`, `α` with Lemma 6.2's inputs, and any versions `g t` of the means of `stripExpl W′ ζ′ β α t`, the
flat clock `FlatClockStatement P univ (stripExpl W′ ζ′ β α) g` holds. -/
theorem flatClockStatement_stripExpl_of_walls {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsConstStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β α : Ω → ℝ≥0 → ℂ}
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ))
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ t : ℝ≥0, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t)) :
    FlatClockStatement P univ (stripExpl W' ζ' β α) g := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  obtain ⟨ℋ, hℋle, hℋmono, hlocE, hrec, hAm, hAc, hsub⟩ := StripSafe.stripExpl_markedLaw hS hcumL hcumR hu₀ hβc hβ0 hβm
    hβdet hβloc hαc hα0 hαm hαdet hαloc htr
  refine flatClockStatement_of_nested (fun t _ => hAc t) (fun r _ s _ hrs => hsub r s hrs) ?_
  intro r _ s _ hrs φ
  exact IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq hX (hAm r) (hAm s) (hℋle r) (hℋle s) (hℋmono r s hrs)
    (hlocE r) (hlocE s) (hAc r) (hAc s) (hsub r s hrs) (hrec r s hrs) (hg r) (hg s) φ

/-- (Port to `IsConstStripSystem`.)
**The strip exploration has versions of its means at every time** (Lemma 3.6, (i) ⇒ (iii), from the marked law):
there is a family `g` with `IsLocalSetMean (stripExpl W′ ζ′ β α t) (centredField h u₀) P (g t)` for every `t`; and
`stripExpl W′ ζ′ β α t` is a local set of the centred field. -/
theorem exists_isLocalSetMean_stripExpl_of_walls {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsConstStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β α : Ω → ℝ≥0 → ℂ}
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ)) :
    (∀ t, IsLocalSet (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P) ∧
      ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
        ∀ t, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  obtain ⟨ℋ, -, -, hlocE, -, hAm, hAc, -⟩ := StripSafe.stripExpl_markedLaw hS hcumL hcumR hu₀ hβc hβ0 hβm
    hβdet hβloc hαc hα0 hαm hαdet hαloc htr
  have hav : ∀ t, IsAvoidanceLocal (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P := fun t =>
    (hlocE t).isAvoidanceLocal
  have hex : ∀ t, ∃ g, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P g := fun t =>
    ((isLocalSet_tfae hX (hAm t) (hAc t)).out 1 3).1 (hav t)
  exact ⟨fun t => ((isLocalSet_tfae hX (hAm t) (hAc t)).out 1 4).1 (hav t),
    fun t => (hex t).choose, fun t => (hex t).choose_spec⟩


end Clock

end InteractingSLE.Sec7.StripSafe
