/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37GermFinishFill
import InteractingSLE.Spec.Sec5.GlueCondUnionImgMean
import InteractingSLE.Spec.Sec5.GlueCondMean

/-!
# Aux. lemma 37 at one rational witness: the counterflow hull's own germ (G2)

Packet PROVE-STRIPSYS39, item (1). Specification §6.2, Aux. lemma 36 ("Boundary data on the exposed counterflow part",
`source/spec/p193-240.md` L62, p. 196) and Aux. lemma 37's proof ((PFI3), L118–L120, p. 199).

The counterflow hull at a fixed time `s`, read in the flow chart, is `cfHull W′ ζ′ s = m(K′_s)` (`m z = −1/z`). Its
conditional mean is explicit (`GlueCond.exists_isLocalSetMean_cfHullQ`): off the hull it is
`−𝔥′_s ∘ m + u′ ∘ m`, with `𝔥′_s = couplingMean (16/κ) W′ s uG` the counterflow's own coupling mean (parameter
`κ′ = 16/κ`) and `u′` the harmonic extension of the counterflow word's data. We read it in the **counterflow chart**
`Ψ = m ∘ f_s ∘ m` (`WangWu.revChart`) with the derivative lift `L_Ψ` (`GlueImg.logDerivPsi`):

* `explicit_add_eq` (deterministic): `(−𝔥′_s ∘ m + u′ ∘ m) + u_b + χ Im L_Ψ = −uG ∘ f_s ∘ m + 2χ arg Ψ − πχ` off the
  hull (`χ = χ(κ)`; the unbounded terms cancel since `χ(16/κ) = −χ(κ)`, and the two centrings agree,
  `GlueImg.negInv_add_eq_of_returnBHE`);
* `tendsto_cfGerm` (deterministic): along any approach on which `f_s ∘ m` tends to a real `y` in the first constant
  interval of the counterflow word (between the tip and the nearest force point), the right side tends to
  `λ′ − πχ` if `y < 0` and to `−λ′ + πχ = (−λ′ − πχ) + 2πχ` if `y > 0`: the source's counterflow-side heights
  `ε λ′ − πχ` (PFI3) up to the branch shift `2πχ`, which the branch integer of (BR) absorbs;
* **`ae_cfGerm_strip`**: for the strip system, a version of the hull mean whose explicit representative has these
  germs, almost surely;
* **`ae_cfGerm_union_strip`** (G2 for the union): with `Aux37Germ.ae_tendsto_sub_hull`, every harmonic representative
  of the mean of `stripExpl s = cfHull s ∪ walls` has the same germs at every hull point near which the walls lie in
  the hull.

Which side (`y < 0` or `y > 0`) the pocket approach takes is the traversal-side claim (PFI3); it is not proved here.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Bornology Function Complex
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Aux37Assembly

open QuantumZipper (H Hbar chiC fwdHull fwdMap logDerivFwd)
open WangWu (negInv revChart)
open LocalSets Aux119Nested Aux37Germ

/-! ### The explicit hull mean in the counterflow chart -/

section Explicit

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The explicit counterflow-hull mean in the counterflow chart** (deterministic): off `m(K_s)`,
`(−couplingMean (16/κ) w s v ∘ m + u′ ∘ m) + u_b + χ Im L_Ψ = −v ∘ f_s ∘ m + 2χ arg Ψ − πχ`. -/
theorem explicit_add_eq (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {u_b : ℂ → ℝ}
    (hu_b : IsBoundedHarmonicExtension b jumps u_b) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension (Sec5.GlueCond.cfWordData κ b jumps) (Sec5.GlueCond.cfWordJumps κ b jumps) u')
    {w : ℝ → ℝ} (hw : Continuous w) {s : ℝ} (hs : 0 ≤ s) (v : ℂ → ℝ) {z : ℂ}
    (hz : z ∈ H \ negInv '' fwdHull w s) :
    (-couplingMean (16 / κ) w s v (negInv z) + u' (negInv z)) + u_b z +
        chiC κ * (Sec5.GlueImg.logDerivPsi w s z).im =
      -v (fwdMap w s (negInv z)) + 2 * chiC κ * arg (revChart w s z) - π * chiC κ := by
  have h1 := Sec5.GlueImg.neg_couplingMean_add_chiC_mul hκ hw hs v hz
  have h2 := Sec5.GlueImg.negInv_add_eq_of_returnBHE hκ hb hu_b hu' hz.1
  have e : negInv (revChart w s z) = fwdMap w s (negInv z) := by
    rw [revChart, WangWu.negInv_negInv]
  rw [e] at h1
  linear_combination h1 + h2

end Explicit

/-! ### The germ at a first-interval boundary point of the counterflow chart -/

section Germ

variable {κ' χ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {pL : Fin nL → ℝ} {pR : Fin nR → ℝ}

/-- The force-word data at a point `y < 0` right of every left force point is `−λ`. -/
theorem forceBoundaryData_of_neg {y : ℝ} (hy : y < 0) (hL : ∀ i, pL i ≤ y) :
    forceBoundaryData κ' ρL ρR pL pR y = -sleLambda κ' := by
  have e : Finset.univ.filter (fun i => y < pL i) = ∅ :=
    Finset.filter_false_of_mem fun i _ => not_lt.2 (hL i)
  simp only [forceBoundaryData, hy, ↓reduceIte, e, Finset.sum_empty, add_zero, mul_one, sleLambda]

/-- The force-word data at a point `y > 0` left of every right force point is `λ`. -/
theorem forceBoundaryData_of_pos {y : ℝ} (hy : 0 < y) (hR : ∀ i, y ≤ pR i) (hRy : ∀ i, pR i ≠ y) :
    forceBoundaryData κ' ρL ρR pL pR y = sleLambda κ' := by
  have e : Finset.univ.filter (fun i => pR i ≤ y) = ∅ :=
    Finset.filter_false_of_mem fun i _ h => hRy i (le_antisymm h (hR i))
  simp only [forceBoundaryData, not_lt.2 hy.le, ↓reduceIte, e, Finset.sum_empty, add_zero, mul_one, sleLambda]

/-- **The counterflow-side germ in the counterflow chart** (deterministic): if `f → y` along `F` from `ℍ`, with `y` a
non-jump point of the force word's data in the first constant interval, then `−v ∘ f + 2χ arg(m ∘ f) − πχ` tends to
`λ′ − πχ` (if `y < 0`) or to `−λ′ + πχ` (if `y > 0`), `v` the bounded harmonic extension of the data. -/
theorem tendsto_cfGerm {v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR pL pR) (forceJumpSet pL pR) v)
    {F : Filter ℂ} {f : ℂ → ℂ} (hfH : ∀ᶠ z in F, f z ∈ H) {y : ℝ} (hf : Tendsto f F (𝓝 (y : ℂ)))
    (hyJ : y ∉ forceJumpSet pL pR) :
    (y < 0 → (∀ i, pL i ≤ y) →
      Tendsto (fun z => -v (f z) + 2 * χ * arg (negInv (f z)) - π * χ) F (𝓝 (sleLambda κ' - π * χ))) ∧
    (0 < y → (∀ i, y ≤ pR i) →
      Tendsto (fun z => -v (f z) + 2 * χ * arg (negInv (f z)) - π * χ) F (𝓝 (-sleLambda κ' + π * χ))) := by
  have hfW : Tendsto f F (𝓝[H] (y : ℂ)) := tendsto_nhdsWithin_iff.2 ⟨hf, hfH⟩
  have hvy := (hv.2.2 y hyJ).comp hfW
  have hy0 : y ≠ 0 := fun h => hyJ (h ▸ mem_insert 0 _)
  have hmi : Tendsto (fun z => negInv (f z)) F (𝓝 (negInv (y : ℂ))) :=
    ((WangWu.continuousAt_negInv (by exact_mod_cast hy0)).tendsto).comp hf
  have hmiH : ∀ᶠ z in F, negInv (f z) ∈ H := hfH.mono fun z hz => WangWu.negInv_mem_H hz
  have eny : negInv (y : ℂ) = ((-y⁻¹ : ℝ) : ℂ) := by
    simp only [negInv, ofReal_neg, ofReal_inv]
  refine ⟨fun hy hL => ?_, fun hy hR => ?_⟩
  · rw [forceBoundaryData_of_neg hy hL] at hvy
    have hpos : (0 : ℝ) < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy)
    have harg : Tendsto (fun z => arg (negInv (f z))) F (𝓝 0) := by
      have hc := (continuousAt_arg (x := ((-y⁻¹ : ℝ) : ℂ)) (ofReal_mem_slitPlane.2 hpos)).tendsto
      rw [arg_ofReal_of_nonneg hpos.le] at hc
      rw [eny] at hmi
      exact hc.comp hmi
    have := ((hvy.neg).add (harg.const_mul (2 * χ))).sub_const (π * χ)
    have e : sleLambda κ' - π * χ = - -sleLambda κ' + 2 * χ * 0 - π * χ := by ring
    rw [e]
    exact this
  · have hRy : ∀ i, pR i ≠ y := fun i h => hyJ (mem_insert_of_mem 0 (Or.inr ⟨i, h⟩))
    rw [forceBoundaryData_of_pos hy hR hRy] at hvy
    have hneg : -y⁻¹ < (0 : ℝ) := neg_neg_iff_pos.2 (inv_pos.2 hy)
    have harg : Tendsto (fun z => arg (negInv (f z))) F (𝓝 π) := by
      have hc := tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (z := ((-y⁻¹ : ℝ) : ℂ))
        (by rw [ofReal_re]; exact hneg) (ofReal_im _)
      rw [eny] at hmi
      refine hc.comp (tendsto_nhdsWithin_iff.2 ⟨hmi, hmiH.mono fun z hz => ?_⟩)
      exact (show 0 < (negInv (f z)).im from hz).le
    have := ((hvy.neg).add (harg.const_mul (2 * χ))).sub_const (π * χ)
    have e : -sleLambda κ' + π * χ = -sleLambda κ' + 2 * χ * π - π * χ := by ring
    rw [e]
    exact this

end Germ

/-! ### The strip system: the hull mean's germ, almost surely -/

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

open Sec5.GlueCond Sec7.StripSysField in
/-- **(G2) the counterflow hull's own germ, almost surely** (Aux. lemma 36, "Boundary data on the exposed counterflow
part", p. 196). For the strip system and the bounded harmonic extension `u₀` of its data `b`, at a deterministic time
`s`, the counterflow hull `cfHull W′ ζ′ s` has a mean `gA` for `h − u₀` with, almost surely, a harmonic representative
`wA` such that: along every approach `F` that eventually stays off the hull and on which `f_s ∘ m` (the counterflow's
centred Loewner map read in the flow chart) tends to a real `y` off the force word's jumps, `wA + u₀ + χ Im L_Ψ` tends
to `λ′ − πχ` if `y < 0` lies right of every left force position, and to `−λ′ + πχ` if `y > 0` lies left of every right
force position (`λ′ = λ(16/κ)`, `L_Ψ` the derivative lift of the counterflow chart `Ψ = m ∘ f_s ∘ m`). -/
theorem ae_cfGerm_strip {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
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
    filter_upwards [StripPocketPath.ae_counterflow_trace hS hcumL hcumR] with ω hω
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
/-- **(G2) for the union**: for the strip system, two transient walls `Lw`, `Rw` with Lemma 6.2's inputs, a version
`g` of the mean of `stripExpl W′ ζ′ Lw Rw s = cfHull s ∪ walls`: almost surely, every harmonic representative `v` of
`g` has, at every hull point `z₀` near which the walls lie in the hull, along every approach `F` from off the union on
which `f_s ∘ m` tends to a real non-jump `y` of the counterflow word, the germ `λ′ − πχ` (`y < 0` in the first left
interval) or `−λ′ + πχ` (`y > 0` in the first right interval) of `v + u₀ + χ Im L_Ψ`. -/
theorem ae_cfGerm_union_strip {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
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
  obtain ⟨gA, hgA, hae⟩ := ae_cfGerm_strip hS hcumL hcumR hu₀ s
  have hsub := ae_tendsto_sub_hull hX hLc hL0 hLm hLdet hLloc hRc hR0 hRm hRdet hRloc htr
    (measurable_cfHull hS.counterflow s) (isLocalSet_cfHull hS hcumL hcumR u₀ hu₀.1 s)
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

end Strip

end InteractingSLE.Sec7.Aux37Assembly
