/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeightRange
import InteractingSLE.Spec.Sec7.Aux70Wire

/-!
# A flow line's side heights: `SinglePathSideHeightStatement`

Packet PROVE-SIDEHEIGHT. Specification §7.2, proof of Aux. lemma 70 (p. 275): "The single-path coupling gives, in the
`gᵢ` coordinate, height `λ − θ₁χ` on the right side of the first trace and height `−λ − θ₂χ` on the left side of the
second". The named statement `SinglePathSideHeightStatement` (`Aux70.lean`, PROVE-LEMMA76) is proved here from the two
named inputs that already feed the first-contact locality and Aux. 70: Lemma 7.5 (`Theorem15.Lemma75Statement`, field
determination) and Aux. lemma 56 at first entrances (`Restart.RetainedRangeEntranceStatement`). They are used only to
make the stopped **range** `η([0, q]) ∩ ℍ` a field-determined local set (Lemma 6.2); everything else comes from the
frozen coupling of the flow line.

The proof, for the angle-`θ` flow line `η` from `x` (coupling field `h' = h(· + x) + θχ`), a deterministic stop `q`
and a version `g` of the range mean:
1. **range = hull off the filling** (`ae_apply_eq_flowMean_of_range`): on `{q < ζ}`, for test functions supported in
   `ℍ \ fill(η([0, q]))`, `g = 𝔥_q(· − x) − θχ − 𝔥₀`, with `𝔥_q` the frozen coupling mean
   (`couplingMean`, driver of the coupling);
2. **harmonic representatives agree** there (`Sec6.eqOn_of_integral_mul_eq`), so along an approach `F` inside
   `ℍ \ fill(η([0, q]))`, `v + 𝔥₀ + χ arg f_q′(· − x) = 𝔥⁰_q(f_q(· − x)) − θχ` (the derivative-lift terms cancel; the
   statement's driver equals the coupling's, `eq_of_isGeneratingTrace`);
3. **side values** (`tendsto_comp_fwdMap_of_pos`, `tendsto_comp_fwdMap_of_neg`): `𝔥⁰_q(f_q) → λ` when `f_q → y > 0`
   and `→ −λ` when `y < 0`, at every point of `ℍ` reached from `ℍ \ K_q`.

## Main results

* **`singlePathSideHeightStatement_of_inputs`**: `Lemma75Statement → RetainedRangeEntranceStatement →
  SinglePathSideHeightStatement`;
* **`aux70Statement_of_inputs'`**: Aux. lemma 70 from Lemma 7.5, Aux. 56 and the deterministic
  `ReverseArcChartStatement` only; the wrappers `lemma77Statement_of_lemma76_of_inputs'`,
  `w8FirstContactStatement_of_lemma76_of_inputs'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace SideHeight

open QuantumZipper (H fwdMap fwdHull)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6

/-- Almost surely equal random sets: a field-determination bound transfers. -/
theorem comap_le_aeSigma_of_ae_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒢 : MeasurableSpace Ω}
    {A A' : Ω → Set ℂ} (hAA' : A =ᵐ[P] A') (h : MeasurableSpace.comap A' hittingSigma ≤ aeSigma 𝒢 P) :
    MeasurableSpace.comap A hittingSigma ≤ aeSigma 𝒢 P := by
  rintro _ ⟨S, hS, rfl⟩
  obtain ⟨G', hG', hae⟩ := h _ ⟨S, hS, rfl⟩
  refine ⟨G', hG', EventuallyEq.trans ?_ hae⟩
  filter_upwards [hAA'] with ω hω
  show (A ω ∈ S) = (A' ω ∈ S)
  rw [hω]

/-- **The single-path side heights** (proof of Aux. lemma 70, p. 275), from Lemma 7.5 and Aux. lemma 56 at first
entrances. -/
theorem singlePathSideHeightStatement_of_inputs (hL75 : Theorem15.Lemma75Statement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) : SinglePathSideHeightStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ Ω _ P _ h hh η ζ hη W htr u₀ hu₀ m q hqm ηc hηcc hηcm hηce g hg
  classical
  obtain ⟨h', 𝓕, W', VL, VR, B, htrans, hC, htr'⟩ := id hη
  obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps x θ)
    (flowLineRhoR κ b jumps x θ) (flowLineXL b jumps x) (flowLineXR b jumps x)
  have hrel := Exist.eqOn_flowLine_harmonicExtension hκ hb x θ hu₀ hu₀'
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hX, -⟩ := hC.2.2.2
  -- good versions of the capped flow line (Lemma 6.2 inputs), from the pair construction with the line twice
  obtain ⟨ηs, hc, h0, hηm, hdet, hloc, hfr, -, hs₁, -⟩ :=
    exists_twoHist_versions hL75 hA56 hκ hκ4 hb hh hη hη hu₀ m
  set s₂ : Fin 2 → ℝ≥0∞ := ![(q : ℝ≥0∞), 0] with hs₂
  have hA₁'loc := isLocalSet_explored_const hh0 hc h0 hηm hdet hloc hfr s₂
  have hA₁'det := comap_explored_const_le_aeSigma hc hdet s₂
  have hA₁'eq : ∀ ω, explored ηs (fun i _ => s₂ i) ω = ηs 0 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H := fun ω =>
    explored_pair_left ηs q (by rw [h0 1 ω]; simp)
  -- the range of the given version
  set A₁ : Ω → Set ℂ := fun ω => ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H with hA₁_def
  have hA₁A₁' : A₁ =ᵐ[P] explored ηs fun i _ => s₂ i := by
    filter_upwards [hηce, hs₁] with ω h1 h2
    rw [hA₁'eq]
    have : ηc ω = ηs 0 ω := funext fun t => (h1 t).trans (h2 t).symm
    show ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = _
    rw [this]
  have hA₁loc := Coupling.IsLocalSet.congr_set hA₁'loc hA₁A₁'
  have hA₁det := comap_le_aeSigma_of_ae_eq hA₁A₁' hA₁'det
  have hA₁m : Measurable[_, hittingSigma] A₁ := by
    have h1 := measurable_explored_const (η := fun _ : Fin 1 => ηc) (fun _ => hηcc) (fun _ => hηcm)
      (fun _ => (q : ℝ≥0∞))
    have e : (explored (fun _ : Fin 1 => ηc) fun _ _ => (q : ℝ≥0∞)) = A₁ := by
      funext ω
      simp only [explored, iUnion_const, hA₁_def]
    rwa [e] at h1
  have hA₁b : ∀ ω, Bornology.IsBounded (A₁ ω) := fun ω =>
    (((isCompact_Icc (a := (0 : ℝ≥0)) (b := q)).image (hηcc ω)).isBounded).subset (inter_subset_left.trans (by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨t, ⟨zero_le, show t ≤ q from by exact_mod_cast ht⟩, rfl⟩))
  -- the range is the stopped range of the flow line on `{q < ζ}`
  have hA₁q : ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → A₁ ω = η ω '' Icc 0 q ∩ H := by
    filter_upwards [hηce] with ω hce hq
    show ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = η ω '' Icc 0 q ∩ H
    congr 1
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      have htq : t ≤ q := by exact_mod_cast ht
      refine ⟨t, ⟨zero_le, htq⟩, ?_⟩
      rw [hce t, Restart.capTime_of_le m (ζ ω) (le_min (ht.trans hq.le) (ENNReal.coe_le_coe.2 (htq.trans hqm)))]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, by exact_mod_cast ht.2, ?_⟩
      rw [hce t, Restart.capTime_of_le m (ζ ω)
        (le_min ((ENNReal.coe_le_coe.2 ht.2).trans hq.le) (ENNReal.coe_le_coe.2 (ht.2.trans hqm)))]
  -- every earlier hull lies in the filling of the range
  have hA₁fill : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ q → (t : ℝ≥0∞) < ζ ω →
      (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t ⊆ fillH (A₁ ω) := by
    filter_upwards [htr', hηce] with ω htrω hce t htq htζ
    rw [fwdHull_eq_fillH_of_isGeneratingTrace htrω htζ, ← Restart.fillH_image_add_real,
      Restart.image_add_real_eq, hA₁_def, fillH_inter_H]
    refine fillH_mono ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s, show (s : ℝ≥0∞) ≤ q from ENNReal.coe_le_coe.2 (hs.2.trans htq), ?_⟩
    rw [hce s, Restart.capTime_of_le m (ζ ω)
      (le_min ((ENNReal.coe_le_coe.2 hs.2).trans htζ.le) (ENNReal.coe_le_coe.2 ((hs.2.trans htq).trans hqm)))]
  -- the force data at `q`
  choose u hu using fun ω => Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps x θ)
    (flowLineRhoR κ b jumps x θ) (fun i => VL i q ω - W' q ω) (fun i => VR i q ω - W' q ω)
  have hmain := ae_apply_eq_flowMean_of_range hC hκ htrans hh0 hu₀.1 hu₀' hrel hX htr' hA₁m
    (fun ω => inter_subset_right) hA₁b hA₁loc hA₁det hA₁q hA₁fill hg hu
  filter_upwards [hmain, htr, htr', hC.1.2.2.2.2, hA₁q, hA₁fill] with ω hmω htrω htr'ω hp h1 hfill hq v hv hrep
    t₀ ht₀ hη₀ F hFne hFle y hy
  have := hFne
  set χ := QuantumZipper.chiC κ with hχ
  -- the unbounded part and the identification of `v`
  set U := H \ fillH (A₁ ω) with hU
  have hUo : IsOpen U := isOpen_H_diff_fillH (hA₁b ω)
  have hUA : U ⊆ H \ A₁ ω := fun z hz => ⟨hz.1, fun h => hz.2 (subset_fillH inter_subset_right h)⟩
  set M : ℂ → ℝ := fun z => couplingMean κ (fun s : ℝ => W' s.toNNReal ω) q (u ω) (z - x) - θ * χ - u₀ z with hM
  have hKU : U ⊆ H \ (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) q := fun z hz =>
    ⟨hz.1, fun h => hz.2 (hfill q le_rfl hq h)⟩
  have hMh : InnerProductSpace.HarmonicOnNhd M U :=
    (harmonicOnNhd_flowMean hp.2.2.2.1 hq (hu ω).1 x (θ * χ) hu₀.1).mono hKU
  have hvM : EqOn v M U := eqOn_of_integral_mul_eq hUo (hUA.trans sdiff_subset) (hv.mono hUA) hMh
    fun φ hφ => by rw [← hrep φ (hφ.trans hUA), hmω hq φ hφ]
  have hfillη : fillH (η ω '' Icc 0 q) = fillH (A₁ ω) := by rw [h1 hq, fillH_inter_H]
  have hev : ∀ᶠ z in F, z ∈ U := by
    have := hFle self_mem_nhdsWithin
    rwa [hfillη] at this
  -- the coupling's driver generates the same trace
  have hf := fwdMap_eq_of_isGeneratingTrace htrω htr'ω hq
  have hL := logDerivFwd_eq_of_isGeneratingTrace htrω htr'ω hq
  -- the approach in the centred chart
  set F' : Filter ℂ := Filter.map (fun z => z - x) F with hF'
  have hp0 : η ω t₀ - x ∈ H := show 0 < (η ω t₀ - x).im by simpa using (show 0 < (η ω t₀).im from hη₀)
  have hF'le : F' ≤ 𝓝[H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) q] (η ω t₀ - x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((continuous_sub_right (x : ℂ)).tendsto _).comp
      (hFle.trans nhdsWithin_le_nhds), hev.mono fun z hz => ?_⟩
    have hz' := hKU hz
    refine ⟨show 0 < (z - x).im by simpa using (show 0 < z.im from hz'.1), fun hK => hz'.2 ⟨z - x, hK, by ring⟩⟩
  have hy' : Tendsto (fwdMap (fun s : ℝ => W' s.toNNReal ω) q) F' (𝓝 (y : ℂ)) := by
    rw [← hf]
    exact tendsto_map'_iff.2 hy
  -- the function along `F`
  have hcongr : (fun z => v z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im)
      =ᶠ[F] fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x)) - θ * χ := by
    filter_upwards [hev] with z hz
    rw [hvM hz, hM, hL]
    simp only [couplingMean]
    ring
  refine ⟨fun hy0 => ?_, fun hy0 => ?_⟩
  · have hlim := tendsto_comp_fwdMap_of_pos hp htr'ω hq (hu ω) hp0 hF'le hy' hy0
    have hlim' : Tendsto (fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x))) F (𝓝 (sleLambda κ)) :=
      tendsto_map'_iff.1 hlim
    exact (hlim'.sub_const (θ * χ)).congr' hcongr.symm
  · have hlim := tendsto_comp_fwdMap_of_neg hp htr'ω hq (hu ω) hp0 hF'le hy' hy0
    have hlim' : Tendsto (fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x))) F
        (𝓝 (-sleLambda κ)) :=
      tendsto_map'_iff.1 hlim
    exact (hlim'.sub_const (θ * χ)).congr' hcongr.symm

end SideHeight

/-- **Aux. lemma 70 from Lemma 7.5, Aux. lemma 56 and the deterministic reverse-arc chart geometry** (the named input
`SinglePathSideHeightStatement` of `aux70Statement_of_inputs` is now proved). -/
theorem aux70Statement_of_inputs' (hL75 : Theorem15.Lemma75Statement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) (hgeom : ReverseArcChartStatement) : Aux70Statement.{u} :=
  aux70Statement_of_inputs hL75 hA56 (SideHeight.singlePathSideHeightStatement_of_inputs hL75 hA56) hgeom

theorem lemma77Statement_of_lemma76_of_inputs' (h76 : Lemma76Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u}) (hA56 : Restart.RetainedRangeEntranceStatement.{u})
    (hgeom : ReverseArcChartStatement) : Supp10.Lemma77Statement.{u} :=
  lemma77Statement_of_lemma76_of_inputs h76 hL75 hA56 (SideHeight.singlePathSideHeightStatement_of_inputs hL75 hA56)
    hgeom

theorem w8FirstContactStatement_of_lemma76_of_inputs' (h76 : Lemma76Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u}) (hA56 : Restart.RetainedRangeEntranceStatement.{u})
    (hgeom : ReverseArcChartStatement) : Theorem15.W8FirstContactStatement.{u} :=
  w8FirstContactStatement_of_lemma76_of_inputs h76 hL75 hA56
    (SideHeight.singlePathSideHeightStatement_of_inputs hL75 hA56) hgeom

end Sec7

end InteractingSLE
