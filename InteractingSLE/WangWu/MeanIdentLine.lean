/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.MeanIdentChamber

/-!
# The side values of a complete seed line from those of its prefixes (proof of Proposition 4.19)

Packet PROVE-WW-B5. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), proof of
Proposition 4.19 (p. 28, text dump L1660–1668):

> The complete curve `β` is local by the terminal Gaussian-kernel limit. On a compact subarc of `β`, compare with a
> sufficiently long finite prefix; properness and simplicity separate that subarc from the remaining future.
> Local-set boundary compatibility therefore gives the boundary value `+λ` from `R`. … Bounded harmonic uniqueness
> identifies the single-line component mean. This uses no ordered-union assertion.

This is the single-line identification consumed by Lemma 4.21 (`HasLeftSideLimit`) and Proposition 4.20
(`HasLeftSideLimit`, `HasRightSideLimit`).

## Main results

* `exists_rep_tendsto_side_of_prefix` (deterministic core): if every prefix `γ([0, n])` has a mean whose
  representative tends to `ℓ(γ s)` from a fixed side `Side ⊆ ℍ \ γ` at the points `γ s`, `0 < s < n`, and the complete
  mean satisfies Proposition 3.8's conclusion against every prefix, then the complete mean has a representative with
  these limits at every point `γ s`, `s > 0`.
* `ae_hasLeftSideLimit_of_prefix`, `ae_hasRightSideLimit_of_prefix`: the probabilistic statements for a random proper
  arc whose range and prefixes are field-determined local sets. The prefix values themselves are the boundary values of
  the explicit stopped mean (`frozenMean`) on the two sides of the slit (Definition 1.4: `−λ` and `+λ` for the zero
  level line), not proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv IsZeroBoundaryGFF AEDeterminedSigma)
open InteractingSLE.LocalSets

universe u

namespace InteractingSLE.WangWu

/-- The prefix `γ([0, t])` of a curve. -/
def arcPrefix (γ : ℝ → ℂ) (t : ℝ) : Set ℂ := γ '' Icc 0 t

theorem arcPrefix_subset (γ : ℝ → ℂ) (t : ℝ) : arcPrefix γ t ⊆ arcRange γ :=
  image_mono fun _ hs => mem_Ici.2 hs.1

theorem IsProperArc.isPreconnected_prefix_union_real {γ : ℝ → ℂ} (hγ : IsProperArc γ) {t : ℝ}
    (ht : 0 ≤ t) : IsPreconnected (arcPrefix γ t ∪ {w : ℂ | w.im = 0}) := by
  have hreal : {w : ℂ | w.im = 0} = range (fun x : ℝ => (x : ℂ)) := by
    ext w
    constructor
    · intro hw
      exact ⟨w.re, Complex.ext (by simp) (by simpa using hw.symm)⟩
    · rintro ⟨x, rfl⟩
      simp
  refine IsPreconnected.union 0 ⟨0, left_mem_Icc.2 ht, hγ.zero⟩ (by simp)
    (isPreconnected_Icc.image γ (hγ.cont.mono fun s hs => mem_Ici.2 hs.1)) ?_
  rw [hreal]
  exact isPreconnected_range Complex.continuous_ofReal

/-- **Deterministic core.** Let `Side ⊆ ℍ \ γ`. If for every `n ≥ 1` the prefix mean `g n` is represented on
`ℍ \ γ([0, n])` by a harmonic function tending to `ℓ(γ s)` from `Side` at `γ s` (`0 < s < n`), and the complete mean
`g` satisfies the conclusion of Proposition 3.8 against every prefix, then `g` is represented on `ℍ \ γ` by a harmonic
function tending to `ℓ(γ s)` from `Side` at every `γ s`, `s > 0`. -/
theorem exists_rep_tendsto_side_of_prefix {γ : ℝ → ℂ} (hγ : IsProperArc γ) {Side : Set ℂ}
    (hSide : Side ⊆ H \ arcRange γ) {g : DistOn upperHalfPlaneOpens} {gp : ℕ → DistOn upperHalfPlaneOpens}
    {ℓ : ℂ → ℝ}
    (hp : ∀ n : ℕ, ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ arcPrefix γ (n + 1)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix γ (n + 1) → gp n φ = ∫ z, v z * φ z) ∧
      ∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 → Tendsto v (𝓝[Side] (γ s)) (𝓝 (ℓ (γ s))))
    (hu : ∀ n : ℕ, IsUnionBoundaryLimit (arcRange γ) (arcPrefix γ (n + 1)) g (gp n)) :
    ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ arcRange γ) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcRange γ → g φ = ∫ z, w z * φ z) ∧
      ∀ s > 0, Tendsto w (𝓝[Side] (γ s)) (𝓝 (ℓ (γ s))) := by
  set O : Set ℂ := H \ arcRange γ with hOdef
  have hO : IsOpen O := QuantumZipper.isOpen_H.sdiff hγ.isClosed_arcRange
  have hU : ∀ n : ℕ, H \ (arcRange γ ∪ arcPrefix γ (n + 1)) = O := fun n => by
    rw [union_eq_left.2 (arcPrefix_subset γ _)]
  have hOp : ∀ n : ℕ, O ⊆ H \ arcPrefix γ (n + 1) := fun n =>
    sdiff_subset_sdiff_right (arcPrefix_subset γ _)
  have hcont : ∀ {v : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd v O → ContinuousOn v O :=
    fun hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  -- the representative attached to each prefix
  have hrep : ∀ n : ℕ, ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w O ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O → g φ = ∫ z, w z * φ z) ∧
      ∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 → Tendsto w (𝓝[Side] (γ s)) (𝓝 (ℓ (γ s))) := by
    intro n
    obtain ⟨v, hv, hvg, hvlim⟩ := hp n
    obtain ⟨u, hu', hug, hulim⟩ := hu n
    rw [hU n] at hu' hug hulim
    have hvO : InnerProductSpace.HarmonicOnNhd v O := fun z hz => hv z (hOp n hz)
    refine ⟨u + v, hu'.add hvO, fun φ hφ => ?_, fun s hs hsn => ?_⟩
    · simp only [Pi.add_apply, add_mul]
      rw [integral_add (integrable_mul_test hO (hcont hu') φ hφ)
        (integrable_mul_test hO (hcont hvO) φ hφ), ← hug φ hφ, ← hvg φ (hφ.trans (hOp n))]
      ring
    · obtain ⟨r, hr, hball⟩ := hγ.exists_ball_inter_subset le_rfl (show s ∈ Ioo 0 ((n : ℝ) + 1) from ⟨hs, hsn⟩)
      have l₁ : Tendsto u (𝓝[Side] (γ s)) (𝓝 0) :=
        (hulim (γ s) (Or.inl ⟨s, ⟨hs.le, hsn.le⟩, rfl⟩)
          ⟨r, hr, hball.trans (image_mono Ioo_subset_Icc_self)⟩).mono_left (nhdsWithin_mono _ hSide)
      have := l₁.add (hvlim s hs hsn)
      rw [zero_add] at this
      exact this
  choose w hw hwg hwlim using hrep
  refine ⟨w 0, hw 0, hwg 0, fun s hs => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt s
  have heq := Sec6.eqOn_of_integral_mul_eq hO (fun z hz => hz.1) (hw 0) (hw n)
    fun φ hφ => (hwg 0 φ hφ).symm.trans (hwg n φ hφ)
  refine (hwlim n s hs (by linarith)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (heq (hSide hz)).symm

section Probabilistic

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- Proposition 3.8 against every prefix, for a random proper arc whose range and prefixes are field-determined local
sets: almost surely, for every `n`, the complete mean minus the prefix mean tends to `0` at the points of the prefix
near which the complete arc lies in the prefix. -/
theorem ae_isUnionBoundaryLimit_prefix (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {γ : Ω → ℝ → ℂ}
    (harc : ∀ᵐ ω ∂P, IsProperArc (γ ω))
    (hm : Measurable[mΩ, hittingSigma] fun ω => arcRange (γ ω))
    (hdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hloc : IsLocalSet (fun ω => arcRange (γ ω)) h P)
    (hpm : ∀ n : ℕ, Measurable[mΩ, hittingSigma] fun ω => arcPrefix (γ ω) (n + 1))
    (hploc : ∀ n : ℕ, IsLocalSet (fun ω => arcPrefix (γ ω) (n + 1)) h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) h P g)
    {gp : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgp : ∀ n : ℕ, IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1)) h P (gp n)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, IsUnionBoundaryLimit (arcRange (γ ω)) (arcPrefix (γ ω) (n + 1)) (g ω) (gp n ω) := by
  refine ae_all_iff.2 fun n => ?_
  have hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcPrefix (γ ω) (n + 1)) hittingSigma) P :=
    Sec6.condIndepEv_of_le_aeSigma hh.measurable.comap_le (hpm n).comap_le fun s hs => hdet s hs
  have e : (fun ω => arcRange (γ ω) ∪ arcPrefix (γ ω) (n + 1)) = fun ω => arcRange (γ ω) := by
    funext ω; exact union_eq_left.2 (arcPrefix_subset _ _)
  have hg' : IsLocalSetMean (fun ω => arcRange (γ ω) ∪ arcPrefix (γ ω) (n + 1)) h P g := e ▸ hg
  have hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (arcPrefix (γ ω) (n + 1)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (arcPrefix (γ ω) (n + 1))) z) := by
    filter_upwards [harc] with ω hω
    exact not_isBounded_of_isPreconnected_union_real (hω.isPreconnected_prefix_union_real (by positivity))
  exact LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh hm (hpm n) hci hloc (hploc n) hunb hg' (hgp n)

/-- **The left-side values of a complete seed line from those of its prefixes.** For a random proper arc `γ` whose
range and prefixes `γ([0, n + 1])` are field-determined local sets, if almost surely every prefix mean has left-side
values `ℓ` at the points `γ s`, `0 < s < n + 1` (approached from the left side of the complete arc), then the complete
mean has left-side values `ℓ` at every point `γ s`, `s > 0` (`HasLeftSideLimit`). -/
theorem ae_hasLeftSideLimit_of_prefix (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {γ : Ω → ℝ → ℂ}
    (harc : ∀ᵐ ω ∂P, IsProperArc (γ ω))
    (hm : Measurable[mΩ, hittingSigma] fun ω => arcRange (γ ω))
    (hdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hloc : IsLocalSet (fun ω => arcRange (γ ω)) h P)
    (hpm : ∀ n : ℕ, Measurable[mΩ, hittingSigma] fun ω => arcPrefix (γ ω) (n + 1))
    (hploc : ∀ n : ℕ, IsLocalSet (fun ω => arcPrefix (γ ω) (n + 1)) h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) h P g)
    {gp : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgp : ∀ n : ℕ, IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1)) h P (gp n)) {ℓ : ℂ → ℝ}
    (hpℓ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ arcPrefix (γ ω) (n + 1)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix (γ ω) (n + 1) →
        gp n ω φ = ∫ z, v z * φ z) ∧
      ∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 →
        Tendsto v (𝓝[leftSideOf (arcRange (γ ω))] (γ ω s)) (𝓝 (ℓ (γ ω s)))) :
    ∀ᵐ ω ∂P, HasLeftSideLimit (g ω) (γ ω) ℓ := by
  filter_upwards [harc, hpℓ, ae_isUnionBoundaryLimit_prefix hh harc hm hdet hloc hpm hploc hg hgp]
    with ω hω hpω huω
  exact exists_rep_tendsto_side_of_prefix hω (fun z hz => hz.1) hpω huω

/-- **The right-side values of a complete seed line from those of its prefixes** (mirror of
`ae_hasLeftSideLimit_of_prefix`). -/
theorem ae_hasRightSideLimit_of_prefix (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {γ : Ω → ℝ → ℂ}
    (harc : ∀ᵐ ω ∂P, IsProperArc (γ ω))
    (hm : Measurable[mΩ, hittingSigma] fun ω => arcRange (γ ω))
    (hdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hloc : IsLocalSet (fun ω => arcRange (γ ω)) h P)
    (hpm : ∀ n : ℕ, Measurable[mΩ, hittingSigma] fun ω => arcPrefix (γ ω) (n + 1))
    (hploc : ∀ n : ℕ, IsLocalSet (fun ω => arcPrefix (γ ω) (n + 1)) h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) h P g)
    {gp : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgp : ∀ n : ℕ, IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1)) h P (gp n)) {ℓ : ℂ → ℝ}
    (hpℓ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ arcPrefix (γ ω) (n + 1)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix (γ ω) (n + 1) →
        gp n ω φ = ∫ z, v z * φ z) ∧
      ∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 →
        Tendsto v (𝓝[rightSideOf (arcRange (γ ω))] (γ ω s)) (𝓝 (ℓ (γ ω s)))) :
    ∀ᵐ ω ∂P, HasRightSideLimit (g ω) (γ ω) ℓ := by
  filter_upwards [harc, hpℓ, ae_isUnionBoundaryLimit_prefix hh harc hm hdet hloc hpm hploc hg hgp]
    with ω hω hpω huω
  exact exists_rep_tendsto_side_of_prefix hω (fun z hz => hz.1) hpω huω

end Probabilistic

end InteractingSLE.WangWu
