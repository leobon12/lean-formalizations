import InteractingSLE.Spec.Sec4.Special3Uniqueness
import InteractingSLE.Spec.Sec4.SpecialSimple
import InteractingSLE.Spec.Sobolev.GFFRegularity
import InteractingSLE.Impl.ForceBoundaryData
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling

/-!
# Aux. lemma 23: the coupling field and the thin hull (§4.2)

Packet PROVE-SEC4-B3. Two steps of the proof of Aux. lemma 23 (`source/spec/p097-144.md` L608–L615, pp. 122–123)
for the actual couplings of Theorem 1.1:

* "The marginal GFF is locally square-integrable with values in `H^{-ε}` by Aux. lemma 11"
  (`IsOptionalHullCoupling.lintegral_negSobolevSq_lt_top`): the field `h = h⁰ + 𝔥₀` of every coupling with the
  optional hull specification satisfies (SR1);
* "`K_S ∩ ℍ = η([0, S]) ∩ ℍ` … The bound and a countable compact exhaustion give `dim_H(K_S ∩ L) < 2 − 2ε` for every
  compact `L ⊂ ℍ`" (`dimH_fwdHull_inter_lt`, `closure_fwdHull_inter_H_subset`): for a thin simple hull, the
  hypotheses (SR3) and relative closedness of `A = K_S` used by `map_prod_eq_of_condCharFun_off`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace InteractingSLE.Sec4

open LQGMetric TopologicalSpace InteractingSLE.Sobolev QuantumZipper

/-! ### (SR1) for the field of a Theorem 1.1 coupling -/

/-- Existence of the bounded harmonic extension of force boundary data at arbitrary positions: the landed
`Impl` theorem, read through the definitional bridge of the frozen companion's quarantined provider (the force word
with the given weights and all positions `0`; the boundary data read only the weights). -/
theorem exists_isBoundedHarmonicExtension_forceBoundaryData (κ : ℝ) {nL nR : ℕ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR)
      (forceJumpSet vL vR) u := by
  let F : Impl.ForceWord :=
    { nL := nL, nR := nR, xL := fun _ => 0, xR := fun _ => 0, ρL := ρL, ρR := ρR,
      antitone_xL := fun _ _ _ => le_rfl, xL_nonpos := fun _ => le_rfl,
      monotone_xR := fun _ _ _ => le_rfl, xR_nonneg := fun _ => le_rfl }
  obtain ⟨u, hu, -⟩ := Impl.existsUnique_isBoundedHarmonicExtension_forceBoundaryData κ F vL vR
  exact ⟨u, hu⟩

/-- **(SR1) for the coupling field** (proof of Aux. lemma 23: "The marginal GFF is locally square-integrable with
values in `H^{-ε}` by Aux. lemma 11"). In every coupling with the optional hull specification of Theorem 1.1, the
field `h = h⁰ + 𝔥₀` satisfies `E ‖ζ h‖²_{H^{-ε}} < ∞` for every test function `ζ` and every `ε > 0`. -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.lintegral_negSobolevSq_lt_top {κ : ℝ}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) {ε : ℝ} (hε : 0 < ε)
    (ζc : TestOn upperHalfPlaneOpens) :
    ∫⁻ o, negSobolevSq ε (h o) ζc ∂P < ⊤ := by
  obtain ⟨-, hhm, hgff, -⟩ := hcoup
  obtain ⟨u₀, hu₀⟩ := exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  have hproc := hgff u₀ hu₀
  set m := Distribution.ofFun upperHalfPlaneOpens u₀ volume ⊤ with hmdef
  have hharm : InnerProductSpace.HarmonicOnNhd u₀ (upperHalfPlaneOpens : Set ℂ) := hu₀.1
  have hcont : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := fun x hx =>
    (HarmonicAt.analyticAt (hharm x hx)).continuousAt.continuousWithinAt
  have hloc : LocallyIntegrableOn u₀ (upperHalfPlaneOpens : Set ℂ) volume :=
    hcont.locallyIntegrableOn upperHalfPlaneOpens.isOpen.measurableSet
  have hm : ∀ φ : TestOn upperHalfPlaneOpens, m φ = ∫ z, u₀ z * φ z := fun φ => by
    rw [hmdef, Distribution.ofFun_apply hloc]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul]
    ring
  have h0 : IsZeroBoundaryGFF upperHalfPlaneOpens (fun o => h o - m) P := by
    refine ⟨LQGMetric.measurable_distOn_iff.2 fun φ => ?_, ?_⟩
    · simp only [sub_apply]
      exact ((LQGMetric.measurable_distOn_apply φ).comp hhm).sub_const _
    · convert hproc using 2 with φ
      funext o
      rw [sub_apply, hm]
  have hsr := aux11_sr1 (zbAdmissible_of_subset_H (U := upperHalfPlaneOpens) subset_rfl) h0 hharm
    hε ζc
  rw [← hmdef] at hsr
  simpa only [sub_add_cancel] using hsr

/-! ### The thin hull: (SR3) and relative closedness -/

section Thin

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- A hull lies in `ℍ`. -/
theorem fwdHull_subset_H' (W : ℝ → ℝ) (t : ℝ) : QuantumZipper.fwdHull W t ⊆ H := fun _ hz => hz.1

/-- **(SR3) for a thin simple hull** (proof of Aux. lemma 23). If `η` is a continuous generating trace of `w`
before `T`, simple on `[0, S]` (`S < T`) with `η((0, S]) ⊂ ℍ`, and `dim_H(η([0, S]) ∩ ℍ) ≤ d < 2 − 2ε` (the strict
interior dimension bound of Aux. lemma 15), then `dim_H(K_S ∩ K) < 2 − 2ε` for every set `K`. -/
theorem dimH_fwdHull_inter_lt (hη : IsGeneratingTrace w T η) {S : ℝ≥0} (hS : (S : ℝ≥0∞) < T)
    (hinj : InjOn η (Icc 0 S)) (hH : ∀ t ∈ Ioc 0 S, η t ∈ H) {d ε : ℝ}
    (hdim : dimH (η '' Icc 0 S ∩ H) ≤ ENNReal.ofReal d) (hd : d < 2 - 2 * ε) (hε1 : ε < 1)
    (K : Set ℂ) :
    dimH (QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) S ∩ K) <
      ENNReal.ofReal (2 - 2 * ε) := by
  have hsub : QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) S ∩ K ⊆ η '' Icc 0 S ∩ H := by
    rw [← fwdHull_inter_H_eq_image_inter_H hη hS hinj hH]
    exact fun z hz => ⟨hz.1, fwdHull_subset_H' _ _ hz.1⟩
  calc dimH (QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) S ∩ K)
      ≤ dimH (η '' Icc 0 S ∩ H) := dimH_mono hsub
    _ ≤ ENNReal.ofReal d := hdim
    _ < ENNReal.ofReal (2 - 2 * ε) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hd

/-- **The thin hull is relatively closed in `ℍ`** (`closure A ∩ ℍ ⊆ A` for `A = K_S`): `K_S ∩ ℍ = η([0, S]) ∩ ℍ`
with `η([0, S])` compact. -/
theorem closure_fwdHull_inter_H_subset (hη : IsGeneratingTrace w T η) {S : ℝ≥0}
    (hS : (S : ℝ≥0∞) < T) (hinj : InjOn η (Icc 0 S)) (hH : ∀ t ∈ Ioc 0 S, η t ∈ H) :
    closure (QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) S) ∩
        (upperHalfPlaneOpens : Set ℂ) ⊆ QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) S := by
  have heq := fwdHull_inter_H_eq_image_inter_H hη hS hinj hH
  have hK : QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) S ⊆ η '' Icc 0 S := fun z hz => by
    have : z ∈ QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) S ∩ H :=
      ⟨hz, fwdHull_subset_H' _ _ hz⟩
    rw [heq] at this
    exact this.1
  have hcl : IsClosed (η '' Icc 0 S) :=
    (isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun r hr =>
      (ENNReal.coe_le_coe.2 hr.2).trans hS.le)).isClosed
  intro z ⟨hz, hzH⟩
  have hzη : z ∈ η '' Icc 0 S := closure_minimal hK hcl hz
  have : z ∈ QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) S ∩ H := by
    rw [heq]; exact ⟨hzη, hzH⟩
  exact this.1

end Thin

end InteractingSLE.Sec4
