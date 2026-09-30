import QuantumZipper.Proofs.Section5.Prop16LitIdTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: a Borel event forcing the chart identity (COORD-CHANGE, D98)

`IdGood`: for every cutoff test function `F = χ_{U,n} g` of the chart domain `U_x`
(`g` in the countable dense family `ExA.famF`), the approximations of the chart zoom `Z` against
`F` and those of the straight zoom `Y` against the pulled-back function `F ∘ ψ_x⁻¹` (`pullT`)
converge to a common limit. On readings (rebuilt fields) this is a Borel event
(`measurableSet_litIdSet`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA Prop16Asm

variable {D : Set ℂ} {a b : ℝ} {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}

/-- The cutoff test functions of the chart domains. -/
def FnT (r₀ : ℝ → ℝ) (g : ℂ → ℝ) (n : ℕ) (x : ℝ) (z : ℂ) : ℝ := hbCut (r₀ x) n z * g z

theorem measurable_FnT (hr : Measurable r₀) {g : ℂ → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable fun q : ℝ × ℂ => FnT r₀ g n q.1 q.2 := by
  unfold FnT hbCut
  have h1 : Measurable fun q : ℝ × ℂ => r₀ q.1 := hr.comp measurable_fst
  exact (measurable_const.min (measurable_const.max ((measurable_const.mul
    ((h1.sub (measurable_snd.norm)).min (Complex.measurable_im.comp measurable_snd))).sub
    measurable_const))).mul (hg.comp measurable_snd)

theorem FnT_test {g : ℂ → ℝ} (hg : g ∈ famF) (n : ℕ) (x : ℝ) :
    Continuous (FnT r₀ g n x) ∧ HasCompactSupport (FnT r₀ g n x) ∧
      tsupport (FnT r₀ g n x) ⊆ ball 0 (r₀ x) ∩ H := by
  obtain ⟨hgc, hgs, -⟩ := famF_dense.1 g hg
  exact ⟨(continuous_hbCut _ n).mul hgc, hgs.mul_left,
    (tsupport_mul_subset_left).trans (tsupport_hbCut _ n)⟩

/-- **The countable identity condition** for a chart zoom `Z` and a straight zoom `Y` at `x`. -/
def IdGood (ψ : ℝ → ℂ → ℂ) (a b : ℝ) (r₀ : ℝ → ℝ) (γ : ℝ) (Z Y : FieldSample) (x : ℝ) : Prop :=
  ∀ n : ℕ, ∀ g ∈ famF, ∃ l, Tendsto (fun k => ∫ z, FnT r₀ g n x z ∂areaApprox γ Z k) atTop (𝓝 l) ∧
    Tendsto (fun k => ∫ w, pullT ψ a b r₀ (FnT r₀ g n) x w ∂areaApprox γ Y k) atTop (𝓝 l)

/-- The rebuilt straight zoom as a measurable family. -/
def litYr (D : Set ℂ) (a b γ C : ℝ) (q : (ℕ → ℝ) × ℝ) : FieldSample :=
  Factorization.reconstruct (Factorization.coords (zoomField γ C (repFam D a b 0 q.1) q.2))

theorem measurable_litYr (D : Set ℂ) (a b γ C : ℝ) : Measurable (litYr D a b γ C) :=
  Factorization.measurable_reconstruct.comp (measurable_coords_zoomField_rep D a b γ C)

theorem areaApprox_litYr (D : Set ℂ) (a b γ C : ℝ) (q : (ℕ → ℝ) × ℝ) :
    areaApprox γ (litYr D a b γ C q) = areaApprox γ (zoomField γ C (repFam D a b 0 q.1) q.2) :=
  Prop16Area.areaApprox_recon γ _

/-- The Borel event on the readings. -/
def litIdSet (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) : Set ((ℕ → ℝ) × ℝ) :=
  {q | q.2 ∈ Ioo a b} ∩ {q | IdGood ψ a b r₀ γ (litZr hfam γ C q) (litYr D a b γ C q) q.2}

theorem mem_litIdSet_iff (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) {q : (ℕ → ℝ) × ℝ}
    (hq : q.2 ∈ Ioo a b) : q ∈ litIdSet hfam γ C ↔
      IdGood ψ a b r₀ γ (zoomFieldLit γ C (repFam D a b 0 q.1) q.2 (ψ q.2))
        (zoomField γ C (repFam D a b 0 q.1) q.2) q.2 := by
  have e1 := areaApprox_litZr hfam γ C hq
  have e2 := areaApprox_litYr D a b γ C q
  constructor
  · rintro ⟨-, h⟩
    have h' : IdGood ψ a b r₀ γ (litZr hfam γ C q) (litYr D a b γ C q) q.2 := h
    unfold IdGood at h' ⊢
    rwa [e1, e2] at h'
  · intro h
    refine ⟨hq, ?_⟩
    show IdGood ψ a b r₀ γ (litZr hfam γ C q) (litYr D a b γ C q) q.2
    unfold IdGood at h ⊢
    rwa [e1, e2]

theorem measurableSet_common_limit {α : Type*} [MeasurableSpace α] {f g : ℕ → α → ℝ}
    (hf : ∀ k, Measurable (f k)) (hg : ∀ k, Measurable (g k)) :
    MeasurableSet {q | ∃ l, Tendsto (fun k => f k q) atTop (𝓝 l) ∧
      Tendsto (fun k => g k q) atTop (𝓝 l)} := by
  have e : {q | ∃ l, Tendsto (fun k => f k q) atTop (𝓝 l) ∧ Tendsto (fun k => g k q) atTop (𝓝 l)} =
      {q | ∃ l, Tendsto (fun k => f k q) atTop (𝓝 l)} ∩
        ({q | ∃ l, Tendsto (fun k => g k q) atTop (𝓝 l)} ∩
          {q | limUnder atTop (fun k => f k q) = limUnder atTop (fun k => g k q)}) := by
    ext q
    simp only [mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨l, h1, h2⟩
      exact ⟨⟨l, h1⟩, ⟨l, h2⟩, h1.limUnder_eq.trans h2.limUnder_eq.symm⟩
    · rintro ⟨⟨l, h1⟩, ⟨l', h2⟩, h3⟩
      refine ⟨l, h1, ?_⟩
      rw [← h1.limUnder_eq, h3, h2.limUnder_eq]
      exact h2
  rw [e]
  have hfs : ∀ k, StronglyMeasurable (f k) := fun k => (hf k).stronglyMeasurable
  have hgs : ∀ k, StronglyMeasurable (g k) := fun k => (hg k).stronglyMeasurable
  exact (StronglyMeasurable.measurableSet_exists_tendsto hfs).inter
    ((StronglyMeasurable.measurableSet_exists_tendsto hgs).inter
      (measurableSet_eq_fun (StronglyMeasurable.limUnder hfs).measurable
        (StronglyMeasurable.limUnder hgs).measurable))

/-- Measurability of test integrals against the approximations of a measurable family. -/
theorem measurable_integral_areaApprox_fam {α : Type*} [MeasurableSpace α] {Z : α → FieldSample}
    (hZ : Measurable Z) (γ : ℝ) (k : ℕ) {T : α → ℂ → ℝ}
    (hT : Measurable fun p : α × ℂ => T p.1 p.2) :
    Measurable fun q => ∫ z, T q z ∂areaApprox γ (Z q) k := by
  have e : ∀ q, ∫ z, T q z ∂areaApprox γ (Z q) k =
      ∫ z, E6.areaDensK γ (Z q) k z * T q z ∂(volume.restrict H) :=
    fun q => E6.integral_areaApprox_eq γ (Z q) k _
  simp_rw [e]
  exact (StronglyMeasurable.integral_prod_right' (f := fun p : α × ℂ =>
    E6.areaDensK γ (Z p.1) k p.2 * T p.1 p.2)
    ((measurable_dens hZ γ k).mul hT).stronglyMeasurable).measurable

theorem measurableSet_litIdSet (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) :
    MeasurableSet (litIdSet hfam γ C) := by
  refine (measurableSet_Ioo.preimage measurable_snd).inter ?_
  have e : {q : (ℕ → ℝ) × ℝ | IdGood ψ a b r₀ γ (litZr hfam γ C q) (litYr D a b γ C q) q.2} =
      ⋂ n : ℕ, ⋂ g ∈ famF, {q | ∃ l,
        Tendsto (fun k => ∫ z, FnT r₀ g n q.2 z ∂areaApprox γ (litZr hfam γ C q) k) atTop (𝓝 l) ∧
        Tendsto (fun k => ∫ w, pullT ψ a b r₀ (FnT r₀ g n) q.2 w
          ∂areaApprox γ (litYr D a b γ C q) k) atTop (𝓝 l)} := by
    ext q; simp only [IdGood, mem_setOf_eq, mem_iInter]
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.biInter famF_countable fun g hg => ?_
  have hgm : Measurable g := (famF_dense.1 g hg).1.measurable
  have hF := measurable_FnT hfam.2.1 hgm n
  refine measurableSet_common_limit (fun k => ?_) (fun k => ?_)
  · exact measurable_integral_areaApprox_fam (measurable_litZr hfam γ C) γ k
      (T := fun q z => FnT r₀ g n q.2 z)
      (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  · exact measurable_integral_areaApprox_fam (measurable_litYr D a b γ C) γ k
      (T := fun q w => pullT ψ a b r₀ (FnT r₀ g n) q.2 w)
      ((measurable_pullT hfam hF).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

end Prop16Lit
end QuantumZipper
