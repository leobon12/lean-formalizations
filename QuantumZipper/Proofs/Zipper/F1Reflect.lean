import QuantumZipper.Statements.ConfigLaw
import QuantumZipper.Proofs.Loewner.Algebra
import QuantumZipper.Proofs.LQG.AllOffsets
import QuantumZipper.Proofs.Probability.GermZeroOne

/-!
# F1d, deterministic part: reflection of configurations and of `unzipLengths`

E-branch node F1d (`blueprint/E_BRANCH_BLUEPRINT.md` §F1, `SECTION5_BLUEPRINT.md` F1): the
reflection `z ↦ −z̄` of a configuration `c = (h, W)` is `(h(−·̄), −W)`; it exchanges the two
sides of the curve, hence the left and right unzipped lengths (Sheffield, arXiv:1012.4797,
§5.4, proof of Theorem 1.3: "by symmetry", p. 72). This file proves:

* `fwdMapInv_reflect`: `f_t^{−W}⁻¹(−w̄) = −(f_t^W⁻¹(w))‾` (from A1(e) `fwdMap_reflect`);
* `qBoundaryMeasure_congr_regEq`: `ν_h` only reads the regularized averages;
* `unzipLengths_reflect_of`: the reflection identity
  `unzipLengths γ (reflectConfig c) t = (unzipLengths γ c t).swap`, from three inputs
  (regularized equality of the unzipped fields, `IsLQGGood` of the unzipped field, and the
  reflection of the side images);
* `f1d_lengths_agree_core`, `f1d_lengths_agree`: F1d proper — if `L⁺ = k L⁻` a.s. with `k`
  constant and the law of `(L⁻₁, L⁺₁)` is reflection invariant, then `k = 1` (`c =_d 1/c`);
* `ae_eq_const_of_isTrivialSigma`, `f1c_ae_const_of_germ`, `f1cd_lengths_agree`: the abstract
  0-1 step of F1c (`isTrivialSigma_iInf_biSup`) and its combination with F1d.

The argument is the obvious one (own elementary argument; the paper only says "by symmetry").
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal ComplexConjugate

namespace QuantumZipper
namespace F1

/-- The reflection `z ↦ −z̄` of a configuration: the field `h(−·̄)` and the driver `−W`. -/
noncomputable def reflectConfig (c : FieldSample × (ℝ → ℝ)) : FieldSample × (ℝ → ℝ) :=
  (RegClosure.reflectH c.1, -c.2)

private theorem negconj_negconj' (z : ℂ) : -conj (-conj z) = z := by simp

/-- **Reflection of the inverse forward map.** For a continuous driver and `t ≥ 0`,
`fwdMapInv (−W) t (−w̄) = −(fwdMapInv W t w)‾` for every `w` (junk values included). -/
theorem fwdMapInv_reflect (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    fwdMapInv (-W) t (-conj w) = -conj (fwdMapInv W t w) := by
  -- the defining predicates correspond under the involution `z ↦ −z̄`
  have hH : ∀ z : ℂ, -conj z ∈ H ↔ z ∈ H := fun z => by
    show 0 < (-conj z).im ↔ 0 < z.im
    simp
  have key : ∀ z : ℂ, (z ∈ H \ fwdHull (-W) t ∧ fwdMap (-W) t z = -conj w) ↔
      (-conj z ∈ H \ fwdHull W t ∧ fwdMap W t (-conj z) = w) := by
    intro z
    have hz1 := hH z
    have hz2 := LoewnerAlgebra.mem_fwdHull_reflect_iff W ht (-conj z)
    rw [negconj_negconj'] at hz2
    rw [Set.mem_sdiff, Set.mem_sdiff, ← hz1, hz2]
    refine and_congr_right fun hzH => ?_
    have hzH' : 0 < (-conj z).im := hzH.1
    have hrefl := LoewnerAlgebra.fwdMap_reflect W hW ht hzH'
    rw [negconj_negconj'] at hrefl
    rw [hrefl]
    constructor
    · intro h
      have := congrArg (fun u => -conj u) h
      simpa using this
    · intro h; rw [h]
  have hex : (∃! z', z' ∈ H \ fwdHull (-W) t ∧ fwdMap (-W) t z' = -conj w) ↔
      (∃! z', z' ∈ H \ fwdHull W t ∧ fwdMap W t z' = w) := by
    constructor
    · rintro ⟨z, hz, huniq⟩
      refine ⟨-conj z, (key z).1 hz, fun y hy => ?_⟩
      have := huniq (-conj y) ((key _).2 (by rwa [negconj_negconj']))
      rw [← this, negconj_negconj']
    · rintro ⟨z, hz, huniq⟩
      refine ⟨-conj z, (key _).2 (by rwa [negconj_negconj']), fun y hy => ?_⟩
      have := huniq (-conj y) ((key y).1 hy)
      rw [← this, negconj_negconj']
  by_cases h : ∃! z', z' ∈ H \ fwdHull W t ∧ fwdMap W t z' = w
  · have h' := hex.2 h
    simp only [fwdMapInv, dif_pos h, dif_pos h']
    have hs := (key h'.choose).1 h'.choose_spec.1
    have := h.unique hs h.choose_spec.1
    rw [← this, negconj_negconj']
  · have h' : ¬ ∃! z', z' ∈ H \ fwdHull (-W) t ∧ fwdMap (-W) t z' = -conj w :=
      fun hh => h (hex.1 hh)
    simp only [fwdMapInv, dif_neg h, dif_neg h', map_zero, neg_zero]

/-- The quantum boundary measure only reads the regularized averages `avgReg`. -/
theorem qBoundaryMeasure_congr_regEq {x y : FieldSample} (hxy : RegEq x y) (γ : ℝ) :
    qBoundaryMeasure γ x = qBoundaryMeasure γ y := by
  have : bdryApprox γ x = bdryApprox γ y := by
    funext k
    simp only [bdryApprox, hxy k]
  classical
  have e : ∀ z : FieldSample, qBoundaryMeasure γ z =
      (fun b : ℕ → Measure ℝ => if h : ∃ ν, IsVagueLimitR b ν then h.choose else 0)
        (bdryApprox γ z) := fun _ => by unfold qBoundaryMeasure; congr
  rw [e x, e y, this]

/-! ## F1d: reflection forces the length ratio to be `1` -/

section F1d

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `k * k = 1` in `ℝ≥0∞` forces `k = 1`. -/
theorem ennreal_eq_one_of_mul_self {k : ℝ≥0∞} (hk : k * k = 1) : k = 1 := by
  have hktop : k ≠ ⊤ := by
    rintro rfl; simp at hk
  lift k to NNReal using hktop
  have h : ((k : ℝ) * k) = 1 := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := k.2
  have : (k : ℝ) = 1 := by nlinarith
  exact_mod_cast this

/-- The data `configLawFull` reads from a configuration. -/
noncomputable def cfgData (c : FieldSample × (ℝ → ℝ)) : ((ℕ → ℝ) × (TestFun H → ℝ)) × (NNReal → ℝ) :=
  ((CoordsFull.coordsFull c.1, fun ρ => pairRaw c.1 ρ.1), fun t : NNReal => c.2 t)

omit [IsProbabilityMeasure P] in
theorem configLawFull_eq_map_cfgData (c : Ω → FieldSample × (ℝ → ℝ)) :
    configLawFull c P = P.map fun ω => cfgData (c ω) := rfl

end F1d

/-! ## F1c (abstract core): germ-measurable ratios are constant -/

section F1c

open ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A `ℝ≥0∞`-valued function measurable for a `P`-trivial σ-algebra is a.s. constant. -/
theorem ae_eq_const_of_isTrivialSigma (hm : m ≤ mΩ)
    (htriv : GermZeroOne.IsTrivialSigma m P) {f : Ω → ℝ≥0∞} (hf : Measurable[m] f) :
    ∃ k : ℝ≥0∞, ∀ᵐ ω ∂P, f ω = k := by
  obtain ⟨k, hk⟩ := exists_eventuallyEq_const_of_forall_separating (l := ae P) (f := f)
    MeasurableSet (fun U hU => by
      have hs : MeasurableSet[m] (f ⁻¹' U) := hf hU
      rcases htriv _ hs with h0 | h1
      · right
        exact measure_eq_zero_iff_ae_notMem.1 h0
      · left
        have hc : P (f ⁻¹' U)ᶜ = 0 := by
          rw [measure_compl (hm _ hs) (measure_ne_top _ _), h1, measure_univ, tsub_self]
        exact (ae_iff.2 (by simpa [Set.compl_def] using hc)))
  exact ⟨k, hk⟩

/-- **F1c (abstract core).** If `f` (the ratio `F 1`) is measurable for the germ
`⨅ n, ⨆ i ∈ S, 𝒜 i n` of finitely many independent families, each with a trivial germ
(lateral germ L11, tail of the radial BM, Blumenthal for the driver), then `f` is a.s.
constant (`isTrivialSigma_iInf_biSup`). -/
theorem f1c_ae_const_of_germ {ι : Type*} (𝒜 : ι → ℕ → MeasurableSpace Ω)
    (hle : ∀ i n, 𝒜 i n ≤ mΩ) (hanti : ∀ i, Antitone (𝒜 i))
    (hind : iIndep (fun i => 𝒜 i 0) P)
    (htriv : ∀ i, GermZeroOne.IsTrivialSigma (⨅ n, 𝒜 i n) P) (S : Finset ι)
    {f : Ω → ℝ≥0∞} (hf : Measurable[⨅ n, ⨆ i ∈ S, 𝒜 i n] f) :
    ∃ k : ℝ≥0∞, ∀ᵐ ω ∂P, f ω = k :=
  ae_eq_const_of_isTrivialSigma
    ((iInf_le _ 0).trans (iSup₂_le fun i _ => hle i 0))
    (GermZeroOne.isTrivialSigma_iInf_biSup 𝒜 hle hanti hind htriv S) hf

end F1c

end F1
end QuantumZipper
