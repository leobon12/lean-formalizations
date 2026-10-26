import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.Weak.DetLFPPMetric
import HigherDimLQGMetric.Sec4.Lemma41Uniform

/-!
# Normalizer basics (packet N1)

Generic facts used by the identification of `𝔞_ε` (planning audit MA1, Details A1), the transfer of
Assumption 1.1 (v) (MA1 A3) and Lemma 2.5 (MA1 A7) of `source/higher-dimensional-lfpp-almost-sure.pdf`.
Nothing here depends on the seed `κ` beyond the stated continuity of its convolution field.

* `n1_nullMeasurableSet_supEdist_ge`: for a.s. continuous random functions on `ℝ^d × ℝ^d` with
  a.e.-measurable evaluations, the events `{c ≤ sup_S edist (X ω) (Y ω)}` are null-measurable (the
  supremum over `S` is the supremum over a countable dense subset of `S`);
* `n1_aemeasurable_lfppDist`: for a measurable random distribution whose convolution field is a.s.
  continuous, every LFPP point distance `ω ↦ D^ε_{h(ω)}(p)` is a.e.-measurable (the modification of
  `HigherDimLQGMetric.l10a_aemeasurable_lfppPoint`, at every pair `p`);
* `n1_continuous_lfppDist`, `n1_lfppDist_pos`: for a continuous convolution field the LFPP distance is
  continuous in both endpoints and positive off the diagonal;
* `n1_preimage_eq_normLGFLaw`: the probability of a null-measurable event of a normalized LGF is its
  probability under the normalized law `normLGFLaw d` (the outer-measure inequality
  `l9b_preimage_le_normLGFLaw` becomes an equality).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Normalizer

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-! ## Suprema over dense subsets and null-measurability -/

/-- The supremum of a continuous `ℝ≥0∞`-valued function over `S` equals its supremum over any subset of
`S` whose closure contains `S`. -/
theorem n1_biSup_eq_of_subset_closure {α : Type*} [TopologicalSpace α] {g : α → ℝ≥0∞}
    (hg : Continuous g) {S C : Set α} (hCS : C ⊆ S) (hSC : S ⊆ closure C) :
    ⨆ p ∈ S, g p = ⨆ p ∈ C, g p := by
  refine le_antisymm (iSup₂_le fun p hp => ?_) (biSup_mono hCS)
  have hcl : closure C ⊆ g ⁻¹' Iic (⨆ c ∈ C, g c) :=
    closure_minimal (fun c hc => le_biSup g hc) (isClosed_Iic.preimage hg)
  exact hcl (hSC hp)

/-- **Null-measurability of the events of convergence in probability.** If `X ω`, `Y ω` are a.s.
continuous functions on `ℝ^d × ℝ^d` and all evaluations are a.e.-measurable, then for every set `S` and
level `c`, `{ω | c ≤ sup_{p ∈ S} edist (X ω p) (Y ω p)}` is null-measurable. -/
theorem n1_nullMeasurableSet_supEdist_ge {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → Rd d × Rd d → ℝ}
    (hXc : ∀ᵐ ω ∂P, Continuous (X ω)) (hYc : ∀ᵐ ω ∂P, Continuous (Y ω))
    (hXm : ∀ p, AEMeasurable (fun ω => X ω p) P) (hYm : ∀ p, AEMeasurable (fun ω => Y ω p) P)
    (S : Set (Rd d × Rd d)) (c : ℝ≥0∞) :
    NullMeasurableSet {ω | c ≤ ⨆ p ∈ S, edist (X ω p) (Y ω p)} P := by
  obtain ⟨C, hCS, hCc, hSC⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hF : AEMeasurable (fun ω => ⨆ p ∈ C, edist (X ω p) (Y ω p)) P :=
    AEMeasurable.biSup C hCc fun p _ => (hXm p).edist (hYm p)
  have heq : (fun ω => ⨆ p ∈ C, edist (X ω p) (Y ω p)) =ᵐ[P]
      fun ω => ⨆ p ∈ S, edist (X ω p) (Y ω p) := by
    filter_upwards [hXc, hYc] with ω hx hy
    exact (n1_biSup_eq_of_subset_closure (hx.edist hy) hCS hSC).symm
  exact (hF.congr heq).nullMeasurable measurableSet_Ici

/-! ## The LFPP distance of a continuous convolution field -/

/-- For a continuous convolution field, the LFPP distance is continuous in both endpoints. -/
theorem n1_continuous_lfppDist {d : ℕ} {κ : Rd d → ℝ} {ξ ε : ℝ} {g : DistRd d}
    (hc : Continuous fun z => convMollify κ ε g z) : Continuous (lfppDist κ ξ ε g) := by
  have h := continuous_fieldLfpp (ξ := ξ) hc
  refine h.congr fun p => ?_
  rw [fieldLfpp_eq_lfppDistOn hc p]
  rfl

/-- For a continuous convolution field, the LFPP distance is positive off the diagonal. -/
theorem n1_lfppDist_pos {d : ℕ} {κ : Rd d → ℝ} {ξ ε : ℝ} {g : DistRd d}
    (hc : Continuous fun z => convMollify κ ε g z) {x y : Rd d} (hxy : x ≠ y) :
    0 < lfppDist κ ξ ε g (x, y) :=
  HigherDimLFPP.lfppDistOn_pos hc hxy
    (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ x) (mem_univ y))

/-- **A.e.-measurability of the LFPP point distances.** If the random distribution `h` is measurable and
its convolution field at cutoff `ε` is a.s. continuous, then `ω ↦ D^ε_{h(ω)}(p)` is a.e.-measurable for
every pair `p` (continuous modification on the full-measure event, then measurability of
`φ ↦ lfppDistOn ξ φ univ x y` on `C(ℝ^d, ℝ)`). -/
theorem n1_aemeasurable_lfppDist {d : ℕ} {κ : Rd d → ℝ} (ξ : ℝ) {ε : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d} (hm : Measurable h)
    (hc : ∀ᵐ ω ∂P, Continuous fun z => convMollify κ ε (h ω) z) (p : Rd d × Rd d) :
    AEMeasurable (fun ω => lfppDist κ ξ ε (h ω) p) P := by
  let H : Rd d → Ω → ℝ := fun z ω => convMollify κ ε (h ω) z
  have hHm : ∀ z, Measurable (H z) := fun z =>
    (l10a_measurable_convMollify_apply κ ε z).comp hm
  classical
  let Y : Rd d → Ω → ℝ := fun z ω =>
    if Continuous (fun z => H z ω) then H z ω else 0
  have hYc : ∀ ω, Continuous fun z => Y z ω := by
    intro ω
    by_cases hcont : Continuous (fun z => H z ω)
    · have heq : (fun z => Y z ω) = (fun z => H z ω) := by
        funext z
        exact ite_eq_left hcont
      rw [heq]
      exact hcont
    · have heq : (fun z => Y z ω) = (fun _ => 0) := by
        funext z
        exact ite_eq_right hcont
      rw [heq]
      exact continuous_const
  have hYae : ∀ᵐ ω ∂P, ∀ z, Y z ω = H z ω := by
    filter_upwards [hc] with ω hω z
    exact ite_eq_left hω
  have hYm : ∀ z, AEMeasurable (Y z) P := by
    intro z
    have heq : Y z =ᵐ[P] H z := hYae.mono fun _ hω => hω z
    exact (aemeasurable_congr heq.symm).1 (hHm z).aemeasurable
  have hCM := l10a_aemeasurable_toContMap Y hYm hYc
  have hF : Measurable (fun φ : C(Rd d, ℝ) => HigherDimLFPP.lfppDistOn ξ φ univ p.1 p.2) :=
    HigherDimLFPP.measurable_lfppDistOn_continuousMap isOpen_univ ξ p.1 p.2
  have hAY : AEMeasurable (fun ω =>
      HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) univ p.1 p.2) P := by
    simpa only [Function.comp_def, ContinuousMap.coe_mk] using hF.comp_aemeasurable hCM
  have heq : (fun ω => HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) univ p.1 p.2) =ᵐ[P]
      (fun ω => lfppDist κ ξ ε (h ω) p) := by
    filter_upwards [hYae] with ω hω
    simp only [lfppDist]
    congr 1
    funext z
    exact hω z
  exact (aemeasurable_congr heq).1 hAY

/-! ## Laws of normalized LGFs -/

/-- **Law transfer for null-measurable events.** For a normalized LGF `h` and a set `A` of distributions
that is null-measurable for `normLGFLaw d`, `P (h⁻¹ A) = normLGFLaw d A`. -/
theorem n1_preimage_eq_normLGFLaw {d : ℕ} (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsNormalizedLGF h P)
    {A : Set (DistRd d)} (hA : NullMeasurableSet A (normLGFLaw d)) :
    P (h ⁻¹' A) = normLGFLaw d A := by
  rw [← l9b_map_eq_normLGFLaw hd hh] at hA ⊢
  exact (Measure.map_apply₀ hh.1.measurable.aemeasurable hA).symm

/-- Two normalized LGFs give the same probability to every event that is null-measurable for the
normalized law. -/
theorem n1_preimage_eq_preimage {d : ℕ} (hd : 2 ≤ d) {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {h : Ω → DistRd d} {g : Ω' → DistRd d} (hh : IsNormalizedLGF h P)
    (hg : IsNormalizedLGF g P') {A : Set (DistRd d)} (hA : NullMeasurableSet A (normLGFLaw d)) :
    P (h ⁻¹' A) = P' (g ⁻¹' A) := by
  rw [n1_preimage_eq_normLGFLaw hd hh hA, n1_preimage_eq_normLGFLaw hd hg hA]

end HigherDimLFPPAS.Normalizer
