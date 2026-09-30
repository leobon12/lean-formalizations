import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Proposition 1.7: invariance of a limit law under a shift (abstract step, PROP17-STAT)

Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797, proof of Proposition 1.7 (p. 25–26): in the pre-limit (the Palm zoom of
Proposition 1.6) the shift by quantum length `L` changes the law by a total-variation error that
tends to `0`, and "since this `δ` tends to zero as `C → ∞` we conclude that the limiting surface
law is invariant under the operation that translates the origin by `L`". The paper does not spell
out this passage to the limit; here it is, in the abstract (own elementary argument, AGENT_GUIDE
cost rule):

* `map_eq_self_of_shift_approx`: `μ.map T = μ` if, on a generating π-system `Pi0`,
  (a) `μ_i E → μ E`, (b) `μ_i (T⁻¹E) - μ_i E → 0`, and (c) `T⁻¹E` is approximable from inside by
  sets `D` with `μ_i D → μ D` up to an arbitrary small error (both for `μ` and eventually `μ_i`);
* `shiftApprox_of_local`: (c) holds when the convergence `μ_i F → μ F` is known on a class `𝒜`
  of "local" events and `T` is local on an exhausting increasing family `B n`, modulo a set
  `Good` of full measure for `μ` and every `μ_i` (the exact locality of `T` may fail on junk
  samples);
* `map_eq_self_of_local`: the combination.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

variable {S ι : Type*} [MeasurableSpace S] {l : Filter ι}

/-- **Passage to the limit (abstract).** -/
theorem map_eq_self_of_shift_approx [l.NeBot] {μ : Measure S} [IsProbabilityMeasure μ]
    {μs : ι → Measure S} [∀ i, IsProbabilityMeasure (μs i)] {T : S → S} (hT : Measurable T)
    {Pi0 : Set (Set S)} (hgen : ‹MeasurableSpace S› = MeasurableSpace.generateFrom Pi0)
    (hpi : IsPiSystem Pi0)
    (hE : ∀ E ∈ Pi0, Tendsto (fun i => (μs i).real E) l (𝓝 (μ.real E)))
    (hshift : ∀ E ∈ Pi0, Tendsto (fun i => (μs i).real (T ⁻¹' E) - (μs i).real E) l (𝓝 0))
    (hloc : ∀ E ∈ Pi0, ∀ ε : ℝ, 0 < ε → ∃ D, MeasurableSet D ∧ D ⊆ T ⁻¹' E ∧
      μ.real (T ⁻¹' E \ D) ≤ ε ∧ Tendsto (fun i => (μs i).real D) l (𝓝 (μ.real D)) ∧
      ∀ᶠ i in l, (μs i).real (T ⁻¹' E \ D) ≤ ε) :
    μ.map T = μ := by
  refine ext_of_generate_finite Pi0 hgen hpi (fun E hEP => ?_) (by simp [Measure.map_apply hT])
  have hEm : MeasurableSet E := hgen ▸ MeasurableSpace.measurableSet_generateFrom hEP
  rw [Measure.map_apply hT hEm]
  have hTE : MeasurableSet (T ⁻¹' E) := hT hEm
  suffices h : μ.real (T ⁻¹' E) = μ.real E by
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h
  -- `μ_i (T⁻¹E) → μ E`
  have hx : Tendsto (fun i => (μs i).real (T ⁻¹' E)) l (𝓝 (μ.real E)) := by
    have := (hshift E hEP).add (hE E hEP)
    simpa using this
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨D, hDm, hDsub, hμD, hDconv, hev⟩ := hloc E hEP ε hε
  have split : ∀ ν : Measure S, [IsFiniteMeasure ν] →
      ν.real D + ν.real (T ⁻¹' E \ D) = ν.real (T ⁻¹' E) := fun ν _ => by
    rw [measureReal_add_sdiff hDm, union_eq_right.2 hDsub]
  -- the limit of `μ_i (T⁻¹E \ D)` is `μ E - μ D`
  have hlim : Tendsto (fun i => (μs i).real (T ⁻¹' E \ D)) l (𝓝 (μ.real E - μ.real D)) := by
    refine (hx.sub hDconv).congr fun i => ?_
    have := split (μs i)
    linarith
  have h1 : μ.real E - μ.real D ≤ ε := le_of_tendsto hlim hev
  have h2 : 0 ≤ μ.real E - μ.real D :=
    ge_of_tendsto hlim (Eventually.of_forall fun i => measureReal_nonneg)
  have h3 := split μ
  have h4 : 0 ≤ μ.real (T ⁻¹' E \ D) := measureReal_nonneg
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- **Inner approximation from locality.** -/
theorem shiftApprox_of_local {μ : Measure S} [IsProbabilityMeasure μ]
    {μs : ι → Measure S} [∀ i, IsProbabilityMeasure (μs i)] {T : S → S} (hT : Measurable T)
    {𝒜 : Set (Set S)}
    (hconv : ∀ F ∈ 𝒜, Tendsto (fun i => (μs i).real F) l (𝓝 (μ.real F)))
    {Good : Set S} (hgμ : ∀ᵐ c ∂μ, c ∈ Good) (hgμs : ∀ i, ∀ᵐ c ∂μs i, c ∈ Good)
    {B : ℕ → Set S} (hBmono : Monotone B) (hBm : ∀ n, MeasurableSet (B n))
    (hBcov : ∀ᵐ c ∂μ, c ∈ ⋃ n, B n)
    (hBloc : ∀ n, ∃ F ∈ 𝒜, B n ∩ Good = F ∩ Good)
    {E : Set S} (hEm : MeasurableSet E)
    (hTloc : ∀ n, ∃ F ∈ 𝒜, T ⁻¹' E ∩ B n ∩ Good = F ∩ Good) :
    ∀ ε : ℝ, 0 < ε → ∃ D, MeasurableSet D ∧ D ⊆ T ⁻¹' E ∧
      μ.real (T ⁻¹' E \ D) ≤ ε ∧ Tendsto (fun i => (μs i).real D) l (𝓝 (μ.real D)) ∧
      ∀ᶠ i in l, (μs i).real (T ⁻¹' E \ D) ≤ ε := by
  intro ε hε
  -- sets agreeing on `Good` have the same measure
  have congrG : ∀ (ν : Measure S) {X Y : Set S}, (∀ᵐ c ∂ν, c ∈ Good) →
      X ∩ Good = Y ∩ Good → ν.real X = ν.real Y := fun ν X Y hg h => by
    refine measureReal_congr ?_
    filter_upwards [hg] with c hc
    apply propext
    constructor
    · intro hx
      have : c ∈ Y ∩ Good := h ▸ (show c ∈ X ∩ Good from ⟨hx, hc⟩)
      exact this.1
    · intro hy
      have : c ∈ X ∩ Good := h.symm ▸ (show c ∈ Y ∩ Good from ⟨hy, hc⟩)
      exact this.1
  -- choose `n` with `μ (B n)ᶜ < ε`
  have hcov : Tendsto (fun n => μ.real (B n)) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) hBmono
    have hU : μ (⋃ n, B n) = 1 := by
      rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion hBm)]
      exact ae_iff.1 hBcov |> fun h' => by simpa [compl_def] using h'
    rw [hU] at h
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
    simpa [Function.comp_def, measureReal_def] using this
  obtain ⟨n, hn⟩ := (hcov.eventually (Ioo_mem_nhds (show (1 : ℝ) - ε < 1 by linarith)
    (show (1 : ℝ) < 2 by norm_num))).exists
  obtain ⟨FB, hFB, hFBeq⟩ := hBloc n
  obtain ⟨FD, hFD, hFDeq⟩ := hTloc n
  refine ⟨T ⁻¹' E ∩ B n, (hT hEm).inter (hBm n), inter_subset_left, ?_, ?_, ?_⟩
  · calc μ.real (T ⁻¹' E \ (T ⁻¹' E ∩ B n)) ≤ μ.real (B n)ᶜ :=
          measureReal_mono fun c hc => fun hb => hc.2 ⟨hc.1, hb⟩
      _ = 1 - μ.real (B n) := by rw [measureReal_compl (hBm n), probReal_univ]
      _ ≤ ε := by linarith [hn.1]
  · have h1 : ∀ i, (μs i).real (T ⁻¹' E ∩ B n) = (μs i).real FD := fun i =>
      congrG (μs i) (hgμs i) (by rw [hFDeq])
    have h2 : μ.real (T ⁻¹' E ∩ B n) = μ.real FD := congrG μ hgμ (by rw [hFDeq])
    simp only [h1, h2]
    exact hconv FD hFD
  · have hB : Tendsto (fun i => (μs i).real (B n)) l (𝓝 (μ.real (B n))) := by
      have h1 : ∀ i, (μs i).real (B n) = (μs i).real FB := fun i =>
        congrG (μs i) (hgμs i) hFBeq
      have h2 : μ.real (B n) = μ.real FB := congrG μ hgμ hFBeq
      simp only [h1, h2]
      exact hconv FB hFB
    filter_upwards [hB.eventually (lt_mem_nhds (show μ.real (B n) > 1 - ε from hn.1))]
      with i hi
    calc (μs i).real (T ⁻¹' E \ (T ⁻¹' E ∩ B n)) ≤ (μs i).real (B n)ᶜ :=
          measureReal_mono fun c hc => fun hb => hc.2 ⟨hc.1, hb⟩
      _ = 1 - (μs i).real (B n) := by rw [measureReal_compl (hBm n), probReal_univ]
      _ ≤ ε := by linarith

/-- **Passage to the limit from TV-local data (abstract).** -/
theorem map_eq_self_of_local [l.NeBot] {μ : Measure S} [IsProbabilityMeasure μ]
    {μs : ι → Measure S} [∀ i, IsProbabilityMeasure (μs i)] {T : S → S} (hT : Measurable T)
    {Pi0 : Set (Set S)} (hgen : ‹MeasurableSpace S› = MeasurableSpace.generateFrom Pi0)
    (hpi : IsPiSystem Pi0)
    {𝒜 : Set (Set S)}
    (hconv : ∀ F ∈ 𝒜, Tendsto (fun i => (μs i).real F) l (𝓝 (μ.real F)))
    (hP𝒜 : Pi0 ⊆ 𝒜)
    (hshift : ∀ E ∈ Pi0, Tendsto (fun i => (μs i).real (T ⁻¹' E) - (μs i).real E) l (𝓝 0))
    {Good : Set S} (hgμ : ∀ᵐ c ∂μ, c ∈ Good) (hgμs : ∀ i, ∀ᵐ c ∂μs i, c ∈ Good)
    {B : ℕ → Set S} (hBmono : Monotone B) (hBm : ∀ n, MeasurableSet (B n))
    (hBcov : ∀ᵐ c ∂μ, c ∈ ⋃ n, B n)
    (hBloc : ∀ n, ∃ F ∈ 𝒜, B n ∩ Good = F ∩ Good)
    (hTloc : ∀ E ∈ Pi0, ∀ n, ∃ F ∈ 𝒜, T ⁻¹' E ∩ B n ∩ Good = F ∩ Good) :
    μ.map T = μ :=
  map_eq_self_of_shift_approx hT hgen hpi (fun E hE => hconv E (hP𝒜 hE)) hshift
    fun E hE => shiftApprox_of_local hT hconv hgμ hgμs hBmono hBm hBcov hBloc
      (hgen ▸ MeasurableSpace.measurableSet_generateFrom hE) (hTloc E hE)

end Raw
end FieldLaw
end S5
end QuantumZipper
