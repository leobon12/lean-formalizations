import QuantumZipper.Proofs.Section5.Prop17StatPalm
import QuantumZipper.Proofs.Zipper.D3PlusITV

/-!
# Proposition 1.7, node D4⁺ (Palm zoom): the mixture step (PALMZOOM)

Sheffield, arXiv:1012.4797, proof of Proposition 1.6 (p. 25): "Given `x`, the conditional law
of `h` is that of the original GFF plus `(γ/2) G(x, ·)` [the rooted/Palm measure]; zooming in at
the fixed point `x` gives the `γ`-quantum wedge". The Palm law of the zoom is therefore a mixture,
over the Palm point `x` (law `ρ`, the normalized intensity measure), of the laws of the zooms at
the *fixed* point `x` of the Palm-shifted field; TV-local convergence of each fixed-point zoom
implies TV-local convergence of the mixture (TV is convex: Levin–Peres–Wilmer, *Markov Chains
and Mixing Times* §4.1, in the kernel form `TV.tvDist_bind_le`; then dominated convergence,
since `tvDist ≤ 1`). The same mixture step is the one used for the rooted measure in
Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7 (pp. 77–78).

* `tvLocalTendsto_prod_map_of_ae`: abstract mixture lemma (own elementary proof of this standard
  step, written out from the sources above).
* `Prop17PalmRepStmt γ`: D4⁺ in *mixture form* — a Palm scheme with all regularity clauses of
  `Prop17PalmZoomStmt γ`, whose Palm zoom laws are `(P ⊗ ρ).map (F C)` and whose fixed-point
  zoom laws `P.map (F C (·, x))` converge TV-locally for `ρ`-a.e. `x`.
* `prop17PalmZoomStmt_of_rep : Prop17PalmRepStmt γ → Prop17PalmZoomStmt γ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift

/-! ## 1. The section kernel -/

section Mix

variable {Ω T E : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace E]

/-- The kernel `x ↦ P.map (G (·, x))` of a jointly measurable map. -/
def sectionKernel (P : Measure Ω) [SFinite P] {G : Ω × T → E} (hG : Measurable G) :
    Kernel T E :=
  ⟨fun x => P.map fun ω => G (ω, x), D3Plus.measurable_map_section P hG⟩

theorem sectionKernel_apply (P : Measure Ω) [SFinite P] {G : Ω × T → E} (hG : Measurable G)
    (x : T) : sectionKernel P hG x = P.map fun ω => G (ω, x) := rfl

instance isMarkovKernel_sectionKernel (P : Measure Ω) [IsProbabilityMeasure P] {G : Ω × T → E}
    (hG : Measurable G) : IsMarkovKernel (sectionKernel P hG) :=
  ⟨fun x => by
    rw [sectionKernel_apply]
    exact (Measure.isProbabilityMeasure_map_iff
      (hG.comp (measurable_prodMk_right (y := x))).aemeasurable).2 inferInstance⟩

/-- `(P ⊗ ρ).map G = ρ.bind (x ↦ P.map (G (·, x)))`. -/
theorem prod_map_eq_bind_sectionKernel (P : Measure Ω) [SFinite P] (ρ : Measure T) [SFinite ρ]
    {G : Ω × T → E} (hG : Measurable G) :
    (P.prod ρ).map G = ρ.bind (sectionKernel P hG) := by
  ext s hs
  rw [Measure.map_apply hG hs, Measure.bind_apply hs (sectionKernel P hG).aemeasurable,
    Measure.prod_apply_symm (hG hs)]
  refine lintegral_congr fun x => ?_
  have hx : Measurable fun ω => G (ω, x) := hG.comp measurable_prodMk_right
  rw [sectionKernel_apply, Measure.map_apply hx hs]
  rfl

theorem bind_const_eq_self (ρ : Measure T) [IsProbabilityMeasure ρ] (μ : Measure E) :
    ρ.bind (Kernel.const T μ) = μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.const T μ).aemeasurable]
  simp [Kernel.const_apply]

/-! ## 2. The mixture lemma -/

/-- **Mixture lemma.** If for `ρ`-a.e. `x` the laws `P.map (F i (·, x))` converge TV-locally to
`μ`, then so do the mixtures `(P ⊗ ρ).map (F i)`. -/
theorem tvLocalTendsto_prod_map_of_ae {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ : Measure T) [IsProbabilityMeasure ρ]
    (μ : Measure E) [IsProbabilityMeasure μ] {Fl : ℕ → Type*} [∀ R, MeasurableSpace (Fl R)]
    [∀ R, MeasurableSpace.CountablyGenerated (Fl R)] {loc : ∀ R, E → Fl R}
    (hloc : ∀ R, Measurable (loc R)) {F : ι → Ω × T → E} (hF : ∀ i, Measurable (F i))
    (hlim : ∀ᵐ x ∂ρ, TVLocalTendsto l (fun i => P.map fun ω => F i (ω, x)) μ loc) :
    TVLocalTendsto l (fun i => (P.prod ρ).map (F i)) μ loc := by
  intro R
  have hG : ∀ i, Measurable (loc R ∘ F i) := fun i => (hloc R).comp (hF i)
  set κ : ι → Kernel T (Fl R) := fun i => sectionKernel P (hG i) with hκ
  have : ∀ i, IsMarkovKernel (κ i) := fun i => isMarkovKernel_sectionKernel P (hG i)
  have : IsProbabilityMeasure (μ.map (loc R)) :=
    (Measure.isProbabilityMeasure_map_iff (hloc R).aemeasurable).2 inferInstance
  have hbound : ∀ i, tvDist (((P.prod ρ).map (F i)).map (loc R)) (μ.map (loc R)) ≤
      ∫⁻ x, tvDist (κ i x) (μ.map (loc R)) ∂ρ := by
    intro i
    rw [Measure.map_map (hloc R) (hF i), prod_map_eq_bind_sectionKernel P ρ (hG i)]
    conv_lhs => rw [← bind_const_eq_self ρ (μ.map (loc R))]
    have := tvDist_bind_le (μ := ρ) (κ i) (Kernel.const T (μ.map (loc R)))
    simpa [Kernel.const_apply] using this
  have hκx : ∀ i x, κ i x = (P.map fun ω => F i (ω, x)).map (loc R) := fun i x => by
    have hx : Measurable fun ω => F i (ω, x) := (hF i).comp measurable_prodMk_right
    rw [hκ, sectionKernel_apply, Measure.map_map (hloc R) hx]
    rfl
  have hdom : Tendsto (fun i => ∫⁻ x, tvDist (κ i x) (μ.map (loc R)) ∂ρ) l (𝓝 (∫⁻ _x, 0 ∂ρ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun i => D3Plus.measurable_tvDist_kernel (κ i) _)
      (Eventually.of_forall fun i => ae_of_all _ fun x => tvDist_le_one) (by simp) ?_
    filter_upwards [hlim] with x hx
    simpa only [hκx] using hx R
  rw [lintegral_zero] at hdom
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdom
    (fun _ => bot_le) hbound

end Mix

/-! ## 3. D4⁺ in mixture form -/

/-- **D4⁺ for Proposition 1.7, mixture form (hypothesis).** As `Prop17PalmZoomStmt γ`, except
that the TV-local clause is replaced by a mixture representation: there are a probability
measure `ρ` on `ℝ` (the law of the Palm point) and jointly measurable `F C : Ω × ℝ → (ℕ → ℝ)`
(the zoom coordinates at the fixed point `x` of the Palm-shifted field) with
`(palmLaw P ν a b).map (zoomCoords γ C h) = (P ⊗ ρ).map (F C)`, and for `ρ`-a.e. `x` the
fixed-point zoom laws `P.map (F C (·, x))` converge TV-locally to the reference law. -/
def Prop17PalmRepStmt (γ : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (h : Ω → FieldSample)
      (ν : Kernel Ω ℝ) (a b : ℝ), IsProbabilityMeasure P ∧ IsSFiniteKernel ν ∧
      palmMass P ν a b ≠ 0 ∧ palmMass P ν a b ≠ ∞ ∧
      (∀ᵐ ω ∂P, ν ω = qBoundaryMeasure γ (h ω) ∧ IsLQGGood γ (h ω) ∧
        (∀ t : ℝ, ν ω {t} = 0) ∧ (∀ u v : ℝ, u < v → 0 < ν ω (Ioo u v)) ∧
        (∀ x : ℝ, ν ω (Ici x) = ⊤) ∧ ∀ C x : ℝ, 0 < scaleParam γ (zoomField γ C (h ω) x)) ∧
      (∀ C : ℝ, Measurable (zoomCoords γ C h)) ∧
      ∃ (ρ : Measure ℝ) (F : ℝ → Ω × ℝ → (ℕ → ℝ)), IsProbabilityMeasure ρ ∧
        (∀ C, Measurable (F C)) ∧
        (∀ C, (palmLaw P ν a b).map (zoomCoords γ C h) = (P.prod ρ).map (F C)) ∧
        ∀ᵐ x ∂ρ, TVLocalTendsto atTop (fun C : ℝ => P.map fun ω => F C (ω, x))
          (P'.map fun ω => coordsFull (refField γ X A ω)) locFull

/-- **D4⁺ (Palm zoom) from its mixture form.** -/
theorem prop17PalmZoomStmt_of_rep {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hrep : Prop17PalmRepStmt γ) :
    Prop17PalmZoomStmt γ := by
  intro Ω' _ P' X A hP' hX hA hI
  obtain ⟨Ω, _, P, h, ν, a, b, hP, hν, h0, htop, hae, hmeas, ρ, F, hρ, hF, hrepr, hlim⟩ :=
    hrep Ω' _ P' X A hP' hX hA hI
  refine ⟨Ω, _, P, h, ν, a, b, hP, hν, h0, htop, hae, hmeas, ?_⟩
  have := hP'
  have hW : IsQuantumWedge γ γ (refField γ X A) P' :=
    ⟨gamma_lt_Qc' hγ hγ2, Ω', _, P', X, A, hP', hX, hA, hI, rfl⟩
  have : IsProbabilityMeasure (P'.map fun ω => coordsFull (refField γ X A ω)) :=
    (Measure.isProbabilityMeasure_map_iff
      (Wire3.wedgeDataAEMeasStmt_uncond hγ hγ2 P' _ hW).fst).2 inferInstance
  simp_rw [hrepr]
  exact tvLocalTendsto_prod_map_of_ae P ρ _ measurable_locFull hF hlim

end Raw
end FieldLaw
end S5
end QuantumZipper
