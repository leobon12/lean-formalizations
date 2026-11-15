/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54MarkQ
import InteractingSLE.Spec.Sec7.LocalExtNPost
import InteractingSLE.Spec.Exist.Param12CanonicalExist

/-!
# Aux. lemma 54 for general words, part 10: records on events and the reference side

Packet PROVE-AUX54.

* `recOn D Y y`: the record of a field `Y` read from histories `y` on an event `D` (a fixed value off `D`), measurable
  for any σ-algebra containing `σ(Y)`, `D` and `D ∩ {y ∈ M}`;
* `fieldRecA_add`, `recBuild`, `recBuild_markov`: the record of the field rebuilt from its projection onto `H(U)` and
  the record of the complementary projection;
* `measurable_killedHistory_of_stop`: the history killed at a stop `V₀ ≤ ζ` of the driving filtration is measurable for
  the stopped σ-algebra;
* the **safe events at `s`** of the reference (`refSafeGens`): events of the driving filtration at `s` on which
  `s < ζ₀` and `C ∩ K̂_s = ∅`; the family-local reference satisfies the projection identity on the σ-algebra they
  generate (`setIntegral_lapTest_refSafe`);
* **`setIntegral_recOn_gauss`**: for a σ-algebra `𝓜₀` with the projection identity and `D₀ ∈ 𝓜₀` with
  `D₀ ∩ {y ∈ M} ∈ 𝓜₀`, every bounded function of the record of `X − G X` on `D₀` is independent of `G X`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4 StoppedExtendWF Coupling DomainMarkov LQGMetric.MarkovZB LocalSets
open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {nL nR : ℕ}

/-! ### Records on events -/

section RecOn

variable {Ω : Type*} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

open Classical in
/-- The record of `Y` read from the histories `y` on the event `D` (a fixed value off `D`). -/
def recOn (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (D : Set Ω)
    (Y : Ω → DistOn upperHalfPlaneOpens) (y : Ω → HistorySpace nL nR) (ω : Ω) : RecSpace nL nR :=
  ((if ω ∈ D then y ω else 0),
    fun ψ => if ω ∈ D ∧ Disjoint (tsupport ψ) (recHull ρL ρR xL xR (y ω)) then Y ω ψ else 0)

theorem recOn_of_mem {D : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {y : Ω → HistorySpace nL nR} {ω : Ω}
    (hω : ω ∈ D) : recOn ρL ρR xL xR D Y y ω = recOfA (recHull ρL ρR xL xR) (Y ω) (y ω) := by
  classical
  refine Prod.ext ?_ (funext fun ψ => ?_)
  · simp only [recOn, hω, ↓reduceIte, recOfA]
  · simp only [recOn, hω, true_and, recOfA, fieldRecA]

theorem measurable_recOn {𝓜 𝓐 : MeasurableSpace Ω} {D : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens}
    {y : Ω → HistorySpace nL nR} (hY : Measurable[𝓐] Y) (h𝓐 : 𝓐 ≤ 𝓜) (hD : MeasurableSet[𝓜] D)
    (hy : ∀ M : Set (HistorySpace nL nR), MeasurableSet M → MeasurableSet[𝓜] (D ∩ y ⁻¹' M)) :
    Measurable[𝓜] (recOn ρL ρR xL xR D Y y) := by
  classical
  refine Measurable.prodMk (m := 𝓜) ?_ ?_
  · intro M hM
    have e : (fun ω => if ω ∈ D then y ω else (0 : HistorySpace nL nR)) ⁻¹' M =
        (D ∩ y ⁻¹' M) ∪ (Dᶜ ∩ {_ω | (0 : HistorySpace nL nR) ∈ M}) := by
      ext ω
      by_cases hω : ω ∈ D <;> simp [hω]
    show MeasurableSet[𝓜] ((fun ω => if ω ∈ D then y ω else (0 : HistorySpace nL nR)) ⁻¹' M)
    rw [e]
    refine (hy M hM).union (hD.compl.inter ?_)
    by_cases h0 : (0 : HistorySpace nL nR) ∈ M
    · simp only [h0, ofPred_true, MeasurableSet.univ]
    · simp only [h0, ofPred_false, MeasurableSet.empty]
  · refine (@measurable_pi_iff Ω (TestOn upperHalfPlaneOpens) (fun _ => ℝ) 𝓜 _).2 fun ψ => ?_
    have hset : MeasurableSet[𝓜] {ω | ω ∈ D ∧ Disjoint (tsupport ψ) (recHull ρL ρR xL xR (y ω))} :=
      hy _ (isMeasHull_recHull ρL ρR xL xR _ ψ.hasCompactSupport.isCompact)
    exact Measurable.ite hset (((measurable_distOn_apply ψ).comp hY).mono h𝓐 le_rfl) measurable_const

theorem fieldRecA_add {Γ : Type*} (A : Γ → Set ℂ) (x x' : DistOn upperHalfPlaneOpens) (y : Γ)
    (ψ : TestOn upperHalfPlaneOpens) : fieldRecA A (x + x') y ψ = fieldRecA A x y ψ + fieldRecA A x' y ψ := by
  classical
  by_cases hd : Disjoint (tsupport ψ) (A y)
  · rw [fieldRecA_of_disjoint hd, fieldRecA_of_disjoint hd, fieldRecA_of_disjoint hd]
    rfl
  · simp only [fieldRecA, hd, ↓reduceIte, add_zero]

/-- The record rebuilt from a projection `z`, the mean `T₀` and the record of the complementary projection. -/
def recBuild (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (T₀ : DistOn upperHalfPlaneOpens) (x : DistOn upperHalfPlaneOpens × RecSpace nL nR) : RecSpace nL nR :=
  (x.2.1, fun ψ => fieldRecA (recHull ρL ρR xL xR) (x.1 + T₀) x.2.1 ψ + x.2.2 ψ)

theorem measurable_recBuild (T₀ : DistOn upperHalfPlaneOpens) :
    Measurable (recBuild (nL := nL) (nR := nR) ρL ρR xL xR T₀) := by
  have hs : Measurable (Prod.snd : DistOn upperHalfPlaneOpens × RecSpace nL nR → RecSpace nL nR) := measurable_snd
  have hy : Measurable fun x : DistOn upperHalfPlaneOpens × RecSpace nL nR => x.2.1 := measurable_fst.comp hs
  have hF : Measurable fun x : DistOn upperHalfPlaneOpens × RecSpace nL nR => x.2.2 := measurable_snd.comp hs
  have h1 : Measurable fun x : DistOn upperHalfPlaneOpens × RecSpace nL nR => (x.1 + T₀, x.2.1) :=
    ((WholeField.measurable_add_dist T₀).comp measurable_fst).prodMk hy
  have h2 : ∀ ψ : TestOn upperHalfPlaneOpens,
      Measurable fun x : DistOn upperHalfPlaneOpens × RecSpace nL nR =>
        fieldRecA (recHull ρL ρR xL xR) (x.1 + T₀) x.2.1 ψ + x.2.2 ψ := by
    intro ψ
    have hr : Measurable fun p : DistOn upperHalfPlaneOpens × HistorySpace nL nR =>
        fieldRecA (recHull ρL ρR xL xR) p.1 p.2 ψ :=
      measurable_fieldRecA_apply (isMeasHull_recHull ρL ρR xL xR) ψ
    exact (hr.comp h1).add ((measurable_pi_apply ψ).comp hF)
  exact hy.prodMk (Measurable.of_eval h2)

theorem recBuild_markov (T₀ x : DistOn upperHalfPlaneOpens)
    (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (y : HistorySpace nL nR) :
    recBuild ρL ρR xL xR T₀ (G (x - T₀), recOfA (recHull ρL ρR xL xR) (markovCompl G (x - T₀)) y) =
      recOfA (recHull ρL ρR xL xR) x y := by
  refine Prod.ext rfl (funext fun ψ => ?_)
  simp only [recBuild, recOfA]
  rw [← fieldRecA_add]
  congr 1
  simp only [markovCompl]
  abel

end RecOn

/-! ### The killed history at a stop -/

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V₀ : Ω → ℝ≥0∞}

/-- **The history killed at a stop `V₀ ≤ ζ` of the driving filtration is measurable for the stopped σ-algebra.** -/
theorem measurable_killedHistory_of_stop {P : Measure Ω} (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hV₀ : IsStoppingTime (drivingFiltration P hX) fun ω => (V₀ ω : WithTop ℝ≥0)) (hV₀ζ : ∀ ω, V₀ ω ≤ ζ ω) :
    Measurable[hV₀.measurableSpace] (killedHistory W VL VR V₀) := by
  classical
  have hs : ∀ (p : ℕ × ℕ) (S : Set (DrivingValue nL nR)), MeasurableSet S →
      MeasurableSet[drivingFiltration P hX (dyadicTime p)]
        ((fun ω => (killedHistory W VL VR V₀ ω).2 p) ⁻¹' S) := by
    intro p S hS
    have e : (fun ω => (killedHistory W VL VR V₀ ω).2 p) ⁻¹' S =
        ({ω | (V₀ ω : WithTop ℝ≥0) ≤ ((dyadicTime p : ℝ≥0) : WithTop ℝ≥0)}ᶜ ∩
            (fun ω => (killedHistory W VL VR ζ ω).2 p) ⁻¹' S) ∪
          ({ω | (V₀ ω : WithTop ℝ≥0) ≤ ((dyadicTime p : ℝ≥0) : WithTop ℝ≥0)} ∩
            {_ω | (0 : DrivingValue nL nR) ∈ S}) := by
      ext ω
      simp only [mem_preimage, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
      by_cases hd : (V₀ ω : WithTop ℝ≥0) ≤ ((dyadicTime p : ℝ≥0) : WithTop ℝ≥0)
      · have h1 : ¬ ((dyadicTime p : ℝ≥0∞) < V₀ ω) := not_lt.2 hd
        simp only [killedHistory, h1, ↓reduceIte, hd, not_true_eq_false, false_and, true_and, false_or]
      · have h1 : (dyadicTime p : ℝ≥0∞) < V₀ ω := not_le.1 hd
        have h2 : (dyadicTime p : ℝ≥0∞) < ζ ω := lt_of_lt_of_le h1 (hV₀ζ ω)
        simp only [killedHistory, h1, h2, ↓reduceIte, hd, not_false_eq_true, true_and, false_and, or_false]
    rw [e]
    exact ((hV₀ (dyadicTime p)).compl.inter
      (Ito.le_usualAugmentation _ P _ _ (measurable_killedSample hX p hS))).union
      ((hV₀ (dyadicTime p)).inter (MeasurableSet.const _))
  exact measurable_killedHistory_stopped' hV₀ hs

end Stop

/-! ### The reference side -/

section Ref

variable {Ω₀ : Type*} [mΩ₀ : MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

/-- **The Gaussian factorization on the reference**: for a σ-algebra `𝓜₀` on which the projection identity holds, and
`D₀ ∈ 𝓜₀` with `D₀ ∩ {y ∈ M} ∈ 𝓜₀`, every bounded function of the record of `X − G X` on `D₀` is independent of
`G X` (PROVE-LOCEXT-N's `setIntegral_refRecord_gauss` for general histories). -/
theorem setIntegral_recOn_gauss {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {X : Ω₀ → DistOn upperHalfPlaneOpens} (hXm : Measurable X) {U : TopologicalSpace.Opens ℂ}
    (hUH : (U : Set ℂ) ⊆ H) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hGG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) P₀)
    {𝒢₀ : Set (Set Ω₀)} (h𝓜₀ : MeasurableSpace.generateFrom 𝒢₀ ≤ mΩ₀)
    (hid : ∀ (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (D : Set Ω₀),
      MeasurableSet[MeasurableSpace.generateFrom 𝒢₀] D →
      ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P₀ =
        Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P₀)
    {D₀ : Set Ω₀} (hD₀ : MeasurableSet[MeasurableSpace.generateFrom 𝒢₀] D₀) {y : Ω₀ → HistorySpace nL nR}
    (hy : ∀ M : Set (HistorySpace nL nR), MeasurableSet M →
      MeasurableSet[MeasurableSpace.generateFrom 𝒢₀] (D₀ ∩ y ⁻¹' M))
    {ã : ℝ × RecSpace nL nR → ℂ} (hã : Measurable ã) (χ : TestOn upperHalfPlaneOpens) :
    ∫ ω in D₀, Complex.exp (Complex.I * (G (X ω) χ : ℂ)) *
        ã ((1 : ℝ), recOfA (recHull ρL ρR xL xR) (markovCompl G (X ω)) (y ω)) ∂P₀ =
      LocalExt.gaussFactor U χ *
        ∫ ω in D₀, ã ((1 : ℝ), recOfA (recHull ρL ρR xL xR) (markovCompl G (X ω)) (y ω)) ∂P₀ := by
  classical
  have hind := LocalExt.indep_markov_of_setIntegral_lapTest hXm hUH hGG hd h𝓜₀ hid
  have h𝓜l : MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ≤
      MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔ MeasurableSpace.generateFrom 𝒢₀ :=
    le_sup_left
  have h𝓜r : MeasurableSpace.generateFrom 𝒢₀ ≤
      MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔ MeasurableSpace.generateFrom 𝒢₀ :=
    le_sup_right
  set ρ := recOn ρL ρR xL xR D₀ (fun ω => markovCompl G (X ω)) y with hρdef
  have hρ : Measurable[MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔
      MeasurableSpace.generateFrom 𝒢₀] ρ :=
    measurable_recOn (comap_measurable _) h𝓜l (h𝓜r _ hD₀) fun M hM => h𝓜r _ (hy M hM)
  set B : Ω₀ → ℂ := D₀.indicator fun ω => ã ((1 : ℝ), ρ ω) with hBdef
  have hB : Measurable[MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔
      MeasurableSpace.generateFrom 𝒢₀] B :=
    (hã.comp (Measurable.prodMk (m := MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔
      MeasurableSpace.generateFrom 𝒢₀) measurable_const hρ)).indicator (h𝓜r _ hD₀)
  have hind' : IndepFun (fun ω => G (X ω)) B P₀ :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right hind hB.comap_le)
  have hBm : Measurable B := hB.mono (sup_le ((measurable_markovCompl hGG).comp hXm).comap_le h𝓜₀) le_rfl
  have hprod := hind'.integral_fun_comp_mul_comp (f := fun T : DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * (T χ : ℂ))) (g := id) (hGG.comp hXm).aemeasurable hBm.aemeasurable
    (GFF.measurable_exp_I_mul (measurable_distOn_apply χ)).aestronglyMeasurable
    measurable_id.aestronglyMeasurable
  have hDm : MeasurableSet D₀ := h𝓜₀ _ hD₀
  have e1 : ∫ ω in D₀, Complex.exp (Complex.I * (G (X ω) χ : ℂ)) *
      ã ((1 : ℝ), recOfA (recHull ρL ρR xL xR) (markovCompl G (X ω)) (y ω)) ∂P₀ =
      ∫ ω, Complex.exp (Complex.I * (G (X ω) χ : ℂ)) * B ω ∂P₀ := by
    rw [← integral_indicator hDm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ D₀
    · simp only [indicator_of_mem hω, hBdef, hρdef, recOn_of_mem hω]
    · simp only [indicator_of_notMem hω, hBdef, mul_zero]
  have e2 : ∫ ω in D₀, ã ((1 : ℝ), recOfA (recHull ρL ρR xL xR) (markovCompl G (X ω)) (y ω)) ∂P₀ =
      ∫ ω, B ω ∂P₀ := by
    rw [← integral_indicator hDm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ D₀
    · simp only [indicator_of_mem hω, hBdef, hρdef, recOn_of_mem hω]
    · simp only [indicator_of_notMem hω, hBdef]
  rw [e1, e2]
  simp only [id] at hprod
  rw [hprod, LocalExt.integral_cexp_markov_eq_gauss hXm hUH hGG hd]

/-- The projection identity of `h` transfers to `h − T₀` for `T₀` harmonic on `ℍ`. -/
theorem setIntegral_lapTest_sub_harmonic {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) (f : zsSub (U : Set ℂ))
    (Ξ : TestOn upperHalfPlaneOpens) {S : Set Ω}
    (hid : ∫ ω in S, Complex.exp (Complex.I * (h ω (lapTest U f + Ξ) : ℂ)) ∂μ =
      Coupling.projFactor U f Ξ * ∫ ω in S, Complex.exp (Complex.I * (h ω Ξ : ℂ)) ∂μ) :
    ∫ ω in S, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂μ =
      Coupling.projFactor U f Ξ * ∫ ω in S, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂μ := by
  have h0 : T₀ (lapTest U f) = 0 :=
    IsHarmonicDistOn.apply_lapTest_eq_zero QuantumZipper.isOpen_H hT₀ (show U ≤ upperHalfPlaneOpens from hUH)
      hUH f
  have e : ∀ χ : TestOn upperHalfPlaneOpens, ∀ ω,
      Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) =
        Complex.exp (Complex.I * (h ω χ : ℂ)) * Complex.exp (-(Complex.I * (T₀ χ : ℂ))) := by
    intro χ ω
    rw [← Complex.exp_add]
    congr 1
    simp only [sub_apply]
    push_cast
    ring
  have hT : T₀ (lapTest U f + Ξ) = T₀ Ξ := by rw [map_add, h0, zero_add]
  simp_rw [e]
  rw [integral_mul_const, integral_mul_const, hid, hT]
  ring

end Ref

/-! ### The safe events of the reference at a fixed time -/

section Safe

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω₀ : Type*} [mΩ₀ : MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}
  {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ}
  {ζ₀ : Ω₀ → ℝ≥0∞}

/-- The safe events of the reference at `s` for `C`: events of the driving filtration at `s` on which, almost surely,
`s < ζ₀` and `C` avoids the hull `K̂_s`. -/
def refSafeGens (P₀ : Measure Ω₀) (hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀) (C : Set ℂ) (s : ℝ≥0) :
    Set (Set Ω₀) :=
  {D | MeasurableSet[drivingFiltration P₀ hX₀ s] D ∧ ∀ᵐ ω ∂P₀, ω ∈ D →
    (s : ℝ≥0∞) < ζ₀ ω ∧ Disjoint C (fwdHull (fun r : ℝ => W₀ r.toNNReal ω) (s : ℝ))}

theorem isPiSystem_refSafeGens (hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀) (C : Set ℂ) (s : ℝ≥0) :
    IsPiSystem (refSafeGens P₀ hX₀ C s) := by
  rintro D₁ ⟨hD₁, h₁⟩ D₂ ⟨hD₂, -⟩ -
  exact ⟨hD₁.inter hD₂, h₁.mono fun ω h hω => h hω.1⟩

/-- **The projection identity of a family-local reference on its safe σ-algebra at `s`.** -/
theorem setIntegral_lapTest_refSafe [IsProbabilityMeasure P₀]
    (hEv : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀)
    (hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀) {h₀ : Ω₀ → DistOn upperHalfPlaneOpens} (hh₀ : Measurable h₀)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    (hfam : IsFamilyLocal P₀ 𝓕₀ W₀ ζ₀ fun ω => h₀ ω - T₀)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) {U : TopologicalSpace.Opens ℂ} (hUC : (U : Set ℂ) ⊆ C)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hGG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens (fun ω => h₀ ω - T₀) (fun ω => G (h₀ ω - T₀)) P₀)
    (s : ℝ≥0) (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) {D : Set Ω₀}
    (hD : MeasurableSet[MeasurableSpace.generateFrom (refSafeGens P₀ hX₀ C s)] D) :
    ∫ ω in D, Complex.exp (Complex.I * ((h₀ ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂P₀ =
      Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * ((h₀ ω - T₀) Ξ : ℂ)) ∂P₀ := by
  have hUH : (U : Set ℂ) ⊆ H := hUC.trans hCH
  have hXm : Measurable fun ω => h₀ ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hh₀
  have hle := Ito.drivingFiltration_le_usualAugmentation hEv hX₀
  refine setIntegral_lapTest_of_generateFrom (X := fun ω => h₀ ω - T₀) hXm f Ξ
    (isPiSystem_refSafeGens hX₀ C s) (fun D hD => (drivingFiltration P₀ hX₀).le s _ hD.1)
    (LocalExt.integral_lapTest_eq_of_isMarkovDecomposition hXm hUH hGG hd f Ξ) ?_ hD
  rintro D' ⟨hD'm, hD'safe⟩
  refine setIntegral_lapTest_sub_harmonic hT₀ hUH f Ξ ?_
  exact Exist.Param12.setIntegral_projIndep_of_isFamilyLocal (fun ψ => (measurable_distOn_apply ψ).comp hh₀) hT₀
    hfam hC hCH U hUC (hle s _ hD'm) hD'safe f Ξ

end Safe

end Aux54

end Restart

end InteractingSLE
