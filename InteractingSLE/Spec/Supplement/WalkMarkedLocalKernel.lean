/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkUnionLaw
import InteractingSLE.Spec.Supplement.KernelTower
import InteractingSLE.Spec.Exist.Param12BorelTest

/-!
# The Markov decomposition survives conditioning on the marks of a marked local set

Packet PROVE-T14-WALKLAW2 (Part D.2 of the follow-up note, `source/external/AstraIG1/ig1_followup_a_e_audited.txt`
L771–L832: "Given the old marked datum, a new ordinary stage is the canonical finite-word flow of that conditional
field"). The step from one stage of a boundary walk to the next works under the regular conditional law given the
retained past. For the new piece to be read as a local set of the field *under that conditional law*, the Markov
decomposition `h = G h + (h − G h)` along an open `U ⊆ ℍ` that the old history avoids must still be a Markov
decomposition there. This file proves it for any history-marked local set:

* `measurable_hitting_of_avoid`: a random set whose avoidance events are events of `𝒢` is hitting-measurable;
* `ae_condExpKernel_inter_eq_mul` (generic): if `S` is independent of every event `C ∩ F ∩ T` (`F ∈ 𝒢`), then almost
  surely on `C` the conditional kernel given `𝒢` factors `κ(S ∩ T) = P(S) κ(T)`;
* **`ae_isMarkovDecomposition_condExpKernel`**: for a history-marked local set `A` with marks `𝒢` (avoidance events
  in `𝒢`) of a zero-boundary GFF `h`, a Markov decomposition `G` along `U ⊆ ℍ`, and almost every `ω₀` with
  `A ω₀ ∩ U = ∅`, `G` is still a Markov decomposition of `h` under `condExpKernel P 𝒢 ω₀`, and `G h` keeps its law.

Proof: the history-marked criterion gives the independence of `G h` from `σ(h − G h)` together with the marked
avoidance events (`WholeField.indep_markov_histAvoidSigma`); on the avoidance event this is the conditional
independence given `𝒢`; a countable generating π-system of the standard Borel space `𝒟'(ℍ)` turns the countably many
kernel identities into the product form of the joint conditional law of `(G h, h − G h)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

open LocalSets

section Kernel

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- A random set whose avoidance events of open subsets of `ℍ` are events of `𝒢 ≤ mΩ` is hitting-measurable. -/
theorem measurable_hitting_of_avoid {A : Ω → Set ℂ} (h𝒢 : 𝒢 ≤ mΩ)
    (hA : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝒢] {ω | Disjoint (A ω) U}) :
    Measurable[mΩ, hittingSigma] A := by
  refine @measurable_generateFrom Ω (Set ℂ) mΩ _ _ ?_
  rintro _ ⟨V, hVo, hVH, rfl⟩
  have e : A ⁻¹' {B | (B ∩ V).Nonempty} = {ω | Disjoint (A ω) ((⟨V, hVo⟩ : Opens ℂ) : Set ℂ)}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
    rfl
  rw [e]
  exact (h𝒢 _ (hA ⟨V, hVo⟩ hVH)).compl

/-- **Conditional factorization on an event of `𝒢`.** If the event `S` is independent of every `C ∩ F ∩ T` with
`F ∈ 𝒢` (`C ∈ 𝒢`), then almost surely on `C` the regular conditional law given `𝒢` factors as
`κ(S ∩ T) = P(S) κ(T)`. -/
theorem ae_condExpKernel_inter_eq_mul (h𝒢 : 𝒢 ≤ mΩ) {C : Set Ω} (hC : MeasurableSet[𝒢] C) {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hind : ∀ F, MeasurableSet[𝒢] F → P (S ∩ (C ∩ F ∩ T)) = P S * P (C ∩ F ∩ T)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ C → condExpKernel P 𝒢 ω₀ (S ∩ T) = P S * condExpKernel P 𝒢 ω₀ T := by
  have hCm : MeasurableSet C := h𝒢 _ hC
  set f₁ : Ω → ℝ≥0∞ := fun ω₀ => condExpKernel P 𝒢 ω₀ (C ∩ (S ∩ T)) with hf₁
  set f₂ : Ω → ℝ≥0∞ := fun ω₀ => P S * condExpKernel P 𝒢 ω₀ (C ∩ T) with hf₂
  have hf₁m : Measurable[𝒢] f₁ := measurable_condExpKernel (hCm.inter (hS.inter hT))
  have hf₂m : Measurable[𝒢] f₂ := (measurable_condExpKernel (hCm.inter hT)).const_mul _
  have hint : ∀ F, MeasurableSet[𝒢] F → ∫⁻ ω in F, f₁ ω ∂(P.trim h𝒢) = ∫⁻ ω in F, f₂ ω ∂(P.trim h𝒢) := by
    intro F hF
    rw [setLIntegral_trim h𝒢 hf₁m hF, setLIntegral_trim h𝒢 hf₂m hF, hf₁, hf₂,
      KernelTower.setLIntegral_condExpKernel h𝒢 hF (hCm.inter (hS.inter hT)),
      lintegral_const_mul _ ((measurable_condExpKernel (hCm.inter hT)).mono h𝒢 le_rfl),
      KernelTower.setLIntegral_condExpKernel h𝒢 hF (hCm.inter hT)]
    have e1 : F ∩ (C ∩ (S ∩ T)) = S ∩ (C ∩ F ∩ T) := by
      ext ω; simp only [mem_inter_iff]; tauto
    have e2 : F ∩ (C ∩ T) = C ∩ F ∩ T := by
      ext ω; simp only [mem_inter_iff]; tauto
    rw [e1, e2, hind F hF]
  have hae : f₁ =ᵐ[P.trim h𝒢] f₂ :=
    ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hf₁m hf₂m fun F hF _ => hint F hF
  have hae' : f₁ =ᵐ[P] f₂ := ae_eq_of_ae_eq_trim hae
  filter_upwards [hae', KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hC] with ω₀ h1 h2 hω₀
  have hc : condExpKernel P 𝒢 ω₀ Cᶜ = 0 := h2.1 hω₀
  have e3 : condExpKernel P 𝒢 ω₀ (C ∩ (S ∩ T)) = condExpKernel P 𝒢 ω₀ (S ∩ T) := by
    rw [inter_comm]; exact measure_inter_conull hc
  have e4 : condExpKernel P 𝒢 ω₀ (C ∩ T) = condExpKernel P 𝒢 ω₀ T := by
    rw [inter_comm]; exact measure_inter_conull hc
  have := h1
  simp only [hf₁, hf₂] at this
  rw [← e3, ← e4]
  exact this

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- A countable π-system of measurable sets of `𝒟'(ℍ)` that contains `univ` and generates its σ-algebra. -/
theorem exists_countable_isPiSystem_distOn :
    ∃ D : Set (Set (DistOn upperHalfPlaneOpens)), D.Countable ∧ IsPiSystem D ∧ univ ∈ D ∧
      (inferInstance : MeasurableSpace (DistOn upperHalfPlaneOpens)) = MeasurableSpace.generateFrom D := by
  have : MeasurableSpace.CountablyGenerated (DistOn upperHalfPlaneOpens) := by
    let := upgradeStandardBorel (DistOn upperHalfPlaneOpens); infer_instance
  obtain ⟨Cp, hc, hpi, hgen⟩ := Exist.Param12.exists_countable_isPiSystem_generate (DistOn upperHalfPlaneOpens)
  refine ⟨insert univ Cp, hc.insert univ, hpi.insert_univ, mem_insert _ _, ?_⟩
  rw [MeasurableSpace.generateFrom_insert_univ]
  exact hgen

/-- **The Markov decomposition survives conditioning on the marks, on the avoidance event.** Let `A` satisfy the
history-marked avoidance criterion for the marks `𝒢` (its avoidance events being events of `𝒢`) with respect to a
zero-boundary GFF `h` on `ℍ`, and let `G` give the Markov decomposition of `h` along an open `U ⊆ ℍ`. Then for
almost every `ω₀` with `A ω₀ ∩ U = ∅`, `G` gives the Markov decomposition of `h` under the regular conditional law
given `𝒢` at `ω₀`, and the law of `G h` there is its law under `P`. -/
theorem ae_isMarkovDecomposition_condExpKernel {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) (h𝒢 : 𝒢 ≤ mΩ) {A : Ω → Set ℂ}
    (hA : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝒢] {ω | Disjoint (A ω) U})
    (hloc : WholeField.IsHistoryAvoidanceLocal 𝒢 A h P) {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) :
    ∀ᵐ ω₀ ∂P, Disjoint (A ω₀) U →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) (condExpKernel P 𝒢 ω₀) ∧
        (condExpKernel P 𝒢 ω₀).map (fun ω => G (h ω)) = P.map (fun ω => G (h ω)) := by
  have hhm := hh.measurable
  set Z : Ω → DistOn upperHalfPlaneOpens := fun ω => G (h ω) with hZdef
  set X : Ω → DistOn upperHalfPlaneOpens := fun ω => markovCompl G (h ω) with hXdef
  have hZm : Measurable Z := hG.comp hhm
  have hXm : Measurable X := (measurable_markovCompl hG).comp hhm
  have hAm : Measurable[mΩ, hittingSigma] A := measurable_hitting_of_avoid h𝒢 hA
  have hind := WholeField.indep_markov_histAvoidSigma hh hAm h𝒢 hloc hG hd
  set C : Set Ω := {ω | Disjoint (A ω) U} with hCdef
  have hC : MeasurableSet[𝒢] C := hA U hUH
  -- the conditional factorization for each rectangle
  have key : ∀ S T : Set (DistOn upperHalfPlaneOpens), MeasurableSet S → MeasurableSet T →
      ∀ᵐ ω₀ ∂P, ω₀ ∈ C →
        condExpKernel P 𝒢 ω₀ (Z ⁻¹' S ∩ X ⁻¹' T) = P (Z ⁻¹' S) * condExpKernel P 𝒢 ω₀ (X ⁻¹' T) := by
    intro S T hS hT
    refine ae_condExpKernel_inter_eq_mul h𝒢 hC (hZm hS) (hXm hT) fun F hF => ?_
    refine (Indep_iff _ _ _).1 hind _ _ ⟨S, hS, rfl⟩ ?_
    have h1 : MeasurableSet[WholeField.histAvoidSigma A 𝒢 U] (C ∩ F) :=
      MeasurableSpace.measurableSet_generateFrom ⟨U, F, U.isOpen, subset_rfl, hUH, hF, rfl⟩
    have h2 : MeasurableSet[MeasurableSpace.comap X inferInstance] (X ⁻¹' T) := ⟨T, hT, rfl⟩
    exact ((le_sup_right : WholeField.histAvoidSigma A 𝒢 U ≤ _) _ h1).inter
      ((le_sup_left : MeasurableSpace.comap X inferInstance ≤ _) _ h2)
  obtain ⟨D, hDc, hDpi, hDuniv, hDgen⟩ := exists_countable_isPiSystem_distOn
  have hDm : ∀ S ∈ D, MeasurableSet S := fun S hS => by
    have := MeasurableSpace.measurableSet_generateFrom (s := D) hS
    rw [← hDgen] at this
    exact this
  have hall : ∀ᵐ ω₀ ∂P, ∀ p ∈ D ×ˢ D, ω₀ ∈ C →
      condExpKernel P 𝒢 ω₀ (Z ⁻¹' p.1 ∩ X ⁻¹' p.2) = P (Z ⁻¹' p.1) * condExpKernel P 𝒢 ω₀ (X ⁻¹' p.2) :=
    (ae_ball_iff (hDc.prod hDc)).2 fun p hp => key p.1 p.2 (hDm _ hp.1) (hDm _ hp.2)
  have houts := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hd.ae_restrictDist_outside_eq_zero
  have hharm := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hd.ae_harmonic
  filter_upwards [hall, houts, hharm] with ω₀ hall' houts' hharm' hω₀
  set ν := condExpKernel P 𝒢 ω₀ with hν
  -- the joint law under the kernel is the product of the unconditional law of `Z` and the kernel law of `X`
  have hspan : IsCountablySpanning D := ⟨fun _ => univ, fun _ => hDuniv, iUnion_const univ⟩
  have hprodgen : (inferInstance : MeasurableSpace (DistOn upperHalfPlaneOpens × DistOn upperHalfPlaneOpens)) =
      MeasurableSpace.generateFrom (image2 (· ×ˢ ·) D D) := by
    have := generateFrom_prod_eq hspan hspan
    rw [← hDgen] at this
    exact this
  have hprod : ν.map (fun ω => (Z ω, X ω)) = (P.map Z).prod (ν.map X) := by
    refine ext_of_generate_finite _ hprodgen (hDpi.prod hDpi) ?_ ?_
    · rintro _ ⟨S, hS, T, hT, rfl⟩
      rw [Measure.map_apply (hZm.prodMk hXm) ((hDm S hS).prod (hDm T hT)), Measure.prod_prod,
        Measure.map_apply hZm (hDm S hS), Measure.map_apply hXm (hDm T hT), mk_preimage_prod]
      exact hall' (S, T) ⟨hS, hT⟩ hω₀
    · simp
  have hlawZ : ν.map Z = P.map Z := by
    have e := congrArg (fun μ : Measure (DistOn upperHalfPlaneOpens × DistOn upperHalfPlaneOpens) =>
      μ.map Prod.fst) hprod
    simp only [Measure.map_map measurable_fst (hZm.prodMk hXm), Measure.map_fst_prod] at e
    rw [Measure.map_apply hXm MeasurableSet.univ, preimage_univ, measure_univ, one_smul] at e
    exact e
  have hindν : IndepFun Z X ν := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hZm.aemeasurable hXm.aemeasurable, hlawZ]
    exact hprod
  have hext : GFF.IsZBGFFExtOn U upperHalfPlaneOpens Z ν :=
    GFF.IsZBGFFExtOn.of_map_eq (X := Z) (X' := Z) hZm hZm hlawZ.symm (G := id) measurable_id
      hd.isZBGFFExtOn
  refine ⟨⟨hext, hext.isZeroBoundaryGFF_restrictDist hUH, houts', hindν, hharm'⟩, hlawZ⟩

end Kernel

end WalkLaw

end Theorem14

end InteractingSLE
