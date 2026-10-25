import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S8Budget
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S9
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations




 























set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9

open LQGMetric (DistC addConst circleAvg)

 

 
theorem normalizedGFF_id_map' {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    IsNormalizedWholePlaneGFF (id : DistC → DistC) (P.map h) := by
  have hold := isNormalizedWholePlaneGFF_iff_old.mp hh
  apply isNormalizedWholePlaneGFF_iff_old.mpr
  refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hh.1, ?_⟩
  have hset : MeasurableSet {g : DistC | circleAvg g 1 0 = 0} :=
    measurableSet_eq_fun (LQGMetric.measurable_circleAvg_left 1 0) measurable_const
  exact (ae_map_iff hh.1.measurable.aemeasurable hset).2 hold.2

 


theorem centre_failure_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (μ : Measure DistC)
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ) (z : ℂ) (S : Set DistC) :
    P {ω | addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z) ∈ S} ≤ μ S := by
  set τ : Ω → DistC := fun ω => addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)
    with hτdef
  have hτ : IsNormalizedWholePlaneGFF τ P := normalized_translate_sub_circleAvg hh z
  have hlaw : P.map τ = μ := by
    rw [hτdef, map_normalized_translate_sub_circleAvg hh z,
      map_eq_of_candidate_normalized hh hμ, Measure.map_id]
  calc P {ω | τ ω ∈ S} = P (τ ⁻¹' S) := rfl
    _ ≤ (P.map τ) S := Measure.le_map_apply hτ.1.measurable.aemeasurable S
    _ = μ S := by rw [hlaw]

 
theorem exists_s9_budget_centres (μ : Measure DistC)
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (pbar : Ioo (0 : ℝ) 1) (Emax : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Objects.CorrectedEvent.Constants, ∀ T : Objects.CorrectedEvent.TubeData,
      LQGMetric.gradEnergy T.bump ≤ Emax → A ≤ C.A_RN →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ z : ℂ,
          P {ω | ¬ Objects.CorrectedEvent.S9 C T (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z))} ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨A, hA0, hA⟩ := exists_s9_budget μ hμ pbar Emax
  refine ⟨A, hA0, fun C T hE hAC Ω _ P h hh z => ?_⟩
  exact (centre_failure_le P h hh μ hμ z {g | ¬ Objects.CorrectedEvent.S9 C T g}).trans (hA C T hE hAC)

 
theorem exists_s7_budget_centres (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (pbar : Ioo (0 : ℝ) 1) (𝒩 : Finset (ℝ × Finset ℂ)) (h𝒩 : ∀ s ∈ 𝒩, 0 < s.1) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Objects.CorrectedEvent.Constants, ∀ T : Objects.CorrectedEvent.TubeData, C.ξ = ξ → C.Q = Q →
      (∃ s ∈ 𝒩, T.netRadius = s.1 * C.r ∧
        T.netSites = s.2.image (fun x => (C.r : ℂ) * x)) →
      A ≤ C.A_internal →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ z : ℂ,
          P {ω | ¬ Objects.CorrectedEvent.S7 C T
              (D (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)))
              (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z))} ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨A, hA0, hA⟩ := exists_s7_budget μ hμ ξ Q D hD pbar 𝒩 h𝒩
  refine ⟨A, hA0, fun C T hξ hQ hnet hAC Ω _ P h hh z => ?_⟩
  exact (centre_failure_le P h hh μ hμ z {g | ¬ Objects.CorrectedEvent.S7 C T (D g) g}).trans
    (hA C T hξ hQ hnet hAC)

 
theorem exists_s8_budget_centres (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (pbar : Ioo (0 : ℝ) 1) (lam Aloc ρ Aendpt Amax : ℝ) (hlam : 0 < lam) (hAendpt : 0 < Aendpt) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ C : Objects.CorrectedEvent.Constants, ∀ T : Objects.CorrectedEvent.TubeData, Objects.CorrectedEvent.DataMatch C T →
      C.ξ = ξ → C.Q = Q → C.lamConst = lam → C.A_loc = Aloc → C.ρ = ρ →
      C.A_endpt = Aendpt → C.A_max = Amax → C.A_sup ≤ A₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ z : ℂ,
          P {ω | ¬ Objects.CorrectedEvent.S8 C T
              (D (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)))} ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨A₀, hA0, hA⟩ :=
    exists_s8_budget μ hμ ξ Q D hD pbar lam Aloc ρ Aendpt Amax hlam hAendpt
  refine ⟨A₀, hA0, fun C T hData hξ hQ h1 h2 h3 h4 h5 h6 Ω _ P h hh z => ?_⟩
  exact (centre_failure_le P h hh μ hμ z {g | ¬ Objects.CorrectedEvent.S8 C T (D g)}).trans
    (hA C T hData hξ hQ h1 h2 h3 h4 h5 h6)

 

 
theorem measurable_ambientAcross_comp {D : DistC → LSCMetric} (hD : Measurable D) (w : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Measurable fun g => Objects.CorrectedEvent.ambientAcross (D g) w a b := by
  have heq : (fun g => Objects.CorrectedEvent.ambientAcross (D g) w a b) =
      fun g => acrossDist (D g) ⟨(w, a, b), ha, hab⟩ := by
    funext g
    exact ambientAcross_eq_acrossDist (D g) w ha hab
  rw [heq]
  exact (SupercriticalLQGUniqueness.measurable_acrossDist _).comp hD

 
def supGoodB (C : Objects.CorrectedEvent.Constants) (d : LSCMetric) (c : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell) (k : ℕ) :
    Prop :=
  Objects.CorrectedEvent.around d (Objects.CorrectedEvent.cellCenter c s l) ((2 + 1 / 20) * Objects.CorrectedEvent.supRadius C k)
      ((3 - 1 / 20) * Objects.CorrectedEvent.supRadius C k) < ⊤ ∧
    0 < Objects.CorrectedEvent.ambientAcross d (Objects.CorrectedEvent.cellCenter c s l) ((1 + 1 / 20) * Objects.CorrectedEvent.supRadius C k)
      ((2 - 1 / 20) * Objects.CorrectedEvent.supRadius C k) ∧
    Objects.CorrectedEvent.ambientAcross d (Objects.CorrectedEvent.cellCenter c s l) ((1 + 1 / 20) * Objects.CorrectedEvent.supRadius C k)
      ((2 - 1 / 20) * Objects.CorrectedEvent.supRadius C k) < ⊤ ∧
    Objects.CorrectedEvent.around d (Objects.CorrectedEvent.cellCenter c s l) ((2 + 1 / 20) * Objects.CorrectedEvent.supRadius C k)
        ((3 - 1 / 20) * Objects.CorrectedEvent.supRadius C k) ≤
      ENNReal.ofReal (1 / 2 * Real.exp (-C.ξ * C.A_max)) *
        Objects.CorrectedEvent.ambientAcross d (Objects.CorrectedEvent.cellCenter c s l) ((1 + 1 / 20) * Objects.CorrectedEvent.supRadius C k)
          ((2 - 1 / 20) * Objects.CorrectedEvent.supRadius C k)

theorem supRadius_pos (C : Objects.CorrectedEvent.Constants) (k : ℕ) : 0 < Objects.CorrectedEvent.supRadius C k := by
  rw [supRadius_eq]
  have := C.supPos
  have := C.rPos
  positivity

 
theorem supGood_iff_supGoodB (C : Objects.CorrectedEvent.Constants) (d : LSCMetric) (hB : BiLipschitz.Barrier.Barrier d)
    (hL : d.IsLengthSpace) (c : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell) (k : ℕ) :
    Objects.CorrectedEvent.supGood C d c s l k ↔ supGoodB C d c s l k := by
  have hR := supRadius_pos C k
  have hacr : Objects.CorrectedEvent.acr d (Objects.CorrectedEvent.cellCenter c s l) ((1 + 1 / 20) * Objects.CorrectedEvent.supRadius C k)
      ((2 - 1 / 20) * Objects.CorrectedEvent.supRadius C k) =
      Objects.CorrectedEvent.ambientAcross d (Objects.CorrectedEvent.cellCenter c s l) ((1 + 1 / 20) * Objects.CorrectedEvent.supRadius C k)
        ((2 - 1 / 20) * Objects.CorrectedEvent.supRadius C k) :=
    le_antisymm (acr_le_ambientAcross_of_barrier d hB hL _ (by nlinarith))
      (Objects.ProbabilityS1S2.ambientAcross_le_acr d _ _ _)
  unfold Objects.CorrectedEvent.supGood supGoodB
  simp only
  rw [hacr]

theorem measurableSet_supGoodB {D : DistC → LSCMetric} (hD : Measurable D)
    (C : Objects.CorrectedEvent.Constants) (c : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell) (k : ℕ) :
    MeasurableSet {g : DistC | supGoodB C (D g) c s l k} := by
  have hR := supRadius_pos C k
  have ho : Measurable fun g => Objects.CorrectedEvent.around (D g) (Objects.CorrectedEvent.cellCenter c s l)
      ((2 + 1 / 20) * Objects.CorrectedEvent.supRadius C k) ((3 - 1 / 20) * Objects.CorrectedEvent.supRadius C k) :=
    measurable_around_comp hD _ (by positivity) (by nlinarith)
  have hi : Measurable fun g => Objects.CorrectedEvent.ambientAcross (D g) (Objects.CorrectedEvent.cellCenter c s l)
      ((1 + 1 / 20) * Objects.CorrectedEvent.supRadius C k) ((2 - 1 / 20) * Objects.CorrectedEvent.supRadius C k) :=
    measurable_ambientAcross_comp hD _ (by positivity) (by nlinarith)
  simp only [supGoodB, Set.ofPred_and]
  exact (measurableSet_lt ho measurable_const).inter ((measurableSet_lt measurable_const hi).inter
    ((measurableSet_lt hi measurable_const).inter (measurableSet_le ho (measurable_const.mul hi))))

 
def badLengthB (C : Objects.CorrectedEvent.Constants) (d : LSCMetric) (c : ℂ) (s : ℝ) : ℝ := by
  classical
  exact ∑ l ∈ Finset.range (Objects.CorrectedEvent.numCells C s),
    if (∀ k ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C), ¬ supGoodB C d c s (Objects.CorrectedEvent.circleCell C s l) k) then
      s * ((Objects.CorrectedEvent.circleCell C s l).hi - (Objects.CorrectedEvent.circleCell C s l).lo) else 0

theorem measurable_badLengthB {D : DistC → LSCMetric} (hD : Measurable D)
    (C : Objects.CorrectedEvent.Constants) (c : ℂ) (s : ℝ) :
    Measurable fun g => badLengthB C (D g) c s := by
  classical
  unfold badLengthB
  refine Finset.measurable_sum _ fun l _ => ?_
  have hset : MeasurableSet {g : DistC | ∀ k ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C),
      ¬ supGoodB C (D g) c s (Objects.CorrectedEvent.circleCell C s l) k} := by
    have heq : {g : DistC | ∀ k ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C),
        ¬ supGoodB C (D g) c s (Objects.CorrectedEvent.circleCell C s l) k} =
        ⋂ k ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C),
          {g : DistC | supGoodB C (D g) c s (Objects.CorrectedEvent.circleCell C s l) k}ᶜ := by
      ext g
      simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff]
    rw [heq]
    exact Finset.measurableSet_biInter _ fun k _ =>
      (measurableSet_supGoodB hD C c s (Objects.CorrectedEvent.circleCell C s l) k).compl
  exact Measurable.ite hset measurable_const measurable_const

theorem badLength_eq_badLengthB (C : Objects.CorrectedEvent.Constants) (d : LSCMetric) (hB : BiLipschitz.Barrier.Barrier d)
    (hL : d.IsLengthSpace) (c : ℂ) (s : ℝ) :
    Objects.CorrectedEvent.badLength C d c s = badLengthB C d c s := by
  classical
  unfold Objects.CorrectedEvent.badLength badLengthB Objects.CorrectedEvent.badCell
  refine Finset.sum_congr rfl fun l _ => ?_
  have hiff : (∀ k ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C), ¬ Objects.CorrectedEvent.supGood C d c s (Objects.CorrectedEvent.circleCell C s l) k)
      ↔ (∀ k ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C), ¬ supGoodB C d c s (Objects.CorrectedEvent.circleCell C s l) k) := by
    refine forall₂_congr fun k _ => ?_
    rw [supGood_iff_supGoodB C d hB hL]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl

 

theorem nullMeasurableSet_S8 (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) :
    NullMeasurableSet {g : DistC | Objects.CorrectedEvent.S8 C T (D g)} μ := by
  set t := C.lamConst * C.A_endpt * C.ρ * C.r with htdef
  set SB : Set DistC := ⋂ k : Fin T.K,
    ({g | badLengthB C (D g) (Objects.CorrectedEvent.innerCenter T k) T.blockRadius ≤ t} ∩
      {g | badLengthB C (D g) (Objects.CorrectedEvent.outerCenter T k) T.blockRadius ≤ t}) with hSBdef
  have hSB : MeasurableSet SB :=
    MeasurableSet.iInter fun k =>
      (measurableSet_le (measurable_badLengthB hD.measurable C _ _) measurable_const).inter
        (measurableSet_le (measurable_badLengthB hD.measurable C _ _) measurable_const)
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hae : {g : DistC | Objects.CorrectedEvent.S8 C T (D g)} =ᵐ[μ] SB := by
    filter_upwards [BiLipschitz.Barrier.ae_barrier hD hQ μ id hμ,
      hD.length μ id (LQGMetric.GM.detGFFPlusCont hμ.1)] with g hB hL
    have hB' : BiLipschitz.Barrier.Barrier (D g) := hB
    have hL' : (D g).IsLengthSpace := hL
    simp only [Objects.CorrectedEvent.S8, hSBdef, mem_iInter, mem_inter_iff, mem_ofPred_eq, eq_iff_iff,
      badLength_eq_badLengthB C (D g) hB' hL']
    exact Iff.rfl
  exact hSB.nullMeasurableSet.congr hae.symm


end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9
