import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51Iface
import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.RadiusFromRaw
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RegAllCentre
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5.S5Budget
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.S6
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.Centre
import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.NineClauses




 















set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

theorem null_diff_regularizedTarget {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (hQ : 0 < Q)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus) (hPlusFin : cPlus < ⊤)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (T : Objects.CorrectedEvent.TubeData) (E : Set DistC) :
    (P.map h) (E \ Objects.RadiusResidual.regularizedTarget ξ D D' T cPlus E) = 0 := by
  have hreg : ∀ᵐ g ∂(P.map h), Objects.Producer.LocalGood ξ D D' (range (Objects.CorrectedEvent.site T)) ∅ g :=
    Objects.Producer.ae_localGood hGFF hD hD' hQ (Set.countable_range _) Set.countable_empty
  have hcomp := Objects.RadiusResidual.ae_optimal_upper_field P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hPlusPos hPlusFin hMinus hPlus
  have hall : ∀ᵐ g ∂(P.map h), g ∉ E \ Objects.RadiusResidual.regularizedTarget ξ D D' T cPlus E := by
    filter_upwards [hreg, hcomp] with g hg hc
    rintro ⟨hgE, hgT⟩
    exact hgT ⟨⟨hgE, hg⟩, hc⟩
  exact measure_eq_zero_iff_ae_notMem.2 hall

 

theorem radiusInputs_of_selection {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus) (hQ : 0 < Q) (hcm : 0 < cMinus) (hcp : cPlus < ⊤)
    {a : Set.Ioo (3 / 4 : ℝ) 1} {p : Set.Ioo (0 : ℝ) 1} (pbar : Set.Ioo (0 : ℝ) 1)
    (t : Objects.Density.T58Table ξ Q cMinus.toReal cPlus.toReal a p pbar) (r : Set.Ioi (0 : ℝ))
    (x : ℂ × ℝ × ℝ × ℝ) (hx : x ∈ blockFamily (t.lam * Objects.Density.endptScale t.m) t.m)
    (ρ₁ : ℝ) (X₁ : Finset ℂ)
    (hmesh : MeshProps ((familyParams t.lam (Objects.Density.endptScale t.m) a (Objects.Density.locScale t.K_sh)
      t.ρ x).tube 1) 1 t.A_set ρ₁ X₁)
    (pr : ℝ)
    (hT51 : ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), C.lamConst = t.lam →
      T.rho * T.r = t.ρ * r → T.alpha = a → T.orientation = x.1 → T.psiU = x.2.2.1 →
      T.psiV = x.2.2.2 → T.blockRadius = x.2.1 * (t.ρ * r) →
      ENNReal.ofReal pr ≤ (P.map h)
        {g | Objects.Excursions.blockRaw C T t.K_sh (Objects.Density.Cmid0 cMinus.toReal cPlus.toReal) D D' g})
    (cReg a₀ A₀ : ℝ) (k0 : ℕ)
    (hS123 : ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ↑ξ → C.Q = Q → C.A_across ≤ a₀ → A₀ ≤ C.A_around →
      C.c_reg ≤ cReg → k0 ≤ C.k0 → ∀ z : ℂ,
        (P.map h) (Objects.Producer.centreTarget {g | ¬Objects.CorrectedEvent.S1 C (D g) g} z) ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) ∧
          (P.map h) (Objects.Producer.centreTarget {g | ¬Objects.CorrectedEvent.S2 C (D g) g} z) ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) ∧
          (P.map h) (Objects.Producer.centreTarget {g | ¬Objects.CorrectedEvent.S3 C (D g)} z) ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10))
    (ht_reg : t.c_reg ≤ cReg) (ht_across : t.A_across ≤ a₀) (ht_around : A₀ ≤ t.A_around)
    (ht_k0 : k0 ≤ t.k0)
    (hS4 : ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), Objects.CorrectedEvent.DataMatch C T →
      C.A_loc = 3 * 8 ^ t.K_sh → C.A_endpt ≤ 1 → 0 ≤ C.K_ann → C.lamConst ≤ 1 / 100 →
      C.lamConst * cPlus.toReal / cMinus.toReal < 1 → C.ρ ≤ C.lamConst / C.A_loc →
      C.lamConst = t.lam → C.ρ = t.ρ → C.A_sp = t.A_sp →
      ENNReal.ofReal pr ≤ (P.map h)
        {g | Objects.Excursions.blockRaw C T t.K_sh (Objects.Density.Cmid0 cMinus.toReal cPlus.toReal) D D' g} →
      (P.map h) {g | ¬ Objects.CorrectedEvent.S4 C T (fun z =>
        Objects.Excursions.blockEvent C T t.K_sh (Objects.Density.Cmid0 cMinus.toReal cPlus.toReal) D D' z g)} ≤
        ENNReal.ofReal ((1 - (pbar : ℝ)) / 10))
    (a5 : ℝ) (hS5 : ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ↑ξ → C.Q = Q → C.A_nar < a5 →
      (P.map h) {g | ¬Objects.CorrectedEvent.S5 C (D g)} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10))
    (ht_5 : t.A_nar < a5)
    (K6 : ℝ) (hS6 : ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ↑ξ → C.Q = Q → K6 * C.A_nar ≤ C.lamConst →
      (P.map h) {g | ¬Objects.CorrectedEvent.S6 C (D g) g} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10))
    (ht_6 : K6 * t.A_nar ≤ t.lam)
    (𝒩 : Finset (ℝ × Finset ℂ)) (h𝒩 : (ρ₁, X₁) ∈ 𝒩) (A₇ : ℝ)
    (hS7 : ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), C.ξ = ↑ξ → C.Q = Q →
      (∃ s ∈ 𝒩, T.netRadius = s.1 * C.r ∧
        T.netSites = Finset.image (fun x => (C.r : ℂ) * x) s.2) → A₇ ≤ C.A_internal →
      (P.map h) {g | ¬Objects.CorrectedEvent.S7 C T (D g) g} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10))
    (ht_7 : A₇ ≤ t.A_internal)
    (A₈ : ℝ) (hS8 : ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), Objects.CorrectedEvent.DataMatch C T →
      C.ξ = ↑ξ → C.Q = Q → C.lamConst = t.lam → C.A_loc = Objects.Density.locScale t.K_sh → C.ρ = t.ρ →
      C.A_endpt = Objects.Density.endptScale t.m → C.A_max = t.A_max → C.A_sup ≤ A₈ →
      (P.map h) {g | ¬Objects.CorrectedEvent.S8 C T (D g)} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10))
    (ht_8 : t.A_sup ≤ A₈)
    (hE : familyEnergyBudget t.toT58Stage10 t.A_sup t.E_max) :
    Nonempty (Objects.Producer.RadiusInputs P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) t.params pbar r) := by
  set μ := P.map h with hμdef
  have hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ := Objects.ProbabilityS7S9.normalizedGFF_id_map' P h hGFF
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hGFF.1.measurable.aemeasurable).2 inferInstance
  set C := t.toConstants r with hC
  set Pt := familyParams t.lam (Objects.Density.endptScale t.m) a (Objects.Density.locScale t.K_sh) t.ρ x with hPt
  have S : Objects.TubeMesh.TubeSelection C Pt := familyParams_selection t r hx
  have hSupNar : C.A_sup < C.A_nar := t.sup_lt_set.trans t.set_lt_nar
  have hSmall : 100 * C.A_sup ≤ Pt.sp * Pt.ρ := (S.small hSupNar).1
  have hr : (0 : ℝ) < r := r.2
  set ρ₀ : ℝ := (r : ℝ) * ρ₁ with hρ₀
  set X : Finset ℂ := X₁.image (fun z => ((r : ℝ) : ℂ) * z) with hX
  have hM : MeshProps (Pt.tube C.r) C.r (C.A_set * C.r) ρ₀ X := MeshProps.scale hr hmesh
  have hData : Objects.CorrectedEvent.DataMatch C (Objects.TubeBridge.tubeDataOf C Pt S.good hSmall ρ₀ X) :=
    dataMatch_of_mesh C Pt S hSupNar ρ₀ X hM
  set T := Objects.TubeBridge.tubeDataOf C Pt S.good hSmall ρ₀ X with hT
  set Cm0 : ℝ := Objects.Density.Cmid0 cMinus.toReal cPlus.toReal with hCm0
  set F := Objects.Excursions.blockEvent C T t.K_sh Cm0 D D' with hF
  set E : Set DistC := {g | Objects.CorrectedEvent.correctedEvent C T hData F D D' g} with hE'
  have hcmR : 0 < cMinus.toReal := Objects.Density.toReal_pos_of_pos hcm hcp hstrict
  have hcp0 : 0 < cPlus := hcm.trans hstrict
  
  have hmarg : ENNReal.ofReal pr ≤ μ {g | Objects.Excursions.blockRaw C T t.K_sh Cm0 D D' g} :=
    hT51 C T rfl rfl rfl rfl rfl rfl (by
      change x.2.1 * t.ρ * (r : ℝ) = x.2.1 * (t.ρ * r)
      ring)
  
  have hBlock := aeEventIn_blockRaw_window P h ξ Q D D' hD hD' hGFF cMinus cPlus hcm
    (hstrict.trans hcp) hcp0 hcp hMinus hPlus C T hData t.K_sh Cm0 t.endpt_le_one
    t.Kann_nonneg (by have := t.lam_le_hundredth; change t.lam < 1; linarith)
    t.lam_ratio_lt_one
  have hRe : 3 * (3 * 8 ^ t.K_sh) * (T.rho * T.r) = 3 * C.A_loc * (C.ρ * C.r) := by
    change 3 * (3 * 8 ^ t.K_sh) * (t.ρ * r) = 3 * Objects.Density.locScale t.K_sh * (t.ρ * r)
    unfold Objects.Density.locScale
    ring
  rw [hRe] at hBlock
  have hloc := aeEventIn_correctedEvent μ hμ ξ Q D D' hD C rfl T hData t.K_sh Cm0
    (3 * C.A_loc * (C.ρ * C.r)) (siteBall_subset C T hData (by
      change 3 * Objects.Density.locScale t.K_sh * t.ρ < 1; exact t.ρ_loc)) hBlock t.nar_sixth
    hM.1 (netBall_subset C Pt S.good hSmall ρ₀ X S.widthEq hData)
    (cellBall_subset C T hData t.lam_le t.endpt_le_one t.Kann_nonneg)
    (bump_tsupport_subset C Pt S.good hSmall ρ₀ X S.widthEq)
  obtain ⟨L₀, hL₀m, hL₀e⟩ := hloc
  have hnull : μ (L₀ \ Objects.RadiusResidual.regularizedTarget ξ D D' T cPlus E) = 0 := by
    have h1 : μ (L₀ \ E) = 0 := (ae_eq_set.1 hL₀e).2
    have h2 := null_diff_regularizedTarget P h ξ Q D D' hD hD' hGFF hQ cMinus cPlus hcp0 hcp
      hMinus hPlus T E
    refine measure_mono_null (?_ : L₀ \ Objects.RadiusResidual.regularizedTarget ξ D D' T cPlus E ⊆
      (L₀ \ E) ∪ (E \ Objects.RadiusResidual.regularizedTarget ξ D D' T cPlus E)) (measure_union_null h1 h2)
    intro g ⟨hg1, hg2⟩
    by_cases hgE : g ∈ E
    · exact Or.inr ⟨hgE, hg2⟩
    · exact Or.inl ⟨hg1, hgE⟩
  
  have hS123' := hS123 C rfl rfl ht_across ht_around ht_reg ht_k0 0
  have hcent : ∀ S : Set DistC, MeasurableSet S →
      μ (Objects.Producer.centreTarget S 0) = μ S := fun S hSm =>
    Objects.CentreEvent.measure_centreTarget_eq hGFF S hSm.nullMeasurableSet 0
  have hfail : ∀ i : Fin 9, μ (Objects.RadiusResidual.clauseSet C T F D i)ᶜ ≤
      ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
    intro i
    fin_cases i
    · change μ (Objects.RadiusResidual.clauseSet C T F D 0)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
      have e : (Objects.RadiusResidual.clauseSet C T F D 0)ᶜ = {g | ¬Objects.CorrectedEvent.S1 C (D g) g} := by
        ext g; simp [Objects.RadiusResidual.clauseSet]
      rw [e, ← hcent {g | ¬Objects.CorrectedEvent.S1 C (D g) g} (Objects.ClauseMeasurability.measurableSet_S1 C D hD.1).compl]
      exact hS123'.1
    · change μ (Objects.RadiusResidual.clauseSet C T F D 1)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
      have e : (Objects.RadiusResidual.clauseSet C T F D 1)ᶜ = {g | ¬Objects.CorrectedEvent.S2 C (D g) g} := by
        ext g; simp [Objects.RadiusResidual.clauseSet]
      rw [e, ← hcent {g | ¬Objects.CorrectedEvent.S2 C (D g) g} (Objects.ClauseMeasurability.measurableSet_S2 C D hD.1).compl]
      exact hS123'.2.1
    · change μ (Objects.RadiusResidual.clauseSet C T F D 2)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
      have e : (Objects.RadiusResidual.clauseSet C T F D 2)ᶜ = {g | ¬Objects.CorrectedEvent.S3 C (D g)} := by
        ext g; simp [Objects.RadiusResidual.clauseSet]
      rw [e, ← hcent {g | ¬Objects.CorrectedEvent.S3 C (D g)} (Objects.ClauseMeasurability.measurableSet_S3 C D hD.1).compl]
      exact hS123'.2.2
    · change μ (Objects.RadiusResidual.clauseSet C T F D 3)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
      have e : (Objects.RadiusResidual.clauseSet C T F D 3)ᶜ = {g | ¬Objects.CorrectedEvent.S4 C T (fun z => F z g)} := by
        ext g; simp [Objects.RadiusResidual.clauseSet]
      rw [e]
      exact hS4 C T hData (by change Objects.Density.locScale t.K_sh = _; rfl) t.endpt_le_one t.Kann_nonneg
        t.lam_le_hundredth t.lam_ratio_lt_one t.ρ_loc' rfl rfl rfl hmarg
    · change μ (Objects.RadiusResidual.clauseSet C T F D 4)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
      have e : (Objects.RadiusResidual.clauseSet C T F D 4)ᶜ = {g | ¬Objects.CorrectedEvent.S5 C (D g)} := by
        ext g; simp [Objects.RadiusResidual.clauseSet]
      rw [e]
      exact hS5 C rfl rfl ht_5
    · change μ (Objects.RadiusResidual.clauseSet C T F D 5)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
      have e : (Objects.RadiusResidual.clauseSet C T F D 5)ᶜ = {g | ¬Objects.CorrectedEvent.S6 C (D g) g} := by
        ext g; simp [Objects.RadiusResidual.clauseSet]
      rw [e]
      exact hS6 C rfl rfl ht_6
    · change μ (Objects.RadiusResidual.clauseSet C T F D 6)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
      have e : (Objects.RadiusResidual.clauseSet C T F D 6)ᶜ = {g | ¬Objects.CorrectedEvent.S7 C T (D g) g} := by
        ext g; simp [Objects.RadiusResidual.clauseSet]
      rw [e]
      exact hS7 C T rfl rfl ⟨(ρ₁, X₁), h𝒩, by change (r : ℝ) * ρ₁ = ρ₁ * r; ring, rfl⟩ ht_7
    · change μ (Objects.RadiusResidual.clauseSet C T F D 7)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
      have e : (Objects.RadiusResidual.clauseSet C T F D 7)ᶜ = {g | ¬Objects.CorrectedEvent.S8 C T (D g)} := by
        ext g; simp [Objects.RadiusResidual.clauseSet]
      rw [e]
      exact hS8 C T hData rfl rfl rfl rfl rfl rfl rfl ht_8
    · change μ (Objects.RadiusResidual.clauseSet C T F D 8)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)
      have e : (Objects.RadiusResidual.clauseSet C T F D 8)ᶜ = {g | ¬Objects.CorrectedEvent.S9 C T g} := by
        ext g; simp [Objects.RadiusResidual.clauseSet]
      rw [e]
      have hbump : LQGMetric.gradEnergy T.bump ≤ t.E_max := by
        rw [Objects.RadiusResidual.gradEnergy_tubeDataOf_eq_unit C Pt S.good hSmall ρ₀ X]
        exact hE x hx S.good C.supPos hSmall
      have h9 := Objects.ProbabilityS7S9.s9_failure_le μ hμ.1 C T ⟨t.E_max, t.E_max_pos.le⟩ hbump
      refine h9.trans (ENNReal.ofReal_le_ofReal ?_)
      exact t.rn_budget
  have hprob := Objects.RadiusResidual.correctedEvent_probability_of_clause_budgets μ C T hData F D D' pbar hfail
  have hL₀prob : ENNReal.ofReal (pbar : ℝ) ≤ μ L₀ := by
    rw [← measure_congr hL₀e]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hprob
    have := pbar.2.2
    linarith
  have hUnit : LQGMetric.gradEnergy (Pt.bumpTest 1 C.A_max ⟨C.A_sup, C.supPos⟩ S.good
      (by norm_num) hSmall) ≤ t.E_max := hE x hx S.good C.supPos hSmall
  refine ⟨Objects.RadiusResidual.radiusInputs_of_raw P h pbar t r D D' Pt S ρ₀ X hData E (fun g hg => hg) hUnit
    (fun z => Objects.Producer.normTranslate z ⁻¹' L₀) (fun z => ?_) (fun z => ?_) (fun z => ?_)⟩
  · exact (translate_representative μ hμ C L₀ _ hL₀m hnull z).1
  · exact (translate_representative μ hμ C L₀ _ hL₀m hnull z).2.1
  · rw [(translate_representative μ hμ C L₀ _ hL₀m hnull z).2.2]
    exact hL₀prob

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
