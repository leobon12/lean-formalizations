import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.Assembly1
import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Centre




 













set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology Real
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

 
theorem eventually_count (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), n ≤ ⌊c / ρ⌋₊ := by
  filter_upwards [Objects.Density.ev_pos, Objects.Density.ev_le (show 0 < c / (n + 1) by positivity)] with ρ hρ hρc
  apply Nat.le_floor
  rw [le_div_iff₀ hρ]
  rw [le_div_iff₀ (by positivity)] at hρc
  nlinarith

 
theorem t58BudgetResidual_of_t51
    (hT51 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
      IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      IsNormalizedWholePlaneGFF h P → ∀ cMinus cPlus : ℝ≥0∞,
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
      ∀ (hstrict : cMinus < cPlus), 0 < Q → ∀ (hcm : 0 < cMinus) (hcp : cPlus < ⊤),
      ∀ (θ : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1) (p : Set.Ioo (0 : ℝ) 1)
        (pbar : Set.Ioo (0 : ℝ) 1),
        T51Statement P h D D' ξ Q cMinus.toReal cPlus.toReal a θ p pbar
          (Objects.Density.toReal_pos_of_pos hcm hcp hstrict) (Objects.Density.toReal_lt_of_lt hcp hstrict)) :
    Objects.Density.T58BudgetResidual := by
  intro Ω _ P _ h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict hQ hcm hcp θ a p pbar
  set μ := P.map h with hμdef
  have hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ := Objects.ProbabilityS7S9.normalizedGFF_id_map' P h hGFF
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hGFF.1.measurable.aemeasurable).2 inferInstance
  set cm := cMinus.toReal with hcmdef
  set cp := cPlus.toReal with hcpdef
  have hcmR : 0 < cm := Objects.Density.toReal_pos_of_pos hcm hcp hstrict
  have hcmp : cm < cp := Objects.Density.toReal_lt_of_lt hcp hstrict
  
  obtain ⟨cReg, a₀, A₀, hcReg0, -, ha₀0, -, -, -, k0, -, hS123⟩ :=
    Objects.ProbabilityS3.exists_s1_s2_s3_allCentre_budget μ hμ ξ Q D hD pbar
  obtain ⟨a5, ha5, hS5⟩ := Objects.ProbabilityS5.exists_s5_budget μ hμ ξ Q hQ D hD pbar
  obtain ⟨K6, hK6, hS6⟩ := Objects.AnnulusTails.exists_s6_budget_nar μ hμ ξ Q D hD pbar
  
  obtain ⟨Bm, hBm, hT⟩ := hT51 P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict hQ hcm hcp
    θ a p pbar
  
  have hn : ∀ s : Objects.Density.T58Stage5 ξ Q cm cp a p pbar, ∃ n₀ : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC) (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
      IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' → IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞, 0 < cMinus → cMinus < ⊤ → 0 < cPlus → cPlus < ⊤ →
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
      ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), Objects.CorrectedEvent.DataMatch C T → ∀ (Ksh : ℕ) (Cmid0 : ℝ),
      C.A_sp = s.A_sp → C.A_loc = 3 * 8 ^ Ksh → C.A_endpt ≤ 1 → 0 ≤ C.K_ann →
      C.lamConst ≤ 1 / 100 → C.lamConst * cPlus.toReal / cMinus.toReal < 1 →
      C.ρ ≤ C.lamConst / C.A_loc →
      n₀ ≤ ⌊C.lamConst * s.A_sp / (16 * π * (C.A_loc * C.ρ))⌋₊ →
      ENNReal.ofReal (blockMarginal p s.lam s.m) ≤ (P.map h) {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g} →
      (P.map h) {g | ¬ Objects.CorrectedEvent.S4 C T (fun z => Objects.Excursions.blockEvent C T Ksh Cmid0 D D' z g)} ≤
        ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
    intro s
    have hA1 : s.A_sp ≤ 1 := by
      have h1 := s.sp_lt
      have h2 : Objects.Density.epScale s.k0 ≤ 1 := by
        rw [Objects.Density.epScale_eq_pow]; exact pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    exact exists_s4_table pbar (blockMarginal p s.lam s.m) (blockMarginal_pos p.2.1 _ _)
      (blockMarginal_lt_one p.2.1 p.2.2 _ _) s.A_sp s.sp_pos hA1
  choose n₀ hn₀ using hn
  
  have hmesh : ∀ (s : Objects.Density.T58Stage8 ξ Q cm cp a p pbar) (x : ℂ × ℝ × ℝ × ℝ),
      ∃ e : ℝ × Finset ℂ, 0 < e.1 ∧
        ((familyParams s.lam (Objects.Density.endptScale s.m) a (Objects.Density.locScale s.K_sh) s.ρ x).Good →
          MeshProps ((familyParams s.lam (Objects.Density.endptScale s.m) a (Objects.Density.locScale s.K_sh)
            s.ρ x).tube 1) 1 s.A_set e.1 e.2) := by
    intro s x
    by_cases hG : (familyParams s.lam (Objects.Density.endptScale s.m) a (Objects.Density.locScale s.K_sh) s.ρ x).Good
    · obtain ⟨ρ₁, X₁, hM⟩ := exists_unit_mesh _ hG s.set_pos
      exact ⟨(ρ₁, X₁), hM.1, fun _ => hM⟩
    · exact ⟨(1, ∅), one_pos, fun hG' => absurd hG' hG⟩
  choose mesh hmeshpos hmeshP using hmesh
  
  have hnet : ∀ s : Objects.Density.T58Stage8 ξ Q cm cp a p pbar, ∃ A : ℝ, 0 < A ∧
      ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), C.ξ = ↑ξ → C.Q = Q →
        (∃ e ∈ (blockFamily (s.lam * Objects.Density.endptScale s.m) s.m).image (mesh s),
          T.netRadius = e.1 * C.r ∧ T.netSites = Finset.image (fun x => (C.r : ℂ) * x) e.2) →
        A ≤ C.A_internal → μ {g | ¬Objects.CorrectedEvent.S7 C T (D g) g} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
    intro s
    exact Objects.ProbabilityS7S9.exists_s7_budget μ hμ ξ Q D hD pbar _ (fun e he => by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 he
      exact hmeshpos s x)
  choose A₇ hA₇pos hA₇ using hnet
  
  have hsup : ∀ s : Objects.Density.T58Stage10 ξ Q cm cp a p pbar, ∃ A : ℝ, 0 < A ∧
      ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), Objects.CorrectedEvent.DataMatch C T →
        C.ξ = ↑ξ → C.Q = Q → C.lamConst = s.lam → C.A_loc = Objects.Density.locScale s.K_sh → C.ρ = s.ρ →
        C.A_endpt = Objects.Density.endptScale s.m → C.A_max = s.A_max → C.A_sup ≤ A →
        μ {g | ¬Objects.CorrectedEvent.S8 C T (D g)} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := fun s =>
    Objects.ProbabilityS7S9.exists_s8_budget μ hμ ξ Q D hD pbar s.lam (Objects.Density.locScale s.K_sh) s.ρ (Objects.Density.endptScale s.m)
      s.A_max s.lam_pos (Objects.Density.endptScale_pos s.m)
  choose A₈ hA₈pos hA₈ using hsup
  
  let Cmid0I : Set.Ioi (0 : ℝ) := ⟨Objects.Density.Cmid0 cm cp, Objects.Density.Cmid0_pos hcmR hcmp⟩
  let B : Objects.Density.T58Budgets ξ Q cm cp a p pbar :=
    { reg := fun c => c ≤ cReg
      block := Bm
      shield := fun s m K => Bm s m → BlockGood P h D D' ξ Q a Cmid0I θ p s.lam m K
      across := fun _ x => x ≤ a₀
      around := fun _ y => A₀ ≤ y
      regCount := fun _ k => k0 ≤ k
      event := fun s ρ => n₀ s ≤ ⌊s.lam * s.A_sp / (16 * π * (Objects.Density.locScale s.K_sh * ρ))⌋₊
      narrow := fun s x => x < a5 ∧ K6 * x ≤ s.lam
      network := fun s y => A₇ s ≤ y
      sup := fun s x => x ≤ A₈ s
      energy := fun s x E => familyEnergyBudget s x E }
  have hBev : B.Eventually := by
    refine ⟨Objects.Density.eventually_le_threshold hcReg0, hBm, ?_, fun _ => Objects.Density.eventually_le_threshold ha₀0,
      fun _ => Objects.Density.eventually_ge_threshold A₀, fun _ => Objects.Density.eventually_ge_threshold_nat k0, ?_, ?_,
      fun s => Objects.Density.eventually_ge_threshold (A₇ s), fun s => Objects.Density.eventually_le_threshold (hA₈pos s),
      fun s x => eventually_familyEnergyBudget s x⟩
    · intro s m
      by_cases hb : Bm s m
      · filter_upwards [hT s m hb] with K hK _
        exact hK
      · filter_upwards with K hK
        exact absurd hK hb
    · intro s
      have hc : 0 < s.lam * s.A_sp / (16 * π * Objects.Density.locScale s.K_sh) := by
        have := s.lam_pos; have := s.sp_pos; have := Objects.Density.locScale_pos s.K_sh; positivity
      filter_upwards [eventually_count (n₀ s) hc, Objects.Density.ev_pos] with ρ hρ hρ0
      change n₀ s ≤ ⌊s.lam * s.A_sp / (16 * π * (Objects.Density.locScale s.K_sh * ρ))⌋₊
      rwa [show s.lam * s.A_sp / (16 * π * (Objects.Density.locScale s.K_sh * ρ)) =
        s.lam * s.A_sp / (16 * π * Objects.Density.locScale s.K_sh) / ρ by
          rw [div_div]; ring_nf]
    · intro s
      have hl := s.lam_pos
      filter_upwards [Objects.Density.ev_lt ha5, Objects.Density.ev_le (show 0 < s.lam / K6 by positivity)] with x h1 h2
      refine ⟨h1, ?_⟩
      rw [le_div_iff₀ hK6] at h2
      linarith
  refine ⟨B, hBev, ?_⟩
  intro t ht r hr
  obtain ⟨hreg, hblock, hshield, hacross, haround, hregCount, hevent, hnarrow, hnetwork, hsupB,
    henergy⟩ := ht
  
  obtain ⟨k, hk, -, hH⟩ := t.block_scale_good hr
  have hb : 0 < t.ρ * r := mul_pos t.ρ_pos r.2
  have hH' : ENNReal.ofReal (p : ℝ) ≤
      P {ω | OptimalConstants.Ratios.HtildeEvent D D' (ξ : ℝ) Q ⟨t.ρ * r, hb⟩ a Cmid0I θ (h ω)} := by
    have e1 : (⟨t.ρ * r, hb⟩ : Set.Ioi (0 : ℝ)) = EndSaving.Interfaces.dyadicRadius k := by
      apply Subtype.ext
      exact hk.trans rfl
    have e2 : Cmid0I = t.Cmid0Ioi := Subtype.ext rfl
    rw [e1, e2]
    exact hH
  obtain ⟨x, hx, hsel⟩ := hshield hblock (t.ρ * r) hb hH'
  have hG : (familyParams t.lam (Objects.Density.endptScale t.m) a (Objects.Density.locScale t.K_sh) t.ρ x).Good :=
    (familyParams_selection t r hx).good
  have hM := hmeshP t.toT58Stage8 x hG
  exact radiusInputs_of_selection P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict hQ hcm
    hcp pbar t r x hx (mesh t.toT58Stage8 x).1 (mesh t.toT58Stage8 x).2 hM
    (blockMarginal p t.lam t.m) hsel cReg a₀ A₀ k0 hS123 hreg hacross haround hregCount
    (fun C T hData hAloc hE hK0 hlam hSmall hρloc hlamC hρC hsp hmarg =>
      hn₀ t.toT58Stage5 P h ξ Q D D' hD hD' hGFF cMinus cPlus hcm (hstrict.trans hcp)
        (hcm.trans hstrict) hcp hMinus hPlus C T hData t.K_sh _ hsp hAloc hE hK0 hlam hSmall hρloc
        (by
          rw [hlamC, hAloc, hρC]
          change n₀ t.toT58Stage5 ≤ ⌊t.lam * t.A_sp / (16 * π * (Objects.Density.locScale t.K_sh * t.ρ))⌋₊ at hevent
          unfold Objects.Density.locScale at hevent
          exact hevent) hmarg)
    a5 hS5 hnarrow.1 K6 hS6 hnarrow.2
    ((blockFamily (t.lam * Objects.Density.endptScale t.m) t.m).image (mesh t.toT58Stage8))
    (Finset.mem_image_of_mem _ hx) (A₇ t.toT58Stage8) (hA₇ t.toT58Stage8) hnetwork
    (A₈ t.toT58Stage10) (hA₈ t.toT58Stage10) hsupB henergy

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
