import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.MeshScale
import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.EnergyBudget




 













set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

 
def blockMarginal (p0 lam : ℝ) (m : ℕ) : ℝ :=
  p0 / (16 * ((shapeData (lam * Objects.Density.endptScale m) m).card : ℝ))

theorem gridAngles_nonempty (δ : ℝ) : (gridAngles δ).Nonempty :=
  ⟨δ * (0 : ℤ), Finset.mem_image.2 ⟨0, by simp, rfl⟩⟩

theorem radiusRatios_nonempty (m : ℕ) : (radiusRatios m).Nonempty :=
  ⟨(1 / 4 : ℝ) ^ m, Finset.mem_image.2 ⟨m, by simp; omega, rfl⟩⟩

theorem shapeData_card_pos (δ : ℝ) (m : ℕ) : 0 < (shapeData δ m).card := by
  apply Finset.card_pos.2
  exact (radiusRatios_nonempty m).product ((gridAngles_nonempty δ).product (gridAngles_nonempty δ))

theorem blockMarginal_pos {p0 : ℝ} (hp : 0 < p0) (lam : ℝ) (m : ℕ) : 0 < blockMarginal p0 lam m := by
  unfold blockMarginal
  have := shapeData_card_pos (lam * Objects.Density.endptScale m) m
  positivity

theorem blockMarginal_lt_one {p0 : ℝ} (hp : 0 < p0) (hp1 : p0 < 1) (lam : ℝ) (m : ℕ) :
    blockMarginal p0 lam m < 1 := by
  unfold blockMarginal
  have h1 : (1 : ℝ) ≤ (shapeData (lam * Objects.Density.endptScale m) m).card := by
    exact_mod_cast shapeData_card_pos (lam * Objects.Density.endptScale m) m
  rw [div_lt_one (by positivity)]
  linarith

 
def BlockGood {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (Cmid0 : Set.Ioi (0 : ℝ)) (θ : Set.Ioi (0 : ℝ)) (p : Set.Ioo (0 : ℝ) 1)
    (lam : ℝ) (m Ksh : ℕ) : Prop :=
  ∀ (b : ℝ) (hb : 0 < b),
    ENNReal.ofReal (p : ℝ) ≤ P {ω | OptimalConstants.Ratios.HtildeEvent D D' (ξ : ℝ) Q ⟨b, hb⟩ a Cmid0 θ (h ω)} →
    ∃ x ∈ blockFamily (lam * Objects.Density.endptScale m) m,
      ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), C.lamConst = lam → T.rho * T.r = b →
        T.alpha = a → T.orientation = x.1 → T.psiU = x.2.2.1 → T.psiV = x.2.2.2 →
        T.blockRadius = x.2.1 * b →
        ENNReal.ofReal (blockMarginal p lam m) ≤
          (P.map h) {g | Objects.Excursions.blockRaw C T Ksh (Cmid0 : ℝ) D D' g}

 
def T51Statement {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cm cp : ℝ) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (θ : Set.Ioi (0 : ℝ)) (p : Set.Ioo (0 : ℝ) 1) (pbar : ℝ) (hcm : 0 < cm) (hcmp : cm < cp) : Prop :=
  ∃ Bm : Objects.Density.T58Stage1 ξ Q cm cp a p pbar → ℕ → Prop, (∀ s, ∀ᶠ m in atTop, Bm s m) ∧
    ∀ s m, Bm s m → ∀ᶠ Ksh in atTop,
      BlockGood P h D D' ξ Q a ⟨Objects.Density.Cmid0 cm cp, Objects.Density.Cmid0_pos hcm hcmp⟩ θ p s.lam m Ksh

 
def stageFamilyParams {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (s : Objects.Density.T58Stage10 ξ Q cm cp Kann p0 pbar) (x : ℂ × ℝ × ℝ × ℝ) : Objects.Tube.TubeParams :=
  familyParams s.lam (Objects.Density.endptScale s.m) Kann (Objects.Density.locScale s.K_sh) s.ρ x

 
def familyEnergyBudget {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (s : Objects.Density.T58Stage10 ξ Q cm cp Kann p0 pbar) (Asup Emax : ℝ) : Prop :=
  ∀ x ∈ blockFamily (s.lam * Objects.Density.endptScale s.m) s.m,
    ∀ (hP : (stageFamilyParams s x).Good) (hA : 0 < Asup)
      (hSmall : 100 * Asup ≤ (stageFamilyParams s x).sp * (stageFamilyParams s x).ρ),
      LQGMetric.gradEnergy
        ((stageFamilyParams s x).bumpTest 1 s.A_max ⟨Asup, hA⟩ hP (by norm_num) hSmall) ≤ Emax

theorem eventually_familyEnergyBudget {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (s : Objects.Density.T58Stage10 ξ Q cm cp Kann p0 pbar) (Asup : ℝ) :
    ∀ᶠ Emax in atTop, familyEnergyBudget s Asup Emax := by
  classical
  have hone : ∀ x ∈ blockFamily (s.lam * Objects.Density.endptScale s.m) s.m, ∀ᶠ Emax in atTop,
      ∀ (hP : (stageFamilyParams s x).Good) (hA : 0 < Asup)
        (hSmall : 100 * Asup ≤ (stageFamilyParams s x).sp * (stageFamilyParams s x).ρ),
        LQGMetric.gradEnergy
          ((stageFamilyParams s x).bumpTest 1 s.A_max ⟨Asup, hA⟩ hP (by norm_num) hSmall) ≤
            Emax := by
    intro x _
    by_cases h : ∃ (hP : (stageFamilyParams s x).Good) (hA : 0 < Asup),
        100 * Asup ≤ (stageFamilyParams s x).sp * (stageFamilyParams s x).ρ
    · obtain ⟨hP, hA, hSmall⟩ := h
      filter_upwards [eventually_ge_atTop (LQGMetric.gradEnergy
        ((stageFamilyParams s x).bumpTest 1 s.A_max ⟨Asup, hA⟩ hP (by norm_num) hSmall))]
        with Emax hE hP' hA' hSmall'
      exact hE
    · filter_upwards with Emax hP hA hSmall
      exact False.elim (h ⟨hP, hA, hSmall⟩)
  have := (Filter.eventually_all_finset _).2 hone
  filter_upwards [this] with Emax hE x hx
  exact hE x hx

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
