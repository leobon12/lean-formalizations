import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.EnergyScale
import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly.TubeSelection
import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Select




 






set_option autoImplicit false
noncomputable section
open Filter Topology Set

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual

 
def stageTubeParams {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (s : Objects.Density.T58Stage10 ξ Q cm cp Kann p0 pbar) : Objects.Tube.TubeParams where
  ρ := s.ρ
  K := ⌈s.lam / (Objects.Density.locScale s.K_sh * s.ρ)⌉₊
  α := Kann
  n := 1
  ψu := 0
  ψv := 0
  sp := Objects.Density.endptScale s.m
  wp := s.lam * Objects.Density.endptScale s.m

 
theorem stageTubeParams_table {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (t : Objects.Density.T58Table ξ Q cm cp Kann p0 pbar) :
    stageTubeParams t.toT58Stage10 = Objects.RadiusAssembly.tubeParams t := rfl

 


def unitEnergyBudget {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (s : Objects.Density.T58Stage10 ξ Q cm cp Kann p0 pbar)
    (Asup Emax : ℝ) : Prop :=
  ∀ (hP : (stageTubeParams s).Good) (hA : 0 < Asup)
    (hSmall : 100 * Asup ≤ (stageTubeParams s).sp * (stageTubeParams s).ρ),
    LQGMetric.gradEnergy
      ((stageTubeParams s).bumpTest 1 s.A_max ⟨Asup, hA⟩ hP
        (by norm_num) hSmall) ≤ Emax

 

theorem eventually_unitEnergyBudget
    {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (s : Objects.Density.T58Stage10 ξ Q cm cp Kann p0 pbar) (Asup : ℝ) :
    ∀ᶠ Emax in atTop, unitEnergyBudget s Asup Emax := by
  classical
  by_cases h : ∃ (hP : (stageTubeParams s).Good) (hA : 0 < Asup),
      100 * Asup ≤ (stageTubeParams s).sp * (stageTubeParams s).ρ
  · obtain ⟨hP, hA, hSmall⟩ := h
    let E0 := LQGMetric.gradEnergy
      ((stageTubeParams s).bumpTest 1 s.A_max ⟨Asup, hA⟩ hP
        (by norm_num) hSmall)
    filter_upwards [eventually_ge_atTop E0] with Emax hE hP' hA' hSmall'
    change LQGMetric.gradEnergy
      ((stageTubeParams s).bumpTest 1 s.A_max ⟨Asup, hA'⟩ hP'
        (by norm_num) hSmall') ≤ Emax
    simpa only [E0] using hE
  · filter_upwards with Emax hP hA hSmall
    exact False.elim (h ⟨hP, hA, hSmall⟩)

 

theorem table_unitEnergy_le {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (t : Objects.Density.T58Table ξ Q cm cp Kann p0 pbar)
    (hE : unitEnergyBudget t.toT58Stage10 t.A_sup t.E_max)
    (r : Set.Ioi (0 : ℝ)) :
    LQGMetric.gradEnergy
      ((Objects.RadiusAssembly.tubeParams t).bumpTest 1 (t.toConstants r).A_max
        ⟨(t.toConstants r).A_sup, (t.toConstants r).supPos⟩
        (Objects.RadiusAssembly.tubeSelection t r).good (by norm_num)
        ((Objects.RadiusAssembly.tubeSelection t r).small
          (t.sup_lt_set.trans t.set_lt_nar)).1) ≤ t.E_max := by
  have hP : (stageTubeParams t.toT58Stage10).Good :=
    (Objects.RadiusAssembly.tubeSelection t r).good
  have hSmall : 100 * t.A_sup ≤
      (stageTubeParams t.toT58Stage10).sp * (stageTubeParams t.toT58Stage10).ρ :=
    ((Objects.RadiusAssembly.tubeSelection t r).small
      (t.sup_lt_set.trans t.set_lt_nar)).1
  exact hE hP t.sup_pos hSmall

 
def withUnitEnergy {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (B : Objects.Density.T58Budgets ξ Q cm cp Kann p0 pbar) :
    Objects.Density.T58Budgets ξ Q cm cp Kann p0 pbar :=
  { B with energy := unitEnergyBudget }

 
theorem withUnitEnergy_eventually
    {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (B : Objects.Density.T58Budgets ξ Q cm cp Kann p0 pbar) (hB : B.Eventually) :
    (withUnitEnergy B).Eventually := by
  exact {
    reg := hB.reg
    block := hB.block
    shield := hB.shield
    across := hB.across
    around := hB.around
    regCount := hB.regCount
    event := hB.event
    narrow := hB.narrow
    network := hB.network
    sup := hB.sup
    energy := eventually_unitEnergyBudget }

 

theorem table_unitEnergy_le_of_satisfies
    {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (B : Objects.Density.T58Budgets ξ Q cm cp Kann p0 pbar)
    (t : Objects.Density.T58Table ξ Q cm cp Kann p0 pbar)
    (ht : t.Satisfies (withUnitEnergy B))
    (r : Set.Ioi (0 : ℝ)) :
    LQGMetric.gradEnergy
      ((Objects.RadiusAssembly.tubeParams t).bumpTest 1 (t.toConstants r).A_max
        ⟨(t.toConstants r).A_sup, (t.toConstants r).supPos⟩
        (Objects.RadiusAssembly.tubeSelection t r).good (by norm_num)
        ((Objects.RadiusAssembly.tubeSelection t r).small
          (t.sup_lt_set.trans t.set_lt_nar)).1) ≤ t.E_max := by
  have henergy : unitEnergyBudget t.toT58Stage10 t.A_sup t.E_max := by
    rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, he⟩
    exact he
  exact table_unitEnergy_le t henergy r

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
