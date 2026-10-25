import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Select
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T58c




 


























set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Density

open LQGMetric (DistC)

 

 


theorem nonempty_centreT58Inputs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cMinus cPlus : ℝ≥0∞)
    (pbar : Set.Ioo (0 : ℝ) 1) (C' : ℝ) (hC'lo : cMinus.toReal < C')
    (hC'hi : C' < EndSaving.Interfaces.midpoint cMinus cPlus) {R₀ : Set ℝ} (hR₀ : R₀ ⊆ range dyad) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (par : EndSaving.Interfaces.Parameters ξ)
    (hcount : DyadicCount P h D D' ⟨C', lt_of_le_of_lt ENNReal.toReal_nonneg hC'lo⟩ R₀)
    (hrad : ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ radiiSet ρ R₀ →
      Nonempty (Objects.Producer.RadiusInputs P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) par pbar r)) :
    Nonempty (Objects.Producer.CentreT58Inputs P h D D' ξ Q cMinus cPlus pbar) :=
  ⟨{ cMid' := C'
     cMid'_lower := hC'lo
     cMid'_upper := hC'hi
     radii := admissibleRadii hρ0 hR₀
     params := par
     density := density_of_count P h D D' ⟨C', lt_of_le_of_lt ENNReal.toReal_nonneg hC'lo⟩
       hρ0 hρ1 hR₀ hcount
     radius := fun r hr => Classical.choice (hrad r hr) }⟩

 

 
def T58Table.Cmid0Ioi {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (t : T58Table ξ Q cm cp Kann p0 pbar) : Set.Ioi (0 : ℝ) :=
  ⟨Cmid0 cm cp, Cmid0_pos t.cm_pos t.cm_lt_cp⟩

 
def T58Table.radiiFor {ξ : Set.Ioi (0 : ℝ)} {Q cm cp : ℝ} {pbar : ℝ} {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (θ : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1) (p : Set.Ioo (0 : ℝ) 1)
    (t : T58Table ξ Q cm cp a p pbar) : Set ℝ :=
  radiiSet t.ρ (goodDyadic P h D D' (ξ : ℝ) Q a t.Cmid0Ioi θ p)

 

theorem T58Table.block_scale_good {ξ : Set.Ioi (0 : ℝ)} {Q cm cp : ℝ} {pbar : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {θ : Set.Ioi (0 : ℝ)} {a : Set.Ioo (3 / 4 : ℝ) 1} {p : Set.Ioo (0 : ℝ) 1}
    (t : T58Table ξ Q cm cp a p pbar) {r : ℝ} (hr : r ∈ t.radiiFor P h D D' θ a p) :
    ∃ k : ℕ, t.ρ * r = dyad k ∧ t.ρ * r < t.ρ ∧
      ENNReal.ofReal (p : ℝ) ≤
        P {ω | OptimalConstants.Ratios.HtildeEvent D D' (ξ : ℝ) Q (EndSaving.Interfaces.dyadicRadius k) a t.Cmid0Ioi θ (h ω)} := by
  obtain ⟨hmem, hlt⟩ := mul_mem_of_mem_radiiSet t.ρ_pos hr
  obtain ⟨k, hk, hprob⟩ := hmem
  exact ⟨k, hk, hlt, hprob⟩

 




def T58RadiusResidual : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
    IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
    IsNormalizedWholePlaneGFF h P → ∀ cMinus cPlus : ℝ≥0∞,
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
    cMinus < cPlus → 0 < Q → 0 < cMinus → cPlus < ⊤ →
    ∀ (θ : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1) (p : Set.Ioo (0 : ℝ) 1)
      (pbar : Set.Ioo (0 : ℝ) 1),
      ∃ t : T58Table ξ Q cMinus.toReal cPlus.toReal a p pbar,
        ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ t.radiiFor P h D D' θ a p →
          Nonempty (Objects.Producer.RadiusInputs P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) t.params pbar r)

 



def T58BudgetResidual : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
    IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
    IsNormalizedWholePlaneGFF h P → ∀ cMinus cPlus : ℝ≥0∞,
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
    cMinus < cPlus → 0 < Q → 0 < cMinus → cPlus < ⊤ →
    ∀ (θ : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1) (p : Set.Ioo (0 : ℝ) 1)
      (pbar : Set.Ioo (0 : ℝ) 1),
      ∃ B : T58Budgets ξ Q cMinus.toReal cPlus.toReal a p pbar, B.Eventually ∧
        ∀ t : T58Table ξ Q cMinus.toReal cPlus.toReal a p pbar, t.Satisfies B →
          ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ t.radiiFor P h D D' θ a p →
            Nonempty (Objects.Producer.RadiusInputs P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) t.params pbar r)

theorem toReal_lt_of_lt {cMinus cPlus : ℝ≥0∞} (hcp : cPlus < ⊤) (h : cMinus < cPlus) :
    cMinus.toReal < cPlus.toReal :=
  (ENNReal.toReal_lt_toReal (h.trans hcp).ne hcp.ne).2 h

theorem toReal_pos_of_pos {cMinus cPlus : ℝ≥0∞} (hcm : 0 < cMinus) (hcp : cPlus < ⊤)
    (h : cMinus < cPlus) : 0 < cMinus.toReal :=
  ENNReal.toReal_pos hcm.ne' (h.trans hcp).ne

 

theorem t58RadiusResidual_of_budget (hB : T58BudgetResidual) : T58RadiusResidual := by
  intro Ω _ P _ h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict hQ hcm hcp θ a p pbar
  obtain ⟨B, hBev, hobj⟩ :=
    hB P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict hQ hcm hcp θ a p pbar
  obtain ⟨t, ht⟩ := exists_t58Table (ξ := ξ) hQ (toReal_pos_of_pos hcm hcp hstrict)
    (toReal_lt_of_lt hcp hstrict) a.2.1 a.2.2 p.2.1 p.2.2 pbar.2.1 pbar.2.2 B hBev
  exact ⟨t, hobj t ht⟩

 

 



theorem nonempty_centreT58Inputs_of_inputs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus) (hQ : 0 < Q) (hcm : 0 < cMinus) (hcp : cPlus < ⊤)
    (hP36 : P364DyadicInput) (hR : T58RadiusResidual) :
    ∀ pbar : Set.Ioo (0 : ℝ) 1, Nonempty (Objects.Producer.CentreT58Inputs P h D D' ξ Q cMinus cPlus pbar) := by
  intro pbar
  have hlt : cMinus.toReal < cPlus.toReal := toReal_lt_of_lt hcp hstrict
  obtain ⟨θ, a, p, hS⟩ :=
    hP36 ξ Q hQ D D' hD hD' P h hGFF cMinus hcm (hstrict.trans hcp) hMinus
  obtain ⟨C', hC'lo, hC'mid0, hcount⟩ :=
    hS (Cmid0 cMinus.toReal cPlus.toReal) (cm_lt_Cmid0 hlt)
  have hC'hi : C' < EndSaving.Interfaces.midpoint cMinus cPlus :=
    hC'mid0.trans (Cmid0_lt_Cmid hlt)
  obtain ⟨t, ht⟩ := hR P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict hQ hcm hcp θ a p pbar
  have hρ1 : t.ρ < 1 := lt_trans t.ρ_64 (by norm_num)
  exact nonempty_centreT58Inputs P h D D' ξ Q cMinus cPlus pbar C' hC'lo hC'hi
    (goodDyadic_subset P h D D' (ξ : ℝ) Q a t.Cmid0Ioi θ p) t.ρ_pos hρ1 t.params hcount ht

end SupercriticalLQGUniqueness.Uniqueness.Objects.Density
