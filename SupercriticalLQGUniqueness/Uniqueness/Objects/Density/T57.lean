import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Centre




 



















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Density

open LQGMetric (DistC addFun)

 
theorem blockRadius_ge_of_dataMatch {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData}
    (hData : Objects.CorrectedEvent.DataMatch C T) : C.A_endpt * C.ρ * C.r ≤ T.blockRadius :=
  hData.2.2.2.2.2.2.2.2.2.1

 

def T58Table.mkT57Inputs {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {cMinus cPlus : ℝ≥0∞} {Kann p0 pbar : ℝ}
    (t : T58Table ξ Q cMinus.toReal cPlus.toReal Kann p0 pbar) (D D' : DistC → LSCMetric)
    (r : Set.Ioi (0 : ℝ)) (U₀ V₀ : TopologicalSpace.Opens ℂ) (g₀ : C(ℂ, ℝ)) (Target : Set DistC)
    (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch (t.toConstants r) T) (F : ℂ → DistC → Prop)
    (event : ∀ g ∈ Target, Objects.CorrectedEvent.correctedEvent (t.toConstants r) T hData F D D' g)
    (comp : ∀ g ∈ Target, ∀ x y : ℂ, D' g (x, y) ≤ ENNReal.ofReal cPlus.toReal * D g (x, y))
    (tube_sub : Objects.CorrectedEvent.tubeSet T ⊆ (U₀ : Set ℂ))
    (witness : ∀ g ∈ Target, ∀ c : ℝ, IsCircleAverage g (Objects.Producer.radius (t.toConstants r)) 0 c →
      ∀ (P : ℝ → ℂ) (L τ' τ σ σ' : ℝ),
        EndSaving.Interfaces.BumpedGeodesic (D (addFun g (-g₀))) P L →
        P 0 ∉ ball (0 : ℂ) (4 * (r : ℝ)) → P L ∉ ball (0 : ℂ) (4 * (r : ℝ)) →
        EndSaving.Interfaces.Excursion P L (ball (0 : ℂ) (4 * (r : ℝ))) V₀ τ' τ σ σ' →
        ∀ (hτ : P τ ∈ ball (0 : ℂ) (4 * (r : ℝ))) (hσ : P σ ∈ ball (0 : ℂ) (4 * (r : ℝ))),
          ENNReal.ofReal t.params.Ctime *
              ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)) ≤
            (D g).internal (ball (0 : ℂ) (4 * (r : ℝ))) (⟨P τ, hτ⟩, ⟨P σ, hσ⟩) →
          Nonempty (Objects.Producer.T57Witness (t.toConstants r) T hData t.endpt_le_one (D g) (D' g)
            (D (addFun g (-g₀))) (D' (addFun g (-g₀))) (V₀ : Set ℂ)
            ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)) (Cmid0 cMinus.toReal cPlus.toReal)
            P L τ' τ σ σ')) :
    Objects.Producer.T57Inputs D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) t.params r U₀ V₀ g₀ Target where
  C := t.toConstants r
  T := T
  hData := hData
  F := F
  ξ_eq := rfl
  Q_eq := rfl
  r_eq := rfl
  max_eq := rfl
  inc_eq := rfl
  event := event
  Cp := cPlus.toReal
  Cp_pos := t.cm_pos.trans t.cm_lt_cp
  comp := comp
  Cmid0 := Cmid0 cMinus.toReal cPlus.toReal
  Cmid0_nonneg := (Cmid0_pos t.cm_pos t.cm_lt_cp).le
  cMid_nonneg := ((Cmid0_pos t.cm_pos t.cm_lt_cp).trans (Cmid0_lt_Cmid t.cm_lt_cp)).le
  ratio := t.ratio
  K_nonneg := (t.toConstants_relations r).1
  endpt_le := t.endpt_le_one
  lam_le := t.lam_le
  count := t.toConstants_count r (blockRadius_ge_of_dataMatch hData)
  tube_sub := tube_sub
  sep_small := (t.toConstants_relations r).2.2.2.1
  witness := witness

 
theorem T58Table.mkT57Inputs_C {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {cMinus cPlus : ℝ≥0∞}
    {Kann p0 pbar : ℝ} (t : T58Table ξ Q cMinus.toReal cPlus.toReal Kann p0 pbar)
    (D D' : DistC → LSCMetric) (r : Set.Ioi (0 : ℝ)) (U₀ V₀ : TopologicalSpace.Opens ℂ)
    (g₀ : C(ℂ, ℝ)) (Target : Set DistC) (T : Objects.CorrectedEvent.TubeData)
    (hData : Objects.CorrectedEvent.DataMatch (t.toConstants r) T) (F : ℂ → DistC → Prop) (event) (comp) (tube_sub)
    (witness) :
    (t.mkT57Inputs D D' r U₀ V₀ g₀ Target T hData F event comp tube_sub witness).C =
      t.toConstants r := rfl

end SupercriticalLQGUniqueness.Uniqueness.Objects.Density
