import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLiminfCompare
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNormalizedEquality
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2PatchWitness
import LQGMetric.Papers.DFGPS.L2_1Ratio
import LQGMetric.Papers.DFGPS.L2_1Bdd
import LQGMetric.Field.Measurable

 














set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem locMollify_addFun (ε : ℝ) (hε : 0 < ε) (g : DistC) (F : C(ℂ, ℝ)) (z : ℂ) :
    locMollify ε hε (addFun g F) z = locMollify ε hε g z + locMollify ε hε (ofCont F) z := by
  unfold locMollify addFun
  rfl

 

theorem locMollify_ofCont_congr (ε : ℝ) (hε : 0 < ε) {F F' : C(ℂ, ℝ)} {z : ℂ}
    (h : EqOn F F' (Metric.closedBall z (Real.sqrt ε))) :
    locMollify ε hε (ofCont F) z = locMollify ε hε (ofCont F') z := by
  unfold locMollify
  rw [ofCont_apply, ofCont_apply]
  congr 1
  funext w
  by_cases hw : w ∈ tsupport (locTest ε hε z : ℂ → ℝ)
  · rw [h (tsupport_locTest_subset ε hε z hw)]
  · rw [image_eq_zero_of_notMem_tsupport hw, zero_mul, zero_mul]

 
theorem internal_le_of_weight_close (ξ : Set.Ioi (0 : ℝ)) (a : Set.Ioi (0 : ℝ))
    (φ ψ : C(ℂ, ℝ)) {V : Set ℂ} (hV : IsOpen V) {θ : ℝ}
    (hθ : ∀ z ∈ V, |φ z - ψ z| ≤ θ) (u v : V) :
    (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a φ).internal V (u, v) ≤
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) *
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a ψ).internal V (u, v) := by
  rw [normalizedLFPPMetric_internal_eq_lfppDOn _ _ _ hV,
    normalizedLFPPMetric_internal_eq_lfppDOn _ _ _ hV]
  have h := LQGMetric.DFGPS.lfppDOn_le_of_abs_sub_le (ξ := (ξ : ℝ)) (φ := ψ) (φ' := φ)
    (S := V) (δ := θ) hθ u v
  rw [abs_of_pos ξ.property] at h
  calc ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDOn (ξ : ℝ) φ V u v
      ≤ ENNReal.ofReal ((a : ℝ)⁻¹) *
          (ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) * lfppDOn (ξ : ℝ) ψ V u v) := by gcongr
    _ = _ := by ring

 
theorem lowerNbhdObs_eq_of_weight_close (ξ : Set.Ioi (0 : ℝ)) (a : ℕ → Set.Ioi (0 : ℝ))
    (φ ψ : ℕ → C(ℂ, ℝ)) {V : Set ℂ} (hV : IsOpen V)
    (hclose : ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ V, |φ n z - ψ n z| ≤ θ)
    (x y : V) :
    lowerNeighborhoodObservable (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n) (φ n))
        V x y =
      lowerNeighborhoodObservable
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n) (ψ n)) V x y := by
  unfold lowerNeighborhoodObservable
  refine iSup_congr fun k => ?_
  apply liminf_eq_of_eventually_mul_both
  intro c hc
  have hc0 : 0 < c := lt_trans one_pos hc
  set θ : ℝ := Real.log c / (ξ : ℝ)
  have hθ : 0 < θ := div_pos (Real.log_pos hc) ξ.property
  have hexp : Real.exp ((ξ : ℝ) * θ) = c := by
    simp only [θ]
    rw [mul_div_cancel₀ _ (ne_of_gt ξ.property), Real.exp_log hc0]
  have hev := hclose θ hθ
  constructor
  · filter_upwards [hev] with n hn
    have h := neighborhoodInternal_le_const_mul _ _ x y (1 / ((k : ℝ) + 1))
      (Real.exp_pos _) (fun u v => internal_le_of_weight_close ξ (a n) (φ n) (ψ n) hV hn u v)
    rwa [hexp] at h
  · filter_upwards [hev] with n hn
    have hn' : ∀ z ∈ V, |ψ n z - φ n z| ≤ θ := fun z hz => by
      rw [abs_sub_comm]; exact hn z hz
    have h := neighborhoodInternal_le_const_mul _ _ x y (1 / ((k : ℝ) + 1))
      (Real.exp_pos _) (fun u v => internal_le_of_weight_close ξ (a n) (ψ n) (φ n) hV hn' u v)
    rwa [hexp] at h

end SupercriticalLQGUniqueness.B2.PfeAxioms
