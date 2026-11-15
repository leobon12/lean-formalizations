/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkMart9Time

/-!
# Capped inverse times at the local first-mark stops

The existing path argument for inverse clocks applies to the local separating
horizon. This identifies the actual optional-time coordinate evaluation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Noise10

open Zhan.Retarget

/-- Clock images of the spatial/Brownian source localizers. -/
def imageStops {Ω : Type*} (a : ℝ) (G : Set Ω) (S : ℕ → Ω → ℝ≥0)
    (W B : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ) (VR : Fin 2 → ℝ≥0 → Ω → ℝ)
    (e : Ω → ℝ≥0∞) : ℕ → Ω → ℝ≥0 :=
  Clock7.imageStop (a := a) (G := G) (W := W) (V := VR 0) (A := rLoc 0 G S W VL VR B e)

/-- The stopped source coordinates evaluated at the capped inverse stopping time. -/
def cappedPoint {Ω : Type*} (xL : Fin 0 → ℝ) (a b : ℝ) (G : Set Ω) (S : ℕ → Ω → ℝ≥0)
    (W B : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ) (VR : Fin 2 → ℝ≥0 → Ω → ℝ)
    (e : Ω → ℝ≥0∞) (n : ℕ) (u : ℝ≥0) (ω : Ω) : RCoord 0 2 × ℝ :=
  Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR (rLoc 0 G S W VL VR B e n)
    (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0))
      (Clock7.inverseTime G a W (VR 0) (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) u) ω) ω

variable {Ω : Type*} {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω} {ω : Ω}

/-- The source time read at `u`, stopped at the localizer, is the inverse at `u ∧ Q_n`. -/
theorem min_cap_inverse_localizer (ha : 0 < a) (hab : a < b)
    (hg : Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω) (hω : ω ∈ G) (n : ℕ) (u : ℝ≥0) :
    min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0))
      (Clock7.inverseTime G a W (VR 0) (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) u) ω)
      (rLoc 0 G S W VL VR B e n ω) =
      (invClk (rate a (W · ω) (VR 0 · ω)) (min u (imageStops a G S W B VL VR e n ω) : ℝ≥0)).toNNReal := by
  let σ := rLoc 0 G S W VL VR B e n ω
  let Q := imageStops a G S W B VL VR e n ω
  let T := sepTime (W · ω) (VR 0 · ω) (e ω)
  let I := Clock7.inverseTime G a W (VR 0) (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) u
  have hS : SepUpTo (W · ω) (VR 0 · ω) T := (hg.data ha hab).sep
  have hσT : (σ : ℝ≥0∞) < T := hg.loc_lt n
  have hσn : σ ≤ n := rLoc_le_n n ω
  obtain ⟨h0, hlt⟩ := clk_lt_newHorizon' hS ha hσT
  have hQ : (Q : ℝ) = clk (rate a (W · ω) (VR 0 · ω)) σ := by
    simp only [Q, imageStops, Clock7.imageStop, hω, ↓reduceIte]
    exact Real.coe_toNNReal _ h0
  have hinvσ : (invClk (rate a (W · ω) (VR 0 · ω))
      (clk (rate a (W · ω) (VR 0 · ω)) σ)).toNNReal = σ := by
    rw [invClk_clk_of_lt hS ha hσT, Real.toNNReal_coe]
  have hIe : I ω = if (u : ℝ≥0∞) < newHorizon a (W · ω) (VR 0 · ω) T then
      ((invClk (rate a (W · ω) (VR 0 · ω)) u).toNNReal : WithTop ℝ≥0) else toWT T := by
    simp only [I, Clock7.inverseTime, hω, ↓reduceIte]
    rfl
  have hcap := Sec2.TwoSeed.coe_capTime (fun _ => (n : ℝ≥0)) I ω
  rw [hIe] at hcap
  change min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) I ω) σ =
    (invClk (rate a (W · ω) (VR 0 · ω)) (min u Q : ℝ≥0)).toNNReal
  by_cases hu : (u : ℝ≥0∞) < newHorizon a (W · ω) (VR 0 · ω) T
  · simp only [hu, ↓reduceIte] at hcap
    rw [← WithTop.coe_min] at hcap
    rw [WithTop.coe_inj.1 hcap, min_comm (n : ℝ≥0), min_assoc, min_eq_right hσn]
    by_cases huQ : u ≤ Q
    · rw [min_eq_left huQ]
      refine min_eq_left ((invClk_le_iff hS ha hu hσT).2 ?_)
      rw [← hQ]
      exact_mod_cast huQ
    · rw [not_le] at huQ
      rw [min_eq_right huQ.le, hQ, hinvσ]
      refine min_eq_right ?_
      by_contra hle
      rw [not_le] at hle
      have h := (invClk_le_iff hS ha hu hσT).1 hle.le
      rw [← hQ] at h
      exact (not_le.2 huQ) (by exact_mod_cast h)
  · simp only [hu, ↓reduceIte] at hcap
    have hge : σ ≤ Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) I ω := by
      rw [← WithTop.coe_le_coe, hcap]
      exact le_min (WithTop.coe_le_coe.2 hσn) ((coe_le_toWT_iff _ _).2 hσT.le)
    have huQ : Q < u := by
      have h : (Q : ℝ≥0∞) < u := by
        refine lt_of_lt_of_le ?_ (not_lt.1 hu)
        simpa only [Q, imageStops, Clock7.imageStop, hω, ↓reduceIte] using hlt
      exact_mod_cast h
    rw [min_eq_right hge, min_eq_right huQ.le, hQ, hinvσ]

/-- On a good sample the optional-time tuple is exactly the tuple at the stopped inverse. -/
theorem cappedPoint_eq (ha : 0 < a) (hab : a < b)
    (hg : Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω) (hω : ω ∈ G) (n : ℕ) (u : ℝ≥0) :
    cappedPoint xL a b G S W B VL VR e n u ω =
      (rCoordAt a 0 (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
        (invClk (rate a (W · ω) (VR 0 · ω)) (min u (imageStops a G S W B VL VR e n ω) : ℝ≥0)).toNNReal,
       B (invClk (rate a (W · ω) (VR 0 · ω)) (min u (imageStops a G S W B VL VR e n ω) : ℝ≥0)).toNNReal ω) := by
  simp only [cappedPoint, Adapt8.stoppedCoords, rCoord, hω, ↓reduceIte,
    min_cap_inverse_localizer ha hab hg hω n u]

/-- Every stopped image time is strictly before the raw image horizon on good samples. -/
theorem min_imageStop_lt (ha : 0 < a) (hab : a < b)
    (hg : Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω) (hω : ω ∈ G) (n : ℕ) (u : ℝ≥0) :
    ((min u (imageStops a G S W B VL VR e n ω) : ℝ≥0) : ℝ≥0∞) <
      newHorizon a (W · ω) (VR 0 · ω) (sepTime (W · ω) (VR 0 · ω) (e ω)) := by
  refine (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt ?_
  have hsep : SepUpTo (W · ω) (VR 0 · ω)
    (sepTime (W · ω) (VR 0 · ω) (e ω)) := (hg.data ha hab).sep
  simpa only [imageStops, Clock7.imageStop, hω, ↓reduceIte] using
    (clk_lt_newHorizon' hsep ha (hg.loc_lt (G := G) n)).2

/-- The clock coordinate of the optional-time tuple is exactly the stopped image time. -/
theorem clock_cappedPoint (ha : 0 < a) (hab : a < b)
    (hg : Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω) (hω : ω ∈ G) (n : ℕ) (u : ℝ≥0) :
    (cappedPoint xL a b G S W B VL VR e n u ω).1.2.2.2.2 =
      (min u (imageStops a G S W B VL VR e n ω) : ℝ≥0) := by
  have hsep : SepUpTo (W · ω) (VR 0 · ω)
    (sepTime (W · ω) (VR 0 · ω) (e ω)) := (hg.data ha hab).sep
  have hu := min_imageStop_lt ha hab hg hω n u
  obtain ⟨s, -, -, -, hm, -⟩ := newTime_spec hsep ha hu
  rw [cappedPoint_eq ha hab hg hω]
  simp only [rCoordAt, Real.coe_toNNReal _ hm.1]
  exact clk_invClk_of_lt hsep ha hu

end InteractingSLE.Sec5.TwoMark.Noise10
