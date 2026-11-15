/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalCollision

/-!
# The actual retained word has an admissible interior seed

Packet PROVE-RETPLUMB. Continuity of the inverse chart and the interior second
tip make its two incident side intervals nonempty. Their heights are the
prescribed new-slit heights, so the time-zero force threshold cannot occur.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7 Sec7.Lemma76G

/-- The second tip lies strictly between the images of its two real base ends. -/
theorem zoneData_second_tip_strict {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    {x₁ x₂ : ℝ} {u r : ℝ≥0} {φ ψ : ℂ → ℂ} {l : ℂ → ℝ}
    (hs : IsSetting α ζ₁ x₁ u β ζ₂ x₂ r φ ψ l) :
    (zoneData φ α u β r).L₂ < 0 ∧ 0 < (zoneData φ α u β r).R₂ := by
  let z := zoneData φ α u β r
  have hz := hs.zoneData_good
  have hL : z.L₂ ≤ 0 := hz.L₂_le
  have hR : 0 ≤ z.R₂ := hz.M₂_le
  have hc : Continuous fun w : ℝ => ψ (w : ℂ) :=
    hs.ψc.comp_continuous Complex.continuous_ofReal (fun _ => by simp [QuantumZipper.Hbar])
  have h0 : ψ ((0 : ℝ) : ℂ) ∈ QuantumZipper.H := by
    rw [Complex.ofReal_zero, hs.ψ0]
    exact hs.hpair.2.2.1
  obtain ⟨ε, hε, hnear⟩ := Metric.mem_nhds_iff.1
    ((QuantumZipper.isOpen_H.preimage hc).mem_nhds h0)
  have hnear' : ∀ w : ℝ, |w| < ε → ψ (w : ℂ) ∈ QuantumZipper.H := by
    intro w hw
    exact hnear (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hw)
  constructor
  · apply lt_of_le_of_ne hL
    intro he
    have hw : ψ ((-ε / 2 : ℝ) : ℂ) ∈ QuantumZipper.H :=
      hnear' _ (by rw [abs_of_neg (by linarith)]; linarith)
    have hr := congrArg Complex.im (hs.zone₀_of_lt (w := -ε / 2) (by change -ε / 2 < z.L₂; rw [he]; linarith)).1
    have hr' : (ψ ((-ε / 2 : ℝ) : ℂ)).im = 0 := by simpa only [Complex.ofReal_im] using hr
    exact (ne_of_gt (show 0 < (ψ ((-ε / 2 : ℝ) : ℂ)).im from hw)) hr'
  · apply lt_of_le_of_ne hR
    intro he
    have hL₁ : 0 < z.L₁ := by
      have ht : z.R₂ < z.L₁ := hs.R₂_lt_L₁
      rw [← he] at ht
      exact ht
    let w := min (ε / 2) (z.L₁ / 2)
    have hw0 : 0 < w := lt_min (by linarith) (by linarith)
    have hwε : w < ε := (min_le_left _ _).trans_lt (by linarith)
    have hwL : w < z.L₁ := (min_le_right _ _).trans_lt (by linarith)
    have hw := hnear' w (by rwa [abs_of_pos hw0])
    have hr := congrArg Complex.im (hs.zone₁_of_mem (w := w)
      (by change z.R₂ < w; rw [← he]; exact hw0) hwL).1
    have hr' : (ψ (w : ℂ)).im = 0 := by simpa only [Complex.ofReal_im] using hr
    exact (ne_of_gt (show 0 < (ψ (w : ℂ)).im from hw)) hr'

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- At a good disjoint pair the two incident heights of the retained word are
the new second-slit heights, including when the first cutoff is zero. -/
theorem retWordAt_incident_heights {G : ℝ≥0 → Set Ω}
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    {x₁ x₂ κ θ₁ θ₂ : ℝ} {c₀ : BoundaryWord} {ω : Ω}
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₁ : IsPathGood (η₁' ω) (ζ₁ ω) x₁) (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hx : x₂ < x₁)
    (hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) :
    PiecewiseConstantBoundaryData.leftLim
        (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω).fn 0 =
        -sleLambda κ - θ₂ * QuantumZipper.chiC κ ∧
      PiecewiseConstantBoundaryData.rightLim
        (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω).fn 0 =
        sleLambda κ - θ₂ * QuantumZipper.chiC κ := by
  obtain ⟨hE, hs⟩ := isSetting_of_retData hd hG hp₁ hp₂ hx (fun _ _ => rfl)
    (fun _ _ => rfl) hpair
  have hw := wordM_eq_of_setting hd hE hs (fun _ _ => rfl) (fun _ _ => rfl) hc₀
    (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
    (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)
  obtain ⟨hL, hR⟩ := zoneData_second_tip_strict hs
  change _ ∧ _
  simp only [retWordAt, hw]
  constructor
  · apply Sec4.leftLim_eq_of_forall hL
    intro t ht
    rw [BoundaryWord.trunc_fn]
    exact ZW.fn_side₁ hs.zoneData_good hc₀ ht.1 ht.2
  · apply Sec4.rightLim_eq_of_forall hR
    intro t ht
    rw [BoundaryWord.trunc_fn]
    exact ZW.fn_side₂ hs.zoneData_good hc₀ ht.1 ht.2

end InteractingSLE.Restart.RetAux79
