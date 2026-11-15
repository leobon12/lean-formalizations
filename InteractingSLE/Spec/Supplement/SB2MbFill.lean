/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MaSet
import InteractingSLE.Spec.Supplement.SB2LuLift
import InteractingSLE.Spec.Sec7.R6FdLand
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov

/-!
# The fill correspondence from the real points of the actual tail and its lift

Packet PROVE-T14-SB2LIFT (round 16; `FillCorr`, item 5 of handoff §R14.2). Beyond `R` the closed filled prefixes of
the two walks are read from **real points only**, so no conformal transport of hulls through the upper chart is
needed:

* **`mem_closure_fillH_image_iff`**: for a curve `β` with a real point `β u₀ = a` and a real `x > a` off `β([0, T])`,
  `x` lies in the closure of `fill β([0, T])` iff `β([0, T])` has a real point right of `x`. One direction is
  `R6Fd.exists_real_ge_of_mem_closure_fillH`; the other is `YuanCharacterisation.mem_closure_fillH_of_lt_of_lt`;
* `RayChartLim`, `back_of_rayChartLim`: the inverse chart has the boundary value `y` at `ι y − m` for `y > R`. A real
  point `ι y` of the lift curve then reads the actual point `y` (the converse of SB2LIFTSET's ray clause
  `lift_eq_of_rayChartInj`);
* `LiftCurveData`, `liftCurveData_of`: the curve facts (both curves continuous in `ℍ̄`, start points, the head's real
  points `≤ R`, the ray clause and its converse);
* **`mem_closure_fillH_lift_iff`**: for `x > R`, `x ∈ closure (fill β₀([0, t_L + s])) ↔
  ι x ∈ closure (fill γ([0, s]))`. The real points of the tail beyond `R` and those of `γ` beyond `0` correspond
  through `ι`, and the head contributes none. Points on the curves need the input `OnCurveFill` (they are in the
  closed fill);
* **`fillCorr_of_curves`**: `FillCorr` at a pair of launches when the prefixes of both runs (after the launch, and at
  the times of the piece) are initial segments of `β₀` and of the lift curve `γ` with matching lengths.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W

/-! ### Real points and closed fills of curves -/

theorem image_toNNReal_Icc (β : ℝ≥0 → ℂ) (T : ℝ≥0) :
    (fun r : ℝ => β r.toNNReal) '' Icc 0 (T : ℝ) = β '' Icc 0 T := by
  ext z
  constructor
  · rintro ⟨r, ⟨-, hT⟩, rfl⟩
    exact ⟨r.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hT⟩, rfl⟩
  · rintro ⟨t, ⟨-, ht⟩, rfl⟩
    exact ⟨t, ⟨t.2, NNReal.coe_le_coe.2 ht⟩, by simp⟩

/-- **A real point right of a real point of a curve, off the curve, is in the closed fill iff the curve has a real point
further right.** -/
theorem mem_closure_fillH_image_iff {β : ℝ≥0 → ℂ} (hβ : Continuous β) (hβH : ∀ t, β t ∈ Hbar) {T u₀ : ℝ≥0}
    (hu₀ : u₀ ≤ T) {a : ℝ} (ha : β u₀ = a) {x : ℝ} (hax : a < x) (hxP : (x : ℂ) ∉ β '' Icc 0 T) :
    (x : ℂ) ∈ closure (fillH (β '' Icc 0 T)) ↔ ∃ t ∈ Icc 0 T, (β t).im = 0 ∧ x < (β t).re := by
  constructor
  · intro hx
    have hc : IsCompact (β '' Icc 0 T) := isCompact_Icc.image hβ
    have hsub : β '' Icc 0 T ⊆ Hbar := by
      rintro _ ⟨t, -, rfl⟩
      exact hβH t
    obtain ⟨z, ⟨t, ht, rfl⟩, hz0, hxz⟩ := Sec7.R6Fd.exists_real_ge_of_mem_closure_fillH hc hsub hx
    refine ⟨t, ht, hz0, lt_of_le_of_ne hxz fun h => hxP ⟨t, ht, ?_⟩⟩
    exact Complex.ext (by rw [Complex.ofReal_re]; exact h.symm) (by rw [Complex.ofReal_im]; exact hz0)
  · rintro ⟨t, ht, ht0, hxt⟩
    rw [← image_toNNReal_Icc β T] at hxP ⊢
    refine YuanCharacterisation.mem_closure_fillH_of_lt_of_lt (u₁ := (u₀ : ℝ)) (u₂ := (t : ℝ))
      (hβ.comp continuous_real_toNNReal).continuousOn (fun r _ => hβH _) ⟨u₀.2, NNReal.coe_le_coe.2 hu₀⟩
      ⟨t.2, NNReal.coe_le_coe.2 ht.2⟩ ?_ ?_ ?_ ?_ hxP
    · simp [ha]
    · simpa using ht0
    · simpa [ha] using hax
    · simpa using hxt

/-! ### The lift curve reads the ray back -/

/-- **The inverse chart has the boundary value `y` at `ι y − m`** for every `y > R`. -/
def RayChartLim (c : Chart) (R m : ℝ) (ι : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, R < y → Tendsto c.2.1 (𝓝[H] ((ι y - m : ℝ) : ℂ)) (𝓝 (y : ℂ))

/-- **A real point `ι y` of the lift curve reads the actual point `y`.** -/
theorem back_of_rayChartLim {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {ι : ℝ → ℝ}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hlim : RayChartLim c R m ι) :
    ∀ s, ∀ y : ℝ, R < y → γ s = ι y → β₀ (tL + s) = y := by
  intro s y hy hs
  have h1 := hγ.2.2.2 s
  have hw : γ s - (m : ℂ) = ((ι y - m : ℝ) : ℂ) := by
    rw [hs]
    push_cast
    ring
  rw [hw] at h1
  have : (𝓝[H] (((ι y - m : ℝ)) : ℂ)).NeBot :=
    GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ (((ι y - m : ℝ)) : ℂ).im by simp)
  exact tendsto_nhds_unique h1 (hlim y hy)

/-- **The curve facts of the actual walk `β₀` and its tail lift `γ`.** -/
structure LiftCurveData (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (R : ℝ) (ι : ℝ → ℝ) : Prop where
  contβ : Continuous β₀
  memβ : ∀ t, β₀ t ∈ Hbar
  contγ : Continuous γ
  memγ : ∀ t, γ t ∈ Hbar
  base : β₀ tL = R
  zero : γ 0 = 0
  head : ∀ t ≤ tL, (β₀ t).im = 0 → (β₀ t).re ≤ R
  ray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x
  back : ∀ s, ∀ y : ℝ, R < y → γ s = ι y → β₀ (tL + s) = y

/-- **The curve facts from the lift curve and the ray of the upper chart.** -/
theorem liftCurveData_of {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {ι : ℝ → ℝ}
    (hβ : Supp9B.IsProperCurve β₀) (hγ : IsTailLiftCurve c R m β₀ tL γ)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (hinj : RayChartInj c R m ι) (hlim : RayChartLim c R m ι) :
    LiftCurveData β₀ γ tL R ι where
  contβ := hβ.1
  memβ := hβ.2.2.1
  contγ := hγ.2.1.1
  memγ := hγ.2.1.2.2.1
  base := hγ.1
  zero := hγ.2.2.1
  head t ht h0 := hhead t ht _ (Complex.ext (by simp) (by simp [h0]))
  ray := lift_eq_of_rayChartInj hγ hinj
  back := back_of_rayChartLim hγ hlim

variable {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R : ℝ} {ι : ℝ → ℝ}

/-- **The closed fills of the actual prefix and of its lift agree along the ray** (`x > R`), given that points on the
curves are in the closed fills. -/
theorem mem_closure_fillH_lift_iff {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hD : LiftCurveData β₀ γ tL R ι) {s : ℝ≥0} {x : ℝ} (hx : R < x)
    (hon₁ : (x : ℂ) ∈ β₀ '' Icc 0 (tL + s) → (x : ℂ) ∈ closure (fillH (β₀ '' Icc 0 (tL + s))))
    (hon₂ : ((ι x : ℝ) : ℂ) ∈ γ '' Icc 0 s → ((ι x : ℝ) : ℂ) ∈ closure (fillH (γ '' Icc 0 s))) :
    (x : ℂ) ∈ closure (fillH (β₀ '' Icc 0 (tL + s))) ↔ ((ι x : ℝ) : ℂ) ∈ closure (fillH (γ '' Icc 0 s)) := by
  have hιx : 0 < ι x := hι.map_base ▸ hι.mono (mem_Ici.2 le_rfl) (mem_Ici.2 hx.le) hx
  have htail : ∀ t, (β₀ t).im = 0 → R < (β₀ t).re → tL < t := fun t h0 hR => by
    by_contra h
    exact absurd (hD.head t (not_lt.1 h) h0) (not_le.2 hR)
  have hof : ∀ t, (β₀ t).im = 0 → β₀ t = (((β₀ t).re : ℝ) : ℂ) := fun t h0 =>
    Complex.ext (by simp) (by simp [h0])
  have hmem : (x : ℂ) ∈ β₀ '' Icc 0 (tL + s) ↔ ((ι x : ℝ) : ℂ) ∈ γ '' Icc 0 s := by
    constructor
    · rintro ⟨t, ht, hxt⟩
      have h0 : (β₀ t).im = 0 := by rw [hxt]; simp
      have hre : (β₀ t).re = x := by rw [hxt]; simp
      have htL := htail t h0 (hre ▸ hx)
      obtain ⟨u, rfl⟩ : ∃ u, t = tL + u := ⟨t - tL, (add_tsub_cancel_of_le htL.le).symm⟩
      exact ⟨u, ⟨zero_le, (add_le_add_iff_left tL).1 ht.2⟩, hD.ray u x hx hxt⟩
    · rintro ⟨u, hu, hγu⟩
      exact ⟨tL + u, ⟨zero_le, (add_le_add_iff_left tL).2 hu.2⟩, hD.back u x hx hγu⟩
  by_cases hon : (x : ℂ) ∈ β₀ '' Icc 0 (tL + s)
  · exact ⟨fun _ => hon₂ (hmem.1 hon), fun _ => hon₁ hon⟩
  have hon' : ((ι x : ℝ) : ℂ) ∉ γ '' Icc 0 s := fun h => hon (hmem.2 h)
  rw [mem_closure_fillH_image_iff hD.contβ hD.memβ le_self_add hD.base hx hon,
    mem_closure_fillH_image_iff hD.contγ hD.memγ zero_le (hD.zero.trans Complex.ofReal_zero.symm) hιx hon']
  constructor
  · rintro ⟨t, ht, h0, hxt⟩
    have htL := htail t h0 (hx.trans hxt)
    obtain ⟨u, rfl⟩ : ∃ u, t = tL + u := ⟨t - tL, (add_tsub_cancel_of_le htL.le).symm⟩
    have hR' : R < (β₀ (tL + u)).re := hx.trans hxt
    have hγu := hD.ray u _ hR' (hof _ h0)
    refine ⟨u, ⟨zero_le, (add_le_add_iff_left tL).1 ht.2⟩, by rw [hγu]; simp, ?_⟩
    rw [hγu, Complex.ofReal_re]
    exact hι.mono (mem_Ici.2 hx.le) (mem_Ici.2 hR'.le) hxt
  · rintro ⟨u, hu, h0, hxu⟩
    obtain ⟨y, hRy, hy⟩ := hι.surj (γ u).re (hιx.le.trans hxu.le)
    have hyR : R < y := by
      rcases eq_or_lt_of_le hRy with h | h
      · rw [← h, hι.map_base] at hy
        linarith
      · exact h
    have hγu : γ u = ((ι y : ℝ) : ℂ) := by
      rw [hy]
      exact Complex.ext (by simp) (by simp [h0])
    have hβu := hD.back u y hyR hγu
    refine ⟨tL + u, ⟨zero_le, (add_le_add_iff_left tL).2 hu.2⟩, by rw [hβu]; simp, ?_⟩
    rw [hβu, Complex.ofReal_re]
    by_contra hle
    have := hι.mono.monotoneOn (mem_Ici.2 hRy) (mem_Ici.2 hx.le) (not_lt.1 hle)
    rw [hy] at this
    linarith

/-! ### `FillCorr` from initial segments -/

/-- **Points on the two curves beyond `a` are in the closed fills** of the initial segments of lengths `t_L + s` and
`s`. -/
def OnCurveFill (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (ι : ℝ → ℝ) (a : ℝ) (s : ℝ≥0) : Prop :=
  ∀ x : ℝ, a < x →
    ((x : ℂ) ∈ β₀ '' Icc 0 (tL + s) → (x : ℂ) ∈ closure (fillH (β₀ '' Icc 0 (tL + s)))) ∧
    (((ι x : ℝ) : ℂ) ∈ γ '' Icc 0 s → ((ι x : ℝ) : ℂ) ∈ closure (fillH (γ '' Icc 0 s)))

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ}

/-- **`FillCorr` at a pair of launches from initial segments of the two curves**: after the launch, and at the times of
the piece, the prefixes of the actual and the relative run are `β₀([0, t_L + s])` and `γ([0, s])` for matching `s`. -/
theorem fillCorr_of_curves {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hD : LiftCurveData β₀ γ tL R ι)
    (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hP : ∃ s, SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1) = β₀ '' Icc 0 (tL + s) ∧
      SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1) = γ '' Icc 0 s ∧
      OnCurveFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) s)
    (hpart₁ : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → ∃ s,
      partPrefix κ b₁ J₁ θ D₁ n₁ r = β₀ '' Icc 0 (tL + s) ∧
      OnCurveFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) s ∧
      ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ n₂) ∧ partPrefix κ b₂ J₂ θ D₂ n₂ r' = γ '' Icc 0 s)
    (hpart₂ : ∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) → ∃ s,
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = γ '' Icc 0 s ∧
      OnCurveFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) s ∧
      ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧ partPrefix κ b₁ J₁ θ D₁ n₁ r = β₀ '' Icc 0 (tL + s)) :
    FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι := by
  have key : ∀ s, OnCurveFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) s →
      ∀ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) < x →
        ((x : ℂ) ∈ closure (fillH (β₀ '' Icc 0 (tL + s))) ↔
          ((ι x : ℝ) : ℂ) ∈ closure (fillH (γ '' Icc 0 s))) :=
    fun s hs x hx => mem_closure_fillH_lift_iff hι hD (hRa.trans_lt hx) (hs x hx).1 (hs x hx).2
  unfold FillCorr
  refine ⟨fun x hx => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨s, h1, h2, hs⟩ := hP
    rw [h1, h2]
    exact key s hs x hx
  · rintro ⟨r, hr0, hr, hxr⟩
    obtain ⟨s, h1, hs, r', hr0', hr', h2⟩ := hpart₁ r hr0 hr
    rw [h1] at hxr
    exact ⟨r', hr0', hr', by rw [h2]; exact (key s hs x hx).1 hxr⟩
  · rintro ⟨r', hr0', hr', hxr⟩
    obtain ⟨s, h2, hs, r, hr0, hr, h1⟩ := hpart₂ r' hr0' hr'
    rw [h2] at hxr
    exact ⟨r, hr0, hr, by rw [h1]; exact (key s hs x hx).2 hxr⟩

end InteractingSLE.Theorem14.SB.Lk
