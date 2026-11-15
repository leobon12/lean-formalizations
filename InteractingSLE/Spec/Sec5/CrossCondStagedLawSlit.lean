/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedLawSide

/-!
# The staged cross-conditioning law: the slit-side comparison with born marks

Packet PROVE-CROSSCOND-STAGED3 (S2, the prefix side of the union datum). The root layer
(`GlueImg.tendsto_imgChart_slit_left_of_flow`) compares the flow-side and image-side candidates on the image slit
when both words carry the constant side heights `∓λ` there. A staged prefix carries the force points created at its
switches on its sides. Here:

* `slit_left_limits`, `slit_right_limits`: the data-free part of the root lemmas (at every point of the image slit `Θ`
  has a real limit of the same sign on the flow slit, and the branch of `arg Θ′` tends to `0`);
* `forceBoundaryData_eq_of_neg`, `forceBoundaryData_eq_of_nonneg`: force data agree when the marks on the relevant
  side are in the same position relative to the two points;
* `IsBornPairL`, `IsBornPairR`: a flow-chart mark and an image-chart mark are the marks born at the same switch (base
  images of the shifted chains), or both outer marks;
* **`tendsto_slit_left_of_bornWord`**, **`tendsto_slit_right_of_bornWord`**: for words with equal weights and paired
  marks, at every image slit point that is not an image mark, the flow-chart candidate read through `Θ` and the
  image-chart candidate have the same boundary limit (`(u_A ∘ Θ − χ L_A) − (u − χ L_B) → 0`). This is the prefix side
  of `HasUnionWordBoundary` for a staged prefix (the stage mean is `u_A ∘ f_t − χ arg f_t′` exactly).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)
open QuantumZipper.RS (shiftDrive)
open scoped Real

namespace InteractingSLE.Sec5.CrossCond.StagedLaw

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg
open MartChar.RealFlow Restart.RetAux79

section Slit

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

open CrossCond.Word49 (junL junR)

/-- **The left side of the image slit, without data** (the geometric part of
`GlueImg.tendsto_imgChart_slit_left_of_flow`): at every `x ∈ (chartAL W′ T, 0)`, `Θ` tends to a negative real point
of the flow slit and the branch of `arg Θ′` tends to `0`. -/
theorem slit_left_limits {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0) (hjL : 0 < rightImg Wβ 0 s - Wβ s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {x : ℝ} (hxL0 : chartAL W' T < x) (hx0 : x < 0) :
    ∃ x₁ : ℝ, x₁ < 0 ∧ chartAL Wα t < x₁ ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ)) ∧
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hAR := chartAR_nonneg hW' hT.le (W' := W')
  have hε : 0 < -junL Wβ s := by
    rw [junL, neg_div, neg_neg]; exact div_pos one_pos hjL
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 (continuous_extendFrom_ofReal hη' hW' hW'0 hT.le)
    (chartAL W' T) _ hε
  have hphys : ∀ x' : ℝ, chartAL W' T - δ < x' → x' < chartAL W' T →
      extendFrom H (fwdMapInv W' T) x' = ((extendFrom H (fwdMapInv W' T) x').re : ℂ) ∧
      (extendFrom H (fwdMapInv W' T) x').re < 0 ∧ junL Wβ s < (extendFrom H (fwdMapInv W' T) x').re := by
    intro x' h1 h2
    obtain ⟨him, hre⟩ := re_extendFrom_neg_of_lt_chartAL hη' hη'p hW' hW'0 hT h2
    refine ⟨Complex.ext (by simp) (by simp [him]), hre, ?_⟩
    have hd := hcont x' (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [extendFrom_chartAL_eq_zero hη' hη'p hW' hW'0 hT, dist_zero_right] at hd
    have h3 := Complex.abs_re_le_norm (extendFrom H (fwdMapInv W' T) x')
    have h4 := neg_le_abs (extendFrom H (fwdMapInv W' T) x').re
    linarith
  have hR2c : ∀ x' : ℝ, chartAL W' T - δ < x' → x' < chartAL W' T →
      (∃ p : ℝ, p < 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
        Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
    intro x' h1 h2
    obtain ⟨he, hneg, hj⟩ := hphys x' h1 h2
    exact imgTheta_tendsto_of_extendFrom_neg hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hB hKs hjL hW' hW'0 hT.le hη' hη'p
      he hneg hj
  set I : Set ℝ := Ioo (chartAL W' T - δ) 0 with hIdef
  have hlim : ∀ x' ∈ I, (∃ p : ℝ, p ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
      ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (2 * π * k)) := by
    intro x' hx'
    rcases lt_trichotomy x' (chartAL W' T) with h | h | h
    · obtain ⟨⟨p, hp, hΘp⟩, ha⟩ := hR2c x' hx'.1 h
      exact ⟨⟨p, hp.ne, hΘp⟩, 0, by simpa using ha⟩
    · rw [h]
      exact imgTheta_limits_of_extendFrom_eq_zero hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hW' hW'0 hT.le hη' hGc hdisj
        hdis hK' (extendFrom_chartAL_eq_zero hη' hη'p hW' hW'0 hT)
    · obtain ⟨-, -, -, -, x₁, hx₁0, -, -, hΘ, hk⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hW'
        hW'0 hT hη' hη'p hGc hdisj hdis hK' htip h (by linarith [hx'.2]) hx'.2.ne
      exact ⟨⟨x₁, hx₁0, hΘ⟩, hk⟩
  have hx₀ : chartAL W' T - δ / 2 ∈ I := ⟨by linarith, by linarith⟩
  obtain ⟨⟨p₀, hp₀, hΘ₀⟩, ha₀⟩ := hR2c (chartAL W' T - δ / 2) (by linarith) (by linarith)
  have hxI : x ∈ I := ⟨by linarith, hx0⟩
  obtain ⟨-, -, -, -, x₁, -, hx₁L, -, hΘ, -⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs
    hW' hW'0 hT hη' hη'p hGc hdisj hdis hK' htip hxL0 (by linarith) hx0.ne
  exact ⟨x₁, neg_of_forall_tendsto_real isPreconnected_Ioo (fun x' hx' => (hlim x' hx').1) hx₀ hp₀ hΘ₀ hxI hΘ,
    hx₁L, hΘ, tendsto_zero_of_forall_tendsto_two_pi_int isPreconnected_Ioo (fun x' hx' => (hlim x' hx').2) hx₀ ha₀
      hxI⟩

/-- **The right side of the image slit, without data** (mirror of `slit_left_limits`). -/
theorem slit_right_limits {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0) (hjR : -rightImg (fun r => -Wβ r) 0 s - Wβ s < 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {x : ℝ} (hxR0 : x < chartAR W' T) (hx0 : 0 < x) :
    ∃ x₁ : ℝ, 0 < x₁ ∧ x₁ < chartAR Wα t ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ)) ∧
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hAL := chartAL_nonpos hW' hT.le (W' := W')
  have hε : 0 < junR Wβ s := by
    rw [junR, neg_div, ← div_neg]; exact div_pos one_pos (neg_pos.2 hjR)
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 (continuous_extendFrom_ofReal hη' hW' hW'0 hT.le)
    (chartAR W' T) _ hε
  have hphys : ∀ x' : ℝ, chartAR W' T < x' → x' < chartAR W' T + δ →
      extendFrom H (fwdMapInv W' T) x' = ((extendFrom H (fwdMapInv W' T) x').re : ℂ) ∧
      0 < (extendFrom H (fwdMapInv W' T) x').re ∧ (extendFrom H (fwdMapInv W' T) x').re < junR Wβ s := by
    intro x' h1 h2
    obtain ⟨him, hre⟩ := re_extendFrom_pos_of_chartAR_lt hη' hη'p hW' hW'0 hT h1
    refine ⟨Complex.ext (by simp) (by simp [him]), hre, ?_⟩
    have hd := hcont x' (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [extendFrom_chartAR_eq_zero hη' hη'p hW' hW'0 hT, dist_zero_right] at hd
    have h3 := Complex.abs_re_le_norm (extendFrom H (fwdMapInv W' T) x')
    have h4 := le_abs_self (extendFrom H (fwdMapInv W' T) x').re
    linarith
  have hR2c : ∀ x' : ℝ, chartAR W' T < x' → x' < chartAR W' T + δ →
      (∃ p : ℝ, 0 < p ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
        Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
    intro x' h1 h2
    obtain ⟨he, hpos, hj⟩ := hphys x' h1 h2
    exact imgTheta_tendsto_of_extendFrom_pos hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hB hKs hjR hW' hW'0 hT.le hη' hη'p
      he hpos hj
  set I : Set ℝ := Ioo 0 (chartAR W' T + δ) with hIdef
  have hlim : ∀ x' ∈ I, (∃ p : ℝ, p ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
      ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (2 * π * k)) := by
    intro x' hx'
    rcases lt_trichotomy x' (chartAR W' T) with h | h | h
    · obtain ⟨-, -, -, -, x₁, hx₁0, -, -, hΘ, hk⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hW'
        hW'0 hT hη' hη'p hGc hdisj hdis hK' htip (by linarith [hx'.1]) h hx'.1.ne'
      exact ⟨⟨x₁, hx₁0, hΘ⟩, hk⟩
    · rw [h]
      exact imgTheta_limits_of_extendFrom_eq_zero hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hW' hW'0 hT.le hη' hGc hdisj
        hdis hK' (extendFrom_chartAR_eq_zero hη' hη'p hW' hW'0 hT)
    · obtain ⟨⟨p, hp, hΘp⟩, ha⟩ := hR2c x' h hx'.2
      exact ⟨⟨p, hp.ne', hΘp⟩, 0, by simpa using ha⟩
  have hx₀ : chartAR W' T + δ / 2 ∈ I := ⟨by linarith, by linarith⟩
  obtain ⟨⟨p₀, hp₀, hΘ₀⟩, ha₀⟩ := hR2c (chartAR W' T + δ / 2) (by linarith) (by linarith)
  have hxI : x ∈ I := ⟨hx0, by linarith⟩
  obtain ⟨-, -, -, -, x₁, -, -, hx₁R, hΘ, -⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs
    hW' hW'0 hT hη' hη'p hGc hdisj hdis hK' htip (by linarith) hxR0 hx0.ne'
  exact ⟨x₁, pos_of_forall_tendsto_real isPreconnected_Ioo (fun x' hx' => (hlim x' hx').1) hx₀ hp₀ hΘ₀ hxI hΘ,
    hx₁R, hΘ, tendsto_zero_of_forall_tendsto_two_pi_int isPreconnected_Ioo (fun x' hx' => (hlim x' hx').2) hx₀ ha₀
      hxI⟩

end Slit

/-! ### Force data on the slit with born marks -/

section BornWord

variable {κ : ℝ} {nL nR nL' nR' : ℕ}

/-- Two force data agree at negative points with the same left marks on their right. -/
theorem forceBoundaryData_eq_of_neg (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (ρR' : Fin nR' → ℝ) {vL vL' : Fin nL → ℝ}
    (vR : Fin nR → ℝ) (vR' : Fin nR' → ℝ) {x₁ x : ℝ} (hx₁ : x₁ < 0) (hx : x < 0)
    (h : ∀ i, x₁ < vL i ↔ x < vL' i) :
    forceBoundaryData κ ρL ρR vL vR x₁ = forceBoundaryData κ ρL ρR' vL' vR' x := by
  simp only [forceBoundaryData, hx₁, hx, ↓reduceIte]
  congr 2
  exact Finset.sum_congr (by ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, h i]) fun _ _ => rfl

/-- Two force data agree at nonnegative points with the same right marks on their left. -/
theorem forceBoundaryData_eq_of_nonneg (ρL : Fin nL → ℝ) (ρL' : Fin nL' → ℝ) (ρR : Fin nR → ℝ)
    (vL : Fin nL → ℝ) (vL' : Fin nL' → ℝ) {vR vR' : Fin nR → ℝ} {x₁ x : ℝ} (hx₁ : 0 ≤ x₁) (hx : 0 ≤ x)
    (h : ∀ j, vR j ≤ x₁ ↔ vR' j ≤ x) :
    forceBoundaryData κ ρL ρR vL vR x₁ = forceBoundaryData κ ρL' ρR vL' vR' x := by
  simp only [forceBoundaryData, not_lt.2 hx₁, not_lt.2 hx, ↓reduceIte]
  congr 2
  exact Finset.sum_congr (by ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, h j]) fun _ _ => rfl

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- **Paired left marks.** A left mark `v` of a flow-chart word and a left mark `v'` of an image-chart word are paired
when both are the left base images of the chains shifted at a switch (flow time `a`, image time `A`, `η' A = Ψ(α a)`:
the left mark born at the switch, flowed to the present), or both lie at or left of the left base image of the whole
slit. -/
def IsBornPairL (Wα : ℝ → ℝ) (α : ℝ → ℂ) (t : ℝ) (Wβ : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (η' : ℝ → ℂ) (T : ℝ)
    (v v' : ℝ) : Prop :=
  (∃ a A : ℝ, 0 < a ∧ a < t ∧ 0 < A ∧ A < T ∧ η' A = revChart Wβ s (α a) ∧
      v = chartAL (shiftDrive Wα a) (t - a) ∧ v' = chartAL (shiftDrive W' A) (T - A)) ∨
    (v ≤ chartAL Wα t ∧ v' ≤ chartAL W' T)

/-- **Paired right marks** (mirror of `IsBornPairL`). -/
def IsBornPairR (Wα : ℝ → ℝ) (α : ℝ → ℂ) (t : ℝ) (Wβ : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (η' : ℝ → ℂ) (T : ℝ)
    (v v' : ℝ) : Prop :=
  (∃ a A : ℝ, 0 < a ∧ a < t ∧ 0 < A ∧ A < T ∧ η' A = revChart Wβ s (α a) ∧
      v = chartAR (shiftDrive Wα a) (t - a) ∧ v' = chartAR (shiftDrive W' A) (T - A)) ∨
    (chartAR Wα t ≤ v ∧ chartAR W' T ≤ v')

/-- **The candidate on the left side of the image slit, with born marks.** Let the flow-chart word (marks `vL`, `vR`)
and the image-chart word (marks `vL'`, `vR'`) have the same left weights and paired left marks (`IsBornPairL`: the
marks born at the switches of a staged prefix and the outer marks). At every point `x ∈ (chartAL W′ T, 0)` of the image
slit that is not an image left mark, the flow-chart candidate read through `Θ` and the image-chart candidate have the
same boundary limit: `(u_A ∘ Θ − χ L_A) − (u − χ L_B) → 0`. -/
theorem tendsto_slit_left_of_bornWord {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0) (hjL : 0 < rightImg Wβ 0 s - Wβ s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {ρR' : Fin nR' → ℝ} {vL vL' : Fin nL → ℝ} {vR : Fin nR → ℝ}
    {vR' : Fin nR' → ℝ} (hvR : ∀ j, 0 ≤ vR j) (hvR' : ∀ j, 0 ≤ vR' j)
    (hpair : ∀ i, IsBornPairL Wα α t Wβ s W' η' T (vL i) (vL' i)) {uA u : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) uA)
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR' vL' vR') (forceJumpSet vL' vR') u) (χ : ℝ)
    {x : ℝ} (hxL0 : chartAL W' T < x) (hx0 : x < 0) (hxm : ∀ i, x ≠ vL' i) :
    Tendsto (fun y => (uA (imgTheta Wα t Wβ s W' T y) -
        χ * (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))).im) -
      (u y - χ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
        (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  obtain ⟨x₁, hx₁0, hx₁L, hΘ, hbr⟩ := slit_left_limits hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hB hKs hjL hW' hW'0 hT
    hη' hη'p hGc hdisj hdis hK' htip hxL0 hx0
  have hxH : extendFrom H (fwdMapInv W' T) x ∈ H :=
    extendFrom_mem_H_of_chartAL_lt hη' hη'p hW' hW'0 hT hxL0 (hx0.trans_le (chartAR_nonneg hW' hT.le))
  have hne : ∀ i, x₁ ≠ vL i ∧ (x₁ < vL i ↔ x < vL' i) := by
    intro i
    rcases hpair i with ⟨a, A, ha, hat, hA, hAT, heA, hv, hv'⟩ | ⟨hv, hv'⟩
    · have hARs := chartAR_nonneg (QuantumZipper.RS.continuous_shiftDrive hW' A) (sub_pos.2 hAT).le
        (W' := shiftDrive W' A)
      have hARf := chartAR_nonneg (QuantumZipper.RS.continuous_shiftDrive hWα a) (sub_pos.2 hat).le
        (W' := shiftDrive Wα a)
      have hx₁ne : x₁ ≠ chartAL (shiftDrive Wα a) (t - a) := by
        intro h
        rcases eq_imgChartA_of_eq_chartA hα hαp hWα hWα0 ht.le hWβ hWβ0 hs hη' hη'p hW' hW'0 hT.le hdisj hK' ha hat
          hA hAT heA hxH hΘ (Or.inl h) with h' | h'
        · exact hxm i (h'.trans hv'.symm)
        · unfold chartAR at hARs; rw [h'] at hx0; unfold chartAR at hx0; linarith
      have hxne : x ≠ chartAL (shiftDrive W' A) (T - A) := hv' ▸ hxm i
      have htr := mem_Ioo_chartA_iff_of_imgTheta hα hαp hWα hWα0 ht.le hWβ hWβ0 hs hη' hη'p hW' hW'0 hT.le hdisj
        hK' htip ha hat hA hAT heA hxH hΘ
      have e1 : (chartAL (shiftDrive Wα a) (t - a) < x₁ ∧ x₁ < chartAR (shiftDrive Wα a) (t - a)) ↔
          chartAL (shiftDrive Wα a) (t - a) < x₁ := ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩
      have e2 : (chartAL (shiftDrive W' A) (T - A) < x ∧ x < chartAR (shiftDrive W' A) (T - A)) ↔
          chartAL (shiftDrive W' A) (T - A) < x := ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩
      rw [e1, e2] at htr
      rw [hv, hv']
      refine ⟨hx₁ne, ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
      · rcases lt_or_gt_of_ne hxne with h | h
        · exact h
        · exact absurd (htr.2 h) (not_lt.2 h1.le)
      · rcases lt_or_gt_of_ne hx₁ne with h | h
        · exact h
        · exact absurd (htr.1 h) (not_lt.2 h1.le)
    · refine ⟨fun h => by linarith, ⟨fun h => by linarith, fun h => by linarith⟩⟩
  have hd := forceBoundaryData_eq_of_neg (κ := κ) ρL ρR ρR' vR vR' hx₁0 hx0 fun i => (hne i).2
  have hx₁J : x₁ ∉ forceJumpSet vL vR := by
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, not_or]
    exact ⟨hx₁0.ne, fun ⟨i, hi⟩ => (hne i).1 hi.symm, fun ⟨j, hj⟩ => by linarith [hvR j]⟩
  have hxJ : x ∉ forceJumpSet vL' vR' := by
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, not_or]
    exact ⟨hx0.ne, fun ⟨i, hi⟩ => hxm i hi.symm, fun ⟨j, hj⟩ => by linarith [hvR' j]⟩
  have hΘH : ∀ y ∈ H, imgTheta Wα t Wβ s W' T y ∈ H := fun y hy => by
    have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT.le hK' hy
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  have hΘ' : Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝[H] (x₁ : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hΘ, eventually_nhdsWithin_of_forall hΘH⟩
  have h1 := (huA.2.2 x₁ hx₁J).comp hΘ'
  have h2 := hu.2.2 x hxJ
  have h := (h1.sub h2).sub (hbr.const_mul χ)
  rw [hd, sub_self, mul_zero, sub_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply, imgBranch]
  ring

/-- **The candidate on the right side of the image slit, with born marks** (mirror of
`tendsto_slit_left_of_bornWord`; same right weights, paired right marks `IsBornPairR`, `x ∈ (0, chartAR W′ T)` not an
image right mark). -/
theorem tendsto_slit_right_of_bornWord {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0) (hjR : -rightImg (fun r => -Wβ r) 0 s - Wβ s < 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {ρL : Fin nL → ℝ} {ρL' : Fin nL' → ℝ} {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ} {vL' : Fin nL' → ℝ}
    {vR vR' : Fin nR → ℝ} (hvL : ∀ i, vL i ≤ 0) (hvL' : ∀ i, vL' i ≤ 0)
    (hpair : ∀ j, IsBornPairR Wα α t Wβ s W' η' T (vR j) (vR' j)) {uA u : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) uA)
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR vL' vR') (forceJumpSet vL' vR') u) (χ : ℝ)
    {x : ℝ} (hxR0 : x < chartAR W' T) (hx0 : 0 < x) (hxm : ∀ j, x ≠ vR' j) :
    Tendsto (fun y => (uA (imgTheta Wα t Wβ s W' T y) -
        χ * (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))).im) -
      (u y - χ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
        (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  obtain ⟨x₁, hx₁0, hx₁R, hΘ, hbr⟩ := slit_right_limits hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hB hKs hjR hW' hW'0 hT
    hη' hη'p hGc hdisj hdis hK' htip hxR0 hx0
  have hxH : extendFrom H (fwdMapInv W' T) x ∈ H :=
    extendFrom_mem_H_of_chartAL_lt hη' hη'p hW' hW'0 hT ((chartAL_nonpos hW' hT.le).trans_lt hx0) hxR0
  have hne : ∀ j, x₁ ≠ vR j ∧ (vR j ≤ x₁ ↔ vR' j ≤ x) := by
    intro j
    rcases hpair j with ⟨a, A, ha, hat, hA, hAT, heA, hv, hv'⟩ | ⟨hv, hv'⟩
    · have hALs := chartAL_nonpos (QuantumZipper.RS.continuous_shiftDrive hW' A) (sub_pos.2 hAT).le
        (W' := shiftDrive W' A)
      have hALf := chartAL_nonpos (QuantumZipper.RS.continuous_shiftDrive hWα a) (sub_pos.2 hat).le
        (W' := shiftDrive Wα a)
      have hx₁ne : x₁ ≠ chartAR (shiftDrive Wα a) (t - a) := by
        intro h
        rcases eq_imgChartA_of_eq_chartA hα hαp hWα hWα0 ht.le hWβ hWβ0 hs hη' hη'p hW' hW'0 hT.le hdisj hK' ha hat
          hA hAT heA hxH hΘ (Or.inr h) with h' | h'
        · unfold chartAL at hALs; rw [h'] at hx0; unfold chartAL at hx0; linarith
        · exact hxm j (h'.trans hv'.symm)
      have hxne : x ≠ chartAR (shiftDrive W' A) (T - A) := hv' ▸ hxm j
      have htr := mem_Ioo_chartA_iff_of_imgTheta hα hαp hWα hWα0 ht.le hWβ hWβ0 hs hη' hη'p hW' hW'0 hT.le hdisj
        hK' htip ha hat hA hAT heA hxH hΘ
      have e1 : (chartAL (shiftDrive Wα a) (t - a) < x₁ ∧ x₁ < chartAR (shiftDrive Wα a) (t - a)) ↔
          x₁ < chartAR (shiftDrive Wα a) (t - a) := ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩
      have e2 : (chartAL (shiftDrive W' A) (T - A) < x ∧ x < chartAR (shiftDrive W' A) (T - A)) ↔
          x < chartAR (shiftDrive W' A) (T - A) := ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩
      rw [e1, e2] at htr
      rw [hv, hv']
      refine ⟨hx₁ne, ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
      · rcases lt_or_gt_of_ne hxne with h | h
        · exact absurd (htr.2 h) (not_lt.2 h1)
        · exact h.le
      · rcases lt_or_gt_of_ne hx₁ne with h | h
        · exact absurd (htr.1 h) (not_lt.2 h1)
        · exact h.le
    · refine ⟨fun h => by linarith, ⟨fun h => by linarith, fun h => by linarith⟩⟩
  have hd := forceBoundaryData_eq_of_nonneg (κ := κ) ρL ρL' ρR vL vL' hx₁0.le hx0.le fun j => (hne j).2
  have hx₁J : x₁ ∉ forceJumpSet vL vR := by
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, not_or]
    exact ⟨hx₁0.ne', fun ⟨i, hi⟩ => by linarith [hvL i], fun ⟨j, hj⟩ => (hne j).1 hj.symm⟩
  have hxJ : x ∉ forceJumpSet vL' vR' := by
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, not_or]
    exact ⟨hx0.ne', fun ⟨i, hi⟩ => by linarith [hvL' i], fun ⟨j, hj⟩ => hxm j hj.symm⟩
  have hΘH : ∀ y ∈ H, imgTheta Wα t Wβ s W' T y ∈ H := fun y hy => by
    have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT.le hK' hy
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  have hΘ' : Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝[H] (x₁ : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hΘ, eventually_nhdsWithin_of_forall hΘH⟩
  have h1 := (huA.2.2 x₁ hx₁J).comp hΘ'
  have h2 := hu.2.2 x hxJ
  have h := (h1.sub h2).sub (hbr.const_mul χ)
  rw [hd, sub_self, mul_zero, sub_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply, imgBranch]
  ring

end BornWord

end InteractingSLE.Sec5.CrossCond.StagedLaw
