import SupercriticalLQGUniqueness.B2.PfeWeyl.WeightedPathChain

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

def uniformGrid (L : ℝ) (N : ℕ) (j : ℕ) : ℝ := (j : ℝ) * (L / (N : ℝ))

theorem uniformGrid_props
    (D : LSCMetric) {P : ℝ → ℂ} {L B δ : ℝ} {N : ℕ}
    (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hN : 0 < N) (hLB : L ≤ B)
    (hBδ : B / (N : ℝ) ≤ δ) :
    Monotone (uniformGrid L N) ∧
      uniformGrid L N 0 = 0 ∧ uniformGrid L N N = L ∧
      (∀ j ≤ N, uniformGrid L N j ∈ Icc 0 L) ∧
      (∀ j < N,
        D.len P (uniformGrid L N j) (uniformGrid L N (j + 1)) ≤
          ENNReal.ofReal δ) := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hL : 0 ≤ L := hP.1
  have hdiv : 0 ≤ L / (N : ℝ) := div_nonneg hL hNr.le
  have hmono : Monotone (uniformGrid L N) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hdiv
  have h0 : uniformGrid L N 0 = 0 := by simp [uniformGrid]
  have hlast : uniformGrid L N N = L := by
    simp only [uniformGrid]
    field_simp
  have hnode (j : ℕ) (hj : j ≤ N) : uniformGrid L N j ∈ Icc 0 L := by
    constructor
    · exact h0 ▸ hmono (Nat.zero_le j)
    · calc
        uniformGrid L N j ≤ uniformGrid L N N := hmono hj
        _ = L := hlast
  refine ⟨hmono, h0, hlast, hnode, ?_⟩
  intro j hj
  have hj1 : j + 1 ≤ N := Nat.succ_le_of_lt hj
  have hleft := hnode j hj.le
  have hright := hnode (j + 1) hj1
  have hstep : uniformGrid L N (j + 1) - uniformGrid L N j = L / (N : ℝ) := by
    simp only [uniformGrid, Nat.cast_add, Nat.cast_one]
    ring
  have hlen := LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn
    hu hleft hright
  change LQGMetric.MetricGeometry.curveLength (D.pt ∘ P)
    (uniformGrid L N j) (uniformGrid L N (j + 1)) ≤ _
  rw [hlen, hstep]
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_div_of_nonneg_right hLB hNr.le).trans hBδ

 

theorem uniformGrid_field_lower
    (D : LSCMetric) (f : C(ℂ, ℝ))
    {K : Set ℂ} {δ θ : ℝ}
    (hosc : ∀ u ∈ K, ∀ v ∈ K,
      D (u, v) ≤ ENNReal.ofReal δ → |f u - f v| < θ)
    {P : ℝ → ℂ} {L B : ℝ} {N : ℕ}
    (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hPK : ∀ s ∈ Icc 0 L, P s ∈ K)
    (hN : 0 < N) (hLB : L ≤ B) (hBδ : B / (N : ℝ) ≤ δ) :
    ∀ j < N, ∀ s ∈ Icc (uniformGrid L N j) (uniformGrid L N (j + 1)),
      f (P (uniformGrid L N j)) - θ ≤ f (P s) := by
  obtain ⟨hmono, _, _, hnode, hshort⟩ :=
    uniformGrid_props D hP hu hN hLB hBδ
  intro j hj s hs
  have hj1 : j + 1 ≤ N := Nat.succ_le_of_lt hj
  have hsI : s ∈ Icc 0 L :=
    ⟨(hnode j hj.le).1.trans hs.1, hs.2.trans (hnode (j + 1) hj1).2⟩
  have hd : D (P (uniformGrid L N j), P s) ≤
      D.len P (uniformGrid L N j) (uniformGrid L N (j + 1)) :=
    eVariationOn.edist_le (D.pt ∘ P) ⟨le_rfl, hmono (Nat.le_succ j)⟩ hs
  have ho := hosc _ (hPK _ (hnode j hj.le)) _ (hPK s hsI)
    (hd.trans (hshort j hj))
  exact le_of_lt (by linarith [(abs_lt.mp ho).2])

theorem uniformGrid_weighted_chain_le_cost
    (D : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    {K : Set ℂ} {δ θ : ℝ}
    (hosc : ∀ u ∈ K, ∀ v ∈ K,
      D (u, v) ≤ ENNReal.ofReal δ → |f u - f v| < θ)
    {P : ℝ → ℂ} {L B : ℝ} {N : ℕ}
    (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hPK : ∀ s ∈ Icc 0 L, P s ∈ K)
    (hN : 0 < N) (hLB : L ≤ B) (hBδ : B / (N : ℝ) ≤ δ) :
    (∑ j ∈ Finset.range N,
        chainWeightMinus ξ f θ (P (uniformGrid L N j)) *
          D (P (uniformGrid L N j), P (uniformGrid L N (j + 1)))) ≤
      ∫⁻ s in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P s))) := by
  obtain ⟨ht, ht0, htN, _, _⟩ := uniformGrid_props D hP hu hN hLB hBδ
  exact weighted_chain_le_weyl_cost D ξ hξ f hforget hP hu
    (uniformGrid L N) ht N ht0 htN θ
    (uniformGrid_field_lower D f hosc hP hu hPK hN hLB hBδ)

end SupercriticalLQGUniqueness.B2.PfeWeyl
