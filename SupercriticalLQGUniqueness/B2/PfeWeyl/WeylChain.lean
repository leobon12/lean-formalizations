import SupercriticalLQGUniqueness.B2.PfeWeyl.UniformGrid

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

theorem extMetric_chain_le_sum {α : Type*} {E : α × α → ENNReal}
    (hE : IsExtMetric E) (q : ℕ → α) (N : ℕ) :
    E (q 0, q N) ≤ ∑ j ∈ Finset.range N, E (q j, q (j + 1)) := by
  induction N with
  | zero => simpa using (hE.1 (q 0)).le
  | succ N ih =>
      calc
        E (q 0, q (N + 1)) ≤ E (q 0, q N) + E (q N, q (N + 1)) :=
          hE.2.2.2 _ _ _
        _ ≤ (∑ j ∈ Finset.range N, E (q j, q (j + 1))) +
            E (q N, q (N + 1)) := add_le_add ih le_rfl
        _ = _ := (Finset.sum_range_succ ..).symm

 
def extendChain (N : ℕ) (w : Fin (N + 1) → ℂ) (j : ℕ) : ℂ :=
  w ⟨min j N, Nat.lt_succ_of_le (min_le_right j N)⟩

theorem extendChain_zero (N : ℕ) (w : Fin (N + 1) → ℂ) :
    extendChain N w 0 = w ⟨0, Nat.zero_lt_succ N⟩ := by
  simp [extendChain]

theorem extendChain_last (N : ℕ) (w : Fin (N + 1) → ℂ) :
    extendChain N w N = w ⟨N, Nat.lt_succ_self N⟩ := by
  simp [extendChain]

theorem extendChain_left (N : ℕ) (w : Fin (N + 1) → ℂ) (j : Fin N) :
    extendChain N w j = w (chainLeft N j) := by
  simp [extendChain, chainLeft]

theorem extendChain_right (N : ℕ) (w : Fin (N + 1) → ℂ) (j : Fin N) :
    extendChain N w ((j : ℕ) + 1) = w (chainRight N j) := by
  simp [extendChain, chainRight]

theorem weylScale_chain_le_sum (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (N : ℕ) (w : Fin (N + 1) → ℂ) :
    weylScale ξ f D (w ⟨0, Nat.zero_lt_succ N⟩,
      w ⟨N, Nat.lt_succ_self N⟩) ≤
        ∑ j : Fin N, weylScale ξ f D
          (w (chainLeft N j), w (chainRight N j)) := by
  have hE := Uniqueness.Toolkit.WeylLength.weylScale_isExtMetric D ξ f hforget
  have h := extMetric_chain_le_sum hE (extendChain N w) N
  rw [extendChain_zero, extendChain_last] at h
  let F : ℕ → ENNReal := fun j =>
    weylScale ξ f D (extendChain N w j, extendChain N w (j + 1))
  have hsum : (∑ j : Fin N, F j.val) = ∑ j ∈ Finset.range N, F j :=
    Fin.sum_univ_eq_sum_range F N
  calc
    _ ≤ ∑ j ∈ Finset.range N, F j := h
    _ = ∑ j : Fin N, F j.val := hsum.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [F, extendChain_left, extendChain_right]

theorem weylScale_chain_le_weighted_sum
    (D : LSCMetric) (hD : D.IsLengthSpace)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (δ θ : ℝ)
    {K K' : Set ℂ} (hloc : LocalizedNearMinPaths D ξ f K K')
    (hosc : ∀ u ∈ K', ∀ v ∈ K',
      D (u, v) ≤ ENNReal.ofReal δ → |f u - f v| < θ)
    (hδ : 0 < δ) (hθ : 0 ≤ θ)
    (N : ℕ) (w : Fin (N + 1) → ℂ)
    (hw : ∀ i, w i ∈ K)
    (hshort : ∀ j : Fin N,
      D (w (chainLeft N j), w (chainRight N j)) < ENNReal.ofReal (δ / 2))
    {η : ℝ} (hη : 0 < η) (hηδ : η < δ / 2) (hη1 : η ≤ 1) :
    weylScale ξ f D (w ⟨0, Nat.zero_lt_succ N⟩,
      w ⟨N, Nat.lt_succ_self N⟩) ≤
        ∑ j : Fin N,
          chainWeight ξ f (w (chainLeft N j)) *
            ENNReal.ofReal (Real.exp (ξ * θ)) *
              (D (w (chainLeft N j), w (chainRight N j)) + ENNReal.ofReal η) := by
  have hchain := weylScale_chain_le_sum D ξ f hforget N w
  refine hchain.trans (Finset.sum_le_sum fun j _ => ?_)
  have hlocal := weylScale_le_exp_mul_of_short_dist
    D hD ξ hξ f hforget δ θ hloc hosc
    (w (chainLeft N j)) (hw _) (w (chainRight N j)) (hw _)
    hδ hθ (hshort j) hη hηδ hη1
  have hfactor : ENNReal.ofReal
      (Real.exp (ξ * (f (w (chainLeft N j)) + θ))) =
      chainWeight ξ f (w (chainLeft N j)) *
        ENNReal.ofReal (Real.exp (ξ * θ)) := by
    rw [chainWeight, mul_add, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (ξ * (f (w (chainLeft N j)) + θ))) *
          (D (w (chainLeft N j), w (chainRight N j)) + ENNReal.ofReal η) := hlocal
    _ = _ := by rw [hfactor, mul_assoc]

theorem finiteChain_weighted_liminf_shift
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {K : Set ℂ} (hK : IsCompact K)
    (ξ θ : ℝ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (N : ℕ) (v : ℕ → Fin (N + 1) → ℂ)
    (hv : ∀ n i, v n i ∈ K) :
    ∃ (φ : ℕ → ℕ) (w : Fin (N + 1) → ℂ),
      StrictMono φ ∧ (∀ i, w i ∈ K) ∧
      (∀ i, Tendsto (fun n => v (φ n) i) atTop (𝓝 (w i))) ∧
      (∑ j : Fin N,
          chainWeightMinus ξ f θ (w (chainLeft N j)) *
            D (w (chainLeft N j), w (chainRight N j))) ≤
        liminf (fun n => ∑ j : Fin N,
          chainWeightMinus ξ (fn (φ n)) θ (v (φ n) (chainLeft N j)) *
            G (φ n) (v (φ n) (chainLeft N j), v (φ n) (chainRight N j))) atTop := by
  let c : C(ℂ, ℝ) := ContinuousMap.const ℂ θ
  let g : C(ℂ, ℝ) := f - c
  let gn : ℕ → C(ℂ, ℝ) := fun n => fn n - c
  have hgn : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |gn n x - g x| < ε := by
    intro ε hε
    filter_upwards [hfn ε hε] with n hn x hx
    simpa [gn, g, c, sub_sub_sub_cancel_right] using hn x hx
  simpa only [g, gn, c, chainWeight, chainWeightMinus,
    ContinuousMap.sub_apply, ContinuousMap.const_apply, sub_sub_sub_cancel_right] using
    (finiteChain_weighted_liminf hG hK ξ g gn hgn N v hv)

end SupercriticalLQGUniqueness.B2.PfeWeyl
