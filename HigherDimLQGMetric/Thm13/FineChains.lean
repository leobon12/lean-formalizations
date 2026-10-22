import HigherDimLQGMetric.Thm13.GlobalPatch

/-!
# Fine rational chains for the local patch

The argument samples a near-minimizing path and moves its interior sample
points to rational-coordinate points. Both the metric cost and the Euclidean
step size are controlled. This is the variable-dimensional part of the
geometric patch argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ} {κ : Rd d → ℝ}

/-- A rational chain is the sum of its successive local edges. -/
theorem l8_patchChain_eq_sum (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (m n : ℕ) (c : ℕ → Rd d) :
    l8_patchChain hd hκ ξ εs hεs g m (c 0)
      ((List.range n).map fun k => c (k + 1)) (c (n + 1)) =
      ∑ k ∈ Finset.range (n + 1),
        l8_patchStep hd hκ ξ εs hεs g m (c k) (c (k + 1)) := by
  induction n generalizing c with
  | zero => simp [l8_patchChain]
  | succ n ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map,
        l8_patchChain, Finset.sum_range_succ', add_comm]
      congr 1
      exact ih (fun k => c (k + 1))

/-- A path with a bounded Euclidean image can be approximated by a rational
chain with arbitrarily small Euclidean steps and cost close to its length,
provided local edges agree with the metric on that bounded region. -/
theorem l8_patchInf_le_pathLength (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d) (m : ℕ)
    (z w : Rd d) (γ : Path (D.pt z) (D.pt w))
    (R : ℝ) (hR : ∀ t ∈ Icc (0 : ℝ) 1,
      D.unpt (γ.extend t) ∈ closedBall (0 : Rd d) (R - 1))
    (r : ℝ) (hr : 0 < r)
    (hLocal : ∀ x ∈ closedBall (0 : Rd d) R,
      ∀ y ∈ closedBall (0 : Rd d) R,
      dist x y < r →
      l8_patchStep hd hκ ξ εs hεs g m x y ≤ edist (D.pt x) (D.pt y))
    {η : ℝ} (hη : 0 < η) :
    l8_patchInf hd hκ ξ εs hεs g m z w ≤
      pathLength γ + ENNReal.ofReal η := by
  classical
  let E : ℝ → Rd d := D.unpt ∘ γ.extend
  have hEc : Continuous E := D.continuous_unpt.comp γ.continuous_extend
  have huc : UniformContinuousOn E (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hEc.continuousOn
  set e : ℝ := min (r / 8) (1 / 4) with he
  have he0 : 0 < e := lt_min (by positivity) (by norm_num)
  obtain ⟨α, hα, hEα⟩ := Metric.uniformContinuousOn_iff.1 huc e he0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hα
  set u : ℕ → ℝ := fun k => min ((k : ℝ) / (n + 1)) 1 with hu
  have hu_mono : Monotone u := fun a b hab =>
    min_le_min_right _ (div_le_div_of_nonneg_right (Nat.cast_le.2 hab) (by positivity))
  have hu_mem : ∀ k, u k ∈ Icc (0 : ℝ) 1 := fun k =>
    ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hu_eq : ∀ k, k ≤ n + 1 → u k = k / (n + 1) := fun k hk =>
    min_eq_left ((div_le_one (by positivity)).2 (by exact_mod_cast hk))
  have hEdom : ∀ k, k ≤ n → dist (E (u k)) (E (u (k + 1))) < e := by
    intro k hk
    refine hEα _ (hu_mem k) _ (hu_mem (k + 1)) ?_
    rw [Real.dist_eq, hu_eq k (by omega), hu_eq (k + 1) (by omega)]
    push_cast
    rw [show (k : ℝ) / (n + 1) - (k + 1) / (n + 1) = -(1 / (n + 1)) by ring,
      abs_neg, abs_of_pos (by positivity)]
    exact hn
  have hdense : DenseRange (D.pt ∘ HigherDimLFPP.ratPt (d := d)) :=
    D.ptHomeomorph.surjective.denseRange.comp
      (HigherDimLFPP.denseRange_ratPt (d := d)) D.continuous_pt
  choose δ hδpos hδsmall using fun k => D.2.euclidean_of_small (E (u k)) e he0
  set ρ : ℕ → ℝ := fun k => min (δ k) (η / (4 * (n + 1))) with hρ
  have hρpos (k : ℕ) : 0 < ρ k := lt_min (hδpos k) (by positivity)
  choose q hq using fun k => hdense.exists_dist_lt (γ.extend (u k)) (hρpos k)
  set c : ℕ → Rd d := fun k => if k = 0 then z else if k = n + 1 then w else
    HigherDimLFPP.ratPt (q k) with hc
  have hcD : ∀ k, k ≤ n + 1 →
      dist (D.pt (c k)) (γ.extend (u k)) < ρ k := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [c, u, hρpos]
    · by_cases hkn : k = n + 1
      · subst hkn
        have hu1 : u (n + 1) = 1 := by
          rw [hu_eq _ le_rfl]
          push_cast
          exact div_self (by positivity)
        simp [c, hu1, hρpos]
      · simp only [c, ite_eq_right hk0, ite_eq_right hkn]
        rw [dist_comm]
        exact hq k
  have hcE : ∀ k, k ≤ n + 1 → dist (c k) (E (u k)) < e := by
    intro k hk
    have h := hcD k hk
    have h' : D.1 (E (u k), c k) < δ k := by
      change dist (D.pt (E (u k))) (D.pt (c k)) < δ k
      change dist (D.pt (D.unpt (γ.extend (u k)))) (D.pt (c k)) < δ k
      rw [D.pt_unpt, dist_comm]
      exact h.trans_le (min_le_left _ _)
    simpa only [dist_eq_norm, norm_sub_rev] using hδsmall k (c k) h'
  have hcR : ∀ k, k ≤ n + 1 → c k ∈ closedBall (0 : Rd d) R := by
    intro k hk
    have h1 := hR (u k) (hu_mem k)
    have h2 := hcE k hk
    rw [mem_closedBall] at h1 ⊢
    have h3 := dist_triangle (c k) (E (u k)) 0
    have h4 : e ≤ 1 / 4 := min_le_right _ _
    dsimp [E] at h1 h2 h3
    linarith
  have hvalid : ∀ k, k ≤ n → dist (c k) (c (k + 1)) < r := by
    intro k hk
    have h1 := hcE k (by omega)
    have h2 := hcE (k + 1) (by omega)
    have h3 := hEdom k hk
    have h4 := dist_triangle4 (c k) (E (u k)) (E (u (k + 1))) (c (k + 1))
    have h5 : e ≤ r / 8 := min_le_left _ _
    rw [dist_comm] at h2
    linarith
  have hstep : ∀ k, k ≤ n → dist (D.pt (c k)) (D.pt (c (k + 1))) ≤
      dist (γ.extend (u k)) (γ.extend (u (k + 1))) +
        η / (2 * (n + 1)) := by
    intro k hk
    have h1 := hcD k (by omega)
    have h2 := hcD (k + 1) (by omega)
    rw [dist_comm] at h2
    have h3 := dist_triangle4 (D.pt (c k)) (γ.extend (u k))
      (γ.extend (u (k + 1))) (D.pt (c (k + 1)))
    have h4 : ρ k ≤ η / (4 * (n + 1)) := min_le_right _ _
    have h5 : ρ (k + 1) ≤ η / (4 * (n + 1)) := min_le_right _ _
    have heq : η / (4 * ((n : ℝ) + 1)) + η / (4 * ((n : ℝ) + 1)) =
        η / (2 * ((n : ℝ) + 1)) := by
      field_simp
      ring
    linarith
  have hlist : (List.map HigherDimLFPP.ratPt
      ((List.range n).map fun k => q (k + 1))) =
      (List.range n).map fun k => c (k + 1) := by
    rw [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk' : k < n := List.mem_range.1 hk
    simp only [Function.comp_apply, c, ite_eq_right (Nat.succ_ne_zero k),
      ite_eq_right (show k + 1 ≠ n + 1 by omega)]
  have hc0 : c 0 = z := by simp [c]
  have hcn : c (n + 1) = w := by simp [c]
  have hlen : ∑ k ∈ Finset.range (n + 1),
      edist (γ.extend (u k)) (γ.extend (u (k + 1))) ≤ pathLength γ := by
    refine (Finset.sum_le_sum fun k _ => ?_).trans
      (sum_internalEDist_le_curveLength (Y := univ) γ.continuous_extend.continuousOn
        (mapsTo_univ _ _) hu_mono hu_mem (n + 1))
    rw [edist_comm]
    exact edist_le_internalEDist univ _ _
  have hpert : ((n + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (η / (2 * (n + 1))) ≤ ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hN : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hN]
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have heq : ((n : ℝ) + 1) * (η / (2 * ((n : ℝ) + 1))) = η / 2 := by
      field_simp
    rw [heq]
    linarith
  calc
    l8_patchInf hd hκ ξ εs hεs g m z w
        ≤ l8_patchChain hd hκ ξ εs hεs g m z
            (List.map HigherDimLFPP.ratPt
              ((List.range n).map fun k => q (k + 1))) w := iInf_le _ _
    _ = l8_patchChain hd hκ ξ εs hεs g m (c 0)
          ((List.range n).map fun k => c (k + 1)) (c (n + 1)) := by
        rw [hlist, hc0, hcn]
    _ = ∑ k ∈ Finset.range (n + 1),
          l8_patchStep hd hκ ξ εs hεs g m (c k) (c (k + 1)) :=
        l8_patchChain_eq_sum hd hκ ξ εs hεs g m n c
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          edist (D.pt (c k)) (D.pt (c (k + 1))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact hLocal _ (hcR k (by have := Finset.mem_range.1 hk; omega))
          _ (hcR (k + 1) (by have := Finset.mem_range.1 hk; omega))
          (hvalid k (by have := Finset.mem_range.1 hk; omega))
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          (edist (γ.extend (u k)) (γ.extend (u (k + 1))) +
            ENNReal.ofReal (η / (2 * (n + 1)))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg (by positivity)]
        exact ENNReal.ofReal_le_ofReal
          (hstep k (by have := Finset.mem_range.1 hk; omega))
    _ = ∑ k ∈ Finset.range (n + 1),
          edist (γ.extend (u k)) (γ.extend (u (k + 1))) +
            ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (η / (2 * (n + 1))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ pathLength γ + ENNReal.ofReal η := add_le_add hlen hpert

/-- Compact-local agreement of sufficiently short edges recovers a length
metric from every mesh of the rational-chain formula. -/
theorem l8_patchInf_le_of_local_edges (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (hLocal : ∀ R : ℝ, ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ closedBall (0 : Rd d) R,
      ∀ y ∈ closedBall (0 : Rd d) R,
        dist x y < r →
        l8_localEdge hd hκ ξ εs hεs g x y ≤ edist (D.pt x) (D.pt y))
    (m : ℕ) (z w : Rd d) :
    l8_patchInf hd hκ ξ εs hεs g m z w ≤ ENNReal.ofReal (D.1 (z, w)) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set η : ℝ := (ε : ℝ) / 2 with hηdef
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨γ, hγ⟩ := hD (D.pt z) (D.pt w) η hη
  have hEc : Continuous (D.unpt ∘ γ.extend) :=
    D.continuous_unpt.comp γ.continuous_extend
  obtain ⟨R₀, hR₀⟩ :=
    ((isCompact_Icc.image hEc).isBounded.subset_closedBall
      (0 : Rd d))
  set R : ℝ := R₀ + 1 with hRdef
  have hR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      D.unpt (γ.extend t) ∈ closedBall (0 : Rd d) (R - 1) := by
    convert hR₀ ⟨t, ht, rfl⟩ using 1 <;> simp [R]
  obtain ⟨r₀, hr₀, hloc⟩ := hLocal R
  set r : ℝ := min r₀ (1 / ((m : ℝ) + 1)) with hrdef
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hstep : ∀ x ∈ closedBall (0 : Rd d) R,
      ∀ y ∈ closedBall (0 : Rd d) R,
      dist x y < r →
      l8_patchStep hd hκ ξ εs hεs g m x y ≤ edist (D.pt x) (D.pt y) := by
    intro x hx y hy hxy
    have hxy₁ : dist x y < 1 / ((m : ℝ) + 1) := hxy.trans_le (min_le_right _ _)
    simp only [l8_patchStep, hxy₁, ↓reduceIte]
    exact hloc x hx y hy (hxy.trans_le (min_le_left _ _))
  have hpath := l8_patchInf_le_pathLength hd hκ ξ εs hεs g D m z w γ
    R hR r hr hstep hη
  have hsum : ENNReal.ofReal η + ENNReal.ofReal η = (ε : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have heq : η + η = (ε : ℝ) := by dsimp [η]; ring
    rw [heq, ENNReal.ofReal_coe_nnreal]
  calc
    l8_patchInf hd hκ ξ εs hεs g m z w
        ≤ pathLength γ + ENNReal.ofReal η := hpath
    _ ≤ (edist (D.pt z) (D.pt w) + ENNReal.ofReal η) +
          ENNReal.ofReal η := add_le_add hγ le_rfl
    _ = ENNReal.ofReal (D.1 (z, w)) + ε := by
      rw [ContMetric.edist_pt, add_assoc, hsum]

/-- Deterministic recovery theorem for the global patch. Pointwise ambient
convergence supplies all lower bounds; compact-local short-edge agreement
supplies the upper bound through fine rational chains. -/
theorem l8_patch_eq_of_local_edges (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (hconv : ∀ u v : Rd d,
      Tendsto (fun n => (l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (u, v))
        atTop (𝓝 (D.1 (u, v))))
    (hLocal : ∀ R : ℝ, ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ closedBall (0 : Rd d) R,
      ∀ y ∈ closedBall (0 : Rd d) R,
        dist x y < r →
        l8_localEdge hd hκ ξ εs hεs g x y ≤ edist (D.pt x) (D.pt y)) :
    l8_patch hd hκ ξ εs hεs g = D := by
  apply l8_patch_eq_of_patchInf hd hκ ξ εs hεs g D
  intro m u v
  exact le_antisymm
    (l8_patchInf_le_of_local_edges hd hκ ξ εs hεs g D hD hLocal m u v)
    (l8_patchInf_ge_of_ambient_convergence hd hκ ξ εs hεs g D hconv m u v)

end HigherDimLQGMetric
