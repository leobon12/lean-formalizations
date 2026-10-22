import HigherDimLQGMetric.Thm13.TightContinuousApprox

/-! Open local separation tests for compact families of metric laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Topology Filter Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ norm_e₁)

def l8_localSepDomain {d : ℕ} (n m : ℕ) : Set (Rd d × Rd d) :=
  (closedBall (0 : Rd d) n ×ˢ closedBall 0 (n + 2)) ∩
    {p | 1 / ((m : ℝ) + 1) ≤ ‖p.2 - p.1‖}

theorem l8_localSepDomain_isCompact {d : ℕ} (n m : ℕ) :
    IsCompact (l8_localSepDomain (d := d) n m) := by
  apply ((isCompact_closedBall (0 : Rd d) n).prod
    (isCompact_closedBall (0 : Rd d) (n + 2))).inter_right
  exact isClosed_le continuous_const (by fun_prop)

theorem l8_localSepDomain_nonempty {d : ℕ} (hd : 0 < d) (n m : ℕ) :
    (l8_localSepDomain (d := d) n m).Nonempty := by
  refine ⟨(0, e₁ d), ?_⟩
  change ((0 : Rd d) ∈ closedBall 0 n ∧ e₁ d ∈ closedBall 0 (n + 2)) ∧
    1 / ((m : ℝ) + 1) ≤ ‖e₁ d - (0 : Rd d)‖
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [mem_closedBall, dist_self]
    exact Nat.cast_nonneg n
  · rw [mem_closedBall, dist_zero_right, norm_e₁ hd]
    exact_mod_cast (by omega : 1 ≤ n + 2)
  · rw [sub_zero, norm_e₁ hd]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < m + 1)).mpr (by nlinarith)

def l8_localSepOpen {d : ℕ} (n m k : ℕ) :
    Set C(Rd d × Rd d, ℝ) :=
  {E | 1 / ((k : ℝ) + 1) < sInf (E '' l8_localSepDomain n m)}

theorem l8_localSepOpen_isOpen {d : ℕ} (n m k : ℕ) :
    IsOpen (l8_localSepOpen (d := d) n m k) := by
  let J := l8_localSepDomain (d := d) n m
  have hcont : Continuous (fun q : C(Rd d × Rd d, ℝ) × (Rd d × Rd d) =>
      q.1 q.2) := by fun_prop
  have hInf : Continuous (fun E : C(Rd d × Rd d, ℝ) => sInf (E '' J)) :=
    (l8_localSepDomain_isCompact n m).continuous_sInf hcont
  exact isOpen_lt continuous_const hInf

theorem l8_metric_mem_localSepOpen {d : ℕ} (hd : 0 < d)
    (E : C(Rd d × Rd d, ℝ)) (hE : IsContinuousMetric E) (n m : ℕ) :
    ∃ k, E ∈ l8_localSepOpen n m k := by
  let J := l8_localSepDomain (d := d) n m
  have hJ : IsCompact J := l8_localSepDomain_isCompact n m
  have hJne : J.Nonempty := l8_localSepDomain_nonempty hd n m
  obtain ⟨lmb, hlmb, hgap⟩ :=
    s8a_exists_ball_offdiag_gap (K := ({E} : Set C(Rd d × Rd d, ℝ)))
      isCompact_singleton (by simpa using hE) n m
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hlmb
  obtain ⟨p, hp, hmin⟩ := hJ.exists_sInf_image_eq hJne E.continuous.continuousOn
  refine ⟨k, ?_⟩
  change 1 / ((k : ℝ) + 1) < sInf (E '' J)
  rw [hmin]
  have hp' : p ∈ l8_localSepDomain (d := d) n m := hp
  exact hk.trans_le (hgap E (by simp) p.1 hp'.1.1 p.2 hp'.1.2 hp'.2)

theorem l8_localSepOpen_mono {d : ℕ} (n m : ℕ) :
    Monotone (fun k => l8_localSepOpen (d := d) n m k) := by
  intro k l hkl E hE
  change 1 / ((l : ℝ) + 1) < _
  have hk' : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkl 1
  exact (one_div_le_one_div_of_le (by positivity) hk').trans_lt hE

theorem l8_localSepOpen_lower {d : ℕ} (n m k : ℕ)
    {E : C(Rd d × Rd d, ℝ)}
    (hE : E ∈ l8_localSepOpen n m k)
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) n)
    (hy : y ∈ closedBall (0 : Rd d) (n + 2))
    (hxy : 1 / ((m : ℝ) + 1) ≤ ‖y - x‖) :
    1 / ((k : ℝ) + 1) ≤ E (x, y) := by
  let J := l8_localSepDomain (d := d) n m
  have hJ : IsCompact J := l8_localSepDomain_isCompact n m
  have hJne : J.Nonempty := ⟨(x,y), ⟨⟨hx,hy⟩,hxy⟩⟩
  have hB : BddBelow (E '' J) :=
    (hJ.image E.continuous).isBounded.bddBelow
  exact hE.le.trans (csInf_le hB ⟨(x,y), ⟨⟨hx,hy⟩,hxy⟩, rfl⟩)

/-- For a length metric, a local separation bound also protects points outside
the larger ball: every connecting path must cross its sphere. -/
theorem l8_localSepOpen_global_of_length {d : ℕ}
    (M : ContMetric d) (hMl : M.IsLength)
    (n m k : ℕ) (hM : M.1 ∈ l8_localSepOpen n m k) :
    M.1 ∈ metricSepSet_select n m k := by
  let q : ℝ := 1 / ((k : ℝ) + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsphere : ∀ M' ∈ ({M.1} : Set C(Rd d × Rd d, ℝ)),
      ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ z ∈ sphere (0 : Rd d) (n + 2), q ≤ M' (x, z) := by
    intro M' hM' x hx z hz
    have hM' : M' = M.1 := Set.mem_singleton_iff.mp hM'
    subst M'
    have hxN : ‖x‖ ≤ (n : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hx
    have hzN : ‖z‖ = (n : ℝ) + 2 := by
      simpa only [mem_sphere, dist_zero_right, Nat.cast_add, Nat.cast_ofNat] using hz
    have htri : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
      calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hxy : 1 / ((m : ℝ) + 1) ≤ ‖z - x‖ := by
      have hone : 1 / ((m : ℝ) + 1) ≤ 1 :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < m + 1)).mpr (by nlinarith)
      linarith
    exact l8_localSepOpen_lower n m k hM hx
      (sphere_subset_closedBall hz) hxy
  have hoff : ∀ M' ∈ ({M.1} : Set C(Rd d × Rd d, ℝ)),
      ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ y ∈ closedBall (0 : Rd d) (n + 2),
        1 / ((m : ℝ) + 1) ≤ ‖y - x‖ → q ≤ M' (x, y) := by
    intro M' hM' x hx y hy hxy
    have hM' : M' = M.1 := Set.mem_singleton_iff.mp hM'
    subst M'
    exact l8_localSepOpen_lower n m k hM hx hy hxy
  intro x hx y hxy
  have hlow := s8a_weylScale_sep_lower (K := ({M.1} : Set C(Rd d × Rd d, ℝ)))
    (M := M) (by simp) hMl hsphere hoff
    (ξ := 0) (f := 0) (C := 0) (by simp) hx hxy
  rw [show (0 : C(Rd d, ℝ)) = ContinuousMap.const (Rd d) 0 from rfl,
    weylScale_const_of_isLength hMl] at hlow
  have hreal : q ≤ M.1 (x, y) :=
    (ENNReal.ofReal_le_ofReal_iff (M.nonneg x y)).mp
      (by simpa only [min_self, zero_mul, neg_zero, Real.exp_zero, one_mul] using hlow)
  exact hreal

end HigherDimLQGMetric
