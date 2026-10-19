import HigherDimLFPP.Field.GraphMeasure

/-!
# Piecewise-linear parametrizations of polygon measures (packet P-F3a, T3, part 1)

Source: planning audit HA2 (`planning/audits/HA2-section-3.md`), Details D7, (G4) ("matching
these times and interpolating between consecutive vertices": couplings of normalized arclength
measures through their parametrizations); HA3 D5, Step 1b (parametrization bound).

For breakpoints `T 0 < T 1 < … < T m` and vertices `V 0, …, V m` of `ℝ^d`, the path
`rampPath m T V s = V 0 + Σ_{i<m} ramp(T i, T (i+1), s) (V (i+1) - V i)`, with the ramp
`ramp(a, b, s) = clamp((s - a)/(b - a), 0, 1)`, is affine on each `[T i, T (i+1)]` with
`rampPath (T i) = V i` (`rampPath_eq`).  Hence (`map_rampPath`):

`(Leb|_{[0,1]}).map (rampPath m T V) = Σ_i (T (i+1) - T i) ν_{[V i, V (i+1)]}` (`Upper.segSum`)

when `T 0 = 0`, `T m = 1`.  Two such pushforwards are coupled at the same parameter
(`coupledWithin_map`), and the displacement is controlled vertex by vertex and ramp by ramp
(`norm_rampPath_sub_le`, `abs_ramp_sub_le`); this replaces the time change `σ` of HA2 D7 (G4).

2D analogue: `LQGDimension/LFPP/ConstrainedCovMeas.lean` (`segMeas`, `pairSeg`, `coupled_wc`), where
couplings are built edge by edge with equal weights; here the weights may differ.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

/-! ## Ramps -/

section Ramp

/-- The ramp `clamp((s - a)/(b - a), 0, 1)`. -/
def ramp (a b s : ℝ) : ℝ := max 0 (min 1 ((s - a) / (b - a)))

theorem ramp_nonneg (a b s : ℝ) : 0 ≤ ramp a b s := le_max_left _ _

theorem ramp_le_one (a b s : ℝ) : ramp a b s ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem abs_ramp_le_one (a b s : ℝ) : |ramp a b s| ≤ 1 := by
  rw [abs_of_nonneg (ramp_nonneg a b s)]; exact ramp_le_one a b s

theorem ramp_of_le {a b s : ℝ} (hab : a < b) (hs : s ≤ a) : ramp a b s = 0 := by
  have h : (s - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  unfold ramp
  rw [max_eq_left ((min_le_right _ _).trans h)]

theorem ramp_of_ge {a b s : ℝ} (hab : a < b) (hs : b ≤ s) : ramp a b s = 1 := by
  have h : 1 ≤ (s - a) / (b - a) := by rw [le_div_iff₀ (by linarith)]; linarith
  unfold ramp
  rw [min_eq_left h, max_eq_right zero_le_one]

theorem ramp_of_mem {a b s : ℝ} (hab : a < b) (hs : s ∈ Icc a b) :
    ramp a b s = (s - a) / (b - a) := by
  have h0 : 0 ≤ (s - a) / (b - a) := div_nonneg (by linarith [hs.1]) (by linarith)
  have h1 : (s - a) / (b - a) ≤ 1 := by rw [div_le_one (by linarith)]; linarith [hs.2]
  unfold ramp
  rw [min_eq_right h1, max_eq_right h0]

theorem continuous_ramp (a b : ℝ) : Continuous (ramp a b) := by
  unfold ramp
  fun_prop

/-- The clamp is `1`-Lipschitz. -/
theorem abs_ramp_sub_le (a b a' b' s : ℝ) :
    |ramp a b s - ramp a' b' s| ≤ |(s - a) / (b - a) - (s - a') / (b' - a')| := by
  unfold ramp
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [sub_self, abs_zero]; exact abs_nonneg _
  · refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ le_rfl)
    rw [sub_self, abs_zero]; exact abs_nonneg _

end Ramp

/-! ## Ramp paths -/

section RampPath

variable {d : ℕ}

/-- The piecewise-linear path through `V 0, …, V m` with breakpoints `T 0, …, T m`. -/
def rampPath (m : ℕ) (T : ℕ → ℝ) (V : ℕ → Rd d) (s : ℝ) : Rd d :=
  V 0 + ∑ i ∈ Finset.range m, ramp (T i) (T (i + 1)) s • (V (i + 1) - V i)

theorem continuous_rampPath (m : ℕ) (T : ℕ → ℝ) (V : ℕ → Rd d) :
    Continuous (rampPath m T V) := by
  unfold rampPath
  exact continuous_const.add (continuous_finsetSum _ fun i _ =>
    (continuous_ramp _ _).smul continuous_const)

/-- Breakpoints increasing on `{0, …, m}` are monotone there. -/
theorem le_of_lt_succ_chain {m : ℕ} {T : ℕ → ℝ} (hT : ∀ i < m, T i < T (i + 1)) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ m) : T i ≤ T j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hT j (by omega)).le

/-- On `[T k, T (k+1)]` the ramp path is the affine interpolation of `V k` and `V (k+1)`. -/
theorem rampPath_eq {m : ℕ} {T : ℕ → ℝ} (V : ℕ → Rd d) (hT : ∀ i < m, T i < T (i + 1))
    {k : ℕ} (hk : k < m) {s : ℝ} (hs : s ∈ Icc (T k) (T (k + 1))) :
    rampPath m T V s = V k + ((s - T k) / (T (k + 1) - T k)) • (V (k + 1) - V k) := by
  unfold rampPath
  rw [← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ m by omega), Finset.sum_range_succ]
  have h1 : ∑ i ∈ Finset.range k, ramp (T i) (T (i + 1)) s • (V (i + 1) - V i) = V k - V 0 := by
    rw [Finset.sum_congr rfl fun i hi => by
      rw [ramp_of_ge (hT i (by have := Finset.mem_range.1 hi; omega))
        ((le_of_lt_succ_chain hT (show i + 1 ≤ k by have := Finset.mem_range.1 hi; omega)
          hk.le).trans hs.1), one_smul]]
    exact Finset.sum_range_sub V k
  have h2 : ∑ i ∈ Finset.Ico (k + 1) m, ramp (T i) (T (i + 1)) s • (V (i + 1) - V i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_Ico.1 hi
    rw [ramp_of_le (hT i hi'.2) (hs.2.trans (le_of_lt_succ_chain hT hi'.1 hi'.2.le)), zero_smul]
  rw [h1, h2, ramp_of_mem (hT k hk) hs, add_zero]
  abel

/-- **The pushforward of Lebesgue measure under a ramp path** is the weighted segment
combination with weights `T (i+1) - T i`. -/
theorem map_rampPath {m : ℕ} {T : ℕ → ℝ} (V : ℕ → Rd d) (hT : ∀ i < m, T i < T (i + 1))
    (h0 : T 0 = 0) (h1 : T m = 1) :
    (volume.restrict (Icc (0 : ℝ) 1)).map (rampPath m T V) =
      Upper.segSum m (fun i => T (i + 1) - T i) V := by
  have hmeas : Measurable (rampPath m T V) := (continuous_rampPath m T V).measurable
  rw [← h0, ← h1, ← Upper.sum_restrict_Icc T (fun i hi => (hT i hi).le),
    Upper.map_finsetSum_range hmeas, Upper.segSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hpos : 0 < T (k + 1) - T k := sub_pos.2 (hT k hk')
  obtain ⟨a, ha⟩ : ∃ a : Rd d, a = V k - (T k / (T (k + 1) - T k)) • (V (k + 1) - V k) :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Rd d, b = a + (1 / (T (k + 1) - T k)) • (V (k + 1) - V k) := ⟨_, rfl⟩
  have hlin : ∀ s, Upper.lin a b s =
      V k + ((s - T k) / (T (k + 1) - T k)) • (V (k + 1) - V k) := by
    intro s
    rw [Upper.lin, hb, ha]
    module
  have e1 : (volume.restrict (Icc (T k) (T (k + 1)))).map (rampPath m T V) =
      (volume.restrict (Icc (T k) (T (k + 1)))).map (Upper.lin a b) := by
    refine Measure.map_congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [rampPath_eq V hT hk' hs, hlin]
  have ea : Upper.lin a b (T k) = V k := by rw [hlin, sub_self, zero_div, zero_smul, add_zero]
  have eb : Upper.lin a b (T (k + 1)) = V (k + 1) := by
    rw [hlin, div_self hpos.ne', one_smul]
    abel
  rw [e1, ← Upper.segMeasure_lin a b (hT k hk').le, ea, eb]

/-- **Same-parameter coupling** of two pushforwards of Lebesgue measure on `[0,1]`. -/
theorem coupledWithin_map {Γ Γ' : ℝ → Rd d} (hΓ : Measurable Γ) (hΓ' : Measurable Γ') {u : ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ‖Γ s - Γ' s‖ ≤ u) :
    CoupledWithin ((volume.restrict (Icc (0 : ℝ) 1)).map Γ)
      ((volume.restrict (Icc (0 : ℝ) 1)).map Γ') u := by
  have hp : Measurable fun s => (Γ s, Γ' s) := hΓ.prodMk hΓ'
  refine ⟨(volume.restrict (Icc (0 : ℝ) 1)).map fun s => (Γ s, Γ' s), ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hp]; rfl
  · rw [Measure.map_map measurable_snd hp]; rfl
  · rw [ae_map_iff hp.aemeasurable (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact h s hs

/-- **Displacement between two ramp paths**: vertex differences plus ramp differences. -/
theorem norm_rampPath_sub_le (m : ℕ) (T T' : ℕ → ℝ) (V V' : ℕ → Rd d) (s : ℝ) :
    ‖rampPath m T V s - rampPath m T' V' s‖ ≤ ‖V 0 - V' 0‖ +
      ∑ i ∈ Finset.range m, (‖(V (i + 1) - V i) - (V' (i + 1) - V' i)‖ +
        |ramp (T i) (T (i + 1)) s - ramp (T' i) (T' (i + 1)) s| * ‖V' (i + 1) - V' i‖) := by
  unfold rampPath
  have e : V 0 + ∑ i ∈ Finset.range m, ramp (T i) (T (i + 1)) s • (V (i + 1) - V i) -
      (V' 0 + ∑ i ∈ Finset.range m, ramp (T' i) (T' (i + 1)) s • (V' (i + 1) - V' i)) =
      (V 0 - V' 0) + ∑ i ∈ Finset.range m,
        (ramp (T i) (T (i + 1)) s • ((V (i + 1) - V i) - (V' (i + 1) - V' i)) +
          (ramp (T i) (T (i + 1)) s - ramp (T' i) (T' (i + 1)) s) • (V' (i + 1) - V' i)) := by
    have : ∀ i ∈ Finset.range m,
        ramp (T i) (T (i + 1)) s • ((V (i + 1) - V i) - (V' (i + 1) - V' i)) +
          (ramp (T i) (T (i + 1)) s - ramp (T' i) (T' (i + 1)) s) • (V' (i + 1) - V' i) =
        ramp (T i) (T (i + 1)) s • (V (i + 1) - V i) -
          ramp (T' i) (T' (i + 1)) s • (V' (i + 1) - V' i) := fun i _ => by module
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => (norm_add_le _ _).trans (add_le_add ?_ ?_))))
  · rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (abs_ramp_le_one _ _ _))
  · rw [norm_smul, Real.norm_eq_abs]

/-- A segment combination of vertices in a closed ball is carried by that ball. -/
theorem ae_norm_le_segSum {m : ℕ} {W : ℕ → ℝ} {V : ℕ → Rd d} {D : ℝ}
    (hV : ∀ i ≤ m, ‖V i‖ ≤ D) : ∀ᵐ z ∂(Upper.segSum m W V), ‖z‖ ≤ D := by
  refine Upper.ae_finsetSum m _ fun i hi => Measure.ae_smul_measure ?_ _
  rw [Upper.segMeasure_eq, ae_map_iff (Upper.measurable_lin _ _).aemeasurable
    (measurableSet_le continuous_norm.measurable measurable_const)]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have e : Upper.lin (V i) (V (i + 1)) s = (1 - s) • V i + s • V (i + 1) := by
    rw [Upper.lin]; module
  rw [e]
  have h1 : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  calc ‖(1 - s) • V i + s • V (i + 1)‖ ≤ (1 - s) * ‖V i‖ + s * ‖V (i + 1)‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1,
          abs_of_nonneg hs.1]
    _ ≤ (1 - s) * D + s * D :=
        add_le_add (mul_le_mul_of_nonneg_left (hV i hi.le) h1)
          (mul_le_mul_of_nonneg_left (hV (i + 1) hi) hs.1)
    _ = D := by ring

end RampPath

end HigherDimLFPP
