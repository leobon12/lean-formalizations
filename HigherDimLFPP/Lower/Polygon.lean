import HigherDimLFPP.Lower.Glue
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import LQGDimension.LFPP.SegCombLaw

/-!
# Polygons as admissible paths; LFPP length of polygons; positivity of `D^ζ`

Packet P-L1, target T4 (ruling H6; audit HA4, "Details for later use" D8, finding HA4-13),
stated with the frozen `IsAdmissiblePath`, `lfppLength`, `lfppDistance` (paths from `0` to `e₁`
in `U = (-2,2)^d`).

* `polyPath V m`: the piecewise-affine path through `V 0, …, V m` with uniform parameter speed;
  `isAdmissiblePath_polyPath`: it is admissible when `V 0 = 0`, `V m = e₁` and all vertices lie
  in `U` (`U` is convex, `convex_cube`); `lfppLength_eq_sum`: its LFPP length is
  `Σ_i ‖V(i+1) - V i‖ ∫₀¹ e^{ζ φ(V i + s (V(i+1) - V i))} ds` for continuous `φ`.
* List polygons (`listVert z i = z.getD i 0`): `isAdmissiblePath_listPoly`,
  `riemannCost_eq_sum`, and the Riemann limit `tendsto_riemannCost_listPoly`:
  `riemannCost ζ N z φ → lfppLength ζ φ (polyPath …)` as `N → ∞` (HA4 D8, "Riemann limit").
* `one_le_arclength` (chord ≤ arclength), `exp_le_lfppLength`, `lfppDistance_le`, and
  `lfppDistance_pos`: `D^ζ > 0` for every continuous field and `d ≥ 1` (needed to take
  logarithms, finding HA4-13).

2D source: `LQGDimension/LFPP/PolygonRiemann.lean` (`PolygonRiemannAux.edgeAff`, `polyPath`,
`segAff`, `polyPath_eq_edgeAff`, `continuousOn_polyPath`, `lfppLength_eq_sum`,
`isAdmissiblePath_polyPath`, `edges_eq_range_map`) and
`LQGDimension/LFPP/LowerAssemblyAux1.lean` (`LowerAsm.exists_piece'`, `hasDerivAt_of_piece'`,
`deriv_bound_piece'`, `deriv_intervalIntegrable'`, `one_le_arclength`, `exp_le_lfppLength`,
`admissible_ofReal`, `lfppDistance_pos`), with `ℂ` replaced by `ℝ^d`, `1` by `e₁` and the
square `(-2,2)²` by the cube `(-2,2)^d`. The Riemann limit uses
`LQGDimension.SegLaw.tendsto_riemannSum`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Interval

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-! ## The cube `U` -/

/-- `U = (-2,2)^d` is convex. -/
theorem convex_cube (d : ℕ) : Convex ℝ (cube d) := by
  intro z hz w hw a b ha hb hab i
  have h1 := hz i
  have h2 := hw i
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |a * z.ofLp i + b * w.ofLp i| ≤ |a * z.ofLp i| + |b * w.ofLp i| := abs_add_le _ _
    _ = a * |z.ofLp i| + b * |w.ofLp i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha,
        abs_of_nonneg hb]
    _ < 2 := by
        rcases eq_or_lt_of_le ha with ha0 | ha0
        · rw [← ha0] at hab ⊢
          rw [zero_add] at hab
          rw [hab]
          linarith
        · nlinarith [abs_nonneg (w.ofLp i)]

/-- `U ⊆ B(0, 2√d)`. -/
theorem norm_le_of_mem_cube {z : Rd d} (hz : z ∈ cube d) : ‖z‖ ≤ 2 * √d := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ i, ‖z.ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, (4 : ℝ) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    have := abs_lt.1 (hz i)
    nlinarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  calc √(∑ i, ‖z.ofLp i‖ ^ 2) ≤ √((d : ℝ) * 4) := Real.sqrt_le_sqrt h
    _ = 2 * √d := by
        rw [show (d : ℝ) * 4 = 2 ^ 2 * d by ring, Real.sqrt_mul (by norm_num),
          Real.sqrt_sq (by norm_num)]

/-! ## The polygonal path -/

section PolyPath

variable (V : ℕ → Rd d) (m : ℕ)

/-- The affine parametrization of edge `i` (from `V i` to `V (i+1)`), defined on all of `ℝ`. -/
def edgeAff (i : ℕ) (t : ℝ) : Rd d := V i + (t * (m : ℝ) - (i : ℝ)) • (V (i + 1) - V i)

/-- The piecewise-affine path through `V 0, …, V m`, edge `i` on `[i/m, (i+1)/m]`. -/
def polyPath (t : ℝ) : Rd d := edgeAff V m ⌊t * (m : ℝ)⌋₊ t

/-- Segment parametrization of edge `i` by `s ∈ [0,1]`. -/
def segAff (i : ℕ) (s : ℝ) : Rd d := V i + s • (V (i + 1) - V i)

theorem polyPath_eq_edgeAff (hm : 0 < m) (i : ℕ) (_hi : i < m) (t : ℝ)
    (ht : t ∈ Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m)) :
    polyPath V m t = edgeAff V m i t := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨ht1, ht2⟩ := ht
  have h1 : (i : ℝ) ≤ t * m := (div_le_iff₀ hm').mp ht1
  have h2 : t * m ≤ (i : ℝ) + 1 := (le_div_iff₀ hm').mp ht2
  rcases lt_or_eq_of_le h2 with hlt | heq
  · have hfloor : ⌊t * (m : ℝ)⌋₊ = i := by
      rw [Nat.floor_eq_iff (by linarith : (0 : ℝ) ≤ t * (m : ℝ))]
      exact ⟨h1, hlt⟩
    unfold polyPath
    rw [hfloor]
  · unfold polyPath
    have hfloor : ⌊t * (m : ℝ)⌋₊ = i + 1 := by
      rw [Nat.floor_eq_iff (by linarith : (0 : ℝ) ≤ t * (m : ℝ))]
      constructor
      · push_cast; linarith [heq]
      · push_cast; linarith [heq]
    rw [hfloor]
    unfold edgeAff
    have e0 : t * (m : ℝ) - (((i + 1 : ℕ) : ℝ)) = 0 := by push_cast; linarith [heq]
    rw [e0, zero_smul, add_zero]
    have e1 : t * (m : ℝ) - (i : ℝ) = 1 := by linarith [heq]
    rw [e1, one_smul]
    abel

/-- `edgeAff` is affine, hence differentiable everywhere. -/
theorem hasDerivAt_edgeAff (i : ℕ) (t : ℝ) :
    HasDerivAt (edgeAff V m i) ((m : ℝ) • (V (i + 1) - V i)) t := by
  have h1 : HasDerivAt (fun x : ℝ => x * (m : ℝ)) (m : ℝ) t := hasDerivAt_mul_const (m : ℝ)
  have h2 : HasDerivAt (fun x : ℝ => x * (m : ℝ) - (i : ℝ)) (m : ℝ) t := h1.sub_const (i : ℝ)
  have h3 : HasDerivAt (fun x : ℝ => (x * (m : ℝ) - (i : ℝ)) • (V (i + 1) - V i))
      ((m : ℝ) • (V (i + 1) - V i)) t := h2.smul_const (V (i + 1) - V i)
  exact h3.const_add (V i)

theorem continuous_edgeAff (i : ℕ) : Continuous (edgeAff V m i) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeAff V m i t).continuousAt

/-- At interior points of an edge, `polyPath` has the expected derivative. -/
theorem hasDerivAt_polyPath (hm : 0 < m) (i : ℕ) (hi : i < m) (t : ℝ)
    (ht : t ∈ Ioo ((i : ℝ) / m) (((i : ℝ) + 1) / m)) :
    HasDerivAt (polyPath V m) ((m : ℝ) • (V (i + 1) - V i)) t := by
  have hnhd : Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m) ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have heq : (polyPath V m) =ᶠ[𝓝 t] (edgeAff V m i) :=
    Filter.eventuallyEq_of_mem hnhd (fun t' ht' => polyPath_eq_edgeAff V m hm i hi t' ht')
  exact (hasDerivAt_edgeAff V m i t).congr_of_eventuallyEq heq

theorem polyPath_mem_of_convex {S : Set (Rd d)} (hS : Convex ℝ S) (hm : 0 < m) (i : ℕ)
    (hi : i < m) (hVi : V i ∈ S) (hVi1 : V (i + 1) ∈ S) (t : ℝ)
    (ht : t ∈ Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m)) : polyPath V m t ∈ S := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨ht1, ht2⟩ := ht
  have h1 : (i : ℝ) ≤ t * m := (div_le_iff₀ hm').mp ht1
  have h2 : t * m ≤ (i : ℝ) + 1 := (le_div_iff₀ hm').mp ht2
  rw [polyPath_eq_edgeAff V m hm i hi t ⟨ht1, ht2⟩]
  set s := t * (m : ℝ) - (i : ℝ) with hs_def
  have hs0 : 0 ≤ s := by rw [hs_def]; linarith
  have hs1 : s ≤ 1 := by rw [hs_def]; linarith
  have hcombo : edgeAff V m i t = (1 - s) • V i + s • V (i + 1) := by
    unfold edgeAff
    rw [← hs_def]
    module
  rw [hcombo]
  exact hS hVi hVi1 (by linarith) hs0 (by ring)

/-- The edge index of `t`, clamped to `range m`. -/
def idx (m : ℕ) (t : ℝ) : ℕ := min ⌊t * (m : ℝ)⌋₊ (m - 1)

theorem idx_lt (hm : 0 < m) (t : ℝ) : idx m t < m :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)

theorem mem_Icc_idx (hm : 0 < m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ∈ Icc ((idx m t : ℝ) / m) (((idx m t : ℝ) + 1) / m) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  unfold idx
  by_cases hle : ⌊t * (m : ℝ)⌋₊ ≤ m - 1
  · rw [min_eq_left hle]
    have hfl1 : (⌊t * (m : ℝ)⌋₊ : ℝ) ≤ t * (m : ℝ) := Nat.floor_le (by positivity)
    have hfl2 : t * (m : ℝ) < (⌊t * (m : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    constructor
    · rw [div_le_iff₀ hm']; linarith
    · rw [le_div_iff₀ hm']; linarith
  · push Not at hle
    rw [min_eq_right hle.le]
    have hge : m ≤ ⌊t * (m : ℝ)⌋₊ := by omega
    have hge' : (m : ℝ) ≤ t * (m : ℝ) :=
      le_trans (by exact_mod_cast hge) (Nat.floor_le (by positivity))
    have ht1' : t = 1 := by nlinarith
    subst ht1'
    have hnat : (m - 1) + 1 = m := Nat.sub_add_cancel hm
    have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hnat
    constructor
    · rw [div_le_one hm']; linarith
    · rw [le_div_iff₀ hm', one_mul, hcast]

theorem iUnion_Icc_eq (hm : 0 < m) :
    (⋃ i : Fin m, Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m)) = Icc (0 : ℝ) 1 := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  apply Set.Subset.antisymm
  · rintro t ht
    simp only [mem_iUnion] at ht
    obtain ⟨i, hti⟩ := ht
    have hi_nat : i.1 + 1 ≤ m := i.2
    have hi : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hi_nat
    constructor
    · have : (0 : ℝ) ≤ (i : ℝ) / m := by positivity
      linarith [hti.1]
    · have h2 : ((i : ℝ) + 1) / m ≤ 1 := by rw [div_le_one hm']; linarith
      linarith [hti.2]
  · intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨idx m t, idx_lt m hm t⟩, mem_Icc_idx m hm t ht.1 ht.2⟩

theorem continuousOn_polyPath (hm : 0 < m) : ContinuousOn (polyPath V m) (Icc (0 : ℝ) 1) := by
  rw [← iUnion_Icc_eq m hm]
  refine (locallyFinite_of_finite (fun i : Fin m =>
      Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m))).continuousOn_iUnion
    (fun i => isClosed_Icc) (fun i => ?_)
  apply (continuous_edgeAff V m i).continuousOn.congr
  intro t ht
  exact polyPath_eq_edgeAff V m hm i i.2 t ht

theorem hab_lt (hm : 0 < m) (i : ℕ) : ((i : ℝ) / m) < (((i : ℝ) + 1) / m) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have e3 : (((i : ℝ) + 1) / m) - ((i : ℝ) / m) = 1 / (m : ℝ) := by field_simp; ring
  have hpos : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  linarith [e3]

/-- The two formulas for the cost integrand agree on an edge except at its right endpoint. -/
theorem edge_congr_ae (φ : Rd d → ℝ) (ζ : ℝ) (hm : 0 < m) (i : ℕ) (hi : i < m) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Ι ((i : ℝ) / m) (((i : ℝ) + 1) / m) →
        Real.exp (ζ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖
          = Real.exp (ζ * φ (edgeAff V m i t)) * ‖(m : ℝ) • (V (i + 1) - V i)‖ := by
  have hab : ((i : ℝ) / m) < (((i : ℝ) + 1) / m) := hab_lt m hm i
  rw [uIoc_of_le hab.le, ae_iff]
  apply measure_mono_null (t := {(((i : ℝ) + 1) / m)})
  · intro t ht
    simp only [Set.mem_ofPred_eq, not_imp, Set.mem_singleton_iff] at ht ⊢
    obtain ⟨htmem, hne⟩ := ht
    by_contra htne
    apply hne
    have htOoo : t ∈ Ioo ((i : ℝ) / m) (((i : ℝ) + 1) / m) :=
      ⟨htmem.1, lt_of_le_of_ne htmem.2 htne⟩
    have h1 : polyPath V m t = edgeAff V m i t :=
      polyPath_eq_edgeAff V m hm i hi t ⟨htOoo.1.le, htOoo.2.le⟩
    have h2 : HasDerivAt (polyPath V m) ((m : ℝ) • (V (i + 1) - V i)) t :=
      hasDerivAt_polyPath V m hm i hi t htOoo
    rw [h1, h2.deriv]
  · exact measure_singleton _

/-- The cost integrand is interval integrable over each edge's parameter interval. -/
theorem intervalIntegrable_edge (φ : Rd d → ℝ) (hφ : Continuous φ) (ζ : ℝ) (hm : 0 < m)
    (i : ℕ) (hi : i < m) :
    IntervalIntegrable
      (fun t => Real.exp (ζ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖) volume
      ((i : ℝ) / m) (((i : ℝ) + 1) / m) := by
  have hgcont : Continuous
      (fun t => Real.exp (ζ * φ (edgeAff V m i t)) * ‖(m : ℝ) • (V (i + 1) - V i)‖) :=
    (Real.continuous_exp.comp (continuous_const.mul (hφ.comp (continuous_edgeAff V m i)))).mul
      continuous_const
  have hae := edge_congr_ae V m φ ζ hm i hi
  exact (intervalIntegrable_congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae)).mpr
    (hgcont.intervalIntegrable _ _)

/-- The edge integral equals `‖V(i+1) - V i‖ ∫₀¹ e^{ζ φ(segAff V i s)} ds`. -/
theorem integral_edge (φ : Rd d → ℝ) (ζ : ℝ) (hm : 0 < m) (i : ℕ) (hi : i < m) :
    (∫ t in ((i : ℝ) / m)..(((i : ℝ) + 1) / m),
        Real.exp (ζ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖)
      = ‖V (i + 1) - V i‖ * ∫ s in (0 : ℝ)..1, Real.exp (ζ * φ (segAff V i s)) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set a := (i : ℝ) / m with ha_def
  set b := ((i : ℝ) + 1) / m with hb_def
  have hval : (∫ t in a..b, Real.exp (ζ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖)
      = ∫ t in a..b, Real.exp (ζ * φ (edgeAff V m i t)) * ‖(m : ℝ) • (V (i + 1) - V i)‖ :=
    intervalIntegral.integral_congr_ae (edge_congr_ae V m φ ζ hm i hi)
  have hgval : (∫ t in a..b, Real.exp (ζ * φ (edgeAff V m i t)) *
        ‖(m : ℝ) • (V (i + 1) - V i)‖)
      = (∫ t in a..b, Real.exp (ζ * φ (edgeAff V m i t))) *
          ‖(m : ℝ) • (V (i + 1) - V i)‖ :=
    intervalIntegral.integral_mul_const _ _
  have hkey : ∀ s : ℝ, edgeAff V m i (a + s / m) = segAff V i s := by
    intro s
    have hc : (a + s / m) * (m : ℝ) - (i : ℝ) = s := by rw [ha_def]; field_simp; ring
    unfold edgeAff segAff
    rw [hc]
  have hsub0 : (m : ℝ)⁻¹ • (∫ s in (0 : ℝ)..1, Real.exp (ζ * φ (segAff V i s)))
      = ∫ t in a..b, Real.exp (ζ * φ (edgeAff V m i t)) := by
    have := intervalIntegral.inv_smul_integral_comp_add_div
      (fun s => Real.exp (ζ * φ (edgeAff V m i s)))
      (m : ℝ) a (a := (0 : ℝ)) (b := (1 : ℝ))
    simp only [hkey] at this
    rw [this]
    congr 2
    · simp [ha_def]
    · simp only [ha_def, hb_def]
      field_simp
  have hsub : (∫ t in a..b, Real.exp (ζ * φ (edgeAff V m i t)))
      = (1 / (m : ℝ)) * ∫ s in (0 : ℝ)..1, Real.exp (ζ * φ (segAff V i s)) := by
    rw [← hsub0, smul_eq_mul, one_div]
  rw [hval, hgval, hsub]
  have hnorm : ‖(m : ℝ) • (V (i + 1) - V i)‖ = (m : ℝ) * ‖V (i + 1) - V i‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hm'.le]
  rw [hnorm]
  field_simp

/-- **The LFPP length of a polygon** is a sum over its edges. -/
theorem lfppLength_eq_sum (φ : Rd d → ℝ) (hφ : Continuous φ) (ζ : ℝ) (hm : 0 < m) :
    lfppLength ζ φ (polyPath V m) =
      ∑ i ∈ Finset.range m,
        ‖V (i + 1) - V i‖ * ∫ s in (0 : ℝ)..1, Real.exp (ζ * φ (segAff V i s)) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  show (∫ t in (0 : ℝ)..1, Real.exp (ζ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖) = _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) / m)
    (f := fun t => Real.exp (ζ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖)
    (μ := volume) (n := m)
    (fun k hk => by simpa using intervalIntegrable_edge V m φ hφ ζ hm k hk)
  push_cast at hsum
  have h0 : (0 : ℝ) / m = 0 := by norm_num
  have h1 : (m : ℝ) / m = 1 := by rw [div_self]; exact_mod_cast hm'.ne'
  rw [h0, h1] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_edge V m φ ζ hm i (Finset.mem_range.mp hi)

/-- **A polygon is an admissible path** when `V 0 = 0`, `V m = e₁` and all vertices lie in
`U`. -/
theorem isAdmissiblePath_polyPath (hm : 0 < m) (hV0 : V 0 = 0) (hVm : V m = e₁ d)
    (hVU : ∀ i ≤ m, V i ∈ cube d) : IsAdmissiblePath d (polyPath V m) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h00 : (0 : ℝ) ∈ Icc (((0 : ℕ) : ℝ) / m) ((((0 : ℕ) : ℝ) + 1) / m) :=
      ⟨by rw [Nat.cast_zero, zero_div], by rw [Nat.cast_zero, zero_add]; positivity⟩
    have h0eq : polyPath V m 0 = edgeAff V m 0 0 := polyPath_eq_edgeAff V m hm 0 hm 0 h00
    rw [h0eq]
    unfold edgeAff
    simp [hV0]
  · have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      have hnat : (m - 1) + 1 = m := Nat.sub_add_cancel hm
      exact_mod_cast hnat
    have hlast : (1 : ℝ) ∈ Icc (((m - 1 : ℕ) : ℝ) / m) ((((m - 1 : ℕ) : ℝ) + 1) / m) := by
      rw [hcast]
      refine ⟨?_, by rw [div_self hm'.ne']⟩
      rw [div_le_one hm']
      have := Nat.sub_le m 1
      exact_mod_cast this
    have hm1lt : m - 1 < m := Nat.sub_lt hm Nat.one_pos
    have h11 : polyPath V m 1 = edgeAff V m (m - 1) 1 :=
      polyPath_eq_edgeAff V m hm (m - 1) hm1lt 1 hlast
    rw [h11]
    unfold edgeAff
    have hstep : (1 : ℝ) * (m : ℝ) - ((m - 1 : ℕ) : ℝ) = 1 := by rw [← hcast]; ring
    rw [hstep, one_smul]
    have hnat2 : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [hnat2, hVm]
    abel
  · intro t ht
    have hidx : idx m t < m := idx_lt m hm t
    have hmem : t ∈ Icc ((idx m t : ℝ) / m) (((idx m t : ℝ) + 1) / m) :=
      mem_Icc_idx m hm t ht.1 ht.2
    exact polyPath_mem_of_convex V m (convex_cube d) hm (idx m t) hidx
      (hVU (idx m t) hidx.le) (hVU (idx m t + 1) hidx) t hmem
  · exact continuousOn_polyPath V m hm
  · refine ⟨m, fun j => (j : ℝ) / m, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      have hdiff : (b : ℝ) / m - (a : ℝ) / m = ((b : ℝ) - (a : ℝ)) / m := by ring
      have hpos : (0 : ℝ) < ((b : ℝ) - (a : ℝ)) / m := div_pos (by linarith) hm'
      show (a : ℝ) / m < (b : ℝ) / m
      linarith [hdiff, hpos]
    · simp
    · show ((Fin.last m : Fin (m + 1)) : ℝ) / m = 1
      rw [Fin.val_last]
      exact div_self hm'.ne'
    · intro i
      have hcd : ContDiff ℝ 1 (edgeAff V m i) := by unfold edgeAff; fun_prop
      have heq1 : (fun j : Fin (m + 1) => (j : ℝ) / m) i.castSucc = (i : ℝ) / m := by simp
      have heq2 : (fun j : Fin (m + 1) => (j : ℝ) / m) i.succ = ((i : ℝ) + 1) / m := by simp
      rw [heq1, heq2]
      apply (hcd.contDiffOn (s := Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m))).congr
      intro t ht
      exact polyPath_eq_edgeAff V m hm i i.2 t ht

end PolyPath

/-! ## List polygons and Riemann sums -/

/-- Vertices of a list polygon, `z.getD i 0`. -/
def listVert (z : List (Rd d)) (i : ℕ) : Rd d := z.getD i 0

/-- `edges z` is the range-indexed list of consecutive vertex pairs. -/
theorem edges_eq_range_map (z : List (Rd d)) :
    edges z = (List.range (z.length - 1)).map (fun i => (listVert z i, listVert z (i + 1))) := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < z.length - 1
  · have h1 : n < z.length := by omega
    have h1' : n + 1 < z.length := by omega
    have hz_n : z[n]? = some (z.getD n 0) :=
      List.getElem?_eq_some_iff.mpr ⟨h1, List.getElem_eq_getD (h := h1) 0⟩
    have hz_n1 : z[n + 1]? = some (z.getD (n + 1) 0) :=
      List.getElem?_eq_some_iff.mpr ⟨h1', List.getElem_eq_getD (h := h1') 0⟩
    have hzip : (edges z)[n]? = some (z.getD n 0, z.getD (n + 1) 0) := by
      show (z.zip z.tail)[n]? = _
      rw [List.getElem?_zip_eq_some]
      refine ⟨hz_n, ?_⟩
      rw [List.getElem?_tail]
      exact hz_n1
    have hrange : ((List.range (z.length - 1)).map
        (fun i => (listVert z i, listVert z (i + 1))))[n]? =
        some (z.getD n 0, z.getD (n + 1) 0) := by
      rw [List.getElem?_map, List.getElem?_range hn]
      simp [listVert]
    rw [hzip, hrange]
  · push Not at hn
    have hlen1 : (edges z).length = z.length - 1 := by
      show (z.zip z.tail).length = z.length - 1
      rw [List.length_zip, List.length_tail]
      omega
    have hlen2 : ((List.range (z.length - 1)).map
        (fun i => (listVert z i, listVert z (i + 1)))).length = z.length - 1 := by
      simp
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem finset_sum_range_eq_list_sum {β : Type*} [AddCommMonoid β] (n : ℕ) (g : ℕ → β) :
    ∑ i ∈ Finset.range n, g i = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

/-- The Riemann cost of a list polygon as a sum over its edges. -/
theorem riemannCost_eq_sum (ζ : ℝ) (N : ℕ) (z : List (Rd d)) (φ : Rd d → ℝ) :
    riemannCost ζ N z φ =
      ∑ i ∈ Finset.range (z.length - 1), ‖listVert z (i + 1) - listVert z i‖ * ((1 : ℝ) / N) *
        ∑ l ∈ Finset.range N, Real.exp (ζ * φ (segAff (listVert z) i ((l : ℝ) / N))) := by
  unfold riemannCost
  rw [edges_eq_range_map z, List.map_map, ← finset_sum_range_eq_list_sum]
  rfl

/-- A list polygon from `0` to `e₁` with vertices in `U` has at least one edge, and its
polygonal path is admissible. -/
theorem isAdmissiblePath_listPoly (hd : 0 < d) {z : List (Rd d)} (hz0 : z.head? = some 0)
    (hz1 : z.getLast? = some (e₁ d)) (hzU : ∀ p ∈ z, p ∈ cube d) :
    0 < z.length - 1 ∧ IsAdmissiblePath d (polyPath (listVert z) (z.length - 1)) := by
  have hne : z ≠ [] := by intro h; rw [h] at hz0; simp at hz0
  have hlen1 : 1 ≤ z.length := List.length_pos_iff.mpr hne
  have hm : 0 < z.length - 1 := by
    by_contra hc
    push Not at hc
    have hz1len : z.length = 1 := by omega
    have heq : z.head? = z.getLast? := by
      rw [List.head?_eq_getElem?, List.getLast?_eq_getElem?, hz1len]
    rw [hz0, hz1] at heq
    have h0 : (0 : Rd d) = e₁ d := Option.some.inj heq
    have := norm_e₁ hd
    rw [← h0, norm_zero] at this
    exact zero_ne_one this
  refine ⟨hm, ?_⟩
  have hz0' : z[0]? = some (0 : Rd d) := by rw [← List.head?_eq_getElem?]; exact hz0
  have hV0 : listVert z 0 = 0 := by
    show z.getD 0 0 = 0
    rw [List.getD_eq_getElem?_getD, hz0']
    rfl
  have hzm' : z[z.length - 1]? = some (e₁ d) := by
    have : z[z.length - 1]? = z.getLast? := (List.getLast?_eq_getElem? (l := z)).symm
    rw [this, hz1]
  have hVm : listVert z (z.length - 1) = e₁ d := by
    show z.getD (z.length - 1) 0 = e₁ d
    rw [List.getD_eq_getElem?_getD, hzm']
    rfl
  have hVU : ∀ i ≤ z.length - 1, listVert z i ∈ cube d := by
    intro i hi
    have hi' : i < z.length := by omega
    show z.getD i 0 ∈ cube d
    rw [← List.getElem_eq_getD (h := hi') 0]
    exact hzU _ (List.getElem_mem hi')
  exact isAdmissiblePath_polyPath (listVert z) (z.length - 1) hm hV0 hVm hVU

/-- **Riemann limit** (HA4 D8): for a continuous field, the Riemann costs of a polygon converge
to its LFPP length. -/
theorem tendsto_riemannCost_polyPath (ζ : ℝ) (z : List (Rd d)) (hm : 0 < z.length - 1)
    {φ : Rd d → ℝ} (hφ : Continuous φ) :
    Tendsto (fun N => riemannCost ζ N z φ) atTop
      (𝓝 (lfppLength ζ φ (polyPath (listVert z) (z.length - 1)))) := by
  rw [lfppLength_eq_sum (listVert z) (z.length - 1) φ hφ ζ hm]
  have hfun : (fun N => riemannCost ζ N z φ) = fun N =>
      ∑ i ∈ Finset.range (z.length - 1), ‖listVert z (i + 1) - listVert z i‖ *
        LQGDimension.SegLaw.riemannSum
          (fun s => Real.exp (ζ * φ (segAff (listVert z) i s))) N := by
    funext N
    rw [riemannCost_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LQGDimension.SegLaw.riemannSum, one_div]
    ring
  rw [hfun]
  refine tendsto_finsetSum _ fun i _ => Tendsto.const_mul _ ?_
  refine LQGDimension.SegLaw.tendsto_riemannSum ?_
  unfold segAff
  fun_prop

/-! ## Arclength and positivity of the LFPP distance (from `LowerAssemblyAux1`) -/

section Path

variable {γ : ℝ → Rd d}

theorem exists_piece' {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) :
    ∃ i : Fin k, t i.castSucc < x ∧ x < t i.succ := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (k + 1)), S = Finset.univ.filter fun j => t j < x :=
    ⟨_, rfl⟩
  have hmem : ∀ j, j ∈ S ↔ t j < x := fun j => by simp [hS]
  have hne : S.Nonempty := ⟨0, (hmem 0).2 (by rw [ht0]; exact hx.1)⟩
  have hm : t (S.max' hne) < x := (hmem _).1 (S.max'_mem hne)
  have hml : S.max' hne ≠ Fin.last k := by
    intro h
    rw [h, htk] at hm
    linarith [hx.2]
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hml
  refine ⟨i, by rw [hi]; exact hm, ?_⟩
  rcases lt_or_ge x (t i.succ) with h | h
  · exact h
  · exfalso
    rcases h.lt_or_eq with h | h
    · have : i.succ ≤ S.max' hne := S.le_max' _ ((hmem _).2 h)
      rw [← hi] at this
      exact absurd this (not_le.2 Fin.castSucc_lt_succ)
    · exact hxt ⟨_, h⟩

theorem hasDerivAt_of_piece' {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1)
    (hC : ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ)))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) : HasDerivAt γ (deriv γ x) x := by
  obtain ⟨i, h1, h2⟩ := exists_piece' ht0 htk hx hxt
  exact ((hC i).contDiffAt (Icc_mem_nhds h1 h2)).differentiableAt_one.hasDerivAt

theorem deriv_bound_piece' {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 1 γ (Icc a b)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ Ioo a b, ‖deriv γ x‖ ≤ C := by
  obtain ⟨C, hC'⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl)
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  exact (hC' x (Ioo_subset_Icc_self hx)).trans (le_max_left _ _)

theorem deriv_intervalIntegrable' (hγ : IsAdmissiblePath d γ) :
    IntervalIntegrable (deriv γ) volume 0 1 := by
  obtain ⟨k, t, ht, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  have hB : ∀ i : Fin k, ∃ C, 0 ≤ C ∧
      ∀ x ∈ Ioo (t i.castSucc) (t i.succ), ‖deriv γ x‖ ≤ C :=
    fun i => deriv_bound_piece' (ht Fin.castSucc_lt_succ) (hC i)
  choose C hC0 hCb using hB
  have hbound : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ range t → ‖deriv γ x‖ ≤ ∑ i, C i := by
    intro x hx hxt
    obtain ⟨i, h1, h2⟩ := exists_piece' ht0 htk hx hxt
    exact (hCb i x ⟨h1, h2⟩).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := ∑ i, C i) measure_Ioc_lt_top.ne
    (measurable_deriv γ).aestronglyMeasurable ?_
  have hfin : (insert (1 : ℝ) (range t)).Countable := ((finite_range t).insert 1).countable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hfin.ae_notMem volume] with x hx hxI
  rw [mem_insert_iff, not_or] at hx
  exact hbound x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.1⟩ hx.2

/-- **Chord ≤ arclength**: every admissible path has arclength at least `‖e₁‖ = 1`. -/
theorem one_le_arclength (hd : 0 < d) (hγ : IsAdmissiblePath d γ) :
    1 ≤ ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ := by
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  have hI := deriv_intervalIntegrable' hγ
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le γ (deriv γ) zero_le_one
    (countable_range t) hγ.continuousOn
    (fun x hx => hasDerivAt_of_piece' ht0 htk hC hx.1 hx.2) hI
  have h := intervalIntegral.norm_integral_le_integral_norm (f := deriv γ) (μ := volume)
    zero_le_one
  rw [hFTC, hγ.source, hγ.target, sub_zero, norm_e₁ hd] at h
  exact h

theorem lfppLength_nonneg (ζ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) :
    0 ≤ lfppLength ζ φ γ := by
  unfold lfppLength
  exact intervalIntegral.integral_nonneg zero_le_one fun t _ => by positivity

/-- `D^ζ ≤` the LFPP length of any admissible path. -/
theorem lfppDistance_le (hγ : IsAdmissiblePath d γ) (ζ : ℝ) (φ : Rd d → ℝ) :
    lfppDistance d ζ φ ≤ lfppLength ζ φ γ := by
  have hBdd : BddBelow (Set.range (fun γ' : {γ // IsAdmissiblePath d γ} =>
      lfppLength ζ φ γ'.1)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨γ', rfl⟩
    exact lfppLength_nonneg ζ φ γ'.1
  exact ciInf_le hBdd ⟨γ, hγ⟩

/-- Every admissible path has LFPP length at least `e^{-|ζ| K}` when `|φ| ≤ K` on `U`. -/
theorem exp_le_lfppLength (hd : 0 < d) (hγ : IsAdmissiblePath d γ) {ζ K : ℝ} {φ : Rd d → ℝ}
    (hφ : Continuous φ) (hK : ∀ z ∈ cube d, |φ z| ≤ K) :
    Real.exp (-(|ζ| * K)) ≤ lfppLength ζ φ γ := by
  have hD := deriv_intervalIntegrable' hγ
  have hc : ContinuousOn (fun t => Real.exp (ζ * φ (γ t))) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul hφ).comp_continuousOn hγ.continuousOn)
  have hint : IntervalIntegrable (fun t => Real.exp (ζ * φ (γ t)) * ‖deriv γ t‖) volume 0 1 :=
    hD.norm.continuousOn_mul hc
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
      Real.exp (-(|ζ| * K)) * ‖deriv γ t‖ ≤ Real.exp (ζ * φ (γ t)) * ‖deriv γ t‖ := by
    intro t ht
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have hk := hK (γ t) (hγ.mapsTo ht)
    have h1 : |ζ * φ (γ t)| ≤ |ζ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    linarith [neg_abs_le (ζ * φ (γ t))]
  have hmono := intervalIntegral.integral_mono_on zero_le_one (hD.norm.const_mul _) hint hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have h1 := one_le_arclength hd hγ
  unfold lfppLength
  have hE := Real.exp_pos (-(|ζ| * K))
  nlinarith

/-- `D^ζ` is at most the LFPP length of any list polygon from `0` to `e₁` in `U`. -/
theorem lfppDistance_le_listPoly (hd : 0 < d) {z : List (Rd d)} (hz0 : z.head? = some 0)
    (hz1 : z.getLast? = some (e₁ d)) (hzU : ∀ p ∈ z, p ∈ cube d) (ζ : ℝ) (φ : Rd d → ℝ) :
    lfppDistance d ζ φ ≤ lfppLength ζ φ (polyPath (listVert z) (z.length - 1)) :=
  lfppDistance_le (isAdmissiblePath_listPoly hd hz0 hz1 hzU).2 ζ φ

/-- The segment `t ↦ t e₁` is an admissible path. -/
theorem isAdmissiblePath_smul_e₁ (d : ℕ) : IsAdmissiblePath d fun t : ℝ => t • e₁ d where
  source := zero_smul _ _
  target := one_smul _ _
  mapsTo := by
    intro t ht i
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, e₁_ofLp]
    split_ifs
    · rw [mul_one, abs_of_nonneg ht.1]; linarith [ht.2]
    · rw [mul_zero, abs_zero]; norm_num
  continuousOn := (continuous_id.smul continuous_const).continuousOn
  piecewise_contDiff := by
    refine ⟨1, fun i => ((i : ℕ) : ℝ), ?_, by simp, by simp, fun i => ?_⟩
    · intro a b hab
      simp only
      exact_mod_cast hab
    · exact (contDiff_id.smul contDiff_const).contDiffOn

/-- **Positivity of the LFPP distance** (finding HA4-13): `D^ζ > 0` for every continuous field
when `d ≥ 1`. -/
theorem lfppDistance_pos (hd : 0 < d) (ζ : ℝ) {φ : Rd d → ℝ} (hφ : Continuous φ) :
    0 < lfppDistance d ζ φ := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Rd d) (2 * √d)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hK' : ∀ z ∈ cube d, |φ z| ≤ K := fun z hz => by
    have := hK z (mem_closedBall_zero_iff.2 (norm_le_of_mem_cube hz))
    rwa [Real.norm_eq_abs] at this
  have : Nonempty {γ : ℝ → Rd d // IsAdmissiblePath d γ} :=
    ⟨⟨_, isAdmissiblePath_smul_e₁ d⟩⟩
  exact lt_of_lt_of_le (Real.exp_pos _)
    (le_ciInf fun γ => exp_le_lfppLength (ζ := ζ) hd γ.2 hφ hK')

end Path

end HigherDimLFPP.Lower
