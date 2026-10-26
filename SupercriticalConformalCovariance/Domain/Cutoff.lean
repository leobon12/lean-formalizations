import LQGMetric.Field.Measurable
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Exhaustion of a domain by compacts, continuous cutoffs, and cut-off extensions

For an open `V ⊆ ℂ`:
* `exK V n = {z : ‖z‖ ≤ n, dist(z, w) ≥ 1/(n+1) for all w ∉ V}`: compact, contained in `V`,
  `exK V n ⊆ interior (exK V (n+1))`, and every compact subset of `V` lies in some `exK V n`;
* `exW V n = interior (exK V (n+1))`: open, `⊆ V`, every compact subset of `V` lies in some `exW V n`;
* `cutoff V n ∈ C(ℂ)` (an explicit distance formula, no choice): `1` on `exK V (n+1)`,
  `tsupport ⊆ exK V (n+2) ⊆ V`;
* `cutExt χ f = χ · (f extended by 0)` for `f ∈ C(V)` and `tsupport χ ⊆ V`: continuous on `ℂ`,
  compactly supported (hence bounded) if `χ` is, and measurable in `f`;
* `restrictTo_addFun_eq`: if `h = h₀|_V + f` on `V` (the `IsDomainRealization` identity) and
  `χ = 1` on the open `W ⊆ V`, then `(h₀ + χ f)|_W = h|_W` (pairing form).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped Distributions

namespace SupercriticalConformalCovariance.Domain

open LQGMetric (DistC DistOn TestOn TestC restrictTo addFun ofCont)

/-! ## The exhaustion -/

/-- The `n`-th compact of the exhaustion of `V`. -/
def exK (V : Set ℂ) (n : ℕ) : Set ℂ :=
  {z | ‖z‖ ≤ n ∧ ∀ w ∉ V, ((n : ℝ) + 1)⁻¹ ≤ dist z w}

theorem isClosed_exK (V : Set ℂ) (n : ℕ) : IsClosed (exK V n) := by
  have : exK V n = {z : ℂ | ‖z‖ ≤ n} ∩ ⋂ w ∈ Vᶜ, {z | ((n : ℝ) + 1)⁻¹ ≤ dist z w} := by
    ext z; simp [exK]
  rw [this]
  refine (isClosed_le continuous_norm continuous_const).inter (isClosed_biInter fun w _ => ?_)
  exact isClosed_le continuous_const (continuous_id.dist continuous_const)

theorem isCompact_exK (V : Set ℂ) (n : ℕ) : IsCompact (exK V n) :=
  (isCompact_closedBall (0 : ℂ) n).of_isClosed_subset (isClosed_exK V n) fun z hz => by
    simpa [mem_closedBall, dist_zero_right] using hz.1

theorem exK_subset (V : Set ℂ) (n : ℕ) : exK V n ⊆ V := by
  intro z hz
  by_contra hzV
  have := hz.2 z hzV
  rw [dist_self] at this
  exact absurd this (not_le.2 (by positivity))

/-- The buffer radius between `exK V n` and the complement of `exK V (n+1)`. -/
def exR (n : ℕ) : ℝ := min (1 / 2) (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹)

theorem exR_pos (n : ℕ) : 0 < exR n := by
  refine lt_min (by norm_num) (sub_pos.2 ?_)
  exact inv_strictAnti₀ (by positivity) (by linarith)

theorem ball_subset_exK (V : Set ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ exK V n) :
    ball z (exR n) ⊆ exK V (n + 1) := by
  intro y hy
  rw [mem_ball] at hy
  have hyr1 : dist y z < 1 / 2 := hy.trans_le (min_le_left _ _)
  have hyr2 : dist y z < ((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹ := hy.trans_le (min_le_right _ _)
  refine ⟨?_, fun w hw => ?_⟩
  · have h1 : ‖y‖ ≤ ‖z‖ + dist y z := by
      rw [dist_eq_norm]
      calc ‖y‖ = ‖z + (y - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖y - z‖ := norm_add_le _ _
    push_cast
    linarith [hz.1]
  · have h2 := hz.2 w hw
    have h3 : dist z w ≤ dist z y + dist y w := dist_triangle z y w
    rw [dist_comm z y] at h3
    push_cast
    have : ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 := by ring
    rw [this]
    linarith

theorem exK_subset_interior (V : Set ℂ) (n : ℕ) : exK V n ⊆ interior (exK V (n + 1)) := by
  intro z hz
  rw [mem_interior_iff_mem_nhds]
  exact mem_of_superset (ball_mem_nhds z (exR_pos n)) (ball_subset_exK V n hz)

/-- Every compact subset of an open `V` lies in some `exK V n`. -/
theorem exists_subset_exK {V : Set ℂ} (hV : IsOpen V) {K : Set ℂ} (hK : IsCompact K)
    (hKV : K ⊆ V) : ∃ n, K ⊆ exK V n := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_thickening_subset_open hV hKV
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt R
  obtain ⟨n₂, hn₂⟩ := exists_nat_one_div_lt hδ
  refine ⟨max n₁ n₂, fun z hz => ⟨?_, fun w hw => ?_⟩⟩
  · have := hR hz
    rw [mem_closedBall, dist_zero_right] at this
    have : (n₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_left _ _
    linarith
  · by_contra hlt
    push Not at hlt
    have hle : ((max n₁ n₂ : ℕ) + 1 : ℝ)⁻¹ ≤ 1 / ((n₂ : ℝ) + 1) := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_right _ _) 1)
    have hwK : w ∈ thickening δ K := by
      rw [mem_thickening_iff]
      exact ⟨z, hz, by rw [dist_comm]; linarith⟩
    exact hw (hδV hwK)

/-- The open sets of the exhaustion. -/
def exW (V : Set ℂ) (n : ℕ) : Set ℂ := interior (exK V (n + 1))

theorem isOpen_exW (V : Set ℂ) (n : ℕ) : IsOpen (exW V n) := isOpen_interior

theorem exW_subset_exK (V : Set ℂ) (n : ℕ) : exW V n ⊆ exK V (n + 1) := interior_subset

theorem exW_subset (V : Set ℂ) (n : ℕ) : exW V n ⊆ V :=
  (exW_subset_exK V n).trans (exK_subset V _)

theorem exists_subset_exW {V : Set ℂ} (hV : IsOpen V) {K : Set ℂ} (hK : IsCompact K)
    (hKV : K ⊆ V) : ∃ n, K ⊆ exW V n := by
  obtain ⟨n, hn⟩ := exists_subset_exK hV hK hKV
  exact ⟨n, hn.trans (exK_subset_interior V n)⟩

/-! ## Cutoffs -/

/-- The `n`-th cutoff of `V` (explicit): `z ↦ min 1 (dist(z, (exK V (n+2))ᶜ) / exR (n+1))`; it is
`1` on `exK V (n+1) ⊇ exW V n` and vanishes off `exK V (n+2) ⊆ V`. -/
def cutoff (V : Set ℂ) (n : ℕ) : C(ℂ, ℝ) :=
  ⟨fun z => min 1 (infDist z (exK V (n + 2))ᶜ / exR (n + 1)),
    continuous_const.min ((continuous_infDist_pt _).div_const _)⟩

theorem cutoff_apply (V : Set ℂ) (n : ℕ) (z : ℂ) :
    cutoff V n z = min 1 (infDist z (exK V (n + 2))ᶜ / exR (n + 1)) := rfl

theorem nonempty_compl_exK (V : Set ℂ) (n : ℕ) : (exK V n)ᶜ.Nonempty := by
  refine ⟨((n : ℝ) + 1 : ℝ), fun h => ?_⟩
  have := h.1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  linarith

theorem cutoff_eq_one_of_mem (V : Set ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ exK V (n + 1)) :
    cutoff V n z = 1 := by
  rw [cutoff_apply]
  refine min_eq_left ?_
  rw [le_div_iff₀ (exR_pos _), one_mul]
  refine (le_infDist (nonempty_compl_exK V (n + 2))).2 fun y hy => ?_
  by_contra hlt
  push Not at hlt
  exact hy (ball_subset_exK V (n + 1) hz (by rw [mem_ball, dist_comm]; exact hlt))

theorem cutoff_eq_zero_of_notMem (V : Set ℂ) (n : ℕ) {z : ℂ} (hz : z ∉ exK V (n + 2)) :
    cutoff V n z = 0 := by
  rw [cutoff_apply, infDist_zero_of_mem (show z ∈ (exK V (n + 2))ᶜ from hz), zero_div]
  exact min_eq_right zero_le_one

theorem cutoff_eq_one (V : Set ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ exW V n) : cutoff V n z = 1 :=
  cutoff_eq_one_of_mem V n (exW_subset_exK V n hz)

theorem tsupport_cutoff_subset_exK (V : Set ℂ) (n : ℕ) : tsupport (cutoff V n) ⊆ exK V (n + 2) :=
  closure_minimal (fun z hz => by
    by_contra h
    exact hz (cutoff_eq_zero_of_notMem V n h)) (isClosed_exK V (n + 2))

theorem tsupport_cutoff_subset (V : Set ℂ) (n : ℕ) : tsupport (cutoff V n) ⊆ V :=
  (tsupport_cutoff_subset_exK V n).trans (exK_subset V _)

theorem hasCompactSupport_cutoff (V : Set ℂ) (n : ℕ) : HasCompactSupport (cutoff V n) :=
  HasCompactSupport.intro' (isCompact_exK V (n + 2)) (isClosed_exK V (n + 2))
    fun _ hz => cutoff_eq_zero_of_notMem V n hz

/-! ## Cut-off extensions of continuous functions on `V` -/

/-- The extension of `f ∈ C(V)` by `0` (as in `IsDomainRealization`). -/
def extZ {V : Set ℂ} (f : C(V, ℝ)) : ℂ → ℝ := Function.extend Subtype.val f 0

theorem extZ_of_mem {V : Set ℂ} (f : C(V, ℝ)) {z : ℂ} (hz : z ∈ V) : extZ f z = f ⟨z, hz⟩ := by
  have := Subtype.val_injective.extend_apply (f := (Subtype.val : V → ℂ)) (g := f) 0 ⟨z, hz⟩
  exact this

theorem extZ_of_notMem {V : Set ℂ} (f : C(V, ℝ)) {z : ℂ} (hz : z ∉ V) : extZ f z = 0 := by
  unfold extZ
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨a, rfl⟩
    exact hz a.2

theorem continuousOn_extZ {V : Set ℂ} (f : C(V, ℝ)) : ContinuousOn (extZ f) V := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  funext x
  exact extZ_of_mem f x.2

/-- `χ · (f extended by 0)`. -/
def cutExtFun {V : Set ℂ} (χ : C(ℂ, ℝ)) (f : C(V, ℝ)) : ℂ → ℝ := fun z => χ z * extZ f z

theorem continuous_cutExtFun {V : Set ℂ} (hV : IsOpen V) {χ : C(ℂ, ℝ)} (hχ : tsupport χ ⊆ V)
    (f : C(V, ℝ)) : Continuous (cutExtFun χ f) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ V
  · exact χ.continuous.continuousAt.mul ((continuousOn_extZ f).continuousAt (hV.mem_nhds hz))
  · have hz' : z ∉ tsupport χ := fun h => hz (hχ h)
    have hev : (χ : ℂ → ℝ) =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
    have hev' : cutExtFun χ f =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with y hy
      simp only [cutExtFun, hy, Pi.zero_apply, zero_mul]
    exact continuousAt_const.congr hev'.symm

/-- The cut-off extension as a continuous function on `ℂ`. -/
def cutExt {V : Set ℂ} (hV : IsOpen V) {χ : C(ℂ, ℝ)} (hχ : tsupport χ ⊆ V) (f : C(V, ℝ)) :
    C(ℂ, ℝ) := ⟨cutExtFun χ f, continuous_cutExtFun hV hχ f⟩

theorem cutExt_apply {V : Set ℂ} (hV : IsOpen V) {χ : C(ℂ, ℝ)} (hχ : tsupport χ ⊆ V)
    (f : C(V, ℝ)) (z : ℂ) : cutExt hV hχ f z = χ z * extZ f z := rfl

theorem cutExt_eq_of_eq_one {V : Set ℂ} (hV : IsOpen V) {χ : C(ℂ, ℝ)} (hχ : tsupport χ ⊆ V)
    (f : C(V, ℝ)) {z : ℂ} (hz : z ∈ V) (h1 : χ z = 1) : cutExt hV hχ f z = f ⟨z, hz⟩ := by
  rw [cutExt_apply, h1, one_mul, extZ_of_mem f hz]

theorem exists_bound_cutExt {V : Set ℂ} (hV : IsOpen V) {χ : C(ℂ, ℝ)} (hχ : tsupport χ ⊆ V)
    (hχc : HasCompactSupport χ) (f : C(V, ℝ)) :
    ∃ m M : ℝ, ∀ z, m ≤ cutExt hV hχ f z ∧ cutExt hV hχ f z ≤ M := by
  have hc : HasCompactSupport (cutExt hV hχ f) := hχc.mul_right
  obtain ⟨C, hC⟩ := (cutExt hV hχ f).continuous.bounded_above_of_compact_support hc
  refine ⟨-C, C, fun z => ?_⟩
  have := hC z
  rw [Real.norm_eq_abs] at this
  exact ⟨by linarith [neg_abs_le (cutExt hV hχ f z)], (le_abs_self _).trans this⟩

theorem measurable_cutExt {V : Set ℂ} (hV : IsOpen V) {χ : C(ℂ, ℝ)} (hχ : tsupport χ ⊆ V)
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → C(V, ℝ)} (hf : Measurable f) :
    Measurable fun ω => cutExt hV hχ (f ω) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro z
  simp only [cutExt_apply]
  by_cases hz : z ∈ V
  · simp only [extZ_of_mem _ hz]
    exact ((ContinuousMap.measurable_eval ⟨z, hz⟩).comp hf).const_mul _
  · simp only [extZ_of_notMem _ hz, mul_zero]
    exact measurable_const

/-! ## The restriction identity -/

/-- A test function on `W` and its images in `𝓓(V)` and `𝓓(ℂ)` have the same values. -/
theorem coe_monoCLM {W V : TopologicalSpace.Opens ℂ} (hWV : W ≤ V) (φ : TestOn W) :
    ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := V) φ : TestOn V) : ℂ → ℝ) =
      φ := by
  rw [TestFunction.monoCLM_apply]
  split_ifs with hc
  · rfl
  · exact absurd ⟨le_rfl, hWV⟩ hc

/-- **Restriction identity.** If `h = h₀|_V + f` on `V` and `χ = 1` on the open `W ⊆ V`, then
`(h₀ + χ f)|_W = h|_W`. -/
theorem restrictTo_addFun_cutExt {V W : TopologicalSpace.Opens ℂ} (hWV : W ≤ V)
    {χ : C(ℂ, ℝ)} (hχ : tsupport χ ⊆ (V : Set ℂ)) (hχ1 : ∀ z ∈ (W : Set ℂ), χ z = 1)
    (h : DistOn V) (h₀ : DistC) (f : C((V : Set ℂ), ℝ))
    (hh : h = restrictTo V h₀ + Distribution.ofFun V (Function.extend Subtype.val f 0) volume ⊤)
    (φ : TestOn W) :
    restrictTo W (addFun h₀ (cutExt V.isOpen hχ f)) φ =
      h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := V) φ) := by
  have hψφ : ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := V) φ : TestOn V) :
      ℂ → ℝ) = φ := coe_monoCLM hWV φ
  have hloc : LocallyIntegrableOn (Function.extend Subtype.val f 0) (V : Set ℂ) volume :=
    (continuousOn_extZ f).locallyIntegrableOn V.isOpen.measurableSet
  rw [hh]
  show h₀ _ + ofCont (cutExt V.isOpen hχ f) _ = h₀ _ + Distribution.ofFun V _ volume ⊤ _
  congr 1
  · congr 1
    ext x
    simp only [ContinuousLinearMap.coe_coe]
    rw [coe_monoCLM le_top, coe_monoCLM le_top, hψφ]
  · rw [LQGMetric.ofCont_apply, Distribution.ofFun_apply hloc]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.coe_coe]
    rw [coe_monoCLM le_top, smul_eq_mul, cutExt_apply, hψφ]
    by_cases hx : φ x = 0
    · simp [hx]
    · have hxW : x ∈ (W : Set ℂ) := φ.tsupport_subset (subset_tsupport _ hx)
      rw [hχ1 x hxW, one_mul]
      rfl

end SupercriticalConformalCovariance.Domain
