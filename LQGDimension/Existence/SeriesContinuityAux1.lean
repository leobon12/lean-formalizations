import LQGDimension.Gaussian.ChainingBox
import LQGDimension.Gaussian.Concentration
import Mathlib.Probability.ProductMeasure

/-!
# Tail bounds for oscillations of Gaussian series (helpers for `GaussianSeriesLocallyUnifCont`)

Let `ω` be an i.i.d. standard Gaussian sequence and `X_t(ω) = ∑ₖ v_t(k) ω_k` with finitely
supported `v_t`.  For a countable family `S` of indices whose parameters `p t ∈ ℝ^d` (sup norm)
have diameter at most `a`, and with `‖v_s - v_t‖²_{ℓ²} ≤ L² ‖p s - p t‖` on `S`, we prove
(`gaussSeq_osc_countable`) that for `t₀ ∈ S`, `σ² ≥ L² a`, `s ≥ 0`,
`P(∃ t ∈ S, 20 √5 L √((d+1) a) + s ≤ |X_t - X_{t₀}|) ≤ 2 exp(-2 s² / (π² σ²))`.

Proof: chaining (`ChainBox.chainingBox_bound`) bounds the expected maximum, Gaussian
concentration (`maxConcentration_tail`) gives the tail; this is done in `stdGaussian E` for
finite families (`stdGaussian_osc_tail`), transferred to the sequence space through the
projection on the first `N` coordinates (`map_proj`), and extended to countable families by
continuity from below.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real WithLp
open scoped RealInnerProductSpace ENNReal

namespace LQGDimension

namespace SeriesCont

/-! ### Finite families in `stdGaussian E` -/

section FiniteTail

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- One-sided tail of the oscillation of a finite Gaussian family around `i₀`. -/
theorem stdGaussian_osc_one_sided {d : ℕ} (F : Finset ι) (p : ι → Fin d → ℝ) (w : ι → E)
    {L a σ s : ℝ} (hL : 0 ≤ L) (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a)
    (hw : ∀ i ∈ F, ∀ j ∈ F, ‖w i - w j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖) (hσ : 0 < σ)
    (hσa : L ^ 2 * a ≤ σ ^ 2) (hs : 0 ≤ s) {i₀ : ι} (hi₀ : i₀ ∈ F) :
    stdGaussian E {x | ∃ i ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤ ⟪w i - w i₀, x⟫} ≤
      ENNReal.ofReal (Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2))) := by
  set V : ι → E := fun i => w i - w i₀ with hV
  have hVσ : ∀ i ∈ F, ‖V i‖ ≤ σ := by
    intro i hi
    have h1 := hw i hi i₀ hi₀
    have h2 := hp i hi i₀ hi₀
    have h3 : ‖V i‖ ^ 2 ≤ σ ^ 2 :=
      calc ‖V i‖ ^ 2 ≤ L ^ 2 * ‖p i - p i₀‖ := h1
        _ ≤ L ^ 2 * a := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
        _ ≤ σ ^ 2 := hσa
    nlinarith [norm_nonneg (V i)]
  have hEM : vecExpectedMax F V 0 ≤ 20 * √5 * L * √((d + 1) * a) :=
    ChainBox.chainingBox_bound F p w hL hp hw hi₀
  have hsub : {x | ∃ i ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤ ⟪w i - w i₀, x⟫} ⊆
      {x | s ≤ (⨆ i : F, ⟪V i, x⟫ + (0 : ι → ℝ) i) - vecExpectedMax F V 0} := by
    rintro x ⟨i, hi, hx⟩
    have hle : ⟪V i, x⟫ + (0 : ι → ℝ) i ≤ ⨆ j : F, ⟪V j, x⟫ + (0 : ι → ℝ) j :=
      le_ciSup (f := fun j : F => ⟪V j, x⟫ + (0 : ι → ℝ) j) (Set.finite_range _).bddAbove
        ⟨i, hi⟩
    simp only [Pi.zero_apply, add_zero] at hle
    show s ≤ (⨆ i : F, ⟪V i, x⟫ + (0 : ι → ℝ) i) - vecExpectedMax F V 0
    simp only [Pi.zero_apply, add_zero] at hle ⊢
    have hx' : 20 * √5 * L * √((d + 1) * a) + s ≤ ⟪V i, x⟫ := hx
    linarith
  have htail := (maxConcentration_tail F V 0 hσ hVσ hs).1
  calc stdGaussian E {x | ∃ i ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤ ⟪w i - w i₀, x⟫}
      ≤ stdGaussian E {x | s ≤ (⨆ i : F, ⟪V i, x⟫ + (0 : ι → ℝ) i) - vecExpectedMax F V 0} :=
        measure_mono hsub
    _ = ENNReal.ofReal ((stdGaussian E).real
          {x | s ≤ (⨆ i : F, ⟪V i, x⟫ + (0 : ι → ℝ) i) - vecExpectedMax F V 0}) :=
        (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2))) :=
        ENNReal.ofReal_le_ofReal htail

/-- Two-sided tail of the oscillation of a finite Gaussian family around `i₀`. -/
theorem stdGaussian_osc_tail {d : ℕ} (F : Finset ι) (p : ι → Fin d → ℝ) (w : ι → E)
    {L a σ s : ℝ} (hL : 0 ≤ L) (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a)
    (hw : ∀ i ∈ F, ∀ j ∈ F, ‖w i - w j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖) (hσ : 0 < σ)
    (hσa : L ^ 2 * a ≤ σ ^ 2) (hs : 0 ≤ s) {i₀ : ι} (hi₀ : i₀ ∈ F) :
    stdGaussian E {x | ∃ i ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤ |⟪w i - w i₀, x⟫|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2))) := by
  have h1 := stdGaussian_osc_one_sided F p w hL hp hw hσ hσa hs hi₀
  have h2 := stdGaussian_osc_one_sided F p (fun i => -w i) hL hp (by
      intro i hi j hj
      have := hw i hi j hj
      rwa [show -w i - -w j = -(w i - w j) by abel, norm_neg]) hσ hσa hs hi₀
  have hsub : {x | ∃ i ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤ |⟪w i - w i₀, x⟫|} ⊆
      {x | ∃ i ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤ ⟪w i - w i₀, x⟫} ∪
      {x | ∃ i ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤
        ⟪(fun i => -w i) i - (fun i => -w i) i₀, x⟫} := by
    rintro x ⟨i, hi, hx⟩
    rcases le_abs.1 hx with h | h
    · exact Or.inl ⟨i, hi, h⟩
    · refine Or.inr ⟨i, hi, ?_⟩
      rw [show -w i - -w i₀ = -(w i - w i₀) by abel, inner_neg_left]
      exact h
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [two_mul, ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  exact add_le_add h1 h2

end FiniteTail

/-! ### From the sequence space to `stdGaussian` -/

section Transfer

/-- The law of an i.i.d. standard Gaussian sequence. -/
abbrev gaussSeq : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

/-- The first `N` coordinates, as a vector of `EuclideanSpace`. -/
def proj (N : ℕ) (ω : ℕ → ℝ) : EuclideanSpace ℝ (Finset.range N) :=
  toLp 2 ((Finset.range N).restrict ω)

/-- The first `N` coefficients of a sequence, as a vector of `EuclideanSpace`. -/
def vec (N : ℕ) (u : ℕ → ℝ) : EuclideanSpace ℝ (Finset.range N) :=
  toLp 2 (fun k : Finset.range N => u k)

theorem measurable_proj (N : ℕ) : Measurable (proj N) := by
  unfold proj
  fun_prop

theorem map_proj (N : ℕ) :
    gaussSeq.map (proj N) = stdGaussian (EuclideanSpace ℝ (Finset.range N)) := by
  have : proj N = (toLp 2) ∘ (Finset.range N).restrict := rfl
  calc gaussSeq.map (proj N)
      = (gaussSeq.map (Finset.range N).restrict).map (toLp 2) := by
        rw [this]
        exact (Measure.map_map (by fun_prop) (Finset.measurable_restrict _)).symm
    _ = stdGaussian (EuclideanSpace ℝ (Finset.range N)) := by
        rw [Measure.infinitePi_map_restrict, map_pi_eq_stdGaussian]

theorem inner_vec_proj (N : ℕ) (u ω : ℕ → ℝ) :
    ⟪vec N u, proj N ω⟫ = ∑ k ∈ Finset.range N, u k * ω k := by
  simp only [vec, proj, PiLp.inner_apply, Finset.restrict,
    RCLike.inner_apply, conj_trivial]
  rw [← Finset.sum_coe_sort (Finset.range N) (fun k => u k * ω k)]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem norm_vec_sub_sq (N : ℕ) (u u' : ℕ → ℝ) :
    ‖vec N u - vec N u'‖ ^ 2 = ∑ k ∈ Finset.range N, (u k - u' k) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [vec, PiLp.sub_apply]
  exact Finset.sum_coe_sort (Finset.range N) (fun k => (u k - u' k) ^ 2)

theorem tsum_mul_eq_sum {u : ℕ → ℝ} {N : ℕ} (hN : ∀ k ≥ N, u k = 0) (ω : ℕ → ℝ) :
    ∑' k, u k * ω k = ∑ k ∈ Finset.range N, u k * ω k := by
  refine tsum_eq_sum fun k hk => ?_
  rw [hN k (by simpa using hk), zero_mul]

theorem tsum_sub_sq_eq_sum {u u' : ℕ → ℝ} {N : ℕ} (hN : ∀ k ≥ N, u k = 0)
    (hN' : ∀ k ≥ N, u' k = 0) :
    ∑' k, (u k - u' k) ^ 2 = ∑ k ∈ Finset.range N, (u k - u' k) ^ 2 := by
  refine tsum_eq_sum fun k hk => ?_
  have hk' : N ≤ k := by simpa using hk
  rw [hN k hk', hN' k hk']
  ring

/-- The oscillation tail for a finite subfamily of a Gaussian series. -/
theorem gaussSeq_osc_finset {α : Type*} {d : ℕ} (v : α → ℕ → ℝ) (F : Finset α) (N : ℕ)
    (hN : ∀ t ∈ F, ∀ k ≥ N, v t k = 0) (p : α → Fin d → ℝ) {L a σ s : ℝ} (hL : 0 ≤ L)
    (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ F, ∀ j ∈ F, ∑' k, (v i k - v j k) ^ 2 ≤ L ^ 2 * ‖p i - p j‖) (hσ : 0 < σ)
    (hσa : L ^ 2 * a ≤ σ ^ 2) (hs : 0 ≤ s) {i₀ : α} (hi₀ : i₀ ∈ F) :
    gaussSeq {ω | ∃ t ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤
        |(∑' k, v t k * ω k) - ∑' k, v i₀ k * ω k|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2))) := by
  set w : α → EuclideanSpace ℝ (Finset.range N) := fun t => vec N (v t) with hw
  set A : Set (EuclideanSpace ℝ (Finset.range N)) :=
    {x | ∃ i ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤ |⟪w i - w i₀, x⟫|} with hA
  have hAm : MeasurableSet A := by
    have : A = ⋃ i ∈ F, {x | 20 * √5 * L * √((d + 1) * a) + s ≤ |⟪w i - w i₀, x⟫|} := by
      ext x
      simp [A]
    rw [this]
    exact Finset.measurableSet_biUnion F fun i _ =>
      measurableSet_le measurable_const (by fun_prop)
  have hpre : {ω : ℕ → ℝ | ∃ t ∈ F, 20 * √5 * L * √((d + 1) * a) + s ≤
      |(∑' k, v t k * ω k) - ∑' k, v i₀ k * ω k|} = proj N ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, A]
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [inner_sub_left, hw, inner_vec_proj, inner_vec_proj, tsum_mul_eq_sum (hN t ht),
      tsum_mul_eq_sum (hN i₀ hi₀)]
  rw [hpre, ← Measure.map_apply (measurable_proj N) hAm, map_proj]
  refine stdGaussian_osc_tail F p w hL hp (fun i hi j hj => ?_) hσ hσa hs hi₀
  rw [hw, norm_vec_sub_sq, ← tsum_sub_sq_eq_sum (hN i hi) (hN j hj)]
  exact hv i hi j hj

/-- **Oscillation tail for a countable subfamily of a Gaussian series.**  If the parameters
`p t ∈ ℝ^d` have sup-diameter at most `a` on the countable set `S`, and
`‖v_s - v_t‖²_{ℓ²} ≤ L² ‖p s - p t‖` there, then for `t₀ ∈ S`, `σ² ≥ L² a`, `s ≥ 0`,
`P(∃ t ∈ S, 20 √5 L √((d+1) a) + s ≤ |X_t - X_{t₀}|) ≤ 2 exp(-2 s² / (π² σ²))`. -/
theorem gaussSeq_osc_countable {α : Type*} {d : ℕ} (v : α → ℕ → ℝ)
    (hfin : ∀ t, ∃ N, ∀ k ≥ N, v t k = 0) (S : Set α) (hS : S.Countable)
    (p : α → Fin d → ℝ) {L a σ s : ℝ} (hL : 0 ≤ L) (hp : ∀ i ∈ S, ∀ j ∈ S, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ S, ∀ j ∈ S, ∑' k, (v i k - v j k) ^ 2 ≤ L ^ 2 * ‖p i - p j‖) (hσ : 0 < σ)
    (hσa : L ^ 2 * a ≤ σ ^ 2) (hs : 0 ≤ s) {i₀ : α} (hi₀ : i₀ ∈ S) :
    gaussSeq {ω | ∃ t ∈ S, 20 * √5 * L * √((d + 1) * a) + s ≤
        |(∑' k, v t k * ω k) - ∑' k, v i₀ k * ω k|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2))) := by
  classical
  obtain ⟨e, he⟩ := hS.exists_eq_range ⟨i₀, hi₀⟩
  choose Nf hNf using hfin
  set P : α → (ℕ → ℝ) → Prop := fun t ω => 20 * √5 * L * √((d + 1) * a) + s ≤
    |(∑' k, v t k * ω k) - ∑' k, v i₀ k * ω k| with hP
  set Fn : ℕ → Finset α := fun n => insert i₀ ((Finset.range n).image e) with hFn
  have hFS : ∀ n, ∀ t ∈ Fn n, t ∈ S := by
    intro n t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hi₀
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
      rw [he]
      exact mem_range_self j
  have hmono : Monotone fun n => {ω | ∃ t ∈ Fn n, P t ω} := by
    intro n n' hnn' ω hω
    obtain ⟨t, ht, hPt⟩ := hω
    refine ⟨t, ?_, hPt⟩
    exact Finset.insert_subset_insert _
      (Finset.image_subset_image (Finset.range_subset_range.2 hnn')) ht
  have hunion : {ω | ∃ t ∈ S, P t ω} = ⋃ n, {ω | ∃ t ∈ Fn n, P t ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨t, ht, hPt⟩
      rw [he] at ht
      obtain ⟨j, rfl⟩ := ht
      exact ⟨j + 1, e j, Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem e (Finset.mem_range.2 (Nat.lt_succ_self j))), hPt⟩
    · rintro ⟨n, t, ht, hPt⟩
      exact ⟨t, hFS n t ht, hPt⟩
  change gaussSeq {ω | ∃ t ∈ S, P t ω} ≤ _
  rw [hunion, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  refine gaussSeq_osc_finset v (Fn n) ((Fn n).sup Nf) ?_ p hL
    (fun i hi j hj => hp i (hFS n i hi) j (hFS n j hj))
    (fun i hi j hj => hv i (hFS n i hi) j (hFS n j hj)) hσ hσa hs
    (Finset.mem_insert_self _ _)
  intro t ht k hk
  exact hNf t k (le_trans (Finset.le_sup (f := Nf) ht) hk)

end Transfer

end SeriesCont

end LQGDimension
