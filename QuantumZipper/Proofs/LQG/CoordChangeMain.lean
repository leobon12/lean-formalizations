import QuantumZipper.Proofs.LQG.CoordChangeTest
import QuantumZipper.Proofs.LQG.CoordChangeExt
import QuantumZipper.Proofs.LQG.GoodSample
import QuantumZipper.LQG.Local
import QuantumZipper.Proofs.LQG.VagueUniqueOn

/-!
# M4-T4: conformal coordinate change for the boundary LQG measure

**Main theorem** (`ae_isVagueLimitOnR_coordChange`). Let `ψ` be holomorphic on an open
`U ⊇ J = [a, b]`, real and strictly increasing on `J` with `ψ' ≠ 0` there, and let `X` be a
free-boundary GFF (any additive constant), `γ ∈ (0, 2)`, `Q = 2/γ + γ/2`. Almost surely,
`bdryApprox γ (coordChange (X ω) ψ Q)` converges vaguely on `J° = (a, b)` to

  `ψ⁻¹_*(ν_{X ω}|_{ψ(J°)})`,

written as `((qBoundaryMeasure γ (X ω)).restrict (Ioo (Re ψ a) (Re ψ b))).map Φ.symm` with `Φ`
the global homeomorphism `extIso` extending `Re ψ|_J`. Consequently
`qBoundaryMeasureOn γ (coordChange (X ω) ψ Q) (Ioo a b)` is this measure
(`ae_qBoundaryMeasureOn_coordChange`).

Proof: convergence against one test function (`ae_tendsto_integral_bdryApprox_coordChange`)
for the countable family `locTest N m` and the bumps `bumpL N` (supported in the inner
intervals `IN N`), a.s. finiteness of the approximations on each `IN N`, and a three-ε argument
(`tendsto_of_locTest`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Real
open scoped ENNReal NNReal

namespace QuantumZipper
namespace CoordChange

open GaussTK BdryExist

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Inner intervals and the local test family -/

section LocalFamily

variable {a b : ℝ}

/-- The margin of the `N`-th inner interval. -/
def δN (a b : ℝ) (N : ℕ) : ℝ := (b - a) / (N + 3)

/-- The `N`-th inner interval `[a + δ_N, b − δ_N]`. -/
def IN (a b : ℝ) (N : ℕ) : Set ℝ := Icc (a + δN a b N) (b - δN a b N)

theorem δN_pos (hab : a < b) (N : ℕ) : 0 < δN a b N := div_pos (by linarith) (by positivity)

theorem δN_lt (hab : a < b) (N : ℕ) : δN a b (N + 1) < δN a b N := by
  unfold δN
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  push_cast; linarith

theorem δN_le_half (hab : a < b) (N : ℕ) : 2 * δN a b N ≤ (b - a) * (2 / 3) := by
  unfold δN
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ N := N.cast_nonneg
  nlinarith [mul_nonneg (sub_nonneg.2 hab.le) this]

theorem IN_sub_Ioo (hab : a < b) (N : ℕ) : IN a b N ⊆ Ioo a b := fun x hx =>
  ⟨by linarith [hx.1, δN_pos hab N], by linarith [hx.2, δN_pos hab N]⟩

theorem IN_le (hab : a < b) (N : ℕ) : a + δN a b N ≤ b - δN a b N := by
  have := δN_le_half hab N; linarith

theorem tsupport_sub_IN {f : ℝ → ℝ} (hab : a < b) (hf : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ioo a b) : ∃ N, tsupport f ⊆ IN a b N := by
  rcases (tsupport f).eq_empty_or_nonempty with he | hne
  · exact ⟨0, by rw [he]; exact empty_subset _⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hf.isCompact.exists_isMinOn hne continuousOn_id
  obtain ⟨x₁, hx₁, hmax⟩ := hf.isCompact.exists_isMaxOn hne continuousOn_id
  have h1 : a < x₀ := (hfs hx₀).1
  have h2 : x₁ < b := (hfs hx₁).2
  set ε := min (x₀ - a) (b - x₁)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / ε)
  refine ⟨N, fun x hx => ?_⟩
  have hδ : δN a b N ≤ ε := by
    unfold δN
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  have hx0 : x₀ ≤ x := isMinOn_iff.1 hmin x hx
  have hx1 : x ≤ x₁ := isMaxOn_iff.1 hmax x hx
  constructor
  · linarith [min_le_left (x₀ - a) (b - x₁)]
  · linarith [min_le_right (x₀ - a) (b - x₁)]

/-- The bump: `1` on `IN N`, `0` off `(a + δ_{N+1}, b − δ_{N+1})`. -/
def bumpL (a b : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (min ((x - (a + δN a b (N + 1))) / (δN a b N - δN a b (N + 1)))
    ((b - δN a b (N + 1) - x) / (δN a b N - δN a b (N + 1)))))

theorem continuous_bumpL (a b : ℝ) (N : ℕ) : Continuous (bumpL a b N) := by
  unfold bumpL; fun_prop

theorem bumpL_nonneg (a b : ℝ) (N : ℕ) (x : ℝ) : 0 ≤ bumpL a b N x := le_max_left _ _

theorem bumpL_le_one (a b : ℝ) (N : ℕ) (x : ℝ) : bumpL a b N x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem bumpL_eq_one (hab : a < b) (N : ℕ) {x : ℝ} (hx : x ∈ IN a b N) : bumpL a b N x = 1 := by
  have hw : 0 < δN a b N - δN a b (N + 1) := by linarith [δN_lt hab N]
  have h1 : 1 ≤ (x - (a + δN a b (N + 1))) / (δN a b N - δN a b (N + 1)) := by
    rw [le_div_iff₀ hw]; linarith [hx.1]
  have h2 : 1 ≤ (b - δN a b (N + 1) - x) / (δN a b N - δN a b (N + 1)) := by
    rw [le_div_iff₀ hw]; linarith [hx.2]
  unfold bumpL
  rw [min_eq_left (le_min h1 h2), max_eq_right zero_le_one]

theorem bumpL_eq_zero (hab : a < b) (N : ℕ) {x : ℝ} (hx : x ∉ Ioo (a + δN a b (N + 1))
    (b - δN a b (N + 1))) : bumpL a b N x = 0 := by
  have hw : 0 < δN a b N - δN a b (N + 1) := by linarith [δN_lt hab N]
  unfold bumpL
  apply max_eq_left
  simp only [mem_Ioo, not_and_or, not_lt] at hx
  rcases hx with h | h
  · have : (x - (a + δN a b (N + 1))) / (δN a b N - δN a b (N + 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
    exact (min_le_right _ _).trans ((min_le_left _ _).trans this)
  · have : (b - δN a b (N + 1) - x) / (δN a b N - δN a b (N + 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
    exact (min_le_right _ _).trans ((min_le_right _ _).trans this)

theorem tsupport_bumpL (hab : a < b) (N : ℕ) : tsupport (bumpL a b N) ⊆ IN a b (N + 1) := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hx'
  exact hx (bumpL_eq_zero hab N fun h => hx' ⟨h.1.le, h.2.le⟩)

theorem hasCompactSupport_bumpL (hab : a < b) (N : ℕ) : HasCompactSupport (bumpL a b N) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans (tsupport_bumpL hab N))

/-- A dense sequence in `C([a, b], ℝ)`. -/
def dseqL (a b : ℝ) : ℕ → C(Icc a b, ℝ) := TopologicalSpace.denseSeq _

/-- The local test family. -/
def locTest (a b : ℝ) (hab : a ≤ b) (N m : ℕ) (x : ℝ) : ℝ :=
  bumpL a b N x * dseqL a b m (projIcc a b hab x)

theorem continuous_locTest (hab : a ≤ b) (N m : ℕ) : Continuous (locTest a b hab N m) :=
  (continuous_bumpL a b N).mul ((dseqL a b m).continuous.comp continuous_projIcc)

theorem tsupport_locTest (hab : a < b) (N m : ℕ) :
    tsupport (locTest a b hab.le N m) ⊆ IN a b (N + 1) :=
  (tsupport_mul_subset_left).trans (tsupport_bumpL hab N)

theorem hasCompactSupport_locTest (hab : a < b) (N m : ℕ) :
    HasCompactSupport (locTest a b hab.le N m) :=
  (hasCompactSupport_bumpL hab N).mul_right

theorem abs_locTest_le (hab : a ≤ b) (N m : ℕ) (x : ℝ) :
    |locTest a b hab N m x| ≤ ‖dseqL a b m‖ := by
  unfold locTest
  rw [abs_mul, abs_of_nonneg (bumpL_nonneg a b N x)]
  calc bumpL a b N x * |dseqL a b m (projIcc a b hab x)| ≤ 1 * ‖dseqL a b m‖ := by
        refine mul_le_mul (bumpL_le_one a b N x) ?_ (abs_nonneg _) zero_le_one
        rw [← Real.norm_eq_abs]; exact (dseqL a b m).norm_coe_le_norm _
    _ = _ := one_mul _

theorem exists_locTest_approx (hab : a < b) (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ IN a b N) :
    ∀ ε > 0, ∃ m, ∀ x, |f x - locTest a b hab.le N m x| ≤ ε * bumpL a b N x := by
  intro ε hε
  have hfb : ∀ x, f x = bumpL a b N x * f x := by
    intro x
    by_cases h : f x = 0
    · simp [h]
    · rw [bumpL_eq_one hab N (hfs (subset_tsupport f h)), one_mul]
  let fr : C(Icc a b, ℝ) := ⟨fun y => f y, hf.comp continuous_subtype_val⟩
  obtain ⟨m, hm⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq
    (C(Icc a b, ℝ))) fr ε hε
  refine ⟨m, fun x => ?_⟩
  by_cases hx : x ∈ Icc a b
  · have h1 : |f x - dseqL a b m ⟨x, hx⟩| ≤ ε := by
      have := (ContinuousMap.dist_apply_le_dist (f := fr) (g := dseqL a b m) ⟨x, hx⟩).trans hm.le
      rwa [Real.dist_eq] at this
    unfold locTest
    rw [projIcc_of_mem _ hx, hfb x, ← mul_sub, abs_mul, abs_of_nonneg (bumpL_nonneg a b N x),
      mul_comm ε]
    exact mul_le_mul_of_nonneg_left h1 (bumpL_nonneg a b N x)
  · have hb : bumpL a b N x = 0 := by
      apply bumpL_eq_zero hab N
      intro h; apply hx
      exact ⟨by linarith [h.1, δN_pos hab (N + 1)], by linarith [h.2, δN_pos hab (N + 1)]⟩
    have hf0 : f x = 0 := by rw [hfb x, hb, zero_mul]
    simp [locTest, hb, hf0]

/-- **Convergence from the local family** (three-ε argument). -/
theorem tendsto_of_locTest (hab : a < b) (N : ℕ) {μs : ℕ → Measure ℝ} {ν : Measure ℝ}
    (hfin : ∀ᶠ k in atTop, μs k (IN a b (N + 1)) < ∞) (hνfin : ν (IN a b (N + 1)) < ∞)
    (hconv : ∀ m, Tendsto (fun k => ∫ x, locTest a b hab.le N m x ∂μs k) atTop
      (𝓝 (∫ x, locTest a b hab.le N m x ∂ν)))
    (hbump : Tendsto (fun k => ∫ x, bumpL a b N x ∂μs k) atTop (𝓝 (∫ x, bumpL a b N x ∂ν)))
    {f : ℝ → ℝ} (hf : Continuous f) (hfs : tsupport f ⊆ IN a b N) :
    Tendsto (fun k => ∫ x, f x ∂μs k) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport f).trans hfs)
  have hfs' : tsupport f ⊆ IN a b (N + 1) := hfs.trans (Icc_subset_Icc
    (by linarith [δN_lt hab N]) (by linarith [δN_lt hab N]))
  have hInt : ∀ μ : Measure ℝ, μ (IN a b (N + 1)) < ∞ → ∀ h : ℝ → ℝ, Continuous h →
      HasCompactSupport h → tsupport h ⊆ IN a b (N + 1) → Integrable h μ := by
    intro μ hμ h hh hhc hhs
    exact GoodSample.integrable_of_tsupport (U := IN a b (N + 1))
      (fun K _ hK => (measure_mono hK).trans_lt hμ) hh hhc hhs
  have hbs := tsupport_bumpL hab N
  have hbc := hasCompactSupport_bumpL hab N
  set Bν := ∫ x, bumpL a b N x ∂ν
  have hBν : 0 ≤ Bν := integral_nonneg (bumpL_nonneg a b N)
  -- approximation estimate for a measure with finite mass on `IN (N+1)`
  have happ : ∀ μ : Measure ℝ, μ (IN a b (N + 1)) < ∞ → ∀ η : ℝ, ∀ m : ℕ,
      (∀ x, |f x - locTest a b hab.le N m x| ≤ η * bumpL a b N x) →
      |∫ x, f x ∂μ - ∫ x, locTest a b hab.le N m x ∂μ| ≤ η * ∫ x, bumpL a b N x ∂μ := by
    intro μ hμ η m hm
    have i1 := hInt μ hμ f hf hfc hfs'
    have i2 := hInt μ hμ _ (continuous_locTest hab.le N m) (hasCompactSupport_locTest hab N m)
      (tsupport_locTest hab N m)
    have i3 := hInt μ hμ _ (continuous_bumpL a b N) hbc hbs
    rw [← integral_sub i1 i2]
    have := norm_integral_le_of_norm_le (i3.const_mul η)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hm x)
    rw [Real.norm_eq_abs, integral_const_mul] at this
    exact this
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / (3 * (Bν + 2)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨m, hm⟩ := exists_locTest_approx hab N hf hfs η hη0
  have hb1 : ∀ᶠ k in atTop, ∫ x, bumpL a b N x ∂μs k < Bν + 1 :=
    hbump.eventually (gt_mem_nhds (by linarith))
  have hc1 : ∀ᶠ k in atTop, dist (∫ x, locTest a b hab.le N m x ∂μs k)
      (∫ x, locTest a b hab.le N m x ∂ν) < ε / 3 :=
    (hconv m).eventually (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hfin.and (hb1.and hc1))
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨hk1, hk2, hk3⟩ := hK k hk
  have e1 := happ (μs k) hk1 η m hm
  have e2 := happ ν hνfin η m hm
  rw [Real.dist_eq] at hk3 ⊢
  have hbk : 0 ≤ ∫ x, bumpL a b N x ∂μs k := integral_nonneg (bumpL_nonneg a b N)
  have t1 : η * ∫ x, bumpL a b N x ∂μs k ≤ η * (Bν + 1) :=
    mul_le_mul_of_nonneg_left hk2.le hη0.le
  have t2 : η * (Bν + 1) + η * Bν < ε * (2 / 3) := by
    rw [hη]
    rw [show ε / (3 * (Bν + 2)) * (Bν + 1) + ε / (3 * (Bν + 2)) * Bν =
      ε * (2 * Bν + 1) / (3 * (Bν + 2)) by ring]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  calc |∫ x, f x ∂μs k - ∫ x, f x ∂ν|
      ≤ |∫ x, f x ∂μs k - ∫ x, locTest a b hab.le N m x ∂μs k| +
        |∫ x, locTest a b hab.le N m x ∂μs k - ∫ x, locTest a b hab.le N m x ∂ν| +
        |∫ x, f x ∂ν - ∫ x, locTest a b hab.le N m x ∂ν| := by
        have := abs_sub_le (∫ x, f x ∂μs k) (∫ x, locTest a b hab.le N m x ∂μs k)
          (∫ x, f x ∂ν)
        have h2 := abs_sub_le (∫ x, locTest a b hab.le N m x ∂μs k)
          (∫ x, locTest a b hab.le N m x ∂ν) (∫ x, f x ∂ν)
        rw [abs_sub_comm (∫ x, locTest a b hab.le N m x ∂ν)] at h2
        linarith
    _ < ε := by linarith

end LocalFamily

/-! ### The target measure -/

section Target

variable {ψ : ℂ → ℂ} {a b : ℝ}

/-- `ψ⁻¹_*(ν|_{ψ(J°)})`, via the global homeomorphism `Φ = extIso`. -/
def targetMeasure (ν : Measure ℝ) (Φ : ℝ ≃o ℝ) (a b : ℝ) : Measure ℝ :=
  (ν.restrict (Ioo (Φ a) (Φ b))).map Φ.symm

theorem integral_targetMeasure (ν : Measure ℝ) (Φ : ℝ ≃o ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Ioo a b) :
    ∫ x, f x ∂targetMeasure ν Φ a b = ∫ u, f (Φ.symm u) ∂ν := by
  unfold targetMeasure
  rw [integral_map Φ.symm.continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hu
  have h' := hfs h
  have : u = Φ (Φ.symm u) := (Φ.apply_symm_apply u).symm
  rw [this]
  exact ⟨Φ.strictMono h'.1, Φ.strictMono h'.2⟩

theorem targetMeasure_apply (ν : Measure ℝ) (Φ : ℝ ≃o ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    targetMeasure ν Φ a b A = ν (Ioo (Φ a) (Φ b) ∩ Φ '' A) := by
  unfold targetMeasure
  rw [Measure.map_apply Φ.symm.continuous.measurable hA,
    Measure.restrict_apply (Φ.symm.continuous.measurable hA), inter_comm,
    OrderIso.image_eq_preimage_symm]

end Target

/-! ### Finiteness of the approximations on inner intervals -/

namespace Data

variable {ψ : ℂ → ℂ} {a b δ m C : ℝ}

theorem ae_bdryApprox_lt_top {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) (hab : a ≤ b) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, bdryApprox γ (coordChange (X ω) ψ (Qc γ)) k (Icc a b) < ∞ := by
  obtain ⟨R, j, k₀, hR, -, hj, hscale⟩ := h.exists_scales hab
  have hk : ∀ k, k₀ ≤ k → ∀ᵐ ω ∂P, bdryApprox γ (coordChange (X ω) ψ (Qc γ)) k (Icc a b) < ∞ := by
    intro k hk
    have hf : Measurable ((Icc a b).indicator (1 : ℝ → ℝ)) :=
      measurable_one.indicator measurableSet_Icc
    have hM : ∀ t, |(Icc a b).indicator (1 : ℝ → ℝ) t| ≤ 1 := fun t => by
      simp only [indicator]; split_ifs <;> simp
    obtain ⟨i3, -, -⟩ := h.bound_FA_FB hX hγ hγ2 hR hj (hscale k hk).1 (hscale k hk).2.1 hf hM
    filter_upwards [i3.prod_right_ae] with ω hω
    have hω' : IntegrableOn (fun t => dAf X ψ γ R k t ω) (Icc a b) := by
      refine hω.congr ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => ?_))
      simp only [indicator_of_mem ht, Pi.one_apply, one_mul]
    have hlt : ∫⁻ t in Icc a b, ENNReal.ofReal (dAf X ψ γ R k t ω) < ∞ :=
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun t => by
        unfold dAf; have := radius_pos k; positivity)).1 hω'.2
    unfold bdryApprox
    rw [withDensity_apply _ measurableSet_Icc]
    have e : ∀ t : ℝ, ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
        exp (γ / 2 * avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ))) =
        ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 R))) *
          ENNReal.ofReal (dAf X ψ γ R k t ω) := by
      intro t
      rw [← ENNReal.ofReal_mul (exp_pos _).le]
      congr 1
      unfold dAf
      rw [mul_sub, exp_sub]
      field_simp
      try ring
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      bdryApprox γ (coordChange (X ω) ψ (Qc γ)) (n + k₀) (Icc a b) < ∞ :=
    ae_all_iff.2 fun n => hk (n + k₀) (by omega)
  filter_upwards [hall] with ω hω
  exact eventually_atTop.2 ⟨k₀, fun k hk' => by
    have := hω (k - k₀); rwa [Nat.sub_add_cancel hk'] at this⟩

end Data

/-! ### Uniqueness of local vague limits on `ℝ` -/

theorem isVagueLimitOnR_unique {I : Set ℝ} (hI : IsOpen I) {νs : ℕ → Measure ℝ}
    {ν ν' : Measure ℝ} (h : IsVagueLimitOnR I νs ν) (h' : IsVagueLimitOnR I νs ν') : ν = ν' := by
  obtain ⟨h0, hK, ht⟩ := h
  obtain ⟨h0', hK', ht'⟩ := h'
  have hIm : MeasurableSet I := hI.measurableSet
  have hr : ν.restrict I = ν := Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h0)
  have hr' : ν'.restrict I = ν' := Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h0')
  have : LocallyCompactSpace I := hI.locallyCompactSpace
  let μ : Measure I := Measure.comap Subtype.val ν
  let μ' : Measure I := Measure.comap Subtype.val ν'
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hKc => by
    rw [comap_subtype_coe_apply hIm]
    exact hK _ (hKc.image continuous_subtype_val) (Subtype.coe_image_subset _ _)⟩
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun K hKc => by
    rw [comap_subtype_coe_apply hIm]
    exact hK' _ (hKc.image continuous_subtype_val) (Subtype.coe_image_subset _ _)⟩
  have hμμ' : μ = μ' := by
    refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
    set G : ℝ → ℝ := Subtype.val.extend g 0
    have hGc : Continuous G := HasCompactSupport.continuous_extend_zero hI
      (map_continuous g) g.hasCompactSupport
    have hGs : HasCompactSupport G := g.hasCompactSupport.extend_zero continuous_subtype_val
    have hGI : tsupport G ⊆ I :=
      (g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)
    have key : ∀ m : Measure ℝ, ∫ z, G z ∂(m.restrict I) =
        ∫ x, g x ∂(Measure.comap Subtype.val m) := by
      intro m
      rw [← integral_subtype_comap hIm]
      simp_rw [G, Subtype.val_injective.extend_apply]
    have e1 := key ν
    have e2 := key ν'
    rw [hr] at e1
    rw [hr'] at e2
    rw [← e1, ← e2]
    exact tendsto_nhds_unique (ht G hGc hGs hGI) (ht' G hGc hGs hGI)
  rw [← hr, ← hr', ← map_comap_subtype_coe hIm, ← map_comap_subtype_coe hIm]
  exact congrArg (Measure.map Subtype.val) hμμ'

theorem qBoundaryMeasureOn_eq {γ : ℝ} {x : FieldSample} {I : Set ℝ} (hI : IsOpen I)
    {ν : Measure ℝ} (hν : IsVagueLimitOnR I (bdryApprox γ x) ν) : qBoundaryMeasureOn γ x I = ν := by
  have hex : ∃ ν', IsVagueLimitOnR I (bdryApprox γ x) ν' := ⟨ν, hν⟩
  unfold qBoundaryMeasureOn
  rw [dif_pos hex]
  exact isVagueLimitOnR_unique hI hex.choose_spec hν

/-! ### The main theorem -/

theorem continuousOn_re_of_differentiableOn {ψ : ℂ → ℂ} {a b : ℝ} {U : Set ℂ}
    (hJU : ∀ t ∈ Icc a b, (t : ℂ) ∈ U) (hψ : DifferentiableOn ℂ ψ U) :
    ContinuousOn (fun t : ℝ => (ψ t).re) (Icc a b) :=
  Complex.continuous_re.comp_continuousOn
    (hψ.continuousOn.comp Complex.continuous_ofReal.continuousOn fun t ht => hJU t ht)

/-- **M4-T4 (conformal coordinate change, deterministic map).** -/
theorem ae_isVagueLimitOnR_coordChange {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ψ : ℂ → ℂ} {a b : ℝ} (hab : a < b) {U : Set ℂ} (hU : IsOpen U)
    (hJU : ∀ t ∈ Icc a b, (t : ℂ) ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hre : ∀ t ∈ Icc a b, (ψ t).im = 0)
    (hmono : StrictMonoOn (fun t : ℝ => (ψ t).re) (Icc a b))
    (hne : ∀ t ∈ Icc a b, deriv ψ t ≠ 0) :
    ∀ᵐ ω ∂P, IsVagueLimitOnR (Ioo a b) (bdryApprox γ (coordChange (X ω) ψ (Qc γ)))
      (targetMeasure (qBoundaryMeasure γ (X ω))
        (extIso hab.le (continuousOn_re_of_differentiableOn hJU hψ) hmono) a b) := by
  set hφc := continuousOn_re_of_differentiableOn hJU hψ
  set Φ := extIso hab.le hφc hmono with hΦ
  have hΦeq : ∀ t ∈ Icc a b, Φ t = (ψ t).re := fun t ht => extIso_eq hab.le hφc hmono ht
  -- the local data on each inner interval
  have hdata : ∀ N : ℕ, ∃ δ m C, Data ψ (a + δN a b (N + 1)) (b - δN a b (N + 1)) δ m C :=
    fun N => exists_data hU hJU hψ hre hmono hne (by linarith [δN_pos hab (N + 1)])
      (by linarith [δN_pos hab (N + 1)])
  choose δs ms Cs hD using hdata
  have hINsub : ∀ N, IN a b (N + 1) ⊆ Icc a b := fun N =>
    (IN_sub_Ioo hab (N + 1)).trans Ioo_subset_Icc_self
  -- convergence against one test function supported in `IN (N+1)`
  have hTest : ∀ N (τ : ℝ → ℝ), Continuous τ → HasCompactSupport τ →
      tsupport τ ⊆ IN a b (N + 1) → (∃ M, ∀ t, |τ t| ≤ M) →
      ∀ᵐ ω ∂P, Tendsto (fun k => ∫ t, τ t ∂(bdryApprox γ (coordChange (X ω) ψ (Qc γ)) k))
        atTop (𝓝 (∫ t, τ t ∂(targetMeasure (qBoundaryMeasure γ (X ω)) Φ a b))) := by
    intro N τ hτ hτc hτs ⟨M, hM⟩
    have hfS : ∀ t ∉ Icc (a + δN a b (N + 1)) (b - δN a b (N + 1)), τ t = 0 := fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h => ht (hτs h)
    have hgS : ∀ u ∉ (fun t : ℝ => (ψ t).re) '' Icc (a + δN a b (N + 1)) (b - δN a b (N + 1)),
        (τ ∘ Φ.symm) u = 0 := by
      intro u hu
      by_contra hne'
      apply hu
      have hmem : Φ.symm u ∈ IN a b (N + 1) := hτs (subset_tsupport τ hne')
      refine ⟨Φ.symm u, hmem, ?_⟩
      simp only
      rw [← hΦeq _ (hINsub N hmem), Φ.apply_symm_apply]
    have hfg : ∀ t ∈ Icc (a + δN a b (N + 1)) (b - δN a b (N + 1)),
        τ t = (τ ∘ Φ.symm) (ψ t).re := by
      intro t ht
      simp only [Function.comp]
      rw [← hΦeq t (hINsub N ht), Φ.symm_apply_apply]
    have H := (hD N).ae_tendsto_integral_bdryApprox_coordChange hX (IN_le hab (N + 1)) hγ hγ2
      hτ.measurable hM hfS (hτ.comp Φ.symm.continuous)
      (hτc.comp_homeomorph Φ.symm.toHomeomorph) hgS hfg
    filter_upwards [H] with ω hω
    rw [integral_targetMeasure _ Φ hτ (hτs.trans (IN_sub_Ioo hab (N + 1)))]
    exact hω
  have hA : ∀ᵐ ω ∂P, ∀ N m : ℕ, Tendsto
      (fun k => ∫ t, locTest a b hab.le N m t ∂(bdryApprox γ (coordChange (X ω) ψ (Qc γ)) k))
      atTop (𝓝 (∫ t, locTest a b hab.le N m t ∂(targetMeasure (qBoundaryMeasure γ (X ω)) Φ a b))) :=
    ae_all_iff.2 fun N => ae_all_iff.2 fun m => hTest N _ (continuous_locTest hab.le N m)
      (hasCompactSupport_locTest hab N m) (tsupport_locTest hab N m)
      ⟨_, abs_locTest_le hab.le N m⟩
  have hB : ∀ᵐ ω ∂P, ∀ N : ℕ, Tendsto
      (fun k => ∫ t, bumpL a b N t ∂(bdryApprox γ (coordChange (X ω) ψ (Qc γ)) k))
      atTop (𝓝 (∫ t, bumpL a b N t ∂(targetMeasure (qBoundaryMeasure γ (X ω)) Φ a b))) :=
    ae_all_iff.2 fun N => hTest N _ (continuous_bumpL a b N) (hasCompactSupport_bumpL hab N)
      (tsupport_bumpL hab N) ⟨1, fun t => by
        rw [abs_of_nonneg (bumpL_nonneg a b N t)]; exact bumpL_le_one a b N t⟩
  have hF : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ᶠ k in atTop,
      bdryApprox γ (coordChange (X ω) ψ (Qc γ)) k (IN a b (N + 1)) < ∞ :=
    ae_all_iff.2 fun N => (hD N).ae_bdryApprox_lt_top hX (IN_le hab (N + 1)) hγ hγ2
  filter_upwards [hA, hB, hF, BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2]
    with ω hAω hBω hFω hνω
  set ν := qBoundaryMeasure γ (X ω)
  have : IsLocallyFiniteMeasure ν := hνω.1
  have hfinK : ∀ K, IsCompact K → K ⊆ Ioo a b → targetMeasure ν Φ a b K < ⊤ := by
    intro K hK _
    rw [targetMeasure_apply ν Φ hK.isClosed.measurableSet]
    exact (measure_mono inter_subset_right).trans_lt (hK.image Φ.continuous).measure_lt_top
  refine ⟨?_, hfinK, fun f hf hfc hfs => ?_⟩
  · rw [targetMeasure_apply ν Φ (isOpen_Ioo.measurableSet.compl)]
    have e : Ioo (Φ a) (Φ b) ∩ Φ '' (Ioo a b)ᶜ = ∅ := by
      rw [Set.image_compl_eq Φ.bijective, OrderIso.image_Ioo]
      exact inter_compl_self _
    rw [e, measure_empty]
  · obtain ⟨N, hN⟩ := tsupport_sub_IN hab hfc hfs
    exact tendsto_of_locTest hab N (hFω N)
      (hfinK _ isCompact_Icc (IN_sub_Ioo hab (N + 1))) (hAω N) (hBω N) hf hN

end CoordChange
end QuantumZipper
