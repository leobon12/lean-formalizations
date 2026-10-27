import MatedCRTHarmonic.GMSMain.MainResultsInputs

/-!
# [18] Theorem 1.3 from [18] Theorem 3.2

The boundary-sensitive form of Theorem 1.3 (with Theorem 3.2's boundary condition
`area(B_r(∂D)) ≤ C r`) is a corollary of Theorem 3.2 with the constant `A + 1`, uniform in `f`, and an `f`-dependent
rate constant. This file proves that implication between the two draft anchors, for every frozen coupling:

* `theorem13Body_of_theorem32Body D : Theorem32Body P η bm → Theorem13Body P η bm`.

Proof. Fix `ρ, C`, let `A` be Theorem 3.2's constant and
`A' := A + 1`. Fix `(D, f)` as in Theorem 1.3 and put `E := Energy(f; D)`.
* `E = 0`. Then `∇f = 0` on `D` (`∇f` is continuous on the open `D`, so `|∇f| > 0` at one point would give positive
  energy on a ball), so `f` is constant on `D` (bounded convexity makes `D` connected) and, by continuity, equal to a
  constant `c` on `D̄ ⊇ ∂D`. By T16D's almost sure cellular embedding at every real `ε` (`T16D.ae_cellularEmbeddingAt`)
  and its maximum principle (`T16D.isHarmonicExtension_le`, `_ge`), almost surely `f_ε` exists and every `f_ε` equals
  `c` on `V(D)`, so `Energy(f_ε; G^ε(D)) = 0`: the bad event is null and `C_f = 0` works.
* `E > 0`. `f` and `∇f` are bounded on `D` and `∇f` is `L`-Lipschitz, so `(D, f) ∈ 𝒞_C(ε^β)` as soon as
  `ε ≤ ε₀ := K^{-1/β}` (`K` the largest of these bounds, plus one). For `ε ≤ ε₀` with `ε^α ≤ E`, Theorem 3.2's good
  event gives `Energy(f_ε) ≤ A E + ε^α ≤ (A + 1) E`. Otherwise the failure probability is at most `1`, and
  `1 ≤ ε₀^{-α} ε^α` (when `ε > ε₀`) or `1 ≤ ε^α / E` (when `ε^α > E`). So `C_f := max(C_r, 0) + ε₀^{-α} + E⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

open MatedCRTHarmonic GMS3

/-- A domain with `C`-bounded convexity is preconnected (any two points are joined by a path in it). -/
theorem isPreconnected_of_hasBoundedConvexity {C : ℝ} {D : Set ℂ} (h : HasBoundedConvexity C D) :
    IsPreconnected D := by
  refine isPreconnected_of_forall_pair fun z hz w hw => ?_
  obtain ⟨c, hc, hc0, hc1, hcD, -⟩ := h z hz w hw
  refine ⟨c '' Icc 0 1, ?_, ⟨0, ⟨le_rfl, zero_le_one⟩, hc0⟩, ⟨1, ⟨zero_le_one, le_rfl⟩, hc1⟩,
    isPreconnected_Icc.image c hc⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hcD ht

/-- **Zero Dirichlet energy forces `∇f = 0`** on an open set where `∇f` is continuous. -/
theorem fderiv_eq_zero_of_dirichletEnergy_eq_zero {D : Set ℂ} (hDo : IsOpen D) {f : ℂ → ℝ}
    (hf : DifferentiableOn ℝ f D) (hdf : ContinuousOn (fderiv ℝ f) D) (hE : dirichletEnergy f D hDo hf = 0) :
    EqOn (fderiv ℝ f) 0 D := by
  intro z hz
  by_contra hne
  have hδ : 0 < ‖fderiv ℝ f z‖ := norm_pos_iff.mpr hne
  set δ := ‖fderiv ℝ f z‖ with hδdef
  have hcont : ContinuousAt (fderiv ℝ f) z := hdf.continuousAt (hDo.mem_nhds hz)
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.continuousAt_iff.mp hcont (δ / 2) (by linarith)
  obtain ⟨r₂, hr₂, hr₂'⟩ := Metric.isOpen_iff.mp hDo z hz
  set r := min r₁ r₂ with hrdef
  have hr : 0 < r := lt_min hr₁ hr₂
  have hball : ball z r ⊆ D := (ball_subset_ball (min_le_right _ _)).trans hr₂'
  have hlow : ∀ w ∈ ball z r, ENNReal.ofReal ((δ / 2) ^ 2) ≤ ENNReal.ofReal (‖fderiv ℝ f w‖ ^ 2) := by
    intro w hw
    have hw1 : dist w z < r₁ := lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _)
    have h1 := hr₁' hw1
    rw [dist_eq_norm] at h1
    have h2 : δ / 2 ≤ ‖fderiv ℝ f w‖ := by
      have := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f w)
      rw [norm_sub_rev] at this
      linarith
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) h2 2)
  have hpos : 0 < ENNReal.ofReal ((δ / 2) ^ 2) * volume (ball z r) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' (measure_ball_pos volume z hr).ne'
  have hle : ENNReal.ofReal ((δ / 2) ^ 2) * volume (ball z r) ≤ dirichletEnergy f D hDo hf := by
    rw [← setLIntegral_const]
    calc ∫⁻ _ in ball z r, ENNReal.ofReal ((δ / 2) ^ 2)
        ≤ ∫⁻ w in ball z r, ENNReal.ofReal (‖fderiv ℝ f w‖ ^ 2) :=
          lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_ball hlow)
      _ ≤ ∫⁻ w in D, ENNReal.ofReal (‖fderiv ℝ f w‖ ^ 2) := lintegral_mono_set hball
  rw [hE] at hle
  exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)

/-- **Zero Dirichlet energy on a preconnected open set forces `f` constant on `D̄`** (for `f` continuous on `D̄`). -/
theorem exists_const_of_dirichletEnergy_eq_zero {D : Set ℂ} (hDo : IsOpen D) (hDpc : IsPreconnected D)
    {f : ℂ → ℝ} (hf : DifferentiableOn ℝ f D) (hdf : ContinuousOn (fderiv ℝ f) D)
    (hfc : ContinuousOn f (closure D)) (hE : dirichletEnergy f D hDo hf = 0) :
    ∃ c : ℝ, ∀ z ∈ closure D, f z = c := by
  rcases D.eq_empty_or_nonempty with hemp | ⟨z₀, hz₀⟩
  · exact ⟨0, fun z hz => by rw [hemp, closure_empty] at hz; exact absurd hz (notMem_empty z)⟩
  · have h0 := fderiv_eq_zero_of_dirichletEnergy_eq_zero hDo hf hdf hE
    have hconst : EqOn f (fun _ => f z₀) D := fun z hz =>
      IsOpen.is_const_of_fderiv_eq_zero (𝕜 := ℝ) hDo hDpc hf h0 hz hz₀
    exact ⟨f z₀, fun z hz => hconst.of_subset_closure hfc continuousOn_const subset_closure le_rfl hz⟩

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **The constant case**: for boundary data constant on `∂D`, the good event of Theorem 1.3 holds almost surely
(T16D's cellular embedding at every real mesh and its deterministic maximum principle). -/
theorem measure_bad_eq_zero_of_const
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) {ε : ℝ} (hε : 0 < ε)
    {Dom : Set ℂ} (hDo : IsOpen Dom) (hDb : Bornology.IsBounded Dom) {f : ℂ → ℝ}
    (hf : DifferentiableOn ℝ f Dom) {c : ℝ} (hc : ∀ z ∈ frontier Dom, f z = c) (K : ℝ≥0∞) :
    P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
      (∃ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) Dom f g) ∧
      ∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) Dom f g →
        energyOn (MatedCRT.graph ε (bm ω) h) (verticesMeeting (cell ε (η ω)) Dom) g ≤
          K * dirichletEnergy f Dom hDo hf} = 0 := by
  have hfc : ContinuousOn f (frontier Dom) :=
    continuousOn_const.congr fun z hz => hc z hz
  have hae := T16D.ae_cellularEmbeddingAt D hε
  rw [ae_iff] at hae
  refine measure_mono_null (fun ω hω => ?_) hae
  intro hemb
  apply hω
  obtain ⟨h, H, hH⟩ := hemb
  have hconn := Implementation.matedCRT_graph_connected_impl ε (bm ω) h
  have hHc : H.cell = cell ε (η ω) := hH
  refine ⟨h, ?_, fun g' hg' => ?_⟩
  · rw [← hHc]
    exact ⟨_, T16D.isHarmonicExtension_dirichletSol H hDb hfc⟩
  rw [← hHc] at hg' ⊢
  have hconst : ∀ x ∈ verticesMeeting H.cell Dom, g' x = c := fun x hx =>
    le_antisymm (T16D.isHarmonicExtension_le H hconn hDo hDb hfc hg' (fun z hz => (hc z hz).le) x hx)
      (T16D.isHarmonicExtension_ge H hconn hDo hDb hfc hg' (fun z hz => (hc z hz).ge) x hx)
  rw [energyOn_eq_zero_of_eqOn _ hconst]
  exact bot_le

/-- **[18] Theorem 1.3 (repaired) from [18] Theorem 3.2, for one frozen coupling**:
the draft body of `matedCRT_energy_le_add_of_matingOfTrees` implies the draft body of
`matedCRT_energy_le_of_matingOfTrees`, with the same `α`, the constant `A + 1` and an `f`-dependent rate constant. -/
theorem theorem13Body_of_theorem32Body
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (h32 : Theorem32Body P η bm) : Theorem13Body P η bm := by
  have := D.isProbabilityMeasure
  obtain ⟨α, hα, β, hβ, h32⟩ := h32
  refine ⟨α, hα, fun ρ hρ0 hρ1 C hC => ?_⟩
  obtain ⟨A, hA, Cr, h32⟩ := h32 ρ hρ0 hρ1 C hC
  refine ⟨A + 1, by linarith, fun Dom hDo hDsub hbc hbdry f hf hdf hL hfc => ?_⟩
  have hDb : Bornology.IsBounded Dom := isBounded_ball.subset hDsub
  set E := dirichletEnergy f Dom hDo hf with hEdef
  by_cases hE0 : E = 0
  · -- constant boundary data
    obtain ⟨c, hc⟩ := exists_const_of_dirichletEnergy_eq_zero hDo
      (isPreconnected_of_hasBoundedConvexity hbc) hf hdf hfc hE0
    refine ⟨0, fun ε hε0 _ => ?_⟩
    rw [measure_bad_eq_zero_of_const D hε0 hDo hDb hf (fun z hz => hc z (frontier_subset_closure hz))]
    exact bot_le
  · -- the bounds making `(D, f) ∈ 𝒞_C(ε^β)` for small `ε`
    obtain ⟨M₁, hM₁⟩ := hDb.isCompact_closure.exists_bound_of_continuousOn hfc
    obtain ⟨L, hL⟩ := hL
    obtain ⟨M₂, hM₂⟩ : ∃ M₂ : ℝ, ∀ z ∈ Dom, ‖fderiv ℝ f z‖ ≤ M₂ := by
      rcases Dom.eq_empty_or_nonempty with hemp | ⟨z₀, hz₀⟩
      · exact ⟨0, fun z hz => by rw [hemp] at hz; exact absurd hz (notMem_empty z)⟩
      · refine ⟨‖fderiv ℝ f z₀‖ + L * (2 * ρ), fun z hz => ?_⟩
        have h1 := hL.dist_le_mul z hz z₀ hz₀
        have h2 : dist z z₀ ≤ 2 * ρ := by
          have a := mem_ball_zero_iff.mp (hDsub hz)
          have b := mem_ball_zero_iff.mp (hDsub hz₀)
          calc dist z z₀ ≤ ‖z‖ + ‖z₀‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
            _ ≤ 2 * ρ := by linarith
        have h3 : ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f z₀‖ + dist (fderiv ℝ f z) (fderiv ℝ f z₀) := by
          rw [dist_eq_norm]
          have := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f z₀)
          linarith
        have h4 : (L : ℝ) * dist z z₀ ≤ L * (2 * ρ) := mul_le_mul_of_nonneg_left h2 L.2
        linarith
    set K : ℝ := max (max (L : ℝ) M₁) M₂ + 1 with hKdef
    have hLK : (L : ℝ) ≤ K := by
      have := le_max_left (L : ℝ) M₁
      have := le_max_left (max (L : ℝ) M₁) M₂
      linarith
    have hM₁K : M₁ ≤ K := by
      have := le_max_right (L : ℝ) M₁
      have := le_max_left (max (L : ℝ) M₁) M₂
      linarith
    have hM₂K : M₂ ≤ K := by
      have := le_max_right (max (L : ℝ) M₁) M₂
      linarith
    have hK1 : 1 ≤ K := by
      have := le_max_left (L : ℝ) M₁
      have := le_max_left (max (L : ℝ) M₁) M₂
      linarith [NNReal.coe_nonneg L]
    have hK0 : 0 < K := by linarith
    set ε₀ : ℝ := K ^ (-(1 / β)) with hε₀def
    have hε₀0 : 0 < ε₀ := Real.rpow_pos_of_pos hK0 _
    have hε₀K : ε₀ ^ (-β) = K := by
      rw [hε₀def, ← Real.rpow_mul hK0.le]
      have : -(1 / β) * -β = 1 := by field_simp
      rw [this, Real.rpow_one]
    have hKε : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → K ≤ ε ^ (-β) := fun ε hε hεε₀ => by
      rw [← hε₀K]
      exact Real.rpow_le_rpow_of_nonpos hε hεε₀ (by linarith)
    set Cf : ℝ := max Cr 0 + ε₀ ^ (-α) + (E.toReal)⁻¹ with hCfdef
    have hε₀α : 0 ≤ ε₀ ^ (-α) := (Real.rpow_pos_of_pos hε₀0 _).le
    have hEinv : 0 ≤ (E.toReal)⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    refine ⟨Cf, fun ε hε0 hε1 => ?_⟩
    have hεα : 0 ≤ ε ^ α := Real.rpow_nonneg hε0.le α
    by_cases hsmall : ε ≤ ε₀ ∧ ENNReal.ofReal (ε ^ α) ≤ E
    · -- Theorem 3.2 applies, and its additive error is absorbed
      have hKε' := hKε ε hε0 hsmall.1
      have hbad := h32 ε hε0 hε1 Dom hDo hDsub hbdry hbc f hf
        (fun z hz w hw => by
          have h1 := hL.dist_le_mul z hz w hw
          rw [dist_eq_norm] at h1
          exact h1.trans (mul_le_mul_of_nonneg_right (hLK.trans hKε') dist_nonneg))
        (fun z hz => by
          have := hM₁ z (subset_closure hz)
          rw [Real.norm_eq_abs] at this
          linarith)
        (fun z hz => (hM₂ z hz).trans (hM₂K.trans hKε')) hfc
      refine le_trans (measure_mono ?_) (hbad.trans (ENNReal.ofReal_le_ofReal ?_))
      · intro ω hω hgood
        apply hω
        obtain ⟨h, hex, hall⟩ := hgood
        refine ⟨h, hex, fun g hg => (hall g hg).trans ?_⟩
        calc ENNReal.ofReal A * E + ENNReal.ofReal (ε ^ α) ≤ ENNReal.ofReal A * E + E :=
              add_le_add_right hsmall.2 _
          _ = ENNReal.ofReal (A + 1) * E := by
              rw [ENNReal.ofReal_add hA.le zero_le_one, ENNReal.ofReal_one, add_mul, one_mul]
      · refine mul_le_mul_of_nonneg_right ?_ hεα
        have := le_max_left Cr 0
        linarith
    · -- the failure probability is at most `1 ≤ C_f ε^α`
      refine le_trans prob_le_one ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hrest : 0 ≤ max Cr 0 * ε ^ α := mul_nonneg (le_max_right _ _) hεα
      have hCf : Cf * ε ^ α = max Cr 0 * ε ^ α + ε₀ ^ (-α) * ε ^ α + (E.toReal)⁻¹ * ε ^ α := by
        rw [hCfdef]; ring
      rcases not_and_or.mp hsmall with h1 | h2
      · -- `ε > ε₀`
        have hlt : ε₀ < ε := lt_of_not_ge h1
        have h3 : ε₀ ^ α ≤ ε ^ α := Real.rpow_le_rpow hε₀0.le hlt.le hα.le
        have h4 : ε₀ ^ (-α) * ε₀ ^ α = 1 := by
          rw [Real.rpow_neg hε₀0.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hε₀0 α).ne']
        have h5 : ε₀ ^ (-α) * ε₀ ^ α ≤ ε₀ ^ (-α) * ε ^ α := mul_le_mul_of_nonneg_left h3 hε₀α
        have h6 : 0 ≤ (E.toReal)⁻¹ * ε ^ α := mul_nonneg hEinv hεα
        linarith
      · -- `ε^α > E`
        have hlt : E < ENNReal.ofReal (ε ^ α) := lt_of_not_ge h2
        have hEtop : E ≠ ⊤ := ne_top_of_lt hlt
        have hEr : E.toReal < ε ^ α := (ENNReal.lt_ofReal_iff_toReal_lt hEtop).mp hlt
        have hEpos : 0 < E.toReal := ENNReal.toReal_pos hE0 hEtop
        have h4 : (E.toReal)⁻¹ * E.toReal = 1 := inv_mul_cancel₀ hEpos.ne'
        have h5 : (E.toReal)⁻¹ * E.toReal ≤ (E.toReal)⁻¹ * ε ^ α :=
          mul_le_mul_of_nonneg_left hEr.le hEinv
        have h6 : 0 ≤ ε₀ ^ (-α) * ε ^ α := mul_nonneg hε₀α hεα
        linarith

end MatedCRTHarmonic.GMSMain.MainResults
