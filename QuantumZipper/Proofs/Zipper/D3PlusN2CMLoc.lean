import QuantumZipper.Proofs.Zipper.D3PlusN2CM

/-!
# D3⁺(i), node N2-CM-loc: the local Cameron–Martin bound from the free-field bound and a cutoff

Task D3P-N2 (decision D24). Reduces `D3PlusIN2FixCMLocStmt` (`D3PlusN2CM.lean`) to

* `CMIncrStmt`: the Cameron–Martin total-variation bound for the balanced increments of a free
  field under a `C²`, compactly supported, reflection-even shift `ψ`,
  `|E F(incr(X + ψ)) − E F(incr X)| ≤ √(exp E_H(ψ) − 1)` — exactly the shape of
  `CMTV.abs_integral_incr_shift_sub_le` (task CM-TV, `Proofs/GFF/CameronMartinTV.lean`, in
  progress; Berestycki–Powell arXiv:2004.04720 Lemmas 3.12, 3.14, p. 79). `balIncr` here is
  definitionally `CMTV.incr`.
* `N2CutoffStmt`: for `h` admissible with `h 0 = 0` and every `η > 0`, for all small `ε` there is
  a `C²` compactly supported even `ψ` supported in `ball 0 r`, equal to `h` on
  `closedBall 0 ε ∩ Hbar`, with `E_H(ψ) ≤ η` (the cutoff `χ(·/ε)·(h ∘ foldH)`: `|h| = O(ε)` and
  `|∇h| = O(1)` on `B(0, 2ε)`, so `E_H(ψ) = O(ε²)`; D24).

Key identity (half-disc Markov decomposition, node L2): for an `ε`-local `μ` (`ε ≤ r`),
`Z μ = X μ − X (bal μ)` is the balanced increment at `(μ, bal μ)` (`K3.localIdx`), and since
`bal μ` gives no mass to `ball 0 r ⊇ tsupport ψ` while `ψ = h` on the support of `μ`, the same
increment of `X + ofFun ψ` is `Z μ + ∫ h dμ`. So the pair of laws in `D3PlusIN2FixCMLocStmt` is the
image of the pair `(law incr X, law incr (X + ofFun ψ))` under one measurable map.
(Own elementary argument for the reduction.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace D3Plus

/-- Balanced increments of a field sample (definitionally `CMTV.incr`). -/
def balIncr (x : FieldSample) (j : K3.BalIdx) : ℝ := x j.1.1 - x j.1.2

theorem measurable_balIncr : Measurable balIncr :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- **Cameron–Martin TV bound for the increments of the free field** (shape of
`CMTV.abs_integral_incr_shift_sub_le`). -/
def CMIncrStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) (ψ : ℂ → ℝ), IsFreeGFFModConstH X P → ContDiff ℝ 2 ψ →
    HasCompactSupport ψ → (∀ z, ψ (conj z) = ψ z) →
    ∀ F : (K3.BalIdx → ℝ) → ℝ, Measurable F → (∀ x, |F x| ≤ 1) →
      |∫ ω, F (balIncr (X ω + ofFun ψ)) ∂P - ∫ ω, F (balIncr (X ω)) ∂P| ≤
        Real.sqrt (Real.exp (dirichletEnergyOn H ψ) - 1)

/-- **Cutoff with small Dirichlet energy** (D24). -/
def N2CutoffStmt : Prop :=
  ∀ (r : ℝ) (h : ℂ → ℝ), 0 < r → AdmCorr r h → h 0 = 0 → ∀ η : ℝ, 0 < η →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ ∧ HasCompactSupport ψ ∧
      (∀ z, ψ (conj z) = ψ z) ∧ tsupport ψ ⊆ Metric.ball 0 r ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) ε ∩ Hbar, ψ z = h z) ∧ dirichletEnergyOn H ψ ≤ η

theorem isLocalH_mono {ε r : ℝ} (hεr : ε ≤ r) {μ : Measure ℂ} (hμ : K3.IsLocalH 0 ε μ) :
    K3.IsLocalH 0 r μ := by
  obtain ⟨hadm, r', hr', hμr'⟩ := hμ
  exact ⟨hadm, r', hr'.trans_le hεr, hμr'⟩

/-- Reading the `ε`-local part from the balanced increments. -/
def incrToLoc {r : ℝ} (hr : 0 < r) (ε : ℝ) (hεr : ε ≤ r) (v : K3.BalIdx → ℝ) :
    LocIdx ε → ℝ := fun μ => v (K3.localIdx hr ⟨μ.1, isLocalH_mono hεr μ.2⟩)

theorem measurable_incrToLoc {r : ℝ} (hr : 0 < r) (ε : ℝ) (hεr : ε ≤ r) :
    Measurable (incrToLoc hr ε hεr) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem incrToLoc_balIncr {r : ℝ} (hr : 0 < r) {ε : ℝ} (hεr : ε ≤ r) {Ω : Type*}
    (X : Ω → FieldSample) (ω : Ω) :
    incrToLoc hr ε hεr (balIncr (X ω)) = resField ε (locZField X r ω) := by
  funext μ
  rw [resField, locZField_apply_of_local X ω (isLocalH_mono hεr μ.2)]
  rfl

theorem incrToLoc_balIncr_shift {r : ℝ} (hr : 0 < r) {ε : ℝ} (hεr : ε ≤ r) {Ω : Type*}
    (X : Ω → FieldSample) (ω : Ω) {h ψ : ℂ → ℝ}
    (hψs : tsupport ψ ⊆ Metric.ball 0 r) (hψh : ∀ z ∈ Metric.closedBall (0 : ℂ) ε ∩ Hbar, ψ z = h z) :
    incrToLoc hr ε hεr (balIncr (X ω + ofFun ψ)) =
      resField ε (locZField X r ω) + pairShift ε h := by
  funext μ
  obtain ⟨⟨hfin, ⟨K, hK, hKH, hμK⟩, -⟩, r', hr', hμr'⟩ := μ.2
  have h1 : ∫ z, ψ z ∂μ.1 = ∫ z, h z ∂μ.1 := by
    refine integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμK,
      measure_eq_zero_iff_ae_notMem.1 hμr'] with z hz1 hz2
    refine hψh z ⟨Metric.closedBall_subset_closedBall hr'.le (by simpa using hz2), hKH ?_⟩
    simpa using hz1
  have h2 : ∫ z, ψ z ∂(K3.bal 0 r μ.1) = 0 := by
    refine integral_eq_zero_of_ae ?_
    have hb : K3.bal 0 r μ.1 (Metric.ball ((0 : ℝ) : ℂ) r) = 0 := K3.bal_ball hr
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hb] with z hz
    refine image_eq_zero_of_notMem_tsupport fun hz' => hz ?_
    simpa using hψs hz'
  have e := congrFun (incrToLoc_balIncr hr hεr X ω) μ
  simp only [incrToLoc, balIncr, Pi.add_apply, ofFun, K3.localIdx] at e ⊢
  rw [← e, pairShift, h1, h2]
  ring

theorem sub_le_ofReal_of_abs {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) {c : ℝ}
    (h : |b.toReal - a.toReal| ≤ c) : a - b ≤ ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb,
    ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have := neg_le_abs (b.toReal - a.toReal)
  linarith

/-- The Cameron–Martin bound, in TV form, for any measurable reading of the increments. -/
theorem tvDist_incr_shift_le (hCMI : CMIncrStmt) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {ψ : ℂ → ℝ} (hψ2 : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (hψe : ∀ z, ψ (conj z) = ψ z)
    {β : Type*} [MeasurableSpace β] {T : (K3.BalIdx → ℝ) → β} (hT : Measurable T) :
    TV.tvDist (P.map fun ω => T (balIncr (X ω))) (P.map fun ω => T (balIncr (X ω + ofFun ψ))) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp (dirichletEnergyOn H ψ) - 1)) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hg₁ : Measurable fun ω => balIncr (X ω) := measurable_balIncr.comp hXm
  have hg₂ : Measurable fun ω => balIncr (X ω + ofFun ψ) :=
    measurable_balIncr.comp (hXm.add_const _)
  have key : ∀ S : Set β, MeasurableSet S →
      |(P ((fun ω => balIncr (X ω + ofFun ψ)) ⁻¹' (T ⁻¹' S))).toReal -
        (P ((fun ω => balIncr (X ω)) ⁻¹' (T ⁻¹' S))).toReal| ≤
        Real.sqrt (Real.exp (dirichletEnergyOn H ψ) - 1) := by
    intro S hS
    have hA : MeasurableSet (T ⁻¹' S) := hT hS
    have hF : Measurable ((T ⁻¹' S).indicator (1 : (K3.BalIdx → ℝ) → ℝ)) :=
      measurable_one.indicator hA
    have hFb : ∀ x, |(T ⁻¹' S).indicator (1 : (K3.BalIdx → ℝ) → ℝ) x| ≤ 1 := by
      intro x
      by_cases hx : x ∈ T ⁻¹' S <;> simp [hx]
    have h := hCMI P X ψ hX hψ2 hψc hψe _ hF hFb
    have e : ∀ g : Ω → K3.BalIdx → ℝ, Measurable g →
        ∫ ω, (T ⁻¹' S).indicator (1 : (K3.BalIdx → ℝ) → ℝ) (g ω) ∂P =
          (P (g ⁻¹' (T ⁻¹' S))).toReal := by
      intro g hg
      have : (fun ω => (T ⁻¹' S).indicator (1 : (K3.BalIdx → ℝ) → ℝ) (g ω)) =
          (g ⁻¹' (T ⁻¹' S)).indicator 1 := by
        funext ω
        by_cases hω : g ω ∈ T ⁻¹' S <;> simp [Set.indicator, hω]
      rw [this, integral_indicator_one (hg hA)]
      rfl
    rwa [e _ hg₁, e _ hg₂] at h
  refine iSup_le fun S => iSup_le fun hS => sup_le ?_ ?_
  · rw [Measure.map_apply (f := fun ω => T (balIncr (X ω))) (hT.comp hg₁) hS,
      Measure.map_apply (f := fun ω => T (balIncr (X ω + ofFun ψ))) (hT.comp hg₂) hS]
    exact sub_le_ofReal_of_abs (measure_ne_top _ _) (measure_ne_top _ _) (key S hS)
  · rw [Measure.map_apply (f := fun ω => T (balIncr (X ω))) (hT.comp hg₁) hS,
      Measure.map_apply (f := fun ω => T (balIncr (X ω + ofFun ψ))) (hT.comp hg₂) hS]
    refine sub_le_ofReal_of_abs (measure_ne_top _ _) (measure_ne_top _ _) ?_
    rw [abs_sub_comm]
    exact key S hS

/-- **The local Cameron–Martin bound from the free-field bound and a cutoff** (own elementary
reduction; D24). -/
theorem d3PlusIN2FixCMLoc_of_parts (hCMI : CMIncrStmt) (hcut : N2CutoffStmt) :
    D3PlusIN2FixCMLocStmt := by
  intro r Ω _ P _ X h hr hX hh h0
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hc : Tendsto (fun E : ℝ => ENNReal.ofReal (Real.sqrt (Real.exp E - 1))) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun E : ℝ => ENNReal.ofReal (Real.sqrt (Real.exp E - 1)) :=
      ENNReal.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (Real.continuous_exp.sub (continuous_const (y := (1 : ℝ)))))
    simpa using hcont.tendsto 0
  obtain ⟨δ, hδ, hδη⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds hη))
  filter_upwards [hcut r h hr hh h0 (δ / 2) (half_pos hδ), Ioc_mem_nhdsGT hr] with ε hψ hε
  obtain ⟨ψ, hψ2, hψc, hψe, hψs, hψh, hψE⟩ := hψ
  have hεr : ε ≤ r := hε.2
  have hE0 : 0 ≤ dirichletEnergyOn H ψ :=
    mul_nonneg (inv_nonneg.2 (by positivity)) (integral_nonneg fun _ => by positivity)
  have e1 : (fun ω => resField ε (locZField X r ω)) =
      fun ω => incrToLoc hr ε hεr (balIncr (X ω)) :=
    funext fun ω => (incrToLoc_balIncr hr hεr X ω).symm
  have e2 : (fun ω => resField ε (locZField X r ω) + pairShift ε h) =
      fun ω => incrToLoc hr ε hεr (balIncr (X ω + ofFun ψ)) :=
    funext fun ω => (incrToLoc_balIncr_shift hr hεr X ω hψs hψh).symm
  rw [e1, e2]
  refine (tvDist_incr_shift_le hCMI hX hψ2 hψc hψe (measurable_incrToLoc hr ε hεr)).trans
    (le_of_lt (hδη ?_))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hE0]
  linarith

end D3Plus
end QuantumZipper
