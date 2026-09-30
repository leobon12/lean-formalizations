import QuantumZipper.Proofs.Thm14.FcRPairFixedBasic
import QuantumZipper.Proofs.Thm14.FcRPairReduce

/-!
# FCR-PAIR, part 3: the fixed-driver limit from deterministic semicircle approximations

`SemiApprox κ T c s ψ` says that `ψ j` are smooth probability densities with compact support in
`ℍ` which approximate the semicircle `fc(c, s)` in the two deterministic senses needed, for
**every** continuous driver `W` (with `f = revMap W T`):

* energy: `kernelCov2 neumannH (ψ_j dz ∘ f⁻¹, fc(c,s) ∘ f⁻¹)` (same pair twice) `→ 0`;
* the deterministic part: `∫ ψ_j 𝔥_T → ∫ 𝔥_T d fc(c,s)`.

`fcRFixedLimit_of_semiApprox` proves `FcRFixedLimit` (hence, with `fcRPairingLimit_of_fixed`,
`FcRPairingLimit`) from the existence of such sequences (`SemiApproxExists`), with
`ρ_j = ψ¹_j − ψ⁰_j`. For a fixed driver, a.s.

  `pairRaw h ρ_j − (h(fc_1) − h(fc_0)) = det_j + (X Ψ¹_j − X S₁) − (X Ψ⁰_j − X S₀)`

(`Ψ = ψ dz ∘ f⁻¹`, `S = fc ∘ f⁻¹`; RC1 for the pushforwards, `CharFun.cond_Y2f`,
`CharFun.ae_lin_push`), and the two Gaussian differences are controlled by Chebyshev
(`prob_ge_le_kernelCov2`). Own bookkeeping; the analytic inputs are the fields of `SemiApprox`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm14WDG

open CharFun

/-- Deterministic semicircle approximation by smooth probability densities (see module doc). -/
structure SemiApprox (κ T : ℝ) (c : ℂ) (s : ℝ) (ψ : ℕ → TestFun H) : Prop where
  nonneg : ∀ j z, 0 ≤ (ψ j).1 z
  mass : ∀ j, ∫ z, (ψ j).1 z = 1
  energy : ∀ W : ℝ → ℝ, Continuous W →
    Tendsto (fun j => kernelCov2 neumannH
      ((tdens (ψ j).1).map (revMap W T), (foldedCircle c s).map (revMap W T))
      ((tdens (ψ j).1).map (revMap W T), (foldedCircle c s).map (revMap W T))) atTop (𝓝 0)
  det : ∀ W : ℝ → ℝ, Continuous W →
    Tendsto (fun j => ∫ z, (ψ j).1 z * hTrev κ W T z) atTop
      (𝓝 (∫ z, hTrev κ W T z ∂(foldedCircle c s)))

/-- Existence of semicircle approximations for every real centre and positive radius. -/
def SemiApproxExists : Prop :=
  ∀ κ T : ℝ, 0 < κ → 0 < T → ∀ (c s : ℝ), 0 < s → ∃ ψ : ℕ → TestFun H, SemiApprox κ T c s ψ

theorem tdens_neg_eq_zero {a : ℂ → ℝ} (ha : ∀ z, 0 ≤ a z) : tdens (fun z => -a z) = 0 := by
  unfold tdens
  have : (fun z => ENNReal.ofReal (-a z)) = 0 := funext fun z => by
    simp [ENNReal.ofReal_eq_zero.2 (neg_nonpos.2 (ha z))]
  rw [this, withDensity_zero]

/-- The balanced admissible pair `(ψ dz ∘ f⁻¹, fc(c,s) ∘ f⁻¹)`. -/
theorem exists_bpair {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (ψ : TestFun H)
    (h0 : ∀ z, 0 ≤ ψ.1 z) (h1 : ∫ z, ψ.1 z = 1) (c : ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ p : WedgeTK.BPair,
      p.1 = ((tdens ψ.1).map (revMap W T), (foldedCircle c s).map (revMap W T)) := by
  obtain ⟨M, δ, hd⟩ := exists_dens ψ
  have hm := TwoPoint.measurable_revMap hW hT
  have : IsFiniteMeasure (tdens ψ.1) := hd.admissible.1
  have hA := admissible_of_regular (tdens_push_regular hW hT hd)
  have hB := admissible_of_regular (fc_push_regular hW hT c hs)
  refine ⟨⟨_, hA, hB, ?_⟩, rfl⟩
  rw [Measure.map_apply hm MeasurableSet.univ, Measure.map_apply hm MeasurableSet.univ,
    preimage_univ, measure_univ (μ := foldedCircle c s), tdens, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (TReg.integrable_tf ψ)
      (ae_of_all _ h0), h1, ENNReal.ofReal_one]

section Fixed

variable {κ T : ℝ} (hT : 0 < T) {d : ℂ} {r : ℝ} (hr : 0 < r) {ψ₁ ψ₀ : ℕ → TestFun H}
  (h1 : SemiApprox κ T d r ψ₁) (h0 : SemiApprox κ T 0 1 ψ₀) (f : C(Icc (0 : ℝ) T, ℝ))
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
  (hX : IsFreeGFFModConstH X P)
include hT hr h1 h0 hX

/-- The a.s. decomposition of the error for a fixed driver. -/
theorem ae_error_split (j : ℕ) :
    ∀ᵐ ω ∂P, pairRaw (couplingFieldRev κ (Wof κ T hT.le f) T (X ω))
        (TReg.tfLin (-1) (ψ₀ j) (ψ₁ j)).1 -
      (couplingFieldRev κ (Wof κ T hT.le f) T (X ω) (foldedCircle d r) -
        couplingFieldRev κ (Wof κ T hT.le f) T (X ω) (foldedCircle 0 1)) =
      ((Xfun κ (Wof κ T hT.le f) T (ψ₁ j).1 -
          ∫ z, hTrev κ (Wof κ T hT.le f) T z ∂(foldedCircle d r)) -
        (Xfun κ (Wof κ T hT.le f) T (ψ₀ j).1 -
          ∫ z, hTrev κ (Wof κ T hT.le f) T z ∂(foldedCircle 0 1))) +
      (X ω ((tdens (ψ₁ j).1).map (revMap (Wof κ T hT.le f) T)) -
        X ω ((foldedCircle d r).map (revMap (Wof κ T hT.le f) T))) -
      (X ω ((tdens (ψ₀ j).1).map (revMap (Wof κ T hT.le f) T)) -
        X ω ((foldedCircle 0 1).map (revMap (Wof κ T hT.le f) T))) := by
  have hW := continuous_Wof κ T hT.le f
  have hm := TwoPoint.measurable_revMap hW hT.le
  have : IsProbabilityMeasure ((foldedCircle d r).map (revMap (Wof κ T hT.le f) T)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ((foldedCircle 0 1).map (revMap (Wof κ T hT.le f) T)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have e1 := cond_Y2f κ T hT.le hX (TReg.tfLin (-1) (ψ₀ j) (ψ₁ j)) f
  have e2 := ae_lin_push hX (goodMap_Wof κ T hT.le f) (ψ₀ j) (ψ₁ j)
    (TReg.tfLin (-1) (ψ₀ j) (ψ₁ j)) (-1) (fun z => rfl)
  have e3 := ae_evalReg_eq_of_regular hX (fc_push_regular hW hT.le d hr)
  have e4 := ae_evalReg_eq_of_regular hX (fc_push_regular hW hT.le 0 one_pos)
  have hlin := integral_lin (continuousOn_hTrev κ hW hT.le) (ψ₀ j) (ψ₁ j)
    (TReg.tfLin (-1) (ψ₀ j) (ψ₁ j)) (-1) (fun z => rfl)
  rw [tdens_neg_eq_zero (h0.nonneg j), tdens_neg_eq_zero (h1.nonneg j)] at e2
  filter_upwards [e1, e2, e3, e4] with ω e1 e2 e3 e4
  rw [← TReg.Y2f_eq, e1, e2, TReg.Y2f_eq, TReg.couplingFieldRev_apply,
    TReg.couplingFieldRev_apply, e3, e4]
  unfold Xfun
  rw [hlin]
  ring

/-- **Fixed driver.** The pairings with `ψ¹_j − ψ⁰_j` converge in probability to the balanced
semicircle value. -/
theorem tendstoInMeasure_fixed :
    TendstoInMeasure P (fun j ω => pairRaw (couplingFieldRev κ (Wof κ T hT.le f) T (X ω))
        (TReg.tfLin (-1) (ψ₀ j) (ψ₁ j)).1) atTop
      (fun ω => couplingFieldRev κ (Wof κ T hT.le f) T (X ω) (foldedCircle d r) -
        couplingFieldRev κ (Wof κ T hT.le f) T (X ω) (foldedCircle 0 1)) := by
  have hW := continuous_Wof κ T hT.le f
  set W := Wof κ T hT.le f with hWdef
  set F := revMap W T with hF
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  set e := ε / 3 with he
  have he0 : 0 < e := by positivity
  set det : ℕ → ℝ := fun j => (Xfun κ W T (ψ₁ j).1 - ∫ z, hTrev κ W T z ∂(foldedCircle d r)) -
    (Xfun κ W T (ψ₀ j).1 - ∫ z, hTrev κ W T z ∂(foldedCircle 0 1)) with hdet
  set V : (ℕ → TestFun H) → ℂ → ℝ → ℕ → ℝ := fun ψ c s j => kernelCov2 neumannH
    ((tdens (ψ j).1).map F, (foldedCircle c s).map F)
    ((tdens (ψ j).1).map F, (foldedCircle c s).map F) with hV
  have hdet0 : Tendsto det atTop (𝓝 0) := by
    have := ((h1.det W hW).sub_const (∫ z, hTrev κ W T z ∂(foldedCircle d r))).sub
      ((h0.det W hW).sub_const (∫ z, hTrev κ W T z ∂(foldedCircle 0 1)))
    simp only [sub_self] at this
    exact this
  have key : ∀ j, |det j| < e → P {ω | ε ≤ ‖pairRaw (couplingFieldRev κ W T (X ω))
        (TReg.tfLin (-1) (ψ₀ j) (ψ₁ j)).1 - (couplingFieldRev κ W T (X ω) (foldedCircle d r) -
        couplingFieldRev κ W T (X ω) (foldedCircle 0 1))‖} ≤
      ENNReal.ofReal (V ψ₁ d r j / e ^ 2) + ENNReal.ofReal (V ψ₀ 0 1 j / e ^ 2) := by
    intro j hj
    obtain ⟨p1, hp1⟩ := exists_bpair hW hT.le (ψ₁ j) (h1.nonneg j) (h1.mass j) d hr
    obtain ⟨p0, hp0⟩ := exists_bpair hW hT.le (ψ₀ j) (h0.nonneg j) (h0.mass j) 0 one_pos
    have b1 := prob_ge_le_kernelCov2 hX p1 he0
    have b0 := prob_ge_le_kernelCov2 hX p0 he0
    rw [hp1] at b1
    rw [hp0] at b0
    refine le_trans (measure_mono_ae ?_) ((measure_union_le _ _).trans (add_le_add b1 b0))
    filter_upwards [ae_error_split hT hr h1 h0 f hX j] with ω hω hmem
    simp only [Real.norm_eq_abs] at hmem
    rw [hω] at hmem
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hc
    have := abs_add_three (det j)
      (X ω ((tdens (ψ₁ j).1).map F) - X ω ((foldedCircle d r).map F))
      (-(X ω ((tdens (ψ₀ j).1).map F) - X ω ((foldedCircle 0 1).map F)))
    rw [abs_neg] at this
    have h3 : ε = e + e + e := by rw [he]; ring
    have : |det j + (X ω ((tdens (ψ₁ j).1).map F) - X ω ((foldedCircle d r).map F)) -
        (X ω ((tdens (ψ₀ j).1).map F) - X ω ((foldedCircle 0 1).map F))| < ε := by
      rw [sub_eq_add_neg]; linarith [hc.1, hc.2]
    exact absurd hmem (not_le.2 this)
  have hVlim : Tendsto (fun j => ENNReal.ofReal (V ψ₁ d r j / e ^ 2) +
      ENNReal.ofReal (V ψ₀ 0 1 j / e ^ 2)) atTop (𝓝 0) := by
    have t1 := ENNReal.tendsto_ofReal ((h1.energy W hW).div_const (e ^ 2))
    have t0 := ENNReal.tendsto_ofReal ((h0.energy W hW).div_const (e ^ 2))
    simpa using t1.add t0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hVlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [(tendsto_order.1 (hdet0.abs.trans (by rw [abs_zero]))).2 e he0] with j hj
  exact key j hj

end Fixed

/-- **FCR-PAIR (fixed driver)** from deterministic semicircle approximations. -/
theorem fcRFixedLimit_of_semiApprox (h : SemiApproxExists) : FcRFixedLimit := by
  intro κ hκ _ T hT d k
  obtain ⟨ψ₁, h1⟩ := h κ T hκ hT d (radius k) (radius_pos k)
  obtain ⟨ψ₀, h0⟩ := h κ T hκ hT 0 1 one_pos
  rw [Complex.ofReal_zero] at h0
  refine ⟨fun j => TReg.tfLin0 (-1) (ψ₀ j) (ψ₁ j) (by rw [h0.mass, h1.mass]; ring), ?_⟩
  intro f Ω _ P _ X hX
  exact tendstoInMeasure_fixed hT (radius_pos k) h1 h0 f hX

/-- **FCR-PAIR** (`FcRPairingLimit`) from deterministic semicircle approximations. -/
theorem fcRPairingLimit_of_semiApprox (h : SemiApproxExists) : FcRPairingLimit :=
  fcRPairingLimit_of_fixed (fcRFixedLimit_of_semiApprox h)

end Thm14WDG
end QuantumZipper
