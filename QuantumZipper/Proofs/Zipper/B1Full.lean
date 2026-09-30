import QuantumZipper.Proofs.Zipper.TReg

/-!
# B1-FULL: unzipping preserves the `lawData` law, modulo the additive constant

`E_BRANCH_BLUEPRINT.md` §3 (B1-FULL), `AUDIT3.md` §4.1. For `κ > 0`, `γ = √κ`, `t > 0`, a
Brownian motion `B` and an independent free-boundary GFF `X` (modulo constants), let
`𝒵 = (𝔥₀ + X, √κ B)` and let `N y = addConst y (−y(fc(0,1)))` (`nrm`, the normalization
`PalmNorm.normAt (foldedCircle 0 1)`). Then (`b1_full`) the joint law of
`(lawData (N (unzippedField γ 𝒵 t)), s ↦ W(t+s) − W(t))` equals the joint law of
`(lawData (N (𝔥₀ + X)), W)`.

**Route** (handoff `B1-FULL.md`). Theorem 1.2 (`theorem1_2_holds`) gives B1 at the level of
mass-zero pairings (`UnzipInvariance.unzip_invariance`). Every coordinate of `lawData ∘ N` is an
almost sure limit, along a subsequence, of mass-zero pairings, for both fields:
`y(C_i) − y(fc(0,1)) = lim pairRaw y (m_i − m_⋆)` and
`pairRaw (N y) ρ = lim pairRaw y (ρ − (∫ρ) m_⋆)`, with the mollifiers `m` of `TReg`
(`TReg.tendstoInMeasure_pairRaw_moll_h0rev` for `𝔥₀ + X`,
`TReg.tendstoInMeasure_pairRaw_moll_random` for the reverse coupling field, to which the unzipped
field reduces by REG-SPLIT: `ae_unzip_fc_eq` and `UnzipInvariance.ae_pairRaw_unzip_eq_Y2f`), plus
linearity of the pairings. So both data are the same measurable function `Φ` of the respective
mass-zero pairing data and driver, coordinate by coordinate almost surely, and the laws agree.
Laws on product spaces are determined coordinatewise (`map_eq_of_ae_coords`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B1Full

open CharFun UnzipInvariance UnzipFull TReg

/-! ## 1. Normalization -/

/-- Normalization of a field at the unit folded circle (`= PalmNorm.normAt (foldedCircle 0 1)`). -/
def nrm (y : FieldSample) : FieldSample := addConst y (-(y (foldedCircle 0 1)))

theorem coordsFull_nrm (y : FieldSample) (i : ℕ) :
    CoordsFull.coordsFull (nrm y) i =
      y (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) -
        y (foldedCircle 0 1) := by
  simp only [CoordsFull.coordsFull, nrm, addConst, measure_univ, ENNReal.toReal_one, mul_one]
  ring

theorem tdens_univ_sub (ρ : TestFun H) :
    (tdens ρ.1 univ).toReal - (tdens (fun z => -ρ.1 z) univ).toReal = ∫ z, ρ.1 z := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_tf ρ), tdens, tdens,
    withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem pairRaw_nrm (y : FieldSample) (ρ : TestFun H) :
    pairRaw (nrm y) ρ.1 = pairRaw y ρ.1 - y (foldedCircle 0 1) * ∫ z, ρ.1 z := by
  rw [← tdens_univ_sub]
  simp only [pairRaw, nrm, addConst, tdens]
  ring

theorem measurable_lawData_nrm {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample}
    (hc : ∀ (w : ℂ) (r : ℝ), 0 < r → Measurable fun ω => Y ω (foldedCircle w r))
    (hp : ∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y ω) ρ.1) :
    Measurable (lawData fun ω => nrm (Y ω)) := by
  unfold lawData
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · simp only [coordsFull_nrm]
    exact (hc _ _ (fullIndex_radius_pos i)).sub (hc 0 1 one_pos)
  · simp only [pairRaw_nrm]
    exact (hp ρ).sub ((hc 0 1 one_pos).mul_const _)

/-! ## 2. Measurability and REG-SPLIT for the unzipped field -/

theorem measurable_integral_log_deriv_gen (κ T : ℝ) (hT : 0 ≤ T) (μ : Measure ℂ) [SFinite μ]
    (hμ : μ Hᶜ = 0) :
    Measurable fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ z, Real.log ‖deriv (revMap (Wof κ T hT f) T) z‖ ∂μ := by
  have hae : ∀ᵐ z ∂μ, z ∈ H := ae_iff.2 hμ
  have heq : ∀ f : C(Icc (0 : ℝ) T, ℝ),
      ∫ z, Real.log ‖deriv (revMap (Wof κ T hT f) T) z‖ ∂μ =
        ∫ z, Real.log ‖Dm κ T hT (f, z)‖ ∂μ := fun f =>
    integral_congr_ae (hae.mono fun z hz => by
      show Real.log ‖deriv (revMap (Wof κ T hT f) T) z‖ = Real.log ‖Dm κ T hT (f, z)‖
      rw [Dm_eq κ T hT f hz])
  rw [show (fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ z, Real.log ‖deriv (revMap (Wof κ T hT f) T) z‖ ∂μ) = _ from funext heq]
  exact ((Real.measurable_log.comp (measurable_Dm κ T hT).norm).stronglyMeasurable.integral_prod_right').measurable

theorem measurable_unzip_apply (κ T : ℝ) (hT : 0 ≤ T) (μ : Measure ℂ) [SFinite μ]
    (hμ : μ Hᶜ = 0) :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      coordChange (ofFun (h0rev κ) + p.2) (revMap (Wof κ T hT p.1) T) (Qc (Real.sqrt κ)) μ := by
  unfold coordChange
  exact (measurable_evalReg_h0rev_push_gen κ T hT μ).add
    (measurable_const.mul ((measurable_integral_log_deriv_gen κ T hT μ hμ).comp measurable_fst))

/-- **REG-SPLIT at a folded circle, random driver path.** -/
theorem ae_unzip_fc_eq (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g) (hind : IndepFun g X P) (w : ℂ) {r : ℝ}
    (hr : 0 < r) :
    ∀ᵐ ω ∂P, coordChange (ofFun (h0rev κ) + X ω) (revMap (Wof κ T hT (g ω)) T)
        (Qc (Real.sqrt κ)) (foldedCircle w r) =
      couplingFieldRev κ (Wof κ T hT (g ω)) T (X ω) (foldedCircle w r) := by
  filter_upwards [ae_split_fc_random inputs_holds κ hT hX hg hind w hr] with ω hs
  have hWc := continuous_Wof κ T hT (g ω)
  have hWm := measurable_revMap_Wof κ T hT (g ω)
  rw [CouplingMarkov.couplingFieldRev_eq]
  show evalReg (ofFun (h0rev κ) + X ω) ((foldedCircle w r).map (revMap (Wof κ T hT (g ω)) T)) +
      Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (revMap (Wof κ T hT (g ω)) T) z‖
        ∂(foldedCircle w r) =
    ofFun (hTrev κ (Wof κ T hT (g ω)) T) (foldedCircle w r) +
      (evalReg (X ω) ((foldedCircle w r).map (revMap (Wof κ T hT (g ω)) T)) +
        0 * ∫ z, Real.log ‖deriv (revMap (Wof κ T hT (g ω)) T) z‖ ∂(foldedCircle w r))
  rw [hs, zero_mul, add_zero,
    show ofFun (hTrev κ (Wof κ T hT (g ω)) T) (foldedCircle w r) =
      ∫ z, hTrev κ (Wof κ T hT (g ω)) T z ∂(foldedCircle w r) from rfl,
    integral_hTrev_fc inputs_holds κ hWc hT hWm w hr]
  ring

/-! ## 3. Convergence in probability and laws -/

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem tendstoInMeasure_const' (A : Ω → ℝ) :
    TendstoInMeasure P (fun _ : ℕ => A) atTop A := by
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  have : {ω : Ω | δ ≤ ‖A ω - A ω‖} = ∅ := by
    ext ω; simp [not_le.2 hδ]
  simp only [this, measure_empty, tendsto_const_nhds]

theorem tendstoInMeasure_lin {F G : ℕ → Ω → ℝ} {A B : Ω → ℝ}
    (hF : TendstoInMeasure P F atTop A) (hG : TendstoInMeasure P G atTop B) (c : ℝ) :
    TendstoInMeasure P (fun n ω => c * F n ω + G n ω) atTop (fun ω => c * A ω + B ω) := by
  rw [tendstoInMeasure_iff_norm] at hF hG ⊢
  intro δ hδ
  set η := δ / (2 * (|c| + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hsum := (hF η hη0).add (hG (δ / 2) (by positivity))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    (fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _))
  simp only [mem_setOf_eq, mem_union] at hω ⊢
  by_contra hcon
  push_neg at hcon
  have e : c * F n ω + G n ω - (c * A ω + B ω) = c * (F n ω - A ω) + (G n ω - B ω) := by ring
  rw [e] at hω
  have hm := mul_le_mul_of_nonneg_left hcon.1.le (abs_nonneg c)
  have : ‖c * (F n ω - A ω) + (G n ω - B ω)‖ < δ := by
    calc _ ≤ ‖c * (F n ω - A ω)‖ + ‖G n ω - B ω‖ := norm_add_le _ _
      _ = |c| * ‖F n ω - A ω‖ + ‖G n ω - B ω‖ := by rw [norm_mul, Real.norm_eq_abs]
      _ < (|c| + 1) * η + δ / 2 := by nlinarith [hcon.2]
      _ = δ := by rw [hη]; field_simp; ring
  linarith

theorem exists_subseq_ae₂ {F G : ℕ → Ω → ℝ} {A B : Ω → ℝ}
    (hF : TendstoInMeasure P F atTop A) (hG : TendstoInMeasure P G atTop B) :
    ∃ ns : ℕ → ℕ, (∀ᵐ ω ∂P, Tendsto (fun k => F (ns k) ω) atTop (𝓝 (A ω))) ∧
      ∀ᵐ ω ∂P, Tendsto (fun k => G (ns k) ω) atTop (𝓝 (B ω)) := by
  obtain ⟨n1, hn1, h1⟩ := hF.exists_seq_tendsto_ae
  obtain ⟨n2, hn2, h2⟩ := (hG.comp hn1.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨n1 ∘ n2, ?_, h2⟩
  filter_upwards [h1] with ω hω
  exact hω.comp hn2.tendsto_atTop

/-- Laws on `((ι₁ → ℝ) × (ι₂ → ℝ)) × (ι₃ → ℝ)` are determined coordinatewise. -/
theorem map_eq_of_ae_coords [IsFiniteMeasure P] {ι₁ ι₂ ι₃ : Type*}
    {f g : Ω → ((ι₁ → ℝ) × (ι₂ → ℝ)) × (ι₃ → ℝ)} (hf : Measurable f) (hg : Measurable g)
    (h1 : ∀ i, ∀ᵐ ω ∂P, (f ω).1.1 i = (g ω).1.1 i) (h2 : ∀ i, ∀ᵐ ω ∂P, (f ω).1.2 i = (g ω).1.2 i)
    (h3 : ∀ i, ∀ᵐ ω ∂P, (f ω).2 i = (g ω).2 i) : P.map f = P.map g := by
  set e : ((ι₁ ⊕ ι₂) ⊕ ι₃ → ℝ) ≃ᵐ ((ι₁ → ℝ) × (ι₂ → ℝ)) × (ι₃ → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ)
        (MeasurableEquiv.refl _)) with he
  have key : P.map (e.symm ∘ f) = P.map (e.symm ∘ g) := by
    refine map_eq_of_forall_ae_eq (e.symm.measurable.comp hf) (e.symm.measurable.comp hg) ?_
    rintro ((i | i) | i)
    · exact h1 i
    · exact h2 i
    · exact h3 i
  calc P.map f = P.map (e ∘ (e.symm ∘ f)) := by
        rw [show e ∘ (e.symm ∘ f) = f from funext fun ω => e.apply_symm_apply (f ω)]
    _ = (P.map (e.symm ∘ f)).map e := (Measure.map_map e.measurable
        (e.symm.measurable.comp hf)).symm
    _ = (P.map (e.symm ∘ g)).map e := by rw [key]
    _ = P.map (e ∘ (e.symm ∘ g)) := Measure.map_map e.measurable (e.symm.measurable.comp hg)
    _ = P.map g := by
        rw [show e ∘ (e.symm ∘ g) = g from funext fun ω => e.apply_symm_apply (g ω)]

end Prob

/-! ## 4. The mollifier scales -/

def epsSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem epsSeq_pos (n : ℕ) : 0 < epsSeq n := by unfold epsSeq; positivity

theorem epsSeq_le (n : ℕ) : epsSeq n ≤ 1 := by
  unfold epsSeq
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_epsSeq : Tendsto epsSeq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## 5. The approximating mass-zero test functions -/

/-- Mollifier of the `i`-th enumerated folded circle. -/
def mI (i n : ℕ) : TestFun H :=
  mollTF (CoordsFull.fullIndex i).1 (fullIndex_radius_pos i) (epsSeq_pos n)

/-- Mollifier of the normalization circle `fc(0,1)`. -/
def mS (n : ℕ) : TestFun H := mollTF 0 one_pos (epsSeq_pos n)

theorem integral_mI (i n : ℕ) : ∫ z, (mI i n).1 z = 1 := integral_moll _ _ (epsSeq_pos n)

theorem integral_mS (n : ℕ) : ∫ z, (mS n).1 z = 1 := integral_moll _ _ (epsSeq_pos n)

/-- `m_i − m_⋆`, of mass zero. -/
def dI (i n : ℕ) : TestFun0 H :=
  tfLin0 (-1) (mS n) (mI i n) (by rw [integral_mS, integral_mI]; ring)

/-- `ρ − (∫ρ) m_⋆`, of mass zero. -/
def eI (ρ : TestFun H) (n : ℕ) : TestFun0 H :=
  tfLin0 (-∫ z, ρ.1 z) (mS n) ρ (by rw [integral_mS]; ring)

section Conv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- For a field `Y` whose pairings and circle values agree a.s. with those of a field `V`
satisfying TREG and linearity, the pairings of `Y` with `dI i n` (resp. `eI ρ n`) converge in
probability to the coordinates of `lawData (nrm ∘ Y)`. -/
theorem conv_coords {Y V : Ω → FieldSample}
    (hP : ∀ ρ : TestFun H, ∀ᵐ ω ∂P, pairRaw (Y ω) ρ.1 = pairRaw (V ω) ρ.1)
    (hC : ∀ (w : ℂ) (r : ℝ), 0 < r → ∀ᵐ ω ∂P, Y ω (foldedCircle w r) = V ω (foldedCircle w r))
    (hT : ∀ (w : ℂ) (r : ℝ), 0 < r → TendstoInMeasure P
      (fun n ω => pairRaw (V ω) (moll w r (epsSeq n))) atTop (fun ω => V ω (foldedCircle w r)))
    (hL : ∀ (a : ℝ) (ρ₁ ρ₂ : TestFun H), ∀ᵐ ω ∂P, pairRaw (V ω) (tfLin a ρ₁ ρ₂).1 =
      a * pairRaw (V ω) ρ₁.1 + pairRaw (V ω) ρ₂.1) :
    (∀ i, TendstoInMeasure P (fun n ω => pairRaw (Y ω) (dI i n).1.1) atTop
      (fun ω => CoordsFull.coordsFull (nrm (Y ω)) i)) ∧
    (∀ ρ : TestFun H, TendstoInMeasure P (fun n ω => pairRaw (Y ω) (eI ρ n).1.1) atTop
      (fun ω => pairRaw (nrm (Y ω)) ρ.1)) := by
  refine ⟨fun i => ?_, fun ρ => ?_⟩
  · have h := tendstoInMeasure_lin (hT 0 1 one_pos)
      (hT (CoordsFull.fullIndex i).1 _ (fullIndex_radius_pos i)) (-1)
    refine (h.congr_left fun n => ?_).congr_right ?_
    · filter_upwards [hL (-1) (mS n) (mI i n), hP (tfLin (-1) (mS n) (mI i n))] with ω h1 h2
      exact (h2.trans h1).symm
    · filter_upwards [hC _ _ (fullIndex_radius_pos i), hC 0 1 one_pos] with ω h1 h2
      rw [coordsFull_nrm, h1, h2]
      ring
  · have h := tendstoInMeasure_lin (hT 0 1 one_pos) (tendstoInMeasure_const'
      (fun ω => pairRaw (V ω) ρ.1)) (-∫ z, ρ.1 z)
    refine (h.congr_left fun n => ?_).congr_right ?_
    · filter_upwards [hL (-∫ z, ρ.1 z) (mS n) ρ, hP (tfLin (-∫ z, ρ.1 z) (mS n) ρ)]
        with ω h1 h2
      exact (h2.trans h1).symm
    · filter_upwards [hP ρ, hC 0 1 one_pos] with ω h1 h2
      rw [pairRaw_nrm, h1, h2]
      ring

/-- The same measurable function of the pairing data, along a common subsequence. -/
theorem law_eq_of_conv [IsFiniteMeasure P] {Y0 Y1 : Ω → FieldSample}
    {G0 G1 : Ω → ℝ≥0 → ℝ}
    (hc0 : ∀ (w : ℂ) (r : ℝ), 0 < r → Measurable fun ω => Y0 ω (foldedCircle w r))
    (hp0 : ∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y0 ω) ρ.1)
    (hc1 : ∀ (w : ℂ) (r : ℝ), 0 < r → Measurable fun ω => Y1 ω (foldedCircle w r))
    (hp1 : ∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y1 ω) ρ.1)
    (hG0 : Measurable G0) (hG1 : Measurable G1)
    (hlaw : P.map (fun ω => ((fun ρ : TestFun0 H => pairRaw (Y1 ω) ρ.1.1), G1 ω)) =
      P.map (fun ω => ((fun ρ : TestFun0 H => pairRaw (Y0 ω) ρ.1.1), G0 ω)))
    (hI0 : ∀ i, TendstoInMeasure P (fun n ω => pairRaw (Y0 ω) (dI i n).1.1) atTop
      (fun ω => CoordsFull.coordsFull (nrm (Y0 ω)) i))
    (hI1 : ∀ i, TendstoInMeasure P (fun n ω => pairRaw (Y1 ω) (dI i n).1.1) atTop
      (fun ω => CoordsFull.coordsFull (nrm (Y1 ω)) i))
    (hE0 : ∀ ρ : TestFun H, TendstoInMeasure P (fun n ω => pairRaw (Y0 ω) (eI ρ n).1.1) atTop
      (fun ω => pairRaw (nrm (Y0 ω)) ρ.1))
    (hE1 : ∀ ρ : TestFun H, TendstoInMeasure P (fun n ω => pairRaw (Y1 ω) (eI ρ n).1.1) atTop
      (fun ω => pairRaw (nrm (Y1 ω)) ρ.1)) :
    P.map (fun ω => (lawData (fun ω => nrm (Y1 ω)) ω, G1 ω)) =
      P.map (fun ω => (lawData (fun ω => nrm (Y0 ω)) ω, G0 ω)) := by
  have hD0 := (measurable_lawData_nrm hc0 hp0).prodMk hG0
  have hD1 := (measurable_lawData_nrm hc1 hp1).prodMk hG1
  have hC0 : Measurable fun ω => ((fun ρ : TestFun0 H => pairRaw (Y0 ω) ρ.1.1), G0 ω) :=
    (measurable_pi_iff.2 fun ρ : TestFun0 H => hp0 ρ.1).prodMk hG0
  have hC1 : Measurable fun ω => ((fun ρ : TestFun0 H => pairRaw (Y1 ω) ρ.1.1), G1 ω) :=
    (measurable_pi_iff.2 fun ρ : TestFun0 H => hp1 ρ.1).prodMk hG1
  choose nsI hnsI0 hnsI1 using fun i => exists_subseq_ae₂ (hI0 i) (hI1 i)
  choose nsE hnsE0 hnsE1 using fun ρ => exists_subseq_ae₂ (hE0 ρ) (hE1 ρ)
  let Φ : (TestFun0 H → ℝ) × (ℝ≥0 → ℝ) → ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) :=
    fun p => ((fun i => limUnder atTop fun k => p.1 (dI i (nsI i k)),
      fun ρ => limUnder atTop fun k => p.1 (eI ρ (nsE ρ k))), p.2)
  have hΦm : Measurable Φ := by
    refine Measurable.prodMk (Measurable.prodMk (measurable_pi_iff.2 fun i => ?_)
      (measurable_pi_iff.2 fun ρ => ?_)) measurable_snd
    · exact (StronglyMeasurable.limUnder fun k =>
        ((measurable_pi_apply (dI i (nsI i k))).comp measurable_fst).stronglyMeasurable).measurable
    · exact (StronglyMeasurable.limUnder fun k =>
        ((measurable_pi_apply (eI ρ (nsE ρ k))).comp measurable_fst).stronglyMeasurable).measurable
  have key : ∀ {Y : Ω → FieldSample} {G : Ω → ℝ≥0 → ℝ},
      Measurable (fun ω => (lawData (fun ω => nrm (Y ω)) ω, G ω)) →
      Measurable (fun ω => ((fun ρ : TestFun0 H => pairRaw (Y ω) ρ.1.1), G ω)) →
      (∀ i, ∀ᵐ ω ∂P, Tendsto (fun k => pairRaw (Y ω) (dI i (nsI i k)).1.1) atTop
        (𝓝 (CoordsFull.coordsFull (nrm (Y ω)) i))) →
      (∀ ρ : TestFun H, ∀ᵐ ω ∂P, Tendsto (fun k => pairRaw (Y ω) (eI ρ (nsE ρ k)).1.1) atTop
        (𝓝 (pairRaw (nrm (Y ω)) ρ.1))) →
      P.map (fun ω => (lawData (fun ω => nrm (Y ω)) ω, G ω)) =
        (P.map (fun ω => ((fun ρ : TestFun0 H => pairRaw (Y ω) ρ.1.1), G ω))).map Φ := by
    intro Y G hD hC hI hE
    rw [Measure.map_map hΦm hC]
    refine map_eq_of_ae_coords hD (hΦm.comp hC) (fun i => ?_) (fun ρ => ?_)
      (fun s => ae_of_all _ fun ω => rfl)
    · filter_upwards [hI i] with ω hlim
      exact hlim.limUnder_eq.symm
    · filter_upwards [hE ρ] with ω hlim
      exact hlim.limUnder_eq.symm
  rw [key hD1 hC1 hnsI1 hnsE1, key hD0 hC0 hnsI0 hnsE0, hlaw]

end Conv

/-! ## 6. B1-FULL -/

/-- **B1-FULL.** Unzipping by capacity time `t > 0` preserves the joint law of the normalized
`lawData` of the field and of the driver (future increments). -/
theorem b1_full (κ : ℝ) (hκ : 0 < κ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    P.map (fun ω => (lawData (fun ω => nrm (unzippedField (Real.sqrt κ)
        (ofFun (h0rev κ) + X ω, drive κ B ω) t)) ω,
      fun s : ℝ≥0 => (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).2 s)) =
    P.map (fun ω => (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω,
      fun s : ℝ≥0 => drive κ B ω s)) := by
  have ht0 := ht.le
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  obtain ⟨B', -, hB'm, hB'c, hind', hEq⟩ := exists_unzip_driver κ hB hind ht0
  obtain ⟨g, hg⟩ : ∃ g : Ω → C(Icc (0 : ℝ) t, ℝ), g = pathC t B' hB'c := ⟨_, rfl⟩
  have hgm : Measurable g := hg ▸ measurable_pathC t hB'm hB'c
  have hig : IndepFun g X P := hg ▸ indepFun_pathC t hind' hB'c
  have hgood : ∀ᵐ ω ∂P, EqOn (fwdMapInv (drive κ B ω) t) (revMap (Wof κ t ht0 (g ω)) t) H := by
    filter_upwards [hEq] with ω h
    rwa [revMap_drive_eq κ t ht0 B' hB'c ω, ← hg] at h
  obtain ⟨B₁, hB₁m, -, hB₁eq⟩ := exists_good_version hB
  have hfcH : ∀ (w : ℂ) {r : ℝ}, 0 < r → foldedCircle w r Hᶜ = 0 := fun w r hr =>
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H w hr)
  -- the fields: `Y1` (the unzipped field with the measurable driver), `Yc`, `Y0`
  obtain ⟨Y1, hY1⟩ : ∃ Y1 : Ω → FieldSample, Y1 = fun ω => coordChange (ofFun (h0rev κ) + X ω)
      (revMap (Wof κ t ht0 (g ω)) t) (Qc (Real.sqrt κ)) := ⟨_, rfl⟩
  obtain ⟨Yc, hYc⟩ : ∃ Yc : Ω → FieldSample,
      Yc = fun ω => couplingFieldRev κ (Wof κ t ht0 (g ω)) t (X ω) := ⟨_, rfl⟩
  obtain ⟨Y0, hY0⟩ : ∃ Y0 : Ω → FieldSample, Y0 = fun ω => ofFun (h0rev κ) + X ω := ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : Ω → ℝ≥0 → ℝ,
      G1 = fun ω (s : ℝ≥0) => drive κ B₁ ω (t + max (s : ℝ) 0) - drive κ B₁ ω t := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0 : Ω → ℝ≥0 → ℝ, G0 = fun ω (s : ℝ≥0) => drive κ B₁ ω s := ⟨_, rfl⟩
  have hG1m : Measurable G1 := by
    rw [hG1]; refine measurable_pi_iff.2 fun s => ?_
    simp only [drive]
    exact ((hB₁m _).const_mul _).sub ((hB₁m _).const_mul _)
  have hG0m : Measurable G0 := by
    rw [hG0]; refine measurable_pi_iff.2 fun s => ?_
    simp only [drive]
    exact (hB₁m _).const_mul _
  -- measurability
  have hY0c : ∀ μ : Measure ℂ, Measurable fun ω => Y0 ω μ := fun μ => by
    rw [hY0]; simp only [Pi.add_apply]; exact measurable_const.add (hX.measurable_coord μ)
  have hY0p : ∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y0 ω) ρ.1 := fun ρ =>
    measurable_pairRaw_comp hY0c ρ.1
  have hY1c : ∀ (w : ℂ) (r : ℝ), 0 < r → Measurable fun ω => Y1 ω (foldedCircle w r) :=
    fun w r hr => by
      have key := (measurable_unzip_apply κ t ht0 _ (hfcH w hr)).comp (hgm.prodMk hXm)
      simp only [Function.comp_def] at key
      rw [hY1]
      beta_reduce
      exact key
  have hY1p : ∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y1 ω) ρ.1 := fun ρ => by
    have key := (measurable_pair_unzip κ t ht0 ρ).comp (hgm.prodMk hXm)
    simp only [Function.comp_def] at key
    rw [hY1]
    beta_reduce
    exact key
  -- the convergences
  have cv0 := conv_coords (P := P) (Y := Y0) (V := Y0) (fun ρ => ae_of_all _ fun ω => rfl)
    (fun w r _ => ae_of_all _ fun ω => rfl)
    (fun w r hr => by
      rw [hY0]
      exact tendstoInMeasure_pairRaw_moll_h0rev κ hX w hr epsSeq_pos epsSeq_le tendsto_epsSeq)
    (fun a ρ₁ ρ₂ => by rw [hY0]; exact ae_pairRaw_lin_h0rev κ hX a ρ₁ ρ₂)
  have cv1 := conv_coords (P := P) (Y := Y1) (V := Yc)
    (fun ρ => by
      filter_upwards [ae_pairRaw_unzip_eq_Y2f κ ht0 hX hgm hig ρ] with ω h
      rw [hY1, hYc]
      exact h.trans (by rw [Y2f_eq]))
    (fun w r hr => by
      rw [hY1, hYc]
      exact ae_unzip_fc_eq κ ht0 hX hgm hig w hr)
    (fun w r hr => by
      rw [hYc]
      exact tendstoInMeasure_pairRaw_moll_random κ ht0 hX hgm hig w hr epsSeq_pos epsSeq_le
        tendsto_epsSeq)
    (fun a ρ₁ ρ₂ => by
      filter_upwards [ae_pairRaw_lin_Y2f κ t ht0 hX hgm hig a ρ₁ ρ₂] with ω h
      rw [hYc]
      simpa only [Y2f_eq] using h)
  -- the law of the pairing data (B1 at the `TestFun0` level)
  have hlaw : P.map (fun ω => ((fun ρ : TestFun0 H => pairRaw (Y1 ω) ρ.1.1), G1 ω)) =
      P.map (fun ω => ((fun ρ : TestFun0 H => pairRaw (Y0 ω) ρ.1.1), G0 ω)) := by
    have h := (unzip_invariance theorem1_2_holds κ hκ P B X hB hX hind ht).1
    unfold configLawMod0 at h
    have e1 : (fun ω => ((fun ρ : TestFun0 H => pairRaw (zipCapDown (Real.sqrt κ) t
          (ofFun (h0rev κ) + X ω, drive κ B ω)).1 ρ.1.1),
        fun s : ℝ≥0 => (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).2 s))
        =ᵐ[P] fun ω => ((fun ρ : TestFun0 H => pairRaw (Y1 ω) ρ.1.1), G1 ω) := by
      filter_upwards [hgood, hB₁eq] with ω hgd hb
      refine Prod.ext (funext fun ρ => ?_) (funext fun s => ?_)
      · rw [hY1]; exact pairRaw_coordChange_congr hgd _ _ ρ.1
      · rw [hG1]; simp only [zipCapDown, drive, hb]
    have e0 : (fun ω => ((fun ρ : TestFun0 H => pairRaw (ofFun (h0rev κ) + X ω,
          drive κ B ω).1 ρ.1.1), fun s : ℝ≥0 => (ofFun (h0rev κ) + X ω, drive κ B ω).2 s))
        =ᵐ[P] fun ω => ((fun ρ : TestFun0 H => pairRaw (Y0 ω) ρ.1.1), G0 ω) := by
      filter_upwards [hB₁eq] with ω hb
      refine Prod.ext (funext fun ρ => ?_) (funext fun s => ?_)
      · rw [hY0]
      · rw [hG0]; simp only [drive, hb]
    exact (Measure.map_congr e1).symm.trans (h.trans (Measure.map_congr e0))
  -- the target data
  have eD1 : (fun ω => (lawData (fun ω => nrm (unzippedField (Real.sqrt κ)
        (ofFun (h0rev κ) + X ω, drive κ B ω) t)) ω,
      fun s : ℝ≥0 => (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).2 s))
      =ᵐ[P] fun ω => (lawData (fun ω => nrm (Y1 ω)) ω, G1 ω) := by
    filter_upwards [hgood, hB₁eq] with ω hgd hb
    refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun ρ => ?_)) (funext fun s => ?_)
    · simp only [lawData, unzippedField, hY1]
      rw [coordsFull_nrm, coordsFull_nrm,
        coordChange_congr_of_eqOn hgd (hfcH _ (fullIndex_radius_pos i)),
        coordChange_congr_of_eqOn hgd (hfcH 0 one_pos)]
    · simp only [lawData, unzippedField, hY1]
      rw [pairRaw_nrm, pairRaw_nrm, pairRaw_coordChange_congr hgd,
        coordChange_congr_of_eqOn hgd (hfcH 0 one_pos)]
    · rw [hG1]; simp only [zipCapDown, drive, hb]
  have eD0 : (fun ω => (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω,
      fun s : ℝ≥0 => drive κ B ω s)) =ᵐ[P] fun ω => (lawData (fun ω => nrm (Y0 ω)) ω, G0 ω) := by
    filter_upwards [hB₁eq] with ω hb
    refine Prod.ext ?_ (funext fun s => ?_)
    · rw [hY0]
    · rw [hG0]; simp only [drive, hb]
  rw [Measure.map_congr eD1, Measure.map_congr eD0]
  exact law_eq_of_conv (P := P) (Y0 := Y0) (Y1 := Y1) (G0 := G0) (G1 := G1)
    (fun w r _ => hY0c _) hY0p hY1c hY1p hG0m hG1m hlaw cv0.1 cv1.1 cv0.2 cv1.2

end B1Full
end QuantumZipper
