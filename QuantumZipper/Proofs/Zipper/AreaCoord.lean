import QuantumZipper.Proofs.Zipper.AreaCoordBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AREA-COORD (2): W-A-cc from the merging of the area approximations

Theorem 1.3 / 1.8, node E6. `E6.WedgeAreaCoordStmt` (W-A-cc, `PStarAreaCoord.lean`) asks that
a.s., for **all** `t ≥ 0` at once, `μ_{x_t}(S) = μ_{x_0}(f_t⁻¹(S))` for Borel `S ⊆ ℍ`, where
`x_0 = F2.zU γ X' A` is the unscaled wedge field, `x_t = unzippedField γ (x_0, W) t` and
`f_t⁻¹ = fwdMapInv W t`. Since `qAreaMeasure` is a chosen vague limit (junk `0` otherwise),
this needs the existence of the vague limit for the unzipped field at every `t`.

**Route: Sheffield–Wang**, *Field-measure correspondence in Liouville quantum gravity almost
surely commutes with all conformal maps simultaneously*, Trans. AMS 372 (2020),
arXiv:1605.06171, **Theorem 1.4 and its proof, p. 11–12**: the change of coordinates turns the
approximations (3.5) of `μ_{h∘φ+Q log|φ'|}(φ⁻¹(S))` into integrals over `S`, and the theorem
follows from the statement that these merge with the approximations `μ̃^h_ε(S)` of the original
field, (3.6)/(3.7). The Duplantier–Sheffield rule for one fixed map (Invent. Math. 185 (2011),
arXiv:0808.1560, Prop. 2.1, p. 13) is the special case of one map; DS prove it through the
orthonormal-basis construction of `μ_h` (their Prop. 1.2), not through circle averages, so it
does not fit the circle-average definition of `qAreaMeasure` used here.

Here the merging statement is the named input, for the family `φ = f_t⁻¹`, `t ≥ 0`:

* `mergeDiff γ x W f t k =`
  `∫ f d(areaApprox γ x_t k) − ∫ (1_{ℍ \ K_t} · f ∘ f_t) d(areaApprox γ x k)` (the difference of the scale-`2^{-k}` approximations, read in the unzipped coordinates);
* **`WedgeAreaMergeStmt`** (W-A-merge): a.s., for all `t ≥ 0` and all test functions `f`
  (continuous, compact support in `ℍ`), `mergeDiff … f t k → 0` as `k → ∞`.

It is split, following the pattern of decision D33 (fixed parameter + uniform modulus), into

* **`WedgeAreaMergeFixStmt`** (W-A-merge-fix): for each fixed `t ≥ 0`, a.s. for all test
  functions, `mergeDiff … f t k → 0` (SW Thm 1.4 for the single map `f_t⁻¹`, with the driver
  independent of the field);
* **`WedgeAreaEquiStmt`** (W-A-equi): a.s., for every test function, the differences are
  asymptotically equicontinuous in time: for every `t ≥ 0` and `ε > 0` there are `δ > 0` and `K`
  with `|mergeDiff … f s k − mergeDiff … f t k| ≤ ε` for `|s − t| < δ`, `s ≥ 0`, `k ≥ K` (the
  area analogue of the D33 uniform-Cauchy input; SW prove the stronger uniformity over all `φ`).

Results: `wedgeAreaMergeStmt_of_fix_equi` (rational times + equicontinuity, own elementary
proof), `wedgeAreaCoordStmt_of_merge` (vague convergence to the transported measure,
`AreaCoordBasic`, + uniqueness of vague limits + `E6.ae_areaAll_wedgeField`), and
**`wedgeAreaCoordStmt_of_split`**.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip

/-! ## The merging differences -/

/-- A test function for the area measure on `ℍ`: continuous, compactly supported in `ℍ`. -/
def IsAreaTest (f : ℂ → ℝ) : Prop :=
  Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ H

/-- The difference of the scale-`2^{-k}` area approximations of the unzipped field
`x_t = unzippedField γ (x, W) t` tested against `f`, and of the field `x` tested against the
transported test function `1_{ℍ \ K_t} · (f ∘ f_t)`. -/
def mergeDiff (γ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (f : ℂ → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  ∫ z, f z ∂(areaApprox γ (unzippedField γ (x, W) t) k) -
    ∫ w, transTest W t f w ∂(areaApprox γ x k)

/-! ## The named inputs -/

/-- **W-A-merge** (open; Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7)):
a.s., for all `t ≥ 0` and all test functions, the area approximations of the unzipped unscaled
wedge field and the transported approximations of the wedge field merge. -/
def WedgeAreaMergeStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∀ f : ℂ → ℝ, IsAreaTest f →
      Tendsto (mergeDiff (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (drive κ B'' ω) f t)
        atTop (𝓝 0)

/-- **W-A-merge-fix** (open; SW Thm 1.4 / DS Prop 2.1 for one map): for each fixed `t ≥ 0`,
a.s. the merging holds at time `t` for all test functions. -/
def WedgeAreaMergeFixStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ t, 0 ≤ t → ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, IsAreaTest f →
      Tendsto (mergeDiff (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (drive κ B'' ω) f t)
        atTop (𝓝 0)

/-- **W-A-equi** (open; the area analogue of the D33 uniform-Cauchy input): a.s., for every
test function, the merging differences are asymptotically equicontinuous in time. -/
def WedgeAreaEquiStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, IsAreaTest f → ∀ t, 0 ≤ t → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ s, 0 ≤ s → |s - t| < δ → ∀ k, K ≤ k →
        |mergeDiff (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (drive κ B'' ω) f s k -
          mergeDiff (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (drive κ B'' ω) f t k| ≤ ε

/-! ## Rational times and equicontinuity (deterministic) -/

/-- If `D q k → 0` at every rational time `q ≥ 0` and `D · k` is asymptotically equicontinuous
at `t ≥ 0`, then `D t k → 0`. Own elementary proof (an `ε/2` argument). -/
theorem tendsto_zero_of_rat_equi {D : ℝ → ℕ → ℝ}
    (hq : ∀ q : ℚ, 0 ≤ (q : ℝ) → Tendsto (D q) atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t)
    (he : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ s, 0 ≤ s → |s - t| < δ → ∀ k, K ≤ k →
      |D s k - D t k| ≤ ε) :
    Tendsto (D t) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, K, hK⟩ := he (ε / 2) (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + δ by linarith)
  have hq0 : 0 ≤ (q : ℝ) := ht.trans hq1.le
  have hqt : |(q : ℝ) - t| < δ := by
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hq q hq0) (ε / 2) (by linarith)
  refine ⟨max K N, fun n hn => ?_⟩
  have h1 := hK q hq0 hqt n (le_of_max_le_left hn)
  have h2 := hN n (le_of_max_le_right hn)
  rw [Real.dist_eq, sub_zero] at h2 ⊢
  calc |D t n| = |D q n - (D q n - D t n)| := by ring_nf
    _ ≤ |D q n| + |D q n - D t n| := abs_sub _ _
    _ < ε := by linarith

/-- **W-A-merge from W-A-merge-fix and W-A-equi.** -/
theorem wedgeAreaMergeStmt_of_fix_equi (hF : WedgeAreaMergeFixStmt) (hE : WedgeAreaEquiStmt) :
    WedgeAreaMergeStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hInd hB hIB
  have hQ : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ f : ℂ → ℝ, IsAreaTest f →
      Tendsto (mergeDiff (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (drive κ B'' ω) f q)
        atTop (𝓝 0) := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 ≤ (q : ℝ)
    · filter_upwards [hF κ hκ hκ4 P X' A B'' hX hA hInd hB hIB q hq] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [hQ, hE κ hκ hκ4 P X' A B'' hX hA hInd hB hIB] with ω hq he t ht f hf
  exact tendsto_zero_of_rat_equi (fun q hq0 => hq q hq0 f hf) ht (he f hf t ht)

/-! ## W-A-cc from W-A-merge -/

/-- **Deterministic core.** If the field `x` has `AreaAll` and the merging holds at time `t`
for all test functions, the area measure of the unzipped field is the transported measure, so
the coordinate-change rule holds at time `t`. -/
theorem coord_of_merge {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (hx : AreaAll γ x)
    (hm : ∀ f : ℂ → ℝ, IsAreaTest f → Tendsto (mergeDiff γ x W f t) atTop (𝓝 0))
    (S : Set ℂ) (hSm : MeasurableSet S) (hS : S ⊆ H) :
    qAreaMeasure γ (unzippedField γ (x, W) t) S = qAreaMeasure γ x (fwdMapInv W t '' S) := by
  have hv : IsVagueLimitOn H (areaApprox γ (unzippedField γ (x, W) t))
      (areaTransport (qAreaMeasure γ x) W t) :=
    isVagueLimitOn_areaTransport hW hW0 ht (isVagueLimitOn_qAreaMeasure_of_areaAll hx)
      fun f hf hfc hfH => hm f ⟨hf, hfc, hfH⟩
  rw [qAreaMeasure_eq hv, areaTransport_apply hW hW0 ht _ hSm hS]

/-- **W-A-cc from W-A-merge.** -/
theorem wedgeAreaCoordStmt_of_merge (hM : WedgeAreaMergeStmt) : WedgeAreaCoordStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hInd hB hIB
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  filter_upwards [hM κ hκ hκ4 P X' A B'' hX hA hInd hB hIB,
    ae_areaAll_wedgeField hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hInd,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hMω hxω hc h0 t ht S hSm hS
  have hWc : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  exact coord_of_merge hWc hW0 ht hxω (hMω t ht) S hSm hS

/-- **W-A-cc from the split** W-A-merge-fix + W-A-equi. -/
theorem wedgeAreaCoordStmt_of_split (hF : WedgeAreaMergeFixStmt) (hE : WedgeAreaEquiStmt) :
    WedgeAreaCoordStmt :=
  wedgeAreaCoordStmt_of_merge (wedgeAreaMergeStmt_of_fix_equi hF hE)

/-! ## Both split inputs follow from the Sheffield–Wang uniform form -/

/-- **W-A-merge-unif** (Sheffield–Wang, arXiv:1605.06171, (3.6)/(3.7), restricted to the flow
`φ = f_t⁻¹`, `t ∈ [0,T]`): a.s., for every test function and every horizon `T`, the merging
differences tend to `0` uniformly in `t ∈ [0,T]`. Not used as an input; recorded to show that
the two split inputs are consequences of the published uniform statement. -/
def WedgeAreaMergeUnifStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, IsAreaTest f → ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
      ∀ t, 0 ≤ t → t ≤ T →
        |mergeDiff (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (drive κ B'' ω) f t k| ≤ ε

/-- W-A-merge-fix is a consequence of the uniform form. -/
theorem wedgeAreaMergeFixStmt_of_unif (hU : WedgeAreaMergeUnifStmt) : WedgeAreaMergeFixStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hInd hB hIB t ht
  filter_upwards [hU κ hκ hκ4 P X' A B'' hX hA hInd hB hIB] with ω hω f hf
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := hω f hf t (ε / 2) (by linarith)
  refine ⟨K, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (hK k hk t ht le_rfl).trans_lt (by linarith)

/-- W-A-equi is a consequence of the uniform form. -/
theorem wedgeAreaEquiStmt_of_unif (hU : WedgeAreaMergeUnifStmt) : WedgeAreaEquiStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hInd hB hIB
  filter_upwards [hU κ hκ hκ4 P X' A B'' hX hA hInd hB hIB] with ω hω f hf t ht ε hε
  obtain ⟨K, hK⟩ := hω f hf (t + 1) (ε / 2) (by linarith)
  refine ⟨1, one_pos, K, fun s hs hst k hk => ?_⟩
  have hs1 : s ≤ t + 1 := by linarith [(abs_lt.1 hst).2]
  have h1 := hK k hk s hs hs1
  have h2 := hK k hk t ht (by linarith)
  calc _ ≤ |mergeDiff (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (drive κ B'' ω) f s k| +
        |mergeDiff (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (drive κ B'' ω) f t k| :=
        abs_sub _ _
    _ ≤ ε := by linarith

end QuantumZipper.E6
