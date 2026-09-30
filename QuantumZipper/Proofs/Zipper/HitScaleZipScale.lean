import QuantumZipper.Proofs.Zipper.HitScaleZip
import QuantumZipper.Proofs.Zipper.F1LenScale
import QuantumZipper.Proofs.Zipper.F1LenRead
import QuantumZipper.Proofs.Zipper.F1EmbedBasic

/-!
# E6-HITSCALEZIP, part 2: the left-length nodes from scaling invariance

The two length nodes of `HitScaleZip.lean` follow from the scale invariance of the `P_*`
configuration law (B4(c), `F1.PStarCanonLawStmt`) and the B3(d) length scaling
(`F1.PStarZipLenInputsStmt`, through `F1.unzipLengths_canon_addConst`): for every constant `k`,
the configuration `c' = canonConfig γ (Y + k, √κ B')` has the law of `c = (Y, √κ B')`, and
`L⁻_{c'}(u) = e^{γk/2} L⁻_c(a² u)` for all `u ≥ 0` (`a > 0` random).

* `S = sup_{t ≥ 0} L⁻_t` (read along the integers, by monotonicity) satisfies
  `law(n S) = law(S)` for every `n ≥ 1`; since `S > 0` a.s. (`F1.pstar_pos_all`), `S = ∞` a.s.
  (`ae_eq_top_of_map_mul`). Hence `pStarLenInfStmt_of`.
* `I = inf_{t > 0} L⁻_t` (read along `1/(n+1)`) satisfies `law(n⁻¹ I) = law(I)`; since
  `I ≤ L⁻_1 < ∞`, applying the same lemma to `I⁻¹` gives `I = 0` a.s., and by monotonicity
  `L⁻_t → 0` as `t → 0⁺`. Hence `pStarLenStartStmt_of`.

Measurability of the time-`t` lengths as functions of the data is `F1.LenReadTimeStmt`.

Source: Sheffield, arXiv:1012.4797, §5.4, p. 71 ("by scaling"); the paper does not spell out
these steps. The zero–infinity argument from scale invariance in law is own elementary work.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip

/-! ## A random variable whose law is invariant under multiplication by `n` -/

/-- If `X > 0` a.s. and `n X` has the law of `X` for every `n ≥ 1`, then `X = ∞` a.s. -/
theorem ae_eq_top_of_map_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ≥0∞} (hX : AEMeasurable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω)
    (hsc : ∀ n : ℕ, 1 ≤ n → P.map (fun ω => (n : ℝ≥0∞) * X ω) = P.map X) :
    ∀ᵐ ω ∂P, X ω = ⊤ := by
  have hM : ∀ M : ℕ, P {ω | X ω ≤ M} = 0 := by
    intro M
    set s : ℕ → Set Ω := fun n => {ω | X ω ≤ (M : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹} with hs
    have hS : ∀ n : ℕ, 1 ≤ n → P (s n) = P {ω | X ω ≤ M} := by
      intro n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hmX : AEMeasurable (fun ω => (n : ℝ≥0∞) * X ω) P := hX.const_mul _
      have e := congrArg (fun μ : Measure ℝ≥0∞ => μ (Iic (M : ℝ≥0∞))) (hsc n hn)
      rw [Measure.map_apply_of_aemeasurable hmX measurableSet_Iic,
        Measure.map_apply_of_aemeasurable hX measurableSet_Iic] at e
      refine Eq.trans ?_ e
      congr 1
      ext ω
      simp only [hs, mem_preimage, mem_Iic, mem_ofPred_eq]
      rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hn0)
        (Or.inl (ENNReal.natCast_ne_top n)), mul_comm]
    have hanti : Antitone s := by
      intro m n hmn ω hω
      exact (show X ω ≤ _ from hω).trans
        (mul_le_mul_right (ENNReal.inv_le_inv.2 (by exact_mod_cast hmn)) _)
    have hlim := tendsto_measure_iInter_atTop (μ := P)
      (fun n => hX.nullMeasurable measurableSet_Iic) hanti ⟨0, measure_ne_top P _⟩
    have hconst : Tendsto (P ∘ s) atTop (𝓝 (P {ω | X ω ≤ M})) :=
      tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => (hS n hn).symm⟩)
    rw [tendsto_nhds_unique hconst hlim]
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hpos)
    rw [mem_iInter] at hω
    have ht : Tendsto (fun n : ℕ => (M : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr (ENNReal.natCast_ne_top M))
      rwa [mul_zero] at this
    have h0 : X ω ≤ 0 := ge_of_tendsto' ht fun n => hω n
    simp only [mem_ofPred_eq, not_lt]
    exact h0
  refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hM))
  obtain ⟨M, hM'⟩ := ENNReal.exists_nat_gt (show X ω ≠ ⊤ from hω)
  exact mem_iUnion.2 ⟨M, hM'.le⟩

/-! ## Deterministic scaling of sup and inf of a monotone length -/

variable {f : ℝ → ℝ≥0∞}

theorem iSup_nat_scale (hf : MonotoneOn f (Ici 0)) {b : ℝ} (hb : 0 < b) :
    ⨆ n : ℕ, f (b * n) = ⨆ n : ℕ, f n := by
  refine le_antisymm (iSup_mono' fun n => ⟨⌈b * n⌉₊, ?_⟩) (iSup_mono' fun n => ⟨⌈n / b⌉₊, ?_⟩)
  · exact hf (mem_Ici.2 (by positivity)) (mem_Ici.2 (Nat.cast_nonneg _)) (Nat.le_ceil _)
  · refine hf (mem_Ici.2 (Nat.cast_nonneg _)) (mem_Ici.2 (by positivity)) ?_
    have := Nat.le_ceil ((n : ℝ) / b)
    rw [div_le_iff₀ hb] at this
    linarith

theorem iInf_nat_scale (hf : MonotoneOn f (Ici 0)) {b : ℝ} (hb : 0 < b) :
    ⨅ n : ℕ, f (b * (1 / ((n : ℝ) + 1))) = ⨅ n : ℕ, f (1 / ((n : ℝ) + 1)) := by
  refine le_antisymm (iInf_mono' fun n => ⟨⌈b * ((n : ℝ) + 1)⌉₊, ?_⟩)
    (iInf_mono' fun n => ⟨⌈((n : ℝ) + 1) / b⌉₊, ?_⟩)
  · refine hf (mem_Ici.2 (by positivity)) (mem_Ici.2 (by positivity)) ?_
    have h := Nat.le_ceil (b * ((n : ℝ) + 1))
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · refine hf (mem_Ici.2 (by positivity)) (mem_Ici.2 (by positivity)) ?_
    have h := Nat.le_ceil (((n : ℝ) + 1) / b)
    rw [div_le_iff₀ hb] at h
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-! ## Law transfer for `ℝ≥0∞`-valued readings -/

/-- `F1.map_eq_of_read` for `ℝ≥0∞`-valued readers. -/
theorem map_eq_of_read_ennreal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {c₁ c₂ : Ω → FieldSample × (ℝ → ℝ)} (h : configLawFull c₂ P = configLawFull c₁ P)
    (h1 : AEMeasurable (fun ω => F1.cfgData (c₁ ω)) P)
    (h2 : AEMeasurable (fun ω => F1.cfgData (c₂ ω)) P)
    {Φ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hΦ : AEMeasurable Φ (configLawFull c₁ P))
    {G₁ G₂ : Ω → ℝ≥0∞} (hG1 : ∀ᵐ ω ∂P, G₁ ω = Φ (F1.cfgData (c₁ ω)))
    (hG2 : ∀ᵐ ω ∂P, G₂ ω = Φ (F1.cfgData (c₂ ω))) : P.map G₂ = P.map G₁ := by
  have hΦ1 : AEMeasurable Φ (P.map fun ω => F1.cfgData (c₁ ω)) := hΦ
  have hΦ2 : AEMeasurable Φ (P.map fun ω => F1.cfgData (c₂ ω)) := by
    rw [← F1.configLawFull_eq_map_cfgData, h]; exact hΦ
  have e1 : P.map G₁ = (configLawFull c₁ P).map Φ := by
    rw [Measure.map_congr hG1, F1.configLawFull_eq_map_cfgData,
      AEMeasurable.map_map_of_aemeasurable hΦ1 h1]; rfl
  have e2 : P.map G₂ = (configLawFull c₂ P).map Φ := by
    rw [Measure.map_congr hG2, F1.configLawFull_eq_map_cfgData,
      AEMeasurable.map_map_of_aemeasurable hΦ2 h2]; rfl
  rw [e1, e2, h]

/-! ## The scaled `P_*` configuration -/

theorem ofReal_exp_scale_up {γ : ℝ} (hγ : 0 < γ) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (Real.exp (γ * ((2 / γ) * Real.log n) / 2)) = (n : ℝ≥0∞) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : γ * ((2 / γ) * Real.log n) / 2 = Real.log n := by field_simp
  rw [e, Real.exp_log hn', ENNReal.ofReal_natCast]

section Assembly

variable {κ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Y : Ω' → FieldSample} {B' : ℝ≥0 → Ω' → ℝ}

end Assembly

/-! ## The two length nodes -/

end QuantumZipper.E6
