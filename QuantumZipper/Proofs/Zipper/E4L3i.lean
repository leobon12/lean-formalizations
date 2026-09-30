import QuantumZipper.Proofs.Zipper.E4L3iBasic
import QuantumZipper.Proofs.Zipper.E4Fin

/-!
# E4-L3i: right-continuity of the right-side law at live times (`L3iStmt`)

`handoff/E4.md`, item hL3i, for Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68)
(the `n → ∞` grid step at a fixed `ε`, see `E4LimMain`). For a continuous driver `V`, a point
`x`, a normalizer `ϖ` and a free field `X'`, along any filter `l ≤ 𝓝[Icc 0 T₁] τ` along which
`realRevMap V s x → realRevMap V τ x`:

* `tendsto_energy_gen`, `tendsto_shift_fc_gen`, `tendsto_shift_varpi_gen`: the E4L3Terms limits
  along `l` (copied and generalized; the moving point now tends to an arbitrary `a₀`);
* `tendsto_lintegral_targetField_gen`: `∫⁻ f(coords(targetField κ V s ϖ x X')) dP'` tends to
  its value at `τ` (same proof as `tendsto_lintegral_targetField_coll`: shift + Gaussian noise
  of vanishing variance, `tendsto_lintegral_of_shift`);
* `tendsto_realRevMap_live`: at a live time `s` (`ofReal s < τ_x`), `s' ↦ realRevMap V s' x` is
  continuous within `[0, T₁]` at `s` for some `T₁ > s` (the real solution exists on `[0, T₁]`);
* **`l3iStmt : L3iStmt`**, with `l = 𝓝[≥] s`; hence `e4_unconditional : Thm13Asm.E4Stmt`.

Own elementary arguments (dominated convergence; convergence in probability implies convergence
in distribution, mathlib `TendstoInMeasure.tendstoInDistribution`), as in `E4L3`.
-/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace E4Grid

open E1 TwoPoint PalmNorm B2 RealLine CoordsFull

variable {V : ℝ → ℝ} {l : Filter ℝ} [l.IsCountablyGenerated] {τ T₁ : ℝ}
variable {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {K : Set ℂ} {α C : ℝ}

/-- **Energy continuity** along `l`: `kernelCov2 N (ϖ_s, ϖ_τ) (ϖ_s, ϖ_τ) → 0`. -/
theorem tendsto_energy_gen (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H)
    (hϖK : ϖ Kᶜ = 0) (hα : 0 < α) (hF : IsFrostman ϖ α C) (hl : l ≤ 𝓝[Icc 0 T₁] τ)
    (hτ : τ ∈ Icc (0 : ℝ) T₁) :
    Tendsto (fun s => kernelCov2 neumannH (varpiT V s ϖ, varpiT V τ ϖ)
      (varpiT V s ϖ, varpiT V τ ϖ)) l (𝓝 0) := by
  have hg := fun s (hs : 0 ≤ s) => varpiT_good hV hK hKH hϖK hα hF hs
  have h1 := tendsto_kk_gen hV hK hKH hϖK hα hF hl hτ
  have h2 := tendsto_kernelCov_left_gen hV hK hKH hϖK hl hτ (hg τ hτ.1)
  have h3 := ((h1.sub h2).sub h2).add_const
    (kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ))
  rw [show kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ) -
      kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ) -
      kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ) +
      kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ) = 0 by ring] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_mem_Icc_gen hl] with s hs
  simp only [kernelCov2]
  rw [CoordChange.kernelCov_comm_of_admissible (hg τ hτ.1).adm (hg s hs.1).adm]

/-- The shift integral against a fixed good measure `ν`, along `l`. -/
theorem tendsto_shift_fc_gen (κ : ℝ) (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H)
    (hϖK : ϖ Kᶜ = 0) (hα : 0 < α) (hF : IsFrostman ϖ α C) (hl : l ≤ 𝓝[Icc 0 T₁] τ)
    (hτ : τ ∈ Icc (0 : ℝ) T₁) {a : ℝ → ℝ} {a₀ : ℝ} (ha : Tendsto a l (𝓝 a₀)) {ν : Measure ℂ}
    (hν : GoodMeas ν) :
    Tendsto (fun s => ∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V s ϖ) (a s) u ∂ν)
      l (𝓝 (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V τ ϖ) a₀ u ∂ν)) := by
  have hg := fun s (hs : 0 ≤ s) => varpiT_good hV hK hKH hϖK hα hF hs
  have hcomm : ∀ s, 0 ≤ s → kernelCov neumannH ν (varpiT V s ϖ) =
      kernelCov neumannH (varpiT V s ϖ) ν := fun s hs =>
    CoordChange.kernelCov_comm_of_admissible hν.adm (hg s hs).adm
  rw [integral_shiftFun_eq hν (hg τ hτ.1).adm, hcomm τ hτ.1]
  have hN : Tendsto (fun s => neuPot ν (a s)) l (𝓝 (neuPot ν (a₀ : ℂ))) :=
    (hν.continuous_neuPot.tendsto _).comp ((Complex.continuous_ofReal.tendsto a₀).comp ha)
  refine (tendsto_const_nhds.add (Tendsto.const_mul _ (hN.sub
    (tendsto_kernelCov_left_gen hV hK hKH hϖK hl hτ hν)))).congr' ?_
  filter_upwards [eventually_mem_Icc_gen hl] with s hs
  rw [integral_shiftFun_eq hν (hg s hs.1).adm, hcomm s hs.1]

/-- The shift integral against `ϖ_s` itself, along `l`. -/
theorem tendsto_shift_varpi_gen (κ : ℝ) (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H)
    (hϖK : ϖ Kᶜ = 0) (hα : 0 < α) (hF : IsFrostman ϖ α C) (hl : l ≤ 𝓝[Icc 0 T₁] τ)
    (hτ : τ ∈ Icc (0 : ℝ) T₁) {a : ℝ → ℝ} {a₀ : ℝ} (ha : Tendsto a l (𝓝 a₀)) :
    Tendsto (fun s => ∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V s ϖ) (a s) u
        ∂(varpiT V s ϖ)) l
      (𝓝 (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V τ ϖ) a₀ u ∂(varpiT V τ ϖ))) := by
  have hg := fun s (hs : 0 ≤ s) => varpiT_good hV hK hKH hϖK hα hF hs
  have eh : ∀ s, 0 ≤ s → ∫ u, h0rev κ u ∂(varpiT V s ϖ) = ∫ z, h0rev κ (revMap V s z) ∂ϖ :=
    fun s hs => integral_map (measurable_revMap hV hs).aemeasurable
      (measurable_h0rev κ).aestronglyMeasurable
  have eN : ∀ s, 0 ≤ s → ∀ b : ℝ, neuPot (varpiT V s ϖ) (b : ℂ) =
      ∫ z, neumannH (b : ℂ) (revMap V s z) ∂ϖ := fun s hs b =>
    integral_map (measurable_revMap hV hs).aemeasurable
      (measurable_neumannH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hH := tendsto_integral_comp_revMap_gen hV hK hKH hϖK hl hτ (G := fun _ w => h0rev κ w)
    ((measurable_h0rev κ).comp measurable_snd) (a := fun _ => 0) (a₀ := 0) tendsto_const_nhds
    (continuousOn_h0rev_snd κ 0)
  have hN := tendsto_integral_comp_revMap_gen hV hK hKH hϖK hl hτ
    (G := fun (b : ℝ) w => neumannH (b : ℂ) w)
    (measurable_neumannH.comp ((Complex.measurable_ofReal.comp measurable_fst).prodMk
      measurable_snd)) ha (continuousOn_neumannH_real a₀)
  rw [integral_shiftFun_eq (hg τ hτ.1) (hg τ hτ.1).adm, eh τ hτ.1, eN τ hτ.1]
  refine (hH.add (Tendsto.const_mul _ (hN.sub
    (tendsto_kk_gen hV hK hKH hϖK hα hF hl hτ)))).congr' ?_
  filter_upwards [eventually_mem_Icc_gen hl] with s hs
  rw [integral_shiftFun_eq (hg s hs.1) (hg s hs.1).adm, eh s hs.1, eN s hs.1]

/-- **Law continuity along `l`**: the law of finitely many coordinates of
`targetField κ V s ϖ x X'` is continuous along `l`, given `realRevMap V s x → realRevMap V τ x`. -/
theorem tendsto_lintegral_targetField_gen (κ : ℝ) (hV : Continuous V) {x : ℝ} [l.NeBot]
    (hl : l ≤ 𝓝[Icc 0 T₁] τ) (hτ : τ ∈ Icc (0 : ℝ) T₁)
    (ha : Tendsto (fun s => realRevMap V s x) l (𝓝 (realRevMap V τ x)))
    {ϖ : Measure ℂ} (hϖ : IsNormalizer ϖ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P') {m : ℕ} (I : Fin m → ℕ)
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Continuous f) (hf1 : ∀ y, f y ≤ 1) :
    Tendsto (fun s => ∫⁻ ω', f (fun j => coordsFull (targetField κ V s ϖ x (X' ω')) (I j)) ∂P')
      l (𝓝 (∫⁻ ω', f (fun j => coordsFull (targetField κ V τ ϖ x (X' ω')) (I j)) ∂P')) := by
  have := hϖ.prob
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hF⟩ := hϖ.frost
  have hg := fun s (hs : 0 ≤ s) => varpiT_good hV hKc hKH hK0 hα hF hs
  set μj : Fin m → Measure ℂ := fun j => foldedCircle (fullIndex (I j)).1 (fullIndex (I j)).2
  have hμ : ∀ j, GoodMeas (μj j) := fun j => fc_good _ (by simp only [fullIndex]; positivity)
  set c : ℝ → Fin m → ℝ := fun s j =>
    (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V s ϖ) (realRevMap V s x) u ∂μj j) -
      (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V s ϖ) (realRevMap V s x) u
        ∂varpiT V s ϖ) - qt κ V s ϖ
  set Z : ℝ → Ω' → ℝ := fun s ω => X' ω (varpiT V s ϖ) - X' ω (varpiT V τ ϖ)
  set U : Ω' → Fin m → ℝ := fun ω j => X' ω (μj j) - X' ω (varpiT V τ ϖ)
  have eL : ∀ s ω, (fun j => coordsFull (targetField κ V s ϖ x (X' ω)) (I j)) =
      fun j => c s j + U ω j - Z s ω := fun s ω => by
    funext j
    simp only [coordsFull_targetField, c, U, Z, μj, ofFun]
    ring
  have hZ0 : ∀ ω, Z τ ω = 0 := fun ω => sub_self _
  simp only [eL, hZ0, sub_zero]
  have hUm : Measurable U := measurable_pi_iff.2 fun j =>
    (hX'.measurable_coord _).sub (hX'.measurable_coord _)
  have hZm : ∀ s, Measurable (Z s) := fun s =>
    (hX'.measurable_coord _).sub (hX'.measurable_coord _)
  refine tendsto_lintegral_of_shift c (c τ) Z U hUm hZm ?_ ?_ hf hf1
  · refine tendsto_pi_nhds.2 fun j => ?_
    exact ((tendsto_shift_fc_gen κ hV hKc hKH hK0 hα hF hl hτ ha (hμ j)).sub
      (tendsto_shift_varpi_gen κ hV hKc hKH hK0 hα hF hl hτ ha)).sub
      (tendsto_qt_gen κ hV hKc hKH hK0 hl hτ)
  · intro ε hε
    have hε2 : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    set g2 := gaussianAbsMoment (2 * 1)
    have hE := tendsto_energy_gen hV hKc hKH hK0 hα hF hl hτ
    have hlim : Tendsto (fun s => ENNReal.ofReal (|kernelCov2 neumannH (varpiT V s ϖ,
        varpiT V τ ϖ) (varpiT V s ϖ, varpiT V τ ϖ)| ^ 1 * g2) / ENNReal.ofReal (ε ^ 2))
        l (𝓝 0) := by
      have h1 : Tendsto (fun s => |kernelCov2 neumannH (varpiT V s ϖ, varpiT V τ ϖ)
          (varpiT V s ϖ, varpiT V τ ϖ)| ^ 1 * g2) l (𝓝 0) := by
        simpa using (hE.abs.pow 1).mul_const g2
      have h2 := ENNReal.Tendsto.div_const (ENNReal.tendsto_ofReal h1) (Or.inr hε2)
      simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_mem_Icc_gen hl] with s hs
    have hs1 := (hg s hs.1).prob
    have hτ1 := (hg τ hτ.1).prob
    have hmass : varpiT V s ϖ univ = varpiT V τ ϖ univ := by simp only [measure_univ]
    have hL := RegCont.lintegral_pow_diff_le hX' (hg s hs.1).adm (hg τ hτ.1).adm hmass 1
      le_rfl
    calc P' {ω | ε ≤ |Z s ω|}
        ≤ P' {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal (|Z s ω| ^ (2 * 1))} := by
          refine measure_mono fun ω hω => ?_
          simp only [mem_ofPred_eq] at hω ⊢
          exact ENNReal.ofReal_le_ofReal (by
            rw [mul_one]; exact pow_le_pow_left₀ hε.le hω 2)
      _ ≤ (∫⁻ ω, ENNReal.ofReal (|Z s ω| ^ (2 * 1)) ∂P') / ENNReal.ofReal (ε ^ 2) :=
          meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp
            ((continuous_abs.measurable.comp (hZm s)).pow_const _)).aemeasurable hε2
            ENNReal.ofReal_ne_top
      _ ≤ _ := ENNReal.div_le_div_right hL _

omit [l.IsCountablyGenerated] [IsProbabilityMeasure ϖ] in
/-- At a live time `s`, the real flow of `x` is continuous in time within `[0, T₁]` at `s`, for
some `T₁ > s`. -/
theorem tendsto_realRevMap_live (hV : Continuous V) {s x : ℝ} (hs : 0 ≤ s)
    (hlive : IsLive V s x) : ∃ T₁, s < T₁ ∧
      Tendsto (fun s' => realRevMap V s' x) (𝓝[Icc 0 T₁] s) (𝓝 (realRevMap V s x)) := by
  have h' : ENNReal.ofReal s < realHitTime V x := hlive
  obtain ⟨r, -, hsr, hrh⟩ := ENNReal.lt_iff_exists_real_btwn.1 h'
  have hsr' : s < r := ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs).1 hsr)
  obtain ⟨u, hu⟩ := exists_isRealRevSol_of_lt_realHitTime hrh
  refine ⟨r, hsr', ?_⟩
  rw [realRevMap_eq hV hu hs hsr'.le]
  refine (hu.1 s ⟨hs, hsr'.le⟩).tendsto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realRevMap_eq hV hu ht.1 ht.2).symm

/-- **hL3i** (`L3iStmt`): right-continuity of the right-side law at live times. -/
theorem l3iStmt : L3iStmt := by
  intro κ T Ω _ P _ B X ϖ Ω' _ P' _ X' hS hX' m' I f hf hf1
  obtain ⟨-, -, -, hB, -, -, hϖ⟩ := hS
  filter_upwards [hB.cont] with ω hc x _ s hs0 _ hlive
  have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  obtain ⟨T₁, hsT₁, ha⟩ := tendsto_realRevMap_live hV hs0 hlive
  have hl : 𝓝[≥] s ≤ 𝓝[Icc 0 T₁] s := by
    rw [← nhdsWithin_Icc_eq_nhdsGE hsT₁]
    exact nhdsWithin_mono _ (Icc_subset_Icc_left hs0)
  exact tendsto_lintegral_targetField_gen κ hV hl ⟨hs0, hsT₁.le⟩ (ha.mono_left hl) hϖ hX' I hf
    hf1

/-- **E4** (`Thm13Asm.E4Stmt`), unconditional. -/
theorem e4_unconditional : Thm13Asm.E4Stmt := e4_of_L3i l3iStmt

end E4Grid
end QuantumZipper
