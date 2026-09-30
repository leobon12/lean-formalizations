import QuantumZipper.Proofs.Zipper.D3PlusN2HeartStmt

/-!
# N2-HEART: the radial data (measurable representation, independence, radial TV)

Task N2-HEART. The model's radial data `n2RadR` (embedding time `Tc`, truncated re-centred radial
path) are a.s. a measurable functional `radG` of the radial Brownian path `zRadB`
(via the measurable surrogates `ZoomRadial.Thit`, `ZoomRadial.Zsur` of the project's radial
toolkit); hence H1 gives the independence of the lateral data from the radial data, and
`n2_radial_tv` (DMS arXiv:1409.7055 p. 78 (a)–(c)) gives the radial TV bound in `tvDist` form.
Own bookkeeping on top of the cited project results.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- Radial data as a measurable functional of a path. -/
def radG (α Q c S : ℝ) (p : ℝ≥0 → ℝ) : ℝ × (ℝ → ℝ) :=
  ((ZoomRadial.Thit α Q c p).toReal, ZoomRadial.Zsur α Q c S p)

theorem measurable_radG (α Q c S : ℝ) : Measurable (radG α Q c S) :=
  (ZoomRadial.measurable_Thit α Q c).ennreal_toReal.prodMk (ZoomRadial.measurable_Zsur α Q c S)

section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem Tc_congr_path {α Q c : ℝ} {b b' : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : ∀ s, b s ω = b' s ω) :
    ZoomRadial.Tc α Q c b ω = ZoomRadial.Tc α Q c b' ω := by
  simp only [ZoomRadial.Tc, ZoomRadial.Xc, h]

/-- **A.s. representation of the radial data** through a measurable path. -/
theorem ae_radData_eq {α Q c : ℝ} (S : ℝ) {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    (hαQ : α < Q) (hc : 0 < c) :
    ∃ b₀ : ℝ≥0 → Ω → ℝ, Measurable (pathOf b₀) ∧ ∀ᵐ ω ∂P, pathOf b ω = pathOf b₀ ω ∧
      (ZoomRadial.Tc α Q c b ω, fun s => ZoomRadial.zoomRadial α Q b c ω (max s (-S))) =
        radG α Q c S (pathOf b ω) := by
  obtain ⟨b₀, hb₀m, hb₀c, hb₀z, hb₀h, hb₀b⟩ := ZoomRadial.exists_nice_version hb hαQ hc
  refine ⟨b₀, measurable_pi_iff.2 fun s => hb₀m.of_uncurry_left, ?_⟩
  filter_upwards [hb₀b] with ω hω
  have hp : pathOf b ω = pathOf b₀ ω := funext fun s => (hω s).symm
  refine ⟨hp, ?_⟩
  have hpc : Continuous (pathOf b ω) := by rw [hp]; exact hb₀c ω
  have hp0 : pathOf b ω 0 = 0 := by rw [hp]; exact hb₀z ω
  have hhit : ∃ s : ℝ, 0 ≤ s ∧ ZoomRadial.Xdrift α Q (pathOf b ω) s ≤ -c := by
    rw [hp]; exact ZoomRadial.exists_drift_le (hb₀h ω)
  refine Prod.ext ?_ ?_
  · simp only [radG]
    rw [ZoomRadial.Thit_toReal hpc hp0 hc hhit, ZoomRadial.sInf_drift_eq_Tc]
  · simp only [radG]
    funext s
    rw [ZoomRadial.Zsur_eq_VpathPath hpc hp0 hc hhit, ← ZoomRadial.trunc_Vpath_eq_VpathPath]
    rfl

/-- `Tc` is a.e.-measurable for every level. -/
theorem aemeasurable_Tc {α Q c : ℝ} {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P) (hαQ : α < Q) :
    AEMeasurable (ZoomRadial.Tc α Q c b) P := by
  rcases lt_or_ge 0 c with hc | hc
  · obtain ⟨b₀, hb₀, hae⟩ := ae_radData_eq 0 hb hαQ hc
    refine ((measurable_fst.comp (measurable_radG α Q c 0)).comp hb₀).aemeasurable.congr ?_
    filter_upwards [hae] with ω h
    have := congrArg Prod.fst h.2
    simp only [Function.comp_apply] at this ⊢
    rw [this, h.1]
  · obtain ⟨b₀, -, -, hb₀z, -, hb₀b⟩ := ZoomRadial.exists_nice_version hb hαQ one_pos
    refine (aemeasurable_const (b := (0 : ℝ))).congr ?_
    filter_upwards [hb₀b] with ω hω
    rw [Tc_congr_path (fun s => (hω s).symm)]
    have hmem : IsLeast {t : ℝ | 0 ≤ t ∧ ZoomRadial.Xc α Q c b₀ ω t ≤ 0} 0 := by
      refine ⟨⟨le_rfl, ?_⟩, fun t ht => ht.1⟩
      simp only [ZoomRadial.Xc, Real.toNNReal_zero, hb₀z ω, mul_zero, add_zero]
      exact hc
    exact (hmem.csInf_eq).symm

end

/-! ## The model's radial data -/

section Model
variable {γ α r L : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

theorem aemeasurable_n2RadR (hα : α < Qc γ) (hr : 0 < r) (hX : IsFreeGFFModConstH X P)
    (hL : 0 < n2Lev γ α L r) (K : ℕ) : AEMeasurable (n2RadR γ α L r K X) P := by
  obtain ⟨b₀, hb₀, hae⟩ := ae_radData_eq (Real.log K) (isBrownianReal_zRadB hX hr) hα hL
  refine ((measurable_radG α (Qc γ) (n2Lev γ α L r) (Real.log K)).comp hb₀).aemeasurable.congr ?_
  filter_upwards [hae] with ω h
  simp only [Function.comp_apply, n2RadR]
  rw [h.2, h.1]

/-- **The radial TV bound in `tvDist` form.** -/
theorem tvDist_n2RadR_le {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''}
    [IsProbabilityMeasure P''] {A : ℝ → Ω'' → ℝ} (hγ : 0 < γ) (hα : α < Qc γ) (hr : 0 < r)
    (hX : IsFreeGFFModConstH X P) (hA : IsWedgeProcess α (Qc γ) A P'') (hL : 0 < n2Lev γ α L r)
    {K : ℕ} (hK : 0 < K) :
    TV.tvDist ((P.map (n2RadR γ α L r K X)).map Prod.snd) (P''.map (radR'' K A)) ≤
      ENNReal.ofReal (2 * (P'' {ω | ∃ u ∈ Icc 0 (Real.log K),
        n2Lev γ α L r ≤ A (-u) ω}).toReal) := by
  have hS : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hR := aemeasurable_n2RadR hα hr hX hL K
  have hR'' : AEMeasurable (radR'' K A) P'' :=
    (ZoomRadial.measurable_trunc (Real.log K)).comp_aemeasurable (ZoomRadial.aemeasurable_wedgePath hA)
  rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hR]
  refine tvDist_le_ofReal_of_abs fun E hE => ?_
  rw [Measure.map_apply_of_aemeasurable (measurable_snd.comp_aemeasurable hR) hE,
    Measure.map_apply_of_aemeasurable hR'' hE]
  exact (n2_radial_tv hγ hα hr hX hA hS).2 L hL E hE
end Model

end D3Plus
end QuantumZipper
