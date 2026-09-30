import QuantumZipper.Proofs.Thm18.ZqCFix
import QuantumZipper.Proofs.Thm18.G3ZqO6Shift
import QuantumZipper.Proofs.Thm18.G2PalmLocCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (2): the shifted window condition is a far event; the conditional limit at one point

The shifted window condition `ν[0, x − δ] ≤ U` (`G3ZqO.winD`) reads the boundary measure only on
`[0, x − δ]`. For a good field sample `y` (`IsLQGGood`) the boundary length of that segment is the
local functional `winLen` of `y` read on the folded circles missing `B(x, δ/4)`
(`bdryM_seg_eq_winLen`, from `G2PalmLoc.locLen_restrict_eq`: Duplantier–Sheffield locality of
circle averages). For the wedge Palm field `h^x = N_S(ofFun (palmProf γ x) + V)` every value on
such a circle is a deterministic constant plus a balanced increment of `V` carried outside
`B(x, δ/4)`, so `winLen h^x` is measurable for the σ-algebra of the far Gaussian pairs
`G3ZqF.g3fPairs x (δ/4)` (`measurable_restrict_palmField`), and the window event is a preimage
of the far Gaussian family (`exists_gauss_preimage_winLen`). With the `Γ`-form conditional zoom
(`ZqC.palmFix_gamma`) this gives the conditional zoom limit at one Palm point jointly with the
window event (`palm_window_fix`).

Sheffield, arXiv:1012.4797, proof of Prop. 5.5 (p. 65: the boundary length away from the point is
a function of the field outside a neighbourhood of the point) and of Thm. 1.8 (pp. 70–71).
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open D3Plus S5.FieldLaw.Raw G2PalmLoc

/-- The far Gaussian family of `V` at `x` (balanced increments carried outside `B(x, ρ)`). -/
def gaussV {Ω' : Type} (V : Ω' → FieldSample) (x ρ : ℝ) (ω : Ω') : K3.OutIdx 0 ρ → ℝ :=
  fun k => WedgeTK.gaussFam V (G3ZqF.g3fPairs x ρ) k ω

theorem map_neg_add (μ : Measure ℂ) (x : ℝ) :
    (μ.map (· + ((-x : ℝ) : ℂ))).map (· + (x : ℂ)) = μ := by
  rw [Measure.map_map (measurable_add_const _) (measurable_add_const _)]
  have e : ((· + (x : ℂ)) ∘ (· + ((-x : ℝ) : ℂ))) = id := by
    funext z; simp
  rw [e, Measure.map_id]

theorem map_add_neg_ball (μ : Measure ℂ) (x ρ : ℝ) :
    (μ.map (· + ((-x : ℝ) : ℂ))) (ball ((0 : ℝ) : ℂ) ρ) = μ (ball (x : ℂ) ρ) := by
  rw [Measure.map_apply (measurable_add_const _) measurableSet_ball]
  congr 1
  ext z
  simp only [mem_preimage, mem_ball, dist_eq_norm, Complex.ofReal_zero, sub_zero]
  push_cast
  ring_nf

/-- **The wedge Palm field read on the circles missing `B(x, ρ)` is a function of the far
Gaussian pairs.** -/
theorem measurable_restrict_palmField {Ω' : Type} [MeasurableSpace Ω'] (V : Ω' → FieldSample)
    (γ x ρ : ℝ) (hxρ : |x| + ρ ≤ 1) :
    Measurable[MeasurableSpace.comap (gaussV V x ρ) MeasurableSpace.pi]
      fun ω => restrictField (circOut x ρ x ρ) (G1Zm.palmFieldAt γ x (V ω)) := by
  classical
  set m := MeasurableSpace.comap (gaussV V x ρ) MeasurableSpace.pi with hm
  have hG : Measurable[m] (gaussV V x ρ) := comap_measurable _
  refine (@measurable_pi_iff Ω' _ (fun _ => ℝ) m _ _).2 fun μ => ?_
  by_cases h : μ ∈ circOut x ρ x ρ
  · simp only [restrictField, h, if_true]
    obtain ⟨d, r, hr, rfl, hnull⟩ := h
    rw [union_self] at hnull
    have hμa : IsAdmissibleH (foldedCircle d r) := D3Plus.isAdmissibleH_foldedCircle' d hr
    have hSa : IsAdmissibleH R18.g3zS := D3Plus.isAdmissibleH_foldedCircle' 0 one_pos
    have hSn : R18.g3zS (ball (x : ℂ) ρ) = 0 := by
      have h := refS_ball_null_of (x := x) (κ := 2 * ρ) (t := x) (r := ρ)
        (by rw [show 2 * ρ / 2 = ρ by ring]) hxρ
      rwa [show 2 * ρ / 2 = ρ by ring] at h
    have hmass : (foldedCircle d r).map (· + ((-x : ℝ) : ℂ)) Set.univ =
        R18.g3zS.map (· + ((-x : ℝ) : ℂ)) Set.univ := by
      rw [Measure.map_apply (measurable_add_const _) MeasurableSet.univ,
        Measure.map_apply (measurable_add_const _) MeasurableSet.univ, preimage_univ,
        measure_univ, measure_univ]
    set k : K3.OutIdx 0 ρ := ⟨((foldedCircle d r).map (· + ((-x : ℝ) : ℂ)),
        R18.g3zS.map (· + ((-x : ℝ) : ℂ))),
      isAdmissibleH_map_add_real hμa (-x), isAdmissibleH_map_add_real hSa (-x), hmass,
      by rw [map_add_neg_ball]; exact hnull, by rw [map_add_neg_ball]; exact hSn⟩ with hk
    have ek : ∀ ω, gaussV V x ρ ω k = V ω (foldedCircle d r) - V ω R18.g3zS := by
      intro ω
      simp only [gaussV, WedgeTK.gaussFam, G3ZqF.g3fPairs, hk, map_neg_add]
    have e : (fun ω => G1Zm.palmFieldAt γ x (V ω) (foldedCircle d r)) = fun ω =>
        gaussV V x ρ ω k + (ofFun (G3Za.palmProf γ x) (foldedCircle d r) -
          ofFun (G3Za.palmProf γ x) R18.g3zS) := by
      funext ω
      rw [ek]
      simp only [G1Zm.palmFieldAt, PalmNorm.normAt, addConst, Pi.add_apply, measure_univ,
        ENNReal.toReal_one, mul_one]
      ring
    rw [e]
    exact ((measurable_pi_apply k).comp hG).add measurable_const
  · simp only [restrictField, h, if_false]
    exact measurable_const

/-- The lower end of the shifted window segment. -/
def segLo (left : Bool) (δ x : ℝ) : ℝ := if left then x + δ else 0

/-- The upper end of the shifted window segment. -/
def segHi (left : Bool) (δ x : ℝ) : ℝ := if left then 0 else x - δ

theorem seg_eq_Icc (left : Bool) (δ x : ℝ) :
    g1SideSeg left (G3ZqO.shPt left δ x) = Icc (segLo left δ x) (segHi left δ x) := by
  cases left <;> simp [g1SideSeg, G3ZqO.shPt, segLo, segHi]

/-- The boundary length of the shifted window segment read on the circles missing `B(x, δ/4)`. -/
def winLen (γ : ℝ) (left : Bool) (δ x : ℝ) (y : FieldSample) : ℝ≥0∞ :=
  locLen γ (restrictField (circOut x (δ / 4) x (δ / 4)) y) (segLo left δ x) (segHi left δ x)
    (δ / 4)

theorem seg_far (left : Bool) {δ x : ℝ} (hδ : 0 < δ) :
    ∀ s ∈ Icc (segLo left δ x - δ / 4) (segHi left δ x + δ / 4), δ / 4 + δ / 4 < |s - x| := by
  intro s hs
  cases left
  · simp only [segLo, segHi, Bool.false_eq_true, if_false, mem_Icc] at hs
    rw [abs_of_neg (by linarith [hs.2])]
    linarith [hs.2]
  · simp only [segLo, segHi, if_true, mem_Icc] at hs
    rw [abs_of_pos (by linarith [hs.1])]
    linarith [hs.1]

/-- **For a good sample the shifted window length is the local functional `winLen`.** -/
theorem bdryM_seg_eq_winLen {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) (left : Bool)
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    bdryM γ y (g1SideSeg left (G3ZqO.shPt left δ x)) = winLen γ left δ x y := by
  rw [bdryM, if_pos (G4Core.bCert_of_isLQGGood hy), seg_eq_Icc, winLen,
    locLen_restrict_eq hy (by positivity) (seg_far left hδ)]

/-- **The window event of the wedge Palm field is an event of the far Gaussian pairs.** -/
theorem exists_gauss_preimage_winLen {Ω' : Type} [MeasurableSpace Ω'] (V : Ω' → FieldSample)
    (γ : ℝ) (left : Bool) {δ x : ℝ} (hxδ : |x| + δ / 4 ≤ 1) (U : ℝ≥0∞) :
    ∃ B : Set (K3.OutIdx 0 (δ / 4) → ℝ), MeasurableSet B ∧
      {ω | winLen γ left δ x (G1Zm.palmFieldAt γ x (V ω)) ≤ U} = gaussV V x (δ / 4) ⁻¹' B := by
  have hm := measurable_restrict_palmField V γ x (δ / 4) hxδ
  have hL : Measurable[MeasurableSpace.comap (gaussV V x (δ / 4)) MeasurableSpace.pi]
      fun ω => winLen γ left δ x (G1Zm.palmFieldAt γ x (V ω)) :=
    (measurable_locLen γ _ _ _).comp hm
  obtain ⟨B, hB, e⟩ := MeasurableSpace.measurableSet_comap.1 (hL measurableSet_Iic)
  exact ⟨B, hB, e.symm⟩

/-- The window event of the wedge Palm field at `x`. -/
def palmWin (γ : ℝ) (left : Bool) (U δ x : ℝ) {Ω' : Type} (V : Ω' → FieldSample) : Set Ω' :=
  {ω | winLen γ left δ x (G1Zm.palmFieldAt γ x (V ω)) ≤ ENNReal.ofReal U}

/-- **The conditional zoom limit at one Palm point, jointly with the shifted window event.** -/
theorem palm_window_fix {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a) {left : Bool} {x δ : ℝ}
    (hxs : x ∈ g1SideHalf left) (hx1 : |x| ≤ 1 / 2) (hδ : 0 < δ) (hδ1 : δ ≤ 2)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (V : Ω' → FieldSample) (hV : IsFreeGFFModConstH V P')
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Y'' : Ω'' → FieldSample) (hW : IsQuantumWedge γ γ Y'' P'') (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1)
    (U : ℝ) {e : ℝ≥0∞} (he : 0 < e) :
    ∀ᶠ L in atTop,
      ∫⁻ ω, (palmWin γ left U δ x V).indicator 1 ω *
          Γ (g1zLocData R (G3Z2b2.g1zM γ L Ψ left ((G1Zm.palmFieldAt γ x (V ω), a), x))) ∂P' ≤
        P' (palmWin γ left U δ x V) * (∫⁻ ω, Γ (locFieldFull R (Y'' ω)) ∂P'') + e ∧
      P' (palmWin γ left U δ x V) * (∫⁻ ω, Γ (locFieldFull R (Y'' ω)) ∂P'') ≤
        ∫⁻ ω, (palmWin γ left U δ x V).indicator 1 ω *
          Γ (g1zLocData R (G3Z2b2.g1zM γ L Ψ left ((G1Zm.palmFieldAt γ x (V ω), a), x))) ∂P' +
          e := by
  obtain ⟨B, hB, hWB⟩ := exists_gauss_preimage_winLen V γ left (δ := δ) (x := x)
    (by linarith) (ENNReal.ofReal U)
  filter_upwards [palmFix_gamma hγ hγ2 hsel ha hxs hx1 (by positivity : 0 < δ / 4) P' V hV
    P'' Y'' hW R Γ hΓ hΓ1 he] with L hL
  have e1 : palmWin γ left U δ x V = gaussV V x (δ / 4) ⁻¹' B := hWB
  rw [e1]
  exact hL B hB

end ZqC
end Thm18Asm
end QuantumZipper
