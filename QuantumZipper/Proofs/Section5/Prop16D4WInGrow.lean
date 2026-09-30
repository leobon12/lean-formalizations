import QuantumZipper.Proofs.Section5.Prop16D4WInTV
import QuantumZipper.Proofs.Wire2b

/-!
# D4⁺ʷ inputs (part 6): clauses `hgrow` and `htight`

Clauses `hgrow` (the canonical area of `B_s ∩ ℍ` crosses `1` strictly at `s = 1`, uniformly in
probability) and `htight` (tightness of the area of `B_ρ ∩ ℍ`) of `Prop16D4WInputsStmt`, for
the unperturbed zoomed field, follow from the TV-local convergence of its canonical description
to a wedge `W` (input (1), the Palm zoom) and the area profile of the wedge
(`AreaProfile.HasAreaProfile`: finite, strictly increasing, `= 1` at radius `1`):

* the half-ball area `μ_x(B_{sa} ∩ ℍ) = μ_{canon}(B_s ∩ ℍ)` is squeezed between measurable
  functionals `phiN` of `locField (R+1)` of the canonical field (`canon_point`), which transfer
  through the TV distance (`tv_event_bound`);
* for the wedge, the same functionals are squeezed by the profile at nearby radii
  (`wedge_point`), and the profile is continuous from the right/left in the needed sense by
  strict monotonicity, so the wedge probabilities of the bad events tend to `0`
  (`map_antitone_tendsto`).

The wedge profile of an arbitrary `γ`-quantum wedge is `ae_profileWeak_of_isQuantumWedge`
(`Prop16D4WInWedge.lean`).
Own elementary arguments (Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25, uses the
continuity of the wedge area profile implicitly).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G TV Factorization CoordsFull

/-- The local field of a quantum wedge is a.e.-measurable. -/
theorem aemeasurable_locField_wedge {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} {W : Ω' → FieldSample} (hW : IsQuantumWedge γ γ W P')
    (N : ℕ) : AEMeasurable (fun ω => locField N (W ω)) P' := by
  have hd := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hW.1)
    (hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hW.1) hγ hγ2 hW
  have hm : Measurable fun c : (ℕ → ℝ) × (TestFun H → ℝ) =>
      locField N (reconstruct (WedgeCan4.piC c.1)) :=
    (measurable_locField N).comp ((measurable_reconstruct.comp WedgeCan4.measurable_piC).comp
      measurable_fst)
  refine (hm.comp_aemeasurable hd).congr (Eventually.of_forall fun ω => ?_)
  change locField N (reconstruct (WedgeCan4.piC (coordsFull (W ω)))) = locField N (W ω)
  rw [WedgeCan4.piC_coordsFull]
  exact locField_recon N (W ω)

/-- The local field of a field with a.e.-measurable coordinates is a.e.-measurable. -/
theorem aemeasurable_locField_of_coords {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Z : α → FieldSample} (hZ : AEMeasurable (fun p => coords (Z p)) μ) (N : ℕ) :
    AEMeasurable (fun p => locField N (Z p)) μ :=
  (((measurable_locField N).comp measurable_reconstruct).comp_aemeasurable hZ).congr
    (Eventually.of_forall fun p => locField_recon N (Z p))

/-- Wedge side of the squeeze. -/
theorem wedge_point {γ : ℝ} {w : FieldSample} (hw : IsLQGGood γ w) {R : ℕ} {s1 s2 : ℝ}
    (h12 : s1 < s2) (h2R : s2 ≤ R) :
    qAreaMeasure γ w (ball 0 s1 ∩ H) ≤ phiN γ R (rbump s1 s2) (locField (R + 1) w) ∧
    phiN γ R (rbump s1 s2) (locField (R + 1) w) ≤ qAreaMeasure γ w (ball 0 s2 ∩ H) := by
  have hv := isVagueLimitOn_H_of_good hw
  rw [← liApprox_eq_phiN, liApprox_eq_lintegral subset_rfl inter_subset_right hv
    (continuous_rbump s1 s2) (rbump_nonneg s1 s2) (hasCompactSupport_rbump h12)
    (fun z hz => mem_ball_zero_iff.2 ((norm_lt_of_rbump_ne_zero h12 hz).trans_le h2R))]
  exact ⟨lintegral_rbump_ge h12 _, lintegral_rbump_le h12 hv.1⟩

/-- Canonical side of the squeeze. -/
theorem canon_point {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ} {x : FieldSample}
    (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V)
    (ha : 0 < scaleParamOn γ x U) {R : ℕ} (hR : hball R ⊆ canonicalDomainOn γ x U) {s1 s2 : ℝ}
    (h12 : s1 < s2) (h2R : s2 ≤ R) :
    qAreaMeasureOn γ x U (ball 0 (s1 * scaleParamOn γ x U) ∩ H) ≤
      phiN γ R (rbump s1 s2) (locField (R + 1) (canonicalOn γ x U)) ∧
    phiN γ R (rbump s1 s2) (locField (R + 1) (canonicalOn γ x U)) ≤
      qAreaMeasureOn γ x U (ball 0 (s2 * scaleParamOn γ x U) ∩ H) := by
  obtain ⟨hH, hball', hli⟩ := canon_facts hγ hx hU hUH hUV ha
  rw [← liApprox_eq_phiN, hli R hR _ (continuous_rbump s1 s2) (rbump_nonneg s1 s2)
    (hasCompactSupport_rbump h12)
    (fun z hz => mem_ball_zero_iff.2 ((norm_lt_of_rbump_ne_zero h12 hz).trans_le h2R)),
    ← hball', ← hball']
  exact ⟨lintegral_rbump_ge h12 _, lintegral_rbump_le h12 hH⟩

theorem quarter_sum (θ : ℝ≥0∞) : θ / 2 / 2 + θ / 2 / 2 + (θ / 2 / 2 + θ / 2 / 2) = θ := by
  rw [ENNReal.add_halves, ENNReal.add_halves]

theorem quarter_pos {θ : ℝ≥0∞} (hθ : 0 < θ) : 0 < θ / 2 / 2 :=
  ENNReal.half_pos (ENNReal.half_pos hθ.ne').ne'

end Prop16Asm

end QuantumZipper
