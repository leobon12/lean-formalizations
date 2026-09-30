import QuantumZipper.Proofs.Thm18.G1Z2MeasCore
import QuantumZipper.Proofs.LQG.GoodMeasurable
import QuantumZipper.Proofs.Thm18.G1RegRepMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z5 (D58, S1): a countable certificate for the side boundary limit along all radii

For a regular sample `x`, the side boundary limit along all radii `a 2^{-k}`
(`G1Z2SideBdryLim γ left x ν` for some `ν`) is equivalent to the countable Cauchy condition
`SideCert γ left x`, which is a measurable condition on `x` (`measurable_sideCert`).

The side half-line `S` is identified with `ℝ` by `σ t = log (s t)` (`s = ∓1`), inverse
`τ u = s e^u`. The test functions are the glued functions `S.indicator (g ∘ σ)` for the countable
family `testFam N m`, `bump N` of `BoundaryVague`; the limit measure is produced on `ℝ` from the
pushed approximations `(bdryR|_S).map σ` by Riesz–Markov
(`BdryVague.exists_isVagueLimitR_of_testFam`) and carried back by `τ`. This is the half-line
analogue of `GoodMeas.hasBdryLimit_of_cert` (GoodMeasurable.lean). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z5

open GoodSample GoodMeas
open BdryVague (testFam bump continuous_testFam hasCompactSupport_testFam continuous_bump
  hasCompactSupport_bump)

/-- The sign of the side: `-1` on the left, `1` on the right. -/
def sgn (left : Bool) : ℝ := if left then -1 else 1

theorem sgn_mul_self (left : Bool) : sgn left * sgn left = 1 := by
  cases left <;> simp [sgn]

theorem mem_side_iff (left : Bool) (t : ℝ) : t ∈ g1SideHalf left ↔ 0 < sgn left * t := by
  cases left <;> simp [g1SideHalf, sgn]

/-- The chart `σ : S → ℝ`. -/
def sig (left : Bool) (t : ℝ) : ℝ := Real.log (sgn left * t)

/-- Its inverse `τ : ℝ → S`. -/
def tau (left : Bool) (u : ℝ) : ℝ := sgn left * Real.exp u

theorem continuous_tau (left : Bool) : Continuous (tau left) :=
  continuous_const.mul Real.continuous_exp

theorem measurable_sig (left : Bool) : Measurable (sig left) :=
  Real.measurable_log.comp (measurable_const.mul measurable_id)

theorem tau_mem (left : Bool) (u : ℝ) : tau left u ∈ g1SideHalf left := by
  rw [mem_side_iff, tau, ← mul_assoc, sgn_mul_self, one_mul]; exact Real.exp_pos u

theorem tau_sig {left : Bool} {t : ℝ} (ht : t ∈ g1SideHalf left) : tau left (sig left t) = t := by
  rw [mem_side_iff] at ht
  rw [tau, sig, Real.exp_log ht, ← mul_assoc, sgn_mul_self, one_mul]

theorem sig_tau (left : Bool) (u : ℝ) : sig left (tau left u) = u := by
  rw [sig, tau, ← mul_assoc, sgn_mul_self, one_mul, Real.log_exp]

theorem continuousOn_sig (left : Bool) : ContinuousOn (sig left) (g1SideHalf left) := by
  refine Real.continuousOn_log.comp (continuous_const.mul continuous_id).continuousOn ?_
  intro t ht
  rw [mem_side_iff] at ht
  exact ht.ne'

/-- The glued test function `S.indicator (g ∘ σ)`. -/
def glue (left : Bool) (g : ℝ → ℝ) : ℝ → ℝ := (g1SideHalf left).indicator (g ∘ sig left)

theorem tsupport_glue_subset (left : Bool) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : tsupport (glue left g) ⊆ tau left '' tsupport g := by
  have hc : IsCompact (tau left '' tsupport g) := hgc.image (continuous_tau left)
  refine closure_minimal (fun t ht => ?_) hc.isClosed
  have hts : t ∈ g1SideHalf left := by
    by_contra h; exact ht (indicator_of_notMem h _)
  have hg0 : g (sig left t) ≠ 0 := by
    intro h0; apply ht; rw [glue, indicator_of_mem hts]; exact h0
  exact ⟨sig left t, subset_closure hg0, tau_sig hts⟩

theorem tsupport_glue_side (left : Bool) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : tsupport (glue left g) ⊆ g1SideHalf left := by
  refine (tsupport_glue_subset left hg hgc).trans ?_
  rintro _ ⟨u, -, rfl⟩; exact tau_mem left u

theorem hasCompactSupport_glue (left : Bool) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : HasCompactSupport (glue left g) :=
  IsCompact.of_isClosed_subset (hgc.image (continuous_tau left)) (isClosed_tsupport _)
    (tsupport_glue_subset left hg hgc)

theorem continuous_glue (left : Bool) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Continuous (glue left g) := by
  have hS : IsOpen (g1SideHalf left) := g1z2_isOpen_sideHalf left
  have hon : ContinuousOn (glue left g) (g1SideHalf left) :=
    (hg.comp_continuousOn (continuousOn_sig left)).congr fun t ht => by
      simp [glue, indicator_of_mem ht]
  refine continuous_of_tsupport fun t ht => ?_
  exact hon.continuousAt (hS.mem_nhds (tsupport_glue_side left hg hgc ht))

/-- The approximations pushed to `ℝ` by the chart. -/
def pushR (left : Bool) (μ : Measure ℝ) : Measure ℝ :=
  (μ.restrict (g1SideHalf left)).map (sig left)

theorem integral_glue (left : Bool) (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ t, glue left g t ∂μ = ∫ u, g u ∂pushR left μ := by
  rw [pushR, integral_map (measurable_sig left).aemeasurable hg.aestronglyMeasurable, glue,
    integral_indicator (g1z2_isOpen_sideHalf left).measurableSet]
  rfl

theorem integral_side (left : Bool) (μ : Measure ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    (hfS : tsupport f ⊆ g1SideHalf left) :
    ∫ t, f t ∂μ = ∫ u, f (tau left u) ∂pushR left μ := by
  rw [pushR, integral_map (f := fun u => f (tau left u)) (measurable_sig left).aemeasurable
    (hf.comp (continuous_tau left)).aestronglyMeasurable]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := g1SideHalf left) fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (hfS h)]
  refine setIntegral_congr_fun (g1z2_isOpen_sideHalf left).measurableSet fun t ht => ?_
  simp [tau_sig ht]

theorem pushR_apply_compact_lt_top (left : Bool) {μ : Measure ℝ}
    (hμ : ∀ K, IsCompact K → μ K < ⊤) {K : Set ℝ} (hK : IsCompact K) : pushR left μ K < ⊤ := by
  rw [pushR, Measure.map_apply (measurable_sig left) hK.isClosed.measurableSet,
    Measure.restrict_apply (measurable_sig left hK.isClosed.measurableSet)]
  refine (measure_mono fun t ht => ?_).trans_lt (hμ _ (hK.image (continuous_tau left)))
  exact ⟨sig left t, ht.1, tau_sig ht.2⟩

/-- **The countable side certificate.** -/
def SideCert (γ : ℝ) (left : Bool) (x : FieldSample) : Prop :=
  (∀ N m : ℕ, CauchyB γ (glue left (testFam N m)) x) ∧ ∀ N : ℕ, CauchyB γ (glue left (bump N)) x

theorem measurable_sideCert (γ : ℝ) (left : Bool) : Measurable (SideCert γ left) :=
  (Measurable.forall fun N => Measurable.forall fun m => measurable_CauchyB γ
      (continuous_glue left (continuous_testFam N m) (hasCompactSupport_testFam N m)).measurable).and
    (Measurable.forall fun N => measurable_CauchyB γ
      (continuous_glue left (continuous_bump N) (hasCompactSupport_bump N)).measurable)

theorem sideCert_of_lim {γ : ℝ} {left : Bool} {x : FieldSample} {ν : Measure ℝ}
    (hν : G1Z2SideBdryLim γ left x ν) : SideCert γ left x :=
  ⟨fun N m => cauchyB_of_tendsto (hν.2.2 _
      (continuous_glue left (continuous_testFam N m) (hasCompactSupport_testFam N m))
      (hasCompactSupport_glue left (continuous_testFam N m) (hasCompactSupport_testFam N m))
      (tsupport_glue_side left (continuous_testFam N m) (hasCompactSupport_testFam N m))),
    fun N => cauchyB_of_tendsto (hν.2.2 _
      (continuous_glue left (continuous_bump N) (hasCompactSupport_bump N))
      (hasCompactSupport_glue left (continuous_bump N) (hasCompactSupport_bump N))
      (tsupport_glue_side left (continuous_bump N) (hasCompactSupport_bump N)))⟩

/-- **Side limit from the certificate** (regular samples). -/
theorem sideLim_of_cert {γ : ℝ} {left : Bool} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : IsRegularWith x F) (hc : SideCert γ left x) : ∃ ν, G1Z2SideBdryLim γ left x ν := by
  have hfinR : ∀ i : ℕ × ℝ, 0 < goodRad i → ∀ K, IsCompact K → bdryR γ x (goodRad i) K < ⊤ :=
    fun i hi K hK => bdryR_lt_top γ h hi hK
  have hpos : ∀ k : ℕ, 0 < goodRad (k, 1) := fun k => mul_pos one_pos (radius_pos k)
  have hfin : ∀ k : ℕ, IsFiniteMeasureOnCompacts (pushR left (bdryR γ x (goodRad (k, 1)))) :=
    fun k => ⟨fun K hK => pushR_apply_compact_lt_top left (hfinR _ (hpos k)) hK⟩
  choose lT hlT using fun N m => tendsto_goodFilter_of_cauchyB h
    (continuous_glue left (continuous_testFam N m) (hasCompactSupport_testFam N m))
    (hasCompactSupport_glue left (continuous_testFam N m) (hasCompactSupport_testFam N m))
    (hc.1 N m)
  choose lB hlB using fun N => tendsto_goodFilter_of_cauchyB h
    (continuous_glue left (continuous_bump N) (hasCompactSupport_bump N))
    (hasCompactSupport_glue left (continuous_bump N) (hasCompactSupport_bump N)) (hc.2 N)
  simp only [integral_glue left _ (continuous_testFam _ _)] at hlT
  simp only [integral_glue left _ (continuous_bump _)] at hlB
  obtain ⟨ν₀, hν₀⟩ := BdryVague.exists_isVagueLimitR_of_testFam
    (νs := fun k => pushR left (bdryR γ x (goodRad (k, 1)))) hfin
    (fun N m => ⟨_, (hlT N m).comp tendsto_one_goodFilter⟩)
    (fun N => ⟨_, (hlB N).comp tendsto_one_goodFilter⟩)
  have hT : ∀ N m, lT N m = ∫ t, testFam N m t ∂ν₀ := fun N m =>
    tendsto_nhds_unique ((hlT N m).comp tendsto_one_goodFilter)
      (hν₀.2 _ (continuous_testFam N m) (hasCompactSupport_testFam N m))
  have hB : ∀ N, lB N = ∫ t, bump N t ∂ν₀ := fun N =>
    tendsto_nhds_unique ((hlB N).comp tendsto_one_goodFilter)
      (hν₀.2 _ (continuous_bump N) (hasCompactSupport_bump N))
  haveI := hν₀.1
  refine ⟨ν₀.map (tau left), ?_, fun K hK hKS => ?_, fun f hf hfc hfS => ?_⟩
  · rw [Measure.map_apply (continuous_tau left).measurable
      (g1z2_isOpen_sideHalf left).measurableSet.compl]
    have : tau left ⁻¹' (g1SideHalf left)ᶜ = ∅ := by
      ext u; simp [tau_mem left u]
    rw [this, measure_empty]
  · rw [Measure.map_apply (continuous_tau left).measurable hK.isClosed.measurableSet]
    have hc : IsCompact (sig left '' K) :=
      hK.image_of_continuousOn ((continuousOn_sig left).mono hKS)
    refine (measure_mono (s := tau left ⁻¹' K) (t := sig left '' K) fun u hu =>
      ⟨tau left u, hu, sig_tau left u⟩).trans_lt hc.measure_lt_top
  · have hfτ : Continuous fun u => f (tau left u) := hf.comp (continuous_tau left)
    have hfτc : HasCompactSupport fun u => f (tau left u) := by
      have hc : IsCompact (sig left '' tsupport f) :=
        hfc.image_of_continuousOn ((continuousOn_sig left).mono hfS)
      refine IsCompact.of_isClosed_subset hc (isClosed_tsupport _) (closure_minimal ?_ hc.isClosed)
      intro u hu
      exact ⟨tau left u, subset_closure hu, sig_tau left u⟩
    rw [integral_map (continuous_tau left).aemeasurable hf.aestronglyMeasurable]
    have ht := tendsto_of_testFam_filter (νs := fun i => pushR left (bdryR γ x (goodRad i)))
      (ν := ν₀) (eventually_goodRad_pos.mono fun i hi =>
        ⟨fun K hK => pushR_apply_compact_lt_top left (hfinR i hi) hK⟩)
      (fun N m => by rw [← hT N m]; exact hlT N m) (fun N => by rw [← hB N]; exact hlB N)
      hfτ hfτc
    refine ht.congr fun i => ?_
    exact (integral_side left _ hf hfS).symm

theorem exists_sideLim_iff {γ : ℝ} {left : Bool} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : IsRegularWith x F) : (∃ ν, G1Z2SideBdryLim γ left x ν) ↔ SideCert γ left x :=
  ⟨fun ⟨_, hν⟩ => sideCert_of_lim hν, sideLim_of_cert h⟩

/-- The certificate only reads the regularized averages. -/
theorem sideCert_congr {γ : ℝ} {left : Bool} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    SideCert γ left x ↔ SideCert γ left x' := by
  have hb : bdryR γ x = bdryR γ x' := by
    funext r; unfold bdryR bdryDens evalReg; rw [h]
  simp only [SideCert, CauchyB, bI, hb]

/-- **The certificate is measurable along a family with measurable circle coordinates.** -/
theorem measurableSet_sideCert_of_coords (γ : ℝ) (left : Bool) {Z : Type*} [MeasurableSpace Z]
    {G : Z → FieldSample} (hG : ∀ i, Measurable fun p => CoordsFull.coordsFull (G p) i) :
    MeasurableSet {p | SideCert γ left (G p)} := by
  have hm : Measurable fun p => E1.fromC (CoordsFull.coordsFull (G p)) :=
    G1Meas.measurable_fromC'.comp (measurable_pi_iff.2 hG)
  have e : {p | SideCert γ left (G p)} =
      (fun p => E1.fromC (CoordsFull.coordsFull (G p))) ⁻¹' {x | SideCert γ left x} := by
    ext p
    simp only [mem_setOf_eq, mem_preimage]
    exact (sideCert_congr (CoordsFull.avgReg_congr_full (E1.coordsFull_fromC (G p)))).symm
  rw [e]
  exact hm (measurableSet_setOfPred.2 (measurable_sideCert γ left))

end G1Z5
end Thm18Asm
end QuantumZipper
