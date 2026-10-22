import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.Rho
import HigherDimLQGMetric.Frozen.Theorem12
import HigherDimLQGMetric.Thm13.ProbSubseq
import HigherDimLQGMetric.Thm13.LocalLower
import HigherDimLQGMetric.Sec4.Bridge
import HigherDimLQGMetric.LfppTight.LawInput
import HigherDimLQGMetric.LfppTight.CrossMeas
import HigherDimLQGMetric.LfppTight.CrossGeom
import HigherDimLQGMetric.Sharp.ScaledMetric

/-!
# Fatou passage: basic canonical metric facts

Helpers for the passage from median-normalized convolution LFPP to the canonical strong metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- The uniform DGZ hypothesis supplies exactly the subcriticality needed by Theorem 1.2. -/
theorem fatou_subcritical {d : ℕ} {κ : Rd d → ℝ} {b μ ξ : ℝ}
    (h : UHyp d κ b μ ξ) :
    0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ :=
  ⟨h.base.xi_pos, h.base.subcritical⟩

/-- A canonical strong metric together with convergence of median-normalized convolution LFPP. -/
theorem fatou_exists_canonical {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) :
    ∃ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D ∧
      TendstoInProbLU (normLGFLaw d)
        (fun ε g => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) (𝓝[>] 0)
        (fun g => (D g).1) := by
  let _ : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  obtain ⟨D, hD, hconv⟩ := (HigherDimLQGMetric.theorem12 d ξ hd h.base.xi_pos
    h.base.subcritical).1
  refine ⟨D, hD, ?_⟩
  exact hconv κ hκ (normLGFLaw d) id
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).2.1.1.isLGFPlusBddCont

/-- A fixed positive sequence of convolution scales below one. -/
def fatouEps (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (n + 1)

theorem fatouEps_pos (n : ℕ) : 0 < fatouEps n := by
  unfold fatouEps
  positivity

theorem fatouEps_lt_one (n : ℕ) : fatouEps n < 1 := by
  unfold fatouEps
  have h : (2 : ℝ)⁻¹ < 1 := by norm_num
  exact (pow_lt_one₀ (by norm_num : 0 ≤ (2 : ℝ)⁻¹) h (by omega : n + 1 ≠ 0))

theorem fatouEps_tendsto : Tendsto fatouEps atTop (𝓝[>] (0 : ℝ)) := by
  unfold fatouEps
  exact tendsto_nhdsWithin_iff.2 ⟨
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1),
    Eventually.of_forall fun n => mem_Ioi.2 (fatouEps_pos n)⟩

/-- The canonical metric admits an almost surely locally uniform LFPP subsequence. -/
theorem fatou_exists_subseq {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ξ : ℝ}
    (D : DistRd d → ContMetric d)
    (hconv : TendstoInProbLU (normLGFLaw d)
      (fun ε g => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) (𝓝[>] 0)
      (fun g => (D g).1)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ g ∂(normLGFLaw d),
        Tendsto (fun k => toCMapRd ((aEps κ ξ (fatouEps (ns k)))⁻¹ •
          lfppDist κ ξ (fatouEps (ns k)) g)) atTop (𝓝 (D g).1) := by
  let _ : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  have hn : IsNormalizedLGF id (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).2.1
  let X : ℕ → DistRd d → C(Rd d × Rd d, ℝ) := fun n g =>
    toCMapRd ((aEps κ ξ (fatouEps n))⁻¹ • lfppDist κ ξ (fatouEps n) g)
  have hm (n : ℕ) : AEMeasurable (X n) (normLGFLaw d) :=
    l6a_aemeasurable_normalized_lfpp (by omega : 2 ≤ d) κ hκ ξ
      (fatouEps_pos n) (normLGFLaw d) id hn.1.isLGFPlusBddCont
  have heq (n : ℕ) :
      (fun g => (aEps κ ξ (fatouEps n))⁻¹ • lfppDist κ ξ (fatouEps n) g) =ᵐ[normLGFLaw d]
        (fun g => ⇑(X n g)) := by
    filter_upwards [l10a_ae_continuous_convMollify (by omega : 2 ≤ d)
      κ hκ (normLGFLaw d) id hn (fatouEps_pos n)] with g hg
    funext p
    have hf : lfppDist κ ξ (fatouEps n) g =
        fieldLfpp ξ (convMollify κ (fatouEps n) g) := by
      funext q
      exact (fieldLfpp_eq_lfppDistOn hg q).symm
    have hc : Continuous ((aEps κ ξ (fatouEps n))⁻¹ •
        lfppDist κ ξ (fatouEps n) g) := by
      rw [hf]
      exact (continuous_fieldLfpp hg).const_smul _
    exact (toCMapRd_apply_of_continuous hc p).symm
  have hprobRaw : TendstoInProbLU (normLGFLaw d)
      (fun n g => (aEps κ ξ (fatouEps n))⁻¹ • lfppDist κ ξ (fatouEps n) g)
      atTop (fun g => (D g).1) := by
    intro R hR δ hδ
    exact (hconv R hR δ hδ).comp fatouEps_tendsto
  have hprob : TendstoInProbLU (normLGFLaw d) (fun n g => (X n g)) atTop
      (fun g => (D g).1) := by
    intro R hR δ hδ
    have hevents : (fun n => (normLGFLaw d) {g | ENNReal.ofReal δ ≤
        ⨆ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
          edist (X n g p) ((D g).1 p)}) =
        (fun n => (normLGFLaw d) {g | ENNReal.ofReal δ ≤
        ⨆ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
          edist (((aEps κ ξ (fatouEps n))⁻¹ • lfppDist κ ξ (fatouEps n) g) p)
            ((D g).1 p)}) := by
      funext n
      apply measure_congr
      filter_upwards [heq n] with g hg
      simp only [← hg]
    rw [hevents]
    exact hprobRaw R hR δ hδ
  exact l8_exists_subseq_ae_of_prob (normLGFLaw d) X (fun g => (D g).1) hm hprob

/-- The minimum of a continuous pair observable over two compact sets varies continuously
with the observable in the compact-open topology. -/
theorem fatou_continuous_infPairs {d : ℕ} {A B : Set (Rd d)}
    (hA : IsCompact A) (hB : IsCompact B) :
    Continuous (fun F : C(Rd d × Rd d, ℝ) => infPairs F A B) := by
  have hK : IsCompact (A ×ˢ B) := hA.prod hB
  have hf : Continuous (fun q : C(Rd d × Rd d, ℝ) × (Rd d × Rd d) =>
      ENNReal.ofReal (q.1 q.2)) :=
    ENNReal.continuous_ofReal.comp continuous_eval
  convert hK.continuous_sInf
    (f := fun (F : C(Rd d × Rd d, ℝ)) (p : Rd d × Rd d) => ENNReal.ofReal (F p)) hf using 1
  funext F
  rw [sInf_image, biInf_prod]
  rfl

/-- Across-sphere distance is a continuous observable of the continuous metric function. -/
theorem fatou_continuous_across {d : ℕ} (z : Rd d) (a c : ℝ) :
    Continuous (fun F : C(Rd d × Rd d, ℝ) =>
      infPairs F (sphere z a) (sphere z c)) :=
  fatou_continuous_infPairs (isCompact_sphere _ _) (isCompact_sphere _ _)

/-- Almost surely, taking a compact-pair infimum commutes with the positive median scaling of
the convolution LFPP metric. The sets need no compactness for this algebraic identity. -/
theorem fatou_prelimit_infPairs_ae {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (A B : Set (Rd d)) :
    ∀ᵐ g ∂(normLGFLaw d),
      infPairs (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g)) A B =
        (ENNReal.ofReal (aEps κ ξ ε))⁻¹ * infPairs (lfppDist κ ξ ε g) A B := by
  let _ : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd).2.1
  have ha : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε
  filter_upwards [l10a_ae_continuous_convMollify hd κ hκ (normLGFLaw d) id hn hε]
    with g hg
  have hf : lfppDist κ ξ ε g = fieldLfpp ξ (convMollify κ ε g) := by
    funext p
    exact (fieldLfpp_eq_lfppDistOn hg p).symm
  have hc : Continuous ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) := by
    rw [hf]
    exact (continuous_fieldLfpp hg).const_smul _
  have heq : (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) :
      Rd d × Rd d → ℝ) = fun p => (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε g p := by
    funext p
    rw [toCMapRd_apply_of_continuous hc]
    rfl
  rw [heq, l6a_infPairs_mul _ A B (inv_pos.mpr ha), ENNReal.ofReal_inv_of_pos ha]

/-- The internal distance of the continuous LFPP metric is bounded by the original
piecewise-C¹ LFPP path infimum on the same domain. -/
theorem fatou_field_internal_le {d : ℕ} (ξ : ℝ) (φ : C(Rd d, ℝ))
    (V : Set (Rd d)) (x y : Rd d) :
    (fieldLfppMetric ξ φ).internal V x y ≤ fieldDistIn ξ φ V x y := by
  unfold fieldDistIn
  refine le_iInf fun P => ?_
  have hlen := (fieldLfppMetric ξ φ).internal_le_len zero_le_one
    P.2.1.continuousOn P.2.2
  rw [P.2.1.source, P.2.1.target] at hlen
  exact hlen.trans (fieldLfppMetric_len_le_lfppLen φ P.2.1 le_rfl le_rfl)

/-- On an open connected domain, the previous bound uses HigherDimLFPP's real
internal distance. -/
theorem fatou_field_internal_le_lfppDistOn {d : ℕ} (ξ : ℝ) (φ : C(Rd d, ℝ))
    {V : Set (Rd d)} (hVopen : IsOpen V) (hVconn : IsPreconnected V)
    {x y : Rd d} (hx : x ∈ V) (hy : y ∈ V) :
    (fieldLfppMetric ξ φ).internal V x y ≤
      ENNReal.ofReal (HigherDimLFPP.lfppDistOn ξ φ V x y) := by
  calc
    (fieldLfppMetric ξ φ).internal V x y ≤ fieldDistIn ξ φ V x y :=
      fatou_field_internal_le ξ φ V x y
    _ = _ := fieldDistIn_eq_ofReal φ.continuous
      (DGZ.pcwJoined_of_isPreconnected hVopen hVconn hx hy)

end HigherDimLQGContinuity
