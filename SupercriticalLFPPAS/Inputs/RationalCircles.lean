import SupercriticalLQGUniqueness.B2.Final.Assembly7
import SupercriticalLQGUniqueness.B2.PfeAxioms.R68IdBSite
import SupercriticalLQGUniqueness.B2.LscTop.InProbability
import SupercriticalLQGUniqueness.B2.PfeLocal.L4Main
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable
import SupercriticalLFPPAS.Inputs.RationalCirclePositive
import SupercriticalLFPPAS.Inputs.RationalCircleDistanceFinite
import SupercriticalLFPPAS.Inputs.RationalLFPPFinite
import SupercriticalLFPPAS.Inputs.PositiveCutoffSeqCriterion
import SupercriticalLQGUniqueness.Frozen.Exists_strongLQGMetric_lfppLimit
import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import SupercriticalLQGUniqueness.Frozen.IsLFPPNormalizer
import SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing
import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import LQGMetric.Papers.DFGPS.T12P0
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import SupercriticalLFPPAS.Inputs.ENNRealConvergenceInMeasure

/-! Sequence convergence in probability of normalized LFPP distances between fixed rational
circles, identified with the canonical limit from the frozen DG theorem. -/

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Set
open scoped ENNReal NNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS

private theorem rationalCircle_isRationalCircle (q : ℚ × ℚ) (r : ℚ) (hr : 0 < r) :
    SupercriticalLQGUniqueness.B2.Iface.IsRationalCircle (rationalCircle q r) := by
  refine ⟨q.1, q.2, r, le_of_lt hr, ?_⟩
  change Metric.sphere ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) (r : ℝ) =
    Metric.sphere (Complex.mk (q.1 : ℝ) (q.2 : ℝ)) (r : ℝ)
  congr 1
  apply Complex.ext <;> simp

/-- For any sequence of positive cutoffs tending to zero, the normalized LFPP distance between
two fixed rational circles converges in probability to the distance of the strong-LQG limit map
provided that map has the frozen LFPP limit property. -/
theorem rationalCircleDistance_tendstoInMeasure_seq_of_limit
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    (D : DistC → SupercriticalLQGUniqueness.LSCMetric)
    (hD : IsStrongLQGMetric ξ Q D)
    (hDconv : ∀ (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), LQGMetric.IsGFFPlusBddCont h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
          (∀ ε, IsHeatSmoothing P h ε (X ε)) →
          LSCTendstoInProbability P
            (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
            (fun ω => (D (h ω)).toLSCFun.1))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (O O' : Set ℂ)
    (hO : SupercriticalLQGUniqueness.B2.Iface.IsRationalCircle O)
    (hO' : SupercriticalLQGUniqueness.B2.Iface.IsRationalCircle O')
    (hDfinite : ∀ᵐ ω ∂P,
      SupercriticalLQGUniqueness.B2.Iface.setDistance (D (h ω)).1 O O' < ⊤)
    (hLFPPfinite : ∀ n ω,
      SupercriticalLQGUniqueness.B2.Iface.setDistance
        (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
          (ξ : ℝ) (m (ε n)) (X (ε n) ω)).1 O O' < ⊤) :
    TendstoInMeasure P
        (fun n ω => SupercriticalLQGUniqueness.B2.Iface.setDistance
          (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
            (ξ : ℝ) (m (ε n)) (X (ε n) ω)).1 O O')
        atTop
        (fun ω => SupercriticalLQGUniqueness.B2.Iface.setDistance (D (h ω)).1 O O') := by
  classical
  have hhBdd : LQGMetric.IsGFFPlusBddCont h P :=
    LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1
  have hDconv' := hDconv m hm P h hhBdd X hX
  have hpfe : SupercriticalLQGUniqueness.B2.Iface.PfeThm17 :=
    SupercriticalLQGUniqueness.B2.Final.iface_pfeThm17_of_3bnew
      SupercriticalLQGUniqueness.B2.Final.dg20Interfaces_proved
      ⟨SupercriticalLQGUniqueness.B2.PfeAxioms.s2IdentificationSite_proved,
        SupercriticalLQGUniqueness.B2.PfeLocal.s2LocalitySite_proved⟩
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    SupercriticalLQGUniqueness.B2.Iface.setDistance
      (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
        (ξ : ℝ) (m (ε n)) (X (ε n) ω)).1 O O'
  let g : Ω → ℝ≥0∞ := fun ω =>
    SupercriticalLQGUniqueness.B2.Iface.setDistance (D (h ω)).1 O O'
  have hf : ∀ n, AEStronglyMeasurable (f n) P := by
    intro n
    have hXae : AEMeasurable (X (ε n)) P :=
      SupercriticalLQGUniqueness.B2.PfeAxioms.aemeasurable_heat_smoothing_version
        P h hh (ε n) (X (ε n)) (hX (ε n))
    have hmetric : Measurable fun φ : C(ℂ, ℝ) =>
        SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
          (ξ : ℝ) (m (ε n)) φ :=
      SupercriticalLQGUniqueness.B2.PfeAxioms.measurable_normalizedLFPPMetric_comp
        (ξ : ℝ) (m (ε n)) (fun z => (continuous_eval_const z).measurable)
    have hset : Measurable fun M : SupercriticalLQGUniqueness.LSCMetric =>
        SupercriticalLQGUniqueness.B2.Iface.setDistance M.1 O O' :=
      SupercriticalLQGUniqueness.B2.PfeLocal.l4_measurable_setDistance
        (SupercriticalLQGUniqueness.B2.PfeLocal.l4_isCompact_rationalCircle hO)
        (SupercriticalLQGUniqueness.B2.PfeLocal.l4_isCompact_rationalCircle hO')
    change AEStronglyMeasurable
      (fun ω => SupercriticalLQGUniqueness.B2.Iface.setDistance
        (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
          (ξ : ℝ) (m (ε n)) (X (ε n) ω)).1 O O') P
    exact ((hset.comp_aemeasurable (hmetric.comp_aemeasurable hXae)).aestronglyMeasurable)
  let fr : ℕ → Ω → ℝ≥0 := fun n ω => (f n ω).toNNReal
  let gr : Ω → ℝ≥0 := fun ω => (g ω).toNNReal
  have hfr : ∀ n, AEStronglyMeasurable (fr n) P := by
    intro n
    have ht : Measurable fun x : ℝ≥0∞ => x.toNNReal := by measurability
    exact ((ht.comp_aemeasurable (hf n).aemeasurable).aestronglyMeasurable)
  have hGfinite : ∀ᵐ ω ∂P, g ω ≠ ∞ := by
    filter_upwards [hDfinite] with ω hω
    exact ne_of_lt hω
  have hlimSubseq : ∀ ns : ℕ → ℕ, StrictMono ns →
      ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ ω ∂P, Tendsto (fun k => fr (ns (ns' k)) ω) atTop (𝓝 (gr ω)) := by
    intro ns hns
    let ε' : ℕ → Set.Ioi (0 : ℝ) := ε ∘ ns
    have hε' : Tendsto (fun n => (ε' n : ℝ)) atTop (𝓝 0) :=
      hε.comp hns.tendsto_atTop
    obtain ⟨φ, hφ, D', c, hD'weak, hsub, hratio⟩ := hpfe ξ m hm ε' hε'
    have hε'' : Tendsto (fun n => ((ε' ∘ φ) n : ℝ)) atTop (𝓝 0) :=
      hε'.comp hφ.tendsto_atTop
    obtain ⟨ψ, hψ, hDsub⟩ := hDconv' (ε' ∘ φ) hε''
    have hPfeSub := hsub P h hhBdd X hX
    have hPfeLsc : ∀ᵐ ω ∂P,
        SupercriticalLQGUniqueness.LSCTendsto
          (fun k => SupercriticalLQGUniqueness.rescaledLFPP (ξ : ℝ)
            (m ((ε' ∘ φ) k)) (X ((ε' ∘ φ) k) ω))
          (D' (h ω)).toLSCFun.1 := hPfeSub.1
    have hCanLsc : ∀ᵐ ω ∂P,
        SupercriticalLQGUniqueness.LSCTendsto
          (fun k => SupercriticalLQGUniqueness.rescaledLFPP (ξ : ℝ)
            (m ((ε' ∘ φ) (ψ k))) (X ((ε' ∘ φ) (ψ k)) ω))
          (D (h ω)).toLSCFun.1 := hDsub
    have hPfeLsc' : ∀ᵐ ω ∂P,
        SupercriticalLQGUniqueness.LSCTendsto
          (fun k => SupercriticalLQGUniqueness.rescaledLFPP (ξ : ℝ)
            (m ((ε' ∘ φ) (ψ k))) (X ((ε' ∘ φ) (ψ k)) ω))
          (D' (h ω)).toLSCFun.1 := by
      filter_upwards [hPfeLsc] with ω hω
      exact hω.comp_strictMono hψ
    have hPfeCirc : ∀ᵐ ω ∂P,
        Tendsto (fun k => SupercriticalLQGUniqueness.B2.Iface.setDistance
          (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
            (ξ : ℝ) (m (ε' (φ (ψ k)))) (X (ε' (φ (ψ k))) ω)).1 O O') atTop
          (𝓝 (SupercriticalLQGUniqueness.B2.Iface.setDistance (D' (h ω)).1 O O')) := by
      filter_upwards [hPfeSub.2 O O' hO hO'] with ω hω
      convert hω.comp hψ.tendsto_atTop using 1
      ext k
      simp only [Function.comp_apply,
        SupercriticalLQGUniqueness.B2.PfeAxioms.setDistance_normalizedLFPPMetric]
    have hTargetEq : ∀ᵐ ω ∂P, g ω =
        SupercriticalLQGUniqueness.B2.Iface.setDistance (D' (h ω)).1 O O' := by
      filter_upwards [hCanLsc, hPfeLsc'] with ω hcan hpfe
      have heq := SupercriticalLQGUniqueness.B2.DG20Lim.lscTendsto_unique hpfe hcan
      have hmetricEq : D' (h ω) = D (h ω) := by
        apply Subtype.ext
        funext p
        apply EReal.coe_ennreal_injective
        exact congrFun heq p
      exact (congrArg (fun M : SupercriticalLQGUniqueness.LSCMetric =>
        SupercriticalLQGUniqueness.B2.Iface.setDistance M.1 O O') hmetricEq).symm
    have hlimENN : ∀ᵐ ω ∂P,
        Tendsto (fun k => f (ns (φ (ψ k))) ω) atTop (𝓝 (g ω)) := by
      filter_upwards [hPfeCirc, hTargetEq] with ω hω heq
      simpa only [f, ε', Function.comp_apply, heq] using hω
    have hlimNN : ∀ᵐ ω ∂P,
        Tendsto (fun k => fr (ns (φ (ψ k))) ω) atTop (𝓝 (gr ω)) := by
      filter_upwards [hlimENN, hGfinite] with ω hω hgω
      have hseqfinite : ∀ k, f (ns (φ (ψ k))) ω ≠ ∞ := by
        intro k
        exact ne_of_lt (hLFPPfinite (ns (φ (ψ k))) ω)
      have hω' : Tendsto (fun k => f (ns (φ (ψ k))) ω) atTop
          (𝓝 ((gr ω : ℝ≥0) : ℝ≥0∞)) := by
        rw [ENNReal.coe_toNNReal hgω]
        exact hω
      exact (ENNReal.tendsto_toNNReal_iff' hseqfinite).2 hω'
    exact ⟨φ ∘ ψ, hφ.comp hψ, hlimNN⟩
  have hNN : TendstoInMeasure P fr atTop gr :=
    (MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff
      (μ := P) (f := fr) (g := gr) hfr).2 hlimSubseq
  have hfinite : ∀ n ω, f n ω ≠ ∞ := by
    intro n ω
    exact ne_of_lt (hLFPPfinite n ω)
  exact tendstoInMeasure_ennreal_of_toNNReal f g hfinite hGfinite hNN

/-- The canonical strong-LQG metric is chosen once, before the normalizer, field, heat version,
cutoff sequence, and circles. Its frozen `LSCTendstoInProbability` property identifies the
canonical limit; the proved Pfeffer `PfeThm17` result supplies circle-distance convergence along
extracted subsequences. -/
theorem rationalCircleDistance_tendstoInMeasure_seq
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q) :
    ∃ D : DistC → SupercriticalLQGUniqueness.LSCMetric,
      IsStrongLQGMetric ξ Q D ∧
      ∀ (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)),
        (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
        (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)),
        (∀ ε, IsHeatSmoothing P h ε (X ε)) →
      ∀ (ε : ℕ → Set.Ioi (0 : ℝ)),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
      ∀ (q₁ q₂ : ℚ × ℚ) (r₁ r₂ : ℚ), 0 < r₁ → 0 < r₂ →
        TendstoInMeasure P
          (fun n ω => SupercriticalLQGUniqueness.B2.Iface.setDistance
            (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
              (ξ : ℝ) (m (ε n)) (X (ε n) ω)).1
            (rationalCircle q₁ r₁) (rationalCircle q₂ r₂))
          atTop
          (fun ω => SupercriticalLQGUniqueness.B2.Iface.setDistance (D (h ω)).1
            (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)) := by
  obtain ⟨D, hD, hDconv⟩ :=
    SupercriticalLQGUniqueness.exists_strongLQGMetric_lfppLimit ξ Q hQ
  refine ⟨D, hD, ?_⟩
  intro m hm Ω _ P _ h hh X hX ε hε q₁ q₂ r₁ r₂ hr₁ hr₂
  let O := rationalCircle q₁ r₁
  let O' := rationalCircle q₂ r₂
  have hO : SupercriticalLQGUniqueness.B2.Iface.IsRationalCircle O :=
    rationalCircle_isRationalCircle q₁ r₁ hr₁
  have hO' : SupercriticalLQGUniqueness.B2.Iface.IsRationalCircle O' :=
    rationalCircle_isRationalCircle q₂ r₂ hr₂
  have hDfinite := ae_rationalCircleDistance_lt_top hD P h hh q₁ q₂ r₁ r₂ hr₁ hr₂
  have hLFPPfinite : ∀ n ω,
      SupercriticalLQGUniqueness.B2.Iface.setDistance
        (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
          (ξ : ℝ) (m (ε n)) (X (ε n) ω)).1 O O' < ⊤ := by
    intro n ω
    exact setDistance_normalizedLFPPMetric_lt_top (ξ : ℝ) (m (ε n))
      (X (ε n) ω) hO hO'
  exact rationalCircleDistance_tendstoInMeasure_seq_of_limit hQ D hD hDconv
    m hm P h hh X hX ε hε O O' hO hO' hDfinite hLFPPfinite

/-- The normalized LFPP distance between positive-radius rational circles converges in
probability as the positive cutoff tends to zero, to the distance of the single canonical
strong-LQG limit metric. -/
theorem rationalCircleDistance_tendstoInMeasure
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q) :
    ∃ D : DistC → SupercriticalLQGUniqueness.LSCMetric,
      IsStrongLQGMetric ξ Q D ∧
      ∀ (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)),
        (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
        (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)),
        (∀ ε, IsHeatSmoothing P h ε (X ε)) →
      ∀ (q₁ q₂ : ℚ × ℚ) (r₁ r₂ : ℚ), 0 < r₁ → 0 < r₂ →
        TendstoInMeasure P
          (fun a ω => SupercriticalLQGUniqueness.B2.Iface.setDistance
            (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
              (ξ : ℝ) (m a) (X a ω)).1
            (rationalCircle q₁ r₁) (rationalCircle q₂ r₂))
          (comap Subtype.val (𝓝 (0 : ℝ)))
          (fun ω => SupercriticalLQGUniqueness.B2.Iface.setDistance (D (h ω)).1
            (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)) := by
  obtain ⟨D, hD, hseq⟩ := rationalCircleDistance_tendstoInMeasure_seq hQ
  refine ⟨D, hD, ?_⟩
  intro m hm Ω _ P hP h hh X hX q₁ q₂ r₁ r₂ hr₁ hr₂
  let f : Set.Ioi (0 : ℝ) → Ω → ℝ≥0 := fun a ω =>
    (SupercriticalLQGUniqueness.B2.Iface.setDistance
      (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
        (ξ : ℝ) (m a) (X a ω)).1 (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)).toNNReal
  let g : Ω → ℝ≥0 := fun ω =>
    (SupercriticalLQGUniqueness.B2.Iface.setDistance (D (h ω)).1
      (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)).toNNReal
  have hf : ∀ a ω,
      SupercriticalLQGUniqueness.B2.Iface.setDistance
        (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
          (ξ : ℝ) (m a) (X a ω)).1 (rationalCircle q₁ r₁) (rationalCircle q₂ r₂) ≠ ∞ := by
    intro a ω
    have hO : SupercriticalLQGUniqueness.B2.Iface.IsRationalCircle (rationalCircle q₁ r₁) :=
      rationalCircle_isRationalCircle q₁ r₁ hr₁
    have hO' : SupercriticalLQGUniqueness.B2.Iface.IsRationalCircle (rationalCircle q₂ r₂) :=
      rationalCircle_isRationalCircle q₂ r₂ hr₂
    exact ne_of_lt (setDistance_normalizedLFPPMetric_lt_top (ξ : ℝ) (m a) (X a ω) hO hO')
  have hg : ∀ᵐ ω ∂P,
      SupercriticalLQGUniqueness.B2.Iface.setDistance (D (h ω)).1
        (rationalCircle q₁ r₁) (rationalCircle q₂ r₂) ≠ ∞ := by
    filter_upwards [ae_rationalCircleDistance_lt_top hD P h hh q₁ q₂ r₁ r₂ hr₁ hr₂]
      with ω hω
    exact ne_of_lt hω
  have hseqNN : ∀ e : ℕ → Set.Ioi (0 : ℝ),
      Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0) →
      TendstoInMeasure P (fun n ω => f (e n) ω) atTop g := by
    intro e he
    have hENN := hseq m hm P h hh X hX e he q₁ q₂ r₁ r₂ hr₁ hr₂
    exact tendstoInMeasure_toNNReal_of_ennreal
      (fun n ω => SupercriticalLQGUniqueness.B2.Iface.setDistance
        (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
          (ξ : ℝ) (m (e n)) (X (e n) ω)).1
        (rationalCircle q₁ r₁) (rationalCircle q₂ r₂))
      (fun ω => SupercriticalLQGUniqueness.B2.Iface.setDistance (D (h ω)).1
        (rationalCircle q₁ r₁) (rationalCircle q₂ r₂))
      (by intro n ω; exact hf (e n) ω) hg hENN
  have hNN : TendstoInMeasure P f (comap Subtype.val (𝓝 (0 : ℝ))) g :=
    tendstoInMeasure_positiveCutoff_of_seq P hseqNN
  exact tendstoInMeasure_ennreal_of_toNNReal
    (fun a ω => SupercriticalLQGUniqueness.B2.Iface.setDistance
      (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric
        (ξ : ℝ) (m a) (X a ω)).1 (rationalCircle q₁ r₁) (rationalCircle q₂ r₂))
    (fun ω => SupercriticalLQGUniqueness.B2.Iface.setDistance (D (h ω)).1
      (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)) hf hg hNN

end SupercriticalLFPPAS
