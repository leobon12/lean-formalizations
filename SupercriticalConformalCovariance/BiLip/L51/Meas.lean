import SupercriticalConformalCovariance.BiLip.L51.Data
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection

/-!
# Lemma 5.1: universal measurability of the event set

On `DistC × DistC` (the source field and the target whole-plane field), consider
* `Bset`, the literal good event `∃ c, h_r(z) = c ∧ Good(D_g, ehat(G), c)`;
* `Bset'`, the same with the internal barrier `S` replaced by the ambient set distance `D(M, ∂A)` in G2
  and (9).

`mem_Bset_iff`: `Bset` and `Bset'` agree whenever `barrier = setDist` (true on the sample event, first exit).
`um_Bset'`: `Bset'` is universally measurable. It is the intersection of the following pieces.
* The Borel existence of the circle average.
* G1, over internal codes and dyadic scale by scale (`G1n_iff_code`, `Bad1`): co-analytic.
* G3, which is DG's E3 (`G3_iff_eventClause3`, `E3set_um`): co-analytic.
* G4 (Borel).
* `∀ c, CA → G2(c)`, which is DG's E2 with `C₋ = 2k`, `C₊ = 1` (`E2all_um`).
* `∀ c, CA → G5(c)`: co-analytic, with the Borel bad-witness set `Bad5'` of
  `(c, code, u, v) ∈ ℝ × Path × ℂ × ℂ` (regular pairs via `sourceRegularPair_iff_code`,
  `failureWitness_borel`; `ehat` via `measurable_ehat`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip.L51

open SupercriticalLQGUniqueness (LSCMetric EuclideanAnnulus aroundDist acrossDist IsCircleAverage)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events (eventCarrier eventMiddle eventBoundary
  InternalBoundaryGeodesic spherePairInf EventClause3)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36 (IsIntCode PathCode codeExt codeExt_zero
  codeExt_one codeExt_of_mem intGeod_of_intCode exists_intCode_of_intGeod ibg_iff annulus_eq_mk
  isCompact_eventCarrier Bad1 measurableSet_bad1 E3set_um measurableSet_E4 E2all_um E2Prop E4Prop
  measurableSet_exists_circleAverage measurable_setDist_middle measurableSet_isCircleAverage_rel)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated (aroundRat)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)
open LQGMetric (DistC)

/-! ## G1, scale by scale -/

/-- G1 at the dyadic scale `δ = 2^{-n}` -/
def G1n (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) (θ : Ioi (0 : ℝ)) (n : ℕ) : Prop :=
  ∀ (P : ℝ → ℂ) (s t : ℝ), InternalBoundaryGeodesic D z r P s t →
    ∀ x ∈ eventMiddle z r, (∃ v ∈ Icc s t, P v ∈ ball x (((1 / 2 : ℝ) ^ n) * r)) →
      ∃ A : EuclideanAnnulus, A.center = x ∧ A.innerRadius = ((1 / 2 : ℝ) ^ n) * r ∧
        A.outerRadius = Real.sqrt ((1 / 2 : ℝ) ^ n) * r ∧
        aroundDist D A ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ (θ : ℝ)) * acrossDist D A

theorem G1_iff (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (θ : Ioi (0 : ℝ)) :
    SupercriticalConformalCovariance.GoodAnnulus.G1 D z r q θ ↔ ∀ n : ℕ, (1 / 2 : ℝ) ^ n ≤ q → G1n D z r θ n :=
  ⟨fun h n hn P s t hP x hx hhit => h P s t hP n hn x hx hhit,
    fun h P s t hP n hn x hx hhit => h n hn P s t hP x hx hhit⟩

/-- G1 at one scale over internal codes -/
def G1nCode (D : LSCMetric) (z : ℂ) (r δ θ : ℝ) : Prop :=
  ∀ (γ : PathCode) (x : ℂ), IsIntCode D (eventCarrier z r) γ →
    γ 0 ∈ eventBoundary z r → γ 1 ∈ eventBoundary z r → x ∈ eventMiddle z r →
    (∃ τ, γ τ ∈ ball x (δ * r)) →
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.aroundAt D x (δ * r)
        (Real.sqrt δ * r) ≤ ENNReal.ofReal (δ ^ θ) * spherePairInf D x (δ * r) (Real.sqrt δ * r)

theorem G1n_iff_code (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) (θ : Ioi (0 : ℝ)) (n : ℕ)
    (hδ1 : (1 / 2 : ℝ) ^ n < 1) :
    G1n D z r θ n ↔ G1nCode D z r ((1 / 2 : ℝ) ^ n) θ := by
  have hr : (0 : ℝ) < r := r.2
  have hY := isCompact_eventCarrier z r
  have hδ0 : (0 : ℝ) < (1 / 2) ^ n := pow_pos (by norm_num) n
  have hvalid := SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.loop_annulus_valid
    hr hδ0 hδ1
  constructor
  · intro hE γ x hγ hγ0 hγ1 hx hhit
    obtain ⟨τ, hτ⟩ := hhit
    have hP := intGeod_of_intCode hγ
    have hibg : InternalBoundaryGeodesic D z r (codeExt γ) 0 1 := by
      refine (ibg_iff D z r _ 0 1).mpr ⟨hP, ?_, ?_⟩
      · rw [codeExt_zero]; exact hγ0
      · rw [codeExt_one]; exact hγ1
    have hhit' : ∃ v ∈ Icc (0 : ℝ) 1, codeExt γ v ∈ ball x (((1 / 2 : ℝ) ^ n) * r) :=
      ⟨τ, τ.2, by rw [codeExt_of_mem γ τ.2]; exact hτ⟩
    obtain ⟨A, hc, hi, ho, hA⟩ := hE (codeExt γ) 0 1 hibg x hx hhit'
    have hAeq : A = ⟨(x, ((1 / 2 : ℝ) ^ n * r, Real.sqrt ((1 / 2 : ℝ) ^ n) * r)), hvalid⟩ :=
      annulus_eq_mk hc hi ho hvalid
    rw [SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.aroundAt_eq D x _ _ hvalid]
    subst hAeq
    exact hA
  · intro hC P s t hibg x hx hhit
    obtain ⟨v, hv, hvx⟩ := hhit
    obtain ⟨hP, hs, ht⟩ := (ibg_iff D z r P s t).mp hibg
    obtain ⟨γ, hγ, hγ0, hγ1, -, hseg⟩ := exists_intCode_of_intGeod hY hP
    obtain ⟨σ, -, -, hσ, -, -⟩ := hseg v hv v hv le_rfl
    have hγ0F : γ 0 ∈ eventBoundary z r := by rw [hγ0]; exact hs
    have hγ1F : γ 1 ∈ eventBoundary z r := by rw [hγ1]; exact ht
    have h := hC γ x hγ hγ0F hγ1F hx ⟨σ, by rw [hσ]; exact hvx⟩
    refine ⟨⟨(x, ((1 / 2 : ℝ) ^ n * r, Real.sqrt ((1 / 2 : ℝ) ^ n) * r)), hvalid⟩, rfl, rfl, rfl, ?_⟩
    rw [SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.aroundAt_eq D x _ _ hvalid] at h
    exact h

/-- one dyadic scale of G1 is co-analytic -/
theorem G1n_um {D : DistC → LSCMetric} (hD : Measurable D) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (θ : Ioi (0 : ℝ)) (n : ℕ) (hn : (1 / 2 : ℝ) ^ n ≤ q) :
    LQGMetric.UMeasurableSet {g : DistC | G1n (D g) z r θ n} := by
  have hq1 : (q : ℝ) < 1 / 100 := q.2.2
  have hδ0 : (0 : ℝ) < (1 / 2) ^ n := pow_pos (by norm_num) n
  have hδ1 : (1 / 2 : ℝ) ^ n < 1 := by linarith
  set δ : ℝ := (1 / 2 : ℝ) ^ n with hδdef
  set S : Set (DistC × (PathCode × ℂ)) :=
    (fun p : DistC × (PathCode × ℂ) => (p.1, (p.2.1, δ, p.2.2))) ⁻¹'
      (Bad1 D z r q θ)ᶜ with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_bad1 hD z r q θ).compl.preimage
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_const.prodMk (measurable_snd.comp measurable_snd))))
  have heq : {g : DistC | G1n (D g) z r θ n} = {g | ∀ w : PathCode × ℂ, (g, w) ∈ S} := by
    ext g
    simp only [mem_setOf_eq]
    rw [G1n_iff_code (D g) z r θ n hδ1]
    constructor
    · rintro h ⟨γ, x⟩ ⟨hγ, h0, h1, -, -, hx, hhit, hlt⟩
      exact (not_lt_of_ge (h γ x hγ h0 h1 hx hhit)) hlt
    · intro h γ x hγ h0 h1 hx hhit
      by_contra hn'
      exact h (γ, x) ⟨hγ, h0, h1, hδ0, hn, hx, hhit, lt_of_not_ge hn'⟩
  rw [heq]
  exact LQGMetric.UMeasurableSet.setOf_forall hS

/-- G1 is co-analytic -/
theorem G1_um {D : DistC → LSCMetric} (hD : Measurable D) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (θ : Ioi (0 : ℝ)) :
    LQGMetric.UMeasurableSet {g : DistC | SupercriticalConformalCovariance.GoodAnnulus.G1 (D g) z r q θ} := by
  have heq : {g : DistC | SupercriticalConformalCovariance.GoodAnnulus.G1 (D g) z r q θ} =
      ⋂ n : ℕ, {g : DistC | (1 / 2 : ℝ) ^ n ≤ q → G1n (D g) z r θ n} := by
    ext g; simp only [mem_setOf_eq, mem_iInter, G1_iff]
  rw [heq]
  refine LQGMetric.UMeasurableSet.iInter fun n => ?_
  by_cases hn : (1 / 2 : ℝ) ^ n ≤ q
  · have e : {g : DistC | (1 / 2 : ℝ) ^ n ≤ q → G1n (D g) z r θ n} = {g | G1n (D g) z r θ n} := by
      ext g; simp only [mem_setOf_eq, hn, true_implies]
    rw [e]; exact G1n_um hD z r q θ n hn
  · have e : {g : DistC | (1 / 2 : ℝ) ^ n ≤ q → G1n (D g) z r θ n} = univ := by
      ext g; simp only [mem_setOf_eq, hn, false_implies, mem_univ]
    rw [e]; exact LQGMetric.UMeasurableSet.univ

/-! ## G3 is DG's E3 -/

theorem G3_iff_eventClause3 (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) :
    SupercriticalConformalCovariance.GoodAnnulus.G3 D z r q a ↔ EventClause3 D z r q a := by
  have hqr : (0 : ℝ) ≤ q * r := (mul_pos q.2.1 r.2).le
  constructor
  · intro h P s t hibg v w hv0 hvw hv hw hseg
    have hd := h P s t hibg v w hv0 hv.1 hw.2 hseg
    have hb : Bornology.IsBounded (P '' Icc v w) :=
      isBounded_closedBall.subset (fun y ⟨u, hu, hy⟩ => hy ▸ (hseg u hu).1)
    exact (dist_le_diam_of_mem hb ⟨v, ⟨le_rfl, hvw.le⟩, rfl⟩ ⟨w, ⟨hvw.le, le_rfl⟩, rfl⟩).trans hd
  · intro h P σ τ hP s t hs hσs htτ hseg
    refine Metric.diam_le_of_forall_dist_le hqr ?_
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    have key : ∀ {v w : ℝ}, v ∈ Icc s t → w ∈ Icc s t → v ≤ w → dist (P v) (P w) ≤ q * r := by
      intro v w hv hw hvw
      rcases hvw.lt_or_eq with hlt | heq
      · exact h P σ τ hP v w (hs.trans_le hv.1) hlt ⟨hσs.trans hv.1, hv.2.trans htτ⟩
          ⟨hσs.trans hw.1, hw.2.trans htτ⟩
          (fun u hu => hseg u ⟨hv.1.trans hu.1, hu.2.trans hw.2⟩)
      · rw [heq, dist_self]; exact hqr
    rcases le_total v w with hvw | hwv
    · exact key hv hw hvw
    · rw [dist_comm]; exact key hw hv hwv

/-! ## Regular pairs: Borel codes -/

section Regular

open SupercriticalConformalCovariance.Regular (DyadicallyRegular FailureWitness Input Witness)

theorem dyadicallyRegular_set_eq (z : ℂ) (r α θ m : ℝ) :
    {p : Input | DyadicallyRegular z r α θ m p} =
      {p : Input | FailureWitness z r α θ m ((1 - α)⁻¹ * m) 0 (-1) p} := by
  ext p
  simp only [mem_setOf_eq, FailureWitness]
  constructor
  · intro h
    refine ⟨h, h.2.2.2.2.1, dist_nonneg, ?_⟩
    norm_num
  · exact fun h => h.1

theorem measurableSet_dyadicallyRegular (z : ℂ) (r α θ m : ℝ) :
    MeasurableSet {p : Input | DyadicallyRegular z r α θ m p} := by
  rw [dyadicallyRegular_set_eq]
  exact SupercriticalConformalCovariance.Regular.failureWitness_borel z r α θ m _ 0 (-1)

/-- the normalizer clause of (7) separates from the rest of `DyadicallyRegular` -/
theorem dyadicallyRegular_iff (z : ℂ) (r α θ m : ℝ) (hα : α < 1) (p : Input) :
    DyadicallyRegular z r α θ m p ↔
      (∃ N : ℕ, DyadicallyRegular z r α θ N p) ∧ p.1.1 p.2.2 ≤ ENNReal.ofReal ((1 - α)⁻¹ * m) := by
  have hα' : 0 ≤ (1 - α)⁻¹ := inv_nonneg.2 (by linarith)
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨⌈m⌉₊, h0, h1, h2, h3, h4.trans ?_, h5, h6⟩, h4⟩
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Nat.le_ceil m) hα')
  · rintro ⟨⟨N, h0, h1, h2, h3, -, h5, h6⟩, h4⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

end Regular

/-! ## The event sets -/

section Sets

variable (D : DistC → LSCMetric) (Y : Set ℂ) (φ : ℂ → ℂ) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
  (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ))
  (k η : ℝ)

/-- the literal good event, on (source field, target whole-plane field) -/
def Bset : Set (DistC × DistC) :=
  {x | ∃ c, IsCircleAverage x.1 r z c ∧
    SupercriticalConformalCovariance.Improve.Good (D x.1) (ehat D Y φ x.2) ξ Q z r q a K θ k c η}

/-- (G5) with the ambient middle-to-boundary distance in (9) -/
def G5s (Dm : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞) (c : ℝ) : Prop :=
  ∀ u v : ℂ,
    SupercriticalConformalCovariance.Regular.SourceRegularPair Dm z u v r a θ ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)) →
    dist u v ≤ (q : ℝ) * r →
    aroundRat (Dm, (v, (q : ℝ) * r, Real.sqrt (q : ℝ) * r)) ≤
      ENNReal.ofReal k * setDist Dm (eventMiddle z r) (eventBoundary z r) →
    e (u, v) ≤ ENNReal.ofReal (1 + η) * Dm (u, v)

/-- the event with the ambient middle-to-boundary distance -/
def Bset' : Set (DistC × DistC) :=
  {x | ∃ c, IsCircleAverage x.1 r z c ∧
    SupercriticalConformalCovariance.GoodAnnulus.G1 (D x.1) z r q θ ∧ E2Prop (D x.1) ξ Q z r q a θ (2 * k) 1 c ∧
    SupercriticalConformalCovariance.GoodAnnulus.G3 (D x.1) z r q a ∧ E4Prop (D x.1) z r a K ∧
    G5s ξ Q z r q a θ k η (D x.1) (ehat D Y φ x.2) c}

theorem e2Prop_iff (Dm : LSCMetric) (c : ℝ) :
    E2Prop Dm ξ Q z r q a θ (2 * k) 1 c ↔
      aroundDist Dm (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.outerAnn z r) ≤
        min (ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)))
          (ENNReal.ofReal (k * (q : ℝ) ^ (-(θ : ℝ))) *
            setDist Dm (eventMiddle z r) (eventBoundary z r)) := by
  unfold E2Prop
  rw [show 2 * k / (2 * 1) = k by ring]

/-- `Bset` and `Bset'` agree where the barrier is the ambient set distance -/
theorem mem_Bset_iff (x : DistC × DistC)
    (hbar : SupercriticalConformalCovariance.GoodAnnulus.barrier (D x.1) z r =
      setDist (D x.1) (eventMiddle z r) (eventBoundary z r)) :
    x ∈ Bset D Y φ ξ Q z r q a K θ k η ↔ x ∈ Bset' D Y φ ξ Q z r q a K θ k η := by
  simp only [Bset, Bset', mem_setOf_eq, SupercriticalConformalCovariance.Improve.Good, SupercriticalConformalCovariance.GoodAnnulus.LiteralGood,
    SupercriticalConformalCovariance.GoodAnnulus.G4, e2Prop_iff, SupercriticalConformalCovariance.GoodAnnulus.G2, hbar, SupercriticalConformalCovariance.Improve.G5, G5s, and_assoc]

/-- the bad witnesses `(c, code, u, v)` of `∀ c, CA → G5(c)` -/
def Bad5' : Set ((DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness)) :=
  {p | IsCircleAverage p.1.1 r z p.2.1 ∧
    (∃ N : ℕ, SupercriticalConformalCovariance.Regular.DyadicallyRegular z r a θ N ((D p.1.1, D p.1.1), p.2.2)) ∧
    D p.1.1 (p.2.2.2.1, p.2.2.2.2) ≤
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * p.2.1))) ∧
    dist p.2.2.2.1 p.2.2.2.2 ≤ (q : ℝ) * r ∧
    aroundRat (D p.1.1, (p.2.2.2.2, (q : ℝ) * r, Real.sqrt (q : ℝ) * r)) ≤
      ENNReal.ofReal k * setDist (D p.1.1) (eventMiddle z r) (eventBoundary z r) ∧
    ENNReal.ofReal (1 + η) * D p.1.1 (p.2.2.2.1, p.2.2.2.2) <
      ehat D Y φ p.1.2 (p.2.2.2.1, p.2.2.2.2)}

theorem measurableSet_bad5' (hD : Measurable D) (hY : IsCompact Y) (hφ : ContinuousOn φ Y) :
    MeasurableSet (Bad5' D Y φ ξ Q z r q a θ k η) := by
  have hg : Measurable fun p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hDg : Measurable fun p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) => D p.1.1 := hD.comp hg
  have hc : Measurable fun p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) => p.2.1 :=
    measurable_fst.comp measurable_snd
  have hw : Measurable fun p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) => p.2.2 :=
    measurable_snd.comp measurable_snd
  have hu : Measurable fun p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) => p.2.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp hw)
  have hv : Measurable fun p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) => p.2.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp hw)
  have hDuv : Measurable fun p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) =>
      D p.1.1 (p.2.2.2.1, p.2.2.2.2) :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.jointEval_lsc.measurable.comp
      (hDg.prodMk (hu.prodMk hv))
  have h0 : MeasurableSet {p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) |
      IsCircleAverage p.1.1 r z p.2.1} := by
    have := measurableSet_isCircleAverage_rel (β := ℝ) r z (c := fun t : ℝ => t) measurable_id
    exact this.preimage (hg.prodMk hc)
  have h1 : MeasurableSet {p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) |
      ∃ N : ℕ, SupercriticalConformalCovariance.Regular.DyadicallyRegular z r a θ N ((D p.1.1, D p.1.1), p.2.2)} := by
    have e : {p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) |
        ∃ N : ℕ, SupercriticalConformalCovariance.Regular.DyadicallyRegular z r a θ N ((D p.1.1, D p.1.1), p.2.2)} =
        ⋃ N : ℕ, (fun p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) =>
          (((D p.1.1, D p.1.1), p.2.2) : SupercriticalConformalCovariance.Regular.Input)) ⁻¹'
            {i | SupercriticalConformalCovariance.Regular.DyadicallyRegular z r a θ N i} := by
      ext p; simp only [mem_setOf_eq, mem_iUnion, mem_preimage]
    rw [e]
    exact MeasurableSet.iUnion fun N =>
      (measurableSet_dyadicallyRegular z r a θ N).preimage ((hDg.prodMk hDg).prodMk hw)
  have h2 : MeasurableSet {p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) |
      D p.1.1 (p.2.2.2.1, p.2.2.2.2) ≤
        ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * p.2.1)))} :=
    measurableSet_le hDuv (measurable_const.mul (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul hc)))).ennreal_ofReal
  have h3 : MeasurableSet {p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) |
      dist p.2.2.2.1 p.2.2.2.2 ≤ (q : ℝ) * r} :=
    measurableSet_le (hu.dist hv) measurable_const
  have h4 : MeasurableSet {p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) |
      aroundRat (D p.1.1, (p.2.2.2.2, (q : ℝ) * r, Real.sqrt (q : ℝ) * r)) ≤
        ENNReal.ofReal k * setDist (D p.1.1) (eventMiddle z r) (eventBoundary z r)} :=
    measurableSet_le
      (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.measurable_aroundRat.comp
        (hDg.prodMk (hv.prodMk measurable_const)))
      (measurable_const.mul ((measurable_setDist_middle z r.2).comp hDg))
  have h5 : MeasurableSet {p : (DistC × DistC) × (ℝ × SupercriticalConformalCovariance.Regular.Witness) |
      ENNReal.ofReal (1 + η) * D p.1.1 (p.2.2.2.1, p.2.2.2.2) <
        ehat D Y φ p.1.2 (p.2.2.2.1, p.2.2.2.2)} :=
    measurableSet_lt (measurable_const.mul hDuv)
      ((measurable_ehat hD hY hφ).comp ((measurable_snd.comp measurable_fst).prodMk (hu.prodMk hv)))
  exact h0.inter (h1.inter (h2.inter (h3.inter (h4.inter h5))))

theorem G5all_eq (hα : (a : ℝ) < 1) :
    {x : DistC × DistC | ∀ c, IsCircleAverage x.1 r z c →
      G5s ξ Q z r q a θ k η (D x.1) (ehat D Y φ x.2) c} =
    {x | ∀ w : ℝ × SupercriticalConformalCovariance.Regular.Witness, (x, w) ∈ (Bad5' D Y φ ξ Q z r q a θ k η)ᶜ} := by
  ext x
  simp only [mem_setOf_eq, mem_compl_iff, Bad5', G5s, not_and, not_lt]
  constructor
  · rintro H ⟨c, Q', u, v⟩ hc hN hm huv h9
    exact H c hc u v ((SupercriticalConformalCovariance.Regular.sourceRegularPair_iff_code (D x.1) (D x.1) z u v r a θ _).2
      ⟨Q', (dyadicallyRegular_iff z r a θ _ hα _).2 ⟨hN, hm⟩⟩) huv h9
  · intro H c hc u v hreg huv h9
    obtain ⟨Q', hQ'⟩ := (SupercriticalConformalCovariance.Regular.sourceRegularPair_iff_code (D x.1) (D x.1) z u v r a θ _).1 hreg
    obtain ⟨hN, hm⟩ := (dyadicallyRegular_iff z r a θ _ hα _).1 hQ'
    exact H ⟨c, Q', u, v⟩ hc hN hm huv h9

/-- **The event set with the ambient barrier is universally measurable.** -/
theorem um_Bset' (hD : Measurable D) (hY : IsCompact Y) (hφ : ContinuousOn φ Y) :
    LQGMetric.UMeasurableSet (Bset' D Y φ ξ Q z r q a K θ k η) := by
  have hr : (0 : ℝ) < r := r.2
  have hq0 : (0 : ℝ) < q := q.2.1
  have hα : (a : ℝ) < 1 := a.2.2
  have heq : Bset' D Y φ ξ Q z r q a K θ k η =
      Prod.fst ⁻¹' ({g : DistC | ∃ c, IsCircleAverage g r z c} ∩
          {g | SupercriticalConformalCovariance.GoodAnnulus.G1 (D g) z r q θ} ∩ {g | EventClause3 (D g) z r q a} ∩
          {g | E4Prop (D g) z r a K} ∩
          {g | ∀ c, IsCircleAverage g r z c → E2Prop (D g) ξ Q z r q a θ (2 * k) 1 c}) ∩
        {x : DistC × DistC | ∀ c, IsCircleAverage x.1 r z c →
          G5s ξ Q z r q a θ k η (D x.1) (ehat D Y φ x.2) c} := by
    ext x
    simp only [Bset', mem_setOf_eq, mem_inter_iff, mem_preimage, G3_iff_eventClause3]
    constructor
    · rintro ⟨c, hc, h1, h2, h3, h4, h5⟩
      refine ⟨⟨⟨⟨⟨⟨c, hc⟩, h1⟩, h3⟩, h4⟩, fun c' hc' => ?_⟩, fun c' hc' => ?_⟩
      · rw [← SupercriticalLQGUniqueness.isCircleAverage_unique hc hc']; exact h2
      · rw [← SupercriticalLQGUniqueness.isCircleAverage_unique hc hc']; exact h5
    · rintro ⟨⟨⟨⟨⟨⟨c, hc⟩, h1⟩, h3⟩, h4⟩, h2⟩, h5⟩
      exact ⟨c, hc, h1, h2 c hc, h3, h4, h5 c hc⟩
  rw [heq]
  refine LQGMetric.UMeasurableSet.inter (LQGMetric.UMeasurableSet.preimage ?_ measurable_fst) ?_
  · refine ((((LQGMetric.UMeasurableSet.of_measurableSet
      (measurableSet_exists_circleAverage r z)).inter (G1_um hD z r q θ)).inter
      (E3set_um hD z a hr hq0)).inter
      (LQGMetric.UMeasurableSet.of_measurableSet (measurableSet_E4 hD z r a K))).inter
      (E2all_um hD ξ Q z r q a θ (2 * k) 1)
  · rw [G5all_eq D Y φ ξ Q z r q a θ k η hα]
    exact LQGMetric.UMeasurableSet.setOf_forall (measurableSet_bad5' D Y φ ξ Q z r q a θ k η hD hY hφ).compl

end Sets

end SupercriticalConformalCovariance.BiLip.L51
