import HigherDimLQGContinuity.Events.Profile
import HigherDimLQGContinuity.Witness.Refs
import HigherDimLQGMetric.Events.AnalyticQuant
import HigherDimLQGMetric.Select.MetricBorel

/-!
# Null-measurability of `H↓`, `H↑` and the pair references (packet P5b)

Packet P5b, second module. Source: blueprint Part A, Lemma `a:lem-local`, step (2) of its proof ("the events as
projections"); planning audit NA1, item 20, R4 (alternative M34 route: "take the raw sets: they are projections of Borel
sets of (profiles at rational points) × C([0, 1], K), hence analytic, hence null-measurable for every law"); NA3 N-M17;
the library pattern `amplify_nullMeasurableSet_unitWit` (HDLM `Amplify/UnitWitnessMeas.lean`).

On length metrics the `A`-internal metric is the rational chain formula `ContMetric.chainInf`, which is Borel in
`(G, x, y)` (`ContMetric.measurable_chainInf`). Hence:

* a witness condition is a Borel condition on `(G, γ) ∈ ContMetric d × C([0, 1], ℝ^d)` once its equalities are
  required at rational times only (`p5b_isWitness_iff_witChain`, by continuity of `G(·, ·; A)` along `γ` and the
  finiteness `internal_annA_ne_top`);
* `{q | ∃ γ, …}` is universally measurable (Lusin: `UMeasurableSet.setOf_exists`) for `H↓`, `H↑`;
* the references are universal quantifications of Borel relations over closed sets (`uMeasurableSet_forall_mem`).

`p5b_nullMeasurableSet_hdown`, `p5b_nullMeasurableSet_hup`, `p5b_nullMeasurableSet_pairRefs`: the three events are
null-measurable for every finite law under which `ρ^D_g`, `ρ^E_g` are almost surely length metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Rational times -/

/-- The rational times of `[0, 1]` (projected). -/
def p5bRatTime (a : ℚ) : unitInterval := Set.projIcc 0 1 zero_le_one (a : ℝ)

theorem p5b_denseRange_ratTime : DenseRange p5bRatTime :=
  (Set.projIcc_surjective (zero_le_one' ℝ)).denseRange.comp Rat.denseRange_cast continuous_projIcc

/-! ## Witnesses through the chain formula -/

/-- The witness condition with the `A`-internal metric replaced by the chain formula and the equalities required at
rational times only. -/
def p5bWitChain (G : ContMetric d) (γ : C(unitInterval, Rd d)) : Prop :=
  ‖γ 0‖ = 3 / 4 ∧ ‖γ 1‖ = 1 ∧ (∀ t, γ t ∈ annK d) ∧
    ∀ a b : ℚ, G.chainInf (annA d) (γ (p5bRatTime a)) (γ (p5bRatTime b)) =
      ENNReal.ofReal |((p5bRatTime a : unitInterval) : ℝ) - p5bRatTime b| *
        G.chainInf (annA d) (γ 0) (γ 1)

/-- For a length metric, a witness is exactly a path satisfying the chain condition at rational times. -/
theorem p5b_isWitness_iff_witChain {G : ContMetric d} (hG : G.IsLength) (γ : C(unitInterval, Rd d)) :
    IsWitness G γ ↔ p5bWitChain G γ := by
  have hc : ∀ x y, G.internal (annA d) x y = G.chainInf (annA d) x y :=
    G.internal_eq_chainInf hG isOpen_annA
  constructor
  · intro h
    refine ⟨h.norm_apply_zero, h.norm_apply_one, h.mem_annK, fun a b => ?_⟩
    rw [← hc, ← hc]
    exact h.internal_eq _ _
  · rintro ⟨h0, h1, hK, hrat⟩
    refine ⟨h0, h1, hK, ?_⟩
    have hA : ∀ t, γ t ∈ annA d := fun t => annK_subset_annA (hK t)
    have hfin : G.internal (annA d) (γ 0) (γ 1) ≠ ⊤ := internal_annA_ne_top hG hK 0 1
    let f : unitInterval × unitInterval → ℝ≥0∞ := fun p => G.internal (annA d) (γ p.1) (γ p.2)
    let g : unitInterval × unitInterval → ℝ≥0∞ := fun p =>
      ENNReal.ofReal |(p.1 : ℝ) - p.2| * G.internal (annA d) (γ 0) (γ 1)
    have hfc : Continuous f := by
      have hpair : Continuous fun p : unitInterval × unitInterval => (γ p.1, γ p.2) :=
        (γ.continuous.comp continuous_fst).prodMk (γ.continuous.comp continuous_snd)
      exact (G.continuousOn_internal hG isOpen_annA).comp_continuous hpair
        (fun p => ⟨hA p.1, hA p.2⟩)
    have hgc : Continuous g := by
      refine (ENNReal.continuous_mul_const hfin).comp ?_
      exact ENNReal.continuous_ofReal.comp
        ((continuous_subtype_val.comp continuous_fst).sub
          (continuous_subtype_val.comp continuous_snd)).abs
    have hfg : f = g := by
      refine (p5b_denseRange_ratTime.prodMap p5b_denseRange_ratTime).equalizer hfc hgc ?_
      funext p
      change G.internal (annA d) (γ (p5bRatTime p.1)) (γ (p5bRatTime p.2)) =
        ENNReal.ofReal |((p5bRatTime p.1 : unitInterval) : ℝ) - p5bRatTime p.2| *
          G.internal (annA d) (γ 0) (γ 1)
      rw [hc, hc]
      exact hrat p.1 p.2
    intro s t
    exact congrFun hfg (s, t)

/-- Evaluation of a path at a fixed time is measurable. -/
theorem p5b_measurable_eval (t : unitInterval) :
    Measurable fun γ : C(unitInterval, Rd d) => γ t :=
  (continuous_eval_const t).measurable

/-- The chain formula along a path, at two fixed times, is Borel in `(G, γ)`. -/
theorem p5b_measurable_chainInf_path (V : Set (Rd d)) (s t : unitInterval) :
    Measurable fun p : ContMetric d × C(unitInterval, Rd d) => p.1.chainInf V (p.2 s) (p.2 t) :=
  (ContMetric.measurable_chainInf V).comp (measurable_fst.prodMk
    (((p5b_measurable_eval s).comp measurable_snd).prodMk ((p5b_measurable_eval t).comp measurable_snd)))

theorem p5b_measurableSet_witChain :
    MeasurableSet {p : ContMetric d × C(unitInterval, Rd d) | p5bWitChain p.1 p.2} := by
  have h0 : MeasurableSet {p : ContMetric d × C(unitInterval, Rd d) | ‖p.2 0‖ = 3 / 4} :=
    measurableSet_eq_fun (measurable_norm.comp ((p5b_measurable_eval 0).comp measurable_snd))
      measurable_const
  have h1 : MeasurableSet {p : ContMetric d × C(unitInterval, Rd d) | ‖p.2 1‖ = 1} :=
    measurableSet_eq_fun (measurable_norm.comp ((p5b_measurable_eval 1).comp measurable_snd))
      measurable_const
  have hK : MeasurableSet {p : ContMetric d × C(unitInterval, Rd d) | ∀ t, p.2 t ∈ annK d} := by
    have hc : IsClosed {γ : C(unitInterval, Rd d) | ∀ t, γ t ∈ annK d} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun t => (isClosed_annCl _ _ _).preimage (continuous_eval_const t)
    exact hc.measurableSet.preimage measurable_snd
  have hr : MeasurableSet {p : ContMetric d × C(unitInterval, Rd d) |
      ∀ a b : ℚ, p.1.chainInf (annA d) (p.2 (p5bRatTime a)) (p.2 (p5bRatTime b)) =
        ENNReal.ofReal |((p5bRatTime a : unitInterval) : ℝ) - p5bRatTime b| *
          p.1.chainInf (annA d) (p.2 0) (p.2 1)} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_eq_fun (p5b_measurable_chainInf_path _ _ _)
        (measurable_const.mul (p5b_measurable_chainInf_path _ _ _))
  exact h0.inter (h1.inter (hK.inter hr))

/-! ## `H↓` and `H↑` -/

/-- The Borel relation behind `H↓(D, E; b)` on (pair of metrics, path). -/
def p5bHdownRel (b : ℝ) : Set ((ContMetric d × ContMetric d) × C(unitInterval, Rd d)) :=
  {p | p5bWitChain p.1.2 p.2 ∧
    p.1.2.chainInf (annA d) (p.2 0) (p.2 1) ≤ ENNReal.ofReal b * p.1.1.chainInf (annA d) (p.2 0) (p.2 1)}

/-- The Borel relation behind `H↑(D, E; b)` on (pair of metrics, path). -/
def p5bHupRel (b : ℝ) : Set ((ContMetric d × ContMetric d) × C(unitInterval, Rd d)) :=
  {p | p5bWitChain p.1.1 p.2 ∧
    ENNReal.ofReal b * p.1.1.chainInf (annA d) (p.2 0) (p.2 1) < p.1.2.chainInf (annA d) (p.2 0) (p.2 1)}

/-- The two chain values `(D(γ 0, γ 1; A), E(γ 0, γ 1; A))` are Borel in `((D, E), γ)`. -/
theorem p5b_measurable_chainInf_fst :
    Measurable fun p : (ContMetric d × ContMetric d) × C(unitInterval, Rd d) =>
      p.1.1.chainInf (annA d) (p.2 0) (p.2 1) :=
  (p5b_measurable_chainInf_path (d := d) (annA d) 0 1).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem p5b_measurable_chainInf_snd :
    Measurable fun p : (ContMetric d × ContMetric d) × C(unitInterval, Rd d) =>
      p.1.2.chainInf (annA d) (p.2 0) (p.2 1) :=
  (p5b_measurable_chainInf_path (d := d) (annA d) 0 1).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem p5b_measurableSet_hdownRel (b : ℝ) : MeasurableSet (p5bHdownRel (d := d) b) := by
  have hf : Measurable fun p : (ContMetric d × ContMetric d) × C(unitInterval, Rd d) => (p.1.2, p.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hw : MeasurableSet {p : (ContMetric d × ContMetric d) × C(unitInterval, Rd d) |
      p5bWitChain p.1.2 p.2} :=
    hf p5b_measurableSet_witChain
  have hle : MeasurableSet {p : (ContMetric d × ContMetric d) × C(unitInterval, Rd d) |
      p.1.2.chainInf (annA d) (p.2 0) (p.2 1) ≤ ENNReal.ofReal b * p.1.1.chainInf (annA d) (p.2 0) (p.2 1)} :=
    measurableSet_le p5b_measurable_chainInf_snd (measurable_const.mul p5b_measurable_chainInf_fst)
  exact hw.inter hle

theorem p5b_measurableSet_hupRel (b : ℝ) : MeasurableSet (p5bHupRel (d := d) b) := by
  have hf : Measurable fun p : (ContMetric d × ContMetric d) × C(unitInterval, Rd d) => (p.1.1, p.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hw : MeasurableSet {p : (ContMetric d × ContMetric d) × C(unitInterval, Rd d) |
      p5bWitChain p.1.1 p.2} :=
    hf p5b_measurableSet_witChain
  have hlt : MeasurableSet {p : (ContMetric d × ContMetric d) × C(unitInterval, Rd d) |
      ENNReal.ofReal b * p.1.1.chainInf (annA d) (p.2 0) (p.2 1) < p.1.2.chainInf (annA d) (p.2 0) (p.2 1)} :=
    measurableSet_lt (measurable_const.mul p5b_measurable_chainInf_fst) p5b_measurable_chainInf_snd
  exact hw.inter hlt

theorem p5b_uMeasurableSet_hdown (b : ℝ) :
    LQGMetric.UMeasurableSet {q : ContMetric d × ContMetric d | ∃ γ, (q, γ) ∈ p5bHdownRel (d := d) b} :=
  LQGMetric.UMeasurableSet.setOf_exists (p5b_measurableSet_hdownRel b)

theorem p5b_uMeasurableSet_hup (b : ℝ) :
    LQGMetric.UMeasurableSet {q : ContMetric d × ContMetric d | ∃ γ, (q, γ) ∈ p5bHupRel (d := d) b} :=
  LQGMetric.UMeasurableSet.setOf_exists (p5b_measurableSet_hupRel b)

/-- On length metrics, `H↓` is the projection of its Borel relation. -/
theorem p5b_mem_hdown_iff {D E : DistRd d → ContMetric d} {g : DistRd d} (hD : (rho D g).IsLength)
    (hE : (rho E g).IsLength) (b : ℝ) :
    g ∈ Hdown D E b ↔ ∃ γ, ((rho D g, rho E g), γ) ∈ p5bHdownRel b := by
  have hcD := (rho D g).internal_eq_chainInf hD (isOpen_annA (d := d))
  have hcE := (rho E g).internal_eq_chainInf hE (isOpen_annA (d := d))
  refine exists_congr fun γ => ?_
  change (IsWitness (rho E g) γ ∧ (rho E g).internal (annA d) (γ 0) (γ 1) ≤
      ENNReal.ofReal b * (rho D g).internal (annA d) (γ 0) (γ 1)) ↔
    (p5bWitChain (rho E g) γ ∧ (rho E g).chainInf (annA d) (γ 0) (γ 1) ≤
      ENNReal.ofReal b * (rho D g).chainInf (annA d) (γ 0) (γ 1))
  rw [p5b_isWitness_iff_witChain hE, hcD, hcE]

/-- On length metrics, `H↑` is the projection of its Borel relation. -/
theorem p5b_mem_hup_iff {D E : DistRd d → ContMetric d} {g : DistRd d} (hD : (rho D g).IsLength)
    (hE : (rho E g).IsLength) (b : ℝ) :
    g ∈ Hup D E b ↔ ∃ γ, ((rho D g, rho E g), γ) ∈ p5bHupRel b := by
  have hcD := (rho D g).internal_eq_chainInf hD (isOpen_annA (d := d))
  have hcE := (rho E g).internal_eq_chainInf hE (isOpen_annA (d := d))
  refine exists_congr fun γ => ?_
  change (IsWitness (rho D g) γ ∧ ENNReal.ofReal b * (rho D g).internal (annA d) (γ 0) (γ 1) <
      (rho E g).internal (annA d) (γ 0) (γ 1)) ↔
    (p5bWitChain (rho D g) γ ∧ ENNReal.ofReal b * (rho D g).chainInf (annA d) (γ 0) (γ 1) <
      (rho E g).chainInf (annA d) (γ 0) (γ 1))
  rw [p5b_isWitness_iff_witChain hD, hcD, hcE]

/-! ## The references -/

/-- The reference conditions with the `A`-internal metric replaced by the chain formula, written as universal
quantifications over closed sets of pairs. -/
def p5bRefsChain (G : ContMetric d) (H₀ σ₀ β₀ m M : ℝ) : Prop :=
  (∀ p ∈ annCl (0 : Rd d) (5 / 8) (3 / 2) ×ˢ annCl (0 : Rd d) (5 / 8) (3 / 2),
      ENNReal.ofReal (H₀⁻¹ * ‖p.1 - p.2‖ ^ β₀) ≤ G.chainInf (annA d) p.1 p.2) ∧
    (∀ p ∈ {p : Rd d × Rd d | p ∈ annCl (0 : Rd d) (5 / 8) (3 / 2) ×ˢ annCl (0 : Rd d) (5 / 8) (3 / 2) ∧
        ‖p.1 - p.2‖ ≤ 1 / 64},
      G.chainInf (annA d) p.1 p.2 ≤ ENNReal.ofReal (H₀ * ‖p.1 - p.2‖ ^ σ₀)) ∧
    (∀ p ∈ sphere (0 : Rd d) (3 / 4) ×ˢ sphere (0 : Rd d) 1, ENNReal.ofReal m ≤ G.chainInf (annA d) p.1 p.2) ∧
    (∀ p ∈ sphere (0 : Rd d) 1 ×ˢ sphere (0 : Rd d) 1, G.chainInf (annA d) p.1 p.2 ≤ ENNReal.ofReal M) ∧
    (∀ p ∈ annK d ×ˢ annK d, G.chainInf (annA d) p.1 p.2 ≤ ENNReal.ofReal M)

/-- For a length metric, the references are exactly the chain conditions. -/
theorem p5b_localRefs_iff_chain {G : ContMetric d} (hG : G.IsLength) (H₀ σ₀ β₀ m M : ℝ) :
    LocalRefs G H₀ σ₀ β₀ m M ↔ p5bRefsChain G H₀ σ₀ β₀ m M := by
  have hc : ∀ x y, G.internal (annA d) x y = G.chainInf (annA d) x y :=
    G.internal_eq_chainInf hG isOpen_annA
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
    · rw [← hc]
      exact h.lower p.1 hp.1 p.2 hp.2
    · rw [← hc]
      exact h.upper p.1 hp.1.1 p.2 hp.1.2 hp.2
    · rw [← hc]
      refine h.cross.trans ?_
      unfold setDistIn
      exact iInf₂_le_of_le p.1 hp.1 (iInf₂_le p.2 hp.2)
    · rw [← hc]
      refine le_trans ?_ h.diam
      unfold diamIn
      exact le_iSup₂_of_le p.1 hp.1 (le_iSup₂_of_le p.2 hp.2 le_rfl)
    · rw [← hc]
      refine le_trans ?_ h.diamK
      unfold diamIn
      exact le_iSup₂_of_le p.1 hp.1 (le_iSup₂_of_le p.2 hp.2 le_rfl)
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun x hx y hy => ?_, fun x hx y hy hxy => ?_, ?_, ?_, ?_⟩
    · rw [hc]
      exact h1 (x, y) ⟨hx, hy⟩
    · rw [hc]
      exact h2 (x, y) ⟨⟨hx, hy⟩, hxy⟩
    · unfold setDistIn
      refine le_iInf₂ fun u hu => le_iInf₂ fun v hv => ?_
      rw [hc]
      exact h3 (u, v) ⟨hu, hv⟩
    · unfold diamIn
      refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
      rw [hc]
      exact h4 (u, v) ⟨hu, hv⟩
    · unfold diamIn
      refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
      rw [hc]
      exact h5 (u, v) ⟨hu, hv⟩

/-- The chain formula as a function of `(G, (x, y))`. -/
theorem p5b_measurable_chainInf_pair (V : Set (Rd d)) :
    Measurable fun p : ContMetric d × (Rd d × Rd d) => p.1.chainInf V p.2.1 p.2.2 :=
  ContMetric.measurable_chainInf V

theorem p5b_measurable_normSub :
    Measurable fun p : ContMetric d × (Rd d × Rd d) => ‖p.2.1 - p.2.2‖ :=
  measurable_norm.comp ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))

theorem p5b_uMeasurableSet_refsChain (H₀ σ₀ β₀ m M : ℝ) :
    LQGMetric.UMeasurableSet {G : ContMetric d | p5bRefsChain G H₀ σ₀ β₀ m M} := by
  have hK5 : MeasurableSet (annCl (0 : Rd d) (5 / 8) (3 / 2) ×ˢ annCl (0 : Rd d) (5 / 8) (3 / 2)) :=
    (isClosed_annCl _ _ _).measurableSet.prod (isClosed_annCl _ _ _).measurableSet
  have hL : MeasurableSet {p : Rd d × Rd d |
      p ∈ annCl (0 : Rd d) (5 / 8) (3 / 2) ×ˢ annCl (0 : Rd d) (5 / 8) (3 / 2) ∧ ‖p.1 - p.2‖ ≤ 1 / 64} :=
    hK5.inter (measurableSet_le (measurable_norm.comp (measurable_fst.sub measurable_snd)) measurable_const)
  have hS : MeasurableSet (sphere (0 : Rd d) (3 / 4) ×ˢ sphere (0 : Rd d) 1) :=
    isClosed_sphere.measurableSet.prod isClosed_sphere.measurableSet
  have hS1 : MeasurableSet (sphere (0 : Rd d) 1 ×ˢ sphere (0 : Rd d) 1) :=
    isClosed_sphere.measurableSet.prod isClosed_sphere.measurableSet
  have hKK : MeasurableSet (annK d ×ˢ annK d) :=
    (isClosed_annCl _ _ _).measurableSet.prod (isClosed_annCl _ _ _).measurableSet
  have hc := p5b_measurable_chainInf_pair (d := d) (annA d)
  have r1 : MeasurableSet {p : ContMetric d × (Rd d × Rd d) |
      ENNReal.ofReal (H₀⁻¹ * ‖p.2.1 - p.2.2‖ ^ β₀) ≤ p.1.chainInf (annA d) p.2.1 p.2.2} :=
    measurableSet_le (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (p5b_measurable_normSub.pow_const β₀))) hc
  have r2 : MeasurableSet {p : ContMetric d × (Rd d × Rd d) |
      p.1.chainInf (annA d) p.2.1 p.2.2 ≤ ENNReal.ofReal (H₀ * ‖p.2.1 - p.2.2‖ ^ σ₀)} :=
    measurableSet_le hc (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (p5b_measurable_normSub.pow_const σ₀)))
  have r3 : MeasurableSet {p : ContMetric d × (Rd d × Rd d) |
      ENNReal.ofReal m ≤ p.1.chainInf (annA d) p.2.1 p.2.2} :=
    measurableSet_le measurable_const hc
  have r4 : MeasurableSet {p : ContMetric d × (Rd d × Rd d) |
      p.1.chainInf (annA d) p.2.1 p.2.2 ≤ ENNReal.ofReal M} :=
    measurableSet_le hc measurable_const
  have u1 := uMeasurableSet_forall_mem _ hK5 r1
  have u2 := uMeasurableSet_forall_mem _ hL r2
  have u3 := uMeasurableSet_forall_mem _ hS r3
  have u4 := uMeasurableSet_forall_mem _ hS1 r4
  have u5 := uMeasurableSet_forall_mem _ hKK r4
  exact u1.inter (u2.inter (u3.inter (u4.inter u5)))

/-! ## Null-measurability of the three events -/

variable {D E : DistRd d → ContMetric d}

theorem p5b_measurable_rhoPair (hD : Measurable D) (hE : Measurable E) :
    Measurable fun g : DistRd d => (rho D g, rho E g) :=
  (measurable_rho hD).prodMk (measurable_rho hE)

/-- `H↓(D, E; b)` is null-measurable for every finite law under which `ρ^D`, `ρ^E` are almost surely length
metrics. -/
theorem p5b_nullMeasurableSet_hdown (hD : Measurable D) (hE : Measurable E)
    (μ : Measure (DistRd d)) [IsFiniteMeasure μ] (hlD : ∀ᵐ g ∂μ, (rho D g).IsLength)
    (hlE : ∀ᵐ g ∂μ, (rho E g).IsLength) (b : ℝ) : NullMeasurableSet (Hdown D E b) μ := by
  have hT := ((p5b_uMeasurableSet_hdown (d := d) b).preimage
    (p5b_measurable_rhoPair hD hE)).nullMeasurableSet μ
  refine hT.congr ?_
  filter_upwards [hlD, hlE] with g h1 h2
  exact propext (p5b_mem_hdown_iff h1 h2 b).symm

/-- `H↑(D, E; b)` is null-measurable for every finite law under which `ρ^D`, `ρ^E` are almost surely length
metrics. -/
theorem p5b_nullMeasurableSet_hup (hD : Measurable D) (hE : Measurable E)
    (μ : Measure (DistRd d)) [IsFiniteMeasure μ] (hlD : ∀ᵐ g ∂μ, (rho D g).IsLength)
    (hlE : ∀ᵐ g ∂μ, (rho E g).IsLength) (b : ℝ) : NullMeasurableSet (Hup D E b) μ := by
  have hT := ((p5b_uMeasurableSet_hup (d := d) b).preimage
    (p5b_measurable_rhoPair hD hE)).nullMeasurableSet μ
  refine hT.congr ?_
  filter_upwards [hlD, hlE] with g h1 h2
  exact propext (p5b_mem_hup_iff h1 h2 b).symm

/-- The pair references are null-measurable for every finite law under which `ρ^D`, `ρ^E` are almost surely length
metrics. -/
theorem p5b_nullMeasurableSet_pairRefs (hD : Measurable D) (hE : Measurable E)
    (μ : Measure (DistRd d)) [IsFiniteMeasure μ] (hlD : ∀ᵐ g ∂μ, (rho D g).IsLength)
    (hlE : ∀ᵐ g ∂μ, (rho E g).IsLength) (H₀ σ₀ β₀ m M : ℝ) :
    NullMeasurableSet (PairRefs D E H₀ σ₀ β₀ m M) μ := by
  have hU := p5b_uMeasurableSet_refsChain (d := d) H₀ σ₀ β₀ m M
  have hT := ((hU.preimage (measurable_rho hD)).inter (hU.preimage (measurable_rho hE))).nullMeasurableSet μ
  refine hT.congr ?_
  filter_upwards [hlD, hlE] with g h1 h2
  refine propext ?_
  change (p5bRefsChain (rho D g) H₀ σ₀ β₀ m M ∧ p5bRefsChain (rho E g) H₀ σ₀ β₀ m M) ↔
    (LocalRefs (rho D g) H₀ σ₀ β₀ m M ∧ LocalRefs (rho E g) H₀ σ₀ β₀ m M)
  rw [p5b_localRefs_iff_chain h1, p5b_localRefs_iff_chain h2]

end HigherDimLQGContinuity
