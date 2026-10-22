import HigherDimLQGMetric.Determ.CopyLaw
import HigherDimLQGMetric.Events.WitnessMeas
import LQGMetric.Papers.GM.S4.P412eConcat
import LQGMetric.Meas.UM

/-! Universal measurability of the length metric property in every dimension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open LQGMetric
open LQGMetric.MetricGeometry LQGMetric.GM
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {dim : ℕ}

/-- the dense sequence of `Rd dim` -/
abbrev determQ : ℕ → Rd dim := TopologicalSpace.denseSeq (Rd dim)

/-- the Borel witness relation: `Γ (i, j, m)` is a path from `q i` to `q j` of `d`-length at
most `d(q i, q j) + 1/(m+1)` -/
def determLenS : Set (ContMetric dim × (ℕ × ℕ × ℕ → C(unitInterval, Rd dim))) :=
  {p | ∀ k : ℕ × ℕ × ℕ, p.2 k 0 = determQ k.1 ∧ p.2 k 1 = determQ k.2.1 ∧
    p.1.len (fun t => p.2 k (pj t)) 0 1 ≤
      edist (p.1.pt (determQ k.1)) (p.1.pt (determQ k.2.1)) + ENNReal.ofReal (1 / ((k.2.2 : ℝ) + 1))}

theorem determ_measurableSet_lenS (dim : ℕ) : MeasurableSet (determLenS (dim := dim)) := by
  have key : ∀ k : ℕ × ℕ × ℕ, MeasurableSet {p : ContMetric dim × (ℕ × ℕ × ℕ → C(unitInterval, Rd dim)) |
      p.2 k 0 = determQ k.1 ∧ p.2 k 1 = determQ k.2.1 ∧
      p.1.len (fun t => p.2 k (pj t)) 0 1 ≤
        edist (p.1.pt (determQ k.1)) (p.1.pt (determQ k.2.1)) +
          ENNReal.ofReal (1 / ((k.2.2 : ℝ) + 1))} := by
    intro k
    have ev : Measurable fun p : ContMetric dim × (ℕ × ℕ × ℕ → C(unitInterval, Rd dim)) => p.2 k :=
      (measurable_pi_apply k).comp measurable_snd
    have ev' : ∀ a : unitInterval, Measurable
        fun p : ContMetric dim × (ℕ × ℕ × ℕ → C(unitInterval, Rd dim)) => p.2 k a :=
      fun a => (continuous_eval_const a).measurable.comp ev
    have hlen : Measurable fun p : ContMetric dim × (ℕ × ℕ × ℕ → C(unitInterval, Rd dim)) =>
        p.1.len (fun t => p.2 k (pj t)) 0 1 := by
      have hm0 : Measurable fun p : ContMetric dim × C(unitInterval, Rd dim) =>
          p.1.len (fun t => p.2 (pj t)) 0 1 := lowerSemicontinuous_lenPath.measurable
      exact hm0.comp (f := fun p : ContMetric dim × (ℕ × ℕ × ℕ → C(unitInterval, Rd dim)) => (p.1, p.2 k))
        (measurable_fst.prodMk ev)
    have hed : Measurable fun p : ContMetric dim × (ℕ × ℕ × ℕ → C(unitInterval, Rd dim)) =>
        edist (p.1.pt (determQ k.1)) (p.1.pt (determQ k.2.1)) :=
      ContMetric.measurable_edist_pt.comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_const))
    exact (measurableSet_eq_fun (ev' 0) measurable_const).inter
      ((measurableSet_eq_fun (ev' 1) measurable_const).inter
        (measurableSet_le hlen (hed.add measurable_const)))
  have e : determLenS = ⋂ k : ℕ × ℕ × ℕ, {p : ContMetric dim × (ℕ × ℕ × ℕ → C(unitInterval, Rd dim)) |
      p.2 k 0 = determQ k.1 ∧ p.2 k 1 = determQ k.2.1 ∧
      p.1.len (fun t => p.2 k (pj t)) 0 1 ≤
        edist (p.1.pt (determQ k.1)) (p.1.pt (determQ k.2.1)) +
          ENNReal.ofReal (1 / ((k.2.2 : ℝ) + 1))} := by
    ext p; simp only [determLenS, mem_ofPred_eq, mem_iInter]
  rw [e]
  exact MeasurableSet.iInter key

/-- a path in `d.Space` as an element of `C([0,1], Rd dim)` -/
def determToC (d : ContMetric dim) {x y : d.Space} (γ : Path x y) : C(unitInterval, Rd dim) :=
  ⟨fun t => (ContMetric.ptHomeomorph d).symm (γ t),
    (ContMetric.ptHomeomorph d).symm.continuous.comp γ.continuous⟩

theorem determ_len_toC (d : ContMetric dim) {x y : d.Space} (γ : Path x y) :
    d.len (fun t => determToC d γ (pj t)) 0 1 = pathLength γ := rfl

/-- the dense points are dense in `d.Space` -/
theorem determ_denseRange (d : ContMetric dim) : DenseRange fun n => d.pt (determQ n) :=
  (Function.Surjective.denseRange (f := d.pt) Function.surjective_id).comp
    (TopologicalSpace.denseRange_denseSeq (Rd dim)) (ContMetric.continuous_pt d)

/-- from the witness: every point is joined to some dense point at distance `< δ` by a path of
length `≤ δ` (infinite concatenation, `GM.p412e_concat`) -/
theorem determ_short_path (d : ContMetric dim) {Γ : ℕ × ℕ × ℕ → C(unitInterval, Rd dim)}
    (hΓ : (d, Γ) ∈ determLenS) (x : d.Space) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℕ, dist (d.pt (determQ a)) x < δ ∧
      ∃ γ : Path (d.pt (determQ a)) x, pathLength γ ≤ ENNReal.ofReal δ := by
  set e : ℕ → ℝ := fun k => δ / 8 * (1 / 2) ^ k with he
  have he0 : ∀ k, 0 < e k := fun k => by positivity
  have hemono : ∀ k, e (k + 1) ≤ e k := fun k => by
    have h2 : e (k + 1) = e k / 2 := by simp only [he, pow_succ]; ring
    have := he0 k
    linarith
  have hd := Metric.denseRange_iff.1 (determ_denseRange d)
  choose a ha using fun k => hd x (e k) (he0 k)
  choose m hm using fun k => exists_nat_one_div_lt (he0 k)
  let η : ℕ → C(unitInterval, Rd dim) := fun k => Γ (a k, a (k + 1), m k)
  let γ : ℕ → ℝ → d.Space := fun k t => d.pt (η k (pj t))
  have hcont : ∀ k, ContinuousOn (γ k) (Icc 0 1) := fun k =>
    ((ContMetric.continuous_pt d).comp ((η k).continuous.comp continuous_projIcc)).continuousOn
  have h0 : ∀ k, γ k 0 = d.pt (determQ (a k)) := fun k => by
    show d.pt (η k (pj 0)) = _
    rw [show pj 0 = 0 from Subtype.ext (pj_coe_of_mem ⟨le_rfl, zero_le_one⟩)]
    exact congrArg d.pt (hΓ (a k, a (k + 1), m k)).1
  have h1 : ∀ k, γ k 1 = d.pt (determQ (a (k + 1))) := fun k => by
    show d.pt (η k (pj 1)) = _
    rw [show pj 1 = 1 from Subtype.ext (pj_coe_of_mem ⟨zero_le_one, le_rfl⟩)]
    exact congrArg d.pt (hΓ (a k, a (k + 1), m k)).2.1
  have hj : ∀ k, γ k 1 = γ (k + 1) 0 := fun k => by rw [h1, h0]
  have hlen : ∀ k, curveLength (γ k) 0 1 ≤ ENNReal.ofReal (3 * e k) := fun k => by
    have := (hΓ (a k, a (k + 1), m k)).2.2
    refine this.trans ?_
    rw [edist_dist, ← ENNReal.ofReal_add dist_nonneg (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have t1 := dist_triangle_right (d.pt (determQ (a k))) (d.pt (determQ (a (k + 1)))) x
    have := ha k; have := ha (k + 1); have := hm k; have := hemono k
    rw [dist_comm] at *
    simp only at *
    linarith
  have hsum : HasSum (fun k => 3 * e k) (3 * (δ / 8) * 2) := by
    simp only [he, ← mul_assoc]
    exact (hasSum_geometric_two).mul_left _
  have htsum : ∑' k, curveLength (γ k) 0 1 ≤ ENNReal.ofReal (3 * (δ / 8) * 2) := by
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => (mul_pos three_pos (he0 k)).le)
      hsum.summable]
    exact ENNReal.tsum_le_tsum hlen
  have hp : Tendsto (fun k => γ k 0) atTop (𝓝 x) := by
    simp only [h0]
    have he_t : Tendsto e atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (δ / 8)
      simpa [he] using this
    exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun k => (ha k).le.trans_eq' (dist_comm _ _)) he_t)
  obtain ⟨hc, hc0, hc1, hcl, -⟩ := p412e_concat hcont hj hp
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top htsum)
  obtain ⟨π, hπ, -⟩ := exists_path_of_curve zero_le_one hc
  refine ⟨a 0, (dist_comm _ _).trans_lt ((ha 0).trans_le (by simp [he]; linarith)),
    π.cast (by rw [hc0, h0]) hc1.symm, ?_⟩
  show pathLength π ≤ _
  rw [hπ]
  exact hcl.trans (htsum.trans (ENNReal.ofReal_le_ofReal (by linarith)))

/-- **`d` is a length metric iff it has a Borel witness** -/
theorem determ_isLength_iff (d : ContMetric dim) : d.IsLength ↔ ∃ Γ, (d, Γ) ∈ determLenS := by
  constructor
  · intro hL
    have := fun k : ℕ × ℕ × ℕ => hL (d.pt (determQ k.1)) (d.pt (determQ k.2.1))
      (1 / ((k.2.2 : ℝ) + 1)) (by positivity)
    choose γ hγ using this
    refine ⟨fun k => determToC d (γ k), fun k => ⟨congrArg d.unpt (γ k).source, congrArg d.unpt (γ k).target, ?_⟩⟩
    exact (determ_len_toC d (γ k)).trans_le (hγ k)
  · rintro ⟨Γ, hΓ⟩ x y ε hε
    set δ := ε / 6 with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨a, hax, γa, hγa⟩ := determ_short_path d hΓ x hδ0
    obtain ⟨b, hby, γb, hγb⟩ := determ_short_path d hΓ y hδ0
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ0
    have hab := (hΓ (a, b, m))
    let η : Path (d.pt (determQ a)) (d.pt (determQ b)) :=
      { toFun := fun t => d.pt (Γ (a, b, m) t)
        continuous_toFun := (ContMetric.continuous_pt d).comp (Γ (a, b, m)).continuous
        source' := congrArg d.pt hab.1
        target' := congrArg d.pt hab.2.1 }
    have hη : pathLength η ≤ ENNReal.ofReal (dist (d.pt (determQ a)) (d.pt (determQ b)) + δ) := by
      refine (show pathLength η = d.len (fun t => Γ (a, b, m) (pj t)) 0 1 from rfl) ▸
        hab.2.2.trans ?_
      rw [edist_dist, ← ENNReal.ofReal_add dist_nonneg (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by simp only at hm ⊢; linarith)
    refine ⟨(γa.symm.trans η).trans γb, ?_⟩
    rw [pathLength_trans, pathLength_trans, pathLength_symm, edist_dist,
      ← ENNReal.ofReal_add dist_nonneg hε.le]
    have t1 := dist_triangle4 (d.pt (determQ a)) x y (d.pt (determQ b))
    have hsum : ENNReal.ofReal δ + ENNReal.ofReal (dist (d.pt (determQ a)) (d.pt (determQ b)) + δ) +
        ENNReal.ofReal δ ≤ ENNReal.ofReal (dist x y + ε) := by
      rw [← ENNReal.ofReal_add hδ0.le (by positivity), ← ENNReal.ofReal_add (by positivity)
        hδ0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [dist_comm] at hby
      linarith
    exact (add_le_add (add_le_add hγa hη) hγb).trans hsum

instance determ_sbW (dim : ℕ) : StandardBorelSpace (ℕ × ℕ × ℕ → C(unitInterval, Rd dim)) := inferInstance

/-- **the set of length metrics is universally measurable** (analytic + Lusin) -/
theorem determ_uMeasurableSet_isLength (dim : ℕ) : UMeasurableSet {d : ContMetric dim | d.IsLength} := by
  have := UMeasurableSet.setOf_exists (determ_measurableSet_lenS dim)
  convert this using 1
  ext d
  exact determ_isLength_iff d

/-- Length metrics remain almost surely length metrics after disintegration by a field. -/
theorem determ_kernel_length {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [Nonempty (ContMetric dim)]
    (h : Ω → DistRd dim) (D : Ω → ContMetric dim)
    (hh : Measurable h) (hD : Measurable D)
    (hL : ∀ᵐ ω ∂P, (D ω).IsLength) :
    ∀ᵐ g ∂P.map h, ∀ᵐ d ∂condDistrib D h P g, d.IsLength := by
  have : IsProbabilityMeasure (P.map D) :=
    (Measure.isProbabilityMeasure_map_iff hD.aemeasurable).2 inferInstance
  obtain ⟨M, hMS, hM, hMae⟩ :=
    (determ_uMeasurableSet_isLength dim (P.map D) inferInstance).exists_measurable_subset_ae_eq
  obtain ⟨N, hSN, hN, hN0⟩ := exists_measurable_superset_of_null
    (show (P.map D) ({d : ContMetric dim | d.IsLength} \ M) = 0 from ae_le_set.1 hMae.symm.le)
  have hDM : ∀ᵐ ω ∂P, D ω ∈ M := by
    have hN' : ∀ᵐ ω ∂P, D ω ∉ N := by
      rw [Measure.map_apply hD hN] at hN0
      exact measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hL, hN'] with ω h1 h2
    by_contra h3
    exact h2 (hSN ⟨h1, h3⟩)
  have h2 : ∀ᵐ p ∂(P.map h ⊗ₘ condDistrib D h P), p.2 ∈ M := by
    rw [compProd_map_condDistrib hh.aemeasurable hD.aemeasurable]
    exact (ae_map_iff (hh.prodMk hD).aemeasurable (measurable_snd hM)).2 hDM
  exact ((Measure.ae_compProd_iff (measurable_snd hM)).1 h2).mono fun g hg =>
    hg.mono fun d hd => hMS hd


end HigherDimLQGMetric
