import QuantumZipper.Proofs.GFF.CoordRegCompFixed

/-!
# RC3 composition law: joint measurability and Fubini over the path (RC-COMP)

The events of the composition law for `Y_t` (`CoordRegComp.lhsC`, `rhsC`: regularized and raw
value of `coordChange (ofFun G + x) (revMap A (T−t)) Q` at `μ.map (revMap V t)`, with `V`, `A`
built from one path `g` on `[0,T]` by `revPath`) are jointly measurable in (path, field)
(`measurable_lhsC`, `measurable_rhsC`), so a law holding for every fixed path holds along a random
path independent of the field (`ae_lhsC_eq_rhsC_random`). The targets (R1), (R2) are in
`CoordRegComp.lean`.

Proof: the fixed-driver law `CoordRegComp.ae_evalReg_comp_fixed` (RC3-general applied to the
pushed measure) for every continuous path of the Brownian motion on `[0,T]`, then Fubini over the
independent pair (path, field) (`CharFun.ae_indep`, as in `B2.ae_split_compact_random`). The
event is written through jointly measurable versions of the reverse flow and of its derivative
(`CharFun.Fm`, `CharFun.Dm`). Both the field's map `fwdMapInv W (T−t)` and the pushing map
`revMap V t` are functions of the path of `B` on `[0,T]` (`revPath`).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (via RC3-general);
Sheffield arXiv:1012.4797 §5.2, pp. 57–59. The reduction is an own argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Real Topology

namespace QuantumZipper
namespace CoordRegComp

open CoordReg CharFun B2

/-! ## 1. Paths -/

/-- `r ↦ g(c − r) − g(c)` (clamped to `[0,T]`), as a path on `[0,T']`. -/
def revPath {T : ℝ} (hT : 0 ≤ T) (c T' : ℝ) (g : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) T', ℝ) :=
  ⟨fun r => g (projIcc 0 T hT (c - r)) - g (projIcc 0 T hT c),
    (g.continuous.comp (continuous_projIcc.comp (continuous_const.sub continuous_subtype_val))).sub
      continuous_const⟩

theorem measurable_revPath {T : ℝ} (hT : 0 ≤ T) (c T' : ℝ) : Measurable (revPath hT c T') :=
  ContinuousMap.measurable_iff_eval.2 fun _ =>
    (ContinuousMap.measurable_eval _).sub (ContinuousMap.measurable_eval _)

theorem Wof_revPath (κ : ℝ) {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') (c : ℝ)
    (g : C(Icc (0 : ℝ) T, ℝ)) {r : ℝ} (hr : r ∈ Icc 0 T') :
    Wof κ T' hT' (revPath hT c T' g) r =
      Real.sqrt κ * (g (projIcc 0 T hT (c - r)) - g (projIcc 0 T hT c)) := by
  simp only [Wof, revPath, ContinuousMap.coe_mk, projIcc_of_mem hT' hr]

/-! ## 2. Joint measurability -/

theorem measurable_avgReg_right (y : FieldSample) (k : ℕ) : Measurable fun w => avgReg y k w :=
  (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)

theorem measurable_evalReg_pushΦ {α : Type*} [MeasurableSpace α] (μ : Measure ℂ) [SFinite μ]
    {Φ : α × ℂ → ℂ} (hΦ : Measurable Φ) :
    Measurable fun p : α × FieldSample => evalReg p.2 (μ.map fun u => Φ (p.1, u)) := by
  have heq : ∀ p : α × FieldSample, evalReg p.2 (μ.map fun u => Φ (p.1, u)) =
      limUnder atTop fun k => ∫ z, avgReg p.2 k (Φ (p.1, z)) ∂μ := by
    intro p
    unfold evalReg
    congr 1
    funext k
    rw [integral_map (show Measurable fun u => Φ (p.1, u) from
      hΦ.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (measurable_avgReg_right p.2 k).aestronglyMeasurable]
  rw [show (fun p : α × FieldSample => evalReg p.2 (μ.map fun u => Φ (p.1, u))) = _ from
    funext heq]
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  have hm : Measurable fun q : (α × FieldSample) × ℂ => avgReg q.1.2 k (Φ (q.1.1, q.2)) :=
    (measurable_avgReg k).comp ((measurable_snd.comp measurable_fst).prodMk
      (hΦ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'

variable (κ : ℝ) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (hs : 0 ≤ T - t) (G : ℂ → ℝ) (Q : ℝ)
  (μ : Measure ℂ)

/-- Left side of the composition law, as a function of (path, field). -/
def lhsC (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  evalReg (coordChange (ofFun G + p.2) (revMap (Wof κ (T - t) hs (revPath hT (T - t) (T - t) p.1))
    (T - t)) Q) (μ.map (revMap (Wof κ t ht (revPath hT T t p.1)) t))

/-- Right side of the composition law (raw value), as a function of (path, field). -/
def rhsC (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  coordChange (ofFun G + p.2) (revMap (Wof κ (T - t) hs (revPath hT (T - t) (T - t) p.1))
    (T - t)) Q (μ.map (revMap (Wof κ t ht (revPath hT T t p.1)) t))

theorem measurable_lhsC [SFinite μ] : Measurable (lhsC κ hT ht hs G Q μ) := by
  have heq : ∀ p, lhsC κ hT ht hs G Q μ p = limUnder atTop fun k =>
      ∫ u, avgReg (coordChange (ofFun G + p.2)
        (revMap (Wof κ (T - t) hs (revPath hT (T - t) (T - t) p.1)) (T - t)) Q) k
          (Fm κ t ht (revPath hT T t p.1, u)) ∂μ := by
    intro p
    unfold lhsC evalReg
    congr 1
    funext k
    rw [integral_map (measurable_revMap_Wof κ t ht _).aemeasurable
      (measurable_avgReg_right _ k).aestronglyMeasurable]
    simp only [Fm]
  rw [show lhsC κ hT ht hs G Q μ = _ from funext heq]
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  have hp1 : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ => q.1.1 :=
    measurable_fst.comp measurable_fst
  have hm := (measurable_avgReg_coordChange κ hs G Q k).comp
    ((((measurable_revPath hT (T - t) (T - t)).comp hp1).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_Fm κ t ht).comp (((measurable_revPath hT T t).comp hp1).prodMk measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'

theorem measurable_rhsC [SFinite μ] (hμH : ∀ᵐ z ∂μ, z ∈ H) :
    Measurable (rhsC κ hT ht hs G Q μ) := by
  set Φ : C(Icc (0 : ℝ) T, ℝ) × ℂ → ℂ := fun q =>
    Fm κ (T - t) hs (revPath hT (T - t) (T - t) q.1, Fm κ t ht (revPath hT T t q.1, q.2))
    with hΦ
  have hΦm : Measurable Φ := (measurable_Fm κ (T - t) hs).comp
    (((measurable_revPath hT (T - t) (T - t)).comp measurable_fst).prodMk
      ((measurable_Fm κ t ht).comp (((measurable_revPath hT T t).comp measurable_fst).prodMk
        measurable_snd)))
  set D : C(Icc (0 : ℝ) T, ℝ) × ℂ → ℝ := fun q => Real.log ‖Dm κ (T - t) hs
    (revPath hT (T - t) (T - t) q.1, Fm κ t ht (revPath hT T t q.1, q.2))‖ with hD
  have hDm : Measurable D := Real.measurable_log.comp ((measurable_Dm κ (T - t) hs).comp
    (((measurable_revPath hT (T - t) (T - t)).comp measurable_fst).prodMk
      ((measurable_Fm κ t ht).comp (((measurable_revPath hT T t).comp measurable_fst).prodMk
        measurable_snd)))).norm
  have heq : ∀ p, rhsC κ hT ht hs G Q μ p =
      evalReg (ofFun G + p.2) (μ.map fun u => Φ (p.1, u)) + Q * ∫ u, D (p.1, u) ∂μ := by
    intro p
    have hF := measurable_revMap_Wof κ t ht (revPath hT T t p.1)
    have hA := measurable_revMap_Wof κ (T - t) hs (revPath hT (T - t) (T - t) p.1)
    unfold rhsC coordChange
    rw [Measure.map_map hA hF]
    congr 2
    rw [integral_map hF.aemeasurable (show Measurable fun z => Real.log ‖deriv (revMap
      (Wof κ (T - t) hs (revPath hT (T - t) (T - t) p.1)) (T - t)) z‖ from
      Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable]
    refine integral_congr_ae (hμH.mono fun u hu => ?_)
    have hFu : revMap (Wof κ t ht (revPath hT T t p.1)) t u ∈ H :=
      TwoPoint.im_revMap_pos (continuous_Wof κ t ht _) hu ht
    simp only [hD]
    rw [show Fm κ t ht (revPath hT T t p.1, u) = revMap (Wof κ t ht (revPath hT T t p.1)) t u
      from rfl, Dm_eq κ (T - t) hs _ hFu]
  rw [show rhsC κ hT ht hs G Q μ = _ from funext heq]
  exact ((measurable_evalReg_pushΦ μ hΦm).comp (measurable_fst.prodMk
    ((measurable_const_add _).comp measurable_snd))).add
    ((hDm.stronglyMeasurable.integral_prod_right'.measurable.comp measurable_fst).const_mul Q)

/-! ## 3. Fubini over the independent path -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- For every path the law holds; hence along an independent random path. -/
theorem ae_lhsC_eq_rhsC_random (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure μ]
    (hμH : ∀ᵐ z ∂μ, z ∈ H) {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g)
    (hind : IndepFun g X P)
    (hfix : ∀ f : C(Icc (0 : ℝ) T, ℝ), ∀ᵐ ω ∂P,
      lhsC κ hT ht hs G Q μ (f, X ω) = rhsC κ hT ht hs G Q μ (f, X ω)) :
    ∀ᵐ ω ∂P, lhsC κ hT ht hs G Q μ (g ω, X ω) = rhsC κ hT ht hs G Q μ (g ω, X ω) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  exact ae_indep hg hXm hind
    (measurableSet_eq_fun (measurable_lhsC κ hT ht hs G Q μ)
      (measurable_rhsC κ hT ht hs G Q μ hμH)) hfix

end CoordRegComp
end QuantumZipper
