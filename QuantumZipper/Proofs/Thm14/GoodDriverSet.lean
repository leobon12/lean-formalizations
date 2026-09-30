import QuantumZipper.Proofs.Thm14.WeldingData
import QuantumZipper.Proofs.Thm12.CharFun

/-!
# Theorem 1.4(b): a Borel set of good drivers of full measure

Sheffield, *Conformal weldings of random surfaces*, §1.4 (blueprint node C1).

The blueprint facts (`RohdeSchrammSimple`, `RohdeSchrammHolder`, `JonesSmirnovRemovable`) give
almost sure properties of the driver `√κ B` on an arbitrary probability space. To get a
*Borel* set of paths of full law, we realize them on the product space
`C([0,T], ℝ) × Ω` with the measure `μ_T ⊗ P`, where `μ_T` is the law of `B|[0,T]`, and the glued
process `f(t ∧ T) + B_t − B_{t∧T}` (`glue`), which is a Brownian motion (`isBrownianReal_glue`):
its finite-dimensional laws are those of `B`, because `B|[0,T]` is independent of the increments
after `T` (weak Markov property). Fubini then gives `μ_T`-almost every path good, hence a Borel
set of good paths of full `μ_T`-measure (`exists_goodDriverSet`).
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper

namespace Thm14GoodDriverSet

/-- The good properties of a driver on `[0,T]`: it starts at `0`, its reverse hull at time `T` is
a simple curve whose doubled closure is removable, and the forward hulls of the time-reversed
increment on `[0,T]` are the initial arcs of one simple chord. -/
def GoodDriver (T : ℝ) (W : ℝ → ℝ) : Prop :=
  W 0 = 0 ∧ IsSimpleCurveHull (revHull W T) ∧
    IsConformallyRemovable (closure (revHull W T) ∪ conj '' closure (revHull W T)) ∧
    ∃ η : ℝ → ℂ, IsSimpleChord η ∧
      ∀ s ∈ Icc (0 : ℝ) T, fwdHull (fun r => W (T - r) - W T) s = η '' Ioc 0 s

theorem goodDriver_congr {T : ℝ} (hT : 0 ≤ T) {W W' : ℝ → ℝ} (hW : Continuous W)
    (hW' : Continuous W') (h : EqOn W W' (Icc 0 T)) (hg : GoodDriver T W) : GoodDriver T W' := by
  obtain ⟨h0, hK, hrem, η, hη, hhull⟩ := hg
  have hr : revMap W T = revMap W' T := funext fun z => ReverseFlow.revMap_congr_drive z h
  have hrh : revHull W T = revHull W' T := by unfold revHull; rw [hr]
  refine ⟨by rw [← h ⟨le_rfl, hT⟩]; exact h0, hrh ▸ hK, hrh ▸ hrem, η, hη, fun s hs => ?_⟩
  rw [← hhull s hs]
  refine Thm14FromThm13.fwdHull_eq_of_eqOn (by fun_prop) (by fun_prop) hs.1 fun r hr => ?_
  show W' (T - r) - W' T = W (T - r) - W T
  rw [h ⟨by linarith [hr.2, hs.2], by linarith [hr.1]⟩, h ⟨hT, le_rfl⟩]

/-! ### The glued Brownian motion -/

section Glue

variable {Ω : Type*} (T : ℝ) (hT : 0 ≤ T)

/-- `f(t ∧ T) + B_t − B_{t∧T}` on `C([0,T], ℝ) × Ω`, written with the shifted process
`B_{T+s} − B_T` evaluated at `s = t − T` (truncated subtraction). -/
def glue (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (x : C(Icc (0 : ℝ) T, ℝ) × Ω) : ℝ :=
  x.1 (projIcc 0 T hT t) + (B (T.toNNReal + (t - T.toNNReal)) x.2 - B T.toNNReal x.2)

theorem toNNReal_projIcc (t : ℝ≥0) :
    ((projIcc 0 T hT (t : ℝ) : ℝ)).toNNReal = min t T.toNNReal := by
  rcases le_total (t : ℝ) T with h | h
  · rw [projIcc_of_mem hT ⟨t.coe_nonneg, h⟩, Real.toNNReal_coe,
      min_eq_left ((Real.le_toNNReal_iff_coe_le hT).2 h)]
  · rw [projIcc_of_right_le hT h, min_eq_right]
    exact (Real.toNNReal_le_iff_le_coe).2 h

theorem glue_pathC (B : ℝ≥0 → Ω → ℝ) (hBc : ∀ ω, Continuous fun t => B t ω) (t : ℝ≥0)
    (ω : Ω) : glue T hT B t (CharFun.pathC T B hBc ω, ω) = B t ω := by
  simp only [glue, CharFun.pathC, ContinuousMap.coe_mk]
  rw [toNNReal_projIcc T hT t]
  rcases le_total t T.toNNReal with h | h
  · rw [min_eq_left h, tsub_eq_zero_of_le h, add_zero]
    ring
  · rw [min_eq_right h, add_tsub_cancel_of_le h]
    ring

/-- **The glued process is a Brownian motion** under `μ_T ⊗ P`. -/
theorem isBrownianReal_glue [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) :
    IsBrownianReal (glue T hT B) ((P.map (CharFun.pathC T B hBc)).prod P) := by
  set g := CharFun.pathC T B hBc with hg_def
  have hg : Measurable g := CharFun.measurable_pathC T hBm hBc
  set T' := T.toNNReal with hT'
  let S : Ω → (ℝ≥0 → ℝ) := fun ω s => B (T' + s) ω - B T' ω
  have hS : Measurable S := measurable_pi_iff.2 fun s => (hBm _).sub (hBm _)
  -- independence of the path on `[0,T]` and the increments after `T`
  have hind : IndepFun g S P := by
    have h0 := (hB.toIsPreBrownianReal.indepFun_shift T').symm
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at h0 ⊢
    intro s t hs ht
    have key : ∃ s', MeasurableSet s' ∧
        (fun ω (r : Iic T') => B r ω) ⁻¹' s' = g ⁻¹' s := by
      let _ : MeasurableSpace Ω :=
        MeasurableSpace.comap (fun ω (r : Iic T') => B r ω) MeasurableSpace.pi
      have hgm : Measurable g := ContinuousMap.measurable_iff_eval.2 fun x =>
        show Measurable ((fun h : Iic T' → ℝ =>
            h ⟨x.1.toNNReal, Real.toNNReal_le_toNNReal x.2.2⟩) ∘
            (fun ω (r : Iic T') => B r ω)) from
          (measurable_pi_apply _).comp (comap_measurable _)
      exact hgm hs
    obtain ⟨s', hs', hpre⟩ := key
    rw [← hpre]
    exact h0 s' t hs' ht
  have hjoint : P.map (fun ω => (g ω, S ω)) = (P.map g).prod (P.map S) :=
    (indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hS.aemeasurable).1 hind
  refine ⟨IsPreBrownianReal.mk' fun I => ?_, ae_of_all _ fun x => ?_⟩
  · let R : C(Icc (0 : ℝ) T, ℝ) × (ℝ≥0 → ℝ) → (I → ℝ) :=
      fun p i => p.1 (projIcc 0 T hT (i : ℝ≥0)) + p.2 ((i : ℝ≥0) - T')
    have hR : Measurable R := measurable_pi_iff.2 fun i =>
      ((continuous_eval_const _).measurable.comp measurable_fst).add
        ((measurable_pi_apply _).comp measurable_snd)
    have hfun : (fun x : C(Icc (0 : ℝ) T, ℝ) × Ω => I.restrict (glue T hT B · x)) =
        R ∘ Prod.map id S := rfl
    have hmS : Measurable (Prod.map (id : C(Icc (0 : ℝ) T, ℝ) → _) S) :=
      measurable_id.prodMap hS
    refine ⟨(hR.comp hmS).aemeasurable, ?_⟩
    rw [hfun, ← Measure.map_map hR hmS, ← Measure.map_prod_map _ _ measurable_id hS,
      Measure.map_id, ← hjoint, Measure.map_map hR (hg.prodMk hS)]
    have hcomp : R ∘ (fun ω => (g ω, S ω)) = fun ω => I.restrict (B · ω) := by
      funext ω i
      exact glue_pathC T hT B hBc i ω
    rw [hcomp]
    exact (hB.hasLaw I).map_eq
  · show Continuous fun t : ℝ≥0 => x.1 (projIcc 0 T hT (t : ℝ)) +
      (B ((T' + (t - T') : ℝ≥0)) x.2 - B T' x.2)
    have hc := hBc x.2
    have h1 : Continuous fun t : ℝ≥0 => x.1 (projIcc 0 T hT (t : ℝ)) :=
      x.1.continuous.comp (continuous_projIcc.comp NNReal.continuous_coe)
    have h2 : Continuous fun t : ℝ≥0 => B (T' + (t - T')) x.2 :=
      hc.comp (continuous_const.add (continuous_id.sub continuous_const))
    exact h1.add (h2.sub continuous_const)

end Glue

/-! ### The good set -/

/-- The drive of the glued process agrees on `[0,T]` with `√κ` times the path. -/
theorem drive_glue_eqOn {Ω : Type*} {T : ℝ} (hT : 0 ≤ T) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (x : C(Icc (0 : ℝ) T, ℝ) × Ω) :
    EqOn (drive κ (glue T hT B) x) (CharFun.Wof κ T hT x.1) (Icc 0 T) := by
  intro r hr
  have hle : r.toNNReal ≤ T.toNNReal := Real.toNNReal_le_toNNReal hr.2
  simp only [drive, glue, CharFun.Wof, tsub_eq_zero_of_le hle, add_zero, sub_self,
    Real.coe_toNNReal _ hr.1]

/-- Almost every Brownian driver is good (on any probability space). -/
theorem ae_goodDriver (hRSS : Blueprint.RohdeSchrammSimple) (hRSH : Blueprint.RohdeSchrammHolder)
    (hJS : Blueprint.JonesSmirnovRemovable) {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ GoodDriver T (drive κ B ω) := by
  have hB' := Thm14FromThm13.isBrownianReal_revBM hB T.toNNReal
  filter_upwards [Thm14WeldingData.ae_good_drive hRSS hRSH hJS hκ0 hκ4 hT P B hB,
    hRSS κ hκ0 hκ4.le P _ hB', hB'.cont] with ω ⟨hc, h0, hK, hrem⟩ ⟨hchord, hhull⟩ hc'
  refine ⟨hc, h0, hK, hrem, _, hchord, fun s hs => ?_⟩
  rw [← hhull s hs.1]
  refine Thm14FromThm13.fwdHull_eq_of_eqOn (by fun_prop)
    (Thm14FromThm13.continuous_drive hc') hs.1 fun r hr => ?_
  exact Thm14FromThm13.drive_revBM B ω ⟨hr.1, hr.2.trans hs.2⟩

/-- **A Borel set of good drivers of full measure.** For a Brownian motion `B` there is a Borel
set `G` of paths on `[0,T]`, all of which are good drivers, containing the restriction of the
driver `√κ B` to `[0,T]` almost surely. -/
theorem exists_goodDriverSet (hRSS : Blueprint.RohdeSchrammSimple)
    (hRSH : Blueprint.RohdeSchrammHolder) (hJS : Blueprint.JonesSmirnovRemovable) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ} (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ G : Set C(Icc (0 : ℝ) T, ℝ), MeasurableSet G ∧
      (∀ g ∈ G, GoodDriver T (extIccPath hT.le g)) ∧
      ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ Thm14WeldingData.pathC T (drive κ B ω) ∈ G := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB'B : IsBrownianReal B' P :=
    { toIsPreBrownianReal := hB.toIsPreBrownianReal.congr fun t => by
        filter_upwards [hB'eq] with ω hω using (hω t).symm
      cont := ae_of_all _ hB'c }
  set g := CharFun.pathC T B' hB'c with hg_def
  have hg : Measurable g := CharFun.measurable_pathC T hB'm hB'c
  set μ := P.map g with hμ
  have : IsProbabilityMeasure μ := inferInstance
  -- the good paths form a `μ`-conull set
  have hglue := isBrownianReal_glue T hT.le hB'B hB'm hB'c
  have hae0 := ae_goodDriver hRSS hRSH hJS hκ0 hκ4 hT (μ.prod P) _ hglue
  have hae1 : ∀ᵐ f ∂μ, GoodDriver T (CharFun.Wof κ T hT.le f) := by
    have h := Measure.ae_ae_of_ae_prod (p := fun x => GoodDriver T (CharFun.Wof κ T hT.le x.1))
      (hae0.mono fun x ⟨hc, hgood⟩ => goodDriver_congr hT.le hc
        (CharFun.continuous_Wof κ T hT.le x.1) (drive_glue_eqOn hT.le κ B' x) hgood)
    filter_upwards [h] with f hf
    exact hf.exists.choose_spec
  set G₀ := (toMeasurable μ {f | ¬ GoodDriver T (CharFun.Wof κ T hT.le f)})ᶜ with hG₀
  have hG₀m : MeasurableSet G₀ := (measurableSet_toMeasurable _ _).compl
  have hG₀good : ∀ f ∈ G₀, GoodDriver T (CharFun.Wof κ T hT.le f) := fun f hf => by
    by_contra h
    exact hf (subset_toMeasurable _ _ h)
  have hG₀ae : ∀ᵐ f ∂μ, f ∈ G₀ := by
    refine compl_mem_ae_iff.2 ?_
    rw [measure_toMeasurable]
    exact ae_iff.1 hae1
  have hG₀P : ∀ᵐ ω ∂P, g ω ∈ G₀ := (ae_map_iff hg.aemeasurable hG₀m).1 hG₀ae
  -- rescale by `√κ`
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ0
  refine ⟨(fun h : C(Icc (0 : ℝ) T, ℝ) => (Real.sqrt κ)⁻¹ • h) ⁻¹' G₀,
    (continuous_const_smul _).measurable hG₀m, fun h hh => ?_, ?_⟩
  · refine goodDriver_congr hT.le (CharFun.continuous_Wof κ T hT.le _)
      (continuous_extIccPath hT.le h) (fun r _ => ?_) (hG₀good _ hh)
    simp only [CharFun.Wof, extIccPath, ContinuousMap.smul_apply, smul_eq_mul]
    field_simp
  · filter_upwards [hG₀P, hB'eq, hB.cont] with ω hω heq hc
    have hdc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
    refine ⟨hdc, ?_⟩
    have hpath : (Real.sqrt κ)⁻¹ • Thm14WeldingData.pathC T (drive κ B ω) = g ω := by
      ext x
      simp only [Thm14WeldingData.pathC, hdc, dite_true, ContinuousMap.smul_apply,
        ContinuousMap.coe_mk, smul_eq_mul, hg_def, CharFun.pathC, drive, heq]
      field_simp
    show (Real.sqrt κ)⁻¹ • Thm14WeldingData.pathC T (drive κ B ω) ∈ G₀
    rw [hpath]
    exact hω

end Thm14GoodDriverSet

end QuantumZipper
