import QuantumZipper.Proofs.Zipper.JointModFixed
import QuantumZipper.Proofs.Zipper.JointModExt
import QuantumZipper.Proofs.Zipper.RegContRandom

/-!
# JOINTMOD, step 4: the random part for the Brownian driver

Standing setup: `B` a Brownian motion, `X` a free-boundary GFF modulo constants, `pathOf B ⟂ X`.
The regularized values `evalReg (X ω) (ν4 (drive κ B ω) T q)` (the free-field part of the raw
values `y_t(fc(c,r))`, `q = (Re c, Im c, log₂ r, t)`) have a modification that is continuous in
`q ∈ ℝ⁴` for **every** `ω`:

```
theorem ae_contMod_evalReg [IsProbabilityMeasure P] (κ : ℝ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {T : ℝ} (hT : 0 < T) :
    ∃ Zr : (Fin 4 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Zr q ω) ∧
      ∀ q, ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν4 (drive κ B ω) T q) atTop
        (𝓝 (Zr q ω))
```

(so in particular `Zr q ω = evalReg (X ω) (ν4 (drive κ B ω) T q)` a.s., as a genuine limit).

Proof: condition on the driver, as in `RegCont.ae_continuousOn_unzippedField`. For a fixed
`1/3`-Hölder path the fixed-driver modification `exists_contMod_ν4` agrees a.s. with the
regularized values at the countably many dyadic parameters (`FrostmanReg.ae_evalReg_eq_frostman`),
so the measurable event `UCD` (dyadic uniform continuity, `JointModExt`) holds and the dyadic
extension `extD` equals the modification. The values are jointly measurable in (path, field)
through `RegCont.PsiKm`, so independence (`CharFun.ae_indep`) transfers the event to the Brownian
driver; Brownian paths are `1/3`-Hölder (`RS.bm_holder`).

Sources: as `RegCont` (Duplantier–Sheffield 2011 Prop. 3.1; Revuz–Yor Ch. I Thm (2.1)); the
conditioning/transfer device is the one of `RegContRandom` (**own elementary argument**).
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint UnzipInvariance RegCont KolmD RegSample

variable {T : ℝ}

/-- The regularized values at the parameter `q`, as a jointly measurable function of
`(path, field)`. -/
def Gm (hT : 0 ≤ T) (κ : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) (q : Fin 4 → ℝ) : ℝ :=
  limUnder atTop fun k => PsiKm hT κ (cen q) (rad q) (tP T q) (tP_mem hT q).1 k p

theorem measurable_Gm (hT : 0 ≤ T) (κ : ℝ) (q : Fin 4 → ℝ) :
    Measurable fun p => Gm hT κ p q :=
  (StronglyMeasurable.limUnder fun k =>
    (measurable_PsiKm hT κ _ _ _ _ k).stronglyMeasurable).measurable

theorem Gm_eq (hT : 0 ≤ T) (κ : ℝ) (q : Fin 4 → ℝ) {f : C(Icc (0 : ℝ) T, ℝ)}
    (hf0 : Wof κ T hT f 0 = 0) (x : FieldSample) :
    Gm hT κ (f, x) q = evalReg x (ν4 (Wof κ T hT f) T q) := by
  unfold Gm evalReg
  congr 1
  funext k
  rw [PsiKm_eq hT κ (cen q) (rad_pos q) (tP_mem hT q) k f hf0 x]
  rfl

/-- The measurable event at the parameter `q`: bad path, or dyadic uniform continuity, the
extension equal to the value at `q`, and convergence of the regularized averages at `q`. -/
def Eq4 (hT : 0 ≤ T) (κ : ℝ) (q : Fin 4 → ℝ) : Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
  ((GoodP hT (1 / 3))ᶜ ×ˢ univ) ∪
    ({p | UCD (Gm hT κ p)} ∩ {p | extD (Gm hT κ p) q = Gm hT κ p q} ∩
      {p | ∃ l, Tendsto (fun k => PsiKm hT κ (cen q) (rad q) (tP T q) (tP_mem hT q).1 k p) atTop
        (𝓝 l)})

theorem measurableSet_Eq4 (hT : 0 ≤ T) (κ : ℝ) (q : Fin 4 → ℝ) : MeasurableSet (Eq4 hT κ q) :=
  ((measurableSet_GoodP hT _).compl.prod MeasurableSet.univ).union
    (((measurableSet_UCD (measurable_Gm hT κ)).inter
      (measurableSet_eq_fun (measurable_extD (measurable_Gm hT κ) q) (measurable_Gm hT κ q))).inter
      (StronglyMeasurable.measurableSet_exists_tendsto fun k =>
        (measurable_PsiKm hT κ _ _ _ _ k).stronglyMeasurable))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **The fibre statement** for a fixed path. -/
theorem ae_fibre4 (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (hT : 0 < T) (κ : ℝ)
    (q : Fin 4 → ℝ) (f : C(Icc (0 : ℝ) T, ℝ)) : ∀ᵐ ω ∂P, (f, X ω) ∈ Eq4 hT.le κ q := by
  by_cases hf : f ∈ GoodP hT.le (1 / 3)
  · have hf0 := Wof_zero_of_GoodP hT.le κ hf
    obtain ⟨C, hC⟩ := hf.2
    have hWc := continuous_Wof κ T hT.le f
    obtain ⟨Y, hYc, hYeq, -⟩ := exists_contMod_ν4 hX hWc hf0 hT (a := 1 / 3) (by norm_num)
      (by norm_num) (by positivity : 0 ≤ Real.sqrt κ * C) (Wof_holder hT.le κ hC)
    have hev : ∀ q', ∀ᵐ ω ∂P, evalReg (X ω) (ν4 (Wof κ T hT.le f) T q') = Y q' ω := by
      intro q'
      obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hWc T
      obtain ⟨i1, f1, b1⟩ := νT_box_facts hWc hf0 (rad_pos q') hM (tP_mem hT.le q') le_rfl le_rfl
      have h1 : ∀ᵐ x ∂ν4 (Wof κ T hT.le f) T q', x ∈ Metric.closedBall (0 : ℂ)
          (revBound (2 * M) T (‖cen q'‖ + rad q')) ∩ Hbar :=
        b1.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
      filter_upwards [FrostmanReg.ae_evalReg_eq_frostman hX (ae_iff.1 h1) f1 (by norm_num),
        hYeq q'] with ω e1 e2
      rw [e1, e2]
    have hconv : ∀ᵐ ω ∂P, ∃ l, Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν4 (Wof κ T hT.le f) T q)
        atTop (𝓝 l) := by
      obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hWc T
      obtain ⟨i1, f1, b1⟩ := νT_box_facts hWc hf0 (rad_pos q) hM (tP_mem hT.le q) le_rfl le_rfl
      have h1 : ∀ᵐ x ∂ν4 (Wof κ T hT.le f) T q, x ∈ Metric.closedBall (0 : ℂ)
          (revBound (2 * M) T (‖cen q‖ + rad q)) ∩ Hbar :=
        b1.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
      filter_upwards [FrostmanReg.ae_tendsto_integral_avgReg_frostman hX (ae_iff.1 h1) f1
        (by norm_num)] with ω h
      exact ⟨_, h⟩
    have hall : ∀ᵐ ω ∂P, ∀ (j : ℕ) (a : Fin 4 → ℤ),
        evalReg (X ω) (ν4 (Wof κ T hT.le f) T (lptD j a)) = Y (lptD j a) ω :=
      ae_all_iff.2 fun j => ae_all_iff.2 fun a => hev _
    filter_upwards [hall, hev q, hconv] with ω h1 h2 h3
    have hG : ∀ q', Gm hT.le κ (f, X ω) q' = evalReg (X ω) (ν4 (Wof κ T hT.le f) T q') :=
      fun q' => Gm_eq hT.le κ q' hf0 (X ω)
    have hgY : ∀ (j : ℕ) (a : Fin 4 → ℤ), Gm hT.le κ (f, X ω) (lptD j a) = Y (lptD j a) ω :=
      fun j a => (hG _).trans (h1 j a)
    refine Or.inr ⟨⟨UCD_of_continuous (hYc ω) hgY,
      (extD_eq_of_continuous (hYc ω) hgY q).trans ((hG q).trans h2).symm⟩, ?_⟩
    obtain ⟨l, hl⟩ := h3
    refine ⟨l, hl.congr fun k => ?_⟩
    rw [PsiKm_eq hT.le κ (cen q) (rad_pos q) (tP_mem hT.le q) k f hf0 (X ω)]
    rfl
  · exact ae_of_all _ fun ω => Or.inl ⟨hf, trivial⟩

/-- The continuous extension of the regularized values (zero off the event `UCD`). -/
def ZE (hT : 0 ≤ T) (κ : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) (q : Fin 4 → ℝ) : ℝ :=
  open Classical in if UCD (Gm hT κ p) then extD (Gm hT κ p) q else 0

theorem continuous_ZE (hT : 0 ≤ T) (κ : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) :
    Continuous (ZE hT κ p) := by
  unfold ZE
  by_cases h : UCD (Gm hT κ p)
  · simp only [h, ↓reduceIte]; exact continuous_extD h
  · simp only [h, ↓reduceIte]; exact continuous_const

theorem measurable_ZE (hT : 0 ≤ T) (κ : ℝ) (q : Fin 4 → ℝ) : Measurable fun p => ZE hT κ p q :=
  Measurable.ite (measurableSet_UCD (measurable_Gm hT κ)) (measurable_extD (measurable_Gm hT κ) q)
    measurable_const

omit [MeasurableSpace Ω] in
theorem ae_pathC_good {B B' : ℝ≥0 → Ω → ℝ} [MeasurableSpace Ω] {P : Measure Ω}
    (hB : IsBrownianReal B P) (hB'c : ∀ ω, Continuous fun t => B' t ω)
    (hB'eq : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) (hT : 0 < T) :
    ∀ᵐ ω ∂P, pathC T B' hB'c ω ∈ GoodP hT.le (1 / 3) := by
  filter_upwards [RS.bm_holder hB (a := 1 / 3) (by norm_num), hB.eval_zero_ae_eq_zero, hB'eq]
    with ω hH h0 heq
  refine pathC_mem_GoodP hT.le hB'c (by rw [heq]; exact h0) ?_
  obtain ⟨C, hC⟩ := hH T.toNNReal
  exact ⟨C, fun t ht s hs0 hs1 => by rw [heq, heq]; exact hC t ht s hs0 hs1⟩

/-- The driver `drive κ B ω` agrees on `[0,T]` with the path of the good version. -/
theorem drive_facts {B B' : ℝ≥0 → Ω → ℝ} (κ : ℝ) (hB'c : ∀ ω, Continuous fun t => B' t ω)
    (hT : 0 < T) {ω : Ω} (heq : ∀ t, B' t ω = B t ω)
    (hf0 : Wof κ T hT.le (pathC T B' hB'c ω) 0 = 0) :
    Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 ∧
      EqOn (drive κ B ω) (Wof κ T hT.le (pathC T B' hB'c ω)) (Icc 0 T) := by
  have hdrive : drive κ B ω = drive κ B' ω := funext fun t => by simp [drive, heq]
  have hEq : EqOn (drive κ B ω) (Wof κ T hT.le (pathC T B' hB'c ω)) (Icc 0 T) := by
    intro t ht
    rw [hdrive]
    simp only [drive, Wof, pathC, ContinuousMap.coe_mk, projIcc_of_mem hT.le ht]
  refine ⟨?_, (hEq ⟨le_rfl, hT.le⟩).trans hf0, hEq⟩
  rw [hdrive]; exact continuous_const.mul ((hB'c ω).comp continuous_real_toNNReal)

/-- The unzipped circles of the random driver and of the path of the good version agree. -/
theorem ν4_drive_eq {B B' : ℝ≥0 → Ω → ℝ} (κ : ℝ) (hB'c : ∀ ω, Continuous fun t => B' t ω)
    (hT : 0 < T) {ω : Ω} (heq : ∀ t, B' t ω = B t ω)
    (hf0 : Wof κ T hT.le (pathC T B' hB'c ω) 0 = 0) (q : Fin 4 → ℝ) :
    ν4 (Wof κ T hT.le (pathC T B' hB'c ω)) T q = ν4 (drive κ B ω) T q := by
  obtain ⟨hdc, hd0, hEq⟩ := drive_facts κ hB'c hT heq hf0
  refine Measure.map_congr ?_
  filter_upwards [foldedCircle_ae_mem_H (cen q) (rad_pos q)] with u hu
  exact (fwdMapInv_congr hdc hd0 (continuous_Wof κ T hT.le _) hf0 hEq (tP_mem hT.le q) hu).symm

/-- **The regularized values converge to `ZE`**, for the good version `B'` of the driver. -/
theorem ae_tendsto_ZE [IsProbabilityMeasure P] (κ : ℝ) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hB'm : ∀ t, Measurable (B' t))
    (hB'c : ∀ ω, Continuous fun t => B' t ω) (hB'eq : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω)
    (hind' : IndepFun (pathC T B' hB'c) X P) (hT : 0 < T) (q : Fin 4 → ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν4 (drive κ B ω) T q) atTop
      (𝓝 (ZE hT.le κ (pathC T B' hB'c ω, X ω) q)) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hE := ae_indep (measurable_pathC T hB'm hB'c) hXm hind' (measurableSet_Eq4 hT.le κ q)
    (fun f => ae_fibre4 hX hT κ q f)
  filter_upwards [hE, ae_pathC_good hB hB'c hB'eq hT, hB'eq] with ω hE hgood heq
  rcases hE with h | ⟨⟨hU, hext⟩, l, hl⟩
  · exact absurd hgood h.1
  set f := pathC T B' hB'c ω with hfdef
  have hU' : UCD (Gm hT.le κ (f, X ω)) := hU
  simp only [ZE, hU', ↓reduceIte]
  have hf0 := Wof_zero_of_GoodP hT.le κ hgood
  have hν := ν4_drive_eq κ hB'c hT heq hf0 q
  have hl' : Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν4 (drive κ B ω) T q) atTop (𝓝 l) := by
    refine hl.congr fun k => ?_
    rw [PsiKm_eq hT.le κ (cen q) (rad_pos q) (tP_mem hT.le q) k f hf0 (X ω), ← hν]
    rfl
  have hlim : Gm hT.le κ (f, X ω) q = l := by
    rw [Gm_eq hT.le κ q hf0, hν]
    exact hl'.limUnder_eq
  have hext' : extD (Gm hT.le κ (f, X ω)) q = Gm hT.le κ (f, X ω) q := hext
  rw [hext', hlim]
  exact hl'

end RegUnif
end QuantumZipper
