import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.Section5.Prop16MeasCoords

/-!
# WEDGE-ADDCONST (3): scale invariance of the lateral part under an independent random factor

Input of the translation step of B4(c) (Sheffield, arXiv:1012.4797, §1.6 and §5.4: the lateral
part `h†` of a free-boundary GFF is scale invariant and independent of the radial part;
Duplantier–Miller–Sheffield, arXiv:1409.7055, §4.1 and the proof of Prop. 4.6, where the field is
re-centred at the first hitting radius of the radial part and the lateral part, being independent
of that radius, keeps its law).

`WedgeTK.fieldLawFull_lateralPart_rescale` gives, for each **fixed** `a > 0`, that the lateral
part of `rescale X Q a` has the law of the lateral part of `X`. Here the factor is random,
`a = f (U)`, with `U` independent of `X`: then `(U, lateral coordinates of rescale X Q (f U))` has
the joint law of `(U, lateral coordinates of X)` (`map_prod_latCoords_rescale_indep`,
`map_prod_lateralData_rescale_indep`). Proof: disintegration of the product law along `U`
(`map_prod_mk_dep`: if every section `x ↦ g (u, x)` pushes `ν` to the same `ν₀`, then
`(u, x) ↦ (u, g (u, x))` pushes `μ ⊗ ν` to `μ ⊗ ν₀`), joint measurability of
`(x, a) ↦ rescale x Q a` (`Prop16Area.measurable_rescale_apply_joint`).

Own elementary argument (conditioning on an independent variable, rectangle computation).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace QuantumZipper
namespace F1

open WedgeTK

/-- **Disintegration along the first factor.** If every section `x ↦ g (u, x)` pushes `ν`
forward to the same law `ν₀`, then `(u, x) ↦ (u, g (u, x))` pushes `μ ⊗ ν` to `μ ⊗ ν₀`. -/
theorem map_prod_mk_dep {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μ : Measure β) (ν : Measure γ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : β × γ → δ} (hg : Measurable g) (ν₀ : Measure δ)
    [IsProbabilityMeasure ν₀] (h : ∀ u, ν.map (fun x => g (u, x)) = ν₀) :
    (μ.prod ν).map (fun q => (q.1, g q)) = μ.prod ν₀ := by
  have hm : Measurable fun q : β × γ => (q.1, g q) := measurable_fst.prodMk hg
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hm (hs.prod ht), Measure.prod_apply (hm (hs.prod ht))]
  have e : ∀ u, ν (Prod.mk u ⁻¹' ((fun q : β × γ => (q.1, g q)) ⁻¹' s ×ˢ t)) =
      s.indicator (fun _ => ν₀ t) u := by
    intro u
    by_cases hu : u ∈ s
    · rw [indicator_of_mem hu, ← h u, Measure.map_apply
        (show Measurable fun x => g (u, x) from hg.comp measurable_prodMk_left) ht]
      congr 1
      ext x
      simp [hu]
    · rw [indicator_of_notMem hu]
      have : Prod.mk u ⁻¹' ((fun q : β × γ => (q.1, g q)) ⁻¹' s ×ˢ t) = ∅ := by
        ext x
        simp [hu]
      rw [this, measure_empty]
  simp_rw [e]
  rw [lintegral_indicator_const hs, mul_comm]

/-- The lateral coordinates of `rescale x Q a`, jointly in `(x, a)`. -/
def latRes (Q : ℝ) (p : FieldSample × ℝ) : LatIdx → ℝ :=
  latCoords (fun p : FieldSample × ℝ => rescale p.1 Q p.2) p

theorem measurable_latRes (Q : ℝ) : Measurable (latRes Q) :=
  measurable_latCoords fun μ hμ => by
    haveI := hμ
    exact Prop16Area.measurable_rescale_apply_joint Q μ

theorem measurable_latCoords_id : Measurable (latCoords (id : FieldSample → FieldSample)) :=
  measurable_latCoords fun μ _ => measurable_pi_apply μ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- Fixed-scale invariance, in lateral coordinates. -/
theorem map_latCoords_rescale (hX : IsFreeGFFModConstH X P) (Q : ℝ) {a : ℝ} (ha : 0 < a) :
    P.map (latCoords fun ω => rescale (X ω) Q a) = P.map (latCoords X) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hm1 : Measurable (latCoords fun ω => rescale (X ω) Q a) :=
    measurable_latCoords fun μ hμ => by
      haveI := hμ
      exact Measurable.comp (g := fun p : FieldSample × ℝ => rescale p.1 Q p.2 μ)
        (f := fun ω => (X ω, a)) (Prop16Area.measurable_rescale_apply_joint Q μ)
        (hXm.prodMk measurable_const)
  have hm2 : Measurable (latCoords X) := measurable_latCoords fun μ _ => hX.measurable_coord μ
  have h := fieldLawFull_lateralPart_rescale hX Q ha
  rw [fieldLawFull_eq_map_latCoords hm1, fieldLawFull_eq_map_latCoords hm2] at h
  have h' := congrArg (Measure.map (MeasurableEquiv.sumPiEquivProdPi fun _ : LatIdx => ℝ).symm) h
  simpa only [MeasurableEquiv.map_symm_map] using h'

/-- **Random-scale invariance of the lateral part.** If `U` is independent of the free field
`X` and `f > 0` is measurable, then `(U, latCoords (rescale X Q (f U)))` has the joint law of
`(U, latCoords X)`. -/
theorem map_prod_latCoords_rescale_indep (hX : IsFreeGFFModConstH X P) {β : Type*}
    [MeasurableSpace β] {U : Ω → β} (hU : Measurable U) (hI : IndepFun U X P) {f : β → ℝ}
    (hf : Measurable f) (hpos : ∀ u, 0 < f u) (Q : ℝ) :
    P.map (fun ω => (U ω, latRes Q (X ω, f (U ω)))) = P.map (fun ω => (U ω, latCoords X ω)) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hjoint : P.map (fun ω => (U ω, X ω)) = (P.map U).prod (P.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hXm.aemeasurable).1 hI
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hXm.aemeasurable).2 inferInstance
  have hm2 : Measurable (latCoords X) := measurable_latCoords fun μ _ => hX.measurable_coord μ
  have : IsProbabilityMeasure (P.map (latCoords X)) :=
    (Measure.isProbabilityMeasure_map_iff hm2.aemeasurable).2 inferInstance
  have hg1 : Measurable fun q : β × FieldSample => latRes Q (q.2, f q.1) :=
    (measurable_latRes Q).comp (measurable_snd.prodMk (hf.comp measurable_fst))
  have hg2 : Measurable fun q : β × FieldSample => latCoords id q.2 :=
    measurable_latCoords_id.comp measurable_snd
  have hUX : Measurable fun ω => (U ω, X ω) := hU.prodMk hXm
  have e1 : P.map (fun ω => (U ω, latRes Q (X ω, f (U ω)))) =
      (P.map fun ω => (U ω, X ω)).map fun q => (q.1, latRes Q (q.2, f q.1)) := by
    rw [Measure.map_map (measurable_fst.prodMk hg1) hUX]; rfl
  have e2 : P.map (fun ω => (U ω, latCoords X ω)) =
      (P.map fun ω => (U ω, X ω)).map fun q => (q.1, latCoords id q.2) := by
    rw [Measure.map_map (measurable_fst.prodMk hg2) hUX]; rfl
  rw [e1, e2, hjoint]
  rw [map_prod_mk_dep (P.map U) (P.map X) hg1 (P.map (latCoords X)) fun u => ?_,
    map_prod_mk_dep (P.map U) (P.map X) hg2 (P.map (latCoords X)) fun u => ?_]
  · rw [Measure.map_map measurable_latCoords_id hXm]; rfl
  · have hmu : Measurable fun x : FieldSample => latRes Q (x, f u) :=
      (measurable_latRes Q).comp (measurable_id.prodMk measurable_const)
    rw [show (fun x : FieldSample => latRes Q ((u, x).2, f (u, x).1)) =
      fun x => latRes Q (x, f u) from rfl, Measure.map_map hmu hXm]
    exact map_latCoords_rescale hX Q (hpos u)

/-- The same, in the coordinates `dataFull H` read by `fieldLawFull H`. -/
theorem map_prod_lateralData_rescale_indep (hX : IsFreeGFFModConstH X P) {β : Type*}
    [MeasurableSpace β] {U : Ω → β} (hU : Measurable U) (hI : IndepFun U X P) {f : β → ℝ}
    (hf : Measurable f) (hpos : ∀ u, 0 < f u) (Q : ℝ) :
    P.map (fun ω => (U ω, (CoordsFull.coordsFull (lateralPart (rescale (X ω) Q (f (U ω)))),
        fun ρ : TestFun H => pairRaw (lateralPart (rescale (X ω) Q (f (U ω)))) ρ.1))) =
      P.map (fun ω => (U ω, (CoordsFull.coordsFull (lateralPart (X ω)),
        fun ρ : TestFun H => pairRaw (lateralPart (X ω)) ρ.1))) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  set e := MeasurableEquiv.sumPiEquivProdPi fun _ : LatIdx => ℝ
  have hm : Measurable fun q : β × (LatIdx → ℝ) => (q.1, e q.2) :=
    measurable_fst.prodMk (e.measurable.comp measurable_snd)
  have h := congrArg (Measure.map fun q : β × (LatIdx → ℝ) => (q.1, e q.2))
    (map_prod_latCoords_rescale_indep hX hU hI hf hpos Q)
  have hg1 : Measurable fun ω => (U ω, latRes Q (X ω, f (U ω))) :=
    hU.prodMk ((measurable_latRes Q).comp (hXm.prodMk (hf.comp hU)))
  have hg2 : Measurable fun ω => (U ω, latCoords X ω) :=
    hU.prodMk (measurable_latCoords fun μ _ => hX.measurable_coord μ)
  rw [Measure.map_map hm hg1, Measure.map_map hm hg2] at h
  exact h

end F1
end QuantumZipper
