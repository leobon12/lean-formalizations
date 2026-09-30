import QuantumZipper.Proofs.Zipper.WedgeShiftHit
import QuantumZipper.Proofs.Zipper.WedgeAddConstReembed
import QuantumZipper.Proofs.Zipper.WedgeAddConstLat
import QuantumZipper.Proofs.Wire5

/-!
# WEDGE-SHIFT (2): the translation node `WedgeShiftLawStmt` from a deterministic re-centring node

Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*, arXiv:1409.7055,
proof of Prop. 4.7(i), p. 77 (adding a constant to the wedge field and re-embedding at the first
time the radial part hits a level gives the same law); Sheffield, arXiv:1012.4797, §1.6.

With `Z = wedgeField (lateralPart X) A Q`, `c > 0`, `T` the first time `A ≤ -c` and
`b = e^{-T}`, the field `Z + (m + c)` rescaled by `b` is, at the level of regularized averages,

  `W' = wedgeField (lateralPart (rescale X Q b)) (A(T + ·) + c) Q + m`

(**node `WedgeShiftRegStmt`**, a deterministic identity on an a.s. event, stated for every
re-centring time `s` at once). Given the node, the law identity follows:

1. the canonical data of `Z + (m+c)` and of its rescaling by `b` agree a.s. (as in the
   re-embedding node, `coordsFull_canonical_rescale`, `pairRaw_canonical_rescale_addConst`), and the
   latter is the canonical data of `W'` (`Factorization.canonical_congr`);
2. `(A(T+·)+c, lateral part of rescale X Q e^{-T})` has the law of `(A, lateral part of X)`:
   `T`, `A(T+·)+c` are measurable functions of the path of `A` (`hitT`, `shiftPath`), the lateral
   part of `rescale X Q f(U)` has the law of that of `X` jointly with the independent `U`
   (`map_prod_lateralData_rescale_indep`), and `A(T+·)+c` has the law of `A`
   (`Wire5.wedge_translation_uncond`);
3. equal coordinate laws give equal canonical data laws (`F1.B4d.map_dataFull_canonical_eq`).

Own bookkeeping argument around the cited project results.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1

open Factorization CoordsFull

/-- **Node: the re-centring identity.** A.s., for every re-centring time `s` and constants
`k, c`: rescaling `Z + (k + c)` by `e^{-s}` gives, at the level of regularized averages, the wedge
field of the rescaled lateral part and the re-centred radial path `A(s + ·) + c`, plus `k`. -/
def WedgeShiftRegStmt (γ α : ℝ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ), IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ᵐ ω ∂P', ∀ s k c : ℝ, RegEq
      (rescale (addConst (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) (k + c))
        (Qc γ) (Real.exp (-s)))
      (addConst (wedgeField (lateralPart (rescale (X ω) (Qc γ) (Real.exp (-s))))
        (fun t => A (s + t) ω + c) (Qc γ)) k)

section Law

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {A : ℝ → Ω → ℝ}

/-- The coordinates of `wedgeField y a Q + m` for a continuous `a`. -/
def coordsWm (Q m : ℝ) (p : (ℕ → ℝ) × (ℝ → ℝ)) : ℕ → ℝ := fun j => B4d.coordsW Q p j + m

theorem measurable_coordsWm (Q m : ℝ) : Measurable (coordsWm Q m) :=
  measurable_pi_iff.2 fun j => ((measurable_pi_apply j).comp (B4d.measurable_coordsW Q)).add_const m

theorem coords_addConst_wedgeField (y : FieldSample) {a : ℝ → ℝ} (ha : Continuous a) (Q m : ℝ) :
    coords (addConst (wedgeField y a Q) m) = coordsWm Q m (coordsFull y, a) := by
  rw [coords_addConst, B4d.coords_wedgeField_eq y ha Q]
  rfl

theorem measurable_rescale_hit {Q c : ℝ} (hXm : Measurable X) {U : Ω → ℝ → ℝ}
    (hUm : Measurable U) (μ : Measure ℂ) (hμ : IsFiniteMeasure μ) :
    Measurable fun ω => rescale (X ω) Q (Real.exp (-(hitT c (U ω)))) μ := by
  have := hμ
  have hfm : Measurable fun a : ℝ → ℝ => Real.exp (-(hitT c a)) :=
    (measurable_hitT c).neg.exp
  exact Measurable.comp (g := fun p : FieldSample × ℝ => rescale p.1 Q p.2 μ)
    (f := fun ω => (X ω, Real.exp (-(hitT c (U ω)))))
    (Prop16Area.measurable_rescale_apply_joint Q μ) (hXm.prodMk (hfm.comp hUm))

/-- **Step 2: the joint law of the re-centred inputs.** -/
theorem map_pair_shift_eq {α Q c : ℝ} (hX : IsFreeGFFModConstH X P) (hA : IsWedgeProcess α Q A P)
    (hαQ : α < Q) (hc : 0 < c) (hI : IndepFun X (fun ω t => A t ω) P) {U : Ω → ℝ → ℝ}
    (hUm : Measurable U) (hUe : (fun ω t => A t ω) =ᵐ[P] U) :
    P.map (fun ω => (coordsFull (lateralPart (rescale (X ω) Q (Real.exp (-(hitT c (U ω)))))),
        shiftPath c (U ω))) =
      P.map (fun ω => (coordsFull (lateralPart (X ω)), fun t => A t ω)) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hIU : IndepFun U X P := hI.symm.congr hUe EventuallyEq.rfl
  have hfm : Measurable fun a : ℝ → ℝ => Real.exp (-(hitT c a)) :=
    (measurable_hitT c).neg.exp
  have hY := measurable_rescale_hit (Q := Q) (c := c) hXm hUm
  have h := map_prod_lateralData_rescale_indep hX hUm hIU hfm (fun u => Real.exp_pos _) Q
  set g : (ℝ → ℝ) × ((ℕ → ℝ) × (TestFun H → ℝ)) → (ℕ → ℝ) × (ℝ → ℝ) :=
    fun q => (q.2.1, shiftPath c q.1) with hg
  have hgm : Measurable g :=
    (measurable_fst.comp measurable_snd).prodMk ((measurable_shiftPath c).comp measurable_fst)
  have hm1 := hUm.prodMk (B4d.measurable_latData hY)
  have hm2 := hUm.prodMk (B4d.measurable_latData (Y := X) fun μ _ => hX.measurable_coord μ)
  have h' := congrArg (Measure.map g) h
  rw [Measure.map_map hgm hm1, Measure.map_map hgm hm2] at h'
  refine h'.trans ?_
  -- independence and the translation law
  have hL : Measurable fun ω => coordsFull (lateralPart (X ω)) := B4d.measurable_latId.comp hXm
  have hS : Measurable fun ω => shiftPath c (U ω) := (measurable_shiftPath c).comp hUm
  have hA' : AEMeasurable (fun ω t => A t ω) P := WedgeLaw.aemeasurable_pathA hA
  have i1 : IndepFun (fun ω => coordsFull (lateralPart (X ω))) (fun ω => shiftPath c (U ω)) P :=
    hIU.symm.comp B4d.measurable_latId (measurable_shiftPath c)
  have i2 : IndepFun (fun ω => coordsFull (lateralPart (X ω))) (fun ω t => A t ω) P :=
    hI.comp B4d.measurable_latId measurable_id
  have hlaw : P.map (fun ω => shiftPath c (U ω)) = P.map (fun ω t => A t ω) := by
    rw [← Wire5.wedge_translation_uncond hA hαQ hc]
    refine Measure.map_congr ?_
    filter_upwards [hUe, WedgeCan4.ae_continuous_wedgeProcess hA] with ω h1 h2
    rw [← h1, shiftPath_eq_of_continuous' h2]
  show P.map (fun ω => (coordsFull (lateralPart (X ω)), shiftPath c (U ω))) = _
  rw [(indepFun_iff_map_prod_eq_prod_map_map hL.aemeasurable hS.aemeasurable).1 i1,
    (indepFun_iff_map_prod_eq_prod_map_map hL.aemeasurable hA').1 i2, hlaw]

end Law

/-- **The translation node from the re-centring node.** -/
theorem wedgeShiftLawStmt_of_reg {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    (hR : WedgeShiftRegStmt γ α) : WedgeShiftLawStmt γ α := by
  intro Ω' _ P' _ X A hX hA hI m c hc
  have hUa : AEMeasurable (fun ω t => A t ω) P' := WedgeLaw.aemeasurable_pathA hA
  set U := hUa.mk _ with hU
  have hUm : Measurable U := hUa.measurable_mk
  have hUe : (fun ω t => A t ω) =ᵐ[P'] U := hUa.ae_eq_mk
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  set W' : Ω' → FieldSample := fun ω => addConst (wedgeField (lateralPart (rescale (X ω) (Qc γ)
    (Real.exp (-(hitT c (U ω)))))) (shiftPath c (U ω)) (Qc γ)) m with hW'
  have hcont := WedgeCan4.ae_continuous_wedgeProcess hA
  have hgood : ∀ᵐ ω ∂P', U ω = (fun t => A t ω) ∧ Continuous (U ω) := by
    filter_upwards [hUe, hcont] with ω h1 h2
    exact ⟨h1.symm, h1 ▸ h2⟩
  -- coordinates and their laws
  have hpair1 : Measurable fun ω => (coordsFull (lateralPart (rescale (X ω) (Qc γ)
      (Real.exp (-(hitT c (U ω)))))), shiftPath c (U ω)) :=
    (B4d.measurable_latData (measurable_rescale_hit hXm hUm)).fst.prodMk
      ((measurable_shiftPath c).comp hUm)
  have hpair2 : AEMeasurable (fun ω => (coordsFull (lateralPart (X ω)), fun t => A t ω)) P' :=
    (B4d.measurable_latId.comp hXm).aemeasurable.prodMk hUa
  have e1 : (fun ω => coords (W' ω)) =ᵐ[P'] (coordsWm (Qc γ) m ∘ fun ω =>
      (coordsFull (lateralPart (rescale (X ω) (Qc γ) (Real.exp (-(hitT c (U ω)))))),
        shiftPath c (U ω))) := by
    filter_upwards [hgood] with ω h
    exact coords_addConst_wedgeField _ (continuous_shiftPath h.2) _ m
  have e2 : (fun ω => coords (wedgeShift γ X A m ω)) =ᵐ[P'] (coordsWm (Qc γ) m ∘ fun ω =>
      (coordsFull (lateralPart (X ω)), fun t => A t ω)) := by
    filter_upwards [hcont] with ω h
    exact coords_addConst_wedgeField _ h _ m
  have hc1 : AEMeasurable (fun ω => coords (W' ω)) P' :=
    ((measurable_coordsWm (Qc γ) m).comp hpair1).aemeasurable.congr e1.symm
  have hc2 : AEMeasurable (fun ω => coords (wedgeShift γ X A m ω)) P' :=
    ((measurable_coordsWm (Qc γ) m).comp_aemeasurable hpair2).congr e2.symm
  have hlaw : P'.map (fun ω => coords (W' ω)) =
      P'.map (fun ω => coords (wedgeShift γ X A m ω)) := by
    rw [Measure.map_congr e1, Measure.map_congr e2,
      ← Measure.map_map (measurable_coordsWm _ m) hpair1,
      ← AEMeasurable.map_map_of_aemeasurable (measurable_coordsWm _ m).aemeasurable hpair2,
      map_pair_shift_eq hX hA hα hc hI hUm hUe]
  have hZg : ∀ᵐ ω ∂P', IsLQGGood γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) :=
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A inferInstance hX hA hI
  have hZmg : ∀ᵐ ω ∂P', IsLQGGood γ (wedgeShift γ X A m ω) := hZg.mono fun ω h => h.addConst m
  have hW'g := B4d.ae_good_of_map_coords_eq hc1 hc2 hlaw hZmg
  rw [← B4d.map_dataFull_canonical_eq hc1 hc2 hlaw hZmg]
  -- the shifted field `Z + (m + c)` against `W'`
  have hZp := Wire2.ae_hasAreaProfile_wedgeField hγ hγ2 hα hX hA hI
  have hZc : AEMeasurable (fun ω =>
      coords (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) P' :=
    WedgeMeas.aemeasurable_coords_wedgeField hX.measurable_coord hA
  have hadd : Measurable fun v : ℕ → ℝ => fun j => v j + (m + c) := by fun_prop
  have hc3 : AEMeasurable (fun ω => coords (wedgeShift γ X A (m + c) ω)) P' :=
    (hadd.comp_aemeasurable hZc).congr (ae_of_all _ fun ω => (coords_addConst _ (m + c)).symm)
  have hf := WedgeMeas.aemeasurable_dataFull_canonical hc1 hW'g H
  have hg := WedgeMeas.aemeasurable_dataFull_canonical hc3
    (hZg.mono fun ω h => h.addConst (m + c)) H
  have hcan : ∀ᵐ ω ∂P', canonical γ (W' ω) = canonical γ (rescale (wedgeShift γ X A (m + c) ω)
      (Qc γ) (Real.exp (-(hitT c (U ω))))) := by
    filter_upwards [hR P' X A hX hA hI, hgood] with ω hn hu
    have ew : W' ω = addConst (wedgeField (lateralPart (rescale (X ω) (Qc γ)
        (Real.exp (-(hitT c (U ω)))))) (fun t => A (hitT c (U ω) + t) ω + c) (Qc γ)) m := by
      simp only [hW', shiftPath_eq_of_continuous hu.2]
      congr 3
      funext t
      rw [congrFun hu.1 (hitT c (U ω) + t)]
    rw [ew]
    refine (Factorization.canonical_congr ?_ γ).symm
    funext k z
    exact hn (hitT c (U ω)) m c k z
  refine S5.FieldLaw.Raw.map_prod_eq_of_ae hf hg ?_ fun ρ => ?_
  · filter_upwards [hZg, hZp, hcan] with ω hg hp hce
    have hsy := (CanonicalGood.scaleParam_spec (hasAreaProfile_addConst hg hp (m + c))).1
    show coordsFull (canonical γ (W' ω)) =
      coordsFull (canonical γ (wedgeShift γ X A (m + c) ω))
    rw [hce]
    exact coordsFull_canonical_rescale hγ (hg.addConst (m + c)) (Real.exp_pos _) hsy
  · filter_upwards [hZg, hZp, hcan, ae_contPair_plain hX hcont (Qc γ) ρ] with ω hg hp hce hcl
    have hsy := (CanonicalGood.scaleParam_spec (hasAreaProfile_addConst hg hp (m + c))).1
    obtain ⟨F, hF⟩ := hg.1
    show pairRaw (canonical γ (W' ω)) ρ.1 =
      pairRaw (canonical γ (wedgeShift γ X A (m + c) ω)) ρ.1
    rw [hce]
    exact pairRaw_canonical_rescale_addConst hγ hF.congr_evalReg (hg.addConst (m + c))
      (Real.exp_pos _) hsy ρ (hcl _ hsy)

/-- **Field-level B4(c) from the re-centring node.** -/
theorem wedgeAddConstLawStmt_of_reg
    (hR : ∀ γ α : ℝ, 0 < γ → γ < 2 → α < Qc γ → WedgeShiftRegStmt γ α) :
    WedgeAddConstLawStmt :=
  wedgeAddConstLawStmt_of_shift fun γ α hγ hγ2 hα =>
    wedgeShiftLawStmt_of_reg hγ hγ2 hα (hR γ α hγ hγ2 hα)

end F1
end QuantumZipper
