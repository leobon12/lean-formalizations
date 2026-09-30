import QuantumZipper.Proofs.Section5.Prop16WedgeLocLaw
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.LQG.WedgeRestriction
import QuantumZipper.Proofs.LQG.GoodMeasurableReg

/-!
# WEDGE-LAW (1): the reference law of a quantum wedge does not depend on the witness

`Prop16Asm.RefWedgeLawUnique γ α`: for two reference tuples `(X, A)` on `(Ω, P)` and `(X', A')`
on `(Ω', P')` (free field modulo constants, independent `α`-wedge radial process), the reference
fields `canonical γ (h† + Q(−log|·|) + A_{−log|·|})` have the same `fieldLawFull H` law.
In the paper this is implicit in the definition of the wedge (Sheffield, arXiv:1012.4797,
§1.6, (1.10); Duplantier–Miller–Sheffield, arXiv:1409.7055, Def. 4.5: the wedge is *defined* by
the law of this construction). The Lean proof, for `0 < γ < 2`, `α < Q`:

1. **Canonical data from coordinates.** On the a.s. good event (`LogSingGood.wedgeRefGoodAS_holds`)
   the data of `canonical γ W` is `Dγ (coordsFull W)` for a fixed measurable `Dγ`
   (`WedgeMeas.canonical_eq_resc`, `WedgeMeas.scaleG_coords`).
2. **Coordinates from (lateral Gaussian family, radial path).** A.s.
   `coordsFull W = Φ (L, A)` where `L n = X(fcN n) − X(radSmear (fcN n))` is a countable family
   of balanced Gaussian differences (`WedgeTK.latCoords_X_ae`) and `A` is the (a.s. continuous)
   radial path, read through the measurable dyadic extension `extP` (own elementary device).
3. **Laws.** `L` and `A` are independent (functions of `X` and of `A`); the law of `L` is fixed by
   its covariances (`WedgeRes.map_gaussFam_eq₂`: finite-dimensional distributions determine the
   law, Kallenberg, *Foundations of Modern Probability*, 2nd ed., Prop. 3.2 / Thm. 6.16, used
   through mathlib's projective-limit uniqueness); the law of `A` is the image of two independent
   Brownian path laws (`WedgeRes.map_path_eq`) under `wedgePath`, measurable on pairs of
   continuous paths (`WedgeMeas.measurable_wedgePath_joint`).

Own bookkeeping on top of the cited project results (the law identities are the standard
"finite-dimensional distributions determine the law" and "independence gives the product law").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace WedgeLaw

open CoordsFull

/-! ## 1. A measurable continuous extension of a path from dyadic points -/

/-- The path `a` read at the dyadic roundings `dyadicRound k t → t`. Equal to `a` for
continuous `a`, and jointly measurable in `(a, t)` for the product σ-algebra on paths. -/
def extP (a : ℝ → ℝ) (t : ℝ) : ℝ := limUnder atTop fun k : ℕ => a (dyadicRound k t)

theorem measurable_extP : Measurable fun p : (ℝ → ℝ) × ℝ => extP p.1 p.2 := by
  have hk : ∀ k : ℕ, Measurable fun p : (ℝ → ℝ) × ℝ => p.1 (dyadicRound k p.2) := by
    intro k
    have hg : Measurable fun q : (ℝ → ℝ) × ℤ => q.1 ((q.2 : ℝ) / (2 : ℝ) ^ k) :=
      measurable_from_prod_countable_left fun m => by
        exact measurable_pi_apply ((m : ℝ) / (2 : ℝ) ^ k)
    have hfl : Measurable fun t : ℝ => ⌊(2 : ℝ) ^ k * t⌋ :=
      Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ k))
    exact hg.comp (measurable_fst.prodMk (hfl.comp measurable_snd))
  exact (StronglyMeasurable.limUnder fun k => (hk k).stronglyMeasurable).measurable

theorem extP_of_continuous {a : ℝ → ℝ} (ha : Continuous a) : extP a = a := by
  funext t
  exact ((ha.tendsto t).comp (GoodMeas.tendsto_dyadicRound' t)).limUnder_eq

/-! ## 2. The coordinate map `Φ` and the canonical data map `Dγ` -/

/-- Coordinates of `wedgeField y a Q` from the lateral coordinates `l` of `y` and the path `a`. -/
def Phi (Q : ℝ) (p : (ℕ → ℝ) × (ℝ → ℝ)) : ℕ → ℝ := fun n =>
  p.1 n + ∫ z, (Q * (-Real.log ‖z‖) + extP p.2 (-Real.log ‖z‖)) ∂(WedgeTK.fcN n)

theorem measurable_Phi (Q : ℝ) : Measurable (Phi Q) := by
  refine measurable_pi_iff.2 fun n => ((measurable_pi_apply n).comp measurable_fst).add ?_
  have := (WedgeTK.fcN_admissible n).1
  have hlog : Measurable fun q : ((ℕ → ℝ) × (ℝ → ℝ)) × ℂ => -Real.log ‖q.2‖ :=
    (Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg
  have hf : Measurable fun q : ((ℕ → ℝ) × (ℝ → ℝ)) × ℂ =>
      Q * (-Real.log ‖q.2‖) + extP q.1.2 (-Real.log ‖q.2‖) :=
    (measurable_const.mul hlog).add
      (measurable_extP.comp ((measurable_snd.comp measurable_fst).prodMk hlog))
  exact (StronglyMeasurable.integral_prod_right' (ν := WedgeTK.fcN n) hf.stronglyMeasurable).measurable

/-- The `fieldLawFull` data of `canonical γ x`, as a function of `coordsFull x` (good `x`). -/
def Dg (γ : ℝ) (c : ℕ → ℝ) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  WedgeMeas.dataFull H (WedgeMeas.resc (Qc γ) (WedgeCan4.piC c,
    WedgeMeas.scaleG γ (WedgeCan4.piC c)))

theorem measurable_Dg (γ : ℝ) : Measurable (Dg γ) :=
  (WedgeMeas.measurable_dataFull_resc H (Qc γ)).comp (WedgeCan4.measurable_piC.prodMk
    ((WedgeMeas.measurable_scaleG γ).comp WedgeCan4.measurable_piC))

theorem dataFull_canonical_of_good {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    WedgeMeas.dataFull H (canonical γ x) = Dg γ (coordsFull x) := by
  simp only [Dg, WedgeCan4.piC_coordsFull, WedgeMeas.scaleG_coords hx,
    WedgeMeas.canonical_eq_resc]

/-! ## 3. Per-witness representation -/

/-- The lateral Gaussian family `n ↦ X(fcN n) − X(radSmear (fcN n))`. -/
def latL {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : ℕ → ℝ :=
  fun n => WedgeTK.gaussFam X (WedgeTK.latPairId ∘ Sum.inl) n ω

/-- The radial path. -/
def pathA {Ω : Type*} (A : ℝ → Ω → ℝ) (ω : Ω) : ℝ → ℝ := fun t => A t ω

/-- Pairs of continuous paths (the natural domain of `wedgePath`). -/
abbrev CPair : Type := {q : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) // Continuous q.1 ∧ Continuous q.2}

/-- The wedge path of a pair of continuous paths. -/
def wS (α Q : ℝ) (q : CPair) : ℝ → ℝ := wedgePath α Q q.1.1 q.1.2

theorem measurable_wS (α Q : ℝ) : Measurable (wS α Q) := by
  have h := WedgeMeas.measurable_wedgePath_joint (Ω := CPair) α Q
    (B := fun s q => q.1.1 s) (B' := fun s q => q.1.2 s) (fun q => q.2.1) (fun q => q.2.2)
    (fun s => (measurable_pi_apply s).comp (measurable_fst.comp measurable_subtype_coe))
    (fun s => (measurable_pi_apply s).comp (measurable_snd.comp measurable_subtype_coe))
  exact measurable_pi_iff.2 fun t => h.comp (measurable_id.prodMk measurable_const)

/-- Two measures on a subtype with the same image in the ambient space are equal (the subtype
σ-algebra is the comap one). -/
theorem subtype_measure_eq {β : Type*} [MeasurableSpace β] {p : β → Prop}
    {μ ν : Measure (Subtype p)}
    (h : μ.map Subtype.val = ν.map Subtype.val) : μ = ν := by
  ext t ht
  obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht
  rw [← Measure.map_apply measurable_subtype_coe hu, h,
    Measure.map_apply measurable_subtype_coe hu]

section Witness

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem measurable_latL [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    Measurable (latL X) :=
  WedgeTK.measurable_gaussFam_pi hX _

theorem ae_coordsFull_eq [IsProbabilityMeasure P] {X : Ω → FieldSample} {A : ℝ → Ω → ℝ}
    {α Q : ℝ} (hX : IsFreeGFFModConstH X P) (hA : IsWedgeProcess α Q A P) :
    ∀ᵐ ω ∂P, coordsFull (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q) =
      Phi Q (latL X ω, pathA A ω) := by
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hlat : ∀ᵐ ω ∂P, ∀ n : ℕ, lateralPart (X ω) (WedgeTK.fcN n) = latL X ω n :=
    ae_all_iff.2 fun n => (WedgeTK.latCoords_X_ae hX hG (Sum.inl n)).mono fun ω h => h
  filter_upwards [hlat, WedgeCan4.ae_continuous_wedgeProcess hA] with ω h1 h2
  funext n
  have e : extP (pathA A ω) = fun t => A t ω := extP_of_continuous h2
  simp only [Phi, e]
  show lateralPart (X ω) (WedgeTK.fcN n) + _ = _
  rw [h1 n]
  rfl

/-- A measurable reading of the radial path through a pair of continuous Brownian paths. -/
theorem exists_path_rep {A : ℝ → Ω → ℝ} {α Q : ℝ} (hA : IsWedgeProcess α Q A P) :
    ∃ ι : Ω → CPair, Measurable ι ∧ (pathA A =ᵐ[P] wS α Q ∘ ι) ∧
      ∃ B B' : ℝ≥0 → Ω → ℝ, IsPreBrownianReal B P ∧ IsPreBrownianReal B' P ∧
        Measurable (fun ω s => B s ω) ∧ Measurable (fun ω s => B' s ω) ∧
        IndepFun (fun ω s => B s ω) (fun ω s => B' s ω) P ∧
        ∀ ω, (ι ω).1 = ((fun s => B s ω), (fun s => B' s ω)) := by
  obtain ⟨B, B', hB, hB', hind, hAB⟩ := hA
  obtain ⟨Bt, hBtm, hBtc, hBtB⟩ := WedgeRes.exists_good_version hB
  obtain ⟨Bt', hBtm', hBtc', hBtB'⟩ := WedgeRes.exists_good_version hB'
  have hpm : Measurable fun ω s => Bt s ω :=
    measurable_pi_iff.2 fun s => hBtm.comp (measurable_const.prodMk measurable_id)
  have hpm' : Measurable fun ω s => Bt' s ω :=
    measurable_pi_iff.2 fun s => hBtm'.comp (measurable_const.prodMk measurable_id)
  refine ⟨fun ω => ⟨((fun s => Bt s ω), (fun s => Bt' s ω)), hBtc ω, hBtc' ω⟩,
    (hpm.prodMk hpm').subtype_mk, ?_, Bt, Bt', ?_, ?_, hpm, hpm', ?_, fun ω => rfl⟩
  · filter_upwards [hBtB, hBtB'] with ω h1 h2
    funext t
    have e1 : (fun s => B s ω) = fun s => Bt s ω := funext fun s => (h1 s).symm
    have e2 : (fun s => B' s ω) = fun s => Bt' s ω := funext fun s => (h2 s).symm
    show A t ω = wedgePath α Q (fun s => Bt s ω) (fun s => Bt' s ω) t
    rw [hAB ω t, e1, e2]
  · exact hB.toIsPreBrownianReal.congr fun s => (hBtB.mono fun ω h => (h s).symm)
  · exact hB'.toIsPreBrownianReal.congr fun s => (hBtB'.mono fun ω h => (h s).symm)
  · exact hind.congr (hBtB.mono fun ω h => funext fun s => (h s).symm)
      (hBtB'.mono fun ω h => funext fun s => (h s).symm)

theorem aemeasurable_pathA {A : ℝ → Ω → ℝ} {α Q : ℝ} (hA : IsWedgeProcess α Q A P) :
    AEMeasurable (pathA A) P := by
  obtain ⟨ι, hι, hae, -⟩ := exists_path_rep hA
  exact ((measurable_wS α Q).comp hι).aemeasurable.congr hae.symm

end Witness

/-! ## 4. Cross-witness law identities -/

section Cross

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

theorem map_latL_eq {X : Ω → FieldSample} {X' : Ω' → FieldSample}
    (hX : IsFreeGFFModConstH X P) (hX' : IsFreeGFFModConstH X' P') :
    P.map (latL X) = P'.map (latL X') :=
  WedgeRes.map_gaussFam_eq₂ hX hX' _

theorem map_pathA_eq {A : ℝ → Ω → ℝ} {A' : ℝ → Ω' → ℝ} {α Q : ℝ}
    (hA : IsWedgeProcess α Q A P) (hA' : IsWedgeProcess α Q A' P') :
    P.map (pathA A) = P'.map (pathA A') := by
  obtain ⟨ι, hι, hae, B, B', hB, hB', hBm, hB'm, hI, hιv⟩ := exists_path_rep hA
  obtain ⟨κ, hκ, hae', C, C', hC, hC', hCm, hC'm, hJ, hκv⟩ := exists_path_rep hA'
  have hv : P.map (Subtype.val ∘ ι) = P'.map (Subtype.val ∘ κ) := by
    have e : Subtype.val ∘ ι = fun ω => ((fun s => B s ω), (fun s => B' s ω)) := funext hιv
    have e' : Subtype.val ∘ κ = fun ω => ((fun s => C s ω), (fun s => C' s ω)) := funext hκv
    rw [e, e', (indepFun_iff_map_prod_eq_prod_map_map hBm.aemeasurable hB'm.aemeasurable).1 hI,
      (indepFun_iff_map_prod_eq_prod_map_map hCm.aemeasurable hC'm.aemeasurable).1 hJ,
      WedgeRes.map_path_eq hB hC hBm hCm, WedgeRes.map_path_eq hB' hC' hB'm hC'm]
  have hικ : P.map ι = P'.map κ := subtype_measure_eq (by
    rw [Measure.map_map measurable_subtype_coe hι, Measure.map_map measurable_subtype_coe hκ, hv])
  rw [Measure.map_congr hae, Measure.map_congr hae', ← Measure.map_map (measurable_wS α Q) hι,
    ← Measure.map_map (measurable_wS α Q) hκ, hικ]

end Cross

/-- **The reference law through the two independent inputs.** -/
theorem fieldLawFull_wedgeRef_eq {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} (hX : IsFreeGFFModConstH X P)
    (hA : IsWedgeProcess α (Qc γ) A P) (hI : IndepFun X (fun ω t => A t ω) P) :
    fieldLawFull H (WedgeMeas.wedgeRef γ X A) P =
      (((P.map (latL X)).prod (P.map (pathA A))).map (Phi (Qc γ))).map (Dg γ) := by
  have hgood := LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω _ P X A inferInstance hX hA hI
  have hrep := ae_coordsFull_eq hX hA
  have hLm := measurable_latL hX
  have hAm := aemeasurable_pathA hA
  have hφ : Measurable fun x : FieldSample => fun n : ℕ =>
      x ((WedgeTK.latPairId ∘ Sum.inl) n).1.1 - x ((WedgeTK.latPairId ∘ Sum.inl) n).1.2 :=
    measurable_pi_iff.2 fun n => (measurable_pi_apply _).sub (measurable_pi_apply _)
  have hLA : IndepFun (latL X) (pathA A) P := hI.comp hφ measurable_id
  have hpairm : AEMeasurable (fun ω => (latL X ω, pathA A ω)) P := hLm.aemeasurable.prodMk hAm
  have hpair : P.map (fun ω => (latL X ω, pathA A ω)) =
      (P.map (latL X)).prod (P.map (pathA A)) :=
    (indepFun_iff_map_prod_eq_prod_map_map hLm.aemeasurable hAm).1 hLA
  have hΦp : AEMeasurable (Phi (Qc γ) ∘ fun ω => (latL X ω, pathA A ω)) P :=
    (measurable_Phi _).comp_aemeasurable hpairm
  have e : fieldLawFull H (WedgeMeas.wedgeRef γ X A) P =
      P.map (Dg γ ∘ (Phi (Qc γ) ∘ fun ω => (latL X ω, pathA A ω))) := by
    show P.map (fun ω => WedgeMeas.dataFull H (WedgeMeas.wedgeRef γ X A ω)) = _
    refine Measure.map_congr ?_
    filter_upwards [hgood, hrep] with ω h1 h2
    simp only [Function.comp, WedgeMeas.wedgeRef]
    rw [← h2]
    exact dataFull_canonical_of_good h1
  rw [e, ← AEMeasurable.map_map_of_aemeasurable (measurable_Dg γ).aemeasurable hΦp,
    ← AEMeasurable.map_map_of_aemeasurable (measurable_Phi _).aemeasurable hpairm, hpair]

end WedgeLaw

/-- **`RefWedgeLawUnique` holds** (`0 < γ < 2`, `α < Q`): all reference tuples of
`IsQuantumWedge γ α` give the same `fieldLawFull H` law. -/
theorem Prop16Asm.refWedgeLawUnique_holds {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < Qc γ) : Prop16Asm.RefWedgeLawUnique γ α := by
  intro Ω Ω' _ _ P P' X A X' A' hP hX hA hI hP' hX' hA' hI'
  rw [WedgeLaw.fieldLawFull_wedgeRef_eq hγ hγ2 hα hX hA hI,
    WedgeLaw.fieldLawFull_wedgeRef_eq hγ hγ2 hα hX' hA' hI',
    WedgeLaw.map_latL_eq hX hX', WedgeLaw.map_pathA_eq hA hA']

end QuantumZipper
