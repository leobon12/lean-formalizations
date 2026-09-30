import QuantumZipper.Proofs.Zipper.B2Driver
import QuantumZipper.Proofs.Zipper.B1Full

/-!
# B2(b): the Markov property of the zipped fields at a fixed time

`blueprint/E_BRANCH_BLUEPRINT.md` §4, node B2, clause (b) (notation of `B2Defs`, `B2Driver`).
For `0 ≤ t < T`, `Y_t = unzippedField γ 𝒵 (T − t)`, `N = B1Full.nrm` (normalization at the unit
folded circle), `V^t = Vstop κ T t B` (`u ↦ V (min u t)`) and `W⁰ = W0p κ T B`:

* **`b2_joint`**: `law(lawData (N Y_t), (V^t, W⁰)) = law(lawData (N (𝔥₀ + X)), splitAt t W)`, where
  `splitAt t G = (u ↦ G(t − min u t) − G t, u ↦ G(t+u) − G t)`;
* **`b2_markov`**: `lawData (N Y_t)` is independent of `(V^t, W⁰)`, has the law of
  `lawData (N (𝔥₀ + X))`, and `law(V^t, W⁰) = law(splitAt t W)`.

Proof: `B1Full.b1_full` at time `T − t > 0` (whose driver is `u ↦ W(T−t+u) − W(T−t)`), pushed
forward by `id × splitAt t`; the product form of the right side comes from `B ⊥ X`.

**Deviations from the blueprint text** (reported): (1) the field is normalized (`N Y_t`, i.e.
`lawData` modulo the additive constant), because the constant of `X` is arbitrary
(`IsFreeGFFModConstH`) and B1-FULL is stated modulo constants; every use in E1 goes through
`addConst Y_t (−m)` with `m = h⁰ ϖ = Y_t ϖ_t + q_t`, which is again modulo constants.
(2) `t = T` is excluded: `Y_T = coordChange 𝒵.1 (fwdMapInv W 0) Q` is the *regularization* of
`𝒵.1`, not `𝒵.1` itself (junk-value issue of `coordChange` at the identity), and B1-FULL needs
`T − t > 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B2

open CharFun UnzipInvariance UnzipFull TReg B1Full

/-- The stopped reversed driver `V^t = V (min · t)`, indexed by `ℝ≥0`. -/
def Vstop {Ω : Type*} (κ T t : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ :=
  fun u => Vr κ T B ω (min (u : ℝ) t)

/-- Splitting a path at time `t` into the reversed past (stopped at `t`) and the future
increments. -/
def splitAt (t : ℝ) (G : ℝ≥0 → ℝ) : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (fun u => G (t - min (u : ℝ) t).toNNReal - G t.toNNReal,
    fun u => G (t.toNNReal + u) - G t.toNNReal)

theorem measurable_splitAt (t : ℝ) : Measurable (splitAt t) := by
  unfold splitAt
  exact Measurable.prodMk
    (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _))
    (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _))

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- The driver of the configuration unzipped by `T − t`, split at `t`, is `(V^t, W⁰)`. -/
theorem splitAt_zipDriver (ω : Ω) (ht : 0 ≤ t) (htT : t ≤ T) :
    splitAt t (fun u : ℝ≥0 => (zipCapDown (Real.sqrt κ) (T - t)
      (ofFun (h0rev κ) + X ω, drive κ B ω)).2 u) = (Vstop κ T t B ω, W0p κ T B ω) := by
  refine Prod.ext (funext fun u => ?_) (funext fun u => ?_)
  · have hu : (0 : ℝ) ≤ t - min (u : ℝ) t := sub_nonneg.2 (min_le_right _ _)
    simp only [splitAt, zipCapDown, Vstop, Vr]
    rw [vrev_of_mem ⟨le_min (NNReal.coe_nonneg u) ht, (min_le_right _ _).trans htT⟩, Real.coe_toNNReal _ hu,
      Real.coe_toNNReal _ ht, max_eq_left hu, max_eq_left ht,
      show T - t + (t - min (u : ℝ) t) = T - min (u : ℝ) t by ring, show T - t + t = T by ring]
    ring
  · simp only [splitAt, zipCapDown, W0p, W0, wfut]
    rw [NNReal.coe_add, Real.coe_toNNReal _ ht, max_eq_left (add_nonneg ht (NNReal.coe_nonneg u)), max_eq_left ht,
      max_eq_left (NNReal.coe_nonneg u), show T - t + (t + (u : ℝ)) = T + u by ring, show T - t + t = T by ring]
    ring

/-- A.e.-measurability of the data of `Γ⁰`. -/
theorem aemeasurable_data0 (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) :
    AEMeasurable (fun ω => (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω,
      fun u : ℝ≥0 => drive κ B ω u)) P := by
  obtain ⟨B₁, hB₁m, -, hB₁eq⟩ := exists_good_version hB
  have hY0c : ∀ μ : Measure ℂ, Measurable fun ω => (ofFun (h0rev κ) + X ω) μ := fun μ => by
    simp only [Pi.add_apply]; exact measurable_const.add (hX.measurable_coord μ)
  have hm1 := measurable_lawData_nrm (Y := fun ω => ofFun (h0rev κ) + X ω) (fun _ _ _ => hY0c _)
    (fun ρ => measurable_pairRaw_comp hY0c ρ.1)
  have hm2 : Measurable fun ω (u : ℝ≥0) => drive κ B₁ ω u :=
    measurable_pi_iff.2 fun _ => (hB₁m _).const_mul _
  refine (hm1.prodMk hm2).aemeasurable.congr ?_
  filter_upwards [hB₁eq] with ω hb
  refine Prod.ext rfl (funext fun u => ?_)
  simp only [drive, hb]

/-- A.e.-measurability of the data of `Γ⁰` unzipped by `s ≥ 0` (as in the proof of
`B1Full.b1_full`). -/
theorem aemeasurable_data_unzip (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {s : ℝ} (hs : 0 ≤ s) :
    AEMeasurable (fun ω => (lawData (fun ω => nrm (unzippedField (Real.sqrt κ)
        (ofFun (h0rev κ) + X ω, drive κ B ω) s)) ω,
      fun u : ℝ≥0 => (zipCapDown (Real.sqrt κ) s (ofFun (h0rev κ) + X ω, drive κ B ω)).2 u)) P := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  obtain ⟨B', -, hB'm, hB'c, hind', hEq⟩ := exists_unzip_driver κ hB hind hs
  obtain ⟨g, hg⟩ : ∃ g : Ω → C(Icc (0 : ℝ) s, ℝ), g = pathC s B' hB'c := ⟨_, rfl⟩
  have hgm : Measurable g := hg ▸ measurable_pathC s hB'm hB'c
  have hgood : ∀ᵐ ω ∂P, EqOn (fwdMapInv (drive κ B ω) s) (revMap (Wof κ s hs (g ω)) s) H := by
    filter_upwards [hEq] with ω h
    rwa [revMap_drive_eq κ s hs B' hB'c ω, ← hg] at h
  obtain ⟨B₁, hB₁m, -, hB₁eq⟩ := exists_good_version hB
  have hfcH : ∀ (w : ℂ) {r : ℝ}, 0 < r → foldedCircle w r Hᶜ = 0 := fun w r hr =>
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H w hr)
  obtain ⟨Y1, hY1⟩ : ∃ Y1 : Ω → FieldSample, Y1 = fun ω => coordChange (ofFun (h0rev κ) + X ω)
      (revMap (Wof κ s hs (g ω)) s) (Qc (Real.sqrt κ)) := ⟨_, rfl⟩
  have hY1c : ∀ (w : ℂ) (r : ℝ), 0 < r → Measurable fun ω => Y1 ω (foldedCircle w r) :=
    fun w r hr => by
      have key := (measurable_unzip_apply κ s hs _ (hfcH w hr)).comp (hgm.prodMk hXm)
      simp only [Function.comp_def] at key
      rw [hY1]
      beta_reduce
      exact key
  have hY1p : ∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y1 ω) ρ.1 := fun ρ => by
    have key := (measurable_pair_unzip κ s hs ρ).comp (hgm.prodMk hXm)
    simp only [Function.comp_def] at key
    rw [hY1]
    beta_reduce
    exact key
  have hm1 := measurable_lawData_nrm hY1c hY1p
  have hm2 : Measurable fun ω (u : ℝ≥0) =>
      drive κ B₁ ω (s + max (u : ℝ) 0) - drive κ B₁ ω s :=
    measurable_pi_iff.2 fun _ => ((hB₁m _).const_mul _).sub ((hB₁m _).const_mul _)
  refine (hm1.prodMk hm2).aemeasurable.congr ?_
  filter_upwards [hgood, hB₁eq] with ω hgd hb
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun ρ => ?_)) (funext fun u => ?_)
  · simp only [lawData, unzippedField, hY1]
    rw [coordsFull_nrm, coordsFull_nrm,
      coordChange_congr_of_eqOn hgd (hfcH _ (fullIndex_radius_pos i)),
      coordChange_congr_of_eqOn hgd (hfcH 0 one_pos)]
  · simp only [lawData, unzippedField, hY1]
    rw [pairRaw_nrm, pairRaw_nrm, pairRaw_coordChange_congr hgd,
      coordChange_congr_of_eqOn hgd (hfcH 0 one_pos)]
  · simp only [zipCapDown, drive, hb]

/-- The joint data at time `t` as a pushforward of the B1-FULL data. -/
theorem data_eq_comp (ht : 0 ≤ t) (htT : t ≤ T) :
    (fun ω => (lawData (fun ω => nrm (Yf κ T t B X ω)) ω, (Vstop κ T t B ω, W0p κ T B ω))) =
      Prod.map id (splitAt t) ∘ (fun ω => (lawData (fun ω => nrm (unzippedField (Real.sqrt κ)
        (ofFun (h0rev κ) + X ω, drive κ B ω) (T - t))) ω,
      fun u : ℝ≥0 => (zipCapDown (Real.sqrt κ) (T - t)
        (ofFun (h0rev κ) + X ω, drive κ B ω)).2 u)) := by
  funext ω
  exact Prod.ext rfl (splitAt_zipDriver ω ht htT).symm

/-- **B2(b), joint law.** -/
theorem b2_joint (hκ : 0 < κ) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t < T) :
    P.map (fun ω => (lawData (fun ω => nrm (Yf κ T t B X ω)) ω,
        (Vstop κ T t B ω, W0p κ T B ω))) =
      P.map (fun ω => (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω,
        splitAt t (fun u : ℝ≥0 => drive κ B ω u))) := by
  have hs : 0 < T - t := sub_pos.2 htT
  have hb := b1_full κ hκ P B X hB hX hind hs
  have hg : Measurable (Prod.map (id : (ℕ → ℝ) × (TestFun H → ℝ) → _) (splitAt t)) :=
    measurable_id.prodMap (measurable_splitAt t)
  rw [data_eq_comp ht htT.le, ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable
    (aemeasurable_data_unzip hB hX hind hs.le), hb,
    AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (aemeasurable_data0 hB hX)]
  rfl

/-- **B2(b), Markov property at a fixed time `t ∈ [0,T)`.** `lawData (N Y_t)` is independent
of `(V^t, W⁰)`, has the law of `lawData (N (𝔥₀ + X))`, and `(V^t, W⁰)` has the law of
`splitAt t W`. -/
theorem b2_markov (hκ : 0 < κ) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t < T) :
    IndepFun (fun ω => lawData (fun ω => nrm (Yf κ T t B X ω)) ω)
        (fun ω => (Vstop κ T t B ω, W0p κ T B ω)) P ∧
      P.map (fun ω => lawData (fun ω => nrm (Yf κ T t B X ω)) ω) =
        P.map (fun ω => lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω) ∧
      P.map (fun ω => (Vstop κ T t B ω, W0p κ T B ω)) =
        P.map (fun ω => splitAt t (fun u : ℝ≥0 => drive κ B ω u)) := by
  have hJ := b2_joint hκ hB hX hind ht htT
  have hg : Measurable (Prod.map (id : (ℕ → ℝ) × (TestFun H → ℝ) → _) (splitAt t)) :=
    measurable_id.prodMap (measurable_splitAt t)
  have hfg : AEMeasurable (fun ω => (lawData (fun ω => nrm (Yf κ T t B X ω)) ω,
      (Vstop κ T t B ω, W0p κ T B ω))) P := by
    rw [data_eq_comp ht htT.le]
    exact hg.comp_aemeasurable (aemeasurable_data_unzip hB hX hind (sub_pos.2 htT).le)
  have hfg0 : AEMeasurable (fun ω => (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω,
      splitAt t (fun u : ℝ≥0 => drive κ B ω u))) P :=
    hg.comp_aemeasurable (aemeasurable_data0 hB hX)
  -- independence on the right side
  have hF₀ : Measurable (lawData (fun x : FieldSample => nrm (ofFun (h0rev κ) + x))) := by
    have hc : ∀ μ : Measure ℂ, Measurable fun x : FieldSample => (ofFun (h0rev κ) + x) μ :=
      fun μ => by simp only [Pi.add_apply]; exact measurable_const.add (measurable_pi_apply μ)
    exact measurable_lawData_nrm (fun _ _ _ => hc _) (fun ρ => measurable_pairRaw_comp hc ρ.1)
  have hD : Measurable fun p : ℝ≥0 → ℝ => fun u : ℝ≥0 => Real.sqrt κ * p (u : ℝ).toNNReal :=
    measurable_pi_iff.2 fun _ => (measurable_pi_apply _).const_mul _
  have hind0 : IndepFun (fun ω => lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω)
      (fun ω => splitAt t (fun u : ℝ≥0 => drive κ B ω u)) P :=
    (hind.comp ((measurable_splitAt t).comp hD) hF₀).symm
  have hprod0 := (indepFun_iff_map_prod_eq_prod_map_map hfg0.fst hfg0.snd).1 hind0
  -- marginals
  have hm1 : P.map (fun ω => lawData (fun ω => nrm (Yf κ T t B X ω)) ω) =
      P.map (fun ω => lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω) := by
    have := congrArg (Measure.map Prod.fst) hJ
    rwa [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hfg,
      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hfg0] at this
  have hm2 : P.map (fun ω => (Vstop κ T t B ω, W0p κ T B ω)) =
      P.map (fun ω => splitAt t (fun u : ℝ≥0 => drive κ B ω u)) := by
    have := congrArg (Measure.map Prod.snd) hJ
    rwa [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hfg,
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hfg0] at this
  refine ⟨(indepFun_iff_map_prod_eq_prod_map_map hfg.fst hfg.snd).2 ?_, hm1, hm2⟩
  rw [hJ, hprod0, hm1, hm2]

/-! ## B2(b), `RegEq` clause: reduction to regularity of `Y_t` at pushed circles -/

/-- **B2(b), `RegEq` clause, pathwise reduction.** At every `ω` with a continuous Brownian path
starting at `0`: if the raw values of `Y_t` at the pushed dyadic folded circles
`(fc_i).map (revMap V t)` are its regularized values, then
`RegEq h⁰ (coordChange Y_t (revMap V t) Q)`. The hypothesis is the RC3 composition statement
(`evalReg` of an unzipped field at the image of a folded circle under a reverse map), which is
not proved here (owner RC23, `CoordReg*`). -/
theorem h0f_regEq_of_regular {ω : Ω} (hc : Continuous fun s => B s ω) (h0 : B 0 ω = 0)
    (ht : 0 ≤ t) (htT : t ≤ T)
    (hreg : ∀ i : ℕ, evalReg (Yf κ T t B X ω) ((foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2).map (revMap (Vr κ T B ω) t)) =
      Yf κ T t B X ω ((foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2).map (revMap (Vr κ T B ω) t))) :
    RegEq (h0f κ T B X ω) (coordChange (Yf κ T t B X ω) (revMap (Vr κ T B ω) t)
      (Qc (Real.sqrt κ))) := by
  refine regEq_of_coordsFull (funext fun i => ?_)
  show h0f κ T B X ω (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
    coordChange (Yf κ T t B X ω) (revMap (Vr κ T B ω) t) (Qc (Real.sqrt κ))
      (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)
  rw [h0f_fc_split hc h0 ht htT _ (fullIndex_radius_pos i)]
  unfold coordChange qt
  rw [hreg i]

end B2
end QuantumZipper
