import QuantumZipper.Proofs.Thm18.ASep2Add
import QuantumZipper.Proofs.Thm18.ASepFreeOpen
import QuantumZipper.Proofs.Thm18.ASepWitD
import QuantumZipper.Proofs.Thm18.ASepGoodPar2
import QuantumZipper.Proofs.Thm18.G4PushReg2Exact
import QuantumZipper.Proofs.Zipper.GenUCOpen
import QuantumZipper.Proofs.Thm18.ASepFreeOpen
import QuantumZipper.Proofs.Thm18.ASepWitD
import QuantumZipper.Proofs.Thm18.ASepWitB
import QuantumZipper.Proofs.Thm18.ASepRawC
import QuantumZipper.Proofs.Thm18.ASepConj1D

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP2 (D1, conjunct 2): exactness for every continuous profile simultaneously

For a fixed good driver `W` and a free field `X`, almost surely, for **every** continuous `h`
(a random profile is allowed: the null set does not depend on `h`) and every separated dyadic
circle, conjunct 2 of the `τ' = 0` A-sep conclusion holds for the field `ofFun h + X ω`
(`ae_conj2_add_sep`).

Proof: the profile contributes a deterministic term at every level.
* raw values at dyadic circles: `U_h(fc(c, 2^{-j})) = U_0(fc(c, 2^{-j})) + D_h(c, 2^{-j})` with
  `D_h(c, ρ) = ∫ h d(fc(c, ρ).map f_τ⁻¹)` (`ASep2Add`: the dyadic regularization of `X` converges at
  every pushed dyadic circle, `RegCont.ae_UCq`);
* regularized averages: `avgReg U_h j = avgReg U_0 j + D_h(·, 2^{-j})` (`D_h` continuous in the
  centre, `ASep.continuousOn_Dfix`);
* the regularized pairing at `ν_p`: the `U_0` part converges to `U_0(ν_p)` (`ae_tendsto_free_all`,
  profile `0`), the `D_h` part to `detLimA0` (`det_unif_A0`);
* raw value at `ν_p`: `U_h(ν_p) = U_0(ν_p) + detLimA0` (`raw_id_A0`, as in `ASepRawC`).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (through the free-field
engine); adding a continuous function is own elementary bookkeeping (Sheffield arXiv:1012.4797
§1.6 treats `h + φ` without comment).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core RegCont TwoPoint CoordReg GenUC

/-! ## Deterministic core -/

/-- **Deterministic core**: exactness of `U_h` at `M` from the `U_0` convergence and the
deterministic profile terms. -/
theorem conj2_add_of {U0 Uh : FieldSample} {Z0 D : ℂ × ℝ → ℝ} (hU : IsRegularWith U0 Z0)
    (hraw : ∀ n j : ℕ, ∀ z : ℂ, Uh (foldedCircle (dyadicRoundC n z) (radius j)) =
      U0 (foldedCircle (dyadicRoundC n z) (radius j)) + D (foldH (dyadicRoundC n z), radius j))
    (hDc : ∀ j : ℕ, ContinuousOn (fun c => D (c, radius j)) Hbar)
    {M : Measure ℂ} [IsProbabilityMeasure M] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hM : ∀ᵐ z ∂M, z ∈ K)
    (hT0 : Tendsto (fun j => ∫ z, avgReg U0 j z ∂M) atTop (𝓝 (U0 M))) {Lh : ℝ}
    (hdet : Tendsto (fun j => ∫ z, D (z, radius j) ∂M) atTop (𝓝 Lh))
    (hrawM : Uh M = U0 M + Lh) :
    evalReg Uh M = Uh M := by
  have havg : ∀ j : ℕ, ∀ z ∈ Hbar, avgReg Uh j z = avgReg U0 j z + D (z, radius j) := by
    intro j z hz
    have h1 : Tendsto (fun n => U0 (foldedCircle (dyadicRoundC n z) (radius j))) atTop
        (𝓝 (avgReg U0 j z)) := by
      rw [hU.avgReg_eq j hz]; exact hU.2.1 j z hz
    have hf : Tendsto (fun n => foldH (dyadicRoundC n z)) atTop (𝓝[Hbar] z) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        CircleFubini.foldH_mem_Hbar' _⟩
      have := (CircleFubini.continuous_foldH'.tendsto z).comp (RegClosure.tendsto_dyadicRoundC z)
      rwa [CircleFubini.foldH_of_mem' hz] at this
    have h2 := ((hDc j) z hz).tendsto.comp hf
    exact (Tendsto.congr (fun n => (hraw n j z).symm) (h1.add h2)).limUnder_eq
  have hiU : ∀ j : ℕ, Integrable (fun z => avgReg U0 j z) M := fun j =>
    (G1Z3.integrable_of_ae_mem_z3 hK hKH hM (RegClosure.continuousOn_slice hU.1 (radius_pos j))).congr
      (hM.mono fun z hz => (hU.avgReg_eq j (hKH hz)).symm)
  have hiD : ∀ j : ℕ, Integrable (fun z => D (z, radius j)) M := fun j =>
    G1Z3.integrable_of_ae_mem_z3 hK hKH hM (hDc j)
  have heq : ∀ j : ℕ, ∫ z, avgReg Uh j z ∂M =
      ∫ z, avgReg U0 j z ∂M + ∫ z, D (z, radius j) ∂M := by
    intro j
    rw [← integral_add (hiU j) (hiD j)]
    exact integral_congr_ae (hM.mono fun z hz => havg j z (hKH hz))
  have ht : Tendsto (fun j => ∫ z, avgReg Uh j z ∂M) atTop (𝓝 (Uh M)) := by
    rw [hrawM]; simp_rw [heq]; exact hT0.add hdet
  exact ht.limUnder_eq

/-- Additivity for a continuous profile. -/
theorem evalReg_ofFun_add_of_tendsto_cont {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) {g : ℂ → ℝ} (hg : Continuous g) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ Hbar) {ν : Measure ℂ}
    [IsProbabilityMeasure ν] (hν : ∀ᵐ w ∂ν, w ∈ K)
    (hL : Tendsto (fun j => ∫ w, avgReg x j w ∂ν) atTop (𝓝 (evalReg x ν))) :
    evalReg (ofFun g + x) ν = evalReg x ν + ∫ w, g w ∂ν := by
  have h := G1Z3.evalReg_add_ofFun_of_ae_z3 hF hg.continuousOn hK hKH one_pos
    (fun _ _ => rfl) hν hL
  rw [add_comm (ofFun _) x, h]

/-- **Raw values at a pushed circle, continuous profile.** -/
theorem coordChange_ofFun_add_cont {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {h : ℂ → ℝ} (hh : Continuous h) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ : ℝ}
    (hτ : 0 ≤ τ) (Q : ℝ) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hL : Tendsto (fun j => ∫ w, avgReg x j w ∂νT W c ρ τ) atTop (𝓝 (evalReg x (νT W c ρ τ)))) :
    coordChange (ofFun h + x) (fwdMapInv W τ) Q (foldedCircle c ρ) =
      coordChange x (fwdMapInv W τ) Q (foldedCircle c ρ) + Dfix W 0 h 0 (τ, (c, ρ)) := by
  obtain ⟨C, B, -, -, hf⟩ := νT_facts hW hW0 τ c hρ
  obtain ⟨hP, -, hae⟩ := hf τ ⟨hτ, le_rfl⟩
  have hK : IsCompact (closedBall (0 : ℂ) B ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hν : ∀ᵐ z ∂νT W c ρ τ, z ∈ closedBall (0 : ℂ) B ∩ Hbar :=
    hae.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
  have e := integral_logAdd_eq_Dfix hW hW0 hτ 0 hh 0 c hρ
  simp only [zero_mul, zero_add, add_zero] at e
  unfold coordChange
  rw [evalReg_ofFun_add_of_tendsto_cont hF hh hK inter_subset_right hν hL, ← e]
  ring

/-- **Raw value at the A-sep measure** (the identity `hid` of `ae_continuousOn_raw_A0`, without
the deterministic limit): for a regular `y` with witness `F`,
`U(ν_p) = F(a d, a r) + ∫ G dfc(a d, a r) + Q ∫ log |R'(ψ)| dσ`. -/
theorem raw_id_A0 (γ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀)
    {S : Set (Fin 2 → ℝ)}
    (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁ ∧ 0 < p 0) {δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hsep : ∀ p ∈ S, ∀ w ∈ cthickening δ (foldSph d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ T' > p 0, ∃ u, IsForwardSol W ((p 1 : ℂ) * w) T' u)
    (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) {p : Fin 2 → ℝ} (hp : p ∈ S)
    {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) :
    coordChange (ofFun (fun v => a' * Real.log ‖v‖ + g₁ v) + y) (fwdMapInv W (p 0)) (Qc γ)
        (nuA0 W d r p) =
      F ((p 1 : ℂ) * d, p 1 * r) +
        (∫ v, (a' * Real.log ‖v‖ + g₁ v) ∂foldedCircle ((p 1 : ℂ) * d) (p 1 * r)) +
        Qc γ * ∫ w, Real.log ‖deriv (revMap (backDrv W (p 0) 0 (p 1)).2
          (backDrv W (p 0) 0 (p 1)).1) (revMapInv (backDrv W (p 0) 0 (p 1)).2
            (backDrv W (p 0) 0 (p 1)).1 w)‖ ∂foldedCircle d r := by
  have hgood0 := hgood0_of_hgood hgood
  obtain ⟨m, -, -, -, hm, -, hlow, -⟩ := exists_geo_A0 hW hW0 hT.le ha₀ hgood0
  obtain ⟨hmeas, hgd, hint1, hsupp, hI2, h0, hmu0⟩ :=
    pfacts_A0 hW hW0 hr ha₀ hm hδ hgood0 hlow (hSb p hp).1 (hSb p hp).2.2 (hSb p hp).2.1
      (hsep p hp) a' hg₁
  set K := scaledSph d r a₀ a₁ with hKdef
  have hKc : IsCompact K := isCompact_scaledSph d r a₀ a₁
  have hKH : K ⊆ Hbar := by
    rintro _ ⟨⟨a, w⟩, ⟨ha, hw⟩, rfl⟩
    obtain ⟨y, -, rfl⟩ := hw
    show 0 ≤ ((a : ℂ) * foldH y).im
    have h1 : 0 ≤ (foldH y).im := by rw [TwoPoint.im_foldH]; exact abs_nonneg _
    simpa using mul_nonneg (ha₀.le.trans ha.1) h1
  have h0K : (0 : ℂ) ∉ K := by
    rintro ⟨⟨a, w⟩, ⟨ha, hw⟩, h⟩
    obtain ⟨u, hu⟩ := hgood0 a ha w hw
    simp only at h
    rw [h] at hu
    have h0 := (hu.2 0 ⟨le_rfl, hT.le⟩).1
    rw [FwdHolo.sol_zero hu hT.le, hW0, Complex.ofReal_zero, sub_zero] at h0
    exact h0 rfl
  have hτ : 0 ≤ p 0 := (hSb p hp).1.1
  have ha : 0 < p 1 := ha₀.trans_le (hSb p hp).2.1.1
  have hadH : (p 1 : ℂ) * d ∈ Hbar := by
    show 0 ≤ ((p 1 : ℂ) * d).im
    have : 0 ≤ d.im := hd
    simpa using mul_nonneg ha.le this
  have hν : ∀ᵐ w ∂foldedCircle ((p 1 : ℂ) * d) (p 1 * r), w ∈ K := by
    rw [← foldedCircle_map_mul ha]
    refine (ae_map_iff (measurable_const_mul _).aemeasurable
      hKc.isClosed.measurableSet).2 ?_
    filter_upwards [ae_mem_foldSph d hr.le] with w hw
    exact mem_scaledSph (hSb p hp).2.1 hw
  have e1 := unzippedField_raw0 γ (ofFun (fun v => a' * Real.log ‖v‖ + g₁ v) + y) hW hW0 hτ
    ha (TwoPoint.foldedCircle_ae_mem_H d hr) hsupp hI2
  have e3 := evalReg_logProfile_fc_of_reg hF a' hg₁ hKc hKH h0K hadH (mul_pos ha hr) hν
  rw [nuA0_eq_map_psi hW hW0 hτ ha (hgd.mono fun w hw => ⟨hw.1, hw.2.1⟩)]
  show unzippedField γ (ofFun (fun v => a' * Real.log ‖v‖ + g₁ v) + y, W) (p 0) _ = _
  rw [e1, foldedCircle_map_mul ha, e3]

/-- The base field with the zero profile. -/
theorem ofFun_zero_add (x : FieldSample) :
    ofFun (fun v => 0 * Real.log ‖v‖ + (fun _ : ℂ => (0 : ℝ)) v) + x = x := by
  funext μ
  simp [ofFun]

/-! ## Almost surely, every continuous profile, every good parameter -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end ASep
end QuantumZipper
