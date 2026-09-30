import QuantumZipper.Proofs.Zipper.E1NuExist
import QuantumZipper.Proofs.Zipper.E1TransferMeas
import QuantumZipper.Proofs.Zipper.Collision

/-!
# E3 in the Palm-zip picture: collision has positive Palm mass

`blueprint/E_BRANCH_BLUEPRINT.md` §4 E3; `handoff/E-PLAN-2.md` (E3-HIT, E3-ANTI, E3-POS).
Paper: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 and the discussion after it (PDF pp. 66–69):
the Palm point `x ∈ [−δ,0]` is swallowed by the reverse flow. Downstream (E5, E6) only needs that
the collided part of the (un-normalized) Palm measure is non-trivial, which is E3-POS.

* **E3-HIT** `prob_hitTime_Vr_gt_le`: E3(i) for the reversed driver `V = Vr κ T B`:
  `P(τ_{−δ}(V) > t) ≤ δ²/((4−κ)t)` for `0 < t < T` (`V` is `√κ`·BM on `[0,T]`, `B2.b2_V_brownian`;
  the live set at time `t` reads the driver on `[0,t]` only, `E1.isLive_congr_drive`; then
  `Collision.prob_realHitTime_gt_le`).
* **E3-ANTI** `realHitTime_le_of_mem_Icc`: if `τ_{−δ} ≤ s` then `τ_x ≤ s` for all `x ∈ [−δ,0]`
  (`Collision.realHitTime_anti`, and `τ_0 = 0`).
* `ae_nuPalm_Ioo_pos`: under B3(a), a.s. `ν(u,v) > 0` for `u < v`.
* **E3-POS** `e3_pos`: for `T ≥ 4δ²/(4−κ)`,
  `0 < ∫⁻ ω, ν_ω {x ∈ [−δ,0] | τ_x < T} dP`, given the a.e. measurability of `ω ↦ ν_ω`
  (node NU-MEAS, taken as the hypothesis `hmeas`).

The route (Dynkin for `u²` instead of the paper's Bessel/Itô argument) is the blueprint's; the
assembly is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E3

open B2 E1

/-- **E3-ANTI.** If `−δ` is swallowed by time `s`, so is every `x ∈ [−δ, 0]`. -/
theorem realHitTime_le_of_mem_Icc {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0)
    {δ s x : ℝ} (hx : x ∈ Icc (-δ) 0) (h : realHitTime V (-δ) ≤ ENNReal.ofReal s) :
    realHitTime V x ≤ ENNReal.ofReal s := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact (Collision.realHitTime_anti hV hx.1 (by rw [hV0]; exact hlt)).trans h
  · have h0 := not_isLive_zero hV0 0
    simp only [IsLive, not_lt, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at h0
    rw [h0]
    exact zero_le

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
/-- The live event at time `t < T` is the same for `V = Vr κ T B` and for a driver that agrees
with `V` on `[0,T]`. -/
theorem ae_isLive_Vr_iff {B'' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hB'' : IsBrownianReal B'' P) (hV : ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, Vr κ T B ω s = drive κ B'' ω s)
    {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (x : ℝ) :
    ∀ᵐ ω ∂P, IsLive (Vr κ T B ω) t x ↔ IsLive (drive κ B'' ω) t x := by
  filter_upwards [hV, hB.cont, hB''.cont] with ω hVω hc hc''
  exact isLive_congr_drive (continuous_vrev (drive_continuous hc) T) (drive_continuous hc'') ht
    fun s hs => hVω s ⟨hs.1, hs.2.trans htT⟩

/-- Under B3(a), a.s. the Palm boundary measure charges every open interval. -/
theorem ae_nuPalm_Ioo_pos (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (ϖ : Measure ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℝ, u < v → 0 < nuPalm κ T B X ϖ ω (Ioo u v) := by
  obtain ⟨B'', hB'', hind'', hV⟩ := b2_V_brownian (κ := κ) hB hind hT.le
  filter_upwards [hReg κ hκ hκ4 T hT P B'' X hB'' hX hind'', hV,
    b2_ident_qBoundaryMeasure hB hX hind hT.le, ae_nuPalm_eq_smul (κ := κ) hB hX hind hT.le ϖ]
    with ω hRω hVω hid hsm u v huv
  have hrevV : revMap (Vr κ T B ω) T = revMap (drive κ B'' ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hVω
  have hcf : couplingFieldRev κ (Vr κ T B ω) T (X ω) =
      couplingFieldRev κ (drive κ B'' ω) T (X ω) := by
    simp only [couplingFieldRev, hrevV]
  rw [hsm, Measure.smul_apply, hid, hcf, smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' (hRω.2.1 u v huv).ne'

/-- **E3-POS.** For `T ≥ 4δ²/(4−κ)`, the Palm points of `[−δ,0]` that collide strictly before `T`
have positive (un-normalized) Palm mass. `hmeas` is node NU-MEAS. -/
theorem e3_pos (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {ϖ : Measure ℂ}
    (hmeas : AEMeasurable (fun ω => nuPalm κ T B X ϖ ω) P) {δ : ℝ} (hδ : 0 < δ)
    (hTδ : 4 * δ ^ 2 / (4 - κ) ≤ T) :
    0 < ∫⁻ ω, nuPalm κ T B X ϖ ω
      {x | x ∈ Icc (-δ) 0 ∧ realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} ∂P := by
  obtain ⟨B'', hB'', -, hV⟩ := b2_V_brownian (κ := κ) hB hind hT.le
  have hT2 : 0 < T / 2 := half_pos hT
  have h1 := Collision.aemeasurable_realHitTime hB'' κ (x := -δ) (by linarith)
  set A : Set Ω := {ω | h1.mk _ ω ≤ ENNReal.ofReal (T / 2)} with hAdef
  have hA : MeasurableSet A := measurableSet_le h1.measurable_mk measurable_const
  -- the complement of `A` has probability at most `1/2`
  have hAc : P Aᶜ ≤ ENNReal.ofReal (δ ^ 2 / ((4 - κ) * (T / 2))) := by
    have heq : Aᶜ =ᵐ[P] {ω | ENNReal.ofReal (T / 2) < realHitTime (drive κ B'' ω) (-δ)} := by
      filter_upwards [h1.ae_eq_mk] with ω h
      simp only [hAdef, mem_compl_iff, Set.mem_ofPred_eq, not_le, h]
    rw [measure_congr heq]
    exact Collision.prob_realHitTime_gt_le hB'' hκ hκ4 hδ hT2
  have h4κ : 0 < 4 - κ := by linarith
  have hhalf : δ ^ 2 / ((4 - κ) * (T / 2)) < 1 := by
    rw [div_lt_one (by positivity)]
    have : 4 * δ ^ 2 ≤ T * (4 - κ) := (div_le_iff₀ h4κ).1 hTδ
    nlinarith [sq_nonneg δ, mul_pos hδ hδ]
  have hPA : P A ≠ 0 := by
    intro h0
    have hc : P Aᶜ = 1 := by rw [prob_compl_eq_one_sub hA, h0, tsub_zero]
    have := hc ▸ hAc
    exact absurd (this.trans_lt (ENNReal.ofReal_lt_one.2 hhalf)) (lt_irrefl 1)
  -- the lower bound `1_A · ν(−δ,0) ≤ ν{collided}`
  set G : Ω → ℝ≥0∞ := fun ω => nuPalm κ T B X ϖ ω (Ioo (-δ) 0) with hGdef
  have hGm : AEMeasurable G P := (Measure.measurable_coe measurableSet_Ioo).comp_aemeasurable hmeas
  have hle : ∀ᵐ ω ∂P, A.indicator G ω ≤ nuPalm κ T B X ϖ ω
      {x | x ∈ Icc (-δ) 0 ∧ realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} := by
    filter_upwards [h1.ae_eq_mk, ae_isLive_Vr_iff hB hB'' hV hT2.le (by linarith) (-δ),
      hB.cont] with ω hmk hlive hc
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω]
      have hv : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
      have hv0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
      have hdδ : realHitTime (Vr κ T B ω) (-δ) ≤ ENNReal.ofReal (T / 2) := by
        have h' : realHitTime (drive κ B'' ω) (-δ) ≤ ENNReal.ofReal (T / 2) := by
          rw [hmk]; exact hω
        have := mt hlive.1 (not_lt.2 h')
        simpa [IsLive] using this
      refine measure_mono fun x hx => ⟨Ioo_subset_Icc_self hx, ?_⟩
      exact (realHitTime_le_of_mem_Icc hv hv0 (Ioo_subset_Icc_self hx) hdδ).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hT).2 (by linarith))
    · rw [indicator_of_notMem hω]; exact zero_le
  refine lt_of_lt_of_le ?_ (lintegral_mono_ae hle)
  rw [pos_iff_ne_zero]
  intro h0
  rw [lintegral_eq_zero_iff' (hGm.indicator hA)] at h0
  apply hPA
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [h0, ae_nuPalm_Ioo_pos hReg hκ hκ4 hT hB hX hind ϖ] with ω h hpos hω
  have := hpos (-δ) 0 (by linarith)
  rw [Pi.zero_apply, indicator_of_mem hω] at h
  exact this.ne' h

end E3
end QuantumZipper
