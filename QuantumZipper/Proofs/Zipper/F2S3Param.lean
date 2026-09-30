import QuantumZipper.Proofs.Zipper.F2S3ParamDet
import QuantumZipper.Proofs.Zipper.LogShiftWRed
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun
import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.Zipper.F1Reflect
import QuantumZipper.Proofs.Section5.Prop17Field
import QuantumZipper.Proofs.Field.Factorization
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.Zipper.WedgeTipXNonvanish

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# F2 step (3): `Step3WeldParamStmt` from the `Γ⁰` stage geometry and the stage density of `x`

Theorem 1.3, node F2, step (3), input `F2.Step3WeldParamStmt` (`F2S3Weld.lean`). Sheffield,
*Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4 (pp. 70–72): the boundary measure
of the unzipped field is transported by the unzipping maps, and the two sides of `η[0,s]` are
the preimages of the initial segments of `[O⁻_t, 0]`, `[0, O⁺_t]`.

## Proof (own bookkeeping, `step3WeldParam_of_arcs_dens0`)

Inputs, both existing named nodes:
* `F1.LogShiftWArcsStmt` (stage geometry of the `Γ⁰` picture, Sheffield §1.4/§5.4, Rohde–Schramm
  simple trace): a measurable curve `η` and, at every horizon `t`, boundary position maps `a`, `b`
  (continuous, strictly monotone on `[0,t]` from `O^∓_t` to `0`) with
  `ν_{Γ_t}[O⁻_t, a r] = L^Γ⁻_r`, `ν_{Γ_t}[b r, O⁺_t] = L^Γ⁺_r` and `F_t(a r) = F_t(b r) = η(r)`
  for `r ∈ (0,t]`;
* `F1.LogShiftWDens0Stmt` with `G = 0`, `Z = x = X + α₀(−log|·|)` (local rule (5.1) off the tips,
  TIP-X at the tips): `ν_{x_t} = |F_t|^{−γ²/2}·ν_{Γ_t}` off `{O⁻_t, O⁺_t}`.

(a) Capture times: `φ⁻ = a⁻¹`, `φ⁺ = b⁻¹` (`captureFn`, monotone hence measurable); the curve is
`η` modified at time `0` to the common tip value `F_t(O⁻_t) = F_t(O⁺_t)` (continuity of `F_t`,
`WedgeUnzip.globalCaraStmt_holds`, and `F_t(a r) = F_t(b r)` for `r > 0`).

(b) Lengths: for `0 < s ≤ t`, both `L^x⁻_s = ν_{x_s}[O⁻_s, 0]` and `ν_{x_t}[O⁻_t, a_t(s)]` equal
`∫ ρ(η(r)) dM(r)`, `ρ = |·|^{−γ²/2}`, where `M` is the capture-time image of `ν_Γ` on
`(O⁻, a(s)]`; this image has distribution function `r ↦ L^Γ⁻_{min r s} − L^Γ⁻_0` at both horizons
`s` and `t` (`F2.left_map_eq`), so it is the same measure. At `s = 0` both sides vanish (no atoms of
`ν_x` at the tips). The plus side is symmetric.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

theorem param_arcs_split {νΓ : Measure ℝ} {O : ℝ × ℝ} {h : ℝ} (hh : 0 ≤ h)
    {L : ℝ → ℝ≥0∞ × ℝ≥0∞} {Ψ η : ℝ → ℂ} (hLfin : ∀ r, (L r).1 ≠ ⊤ ∧ (L r).2 ≠ ⊤)
    (hA : F1.LswArcs νΓ O h L Ψ η) :
    ∃ a b : ℝ → ℝ, LeftArc νΓ O.1 h (fun r => (L r).1) a ∧
      RightArc νΓ O.2 h (fun r => (L r).2) b ∧
      ∀ r ∈ Ioc 0 h, Ψ (a r) = η r ∧ Ψ (b r) = η r := by
  obtain ⟨-, a, b, ha, hb, hma, hmb, ha0, has, hb0, hbs, hsub, hpt⟩ := hA
  exact ⟨a, b, ⟨hh, ha, hma, ha0, has, fun r hr => ⟨(hsub r hr).1, (hLfin r).1⟩⟩,
    ⟨hh, hb, hmb, hb0, hbs, fun r hr => ⟨(hsub r hr).2, (hLfin r).2⟩⟩, hpt⟩

theorem param_wd_null {μ : Measure ℝ} {p q : ℝ} {f : ℝ → ℝ≥0∞} {S : Set ℝ}
    (hS : S ⊆ {p, q}) : ((μ.restrict ({p, q} : Set ℝ)ᶜ).withDensity f) S = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply' ((measurableSet_singleton q).insert p).compl]
  exact measure_mono_null (fun w hw => (hw.2 (hS hw.1)).elim) measure_empty

theorem param_wd_apply {μ : Measure ℝ} {T : Set ℝ} {f : ℝ → ℝ≥0∞} {A D : Set ℝ}
    (hA : MeasurableSet A) (hD : A ∩ T = D) :
    ((μ.restrict T).withDensity f) A = ∫⁻ w in D, f w ∂μ := by
  rw [withDensity_apply _ hA, Measure.restrict_restrict hA, hD]

/-- **Left length at one horizon.** -/
theorem param_left_len {νΓ νx : Measure ℝ} {O : ℝ × ℝ} {h : ℝ} {L : ℝ → ℝ≥0∞} {a : ℝ → ℝ}
    {Ψ η : ℝ → ℂ} {g : ℂ → ℝ≥0∞} (hg : Measurable fun r => g (η r))
    (H : LeftArc νΓ O.1 h L a) (hpt : ∀ r ∈ Ioc 0 h, Ψ (a r) = η r) (hO2 : 0 < O.2)
    (hD : νx = (νΓ.restrict ({O.1, O.2} : Set ℝ)ᶜ).withDensity (fun w => g (Ψ w)))
    {s : ℝ} (hs : s ∈ Icc 0 h) :
    νx (Icc O.1 (a s)) = ∫⁻ r, g (η r) ∂((νΓ.restrict (Ioc O.1 (a s))).map (captureFn a h)) := by
  have has : a s ≤ 0 := (H.mem hs).2
  rw [hD, param_wd_apply measurableSet_Icc (D := Ioc O.1 (a s))]
  · refine setLIntegral_eq_map measurableSet_Ioc (measurable_captureFn H.1) hg fun w hw => ?_
    have hw' : w ∈ Icc O.1 0 := ⟨hw.1.le, hw.2.trans has⟩
    obtain ⟨h1, h2⟩ := H.cap hw'
    have hpos := H.cap_pos hw' hw.1
    rw [← hpt _ ⟨hpos, h1.2⟩, h2]
  · ext w
    simp only [mem_inter_iff, mem_Icc, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or,
      mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, -⟩
      exact ⟨lt_of_le_of_ne h1 (Ne.symm h3), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.le, h2⟩, h1.ne', ((h2.trans has).trans_lt hO2).ne⟩

/-- **Right length at one horizon.** -/
theorem param_right_len {νΓ νx : Measure ℝ} {O : ℝ × ℝ} {h : ℝ} {L : ℝ → ℝ≥0∞} {b : ℝ → ℝ}
    {Ψ η : ℝ → ℂ} {g : ℂ → ℝ≥0∞} (hg : Measurable fun r => g (η r))
    (H : RightArc νΓ O.2 h L b) (hpt : ∀ r ∈ Ioc 0 h, Ψ (b r) = η r) (hO1 : O.1 < 0)
    (hD : νx = (νΓ.restrict ({O.1, O.2} : Set ℝ)ᶜ).withDensity (fun w => g (Ψ w)))
    {s : ℝ} (hs : s ∈ Icc 0 h) :
    νx (Icc (b s) O.2) =
      ∫⁻ r, g (η r) ∂((νΓ.restrict (Ico (b s) O.2)).map (rcaptureFn b h)) := by
  have hbs : 0 ≤ b s := (H.mem hs).1
  rw [hD, param_wd_apply measurableSet_Icc (D := Ico (b s) O.2)]
  · refine setLIntegral_eq_map measurableSet_Ico (measurable_rcaptureFn H.1) hg fun w hw => ?_
    have hw' : w ∈ Icc 0 O.2 := ⟨hbs.trans hw.1, hw.2.le⟩
    obtain ⟨h1, h2⟩ := H.cap hw'
    have hpos := H.cap_pos hw' hw.2
    rw [← hpt _ ⟨hpos, h1.2⟩, h2]
  · ext w
    simp only [mem_inter_iff, mem_Icc, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or,
      mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h3⟩
      exact ⟨h1, lt_of_le_of_ne h2 h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.le⟩, (hO1.trans_le (hbs.trans h1)).ne', h2.ne⟩

/-- **Deterministic core of `Step3WeldParamStmt`** (one sample, one horizon `t`). -/
theorem param_of_stages {νΓ νx : ℝ → Measure ℝ} {O : ℝ → ℝ × ℝ} {Ψ : ℝ → ℝ → ℂ}
    {η : ℝ → ℂ} {L Lx : ℝ → ℝ≥0∞ × ℝ≥0∞} {g : ℂ → ℝ≥0∞}
    (hη : Measurable η) (hg : Measurable fun r => g (η r))
    (hLfin : ∀ r, (L r).1 ≠ ⊤ ∧ (L r).2 ≠ ⊤)
    (hΨ : ∀ t, 0 ≤ t → Continuous (Ψ t))
    (hA : ∀ t, 0 ≤ t → F1.LswArcs (νΓ t) (O t) t L (Ψ t) η)
    (hD : ∀ t, 0 ≤ t → νx t =
      ((νΓ t).restrict ({(O t).1, (O t).2} : Set ℝ)ᶜ).withDensity (fun w => g (Ψ t w)))
    (hLx : ∀ s, 0 ≤ s → Lx s = (νx s (Icc (O s).1 0), νx s (Icc 0 (O s).2)))
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ (η' : ℝ → ℂ) (φm φp : ℝ → ℝ), Measurable η' ∧ Measurable φm ∧ Measurable φp ∧
      (∀ w ∈ Icc (O t).1 0, φm w ∈ Icc 0 t ∧ Ψ t w = η' (φm w)) ∧
      (∀ w ∈ Icc 0 (O t).2, φp w ∈ Icc 0 t ∧ Ψ t w = η' (φp w)) ∧
      ∀ s ∈ Icc (0 : ℝ) t, (Lx s).1 = νx t (Icc (O t).1 0 ∩ φm ⁻¹' Iic s) ∧
        (Lx s).2 = νx t (Icc 0 (O t).2 ∩ φp ⁻¹' Iic s) := by
  obtain ⟨a, b, HL, HR, hpt⟩ := param_arcs_split ht hLfin (hA t ht)
  -- the common tip value
  have htip : Ψ t (O t).2 = Ψ t (O t).1 := by
    rcases ht.lt_or_eq with htp | ht0
    · have hc1 : Continuous fun r => Ψ t (a r) := (hΨ t ht).comp HL.2.1
      have hc2 : Continuous fun r => Ψ t (b r) := (hΨ t ht).comp HR.2.1
      have heq : (fun r => Ψ t (b r)) =ᶠ[𝓝[>] 0] (fun r => Ψ t (a r)) := by
        filter_upwards [Ioo_mem_nhdsGT htp] with r hr
        rw [(hpt r ⟨hr.1, hr.2.le⟩).1, (hpt r ⟨hr.1, hr.2.le⟩).2]
      have := tendsto_nhds_unique ((hc2.tendsto 0).mono_left nhdsWithin_le_nhds)
        (((hc1.tendsto 0).mono_left nhdsWithin_le_nhds).congr' heq.symm)
      rwa [HL.2.2.2.1, HR.2.2.2.1] at this
    · subst ht0
      have h1 : (O 0).1 = 0 := by rw [← HL.2.2.2.1, HL.2.2.2.2.1]
      have h2 : (O 0).2 = 0 := by rw [← HR.2.2.2.1, HR.2.2.2.2.1]
      rw [h1, h2]
  set η' : ℝ → ℂ := fun r => if r = 0 then Ψ t (O t).1 else η r with hη'
  have hη'm : Measurable η' := Measurable.ite (measurableSet_singleton 0) measurable_const hη
  refine ⟨η', captureFn a t, rcaptureFn b t, hη'm, measurable_captureFn ht,
    measurable_rcaptureFn ht, fun w hw => ?_, fun w hw => ?_, fun s hs => ?_⟩
  · obtain ⟨h1, h2⟩ := HL.cap hw
    refine ⟨h1, ?_⟩
    by_cases h0 : captureFn a t w = 0
    · simp only [hη', h0, ite_true]
      rw [← h2, h0, HL.2.2.2.1]
    · simp only [hη', h0, ite_false]
      rw [← (hpt _ ⟨lt_of_le_of_ne h1.1 (Ne.symm h0), h1.2⟩).1, h2]
  · obtain ⟨h1, h2⟩ := HR.cap hw
    refine ⟨h1, ?_⟩
    by_cases h0 : rcaptureFn b t w = 0
    · simp only [hη', h0, ite_true]
      rw [← h2, h0, HR.2.2.2.1, htip]
    · simp only [hη', h0, ite_false]
      rw [← (hpt _ ⟨lt_of_le_of_ne h1.1 (Ne.symm h0), h1.2⟩).2, h2]
  rw [hLx s hs.1]
  rcases hs.1.lt_or_eq with hsp | hs0
  · -- `0 < s`: transport between the horizons `s` and `t`
    have hs' : 0 ≤ s := hs.1
    obtain ⟨a', b', HL', HR', hpt'⟩ := param_arcs_split hs' hLfin (hA s hs')
    have hss : s ∈ Icc 0 s := ⟨hs', le_rfl⟩
    have hO2 : ∀ {h : ℝ} {b₀ : ℝ → ℝ} {ν : Measure ℝ} {O₂ : ℝ} {L₀ : ℝ → ℝ≥0∞},
        RightArc ν O₂ h L₀ b₀ → 0 < h → 0 < O₂ := fun {h} {b₀} {ν} {O₂} {L₀} H hh => by
      have := H.2.2.1 ⟨le_rfl, H.1⟩ ⟨H.1, le_rfl⟩ hh
      rwa [H.2.2.2.1, H.2.2.2.2.1] at this
    have hO1 : ∀ {h : ℝ} {a₀ : ℝ → ℝ} {ν : Measure ℝ} {O₁ : ℝ} {L₀ : ℝ → ℝ≥0∞},
        LeftArc ν O₁ h L₀ a₀ → 0 < h → O₁ < 0 := fun {h} {a₀} {ν} {O₁} {L₀} H hh => by
      have := H.2.2.1 ⟨le_rfl, H.1⟩ ⟨H.1, le_rfl⟩ hh
      rwa [H.2.2.2.1, H.2.2.2.2.1] at this
    have htp : 0 < t := hsp.trans_le hs.2
    refine ⟨?_, ?_⟩
    · have e1 : Icc (O s).1 0 = Icc (O s).1 (a' s) := by rw [HL'.2.2.2.2.1]
      have e2 : Icc (O t).1 0 ∩ captureFn a t ⁻¹' Iic s = Icc (O t).1 (a s) := by
        ext w
        simp only [mem_inter_iff, mem_preimage, mem_Iic]
        constructor
        · rintro ⟨hw, hc⟩
          exact ⟨hw.1, (HL.cap_le_iff hw hs).1 hc⟩
        · rintro hw
          have hw' : w ∈ Icc (O t).1 0 := ⟨hw.1, hw.2.trans (HL.mem hs).2⟩
          exact ⟨hw', (HL.cap_le_iff hw' hs).2 hw.2⟩
      rw [e1, e2, param_left_len hg HL' (fun r hr => (hpt' r hr).1) (hO2 HR' hsp) (hD s hs') hss,
        param_left_len hg HL (fun r hr => (hpt r hr).1) (hO2 HR htp) (hD t ht) hs,
        left_map_eq HL' HL hss hs]
    · have e1 : Icc 0 (O s).2 = Icc (b' s) (O s).2 := by rw [HR'.2.2.2.2.1]
      have e2 : Icc 0 (O t).2 ∩ rcaptureFn b t ⁻¹' Iic s = Icc (b s) (O t).2 := by
        ext w
        simp only [mem_inter_iff, mem_preimage, mem_Iic]
        constructor
        · rintro ⟨hw, hc⟩
          exact ⟨(HR.cap_le_iff hw hs).1 hc, hw.2⟩
        · rintro hw
          have hw' : w ∈ Icc 0 (O t).2 := ⟨(HR.mem hs).1.trans hw.1, hw.2⟩
          exact ⟨hw', (HR.cap_le_iff hw' hs).2 hw.1⟩
      rw [e1, e2, param_right_len hg HR' (fun r hr => (hpt' r hr).2) (hO1 HL' hsp) (hD s hs') hss,
        param_right_len hg HR (fun r hr => (hpt r hr).2) (hO1 HL htp) (hD t ht) hs,
        right_map_eq HR' HR hss hs]
  · -- `s = 0`: both sides are masses of tip points
    subst hs0
    obtain ⟨a₀, b₀, HL₀, HR₀, -⟩ := param_arcs_split le_rfl hLfin (hA 0 le_rfl)
    have hO₀1 : (O 0).1 = 0 := by rw [← HL₀.2.2.2.1, HL₀.2.2.2.2.1]
    have hO₀2 : (O 0).2 = 0 := by rw [← HR₀.2.2.2.1, HR₀.2.2.2.2.1]
    refine ⟨?_, ?_⟩
    · have hL0 : Icc (O 0).1 0 ⊆ {(O 0).1, (O 0).2} := by
        intro w hw
        rw [hO₀1] at hw ⊢
        rw [le_antisymm hw.2 hw.1]
        exact mem_insert _ _
      have hLt : Icc (O t).1 0 ∩ captureFn a t ⁻¹' Iic 0 ⊆ {(O t).1, (O t).2} := by
        rintro w ⟨hw, hc⟩
        have h1 := HL.cap hw
        have h0 : captureFn a t w = 0 := le_antisymm hc h1.1.1
        rw [← h1.2, h0, HL.2.2.2.1]
        exact mem_insert _ _
      rw [hD 0 le_rfl, hD t ht, param_wd_null hL0, param_wd_null hLt]
    · have hR0 : Icc 0 (O 0).2 ⊆ {(O 0).1, (O 0).2} := by
        intro w hw
        rw [hO₀2] at hw ⊢
        rw [le_antisymm hw.2 hw.1]
        exact mem_insert_of_mem _ rfl
      have hRt : Icc 0 (O t).2 ∩ rcaptureFn b t ⁻¹' Iic 0 ⊆ {(O t).1, (O t).2} := by
        rintro w ⟨hw, hc⟩
        have h1 := HR.cap hw
        have h0 : rcaptureFn b t w = 0 := le_antisymm hc h1.1.1
        rw [← h1.2, h0, HR.2.2.2.1]
        exact mem_insert_of_mem _ rfl
      rw [hD 0 le_rfl, hD t ht, param_wd_null hR0, param_wd_null hRt]

end F2
end QuantumZipper
