import QuantumZipper.Proofs.Zipper.ZipLen2ContMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RF (4): uniform continuum limit of the `Γ⁰` flow pairings on parameter boxes

Toward `A1RFLoopUCStmt` (A1RFSmear.lean), whose free-field input is a continuum limit of the
smoothed pairings along the pulled-back folded circles `(f_t⁻¹)_* fc(z, ρ)`, **uniformly** in the
centre `z` on bounded sets. `B3d.ZipLen.yFlowContStmt_holds` (ZipLen2ContMain.lean) exports only
the pointwise limit, but its proof gives the Cauchy estimate uniformly over each parameter box
`flowBox m`: the rational Cauchy property `FlowBrownUCcStmt` is uniform over the rational box
points, and the extension to all box points and real radii uses only the joint continuity
`ae_flowPhiYc_joint` at the point. This file records that uniform form:

* `A1RF.ae_flowPhiYc_unifCauchy`: a.s., for every box `flowBox m` and every `n`, there is `δ > 0`
  with `|Φ^c(ρ, p) − Φ^c(ρ', p)| ≤ 1/(n+1)` for all `p ∈ flowBox m` and `ρ, ρ' ∈ (0, δ)`;
* `A1RF.ae_flowPhiYc_tendstoUniformlyOn`: hence, a.s., on every box the pairings converge
  uniformly as `ρ → 0⁺` (to their pointwise limits).

Same proof as `yFlowContStmt_holds` (Revuz–Yor, 3rd ed., Ch. I, Thm (2.1); Duplantier–Sheffield,
Invent. Math. 185 (2011), Prop. 3.1); own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RF

open F1 B3d.ZipLen

/-- **Uniform Cauchy estimate of the `Γ⁰` flow pairings on each parameter box.** -/
theorem ae_flowPhiYc_unifCauchy {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ m n : ℕ, ∃ δ > 0, ∀ p ∈ flowBox m, ∀ ρ ρ' : ℝ, 0 < ρ → ρ < δ → 0 < ρ' →
      ρ' < δ → |flowPhiYc κ (X ω) (drive κ B ω) ρ p - flowPhiYc κ (X ω) (drive κ B ω) ρ' p| ≤
        1 / ((n : ℝ) + 1) := by
  have hfix := flowFixedUCc_of @flowIdentC_holds @flowDetC_tendstoUniformlyOn
  have hUC := flowBrownUCc_of_fixed hfix hκ hκ4 hB hX hind
  filter_upwards [ae_all_iff.2 hUC, ae_flowPhiYc_joint hκ hB hX hind] with ω hUCω hcont
  set W := drive κ B ω with hWdef
  intro m n
  have hcρ : ∀ p' ∈ flowPar, ContinuousOn (fun ρ => flowPhiYc κ (X ω) W ρ p') (Ioi 0) :=
    fun p' hp' => hcont.comp (f := fun ρ : ℝ => (p', ρ)) (by fun_prop) fun ρ hρ => ⟨hp', hρ⟩
  have hcp : ∀ ρ : ℝ, 0 < ρ → ContinuousOn (fun p' => flowPhiYc κ (X ω) W ρ p') flowPar :=
    fun ρ hρ => hcont.comp (f := fun p' => (p', ρ)) (by fun_prop) fun p' hp' => ⟨hp', hρ⟩
  obtain ⟨N, hN⟩ := hUCω m n
  refine ⟨1 / ((N : ℝ) + 1), by positivity, fun p hpbox ρ ρ' hρ hρδ hρ' hρ'δ => ?_⟩
  have hpP : p ∈ flowPar := flowBox_subset_flowPar m hpbox
  -- rational radii, all box points
  have hA : ∀ r1 r1' : ℚ, 0 < r1 → (r1 : ℝ) ≤ 1 / ((N : ℝ) + 1) → 0 < r1' →
      (r1' : ℝ) ≤ 1 / ((N : ℝ) + 1) →
      |flowPhiYc κ (X ω) W r1 p - flowPhiYc κ (X ω) W r1' p| ≤ 1 / ((n : ℝ) + 1) := by
    intro r1 r1' h1 h2 h3 h4
    have h1' : (0 : ℝ) < r1 := by exact_mod_cast h1
    have h3' : (0 : ℝ) < r1' := by exact_mod_cast h3
    set s : Set (ℝ × ℝ × ℂ × ℝ) := {p' | ∃ q, flowQ q = p' ∧ p' ∈ flowBox m} with hs
    have hsub : s ⊆ flowPar := fun p' ⟨_, _, hp'⟩ => flowBox_subset_flowPar m hp'
    have hF : ContinuousWithinAt (fun p' => |flowPhiYc κ (X ω) W r1 p' -
        flowPhiYc κ (X ω) W r1' p'|) flowPar p :=
      (((hcp _ h1') p hpP).sub ((hcp _ h3') p hpP)).abs
    refine ContinuousWithinAt.closure_le (flowBox_subset_closure m hpbox) (hF.mono hsub)
      continuousWithinAt_const ?_
    rintro _ ⟨q, rfl, hq⟩
    exact hN r1 r1' h1 h2 h3 h4 q hq
  have hB' : ∀ r1' : ℚ, 0 < r1' → (r1' : ℝ) ≤ 1 / ((N : ℝ) + 1) →
      |flowPhiYc κ (X ω) W ρ p - flowPhiYc κ (X ω) W r1' p| ≤ 1 / ((n : ℝ) + 1) := by
    intro r1' h3 h4
    exact le_of_rat_radii (f := fun x => |flowPhiYc κ (X ω) W x p -
        flowPhiYc κ (X ω) W r1' p|) ((hcρ p hpP).sub continuousOn_const).abs
      (fun r1 h1 h2 => hA r1 r1' h1 h2 h3 h4) hρ hρδ
  exact le_of_rat_radii (f := fun x => |flowPhiYc κ (X ω) W ρ p - flowPhiYc κ (X ω) W x p|)
    (continuousOn_const.sub (hcρ p hpP)).abs hB' hρ' hρ'δ

/-- A uniform Cauchy estimate as `ρ → 0⁺` gives uniform convergence to the pointwise limits. -/
theorem tendstoUniformlyOn_of_unifCauchy {α : Type*} {S : Set α} {Φ : ℝ → α → ℝ}
    (h : ∀ n : ℕ, ∃ δ > 0, ∀ p ∈ S, ∀ ρ ρ' : ℝ, 0 < ρ → ρ < δ → 0 < ρ' → ρ' < δ →
      |Φ ρ p - Φ ρ' p| ≤ 1 / ((n : ℝ) + 1)) :
    ∃ L : α → ℝ, TendstoUniformlyOn Φ L (𝓝[>] 0) S := by
  have hC : UniformCauchySeqOn Φ (𝓝[>] 0) S := by
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨δ, hδ, hδc⟩ := h n
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ < δ := Ioo_mem_nhdsGT hδ
    refine (hev.prod_mk hev).mono fun q hq p hp => hεu ?_
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hδc p hp q.1 q.2 hq.1.1 hq.1.2 hq.2.1 hq.2.2) hn
  have hpt : ∀ p ∈ S, ∃ L : ℝ, Tendsto (fun ρ => Φ ρ p) (𝓝[>] 0) (𝓝 L) := fun p hp =>
    cauchy_map_iff_exists_tendsto.1 (hC.cauchy_map hp)
  choose! L hL using hpt
  exact ⟨L, hC.tendstoUniformlyOn_of_tendsto hL⟩

/-- **Uniform continuum limit of the `Γ⁰` flow pairings on each parameter box.** -/
theorem ae_flowPhiYc_tendstoUniformlyOn {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ (X ω) (drive κ B ω) ρ p) L (𝓝[>] 0)
        (flowBox m) := by
  filter_upwards [ae_flowPhiYc_unifCauchy hκ hκ4 hB hX hind] with ω h m
  exact tendstoUniformlyOn_of_unifCauchy (h m)

end A1RF
end R18
end QuantumZipper
