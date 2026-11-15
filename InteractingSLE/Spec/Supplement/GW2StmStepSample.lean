/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StmTip
import InteractingSLE.Spec.Supplement.GW2StmContact

/-!
# GW2's stage step, part 11: the launch clock of the next piece at one sample

Packet PROVE-GW2-STAGEMEAN, step round. At one sample of the conditional law after the new piece: the old launch clock
(`GW1LaunchClock.IsPrefixClock` of the conditional counterflow `W_k` through the launch chart `c`, onto the times
before the original counterflow's first visit of the old union `A`), GB6's relation for the new piece (the tips of
`W₂` through the piece's Loewner chart are those of `W_k` at `ℓ₂`, with `ℓ₂` onto the times before GB6's first contact
`T_c`), and the fibre property of `c` give the launch clock of the next piece: through `c.loewner U T`, onto the times
before the first visit of `A ∪ B`, `B` the new piece's physical tips, with the clock `ℓ_k ∘ ℓ₂`.

* `tipAt_loewner_trans_iff_pre`: the tip relation through `c.loewner U T` in terms of the tips through `c`;
* **`isPrefixClock_step`**: the per-sample step.

Deterministic. Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Stm

open GW1LaunchClock

/-- **The tip relation through the next launch chart, in terms of the current one.** -/
theorem tipAt_loewner_trans_iff_pre {d : Chart} (hd : GW1P.HasProperBdryExt d) {U : ℝ → ℝ} (hU : Continuous U)
    (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hB : HasBdryLimits (fwdMapInv U T)) {W₂ Wk : ℝ≥0 → ℝ}
    {Γ γk : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace W₂ ⊤ Γ) (hW₂ : Continuous W₂) (hW₂0 : W₂ 0 = 0)
    (hγk : IsGeneratingTrace Wk ⊤ γk) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) {ℓ₂ : ℝ≥0 → ℝ≥0}
    (h₂ : ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner U T).trans infinitySourceChart).tipAt W₂ r z ↔
      infinitySourceChart.tipAt Wk (ℓ₂ r) z) :
    ∀ (r : ℝ≥0) (z : ℂ), ((d.loewner U T).trans infinitySourceChart).tipAt W₂ r z ↔
      (d.trans infinitySourceChart).tipAt Wk (ℓ₂ r) z := by
  obtain ⟨f, C, hf, hC⟩ := hd
  obtain ⟨g, C', hg, hC'⟩ := BRLeaf.hasProperBdryExt_id.loewner hU hU0 hT hB
  have heH : ∀ w ∈ H, (Chart.id.loewner U T).2.1 w ∈ H := fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_H hU hU0 hT hw
  intro r z
  rw [Chart.loewner_eq_trans, BW1Det.tipAt_trans_trans_iff hf hC hg hC' heH hΓ hW₂ hW₂0,
    GW1Det.tipAt_trans_iff_exists hf hC hγk hWk hWk0]
  simp_rw [h₂]

/-- **The launch clock of the next piece, at one sample.** -/
theorem isPrefixClock_step {c : Chart} {A : Set ℂ} (hfib : GW1Z.FiberGood c A) {W' Wk W₂ : ℝ≥0 → ℝ}
    {ℓk ℓ₂ : ℝ≥0 → ℝ≥0} (hold : IsPrefixClock c W' Wk A ℓk)
    {γk : ℝ≥0 → ℂ} (hγk : IsGeneratingTrace Wk ⊤ γk) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    {Γ : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace W₂ ⊤ Γ) (hW₂ : Continuous W₂) (hW₂0 : W₂ 0 = 0)
    {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hB : HasBdryLimits (fwdMapInv U T))
    {Wp : ℝ≥0 → ℝ} {S : ℝ≥0} {αp : ℝ≥0 → ℂ} (hαp : IsGeneratingTrace Wp S αp)
    (hWp : ContinuousOn Wp {t | (t : ℝ≥0∞) ≤ S}) (hWp0 : Wp 0 = 0)
    (hℓ₂ : Continuous ℓ₂) (hℓ₂m : StrictMono ℓ₂)
    (hℓ₂r : range ℓ₂ = {t : ℝ≥0 | (t : ℝ≥0∞) < Supp8.GB6.firstContactTime
      (fun t => Supp8.GB6.sphereInv (γk t : OnePoint ℂ)) ((fun t => (αp t : OnePoint ℂ)) '' Icc 0 S)})
    (h₂ : ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner U T).trans infinitySourceChart).tipAt W₂ r z ↔
      infinitySourceChart.tipAt Wk (ℓ₂ r) z) :
    IsPrefixClock (c.loewner U T) W' W₂
      (A ∪ c.tipSet (fun r : ℝ≥0 => Wp (min (r : ℝ≥0∞) S).toNNReal) S) (ℓk ∘ ℓ₂) := by
  have hext : GW1P.HasProperBdryExt c := by
    obtain ⟨f, C, hf, hC, -⟩ := hfib
    exact ⟨f, C, hf, hC⟩
  have hoff : ∀ (t : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk t z → z ∉ A :=
    GW1Z.notMem_of_clock hold.2.2.1 hold.2.2.2
  obtain ⟨hT', hhit⟩ := firstTipTime_piece_eq hfib hγk hWk hWk0 hoff hαp hWp hWp0
  exact IsPrefixClock.compose_cut_top hold hT' hhit hℓ₂ hℓ₂m hℓ₂r
    (tipAt_loewner_trans_iff_pre hext hU hU0 hT hB hΓ hW₂ hW₂0 hγk hWk hWk0 h₂)

end InteractingSLE.Theorem14.GW2Stm
