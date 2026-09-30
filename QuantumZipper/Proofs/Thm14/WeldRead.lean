import QuantumZipper.Proofs.Thm14.WeldReadBasic
import QuantumZipper.Proofs.Thm14.WDGReduce
import QuantumZipper.Proofs.LQG.RevCouplingReg

/-!
# WELD-READ: `WeldRPairingReadable` from the semicircle pairing limits

Task WELD-READ (Theorem 1.4(b), field side). Sheffield, *Conformal weldings of random surfaces*
(arXiv:1012.4797), p. 16: "`h` determines `ν_h`, hence `R`". The formal content is
`Thm14WDG.WeldRPairingReadable`: the rational values of `R_h` are a.s. a measurable function of
countably many pairings of `h = couplingFieldRev κ (√κ B) T X` with mass-zero test functions.

We prove it (`weldRPairingReadable_of`) from one analytic input, stated as the proposition
`FcRPairingLimit`: for each real centre `d` and dyadic radius `2^{-k}`, the balanced semicircle
value `h(fc(d, 2^{-k})) - h(fc(0, 1))` of `h` is the limit in probability of the pairings of `h` with some
sequence of mass-zero test functions compactly supported in `ℍ`
(Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), §3.1 and
§6: the semicircle averages of `h` are limits of pairings of `h` with smooth test functions;
balancing against the reference semicircle `fc(0,1)` removes the additive constant).

Route (own bookkeeping, no separate source):
1. pass to deterministic subsequences converging a.s., enumerate the countably many
   real-centred dyadic semicircles (`fcR`) and interleave the test sequences; `Ψ` takes `limUnder` along each sequence, reconstructs a field sample from the
   limits (`recR`) and applies the measurable reading functional `weldReadF`
   (`WeldReadBasic`);
2. the limits are the values of `h` shifted by the constant `-h(fc(0,1))`; the raw circle
   averages of `h` converge a.s. (`ae_rawConverges_couplingFieldRev`: time reversal as in
   `RevCouplingReg`, `B2.b2_ident`, `E1.ae_rawConverges_h0f`), so the shift multiplies the vague
   limit by a positive finite constant, which `R` does not see;
3. the vague limit exists a.s. because `ν_h` charges intervals
   (`RevCouplingReg.revCouplingBoundaryMeasureRegular`), which excludes the junk value `0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm14WDG

/-- **Analytic input (semicircle values as pairing limits).** For every real centre `d` and
dyadic radius `2^{-k}` there is a sequence of mass-zero test functions compactly supported in `ℍ`
whose pairings with `h = couplingFieldRev κ (√κ B) T X` converge **in probability** to the
balanced semicircle value `h(fc(d, 2^{-k})) - h(fc(0, 1))` (a.s. convergence along a
deterministic subsequence follows, `TendstoInMeasure.exists_seq_tendsto_ae`). -/
def FcRPairingLimit : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ (d : ℝ) (k : ℕ), ∃ ρ : ℕ → TestFun0 H,
      TendstoInMeasure P
        (fun j ω => pairRaw (couplingFieldRev κ (drive κ B ω) T (X ω)) (ρ j).1.1) atTop
        (fun ω => couplingFieldRev κ (drive κ B ω) T (X ω) (foldedCircle (d : ℂ) (radius k)) -
          couplingFieldRev κ (drive κ B ω) T (X ω) (foldedCircle 0 1))

section RawConv

open CharFun UnzipInvariance UnzipFull B1Full B2

/-- A.s. the raw dyadic circle averages of the reverse coupling field converge at every point of
`Hbar` (transfer of `E1.ae_rawConverges_h0f` through time reversal and `B2.b2_ident`, as in
`RevCouplingReg.revCouplingBoundaryMeasureRegular`). -/
theorem ae_rawConverges_couplingFieldRev {κ T : ℝ} (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, LocalRule.RawConverges (couplingFieldRev κ (drive κ B ω) T (X ω)) Hbar := by
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hB₁ : IsPreBrownianReal B₁ P := hB.toIsPreBrownianReal.congr fun s => by
    filter_upwards [hB₁eq] with ω h using (h s).symm
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  have hBt : IsBrownianReal (revBM B₁ T.toNNReal) P := isBrownianReal_revBM hB₁ hB₁c _
  have hindt : IndepFun (pathOf (revBM B₁ T.toNNReal)) X P := by
    have hΦ : Measurable fun p : ℝ≥0 → ℝ =>
        fun s => p (T.toNNReal - s) + p (max s T.toNNReal) - 2 * p T.toNNReal := by
      fun_prop
    exact hind₁.comp hΦ measurable_id
  filter_upwards [b2_ident (κ := κ) hBt hX hindt hT.le, E1.ae_rawConverges_h0f hBt hX hindt hT.le,
    hB₁eq, hB₁.eval_zero_ae_eq_zero] with ω hc hraw hb h0
  have hV : EqOn (Vr κ T (revBM B₁ T.toNNReal) ω) (drive κ B ω) (Icc 0 T) := by
    intro s hs
    have hs' : T - s ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have e1 := drive_revBM_eq (κ := κ) B₁ hT.le ω hs'
    have e2 := drive_revBM_eq (κ := κ) B₁ hT.le ω (⟨hT.le, le_rfl⟩ : T ∈ Icc 0 T)
    rw [Vr, vrev_of_mem hs, e1, e2, sub_sub_cancel, sub_self]
    simp only [drive, Real.toNNReal_zero, h0, hb]
    ring
  have hrev : revMap (Vr κ T (revBM B₁ T.toNNReal) ω) T = revMap (drive κ B ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hV
  have hfield : couplingFieldRev κ (Vr κ T (revBM B₁ T.toNNReal) ω) T (X ω) =
      couplingFieldRev κ (drive κ B ω) T (X ω) := by
    simp only [couplingFieldRev, hrev]
  rw [hfield] at hc
  intro k z hz
  obtain ⟨l, hl⟩ := hraw k z hz
  refine ⟨l, hl.congr fun n => ?_⟩
  rw [CoordsFull.radius_eq_div]
  exact CoordsFull.coordsFull_apply_eq hc n z 1 one_pos k

end RawConv

/-- **WELD-READ.** `WeldRPairingReadable` follows from the semicircle pairing limits
`FcRPairingLimit`. -/
theorem weldRPairingReadable_of (hL : FcRPairingLimit) : WeldRPairingReadable := by
  intro κ hκ hκ4 T hT Ω _ P _ B X hB hX hind
  have hρ := fun i : ℤ × ℕ × ℕ =>
    hL κ hκ hκ4 T hT P B X hB hX hind ((i.1 : ℝ) / (2 : ℝ) ^ i.2.1) i.2.2
  choose ρ₀ hρ₀ using hρ
  choose ns hmono hρ' using fun i => (hρ₀ i).exists_seq_tendsto_ae
  set ρ' : ℤ × ℕ × ℕ → ℕ → TestFun0 H := fun i j => ρ₀ i (ns i j) with hρ'_def
  let e : ℕ ≃ (ℤ × ℕ × ℕ) × ℕ := (Denumerable.eqv _).symm
  refine ⟨fun N => ρ' (e N).1 (e N).2, fun p q => weldReadF (Real.sqrt κ) q
    (recR fun i => limUnder atTop fun j => p (e.symm (i, j))), ?_, ?_⟩
  · refine measurable_pi_iff.2 fun q => (measurable_weldReadF _ q).comp
      (measurable_recR.comp (measurable_pi_iff.2 fun i => ?_))
    exact (StronglyMeasurable.limUnder fun j =>
      (measurable_pi_apply (e.symm (i, j))).stronglyMeasurable).measurable
  · have hreg := RevCouplingReg.revCouplingBoundaryMeasureRegular κ hκ hκ4 T hT P B X hB hX hind
    filter_upwards [ae_all_iff.2 hρ', hreg, ae_rawConverges_couplingFieldRev hT hB hX hind]
      with ω hl hr hraw
    have hex : ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ)
        (couplingFieldRev κ (drive κ B ω) T (X ω))) ν := by
      by_contra hne
      have h01 := hr.2.1 0 1 one_pos
      unfold qBoundaryMeasure at h01
      rw [dif_neg hne] at h01
      simp at h01
    obtain ⟨ν, hν⟩ := hex
    funext q
    refine weldReadF_recR (c := -(couplingFieldRev κ (drive κ B ω) T (X ω) (foldedCircle 0 1)))
      (fun i => ?_) hraw hν q
    simp only [Thm14Determination.pairSeq, Equiv.apply_symm_apply]
    rw [(hl i).limUnder_eq, sub_eq_add_neg]
    rfl

end Thm14WDG
end QuantumZipper
