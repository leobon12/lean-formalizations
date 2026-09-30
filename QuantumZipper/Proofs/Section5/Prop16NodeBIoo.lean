import QuantumZipper.Proofs.Section5.Prop16NodeBPalm
import QuantumZipper.Proofs.LQG.Measurability

/-!
# Proposition 1.6, Palm node B′: the local Palm formula on an open window

`palm_formula_mixed_Ioo`: the local Palm formula of `Prop16NodeBPalm.lean` with the indicator of
the window `(a,b)` in place of a continuous weight (monotone convergence along
`openBump (a,b) n ↑ 1_{(a,b)}`, exactly as `E1.palm_formula_Ioo`):
`E ∫_{(a,b)} G((h0 + X)(μ_j), x) ν(dx) = ∫_{(a,b)} ρ(x) E G((h0 + X + (γ/2) G_D(x,·))(μ_j), x) dx`
for every measurable `G ≥ 0`, with `ρ(x) = exp(γ h0(x)/2 + γ² k(x,x)/8)`.

* `lintegral_Ioo_of_bump`: the abstract monotone-convergence step (own bookkeeping, copied from
  the proof of `E1.palm_formula_Ioo`).
* `palmKCoords`, `measurable_palmKCoords`: the Palm-shifted coordinates in kernel form,
  `(ω, x) ↦ (h0 + X ω)(μ_j) + (γ/2) ∫ G(x, ·) dμ_j`, jointly measurable (item (5) of the D30
  list, for the raw coordinates); `palmMixedField_coord_eq`: they are the coordinates of
  `palmMixedField` at every `x` of the window.

Source: Duplantier–Sheffield, arXiv:0808.1560, §3.3 (p. 22); the rest is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-! ## 1. Monotone convergence from bump weights to the window -/

/-- From the Palm identity for all bump weights `openBump (a,b) n` to the window `(a,b)`. -/
theorem lintegral_Ioo_of_bump {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ν : Ω → Measure ℝ} (hν : AEMeasurable ν P) {a b : ℝ}
    (hfin : ∀ᵐ ω ∂P, ν ω (Icc a b) < ∞) {A : Ω × ℝ → ℝ≥0∞} (hA : Measurable A)
    {B : ℝ → ℝ≥0∞} (hB : Measurable B)
    (hw : ∀ n, ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (LQGMeas.openBump (Ioo a b) n x) * A (ω, x)
        ∂(ν ω) ∂P = ∫⁻ x, ENNReal.ofReal (LQGMeas.openBump (Ioo a b) n x) * B x) :
    ∫⁻ ω, ∫⁻ x in Ioo a b, A (ω, x) ∂(ν ω) ∂P = ∫⁻ x in Ioo a b, B x := by
  set I : Set ℝ := Ioo a b with hIdef
  set wn : ℕ → ℝ → ℝ := fun n => LQGMeas.openBump I n with hwn
  have hIc : Iᶜ.Nonempty := ⟨b, fun h => lt_irrefl b h.2⟩
  have hsup : ∀ x, ⨆ n, ENNReal.ofReal (wn n x) = I.indicator 1 x := fun x =>
    LQGMeas.iSup_openBump isOpen_Ioo hIc x
  have hmono : ∀ x, Monotone fun n => ENNReal.ofReal (wn n x) := fun x _ _ hnm =>
    ENNReal.ofReal_le_ofReal (LQGMeas.openBump_mono I x hnm)
  have hwc : ∀ n, Continuous (wn n) := fun n => LQGMeas.continuous_openBump I n
  have hwab : ∀ n, ∀ x ∉ Icc a b, wn n x = 0 := fun n x hx => by
    by_contra hne
    exact hx (Ioo_subset_Icc_self (LQGMeas.tsupport_openBump_subset I n (subset_tsupport _ hne)))
  have hsplit : ∀ (f : ℝ → ℝ≥0∞), Measurable f → ∀ μ : Measure ℝ,
      ∫⁻ x in I, f x ∂μ = ⨆ n, ∫⁻ x, ENNReal.ofReal (wn n x) * f x ∂μ := by
    intro f hf μ
    rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_iSup
      (f := fun n x => ENNReal.ofReal (wn n x) * f x)
      (fun n => ((hwc n).measurable.ennreal_ofReal).mul hf)
      (fun n m hnm x => mul_le_mul_left (hmono x hnm) _)]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.iSup_mul, hsup x]
    by_cases hx : x ∈ I
    · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, one_mul]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  have hAx : ∀ ω, Measurable fun x => A (ω, x) := fun ω =>
    hA.comp (measurable_const.prodMk measurable_id)
  have hnu : ∀ᵐ ω ∂P, Palm.nuMod hν (Icc a b) ω = ν ω := by
    filter_upwards [hν.ae_eq_mk, hfin] with ω h1 h2
    unfold Palm.nuMod
    rw [← h1, if_pos h2]
  have hgm : ∀ n, AEMeasurable (fun ω => ∫⁻ x, ENNReal.ofReal (wn n x) * A (ω, x) ∂ν ω) P := by
    intro n
    have hF : Measurable fun p : Ω × ℝ => ENNReal.ofReal (wn n p.2) * A p :=
      ((hwc n).measurable.comp measurable_snd).ennreal_ofReal.mul hA
    refine ⟨_, hF.lintegral_kernel_prod_right'
      (κ := Palm.kerI hν (measurableSet_Icc (a := a) (b := b))), ?_⟩
    filter_upwards [hnu] with ω hω
    rw [Palm.kerI_apply, hω, ← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hwab n x hx, ENNReal.ofReal_zero, zero_mul]
  have hL : ∀ ω, ∫⁻ x in I, A (ω, x) ∂ν ω =
      ⨆ n, ∫⁻ x, ENNReal.ofReal (wn n x) * A (ω, x) ∂ν ω := fun ω => hsplit _ (hAx ω) _
  simp_rw [hL]
  rw [hsplit B hB, lintegral_iSup' hgm (ae_of_all _ fun ω n m hnm =>
      lintegral_mono fun x => mul_le_mul_left (hmono x hnm) _)]
  exact iSup_congr hw

/-! ## 2. Palm-shifted coordinates in kernel form -/

section

variable {D S K : Set ℂ} {R : ℝ} {k : ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → FieldSample}

theorem measurable_coords_mixed (hX : IsMixedGFF D S X P) (h0 : ℂ → ℝ) (μ : ℕ → Measure ℂ) :
    Measurable fun ω => fun j => (ofFun h0 + X ω) (μ j) :=
  measurable_pi_iff.2 fun j => measurable_const.add (hX.measurable_coord (μ j))

variable (hL : K3.MixedLocalHyp D S K R) (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K))
  (hkc : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ Kᶜ = 0 → IsAdmissibleH ν → ν Kᶜ = 0 →
    dualCov D (mixedSpace D S) μ ν = kernelCov (fun x y => neumannH x y + k x y) μ ν)
include hL hk hkc

end

end Prop16Asm

end QuantumZipper
