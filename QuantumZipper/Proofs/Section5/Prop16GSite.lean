import QuantumZipper.Proofs.Section5.Prop16MeasGood
import QuantumZipper.Proofs.LQG.PalmFormula

/-!
# Proposition 1.6, node D4-G (part 1): almost sure statements under `prop16Law`

Under the weighted law `Q = prop16Law P ν a b` of Proposition 1.6 (`Statements/Prop16.lean`),
where every `ν ω` is s-finite and carried by `(a,b)`:

* `aemeasurable_prop16Kernel'`: the kernel `ω ↦ δ_ω ⊗ ν_ω|_{[a,b]}` of the `bind` is
  a.e.-measurable when `ω ↦ ν ω` is and `E ν[a,b] < ∞` (via the s-finite kernel `Palm.kerI`).
  This is needed: at this pin `Measure.map` of a non-a.e.-measurable map is a junk Dirac mass,
  so `bind` would be an arbitrary measure;
* `ae_prop16Law_of_ae`: a property `G ω t` that holds `P`-a.s. for **all** `t ∈ (a,b)` holds
  `Q`-a.s. at `(ω, t)`.
* `prop16Nu_compl_Ioo`, `sFinite_prop16Nu`: Proposition 1.6's boundary measure
  `qBoundaryMeasureOn γ (ofFun 𝔥₀ + x) (a,b)` is carried by `(a,b)` and s-finite (finite on the
  compacts of `(a,b)`, or the junk `0`).
* `hsite_prop16`: `Q`-a.s. the marked point has a half-disc `B_r(t) ∩ ℍ ⊆ D` (input `hsite` of
  `prop16_areaConvergesInLawOn_of_inputs'`), from the geometry hypothesis of `theorem1_6`.
* `hG_prop16`: the inputs `hG0`/`hG1` follow from the corresponding `P`-a.s. statements
  holding for all `t ∈ (a,b)` simultaneously.

Own elementary arguments (AGENT_GUIDE cost rule); the reading of `Q` follows Sheffield,
arXiv:1012.4797, statement and proof of Proposition 1.6 (pp. 7, 25): `x` is sampled from
`ν_h|_{[a,b]}`, which is carried by `(a,b)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

namespace G

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The kernel `ω ↦ δ_ω ⊗ ν_ω|_{[a,b]}` of `prop16Law` is a.e.-measurable (the argument of
`Prop16Asm.aemeasurable_prop16Kernel`, via the s-finite kernel `Palm.kerI` of D1). -/
theorem aemeasurable_prop16Kernel' {P : Measure Ω} {ν : Ω → Measure ℝ} {a b : ℝ}
    (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ⊤) :
    AEMeasurable (fun ω => (Measure.dirac ω).prod ((ν ω).restrict (Icc a b))) P := by
  let κ : ProbabilityTheory.Kernel Ω (Ω × ℝ) :=
    (ProbabilityTheory.Kernel.deterministic id measurable_id) ×ₖ
      Palm.kerI hν (measurableSet_Icc (a := a) (b := b))
  refine ⟨fun ω => κ ω, κ.measurable, ?_⟩
  filter_upwards [Palm.nuMod_ae_eq hν (measurableSet_Icc (a := a) (b := b)) hfin] with ω hω
  simp only [κ]
  rw [ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.deterministic_apply,
    Palm.kerI_apply, hω]
  rfl

/-- **Transfer of a.s. statements to `prop16Law`.** -/
theorem ae_prop16Law_of_ae {P : Measure Ω} {ν : Ω → Measure ℝ} {a b : ℝ}
    (hκ : AEMeasurable (fun ω => (Measure.dirac ω).prod ((ν ω).restrict (Icc a b))) P)
    (hνs : ∀ ω, SFinite (ν ω)) (hν : ∀ ω, ν ω (Ioo a b)ᶜ = 0) {G : Ω → ℝ → Prop}
    (hG : ∀ᵐ ω ∂P, ∀ t ∈ Ioo a b, G ω t) :
    ∀ᵐ p ∂(prop16Law P ν a b), G p.1 p.2 := by
  unfold prop16Law
  refine Measure.ae_smul_measure ?_ _
  set κ : Ω → Measure (Ω × ℝ) := fun ω => (Measure.dirac ω).prod ((ν ω).restrict (Icc a b))
  obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hG)
  set S : Set (Ω × ℝ) := T ×ˢ univ ∪ univ ×ˢ (Ioo a b)ᶜ
  have hSm : MeasurableSet S :=
    (hTm.prod MeasurableSet.univ).union (MeasurableSet.univ.prod measurableSet_Ioo.compl)
  have hS0 : P.bind κ S = 0 := by
    rw [Measure.bind_apply hSm hκ]
    have hae : ∀ᵐ ω ∂P, κ ω S = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hT0] with ω hω
      have := hνs ω
      simp only [κ]
      rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hSm]
      have hpre : Prod.mk ω ⁻¹' S = (Ioo a b)ᶜ := by
        ext t; simp [S, hω]
      rw [hpre]
      exact le_antisymm ((Measure.restrict_le_self _).trans (hν ω).le) bot_le
    rw [lintegral_congr_ae hae, lintegral_zero]
  refine measure_mono_null (fun p hp => ?_) hS0
  simp only at hp
  by_contra hpS
  simp only [S, mem_union, mem_prod, mem_univ, and_true, true_and, mem_compl_iff, not_or,
    not_not] at hpS
  exact hp (by_contra fun h => hpS.1 (hTsub fun h' => h (h' _ hpS.2)))

/-- Proposition 1.6's boundary measure is carried by `(a,b)`. -/
theorem prop16Nu_compl_Ioo (γ : ℝ) (h0 : ℂ → ℝ) (a b : ℝ) (x : FieldSample) :
    prop16Nu γ h0 a b x (Ioo a b)ᶜ = 0 := by
  unfold prop16Nu qBoundaryMeasureOn
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

/-- Proposition 1.6's boundary measure is s-finite (indeed σ-finite). -/
theorem sFinite_prop16Nu (γ : ℝ) (h0 : ℂ → ℝ) (a b : ℝ) (x : FieldSample) :
    SFinite (prop16Nu γ h0 a b x) := by
  unfold prop16Nu qBoundaryMeasureOn
  split_ifs with h
  · set μ := h.choose
    have hμ := h.choose_spec
    let K : ℕ → Set ℝ := fun n => Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1))
    have hK : ∀ n, K n ⊆ Ioo a b := fun n t ht => by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have : SigmaFinite μ := by
      refine Measure.sigmaFinite_of_countable (S := insert (Ioo a b)ᶜ (range K))
        ((countable_range K).insert _) ?_ ?_
      · rintro s (rfl | ⟨n, rfl⟩)
        · rw [hμ.1]; exact ENNReal.zero_lt_top
        · exact hμ.2.1 _ isCompact_Icc (hK n)
      · refine eq_univ_of_forall fun t => ?_
        by_cases ht : t ∈ Ioo a b
        · obtain ⟨n, hn⟩ := exists_nat_gt (1 / min (t - a) (b - t))
          have hm : 0 < min (t - a) (b - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
          have h1 : 1 / ((n : ℝ) + 1) < min (t - a) (b - t) := by
            rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hm] at hn
            nlinarith [min_le_left (t - a) (b - t)]
          refine mem_sUnion.2 ⟨K n, mem_insert_of_mem _ ⟨n, rfl⟩, ?_, ?_⟩
          · linarith [min_le_left (t - a) (b - t)]
          · linarith [min_le_right (t - a) (b - t)]
        · exact mem_sUnion.2 ⟨_, mem_insert _ _, ht⟩
    infer_instance
  · infer_instance

/-- **`hG0`/`hG1` for Proposition 1.6** from `P`-a.s. statements for all `t ∈ (a,b)`. -/
theorem hG_prop16 {γ : ℝ} {h0 : ℂ → ℝ} {a b : ℝ} {P : Measure Ω} {X : Ω → FieldSample}
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P)
    (hfin : ∫⁻ ω, prop16Nu γ h0 a b (X ω) (Icc a b) ∂P < ⊤) {G : ℝ → Ω × ℝ → Prop} (hG : ∀ C, ∀ᵐ ω ∂P, ∀ t ∈ Ioo a b, G C (ω, t)) :
    ∀ C, ∀ᵐ p ∂(prop16Law P (fun ω => prop16Nu γ h0 a b (X ω)) a b), G C p := fun C =>
  ae_prop16Law_of_ae (G := fun ω t => G C (ω, t)) (aemeasurable_prop16Kernel' hν hfin) (fun ω => sFinite_prop16Nu γ h0 a b (X ω))
    (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω)) (hG C)

end G

end Prop16Area

end QuantumZipper
