import QuantumZipper.Proofs.Section5.Prop16D4WInScale
import QuantumZipper.Proofs.Section5.Prop16MeasInst
import QuantumZipper.Proofs.Zipper.D3PlusProb

/-!
# D4⁺ʷ inputs (part 4): clause `hsc0` (the local scale tends to `0` in probability)

Under the weighted law `Q = prop16Q`, the local scale `a_C` of the unperturbed zoomed field
`zoomFree γ C 𝔥₀ X` on `D − t` satisfies `Q{¬(0 < a_C < δ)} → 0` (`prop16_hsc0`), given that
the mixed field is almost surely locally nice on `D ∪ (a,b)` (`IsLocNiceOn`).

Proof (own elementary argument): by `scale_point`, `Q`-a.s. the event `¬(0 < a_C < δ)` is
eventually false and antitone in `C`. The scale is a.e.-measurable (`aemeasurable_zoomFree_scale`:
`𝔥₀(t)` is replaced by a measurable version equal to it on `(a,b)`, where `Q` lives, and the
generic `Prop16Area.Meas.aemeasurable_scaleParamOn` applies). A.s. eventual avoidance of
null-measurable events gives convergence of probabilities along integers
(`D3Plus.tendsto_measure_of_ae_eventually_notMem`), and antitonicity passes to real `C`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G Prop16Area.Meas TV Factorization

variable {Ω : Type} [MeasurableSpace Ω]

/-- The scale of the unperturbed zoomed field is a.e.-measurable under the weighted law. -/
theorem aemeasurable_zoomFree_scale {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ}
    {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P)
    (hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω)) (C : ℝ) :
    AEMeasurable (fun p => scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2))
      (prop16Q γ h0 a b P X) := by
  classical
  have hdat' := hdat
  obtain ⟨-, -, ⟨hDo, -, -, hDH, -⟩, -, -, -, hh0, -, hX, -, hfin⟩ := hdat'
  set Q := prop16Q γ h0 a b P X
  have hXm : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ := fun μ => hX.measurable_coord μ
  have hta : ∀ᵐ p ∂Q, p.2 ∈ Ioo a b :=
    ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b) (aemeasurable_prop16Kernel' hν hfin)
      (fun ω => sFinite_prop16Nu γ h0 a b (X ω)) (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
      (ae_of_all _ fun _ _ ht => ht)
  -- a measurable version of `t ↦ 𝔥₀(t)`
  set F : ℝ → ℝ := (Ioo a b).piecewise (fun s => h0 s) 0 with hF
  have hFm : Measurable F := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ioo
    exact hh0.comp Complex.continuous_ofReal.continuousOn fun s hs => Or.inr ⟨s, hs, rfl⟩
  set xg : Ω × ℝ → FieldSample := fun p => addConst (zoomField γ C (X p.1) p.2) (F p.2)
  have e0 : ∀ ω, ofFun (fun _ => (0 : ℝ)) + X ω = X ω := fun ω => by
    funext μ; simp [ofFun]
  have hZ : Measurable fun p : Ω × ℝ => coords (zoomField γ C (X p.1) p.2) := by
    have := measurable_coords_zoomField γ C (fun _ => (0 : ℝ)) hXm
    simpa only [e0] using this
  have hxc : Measurable fun p => coords (xg p) := by
    refine measurable_pi_iff.2 fun i => ?_
    have e : (fun p => coords (xg p) i) = fun p => coords (zoomField γ C (X p.1) p.2) i +
        F p.2 * ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) univ).toReal := by
      funext p; rfl
    rw [e]
    exact ((measurable_pi_apply i).comp hZ).add ((hFm.comp measurable_snd).mul measurable_const)
  have hxm : Measurable fun p => recon (xg p) := measurable_reconstruct.comp hxc
  have hDc : Dᶜ.Nonempty := ⟨0, fun h => by simpa [H] using hDH h⟩
  have hφ := isBumpFamily_comp (α := Ω × ℝ) hDo hDc (g := fun p z => z + (p.2 : ℂ))
    (by fun_prop) (fun p => by fun_prop)
  have hxe : ∀ᵐ p ∂Q, xg p = zoomFree γ C h0 X p := by
    filter_upwards [hta] with p hp
    simp only [xg, zoomFree, hF, Set.piecewise_eq_of_mem _ _ _ hp]
  have hloc := prop16_hloc hdat hν hlg C
  have hG : NullMeasurableSet (goodSet γ (fun p => recon (xg p))
      (fun p => (fun z => z + (p.2 : ℂ)) ⁻¹' D)) Q := by
    refine nullMeasurableSet_of_ae ?_
    filter_upwards [hxe, hloc] with p hp hl
    obtain ⟨⟨W, hWo, hWV, y, ψ, hy, hψ, hag⟩, hUV, -⟩ := hl
    show ∃ m, IsVagueLimitOn _ (areaApprox γ (recon (xg p))) m
    rw [areaApprox_recon, hp]
    have hUo : IsOpen (zoomDomain D p.2) := hDo.preimage (continuous_id.add continuous_const)
    have hUH : zoomDomain D p.2 ⊆ H := fun z hz => by
      have : 0 < (z + (p.2 : ℂ)).im := hDH hz
      show 0 < z.im
      simpa using this
    exact exists_limit_of_agree hWo hy (hWV ▸ hψ) hag hUo hUH
      fun z hz => by have := hUV hz; rw [← hWV] at this; exact this.1
  have h := aemeasurable_scaleParamOn (γ := γ) hxm hφ (μ := Q) hG
  refine h.congr ?_
  filter_upwards [hxe] with p hp
  change scaleParamOn γ (recon (xg p)) (zoomDomain D p.2) = _
  rw [scaleParamOn_recon, hp]

/-- The bad event of clause `hsc0`. -/
def scBad (γ δ : ℝ) (h0 : ℂ → ℝ) (D : Set ℂ) (X : Ω → FieldSample) (C : ℝ) : Set (Ω × ℝ) :=
  {p | ¬ (0 < scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) ∧
    scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) < δ)}

/-- **Clause `hsc0` of `Prop16D4WInputsStmt`.** -/
theorem prop16_hsc0 {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ} {P : Measure Ω}
    {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P)
    (hnice : ∀ᵐ ω ∂P, IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (X ω)) :
    ∀ δ > 0, Tendsto (fun C => prop16Q γ h0 a b P X
      {p | ¬ (0 < scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) ∧
        scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) < δ)}) atTop (𝓝 0) := by
  intro δ hδ
  change Tendsto (fun C => prop16Q γ h0 a b P X (scBad γ δ h0 D X C)) atTop (𝓝 0)
  have hdat' := hdat
  obtain ⟨hγ, -, ⟨hDo, -, -, hDH, -, -, hhd⟩, -, hca, hbd, -, -, -, hpos, hfin⟩ := hdat'
  have : IsProbabilityMeasure (prop16Q γ h0 a b P X) := isProbabilityMeasure_prop16Law' hν hpos hfin
  have hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω) :=
    hnice.mono fun _ h => h.isLocallyGoodOn
  have hG : ∀ᵐ p ∂(prop16Q γ h0 a b P X), (∀ᶠ C in atTop, p ∉ scBad γ δ h0 D X C) ∧
      ∀ C' C, C' ≤ C → p ∈ scBad γ δ h0 D X C → p ∈ scBad γ δ h0 D X C' := by
    refine ae_prop16Law_of_ae (G := fun ω t =>
        (∀ᶠ C in atTop, (ω, t) ∉ scBad γ δ h0 D X C) ∧
        ∀ C' C, C' ≤ C → (ω, t) ∈ scBad γ δ h0 D X C → (ω, t) ∈ scBad γ δ h0 D X C')
      (aemeasurable_prop16Kernel' hν hfin) (fun ω => sFinite_prop16Nu γ h0 a b (X ω))
      (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω)) ?_
    filter_upwards [hnice] with ω hω t ht
    obtain ⟨r, hr, hrD⟩ := hhd t ⟨lt_of_le_of_lt hca ht.1, lt_of_lt_of_le ht.2 hbd⟩
    have hsp := scale_point hγ hDo hDH hω ht hr hrD (h0 t)
    simp only [scBad, mem_ofPred_eq, zoomFree, not_not]
    exact ⟨hsp.1 δ hδ, hsp.2 δ⟩
  have hAm : ∀ C, NullMeasurableSet (scBad γ δ h0 D X C) (prop16Q γ h0 a b P X) := by
    intro C
    have e : scBad γ δ h0 D X C = (fun p => scaleParamOn γ (zoomFree γ C h0 X p)
        (zoomDomain D p.2)) ⁻¹' (Ioi 0 ∩ Iio δ)ᶜ := by
      ext p; simp only [scBad, mem_ofPred_eq, mem_preimage, mem_compl_iff, mem_inter_iff,
        mem_Ioi, mem_Iio]
    rw [e]
    exact (aemeasurable_zoomFree_scale hdat hν hlg C).nullMeasurable
      ((measurableSet_Ioi.inter measurableSet_Iio).compl)
  have hnat : Tendsto (fun n : ℕ => prop16Q γ h0 a b P X (scBad γ δ h0 D X n)) atTop (𝓝 0) := by
    refine D3Plus.tendsto_measure_of_ae_eventually_notMem (fun n => hAm n) ?_
    filter_upwards [hG] with p hp
    exact tendsto_natCast_atTop_atTop.eventually hp.1
  have hle : ∀ᶠ C in atTop, prop16Q γ h0 a b P X (scBad γ δ h0 D X C) ≤
      prop16Q γ h0 a b P X (scBad γ δ h0 D X ⌊C⌋₊) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with C hC
    refine measure_mono_ae ?_
    filter_upwards [hG] with p hp hpA
    exact hp.2 _ _ (Nat.floor_le hC) hpA
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hnat.comp tendsto_nat_floor_atTop) (Eventually.of_forall fun _ => zero_le) hle

end Prop16Asm

end QuantumZipper
