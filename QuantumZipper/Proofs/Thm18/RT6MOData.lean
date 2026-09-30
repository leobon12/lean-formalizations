import QuantumZipper.Proofs.Thm18.RT6MODefs
import QuantumZipper.Proofs.Thm18.R18RTRound
import QuantumZipper.Proofs.Thm18.RT6Inverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6 (D87): the pieces flow on a standard Borel data space

For Sheffield's inverse argument (arXiv:1012.4797, p. 26; `RT6Inv.InvFlow.group`) the zipper of
D87 is made a map of a standard Borel space: a configuration is encoded by its masked circle
coordinates, its driver at the rational times and a flag recording that the driver is
continuous on `[0,∞)` (`encR`). Continuous drivers are recovered from their rational values
(`decR_encR`), so on configurations with continuous drivers the encoding is injective and the
zipper `zipLenMO` acts through `TR` (`TR_encR`). The data space is standard Borel, so equality
events are measurable, which is what the transfer of a.s. identities from the sample to the law
needs. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The data space: masked circle coordinates, driver at rational times, continuity flag. -/
abbrev RD := ((ℕ → ℝ) × (ℚ → ℝ)) × ℝ

/-- The masked circle coordinates and driver of a configuration. -/
def πdO (c : AreaConfig) : (ℕ → ℝ) × (ℝ≥0 → ℝ) := πd (offData c.toPair)

open Classical in
/-- Encoding of masked data. -/
def encR (e : (ℕ → ℝ) × (ℝ≥0 → ℝ)) : RD :=
  ((e.1, fun q => e.2 (ratNN q)), if Continuous e.2 then 1 else 0)

/-- The measurable encoding (flag set), equal to `encR` on continuous drivers. -/
def encT (d : E6.FullData) : RD := ((d.1.1, fun q => d.2 (ratNN q)), 1)

theorem measurable_encT : Measurable encT := by
  refine Measurable.prodMk (Measurable.prodMk (measurable_fst.comp measurable_fst) ?_)
    measurable_const
  exact measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp measurable_snd

theorem encR_πd_eq_encT {d : E6.FullData} (hc : Continuous d.2) : encR (πd d) = encT d := by
  simp [encR, encT, πd, hc]

/-- Extension of a function of the rational times to `ℝ≥0`. -/
def extR (g : ℚ → ℝ) : ℝ≥0 → ℝ := fun s => limUnder (comap ratNN (𝓝 s)) g

def decR (y : RD) : (ℕ → ℝ) × (ℝ≥0 → ℝ) := (y.1.1, extR y.1.2)

theorem ratNN_eq : ratNN = fun q : ℚ => Real.toNNReal (q : ℝ) := rfl

theorem denseRange_ratNN : DenseRange ratNN := by
  rw [ratNN_eq]
  have hs : Function.Surjective Real.toNNReal := fun x => ⟨x, Real.toNNReal_coe⟩
  exact (hs.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal :
    DenseRange (Real.toNNReal ∘ ((↑) : ℚ → ℝ)))

theorem extR_of_continuous {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    extR (fun q => f (ratNN q)) = f := by
  funext s
  have : NeBot (comap ratNN (𝓝 s)) := by
    refine comap_neBot fun t ht => ?_
    obtain ⟨u, hu, huo, hsu⟩ := mem_nhds_iff.1 ht
    obtain ⟨q, hq⟩ := denseRange_ratNN.exists_mem_open huo ⟨s, hsu⟩
    exact ⟨q, hu hq⟩
  exact ((hf.tendsto s).comp tendsto_comap).limUnder_eq

theorem decR_encR {e : (ℕ → ℝ) × (ℝ≥0 → ℝ)} (hc : Continuous e.2) : decR (encR e) = e := by
  simp only [decR, encR]
  rw [extR_of_continuous hc]

theorem encR_inj {e e' : (ℕ → ℝ) × (ℝ≥0 → ℝ)} (hc : Continuous e.2) (h : encR e = encR e') :
    e = e' := by
  have hf := congrArg Prod.snd h
  have hc' : Continuous e'.2 := by
    by_contra hn
    simp [encR, hc, hn] at hf
  rw [← decR_encR hc, h, decR_encR hc']

/-- Equal encodings of configurations with continuous drivers give equality off the curve. -/
theorem configEqOff_of_encR {c c' : AreaConfig} (hc : Continuous (πdO c).2)
    (h : encR (πdO c) = encR (πdO c')) : ConfigEqOff c.toPair c'.toPair := by
  have e := encR_inj hc h
  have hdrv : ∀ u : ℝ, 0 ≤ u → c.drv u = c'.drv u := fun u hu => by
    have := congrArg (fun p : (ℕ → ℝ) × (ℝ≥0 → ℝ) => p.2 ⟨u, hu⟩) e
    exact this
  have hcur : curveOf c.drv = curveOf c'.drv := curveOf_congr hdrv
  refine ⟨regEqOff_of_coordsOffU fun i hi => ?_, hdrv⟩
  have e' := congrArg (fun p : (ℕ → ℝ) × (ℝ≥0 → ℝ) => p.1 i) e
  simp only [πdO, πd, offData, lawDataOff] at e'
  have hi' : CircleOff (curveOf c.toPair.2) (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2 := by
    show CircleOff (curveOf c.drv) _ _
    rw [hcur]; exact hi
  rw [if_pos hi', if_pos hi] at e'
  exact e'

/-- Transfer of an a.s. identity from the sample to the law, for a.e.-measurable maps. -/
theorem ae_law_of_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → RD}
    (hX : AEMeasurable X P) {f g : RD → RD} (hf : AEMeasurable f (P.map X))
    (hg : AEMeasurable g (P.map X)) (h : ∀ᵐ ω ∂P, f (X ω) = g (X ω)) :
    ∀ᵐ y ∂(P.map X), f y = g y := by
  have hS : MeasurableSet {y | hf.mk f y = hg.mk g y} :=
    measurableSet_eq_fun hf.measurable_mk hg.measurable_mk
  have h1 : ∀ᵐ y ∂(P.map X), hf.mk f y = hg.mk g y := by
    rw [ae_map_iff hX hS]
    filter_upwards [h, ae_of_ae_map hX hf.ae_eq_mk, ae_of_ae_map hX hg.ae_eq_mk] with ω e1 e2 e3
    rw [← e2, ← e3, e1]
  filter_upwards [h1, hf.ae_eq_mk, hg.ae_eq_mk] with y e1 e2 e3
  rw [e2, e3, e1]

end R18
end QuantumZipper
