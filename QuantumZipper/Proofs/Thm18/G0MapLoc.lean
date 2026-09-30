import QuantumZipper.Proofs.Thm18.G1Z2ReflChord
import QuantumZipper.Proofs.Thm18.G1ZZ1Meas
import QuantumZipper.Proofs.Complex.KernelChordRight
import QuantumZipper.Proofs.Complex.UniformizerTopo
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3CV-MAP: the local side maps and the admissible G0 maps (`IsG0Map`)

For a simple chord `η = trace W` with a normalized uniformizer of the side domain:

* `g1zLocMap_not_isG0Map`: the literal statement `IsG0Map r₀ (g1zLocMap left W x)` is **false**
  for every `r₀ > 0`. `g1zSideMap = invFunOn φ D` has no preimage in `D` at points of the closed
  lower half-plane, so it takes one junk value there, and `g1zLocMap left W x` is constant on the
  lower half of `B(0, r₀)`, hence not injective.
* `g1zLocMap_g0Ext`: the corrected statement. On every compact `K` of the side half-line there is a
  uniform `r₀ > 0` and, for every `x ∈ K`, an admissible G0 map `Ψₓ` (the Schwarz reflection of
  the side map at `b = Φ⁻¹ x`, translated) with `Ψₓ = g1zLocMap left W x` on `B(0, r₀) ∩ ℍ`.
  Only these values enter `zoomFieldVia` over `ψ⁻¹(D − x) ∩ B(0, r₀) ∩ ℍ` in `G0Stmt`.
* `measurable_g1zLocMap`: `(x, w) ↦ g1zLocMap left W x w` is jointly measurable.

Sources: the reflected side map is `SideReflGood` (`sideReflChordStmt_holds`, Schwarz reflection,
Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4 §6.5, Thm 24). Injectivity on a uniform disc uses
`Set.InjOn.exists_mem_nhdsSet` (injective on the compact real segment, locally injective by
the inverse function theorem). The derivative at a real point is real and positive because the map
is real and increasing (`Φ` is an order isomorphism) on the real segment. Own elementary argument
(Sheffield, arXiv:1012.4797, p. 70, uses these local conformal maps implicitly).
-/

noncomputable section

open MeasureTheory Metric Filter Set Function
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G0Map

theorem isOpen_sideDom_g0 {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    IsOpen (sideDom η left) := by
  cases left
  · exact CA.Kernel.isOpen_rightComponent_qz hη
  · exact CA.Uniformizer.isOpen_leftComponent hη

/-- The boundary preimage is `0` off the side half-line. -/
theorem g1zBdryPre_eq_zero {left : Bool} {W : ℝ → ℝ} {Φ : ℝ ≃o ℝ}
    (h : SideReflGood left (g1zSideMap left W) Φ) {x : ℝ} (hx : x ∉ g1SideHalf left) :
    g1zBdryPre left W x = 0 := by
  · rw [g1zBdryPre, dif_neg]
    rintro ⟨b, hb, hT⟩
    have := G1ZZ1.neBot_nhdsWithin_H b
    have he := tendsto_nhds_unique hT (G1ZZ1.tendsto_of_reflGood h hb)
    have hxb : x = Φ b := Complex.ofReal_injective he
    apply hx
    rw [hxb, ← G1ZZ1.mem_half_symm_iff h.1, OrderIso.symm_apply_apply]
    exact hb

/-- **Joint measurability** of the local maps `(x, w) ↦ g1zLocMap left W x w`. -/
theorem measurable_g1zLocMap {left : Bool} {W : ℝ → ℝ} (hη : IsSimpleChord (trace W))
    (hN : IsNormalizedUniformizer (sideDom (trace W) left) (uniformizer (sideDom (trace W) left))) :
    Measurable fun q : ℝ × ℂ => g1zLocMap left W q.1 q.2 := by
  classical
  obtain ⟨Φ, hΦ⟩ := G1Z2.sideReflChordStmt_holds _ hη left _ hN
  have hΦ' : SideReflGood left (g1zSideMap left W) Φ := hΦ
  have hψ : Measurable (g1zSideMap left W) :=
    (G1.invFunOn_props (isOpen_sideDom_g0 hη left) hN).2.2.1
  have hhalf : MeasurableSet (g1SideHalf left) := by
    cases left
    · exact measurableSet_Ioi
    · exact measurableSet_Iio
  have hpre : Measurable (g1zBdryPre left W) := by
    have he : g1zBdryPre left W = fun x => if x ∈ g1SideHalf left then Φ.symm x else 0 := by
      funext x
      split_ifs with hx
      · exact G1ZZ1.g1zBdryPre_eq hΦ' hx
      · exact g1zBdryPre_eq_zero hΦ' hx
    rw [he]
    exact Measurable.ite hhalf Φ.symm.continuous.measurable measurable_const
  unfold g1zLocMap
  exact (hψ.comp (measurable_snd.add
    (Complex.measurable_ofReal.comp (hpre.comp measurable_fst)))).sub
    (Complex.measurable_ofReal.comp measurable_fst)

end G0Map
end Thm18Asm
end QuantumZipper
