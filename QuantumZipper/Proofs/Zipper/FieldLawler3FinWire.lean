import QuantumZipper.Proofs.Zipper.FieldLawler3Fin
import QuantumZipper.Proofs.Zipper.FieldLawler3ExistLoew
import QuantumZipper.Proofs.RS.GenerationCor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-FIN wiring: `flExist_loewner_arcs` without the `hfin` hypothesis

For the Loewner trace under the hypotheses of `FLImageSumBoundStmt` (simple trace, `K_t = γ((0,t])`,
first hitting of `{|z| = R}` at `t`), the finiteness hypothesis `hfin` of `flExist_loewner_arcs`
holds by `flFin_components`; `ℍ \ K_t` is preconnected by `RS.isPreconnected_compl_fwdHull`.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- **Harmonic measure of the removed arcs**, `hfin` discharged. -/
theorem flExist_loewner_arcs_trace {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t R ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (hεR : ε < R)
    (htr0 : trace W 0 = 0) (hcont : ContinuousOn (trace W) (Icc 0 t))
    (hH : ∀ s ∈ Ioc 0 t, trace W s ∈ H) (hhull : fwdHull W t = trace W '' Ioc 0 t)
    (hγR : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (hγt : ‖trace W t‖ = R)
    {ι : Type*} (I₀ : Finset ι) {α β : ι → ℝ} (hαβ : ∀ i ∈ I₀, α i ≤ β i)
    (hend : ∀ i ∈ I₀, (ε : ℂ) * exp (α i * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0} ∧
      (ε : ℂ) * exp (β i * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0})
    (harc : ∀ i ∈ I₀, flCircArc ε (α i) (β i) ⊆ H \ trace W '' Ioc 0 t) :
    ∃ g : ℂ → ℝ, IsHarmMeas (((H \ trace W '' Ioc 0 t) ∩ ball 0 R) \
      ⋃ i ∈ I₀, flCircArc ε (α i) (β i)) (⋃ i ∈ I₀, flCircArc ε (α i) (β i)) g :=
  flExist_loewner_arcs ht (by linarith) hcont htr0 I₀ hαβ hend
    (flFin_components ht hε hεR hcont htr0 hH hγR hγt
      (by rw [← hhull]; exact RS.isPreconnected_compl_fwdHull hW hW0 ht) I₀ hend harc)

end FieldLawler
end QuantumZipper
