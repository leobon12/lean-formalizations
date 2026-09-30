import QuantumZipper.Proofs.Section5.Prop16ShiftGoodBasic
import QuantumZipper.Proofs.Section5.Prop16NodeCMaskFinal

/-!
# Proposition 1.6, node C′: the Palm-shifted mixed field has a local area measure

Node C′ of Proposition 1.6 (`Prop16Asm.Prop16PalmShiftGoodStmt`, `Prop16NodeCMaskFinal.lean`): for
a mixed GFF `X` on `D` with free arc `[c,d]`, a.s. locally nice on `D ∪ (a,b)` and a point
`x ∈ (a,b)`, almost surely the zoomed Palm-shifted field `(X + (γ/2) G_D(x, ·))(· + x) + C/γ +
𝔥₀(x)` has a local area measure on `D − x`.

Mathematically (Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25): near the free-arc point `x`
the Palm shift is `G_D(x, ·) = -2 log|· − x| + (harmonic, continuous on D)`, so the Palm-shifted
field is a locally nice field plus a function continuous on `D`; the LQG area measure of a locally
nice field with a continuous additive function exists by the local rule (5.1)
(`Prop16Area.G.exists_limit_of_agree`).

The deterministic content is isolated in two steps:

* `PalmCircRepStmt` (global M6 node, proved as `palmCircRepStmt_proved` in `Prop16ShiftGoodPalm.lean`): the Palm shift agrees, on the dyadic
  folded circles inside `D`, with `ofFun ψ` for a single function `ψ` continuous on `D`. By
  `Prop16ShiftGoodBasic.tendsto_mixedGreenSample_fc` the per-compact kernels `mixedGreenK K k x ·`
  of K3 node M6 agree on the interiors of their compacts (they both are the limit of the same
  circle values), so this is the statement that the mixed Green function on `D` is a genuine
  continuous function away from the free arc; it needs a compact cover of `D` by compacts satisfying
  `K3.MixedLocalHyp` together with `x` and the small circles around `x`.
* `exists_limit_zoomFree_palmMixedField`: given such a `ψ`, the local area measure exists
  (transport of `CircAgree` through translation/zoom and `exists_limit_of_agree`);
* `prop16PalmShiftGoodStmt_of_palmCircRep`: the a.s. statement, one line.

Sources: Sheffield, arXiv:1012.4797 (Prop. 1.6, p. 25); Duplantier–Sheffield, arXiv:0808.1560, §6.1
(rule (5.1)). Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization Prop16Area Prop16Area.G

/-- Composition of additive constants. -/
theorem addConst_addConst (x : FieldSample) (c₁ c₂ : ℝ) :
    addConst (addConst x c₁) c₂ = addConst x (c₁ + c₂) := by
  funext μ
  simp only [addConst]
  ring

/-- **The Palm shift is a continuous function inside `D` (global M6 node; proved in `Prop16ShiftGoodPalm.lean`).** For the
domain `D` of Proposition 1.6 with free arc `[c,d]` and `x` in the free arc, the Palm shift
`mixedGreenSample D S x` agrees, on every dyadic folded circle inside `D`, with `ofFun ψ` for one
function `ψ` continuous on `D` (the mixed Green function `G_D(x, ·)`, which is harmonic and
continuous away from `x ∉ D`). -/
def PalmCircRepStmt : Prop :=
  ∀ (D : Set ℂ) (c d x : ℝ), K3.Prop16Geometry D c d → x ∈ Ioo c d →
    ∃ ψ : ℂ → ℝ, ContinuousOn ψ D ∧
      CircAgree D (mixedGreenSample D (realSet (Icc c d)) x) (ofFun ψ)

/-- **Deterministic core of node C′.** For a field which is locally nice on `D ∪ (a,b)` and whose
Palm shift is a continuous function `ψ` on `D`, the zoomed Palm-shifted field has a local area
measure on `D − x`. -/
theorem exists_limit_zoomFree_palmMixedField {γ : ℝ} {D S : Set ℂ} {a b x : ℝ} {h0 : ℂ → ℝ}
    {Ω : Type} (X : Ω → FieldSample) (ω : Ω) (hDo : IsOpen D) (hDH : D ⊆ H)
    {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ D)
    (hagP : CircAgree D (mixedGreenSample D S x) (ofFun ψ))
    (hloc : IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (X ω)) (C : ℝ) :
    ∃ m, IsVagueLimitOn (zoomDomain D x)
      (areaApprox γ (zoomFree γ C h0 (palmMixedField γ D S X x) (ω, x))) m := by
  obtain ⟨W, hWo, hWV, y, ψ₀, hy, -, -, hψ₀, hag⟩ := hloc
  have hDW : D ⊆ W := fun z hz => by
    have : z ∈ W ∩ Hbar := by rw [hWV]; exact Or.inl hz
    exact this.1
  -- the Palm-shifted field agrees with `y + ofFun φ`, `φ = ψ₀ + (γ/2) ψ`
  have h1 : CircAgree D (X ω) (y + ofFun ψ₀) := fun n k z hz hW => hag n k z hz (hW.trans hDW)
  have hψ₀D : ContinuousOn ψ₀ D := hψ₀.mono subset_union_left
  set φ : ℂ → ℝ := fun z => ψ₀ z + γ / 2 * ψ z with hφdef
  have h3 : CircAgree D (palmMixedField γ D S X x ω) (y + ofFun φ) := by
    intro n k z hz hW
    have hX := h1 n k z hz hW
    have hP := hagP n k z hz hW
    have hz' := CircleCont.dyadicRoundC_mem_Hbar hz n
    have hr := radius_pos k
    simp only [palmMixedField, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofFun, hφdef] at hX hP ⊢
    rw [hX, hP, integral_add (f := ψ₀) (g := fun z => γ / 2 * ψ z)
      (integrable_fc_of_continuousOn hz' hr (hψ₀D.mono hW))
      (integrable_fc_of_continuousOn hz' hr ((continuousOn_const.mul hψ).mono hW)),
      integral_const_mul]
    ring
  have hφ : ContinuousOn φ D := hψ₀D.add (continuousOn_const.mul hψ)
  have hφH : ContinuousOn φ (D ∩ Hbar) := hφ.mono inter_subset_left
  -- transport through the zoom at `x`
  have hWx : (fun z => z + (x : ℂ)) ⁻¹' D = zoomDomain D x := rfl
  have hzo : IsOpen ((fun z => z + (x : ℂ)) ⁻¹' D) :=
    hDo.preimage (continuous_id.add continuous_const)
  have hA : FcAgree ((fun z => z + (x : ℂ)) ⁻¹' D) (translate (palmMixedField γ D S X x ω) (x : ℂ))
      (translate (y + ofFun φ) (x : ℂ)) := fcAgree_translate hDo h3 x
  have hB := fcAgree_translate_add_ofFun hy.1 hDo hφH x
  have hfin : CircAgree ((fun z => z + (x : ℂ)) ⁻¹' D)
      (zoomFree γ C h0 (palmMixedField γ D S X x) (ω, x))
      (addConst (translate y (x : ℂ)) (C / γ + h0 x) + ofFun (fun u => φ (u + x))) := by
    have h := fcAgree_addConst (hA.trans hB) (C / γ + h0 x)
    rw [addConst_add_ofFun] at h
    rw [show zoomFree γ C h0 (palmMixedField γ D S X x) (ω, x) =
      addConst (translate (palmMixedField γ D S X x ω) (x : ℂ)) (C / γ + h0 x) from by
        simp only [zoomFree, zoomField, addConst_addConst]]
    exact h.circAgree
  refine exists_limit_of_agree hzo ((hy.translate x).addConst (C / γ + h0 x))
    (hφ.comp (continuous_id.add continuous_const).continuousOn fun u hu => hu.1) hfin
    (hDo.preimage (continuous_id.add continuous_const)) (fun z hz => ?_) (fun z hz => hz)
  have h' : 0 < (z + (x : ℂ)).im := hDH hz
  show 0 < z.im
  simpa using h'

/-- **Node C′ from the remaining global-M6 node** (`Prop16PalmShiftGoodStmt`). -/
theorem prop16PalmShiftGoodStmt_of_palmCircRep (hrep : PalmCircRepStmt) :
    Prop16PalmShiftGoodStmt := by
  intro γ D c d a b h0 _hγ _hγ2 hgeo _hab hca hbd Ω _ P X _hP _hX hn x hx C
  obtain ⟨hDo, -, -, hDH, -, -, -⟩ := id hgeo
  have hxcd : x ∈ Ioo c d := ⟨lt_of_le_of_lt hca hx.1, lt_of_lt_of_le hx.2 hbd⟩
  obtain ⟨ψ, hψ, hagP⟩ := hrep D c d x hgeo hxcd
  filter_upwards [hn] with ω hloc
  exact exists_limit_zoomFree_palmMixedField (γ := γ) (h0 := h0) (S := realSet (Icc c d))
    X ω hDo hDH hψ hagP hloc C

end Prop16Asm

end QuantumZipper
