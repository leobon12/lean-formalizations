import QuantumZipper.Proofs.Thm18.G1RCComm
import QuantumZipper.Proofs.Zipper.RegUnifDet

/-!
# G1-RC, part 5: RC2 and every-circle RC3 from one raw representation

A field sample `x` whose raw values at **all** folded circles `fc(d, r)`, `d ∈ Hbar`, `r > 0`,
are given by a function `F` continuous on `Hbar × (0,∞)` and smoothing-symmetric is regular with
witness `F` (RC2) and satisfies RC3 at every folded circle (`G1RC.rc_of_raw`, deterministic: the
regularized value `evalReg x (fc d r)` is `F (d, r)` for a regular sample).

`G1RC.ae_rc_of_smoothing` is the probabilistic form used for the pulled-back canonical wedge
field `x = coordChange (wedgeRep γ X A) ψ Q` (G1 core, DECISIONS.md D32): if, almost surely, the
raw value `x(fc(d, r))` is `L + D(d, r)` (with `D` a random continuous smoothing-symmetric part)
**whenever** the circle-smoothed pairings `∫ G(u, S 2^{-k}) d((S ψ)_* fc(d, r))(u)` of a regular
version `G` of the free field converge to `L` (`k → ∞`), at a **random** scale `S > 0` (the
canonical scale), then `x` is
a.s. a regular sample and satisfies RC3 at every folded circle. The witness is
`V(d, r, S) + D(d, r)` with `V` from `exists_pushed_limit` and the commutation from
`ae_comm_pushed`.

Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (via G1RC{Kolm,Eval,Circle,
Comm}); the assembly is own bookkeeping (`RegUnif.isRegularWith_of_witness`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK

/-- **RC2 and every-circle RC3 from a raw representation at all folded circles.** -/
theorem rc_of_raw {x : FieldSample} {F : ℂ × ℝ → ℝ} (hFc : ContinuousOn F (Hbar ×ˢ Ioi 0))
    (hcomm : ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ →
      ∫ u, F (u, ρ) ∂foldedCircle w r = ∫ v, F (v, r) ∂foldedCircle w ρ)
    (hraw : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = F (d, r)) :
    IsRegularWith x F ∧ ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → evalReg x (foldedCircle d r) =
      x (foldedCircle d r) := by
  have hreg : IsRegularWith x F := (RegUnif.isRegularWith_of_witness hFc
    (fun k d hd => hraw d (RegUnif.Dy_subset_Hbar hd) _ (radius_pos k)) hcomm).1
  exact ⟨hreg, fun d hd r hr => by rw [hreg.evalReg_fc_of_mem hd hr, hraw d hd r hr]⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

/-- **RC2 + RC3 at a random scale from the smoothing identification of the raw values.** -/
theorem ae_rc_of_smoothing {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψc : ContinuousOn ψ Hbar)
    (hψH : MapsTo ψ Hbar Hbar) {β : ℝ} (hβ : 0 < β) (hB : PushFamBounds ψ β)
    (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G)
    {x : Ω → FieldSample} {S : Ω → ℝ} {D : Ω → ℂ × ℝ → ℝ}
    (hD : ∀ᵐ ω ∂P, 0 < S ω ∧ ContinuousOn (D ω) (Hbar ×ˢ Ioi 0) ∧
      ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ →
        ∫ u, D ω (u, ρ) ∂foldedCircle w r = ∫ v, D ω (v, r) ∂foldedCircle w ρ)
    (hlim : ∀ᵐ ω ∂P, ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → ∀ L : ℝ,
      Tendsto (fun k : ℕ => ∫ u, G ω (u, S ω * radius k)
          ∂((foldedCircle d r).map fun z => (S ω : ℂ) * ψ z)) atTop (𝓝 L) →
        x ω (foldedCircle d r) = L + D ω (d, r)) :
    ∀ᵐ ω ∂P, IsRegularSample (x ω) ∧ ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (x ω) (foldedCircle d r) = x ω (foldedCircle d r) := by
  obtain ⟨V, hVc, hVV, hVlim⟩ := exists_pushed_limit hψm hψc hψH hβ hB hX hG
  filter_upwards [hD, hlim, hVlim, ae_comm_pushed hψm hB hX hVc hVV] with ω ⟨hS, hDc, hDs⟩
    hl hVl hcomm
  set F : ℂ × ℝ → ℝ := fun p => V (p.1, p.2, S ω) ω + D ω p with hF
  have hVs : ContinuousOn (fun p : ℂ × ℝ => V (p.1, p.2, S ω) ω) (Hbar ×ˢ Ioi 0) :=
    (hVc ω).comp (by fun_prop : Continuous fun p : ℂ × ℝ => (p.1, p.2, S ω)).continuousOn
      fun p hp => ⟨mem_univ _, hp.2, hS⟩
  have hFc : ContinuousOn F (Hbar ×ˢ Ioi 0) := hVs.add hDc
  have hslice : ∀ {g : ℂ × ℝ → ℝ}, ContinuousOn g (Hbar ×ˢ Ioi 0) → ∀ {ρ : ℝ}, 0 < ρ →
      ∀ (w : ℂ) {r : ℝ}, 0 ≤ r → Integrable (fun u => g (u, ρ)) (foldedCircle w r) :=
    fun hg ρ hρ w r hr => RegClosure.integrable_fc (hg.comp
      (continuous_id.prodMk continuous_const).continuousOn fun u hu => ⟨hu, hρ⟩) w hr
  refine (fun h => ⟨⟨F, h.1⟩, h.2⟩) (rc_of_raw hFc ?_ ?_)
  · intro w hw r ρ hr hρ
    show ∫ u, (V (u, ρ, S ω) ω + D ω (u, ρ)) ∂foldedCircle w r =
      ∫ v, (V (v, r, S ω) ω + D ω (v, r)) ∂foldedCircle w ρ
    rw [integral_add (hslice hVs hρ w hr.le) (hslice hDc hρ w hr.le),
      integral_add (hslice hVs hr w hρ.le) (hslice hDc hr w hρ.le),
      hcomm w hw r ρ (S ω) hr hρ hS, hDs w hw r ρ hr hρ]
  · intro d hd r hr
    have ht : Tendsto (fun k : ℕ => S ω * radius k) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k =>
        mul_pos hS (radius_pos k)⟩
      have hr0 : Tendsto radius atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using hr0.const_mul (S ω)
    exact hl d hd r hr _ ((hVl d r (S ω) hr hS).comp ht)

end G1RC
end Thm18Asm
end QuantumZipper
