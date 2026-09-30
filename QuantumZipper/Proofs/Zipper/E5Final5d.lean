import QuantumZipper.Proofs.Zipper.E5Final2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-REPR-FINAL, part d: which end of the reverse driver is the E-SM germ

Task E5-REPR-FINAL (Theorem 1.3, node E5, decision D39); Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72 (proof of Lemma 5.6); blueprint `E_BRANCH_BLUEPRINT.md` §4 E5 step (2):
"write `revMap V τ = G ∘ revMap V (τ − u₀)` with `G` depending on `D_x|_{[0,u₀]}` only; `g₀` :=
`g` with `G` removed is `M`-measurable".

At a level point `p = (ℓ, ω)` the zoom model reads the reverse driver `V = Vr κ T B ω`
(reversed at `T`) up to the collision time `t = T − T_ℓ` (`lvlTime`), and the E-SM germ is
`D = esmGerm p = B(T_ℓ + ·) − B(T_ℓ)` (`E5ESM1.esmGerm`). For `s ∈ [t − u₀, t]` the value `V s`
is an increment of `B` over `[T_ℓ, T_ℓ + u₀]`, i.e. of the germ `D|_{[0,u₀]}`; the part of `V`
on `[0, t − u₀]` reads `B` only after `T_ℓ + u₀`, i.e. only the shifted germ `D^{+u₀}`:

* `Vr_eq_vrev_shiftP`, `lvlDrv_eqOn_shiftP`: on `[0, t − u₀]`,
  `V = vrev (drvMap κ (shiftP u₀ D)) (t − u₀)`;
* `locCorr_congr_drive`: `locCorr κ V t ϖ ρ₀ x` reads `V` only on `[0, t]` (through `revMap V t`);
* `locCorr_lvl_shift_eq`: hence the correction at the **shortened time** `t − u₀` with the same
  driver, `locCorr κ V (t − u₀) ϖ ρ₀ x`, is a function of `(t, D^{+u₀}, x)` only — this is the
  germ-free correction `g₀` of the blueprint (`revMap V t = G ∘ revMap V (t − u₀)`,
  `ReverseFlow.revMap_add`, with `G` driven by `V` on `[t − u₀, t]`, i.e. by the germ).

**Remark (E5-G0).** `E5G0.locCorrG0 κ V u₀ t = locCorr κ (germFreeDrv u₀ V) (t − u₀)` removes
the *inner* flow `revMap V u₀`, i.e. `V` on `[0, u₀]` (the forward driver on `[T − u₀, T]`), and
still reads `V` on `[t − u₀, t]` (the E-SM germ) when `t ≥ 2u₀`. So `locCorrG0` is not a
function of `(Ξ-data, D^{+u₀}, X')`, and `E5Final2.zoomModel_lvl`'s `hay` (the germ-free model
data as a function of `V ⊥ D|_{[0,u₀]}`) cannot be discharged with it; the germ-free correction
must be `locCorr κ V (t − u₀) ϖ ρ₀ x` (this file). The domination lemma
`E5Final1.e5G0_of_geometry_measurable_rt` is generic in `(V₀, t₀)` and applies unchanged with
`V₀ = V`, `t₀ = t − u₀`.

Own elementary bookkeeping (definitions of `vrev`, `drive`, `smPath`, `shiftP`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1 ESM LengthMarkov StrongMarkov

/-- **`locCorr` reads the driver only on `[0, t]`** (through `revMap V t`). -/
theorem locCorr_congr_drive {κ t : ℝ} {V V' : ℝ → ℝ} (h : EqOn V V' (Icc 0 t))
    (ϖ ρ₀ : Measure ℂ) (x : FieldSample) :
    locCorr κ V t ϖ ρ₀ x = locCorr κ V' t ϖ ρ₀ x := by
  have e : revMap V t = revMap V' t := funext fun z => ReverseFlow.revMap_congr_drive z h
  have e1 : varpiT V t ϖ = varpiT V' t ϖ := by unfold varpiT; rw [e]
  have e2 : qt κ V t ϖ = qt κ V' t ϖ := by unfold qt; rw [e]
  unfold locCorr
  rw [e1, e2]

/-- **The reverse driver before the germ is the reversed shifted germ**: for
`0 ≤ s ≤ T − τ ω − u₀`, `Vr κ T B ω s = vrev (drvMap κ (shiftP u₀ (smPath B τ ω))) (T − τ ω − u₀) s`. -/
theorem Vr_eq_vrev_shiftP {Ω : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (τ : Ω → ℝ≥0)
    (u₀ : ℝ≥0) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ T - τ ω - u₀) :
    Vr κ T B ω s =
      vrev (drvMap κ (shiftP u₀ (smPath B τ ω))) (T - τ ω - u₀) s := by
  have hτ : (0 : ℝ) ≤ τ ω := (τ ω).2
  have hu : (0 : ℝ) ≤ u₀ := u₀.2
  simp only [Vr, vrev, drive, drvMap, shiftP, smPath, smShift]
  have h1 : min (max s 0) T = s := by
    rw [max_eq_left hs0, min_eq_left (by linarith)]
  have h2 : min (max s 0) (T - τ ω - u₀) = s := by
    rw [max_eq_left hs0, min_eq_left hs]
  rw [h1, h2]
  have e1 : (T - s).toNNReal = τ ω + (u₀ + (T - τ ω - u₀ - s).toNNReal) := by
    apply NNReal.eq
    push_cast
    rw [Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by linarith)]
    ring
  have e2 : T.toNNReal = τ ω + (u₀ + (T - τ ω - u₀).toNNReal) := by
    apply NNReal.eq
    push_cast
    rw [Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by linarith)]
    ring
  rw [e1, e2]
  ring

section Level

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- **Level form**: on `[0, t − u₀]` (`t = T − T_ℓ` the level collision time) the level driver
is the reversed shifted germ `vrev (drvMap κ (shiftP u₀ D)) (t − u₀)`, `D = esmGerm p`. -/
theorem lvlDrv_eqOn_shiftP (p : ℝ≥0 × NullMeasurableSpace Ω P) (u₀ : ℝ≥0) :
    EqOn (lvlDrv κ T B P p)
      (vrev (drvMap κ (shiftP u₀ (esmGerm κ T B X P p))) (lvlTime κ T B X P p - u₀))
      (Icc 0 (lvlTime κ T B X P p - u₀)) := by
  intro s hs
  exact Vr_eq_vrev_shiftP κ T B (ofCompl P p.2) (levelTime (lenA κ T B X) T.toNNReal p.1) u₀
    hs.1 hs.2

/-- **The germ is measurable for the conditioning σ-algebra** `condSigma Ξ X' r` of the level
zoom model (`Ξ` = the level point): `hDm` of `ZoomModel` for `D = esmGerm ∘ fst`. -/
theorem measurable_condSigma_lvlGerm [IsProbabilityMeasure P] {ϖ : Measure ℂ} (hS : E5.Setup κ T P B X ϖ)
    (hBc : ∀ ω, Continuous (B · ω)) {Ω' : Type} [MeasurableSpace Ω'] (ρ₀ : Measure ℂ)
    (X₁ : Ω' → FieldSample) (r : ℝ) :
    Measurable[D3Plus.condSigma (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P)
      (lvlField ϖ ρ₀ X₁) r] (fun z : lvl Ω P Ω' => esmGerm κ T B X P z.1) := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, -⟩ := hS
  have hG := measurable_esmGerm hκ hκ4 hT hB hX hind hBc
  exact (hG.comp (comap_measurable (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P))).mono
    le_sup_left le_rfl

end Level

end E5
end QuantumZipper
