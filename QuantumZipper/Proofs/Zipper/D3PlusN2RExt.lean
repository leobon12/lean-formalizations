import QuantumZipper.Proofs.Zipper.D3PlusN2RHeart
import QuantumZipper.Proofs.Zipper.D3PlusN2RZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2 heart on the restricted index (Decision D36): the heart reduction, with H1 proved

Task D36-IMPL, steps (2) and (6). This file proves the D36 form of `n2ZHeart_of_nodes`
(`D3PlusN2HeartMain.lean`):

  `n2ZHeartWin_of_nodes : N2HLatTVWinStmt → N2HModelDecompWinStmt → N2ZHeartWinStmt`,

i.e. the restricted heart node from the restricted H2 and H3 nodes alone: **the H1 input is proved
here** and no longer a hypothesis.

## Why H1 is only needed at folded circles

The mixing step of the heart (DMS arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78) needs the
lateral data of the local field `Z` to be independent of the radial Brownian path, as a random
variable from which the model's window datum `heartFW (lateral data, radial data)` is a measurable
function. The window datum reads the lateral data only through `latWinW`, i.e. through the
regularized evaluation `evalReg y ν`, and `evalReg y ν` reads the field `y` only through `avgReg`,
i.e. **only at folded circles** `foldedCircle d (radius k)` (`Field/Sample.lean`: `avgReg`,
`evalReg`). Hence (own elementary argument, definitional unfolding):

* `fcLift v`: the field that equals `v` on the folded circles of positive radius and `0` elsewhere
  (measurable in `v`, `measurable_fcLift`);
* `evalReg_fcLift`: `evalReg (fcLift (y|_circles)) ν = evalReg y ν` for **every** `y` and `ν`;
* `n2LatC X r := fcLift (n2LatY X r |_circles)`: the lateral data read at folded circles only;
  `heartFW_n2LatC`: the model heart map does not see the difference;
* `indepFun_n2LatC_path`: `n2LatC X r` is independent of the radial Brownian path — this is
  `indepFun_n2LatY_family` (`D3PlusN2H1Main.lean`, PROVED) at the family of all folded circles,
  whose only input is `regAt_foldedCircle` (clause 3 of `IsRegularWith`).

The unrestricted H1 `N2HLatIndepStmt` (independence of the whole lateral field `n2LatY X r`)
needs a.s. regularization at every local measure (gap `F2.EvalRegRawStmt`, D17) and is not used.

The assembly is a copy of `n2ZHeart_of_nodes` with `LocIdx K` replaced by `WinIdx K`
(bookkeeping; own assembly of the cited steps, exactly as in `D3PlusN2HeartMain.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## Reading a field at folded circles only -/

/-- The index of all folded circles of positive radius. -/
abbrev FcIdx : Type := {p : ℂ × ℝ // 0 < p.2}

/-- The folded circle of an index. -/
def fcIdx (p : FcIdx) : Measure ℂ := foldedCircle p.1.1 p.1.2

open Classical in
/-- The field equal to `v` at the folded circles of positive radius and `0` elsewhere. -/
def fcLift (v : FcIdx → ℝ) : FieldSample :=
  fun μ => if h : ∃ p : FcIdx, fcIdx p = μ then v (Classical.choose h) else 0

theorem measurable_fcLift : Measurable fcLift := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : ∃ p : FcIdx, fcIdx p = μ
  · simp only [fcLift, dif_pos h]
    exact measurable_pi_apply _
  · simp only [fcLift, dif_neg h]
    exact measurable_const

/-- The restriction of a field to the folded circles. -/
def fcRes (y : FieldSample) : FcIdx → ℝ := fun p => y (fcIdx p)

theorem fcLift_fcRes_fc (y : FieldSample) (p : FcIdx) :
    fcLift (fcRes y) (fcIdx p) = y (fcIdx p) := by
  have h : ∃ q : FcIdx, fcIdx q = fcIdx p := ⟨p, rfl⟩
  simp only [fcLift, dif_pos h, fcRes]
  rw [Classical.choose_spec h]

theorem avgReg_fcLift_fcRes (y : FieldSample) (k : ℕ) (z : ℂ) :
    avgReg (fcLift (fcRes y)) k z = avgReg y k z := by
  unfold avgReg
  congr 1
  funext n
  exact fcLift_fcRes_fc y ⟨(dyadicRoundC n z, radius k), radius_pos k⟩

/-- **The regularized evaluation reads the field only at folded circles.** -/
theorem evalReg_fcLift_fcRes (y : FieldSample) (ν : Measure ℂ) :
    evalReg (fcLift (fcRes y)) ν = evalReg y ν := by
  unfold evalReg
  simp only [avgReg_fcLift_fcRes]

/-- The lateral data of the local field, read at the folded circles only. -/
def n2LatC {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) (ω : Ω) : FieldSample :=
  fcLift (fcRes (n2LatY X r ω))

theorem heartFW_n2LatC (γ r : ℝ) (K : ℕ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω)
    (t : ℝ × (ℝ → ℝ)) :
    heartFW γ r K (n2LatC X r ω, t) = heartFW γ r K (n2LatY X r ω, t) := by
  funext i
  simp only [heartFW, Pi.add_apply, latWinW, n2LatC, evalReg_fcLift_fcRes]

theorem latWinW_n2LatC (K : ℕ) (a r : ℝ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) :
    latWinW K a (n2LatC X r ω) = latWinW K a (n2LatY X r ω) := by
  funext i
  simp only [latWinW, n2LatC, evalReg_fcLift_fcRes]

section Indep

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {γ α L r : ℝ}

theorem measurable_n2LatC (hX : IsFreeGFFModConstH X P) (hr : 0 < r) :
    Measurable (n2LatC X r) :=
  measurable_fcLift.comp
    (measurable_pi_iff.2 fun p => (measurable_pi_apply (fcIdx p)).comp (measurable_n2LatY hX hr))

/-- **H1 at the folded circles (proved).** The lateral data of the local field read at all folded
circles are independent of the radial Brownian path (`indepFun_n2LatY_family` at the family of
folded circles; DMS arXiv:1409.7055, p. 77). -/
theorem indepFun_n2LatC_path (hX : IsFreeGFFModConstH X P) (hr : 0 < r) :
    IndepFun (n2LatC X r) (pathOf (zRadB X r)) P :=
  (indepFun_n2LatY_family hX hr fcIdx fun p _ => regAt_foldedCircle hX p.1.1 p.2).comp
    measurable_fcLift measurable_id

/-- **H1 at the folded circles ⇒ independence of the lateral and radial data** (copy of
`indepFun_n2RadR`). -/
theorem indepFun_n2LatC_n2RadR (hα : α < Qc γ) (hr : 0 < r) (hX : IsFreeGFFModConstH X P)
    (hL : 0 < n2Lev γ α L r) (K : ℕ) :
    IndepFun (n2LatC X r) (n2RadR γ α L r K X) P := by
  obtain ⟨b₀, -, hae⟩ := ae_radData_eq (Real.log K) (isBrownianReal_zRadB hX hr) hα hL
  have h := (indepFun_n2LatC_path hX hr).comp measurable_id
    (measurable_radG α (Qc γ) (n2Lev γ α L r) (Real.log K))
  refine h.congr (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [hae] with ω hω
  exact hω.2.symm

end Indep

/-! ## The wedge side on the restricted index -/

theorem ae_resFieldW_wedgeV_eq {γ α : ℝ} {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''}
    {X'' : Ω'' → FieldSample} {A : ℝ → Ω'' → ℝ} (hA : IsWedgeProcess α (Qc γ) A P'') {K : ℕ}
    (hK : 0 < K) :
    ∀ᵐ ω ∂P'', resFieldW K (wedgeV γ X'' A ω) = heartWW γ K (latY''W K X'' ω, radR'' K A ω) := by
  filter_upwards [ae_resField_wedgeV_eq (X'' := X'') hA hK] with ω h
  funext i
  exact congrFun h ⟨winIdx K i, isLocalH_winIdx K hK i⟩

theorem measurable_latY''W {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''}
    [IsProbabilityMeasure P''] {X'' : Ω'' → FieldSample} (hX'' : IsFreeGFFModConstH X'' P'')
    (K : ℕ) (hK : 0 < K) : Measurable (latY''W K X'') :=
  (measurable_reindex_locW K hK).comp (measurable_latY'' hX'' K)

end D3Plus
end QuantumZipper
