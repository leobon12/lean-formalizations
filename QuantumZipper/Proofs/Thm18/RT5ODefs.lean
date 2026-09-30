import QuantumZipper.Proofs.Thm18.R18RTDefs
import QuantumZipper.Proofs.Thm18.R18RTMaskOff
import QuantumZipper.Proofs.Thm18.R18RTCoreDet
import QuantumZipper.Proofs.Thm18.D74Basic
import QuantumZipper.Proofs.Zipper.LocLenBridge
import QuantumZipper.Proofs.Thm18.G4WedgeCert
import QuantumZipper.Proofs.LQG.WedgeBoundaryReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D86: the zip-up welds the pieces by their own (open-arc) boundary lengths

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26
(`literature/1012.4797.txt` lines 1005–1040): `Z^LEN_t`, `t > 0`, is the inverse of `Z^LEN_{−t}`,
"a.s. uniquely defined (via conformal welding)" of the pair of pieces `((D₁,h_{D₁}),(D₂,h_{D₂}))`:
the boundary arc of `D₁` next to `0` is glued to the boundary arc of `D₂` by quantum length. The
lengths are those of each piece, "well defined by unzipping", i.e. read on the open boundary arcs
of the pieces (Berestycki–Powell arXiv:2404.16642, Def 6.41 p. 229, on an open segment; D73/D75).

`zipLenUpA` (Statements/Thm18Paper.lean) reads the weld point and the welding homeomorphism from
the GLOBAL boundary limit `qBoundaryMeasure`, whose approximations `bdryApprox` read semicircles
centred at real points near `0` that cross the curve of the configuration. For the pieces of D82
(`zipLenDownMA`, fields read off the curve) those values are junk, and the round trip
`Z_ℓ ∘ Z_{−ℓ}^{pieces}` needed the unsourced node `Rt5BdryStmt`. Decision D86 (pre-approved paper
alignment): the zip-up reads the lengths on open arcs `(s,0)` and `(0,r)` (`openArcLen`), exactly
as the D73/D75 unzipping lengths do. New definitions, next to the old ones:
`lenWeldPointO`, `weldHomRO`, `IsLenWeldingDriverO`, `lenWeldDriverO`, `zipLenUpOA`. Combined with
D87 (the zip-up acts on the pieces read off the curve), `Z_ℓ = zipLenUpOA γ ℓ ∘ offConfig γ`.

Proved here (deterministic):
* **bridge** `zipLenUpOA_eq_of_bReg`: when the global boundary limit exists and has no atoms
  (`WedgeBdry.BReg`, a.s. the case for the wedge and for the unzipped wedge), the open-arc
  zip-up IS the old one (`LocLen.arcLen_eq_of_isVagueLimitR`);
* **congruence** `lenWeldDriverO_congr_off`: two fields that agree off a closed set meeting `ℝ`
  at most in `0` have the same open-arc welding driver (`qBoundaryMeasureOn_congr_off`); in
  particular a configuration and its pieces read off the curve (`lenWeldDriverO_offConfig_eq`).
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-! ## Definitions (D86) -/

/-- The left welding point for quantum length `ℓ`, lengths read on the open arcs `(s,0)` of the
left piece: `sup {s ≤ 0 : ℓ ≤ ν(s,0)}` (open-arc copy of `lenWeldPoint`). -/
def lenWeldPointO (γ : ℝ) (x : FieldSample) (ℓ : ℝ) : ℝ :=
  sSup {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ openArcLen γ x s 0}

/-- The welding homeomorphism `R_h` by open-arc lengths: the smallest `r ≥ 0` with
`ν(s,0) ≤ ν(0,r)` (open-arc copy of `weldHomR`). -/
def weldHomRO (γ : ℝ) (x : FieldSample) (s : ℝ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ openArcLen γ x s 0 ≤ openArcLen γ x 0 r}

/-- Length-welding driver with open-arc lengths (copy of `IsLenWeldingDriver`). -/
def IsLenWeldingDriverO (γ : ℝ) (x : FieldSample) (ℓ : ℝ) (p : ℝ × (ℝ → ℝ)) : Prop :=
  0 ≤ p.1 ∧ Continuous p.2 ∧ p.2 0 = 0 ∧ (p.1 = 0 ∨ IsSimpleCurveHull (revHull p.2 p.1)) ∧
    zeroMinus p.2 p.1 = lenWeldPointO γ x ℓ ∧
    ∀ s ∈ Icc (zeroMinus p.2 p.1) 0, weldingHom p.2 p.1 s = weldHomRO γ x s

/-- The open-arc length-welding driver, chosen by `Classical.epsilon`. -/
def lenWeldDriverO (γ : ℝ) (x : FieldSample) (ℓ : ℝ) : ℝ × (ℝ → ℝ) :=
  Classical.epsilon (IsLenWeldingDriverO γ x ℓ)

/-- `Z^LEN_ℓ`, `ℓ ≥ 0`, D86 form: weld the pieces by their open-arc lengths, then rescale by
(1.8) with the transported area. -/
def zipLenUpOA (γ ℓ : ℝ) (c : AreaConfig) : AreaConfig :=
  canonAConfig γ (zipWeldUpA γ (lenWeldDriverO γ c.fld ℓ).1 (lenWeldDriverO γ c.fld ℓ).2 c)

/-! ## Bridge: open arcs = global limit when the latter exists without atoms -/

/-- Open-arc lengths are the global closed-arc masses, for a field with a global boundary limit
without atoms. -/
theorem openArcLen_eq_of_limit {γ : ℝ} {x : FieldSample}
    (hx : IsVagueLimitR (bdryApprox γ x) (qBoundaryMeasure γ x))
    (hat : ∀ t : ℝ, qBoundaryMeasure γ x {t} = 0) (a b : ℝ) :
    openArcLen γ x a b = qBoundaryMeasure γ x (Icc a b) := by
  rcases lt_or_ge a b with hab | hab
  · rw [openArcLen_eq]
    exact LocLen.arcLen_eq_of_isVagueLimitR hx (hat a) (hat b)
  · have h1 : Ioo a b = ∅ := Ioo_eq_empty (not_lt.2 hab)
    rw [openArcLen, h1, measure_empty]
    rcases hab.lt_or_eq with h | h
    · rw [Icc_eq_empty (not_le.2 h), measure_empty]
    · rw [h, Icc_self, hat]

theorem openArcLen_eq_of_bReg {γ : ℝ} {x : FieldSample} (h : WedgeBdry.BReg γ x) (a b : ℝ) :
    openArcLen γ x a b = qBoundaryMeasure γ x (Icc a b) :=
  openArcLen_eq_of_limit (Thm18Asm.isVagueLimitR_qBoundaryMeasure_of_isLQGGood h.1) h.noAtom a b

section Bridge

variable {γ : ℝ} {x : FieldSample}

theorem lenWeldPointO_eq_of (h : ∀ a b, openArcLen γ x a b = qBoundaryMeasure γ x (Icc a b))
    (ℓ : ℝ) : lenWeldPointO γ x ℓ = lenWeldPoint γ x ℓ := by
  simp only [lenWeldPointO, lenWeldPoint, h]

theorem weldHomRO_eq_of (h : ∀ a b, openArcLen γ x a b = qBoundaryMeasure γ x (Icc a b)) :
    weldHomRO γ x = weldHomR γ x := by
  funext s
  simp only [weldHomRO, weldHomR, h]

theorem isLenWeldingDriverO_eq_of
    (h : ∀ a b, openArcLen γ x a b = qBoundaryMeasure γ x (Icc a b)) (ℓ : ℝ) :
    IsLenWeldingDriverO γ x ℓ = IsLenWeldingDriver γ x ℓ := by
  funext p
  simp only [IsLenWeldingDriverO, IsLenWeldingDriver, lenWeldPointO_eq_of h, weldHomRO_eq_of h]

theorem lenWeldDriverO_eq_of (h : ∀ a b, openArcLen γ x a b = qBoundaryMeasure γ x (Icc a b))
    (ℓ : ℝ) : lenWeldDriverO γ x ℓ = lenWeldDriver γ x ℓ := by
  unfold lenWeldDriverO lenWeldDriver
  rw [isLenWeldingDriverO_eq_of h]

end Bridge

/-! ## Congruence: the open-arc welding driver only reads the field off the curve -/

theorem openArcLen_congr_off {K : Set ℂ} (hK : IsClosed K) {x y : FieldSample}
    (h : RegEqOff K x y) (γ : ℝ) (hR : ∀ t : ℝ, t ≠ 0 → (t : ℂ) ∉ K) {a b : ℝ}
    (hab : b ≤ 0 ∨ 0 ≤ a) : openArcLen γ x a b = openArcLen γ y a b := by
  unfold openArcLen
  rw [qBoundaryMeasureOn_congr_off hK h γ (fun t ht => hR t ?_)]
  rcases hab with hb | ha
  · exact (lt_of_lt_of_le ht.2 hb).ne
  · exact (lt_of_le_of_lt ha ht.1).ne'

/-- **Congruence (D86)**: fields that agree off a closed set meeting `ℝ` at most in `0` have the
same open-arc welding driver. -/
theorem lenWeldDriverO_congr_off {K : Set ℂ} (hK : IsClosed K) {x y : FieldSample}
    (h : RegEqOff K x y) (γ : ℝ) (hR : ∀ t : ℝ, t ≠ 0 → (t : ℂ) ∉ K) (ℓ : ℝ) :
    lenWeldDriverO γ x ℓ = lenWeldDriverO γ y ℓ := by
  have hL : lenWeldPointO γ x ℓ = lenWeldPointO γ y ℓ := by
    unfold lenWeldPointO
    congr 1
    ext s
    exact and_congr_right fun _ => by
      rw [openArcLen_congr_off hK h γ hR (Or.inl le_rfl)]
  have hW : weldHomRO γ x = weldHomRO γ y := by
    funext s
    unfold weldHomRO
    congr 1
    ext r
    exact and_congr_right fun _ => by
      rw [openArcLen_congr_off hK h γ hR (Or.inl le_rfl),
        openArcLen_congr_off hK h γ hR (Or.inr le_rfl)]
  unfold lenWeldDriverO
  congr 1
  funext p
  simp only [IsLenWeldingDriverO, hL, hW]

/-! ## The pieces read off the curve (D82 `offConfig`, D87) -/

/-- The field read off the curve agrees with the field off the curve. -/
theorem regEqOff_offConfig (γ : ℝ) {c : AreaConfig} (hc : Continuous c.drv) (h0 : c.drv 0 = 0) :
    RegEqOff (curveOf c.drv) (offConfig γ c).fld c.fld :=
  fun _ _ hoff => (avgReg_readOffField_eq_of_circleOff (x := c.toPair) hc h0 hoff).symm

/-- **Boundary identity for the pieces (D86)**: a configuration and its pieces read off the curve
have the same open-arc welding driver, when the curve meets `ℝ` at most in `0`. -/
theorem lenWeldDriverO_offConfig_eq (γ : ℝ) {c : AreaConfig} (hc : Continuous c.drv)
    (h0 : c.drv 0 = 0) (hR : ∀ t : ℝ, t ≠ 0 → (t : ℂ) ∉ curveOf c.drv) (ℓ : ℝ) :
    lenWeldDriverO γ (offConfig γ c).fld ℓ = lenWeldDriverO γ c.fld ℓ :=
  lenWeldDriverO_congr_off (Thm18Asm.D74.isClosed_curveOf _) (regEqOff_offConfig γ hc h0) γ hR ℓ

/-- The driver read off the data of a rescaled configuration is its driver. -/
theorem offConfig_drv_canon (γ : ℝ) (c : AreaConfig) :
    (offConfig γ (canonAConfig γ c)).drv = (canonAConfig γ c).drv := by
  funext s
  simp [offConfig, configOfData, drvOfData, offData, canonAConfig, AreaConfig.toPair]
  rfl

end R18
end QuantumZipper
