import QuantumZipper.Proofs.Thm18.RT6MOTrans4
import QuantumZipper.Proofs.Thm18.RT5FarGeo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6b: FarPull at the wedge (`ZipFarWedgeStmt`) from the goodness of the zipped driver

RT5's geometric lemma `rt5far_geo` (Carathéodory extension of the reverse map, Loewner
concatenation, compactness) applies to any configuration `c` whose driver is the unzipping of a
good driver `W` re-zipped by `(T, W')`. At `c₀` take `W` = the driver of `Z^LEN_ℓ c₀` itself: the
zipped driver is `rt5V T W' c₀.drv` rescaled (definition of `zipLenUpA`), and unzipping it by the
welding time recovers `c₀.drv` (`rt5V_shift`). The only input is that the zipped driver is a good
chordal driver and the zip scale is positive (`ZipGoodStmt`: Sheffield Thm 1.8, the zipped
curve is again an SLE curve; by clause (3) its driver has the law of the SLE driver).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **The zipped driver is a good chordal driver, and the zip scale is positive** (open). -/
def ZipGoodStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ ℓ : ℝ, 0 ≤ ℓ → ∀ᵐ ω ∂P,
      0 < areaScale (zipWeldUpA γ (lenWeldDriver γ (wedgeAConfig γ B Y ω).fld ℓ).1
        (lenWeldDriver γ (wedgeAConfig γ B Y ω).fld ℓ).2 (wedgeAConfig γ B Y ω)).area ∧
      RS.RadialGood (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv ∧
      InjOn (trace (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv) (Ici 0) ∧
      (∀ t > (0 : ℝ), trace (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv t ∈ H) ∧
      ∀ t : ℝ, 0 ≤ t → fwdHull (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv t =
        trace (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv '' Ioc 0 t

theorem rt6b_rt5V_congr {T : ℝ} {W' D D' : ℝ → ℝ} (h : ∀ r : ℝ, 0 ≤ r → D r = D' r) :
    rt5V T W' D = rt5V T W' D' := by
  funext x
  unfold rt5V
  split_ifs with hx
  · rfl
  · rw [h _ (by linarith [not_le.1 hx])]

/-- FarPull at a configuration from the goodness of its zipped driver (deterministic). -/
theorem rt6b_farPull_of_good {γ ℓ : ℝ} {c : AreaConfig} (hc0 : c.drv 0 = 0)
    (hp : IsLenWeldingDriver γ c.fld ℓ (lenWeldDriver γ c.fld ℓ))
    (hpos : 0 < areaScale (zipWeldUpA γ (lenWeldDriver γ c.fld ℓ).1
      (lenWeldDriver γ c.fld ℓ).2 c).area)
    (hRG : RS.RadialGood (zipLenUpA γ ℓ c).drv)
    (hinj : InjOn (trace (zipLenUpA γ ℓ c).drv) (Ici 0))
    (hH : ∀ t > (0 : ℝ), trace (zipLenUpA γ ℓ c).drv t ∈ H)
    (hhull : ∀ t : ℝ, 0 ≤ t → fwdHull (zipLenUpA γ ℓ c).drv t =
      trace (zipLenUpA γ ℓ c).drv '' Ioc 0 t) :
    Rt5FarPull γ ℓ c := by
  refine ⟨hpos, fun d k hoff => ?_⟩
  set p := lenWeldDriver γ c.fld ℓ with hpdef
  set a := areaScale (zipWeldUpA γ p.1 p.2 c).area with hadef
  set Wz := (zipLenUpA γ ℓ c).drv with hWz
  have hT : 0 ≤ p.1 := hp.1
  have hW'0 : p.2 0 = 0 := hp.2.2.1
  have eWz : ∀ u : ℝ, Wz u = rt5V p.1 p.2 c.drv (a ^ 2 * max u 0) / a := fun u => rfl
  set s := p.1 / a ^ 2 with hs
  set D := outDrv Wz s a⁻¹ with hD
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have hDc : ∀ r : ℝ, 0 ≤ r → D r = c.drv r := by
    intro r hr
    have e1 : s + max (a⁻¹ ^ 2 * max r 0) 0 = (p.1 + r) / a ^ 2 := by
      rw [max_eq_left hr, max_eq_left (by positivity), hs]; field_simp
    simp only [hD, outDrv]
    rw [e1, eWz, eWz, max_eq_left (by positivity), max_eq_left (by positivity),
      show a ^ 2 * ((p.1 + r) / a ^ 2) = p.1 + r by field_simp,
      show a ^ 2 * (p.1 / a ^ 2) = p.1 by field_simp]
    have h := rt5V_shift (D := c.drv) hW'0 hT hc0 (show r ∈ Ici (0 : ℝ) from hr)
    simp only [RS.shiftDrive] at h
    rw [← h]
    field_simp
  have hV : ∀ u : ℝ, 0 ≤ u → rt5V p.1 p.2 D (a ^ 2 * max u 0) / a = Wz u := fun u _ => by
    rw [eWz, rt6b_rt5V_congr hDc]
  have hcurveZ : curveOf (fun u => rt5V p.1 p.2 D (a ^ 2 * max u 0) / a) = curveOf Wz :=
    curveOf_congr hV
  have hK : p.1 = 0 ∨ IsSimpleCurveHull (revHull p.2 p.1) := hp.2.2.2.1
  obtain ⟨δ, hδ, hae⟩ := rt5far_geo (W := Wz) (W' := p.2) (T := p.1) (s := s) (b := a⁻¹)
    hRG hinj hH hhull (by positivity) (inv_pos.2 hpos) hT hp.2.1 hW'0 hK hpos hV d k
    (by rw [hcurveZ]; exact hoff)
  have hcur : curveOf D = curveOf c.drv := curveOf_congr hDc
  refine ⟨δ, hδ, ?_⟩
  rw [hcur] at hae
  exact hae

/-- **FarPull at the wedge**, from the goodness of the zipped driver. -/
theorem zipFarWedgeStmt_of_good (hX1 : BaseFin.BaseFiniteStmt) (hZG : ZipGoodStmt) :
    ZipFarWedgeStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  have hex : ∀ᵐ ω ∂P, ∃ p, IsLenWeldingDriver γ (Y ω) ℓ p := by
    rcases hℓ.lt_or_eq with h | h
    · have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
      have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
      exact (g4WeldAStmt_holds hX1 γ P B Y hS hIn hE6 hEq ℓ h).mono fun ω hw => hw.1
    · subst h
      exact ae_of_all _ fun ω => ⟨_, isLenWeldingDriver_zero_zero γ _⟩
  filter_upwards [hex, hZG γ P B Y hS hIn ℓ hℓ, D74.ae_wedgeConfig_snd_good hS] with ω hx hg hω
  obtain ⟨hpos, hRG, hinj, hH, hhull⟩ := hg
  exact rt6b_farPull_of_good hω.2 (lenWeldDriver_spec hx) hpos hRG hinj hH hhull

end R18
end QuantumZipper
