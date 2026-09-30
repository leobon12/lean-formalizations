import QuantumZipper.Proofs.Thm18.G1PathCoord
import QuantumZipper.Proofs.RS.TipA
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-HOLDER: the Hölder part of the good predicate, almost-sure reduction

Target: `G1GoodBMStmt SideHolderGood` (G1PathCoord.lean), i.e. almost surely, for `κ = γ² < 4`,
both complementary components of the whole SLE_κ chord are Hölder domains in the form
`LocHolderHbar` (one exponent, constants on bounded parts of `Hbar`).

This file proves **`g1GoodBMStmt_sideHolder_of_det`**: `G1GoodBMStmt SideHolderGood` follows
from the deterministic localization statement `SideHolderDetStmt` ("if `f̂_n = fwdMapInv W n`
is `α`-Hölder on bounded parts of `ℍ` for every integer `n`, with one exponent `α`, then the
side maps of the chord are `α`-Hölder on bounded parts of `Hbar`"). The probabilistic input is

* Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), **Thm 5.2** (p. 21) and its
  proof (p. 22), at every integer time, with the exponent `RS.rsHolderExp κ` that depends only
  on `κ` (`ae_fwdMapInv_holder_nat`, from the repo's RH2 `RS.ae_rsGrid_bound`,
  `RS.norm_deriv_revMap_le_of_grid`, `RS.hardyLittlewood_holder`, transported from the reverse
  to the forward map by the time-reversal identity `RS.fwdMapInv_drive_eq_revMap_revBM`, exactly
  as in `RS.ae_fwdMapInv_holder`, which hides the exponent);
* Rohde–Schramm Thms 4.7, 6.1 (`RS.rohdeSchrammSimple`): the trace is a simple chord and the
  hulls are its initial arcs.

`SideHolderDetStmt` is proved from the localization argument of `handoff/G1-HOLDER.md`
(own argument; no written proof of the whole-chord statement was found) in G1HolderDet.lean /
G1HolderMain.lean.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

/-- `f̂_n = fwdMapInv W n` is `α`-Hölder on bounded parts of `ℍ` at every integer time `n`. -/
def FwdHolderAll (W : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ n : ℕ, ∀ ρ : ℝ, ∃ C : ℝ, ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
    ‖fwdMapInv W n z - fwdMapInv W n w‖ ≤ C * ‖z - w‖ ^ α

/-- **Deterministic localization statement.** For a continuous driver `W` (`W 0 = 0`) whose
hulls are the initial arcs of a simple chord `η`, if every `f̂_n` is `α`-Hölder on bounded parts
of `ℍ` (one `α ∈ (0,1]`), then for both sides and every normalized uniformizer `φ` the inverse
`φ⁻¹` has a continuous extension to `Hbar` that is `LocHolderHbar`. -/
def SideHolderDetStmt : Prop :=
  ∀ (W : ℝ → ℝ) (η : ℝ → ℂ), Continuous W → W 0 = 0 → IsSimpleChord η →
    (∀ t : ℝ, 0 ≤ t → fwdHull W t = η '' Ioc 0 t) → ∀ α : ℝ, 0 < α → α ≤ 1 →
    FwdHolderAll W α → ∀ left : Bool, ∀ φ : ℂ → ℂ,
      IsNormalizedUniformizer (sideDom η left) φ →
        ∃ ψe : ℂ → ℂ, ContinuousOn ψe Hbar ∧ EqOn (invFunOn φ (sideDom η left)) ψe H ∧
          LocHolderHbar ψe

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- RS Thm 5.2 for the reverse map with the explicit exponent `rsHolderExp κ` (the proof of
`RS.ae_revMap_holder_of_ne_four`, whose statement hides the exponent). -/
theorem ae_revMap_holder_rsExp (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ ρ : ℝ, ∃ C, ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖revMap (drive κ B ω) T z - revMap (drive κ B ω) T w‖ ≤
        C * ‖z - w‖ ^ RS.rsHolderExp κ := by
  obtain ⟨hα0, hα1, -⟩ := RS.rsHolderExp_spec hκ hκ4.ne
  filter_upwards [RS.ae_rsGrid_bound hB hκ hκ4.ne (by linarith) hT, hB.cont] with ω hgrid hcont
  intro ρ
  have hW : Continuous (drive κ B ω) := drive_continuous hcont
  set R := max ρ 0
  obtain ⟨M, hM⟩ := exists_nat_ge (R + 3)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hgrid M)
  have hbd := RS.norm_deriv_revMap_le_of_grid hW hT hα1 hM hN
  obtain ⟨C', -, hC'⟩ := RS.hardyLittlewood_holder (differentiableOn_revMap _ hW hT)
    (le_max_of_le_left (by positivity)) hα0 hα1 hbd
  refine ⟨C', fun z hz w hw hzρ hwρ => hC' z hz w hw ?_ ?_⟩
  · exact hzρ.trans (le_max_left _ _)
  · exact hwρ.trans (le_max_left _ _)

/-- **RS Thm 5.2 at all integer times, common exponent.** For `0 < κ < 4`, almost surely every
`f̂_n = fwdMapInv (drive κ B ω) n` is `rsHolderExp κ`-Hölder on bounded parts of `ℍ`. -/
theorem ae_fwdMapInv_holder_nat (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∀ᵐ ω ∂P, FwdHolderAll (drive κ B ω) (RS.rsHolderExp κ) := by
  obtain ⟨B', -, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB'pre : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ ρ : ℝ, ∃ C, ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖fwdMapInv (drive κ B ω) n z - fwdMapInv (drive κ B ω) n w‖ ≤
        C * ‖z - w‖ ^ RS.rsHolderExp κ := by
    intro n
    have hT : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h := ae_revMap_holder_rsExp
      (UnzipInvariance.isBrownianReal_revBM hB'pre hB'c (n : ℝ).toNNReal) hκ hκ4 hT
    filter_upwards [h, hB'eq, hB.eval_zero_ae_eq_zero] with ω hω heq h0 ρ
    obtain ⟨C, hC⟩ := hω ρ
    have h0' : B' 0 ω = 0 := by rw [heq 0, h0]
    have hdr : drive κ B ω = drive κ B' ω := by funext t; simp [drive, heq]
    refine ⟨C, fun z hz w hw hzρ hwρ => ?_⟩
    rw [hdr, RS.fwdMapInv_drive_eq_revMap_revBM κ B' hT (hB'c ω) h0' hz,
      RS.fwdMapInv_drive_eq_revMap_revBM κ B' hT (hB'c ω) h0' hw]
    exact hC z hz w hw hzρ hwρ
  filter_upwards [ae_all_iff.2 hn] with ω hω n
  exact hω n

/-- **`G1GoodBMStmt SideHolderGood` from the deterministic localization statement.** -/
theorem g1GoodBMStmt_sideHolder_of_det (hD : SideHolderDetStmt) :
    G1GoodBMStmt SideHolderGood := by
  intro γ hγ hγ2 Ω _ P _ B hB hc
  have hκ : 0 < γ ^ 2 := by positivity
  have hκ4 : γ ^ 2 < 4 := by nlinarith
  obtain ⟨hα0, hα1, -⟩ := RS.rsHolderExp_spec hκ hκ4.ne
  filter_upwards [RS.rohdeSchrammSimple (γ ^ 2) hκ hκ4.le P B hB,
    ae_fwdMapInv_holder_nat hB hκ hκ4, hB.eval_zero_ae_eq_zero] with ω hω hH h0
  intro left φ hφ
  exact hD (drive (γ ^ 2) B ω) (sleTrace (γ ^ 2) B ω) (drive_continuous (hc ω))
    (by simp [drive, h0]) hω.1 hω.2 _ hα0 hα1 hH left φ hφ

end G1RC
end Thm18Asm
end QuantumZipper
