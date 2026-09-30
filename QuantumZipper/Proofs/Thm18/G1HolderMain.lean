import QuantumZipper.Proofs.Thm18.G1HolderDet
import QuantumZipper.Proofs.Thm18.G1HolderHarm
import QuantumZipper.Proofs.Thm18.G1HolderLoew

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-HOLDER: the side components of SLE_κ, κ < 4, are Hölder domains

**`g1GoodBMStmt_sideHolderGood : G1GoodBMStmt SideHolderGood`**, proved.

Assembly (handoff/G1-HOLDER.md): `sideHolderDetStmt_holds` proves the deterministic
localization statement `SideHolderDetStmt` (G1HolderRed.lean) from

* the continuous extension `ψe` of `φ⁻¹` (`psiExtContStmt_holds`, Pommerenke 1992, Thm 2.6);
* the Loewner factorization `ψe = f̂_n ∘ F`, `F = f_n ∘ ψe`, at an integer time `n` beyond the
  part of the chord seen by `ψe([−ρ, ρ])` (`exists_fwd_factor`, G1HolderLoew.lean);
* the boundary Lipschitz bound `Im F(z) ≤ K Im z` (`im_le_mul_im_of_tendsto_zero`,
  G1HolderHarm.lean, maximum modulus with an explicit harmonic majorant);
* Cauchy + Koebe + Hardy–Littlewood (`locHolderHbar_of_factor`, G1HolderDet.lean);

and `g1GoodBMStmt_sideHolder_of_det` (G1HolderRed.lean) adds Rohde–Schramm, *Basic properties of
SLE*, Ann. Math. 161 (2005), Thm 5.2 at all integer times (common exponent `rsHolderExp κ`) and
Thms 4.7/6.1 (simple chord, hulls = initial arcs). The localization of the fixed-time statement
to the whole chord is an own argument: no written proof was found (Sheffield, arXiv:1012.4797,
p. 16–17, and Duplantier–Miller–Sheffield, arXiv:1409.7055, p. 65, state only fixed `t`;
Kavvadias–Miller–Schoug, arXiv:2209.10532, §1, attribute the whole-chord form to RS Thm 5.2).
-/

noncomputable section

open Filter Set Function Metric

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

/-- **The deterministic localization statement holds.** -/
theorem sideHolderDetStmt_holds : SideHolderDetStmt := by
  intro W η hW hW0 hη hK α hα hα1 hH left φ hφ
  obtain ⟨ψe, -, hc, -, heq⟩ := psiExtContStmt_holds η hη left φ hφ
  refine ⟨ψe, hc, heq, locHolderHbar_of_factor hc hα hα1 fun R => ?_⟩
  set ρ := 4 * max R 0 + 4 with hρ
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨n, hmaps, hinj, hdiff, hinv, ⟨M, hM⟩, htend⟩ :=
    exists_fwd_factor hW hW0 hη hK hφ hc heq ρ
  have hFd' : DifferentiableOn ℂ (fun z => fwdMap W n (ψe z)) (H ∩ ball (0 : ℂ) ρ) :=
    hdiff.mono inter_subset_left
  have hFM : ∀ z ∈ H ∩ ball (0 : ℂ) ρ, (fwdMap W n (ψe z)).im ≤ M := fun z hz =>
    (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans
      (hM z hz.1 (mem_ball_zero_iff.1 hz.2)))
  obtain ⟨K, hKb⟩ := im_le_mul_im_of_tendsto_zero hρ0 hFd' hFM htend
  refine ⟨fwdMapInv W n, fun z => fwdMap W n (ψe z),
    RS.differentiableOn_fwdMapInv hW hW0 (Nat.cast_nonneg n), hH n, hdiff, hinj, hmaps,
    fun z hz => (hinv z hz).symm, ⟨M, fun z hz hzR => hM z hz ?_⟩,
    ⟨K, fun z hz hzR => hKb z hz ?_⟩⟩
  · have : R ≤ max R 0 := le_max_left _ _
    linarith
  · have : R ≤ max R 0 := le_max_left _ _
    rw [hρ]
    linarith

/-- **G1-HOLDER: the side components of the SLE_κ chord, κ = γ² < 4, are a.s. Hölder
domains** (Rohde–Schramm 2005, Thm 5.2, localized to the whole chord). -/
theorem g1GoodBMStmt_sideHolderGood : G1GoodBMStmt SideHolderGood :=
  g1GoodBMStmt_sideHolder_of_det sideHolderDetStmt_holds

end G1RC
end Thm18Asm
end QuantumZipper
