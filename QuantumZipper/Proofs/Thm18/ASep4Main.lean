import QuantumZipper.Proofs.Thm18.ASep4Cut
import QuantumZipper.Proofs.Thm18.ASep3Prof
import QuantumZipper.Proofs.Thm18.ASep2Wedge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 10): `G4SepScale0Stmt` — the free-field conclusion uniformly in the scale

`g4SepScale0Stmt_holds`: for a free field `X` and a good driver `W`, almost surely, for every
scale `s > 0` and every profile `g` continuous off `0`,
`G4SepConcl0 γ (rescale (ofFun g + X ω) Q s, W)`.

Assembly (per sample, all deterministic once the almost-sure inputs hold):
* profile continuous off `0` → continuous profile: `concl0_rescale_cutoff` (ASep4Cut);
* continuous profile commutes with the rescaling: `g4SepConcl0_rescale_ofFun_add_iff` (ASep3Prof);
* conjuncts 1 and 2 for `ofFun h + rescale X Q s`: `conj1_add_gen`, `conj2_add_gen` (ASep4All)
  with the scale-uniform inputs: the scale joint witness `ae_isRegularWith_rescale_all` (ASep4Wit),
  the scale engine run `ae_scale_run_all` (ASep4All/ASep4Run), the pushed-circle convergence
  `ae_tendsto_PsiK_rescale_all` (ASep3PsiRun), regularity of the free field;
* `concl0_of_good` (ASep4Cut).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (through the engine files);
Sheffield arXiv:1012.4797 §1.6 (the conclusion is used for the canonical wedge representative).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core RegCont TwoPoint CoordReg GenUC

/-- **`G4SepScale0Stmt` holds.** -/
theorem g4SepScale0Stmt_holds : G4SepScale0Stmt := by
  intro γ _ _ Ω _ P _ X hX W hWg
  have hrun := ae_all_iff.2 fun i : ℕ => ae_scale_run_all hX γ hWg
    (d := foldH (CoordsFull.fullIndex i).1) (foldH_mem_Hbar' _)
    (r := (CoordsFull.fullIndex i).2) (UnzipFull.fullIndex_radius_pos i)
  filter_upwards [hrun, ae_isRegularWith_rescale_all hX hWg (Qc γ),
    ae_tendsto_PsiK_rescale_all hX hWg (Qc γ), RegSample.ae_isRegularSample hX]
    with ω hrunω hwitω hψω hregω s hs g hg
  obtain ⟨F, hF⟩ := hregω
  have hFs := hF.rescale' (Qc γ) hs
  refine concl0_rescale_cutoff γ hWg (X ω) hs (fun g' hg' => ?_) hg
  rw [g4SepConcl0_rescale_ofFun_add_iff hF hg' hs W]
  have hgs : Continuous fun z : ℂ => g' ((s : ℂ) * z) :=
    hg'.comp (continuous_const.mul continuous_id)
  refine concl0_of_good γ hWg (fun i p hp => ?_) (fun i p hp => ?_)
  · have hτ : 0 ≤ p 0 := (show 0 < p 0 from hp.1).le
    obtain ⟨Z, hZ⟩ := hwitω s hs (p 0) hτ
    exact conj1_add_gen γ hWg (foldH_mem_Hbar' _) (UnzipFull.fullIndex_radius_pos i) hFs hp hZ
      (hrunω i s hs p hp).1 (fun c hc k => hψω s hs c hc k (p 0) hτ) hgs
  · have hτ : 0 ≤ p 0 := (show 0 < p 0 from hp.1).le
    obtain ⟨Z, hZ⟩ := hwitω s hs (p 0) hτ
    exact conj2_add_gen γ hWg (foldH_mem_Hbar' _) (UnzipFull.fullIndex_radius_pos i) hFs hp hZ
      (hrunω i s hs p hp).2 (fun c hc k => hψω s hs c hc k (p 0) hτ) hgs

end ASep
end QuantumZipper
