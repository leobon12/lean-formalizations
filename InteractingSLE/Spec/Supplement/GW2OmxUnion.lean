/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmIdent

/-!
# GW2's open lines: the launch image of the stage union (deterministic core)

Packet PROVE-GW2-STAGEMEAN, R120 round. Under the conditional law of the earlier pieces, the kernel union mean is
stated for the conditional counterflow's inverted hull together with the current piece's own hull; the instance's
union is the original retained set together with the explored hull. Pathwise, through the launch chart `cL` (whose
inverse is the inverse Loewner map of the earlier pieces' joined driver `J` at the launch time `T`):

* **`launchImage_union_eq`**: if `cL⁻¹` carries the conditional counterflow's inverted hull `Ak` onto the original
  retained set `Aret`, the explored driver `J'` agrees with `J` up to `T`, and after `T` it is the current piece's
  driver `P` shifted (on `[0, t]`), then `cL((Aret ∪ K_{J'}(T + t)) ∩ dom cL) = Ak ∪ K_P(t)`
  (`GW2Olm.image_chart_union_hull`, `GW2Olm.image_fwdMap_of_inv_image`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

/-- **The launch image of the stage union.** -/
theorem launchImage_union_eq {cL : Chart} (hc : cL.IsConformal) {J J' : ℝ → ℝ} (hJ : Continuous J)
    (hJ0 : J 0 = 0) (hJ' : Continuous J') (hJ'0 : J' 0 = 0) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t)
    (hinv : ∀ w ∈ H, cL.2.1 w = fwdMapInv J T w) (heq : EqOn J J' (Icc 0 T)) {Ak Aret : Set ℂ} (hAk : Ak ⊆ H)
    (himg : cL.2.1 '' Ak = Aret) {Pd : ℝ → ℝ} (hP : Continuous Pd)
    (hPeq : EqOn (fun r => J' (T + r) - J' T) Pd (Icc 0 t)) :
    cL.1 '' ((Aret ∪ fwdHull J' (T + t)) ∩ (cL.dom : Set ℂ)) = Ak ∪ fwdHull Pd t := by
  rw [GW2Olm.image_chart_union_hull hc hJ hJ0 hJ' hJ'0 hT ht hinv heq Aret,
    GW2Olm.image_fwdMap_of_inv_image hJ hJ0 hT hinv hAk himg]
  congr 1
  have hs : Continuous fun r => J' (T + r) - J' T := (hJ'.comp (continuous_const.add continuous_id)).sub
    continuous_const
  exact QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn hs hP ht hPeq

end InteractingSLE.Theorem14.GW2Omx
