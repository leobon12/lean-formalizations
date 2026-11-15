/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmKer2

/-!
# GW2's open lines: the union read in the launch chart

Packet PROVE-GW2-STAGEMEAN, R119 round. In the chart of the earlier pieces (the Loewner map of the joined driver at
the launch time `T`), the union `retained ∪ (explored hull at T + t)` becomes the image of the retained set together
with the current piece's own hull at time `t`:

* **`image_fwdMap_union_hull`**: for a continuous driver `W` from `0` and any set `A`,
  `f_T((A ∪ K_{T+t}) ∩ (ℍ ∖ K_T)) = f_T(A ∩ (ℍ ∖ K_T)) ∪ K^{(T)}_t`, `K^{(T)}` the hull of the shifted driver
  (`QuantumZipper.fwdHull_add_diff`: the hull increment is the preimage of the shifted hull; `f_T` maps `ℍ ∖ K_T` onto
  `ℍ`);
* **`image_chart_union_hull`**: the same through any conformal chart whose inverse is the inverse Loewner map of `J`
  at `T` (the launch chart, `Swc.succChart_inv_eq`), for a driver `J'` agreeing with `J` on `[0, T]` (the joined driver
  of the earlier pieces and the current one);
* **`image_fwdMap_of_inv_image`**: if the chart's inverse carries `Aₖ ⊆ ℍ` onto `A'` (the retained set:
  `GW2Shr.invHull_eq_launch`), the forward Loewner map carries `A' ∩ (ℍ ∖ K_T)` back onto `Aₖ`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Olm

/-- **The union through the launch chart**: the image of `(A ∪ K_{T+t}) ∩ (ℍ ∖ K_T)` under `f_T` is the image of
`A ∩ (ℍ ∖ K_T)` together with the shifted driver's hull at `t`. -/
theorem image_fwdMap_union_hull {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T t : ℝ} (hT : 0 ≤ T)
    (ht : 0 ≤ t) (A : Set ℂ) :
    fwdMap W T '' ((A ∪ fwdHull W (T + t)) ∩ (H \ fwdHull W T)) =
      fwdMap W T '' (A ∩ (H \ fwdHull W T)) ∪ fwdHull (fun r => W (T + r) - W T) t := by
  have hsplit : (A ∪ fwdHull W (T + t)) ∩ (H \ fwdHull W T) =
      (A ∩ (H \ fwdHull W T)) ∪ (fwdHull W (T + t) \ fwdHull W T) := by
    ext z
    simp only [mem_inter_iff, mem_union, mem_sdiff]
    constructor
    · rintro ⟨hA | hK, hH, hT'⟩
      · exact Or.inl ⟨hA, hH, hT'⟩
      · exact Or.inr ⟨hK, hT'⟩
    · rintro (⟨hA, hH, hT'⟩ | ⟨hK, hT'⟩)
      · exact ⟨Or.inl hA, hH, hT'⟩
      · exact ⟨Or.inr hK, hK.1, hT'⟩
  rw [hsplit, image_union, QuantumZipper.fwdHull_add_diff hW hT ht]
  congr 1
  ext w
  constructor
  · rintro ⟨z, ⟨-, hz⟩, rfl⟩
    exact hz
  · intro hw
    have hwH : w ∈ H := hw.1
    refine ⟨fwdMapInv W T w, ⟨QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT hwH, ?_⟩, ?_⟩
    · rw [QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hT hwH]
      exact hw
    · exact QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hT hwH

/-- **The union through a chart whose inverse is an inverse Loewner map.** -/
theorem image_chart_union_hull {cL : Chart} (hc : cL.IsConformal) {J J' : ℝ → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0)
    (hJ' : Continuous J') (hJ'0 : J' 0 = 0) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t)
    (hinv : ∀ w ∈ H, cL.2.1 w = fwdMapInv J T w) (heq : Set.EqOn J J' (Icc 0 T)) (A : Set ℂ) :
    cL.1 '' ((A ∪ fwdHull J' (T + t)) ∩ (cL.dom : Set ℂ)) =
      fwdMap J T '' (A ∩ (H \ fwdHull J T)) ∪ fwdHull (fun r => J' (T + r) - J' T) t := by
  have hdom : (cL.dom : Set ℂ) = H \ fwdHull J T := by
    rw [hc.coe_dom, ← QuantumZipper.RS.image_fwdMapInv_H hJ hJ0 hT]
    exact image_congr hinv
  have hfwd : ∀ z ∈ (cL.dom : Set ℂ), cL.1 z = fwdMap J T z := by
    intro z hz
    rw [hc.coe_dom] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hc.2.2 w hw, hinv w hw, QuantumZipper.RS.fwdMap_fwdMapInv hJ hJ0 hT hw]
  have hK : fwdHull J T = fwdHull J' T := QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn hJ hJ' hT heq
  have hM : fwdMap J T = fwdMap J' T := QuantumZipper.CharFunRhs.fwdMap_eq_of_eqOn fun r hr => heq hr
  have e1 : cL.1 '' ((A ∪ fwdHull J' (T + t)) ∩ (cL.dom : Set ℂ)) =
      fwdMap J' T '' ((A ∪ fwdHull J' (T + t)) ∩ (H \ fwdHull J' T)) := by
    rw [← hK, ← hM, ← hdom]
    exact image_congr fun z hz => hfwd z hz.2
  rw [e1, image_fwdMap_union_hull hJ' hJ'0 hT ht A, hK, hM]

/-- **The retained set through the launch chart, forward form.** -/
theorem image_fwdMap_of_inv_image {cL : Chart} {J : ℝ → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) (hinv : ∀ w ∈ H, cL.2.1 w = fwdMapInv J T w) {Ak A' : Set ℂ} (hAk : Ak ⊆ H)
    (himg : cL.2.1 '' Ak = A') : fwdMap J T '' (A' ∩ (H \ fwdHull J T)) = Ak := by
  have hA' : A' = fwdMapInv J T '' Ak := by
    rw [← himg]
    exact image_congr fun w hw => hinv w (hAk hw)
  have hsub : A' ⊆ H \ fwdHull J T := by
    rw [hA']
    rintro _ ⟨w, hw, rfl⟩
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hJ hJ0 hT (hAk hw)
  rw [inter_eq_left.2 hsub, hA', image_image]
  conv_rhs => rw [← image_id Ak]
  exact image_congr fun w hw => QuantumZipper.RS.fwdMap_fwdMapInv hJ hJ0 hT (hAk hw)

end InteractingSLE.Theorem14.GW2Olm
