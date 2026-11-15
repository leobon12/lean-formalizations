/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop411Q
import InteractingSLE.WangWu.ReverseContactBdryGlue
import InteractingSLE.Foundations.Loewner.TraceClose

/-!
# Lemma 4.7 in the chart `Q`: the first contact from the mapped picture

Packet PROVE-SEC5-Q. Specification §4.2, proof of Lemma 4.7 (`source/spec/p097-144.md#lem-4.7-proof`, pp. 117–118):
"conformally mapping `𝒮 ∖ η([0, τ])` back to `𝒮` with `η(τ)` sent to `0` … leaves us in the setting of the lemma
with `τ = 0`. Thus we just need to argue that `η′` first hits `∂_L𝒮` at `0`."

This is the deterministic last step of that argument in the chart `Q`. The flow line `η` is a simple proper Loewner
trace of `W`; its prefix `η((0, q])` is mapped out by the centred map `f_q = fwdMap W q`, which sends the tip `η(q)`
to `0`. If the counterflow `η′ = R ∘ β` stays in `ℍ ∖ η((0, q])` on `(0, u)` and its image `f_q ∘ η′` tends to `0`
as the time increases to `u` (the mapped counterflow first reaches the lower boundary at the image of the tip), then
`η′(u) = η(q)` (continuity of `F_q = f_q⁻¹` at `0`: `tendsto_fwdMapInv_tip_of_isLoewnerTraceLT`), so the
first-contact property `Prop411Q.IsFirstHitQ η β q` holds.

* **`isFirstHitQ_of_tendsto_fwdMap`**.

The probabilistic part of Lemma 4.7 (the conditional law of the counterflow given the flow-line prefix, Propositions
3.7–3.8 and Theorem 2.4, and Lemma 4.5 for the counterflow at `κ′ = 16/κ`) is not proved here; see the handoff of
PROVE-SEC5-Q.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec5.Lemma47Q

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop411Q

/-- **The first contact of Lemma 4.7 from the mapped picture.** Let `η` be a simple proper Loewner trace of a
continuous driver `W` with `W 0 = 0`, and `q > 0`. If the counterflow `η′ = R ∘ β` (`β` continuous from the left at
`u > 0`) stays in `ℍ ∖ K_q` on `(0, u)`, and `f_q(η′(v)) → 0` as `v ↑ u`, then `η′` first hits `η((0, q])` at `η(q)`,
at the time `u`. -/
theorem isFirstHitQ_of_tendsto_fwdMap {W : ℝ → ℝ} {η β : ℝ → ℂ} {q u : ℝ} (hη : IsLoewnerTrace W η)
    (hP : IsProperArc η) (hW : Continuous W) (hW0 : W 0 = 0) (hq : 0 < q) (hu : 0 < u)
    (hβ : ContinuousWithinAt β (Ioo 0 u) u) (hav : ∀ v ∈ Ioo 0 u, negInv (β v) ∈ H \ fwdHull W q)
    (hlim : Tendsto (fun v => fwdMap W q (negInv (β v))) (𝓝[Ioo 0 u] u) (𝓝 0)) :
    IsFirstHitQ η β q := by
  have hne : (𝓝[Ioo 0 u] u).NeBot := right_nhdsWithin_Ioo_neBot hu
  have hmapH : Tendsto (fun v => fwdMap W q (negInv (β v))) (𝓝[Ioo 0 u] u) (𝓝[H] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, eventually_nhdsWithin_of_forall fun v hv =>
      QuantumZipper.FwdHolo.mapsTo_fwdMap hW hq.le (hav v hv)⟩
  have htip : Tendsto (fwdMapInv W q) (𝓝[H] 0) (𝓝 (η q)) :=
    TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT (isLoewnerTraceLT_of_isLoewnerTrace hη q) hW hW0 hq
      (hη.2.1.mono Icc_subset_Ici_self)
  have h3 : Tendsto (fun v => negInv (β v)) (𝓝[Ioo 0 u] u) (𝓝 (η q)) := by
    refine (htip.comp hmapH).congr' (eventually_nhdsWithin_of_forall fun v hv => ?_)
    exact QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hq.le (hav v hv)
  have hqH : η q ∈ H := hP.mem_H q hq
  have hq0 : η q ≠ 0 := ne_zero_of_mem_H hqH
  have h4 : Tendsto β (𝓝[Ioo 0 u] u) (𝓝 (negInv (η q))) := by
    have := ((continuousAt_negInv hq0).tendsto).comp h3
    refine this.congr fun v => ?_
    simp
  have hβu : β u = negInv (η q) := tendsto_nhds_unique hβ.tendsto h4
  have hK : fwdHull W q = η '' Ioc 0 q := fwdHull_eq_image_Ioc hη hP hq.le
  refine ⟨u, hu, by rw [hβu, negInv_negInv], fun v hv hm => ?_⟩
  rw [← hK] at hm
  exact (hav v hv).2 hm

end InteractingSLE.Sec5.Lemma47Q
