import QuantumZipper.Proofs.Zipper.SWCoreA8Cont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A8 (4): from the countable event to all times and centres (pathwise)

`a8_path`: if `(f, x) ∈ a8Ev` with `x` a regular sample, then for the driver `W = Wof f`:
eventually in `k`, for all `t ∈ [0,T]`, `z ∈ [A,B] × [C,D]`, the smoothed pushed pairings
converge to `evalReg x (fc(z,2^{-k}).map f_t⁻¹)`, which is continuous in `z`; and for every
`η > 0`, eventually in `k`, it is `η`-close to the round value. Proof: the rational bounds
extend to the box by joint continuity (`a8_cont_phi`, `a8_cont_rnd`, `a8_le_of_rat`), the
uniform Cauchy property gives the limit and its continuity. Own bookkeeping (as GenUCConv).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

open CharFun RegCont

/-- **Pathwise extension.** -/
theorem a8_path (κ : ℝ) {Tq : ℚ} (hT : (0 : ℝ) ≤ Tq) {A B C D : ℚ} (hAB : (A : ℝ) ≤ B)
    (hC : (0 : ℝ) < C) (hCD : (C : ℝ) ≤ D) {f : C(Icc (0 : ℝ) Tq, ℝ)}
    (hf0 : Wof κ Tq hT f 0 = 0) {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (hE : a8Ev κ hT A B C D (f, x)) :
    (∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) Tq,
      (∀ z ∈ rectC (A : ℝ) B C D, Tendsto (fun j => ∫ u, avgReg x j u
          ∂((foldedCircle z (radius k)).map (fwdMapInv (Wof κ Tq hT f) t))) atTop
          (𝓝 (evalReg x ((foldedCircle z (radius k)).map (fwdMapInv (Wof κ Tq hT f) t))))) ∧
      ContinuousOn (fun z => evalReg x ((foldedCircle z (radius k)).map
        (fwdMapInv (Wof κ Tq hT f) t))) (rectC (A : ℝ) B C D)) ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) Tq, ∀ z ∈ rectC (A : ℝ) B C D,
      |evalReg x ((foldedCircle z (radius k)).map (fwdMapInv (Wof κ Tq hT f) t)) -
        evalReg x (foldedCircle (fwdMapInv (Wof κ Tq hT f) t z)
          (radius k * ‖deriv (fwdMapInv (Wof κ Tq hT f) t) z‖))| ≤ η := by
  set W := Wof κ Tq hT f with hWdef
  have hW : Continuous W := continuous_Wof κ Tq hT f
  set S : Set (ℝ × ℂ) := Icc (0 : ℝ) Tq ×ˢ rectC (A : ℝ) B C D with hSdef
  set Φ : ℕ → ℕ → ℝ × ℂ → ℝ := fun j k p =>
    ∫ u, avgReg x j u ∂((foldedCircle p.2 (radius k)).map (fwdMapInv W p.1)) with hΦ
  set Rn : ℕ → ℝ × ℂ → ℝ := fun k p => evalReg x (foldedCircle (fwdMapInv W p.1 p.2)
    (radius k * ‖deriv (fwdMapInv W p.1) p.2‖)) with hRn
  have hRH : rectC (A : ℝ) B C D ⊆ H := a8_rect_H hC
  have hHHbar : H ⊆ Hbar := fun w hw => le_of_lt (show 0 < w.im from hw)
  have hrad : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨Kr, hKr⟩ := eventually_atTop.1
    (hrad.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < (C : ℝ) / 2)))
  have hgj : ∀ j : ℕ, ContinuousOn (avgReg x j) Hbar := fun j =>
    ContinuousOn.congr (f := fun w => F (w, radius j))
      (hF.1.comp (continuousOn_id.prodMk continuousOn_const) fun w hw => ⟨hw, radius_pos j⟩)
      fun w hw => hF.avgReg_eq j hw
  have hΦc : ∀ j k, Kr ≤ k → ContinuousOn (Φ j k) S := fun j k hk =>
    a8_cont_phi hW hf0 (T := Tq) (A := A) (B := B) (D := D) hC (radius_pos k) (hKr k hk)
      (hgj j) (RegClosure.measurable_avgReg_slice x j)
  have hΦq : ∀ j k (q : ℚ) (hq : (q : ℝ) ∈ Icc (0 : ℝ) Tq) (z : ℂ),
      Φ j k (q, z) = a8Phi κ hT j k q hq.1 z (f, x) := fun j k q hq z =>
    (a8Phi_eq hf0 hq j k z x).symm
  have hRq : ∀ k (q : ℚ) (hq : (q : ℝ) ∈ Icc (0 : ℝ) Tq) (z : ℂ), z ∈ H →
      Rn k (q, z) = a8Rd κ hT k q hq.1 z (f, x) := fun k q hq z hz =>
    (a8Rd_eq hf0 hq k hz x).symm
  have hRc : ∀ k, ContinuousOn (Rn k) S := fun k =>
    a8_cont_rnd hW hf0 hT hC hF (radius_pos k)
  obtain ⟨K₀, hK₀⟩ := hE.1
  have hcau : ∀ k, max K₀ Kr ≤ k → ∀ m : ℕ, ∃ J, ∀ j, J ≤ j → ∀ j', J ≤ j' → ∀ p ∈ S,
      |Φ j k p - Φ j' k p| ≤ 1 / ((m : ℝ) + 1) := by
    intro k hk m
    obtain ⟨J, hJ⟩ := hK₀ k (le_of_max_le_left hk) m
    refine ⟨J, fun j hj j' hj' => a8_le_of_rat hT hAB hCD
      (((hΦc j k (le_of_max_le_right hk)).sub (hΦc j' k (le_of_max_le_right hk))).abs) ?_⟩
    intro q hq z hz
    show |Φ j k (q, zQ z) - Φ j' k (q, zQ z)| ≤ _
    rw [hΦq j k q hq, hΦq j' k q hq]
    exact hJ j hj j' hj' q hq z hz
  have hlim : ∀ k, max K₀ Kr ≤ k → ∀ p ∈ S, Tendsto (fun j => Φ j k p) atTop
      (𝓝 (evalReg x ((foldedCircle p.2 (radius k)).map (fwdMapInv W p.1)))) := by
    intro k hk p hp
    have hcs : CauchySeq fun j => Φ j k p := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨J, hJ⟩ := hcau k hk m
      exact ⟨J, fun j hj => by rw [Real.dist_eq]; exact (hJ j hj J le_rfl p hp).trans_lt hm⟩
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
    have e : evalReg x ((foldedCircle p.2 (radius k)).map (fwdMapInv W p.1)) = L :=
      hL.limUnder_eq
    rw [e]
    exact hL
  have hunif : ∀ k, max K₀ Kr ≤ k → ∀ m : ℕ, ∃ J, ∀ j, J ≤ j → ∀ p ∈ S,
      |Φ j k p - evalReg x ((foldedCircle p.2 (radius k)).map (fwdMapInv W p.1))| ≤
        1 / ((m : ℝ) + 1) := by
    intro k hk m
    obtain ⟨J, hJ⟩ := hcau k hk m
    refine ⟨J, fun j hj p hp => ?_⟩
    have ht := ((hlim k hk p hp).const_sub (Φ j k p)).abs
    exact le_of_tendsto ht (eventually_atTop.2 ⟨J, fun j' hj' => hJ j hj j' hj' p hp⟩)
  refine ⟨?_, ?_⟩
  · refine eventually_atTop.2 ⟨max K₀ Kr, fun k hk t ht =>
      ⟨fun z hz => hlim k hk (t, z) ⟨ht, hz⟩, ?_⟩⟩
    have hTU : TendstoUniformlyOn (fun j z => Φ j k (t, z))
        (fun z => evalReg x ((foldedCircle z (radius k)).map (fwdMapInv W t))) atTop
        (rectC (A : ℝ) B C D) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨J, hJ⟩ := hunif k hk m
      exact eventually_atTop.2 ⟨J, fun j hj z hz => by
        rw [Real.dist_eq, abs_sub_comm]; exact (hJ j hj (t, z) ⟨ht, hz⟩).trans_lt hm⟩
    refine hTU.continuousOn (Eventually.of_forall fun j => ?_).frequently
    exact (hΦc j k (le_of_max_le_right hk)).comp (continuousOn_const.prodMk continuousOn_id)
      fun z hz => ⟨ht, hz⟩
  · intro η hη
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
    obtain ⟨K, hK⟩ := hE.2 n
    refine eventually_atTop.2 ⟨max K (max K₀ Kr), fun k hk t ht z hz => ?_⟩
    have hk1 : K ≤ k := le_of_max_le_left hk
    have hk2 : max K₀ Kr ≤ k := le_of_max_le_right hk
    obtain ⟨J, hJ⟩ := hK k hk1
    have hext : ∀ j, J ≤ j → ∀ p ∈ S, |Φ j k p - Rn k p| ≤ 1 / ((n : ℝ) + 1) := fun j hj =>
      a8_le_of_rat hT hAB hCD (((hΦc j k (le_of_max_le_right hk2)).sub (hRc k)).abs)
        fun q hq z' hz' => by
          show |Φ j k (q, zQ z') - Rn k (q, zQ z')| ≤ _
          rw [hΦq j k q hq, hRq k q hq (zQ z') (hRH hz')]
          exact hJ j hj q hq z' hz'
    have ht2 := ((hlim k hk2 (t, z) ⟨ht, hz⟩).sub_const (Rn k (t, z))).abs
    exact (le_of_tendsto ht2 (eventually_atTop.2 ⟨J, fun j hj => hext j hj (t, z) ⟨ht, hz⟩⟩)).trans
      hn.le

end SWCore
end QuantumZipper
