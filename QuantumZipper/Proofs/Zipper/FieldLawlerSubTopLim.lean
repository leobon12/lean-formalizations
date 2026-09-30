import QuantumZipper.Proofs.Thm18.LWFarSideMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-IMAGETOP (partial): end limits of a path approaching a boundary point

Task FL-IMAGETOP (helper of FL-THM, D75). Abstract cluster-set lemma used for the end points of
the crosscuts `Z_t ηⱼ` in Field–Lawler, EJP 20 (2015), proof of Prop. 3.4 (p. 9).

`fl_tendsto_real_of_subseq`: let `g` be continuous on `(0,1)`, and suppose every sequence
`sₙ ↓ 0` has a subsequence along which `g` converges to a real `a` with `F a = x₀`, where `F`
is not constant on any open real interval. Then `g(s)` converges, as `s ↓ 0`, to a real `a` with
`F a = x₀`.

Own elementary argument (the standard proof that the cluster set of a curve is connected,
Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2, specialised to a real cluster set): two
distinct real cluster values `a < a'` would give, by the intermediate value theorem for `Re g`,
every `c ∈ (a, a')` as a cluster value, so `F ≡ x₀` on `(a, a')`.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

variable {g : ℝ → ℂ} {F : ℂ → ℂ} {x₀ : ℂ}

/-- Subsequential limit property of `g` at `0+`. -/
def FLSubLim (g : ℝ → ℂ) (F : ℂ → ℂ) (x₀ : ℂ) : Prop :=
  ∀ ns : ℕ → ℝ, Tendsto ns atTop (𝓝[>] 0) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a : ℝ, F a = x₀ ∧
    Tendsto (fun n => g (ns (φ n))) atTop (𝓝 (a : ℂ))

lemma fl_clusters_lt (hg : ContinuousOn g (Ioo 0 1))
    (hnc : ∀ a b : ℝ, a < b → ∀ c : ℂ, ¬ ∀ s ∈ Ioo a b, F s = c) (hsub : FLSubLim g F x₀)
    {s s' : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[>] 0)) (hs' : Tendsto s' atTop (𝓝[>] 0)) {a a' : ℝ}
    (ha : Tendsto (fun n => g (s n)) atTop (𝓝 (a : ℂ)))
    (ha' : Tendsto (fun n => g (s' n)) atTop (𝓝 (a' : ℂ))) : ¬ a < a' := by
  intro haa
  refine hnc a a' haa x₀ fun c hc => ?_
  have hre : Tendsto (fun n => (g (s n)).re) atTop (𝓝 a) := by
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp ha
  have hre' : Tendsto (fun n => (g (s' n)).re) atTop (𝓝 a') := by
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp ha'
  have hr : ∀ n : ℕ, ∃ r : ℝ, r ∈ Ioo 0 (min (1 / ((n : ℝ) + 1)) 1) ∧ (g r).re = c := by
    intro n
    have hδ : 0 < min (1 / ((n : ℝ) + 1)) 1 := lt_min (by positivity) one_pos
    obtain ⟨m, hm1, hm2⟩ := ((hs.eventually (Ioo_mem_nhdsGT hδ)).and
      (hre.eventually (gt_mem_nhds hc.1))).exists
    obtain ⟨m', hm1', hm2'⟩ := ((hs'.eventually (Ioo_mem_nhdsGT hδ)).and
      (hre'.eventually (lt_mem_nhds hc.2))).exists
    have hsub1 : uIcc (s m) (s' m') ⊆ Ioo 0 (min (1 / ((n : ℝ) + 1)) 1) := by
      intro r hr'
      rcases le_total (s m) (s' m') with h | h
      · rw [uIcc_of_le h] at hr'
        exact ⟨hm1.1.trans_le hr'.1, hr'.2.trans_lt hm1'.2⟩
      · rw [uIcc_of_ge h] at hr'
        exact ⟨hm1'.1.trans_le hr'.1, hr'.2.trans_lt hm1.2⟩
    have hsub2 : Ioo 0 (min (1 / ((n : ℝ) + 1)) 1) ⊆ Ioo (0 : ℝ) 1 := fun r hr' =>
      ⟨hr'.1, hr'.2.trans_le (min_le_right _ _)⟩
    have hcont : ContinuousOn (fun r => (g r).re) (uIcc (s m) (s' m')) :=
      Complex.continuous_re.comp_continuousOn (hg.mono (hsub1.trans hsub2))
    obtain ⟨r, hr1, hr2⟩ := intermediate_value_uIcc hcont
      (show c ∈ uIcc (g (s m)).re (g (s' m')).re from
        (uIcc_of_le (hm2.trans hm2').le).symm ▸ ⟨hm2.le, hm2'.le⟩)
    exact ⟨r, hsub1 hr1, hr2⟩
  choose r hr using hr
  have hrt : Tendsto r atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (hr n).1.1⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hr n).1.1.le) fun n => ?_
    exact ((hr n).1.2.trans_le (min_le_left _ _)).le
  obtain ⟨φ, -, b, hb, hlim⟩ := hsub r hrt
  have hlre : Tendsto (fun n => (g (r (φ n))).re) atTop (𝓝 b) := by
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp hlim
  have hcb : c = b := by
    have : Tendsto (fun n => (g (r (φ n))).re) atTop (𝓝 c) := by
      simp only [(hr _).2]; exact tendsto_const_nhds
    exact tendsto_nhds_unique this hlre
  rw [hcb]; exact hb

/-- **End limit.** Under the subsequence property and non-constancy of `F`, `g` converges at
`0+` to a real point `a` with `F a = x₀`. -/
theorem fl_tendsto_real_of_subseq (hg : ContinuousOn g (Ioo 0 1))
    (hnc : ∀ a b : ℝ, a < b → ∀ c : ℂ, ¬ ∀ s ∈ Ioo a b, F s = c) (hsub : FLSubLim g F x₀) :
    ∃ a : ℝ, F a = x₀ ∧ Tendsto g (𝓝[>] 0) (𝓝 (a : ℂ)) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by show (0 : ℝ) < _; positivity⟩
  obtain ⟨φ₀, hφ₀, a₀, ha₀, hlim₀⟩ := hsub _ h0
  refine ⟨a₀, ha₀, tendsto_of_subseq_tendsto fun ns hns => ?_⟩
  obtain ⟨φ, hφ, a, -, hlim⟩ := hsub ns hns
  have e1 := fl_clusters_lt hg hnc hsub (hns.comp hφ.tendsto_atTop) (h0.comp hφ₀.tendsto_atTop)
    hlim hlim₀
  have e2 := fl_clusters_lt hg hnc hsub (h0.comp hφ₀.tendsto_atTop) (hns.comp hφ.tendsto_atTop)
    hlim₀ hlim
  have : a = a₀ := le_antisymm (not_lt.1 e2) (not_lt.1 e1)
  exact ⟨φ, this ▸ hlim⟩

end FieldLawler
end QuantumZipper
