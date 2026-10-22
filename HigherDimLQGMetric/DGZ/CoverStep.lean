import HigherDimLQGMetric.DGZ.CoverState

/-!
# One downward step of the DGZ bypass-cover induction

The finite greedy selection at level `i+1` extends a cover state whose lowest processed level
is `i+2`.  Its new centres are separated, and the certificates and higher nice boxes give their
full-field control.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.DGZ

open Set HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- One downward induction step, with the certified deterministic consequence of `𝒞` supplied
in the exact form of `aroundGood_of_niceCEvent`. -/
def coverState_step (p : NiceParams) (H : ℕ → Rd d → ℝ) (hc : ∀ q, Continuous (H q))
    (m i : ℕ) (him : i + 2 ≤ m) (st : CoverState p H m (i + 2))
    (hmono : Monotone p.a) (ham : p.a m ≤ p.n)
    (hR : 1 ≤ p.R) (hξ : 0 < p.ξ)
    (hgap : 40 * (p.R : ℝ) * p.s (i + 1) ≤ p.s (i + 2))
    {lam : ℝ} (hlam : 0 ≤ lam) (hK : 2 ≤ p.K) (ha : p.a = dgzSeq lam p.K)
    {g : ℕ} (hg3 : 3 ≤ g) (hg : (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4)
    (hKmargin : 6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2))
    (hJ2 : EventJ2' p H m)
    (hAround : ∀ j, 2 ≤ j → j ≤ m → ∀ u w : Zd d,
      latPt (p.s (j - 1)) w ∈ obox (0 : Rd d) 2 → NiceCEvent p H j u w →
        AroundGood p.ξ (fun v => H p.n v - H (p.n - p.a j) v)
          (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1))
          (2 * p.R * p.s (j - 1)) (obox (0 : Rd d) 2) (p.tStar j) ∧
        Real.exp ((p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a j : ℝ)) * p.tStar j <
          acrossDist p.ξ (fun v => H p.n v - H (p.n - p.a j) v)
            (latPt (p.s j) u) (4 * p.s j) (2 * p.s j)) :
    CoverState p H m (i + 1) := by
  classical
  let Uhi := coverU (p.R : ℝ) m p.s st.X
  have hjn : p.a (i + 2) ≤ p.n := (hmono him).trans ham
  have hnice (u : Zd d)
      (hbig : obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) ⊆ obox (0 : Rd d) 2)
      (hout : ¬ obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) ⊆ Uhi) :
      NiceBox p H (i + 2) u := st.niceOutside (i + 2) le_rfl him u hbig hout
  let hSExists := exists_coverEntries_level p H hmono hjn hR hgap Uhi hnice
  let S := Classical.choose hSExists
  obtain ⟨hSsep, hScov, hSout⟩ := Classical.choose_spec hSExists
  let Z : Finset (Rd d) := S.image (fun e => latPt (p.s (i + 1)) e.z)
  let X' : ℕ → Set (Rd d) := coverInsert st.X (i + 1) (Z : Set (Rd d))
  have hold : st.X (i + 1) = ∅ := st.emptyBelow (i + 1) (by omega)
  have hUmono : Uhi ⊆ coverU (p.R : ℝ) m p.s X' :=
    coverU_subset_coverInsert st.X hold (Z : Set (Rd d))
  have hctrlEntry (e : CoverEntry p H i) (he : e ∈ S) :
      ∃ x ∈ cbox (latPt (p.s (i + 1)) e.z) (p.s (i + 2)), ∃ t : ℝ,
        AroundGood p.ξ (H p.n) (latPt (p.s (i + 1)) e.z)
          (4 * p.R * p.s (i + 1)) (2 * p.R * p.s (i + 1))
          (obox (0 : Rd d) 2) t ∧
        t < coverWeight p (i + 1) *
          acrossDist p.ξ (H p.n) x (4 * p.s (i + 2)) (2 * p.s (i + 2)) := by
    have hHigher : ∀ l : ℕ, i + 2 < l → l ≤ m → ∃ u : Zd d,
        obox (latPt (p.s (i + 2)) e.u) (p.s (i + 2)) ⊆
          obox (latPt (p.s l) u) (p.s l) ∧ NiceBox p H l u := by
      intro l hil hlm
      obtain ⟨u, hsub, hbig⟩ :=
        exists_niceParent_chain p hmono hil.le ((hmono hlm).trans ham) e.u e.big
      have hout : ¬ obox (latPt (p.s l) u) (p.s l) ⊆ Uhi := by
        intro h
        exact hSout e he (e.parent.trans (hsub.trans h))
      exact ⟨u, hsub, st.niceOutside l hil.le hlm u hbig hout⟩
    have hOsc := coverEntry_osc_of_higherNice p H hlam (by omega : 1 ≤ p.K)
      ha hg3 hg him e hJ2 hHigher
    have hz2 : latPt (p.s (i + 1)) e.z ∈ obox (0 : Rd d) 2 := e.big e.zmem
    have hFine := hAround (i + 2) (by omega) him e.u e.z
      (by simpa only [show i + 2 - 1 = i + 1 by omega] using hz2) e.cert
    have h := coverEntry_ctrl_of_osc p H hc hξ e hgap (hmono (by omega))
      hKmargin hFine hOsc
    simpa only [coverWeight] using h
  refine ⟨X', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hne : j ≠ i + 1 := by omega
    simp only [X', coverInsert_ne st.X hne (Z : Set (Rd d))]
    exact st.emptyBelow j (by omega)
  · intro j hj
    have hne : j ≠ i + 1 := by omega
    simp only [X', coverInsert_ne st.X hne (Z : Set (Rd d))]
    exact st.emptyAbove j hj
  · intro j
    by_cases hj : j = i + 1
    · subst j
      simp only [X', coverInsert_at]
      exact Z.finite_toSet
    · simp only [X', coverInsert_ne st.X hj (Z : Set (Rd d))]
      exact st.finite j
  · intro j z hz
    by_cases hj : j = i + 1
    · subst j
      simp only [X', coverInsert_at] at hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      exact e.big e.zmem
    · simp only [X', coverInsert_ne st.X hj (Z : Set (Rd d))] at hz
      exact st.sub j hz
  · intro j z hz
    by_cases hj : j = i + 1
    · subst j
      simp only [X', coverInsert_at] at hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨e.z, rfl⟩
    · simp only [X', coverInsert_ne st.X hj (Z : Set (Rd d))] at hz
      exact st.lattice j z hz
  · intro j z hz z' hz' hne
    by_cases hj : j = i + 1
    · subst j
      simp only [X', coverInsert_at] at hz hz'
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hz'
      have hee' : e ≠ e' := by
        intro heq
        exact hne (by rw [heq])
      exact hSsep e he e' he' hee'
    · simp only [X', coverInsert_ne st.X hj (Z : Set (Rd d))] at hz hz'
      exact st.sep j z hz z' hz' hne
  · intro j hj1 hjm z hz
    by_cases hj : j = i + 1
    · subst j
      simp only [X', coverInsert_at] at hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      exact hctrlEntry e he
    · simp only [X', coverInsert_ne st.X hj (Z : Set (Rd d))] at hz
      exact st.ctrl j hj1 hjm z hz
  · intro l hlo hlm u hbig hnot
    by_cases hl : l = i + 1
    · subst l
      by_contra hbad
      have hnotOld : ¬ obox (latPt (p.s (i + 1)) u) (p.s (i + 1)) ⊆ Uhi := by
        intro h
        exact hnot (h.trans hUmono)
      obtain ⟨e, he, hcov⟩ := hScov u hbad hbig hnotOld
      apply hnot
      intro v hv
      apply mem_coverU_iff.mpr
      refine ⟨i + 1, by omega, by omega, latPt (p.s (i + 1)) e.z, ?_, hcov hv⟩
      simp only [X', coverInsert_at]
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    · have hli : i + 2 ≤ l := by omega
      apply st.niceOutside l hli hlm u hbig
      intro h
      exact hnot (h.trans hUmono)

end HigherDimLQGMetric.DGZ
