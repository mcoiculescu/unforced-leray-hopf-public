import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5

/-!
# `PartII-b:T13/1/7/2` decomposition: transfer of the weak identities to the window

Source: `the November 2 reference manuscript` lines 1928-1933.  The assembly
`wbdTransfer_of` is proved from two leaves: local integrability of periodic `L^r(cylMeas)`
functions (`MollLoc`, from `Sub/PartII-b_T13_1_5_5.lean`) and the integrability of a component of
`b ∈ H_r` against continuous compactly supported tests in `s > 0` (`WbdIntH`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- **Integrability of `b ∈ H_r` against tests in `s > 0`** (SP 1928-1933): the density of
`hMeas c r` with respect to Lebesgue measure on `s > 0` is `s^{r/2-5/2}/c` times the indicator of
the cell in `q`; it is bounded above and below on compacts of `s > 0`; Hölder with `r > 1` and
`q`-periodicity (finitely many cells cover the support). -/
def WbdIntH : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ b : CProf, InHr c r b → ∀ i : Fin 2, ∀ ψ : Coord → ℝ,
    Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi (0 : ℝ) ×ˢ univ →
    Integrable (fun x => b x i * (ψ x : ℂ)) volume

theorem wb_cpd_zero (j : Fin 3) (ψ : Coord → ℝ) (x : Coord) (h : x ∉ tsupport ψ) :
    cpd j ψ x = 0 := by
  simp [cpd, fderiv_of_notMem_tsupport ℝ h]

theorem wb_cpd_prop (j : Fin 3) (ψ : Coord → ℝ) (hψ : IsSTTestCoord ψ) :
    Continuous (cpd j ψ) ∧ HasCompactSupport (cpd j ψ) ∧ tsupport (cpd j ψ) ⊆ tsupport ψ := by
  refine ⟨?_, hψ.compact.fderiv_apply ℝ (cdir j), tsupport_fderiv_apply_subset ℝ (cdir j)⟩
  exact (hψ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const

theorem wb_ct_S (φ : Coord → ℝ) (x : Coord) :
    coordTranspose vS dZero φ x = -cpd 0 (fun y => y.1 * φ y) x := by
  simp [coordTranspose, Fin.sum_univ_three, vS, dZero, cpd]

theorem wb_ct_Q (φ : Coord → ℝ) (x : Coord) :
    coordTranspose vQ0 dZero φ x = -cpd 1 φ x := by
  simp [coordTranspose, Fin.sum_univ_three, vQ0, dZero, cpd]

theorem wb_ct_E (φ : Coord → ℝ) (x : Coord) :
    coordTranspose vEta dZero φ x = -cpd 2 φ x := by
  simp [coordTranspose, Fin.sum_univ_three, vEta, dZero, cpd]

theorem wb_int_loc (f : Coord → ℂ) (hf : LocallyIntegrable f volume) (ψ : Coord → ℝ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x => f x * (ψ x : ℂ)) volume :=
  hf.integrable_smul_right_of_hasCompactSupport (g := fun x => (ψ x : ℂ))
    (Complex.continuous_ofReal.comp hc) (hs.comp_left Complex.ofReal_zero)

theorem wb_replace (M : ℝ) (hM : WinCutBd M) (a : ℝ) (ha : 0 < a) (b : CProf) (i : Fin 2)
    (j : Fin 3) (ψ : Coord → ℝ) (hsub : tsupport ψ ⊆ winOpen a) (x : Coord) :
    windowProfile a b x i * (cpd j ψ x : ℂ) = b x i * (cpd j ψ x : ℂ) := by
  by_cases hx : x ∈ tsupport ψ
  · have hx' := hsub hx
    have h1 := (hM a ha).2.1 x.1 ⟨hx'.1.1.le, hx'.1.2.le⟩
    simp [windowProfile, h1]
  · simp [wb_cpd_zero j ψ x hx]

theorem wb_core (M : ℝ) (hM : WinCutBd M) (a : ℝ) (ha : 0 < a) (b : CProf) (i : Fin 2)
    (j : Fin 3) (ψ : Coord → ℝ) (hsub : tsupport ψ ⊆ winOpen a) (D : Coord → ℂ)
    (T : Coord → ℝ) (hT : ∀ x, T x = -cpd j ψ x)
    (hE : ∫ x, windowProfile a b x i * (cpd j ψ x : ℂ) = -∫ x, D x * (ψ x : ℂ)) :
    ∫ x, D x * (ψ x : ℂ) = ∫ x, b x i * (T x : ℂ) := by
  have h1 : ∫ x, b x i * (T x : ℂ) = -∫ x, b x i * (cpd j ψ x : ℂ) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hT x]
  rw [h1, ← integral_congr_ae (Filter.Eventually.of_forall (wb_replace M hM a ha b i j ψ hsub)), hE]
  ring

theorem wbdTransfer_of (hL : MollLoc) (hH : WbdIntH) : WbdTransfer := by
  intro M hM c r hc hr μ G b hG hb a ha i Dt D1 hDt hD1 hT hQ
  have hlocDt : LocallyIntegrable Dt volume := hL c r hc hr Dt hDt.1 hDt.2.1 hDt.2.2
  have hlocD1 : ∀ j, LocallyIntegrable (D1 j) volume := fun j =>
    hL c r hc hr _ (hD1 j).1 (hD1 j).2.1 (hD1 j).2.2
  have hpos : winOpen a ⊆ Ioi (0 : ℝ) ×ˢ univ := fun x hx =>
    ⟨lt_trans ha hx.1.1, trivial⟩
  -- a generic treatment of one coordinate direction
  have gen : ∀ (j : Fin 3) (ψ : Coord → ℝ) (φ : Coord → ℝ) (D g : Coord → ℂ) (T : Coord → ℝ),
      IsCoordTest φ → tsupport φ ⊆ winOpen a → IsSTTestCoord ψ → tsupport ψ ⊆ tsupport φ →
      LocallyIntegrable D volume → (∀ x, T x = -cpd j ψ x) →
      (∀ x, g x * (φ x : ℂ) = D x * (ψ x : ℂ)) →
      (∫ x, windowProfile a b x i * (cpd j ψ x : ℂ) = -∫ x, D x * (ψ x : ℂ)) →
      Integrable (fun x => b x i * (T x : ℂ)) volume ∧ Integrable (fun x => g x * (φ x : ℂ)) volume ∧
        ∫ x, g x * (φ x : ℂ) = ∫ x, b x i * (T x : ℂ) := by
    intro j ψ φ D g T hφ hsub hψ hψφ hlD hT' hg hE
    have hsubψ : tsupport ψ ⊆ winOpen a := hψφ.trans hsub
    obtain ⟨hc1, hc2, hc3⟩ := wb_cpd_prop j ψ hψ
    have hTeq : T = fun x => -cpd j ψ x := funext hT'
    refine ⟨?_, ?_, ?_⟩
    · refine hH c r hc hr b hb i T ?_ ?_ ?_
      · rw [hTeq]; exact hc1.neg
      · rw [hTeq]; exact hc2.neg
      · rw [hTeq]; show tsupport (-(cpd j ψ)) ⊆ _; rw [tsupport_neg]; exact hc3.trans (hψφ.trans (hsub.trans hpos))
    · simp_rw [hg]
      exact wb_int_loc D hlD ψ hψ.smooth.continuous hψ.compact
    · simp_rw [hg]
      exact wb_core M hM a ha b i j ψ hsubψ D T hT' hE
  have hψ1 : ∀ φ : Coord → ℝ, IsCoordTest φ → IsSTTestCoord (fun y => y.1 * φ y) := fun φ hφ =>
    ⟨contDiff_fst.mul hφ.smooth, hφ.compact.mul_left⟩
  have hψ1s : ∀ φ : Coord → ℝ, tsupport (fun y : Coord => y.1 * φ y) ⊆ tsupport φ := fun φ =>
    tsupport_mul_subset_right (f := fun y : Coord => y.1) (g := φ)
  refine ⟨?_, ?_, ?_⟩
  · intro φ hφ hsub
    exact gen 0 (fun y => y.1 * φ y) φ Dt (fun x => (x.1 : ℂ) * Dt x) (coordTranspose vS dZero φ)
      hφ hsub (hψ1 φ hφ) (hψ1s φ) hlocDt (fun x => by simp [wb_ct_S φ x])
      (fun x => by push_cast; ring) (by
        have := hT _ (hψ1 φ hφ); simpa using this)
  · intro φ hφ hsub
    exact gen 1 φ φ (D1 0) (D1 0) (coordTranspose vQ0 dZero φ) hφ hsub ⟨hφ.smooth, hφ.compact⟩
      subset_rfl (hlocD1 0) (fun x => wb_ct_Q φ x) (fun x => rfl)
      (hQ 0 φ ⟨hφ.smooth, hφ.compact⟩)
  · intro φ hφ hsub
    exact gen 2 φ φ (D1 1) (D1 1) (coordTranspose vEta dZero φ) hφ hsub ⟨hφ.smooth, hφ.compact⟩
      subset_rfl (hlocD1 1) (fun x => wb_ct_E φ x) (fun x => rfl)
      (hQ 1 φ ⟨hφ.smooth, hφ.compact⟩)

end UnforcedLeray.Short.IIb
