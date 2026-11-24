import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_4

/-!
# `PartII-a:N01/9/1/2/4/4` (heat integral): `HeatSliceDivZero`

Source `the November 2 reference manuscript`
lines 1684-1689, 3379-3383.  For a `c`-periodic smooth force, the periodized slice is
`heatSlice c F σ w = σ⁻¹ • F (σ, w)` (`B0220.periodic_reduceIoc_eq`), so its component divergence
is `σ⁻¹` times the slab divergence `slabDiv F σ`, which vanishes by hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- Chain rule for a continuous real-linear functional applied to a differentiable map. -/
theorem hsd_fderiv_clm_comp (L : MeridC →L[ℝ] ℂ) {h : ℝ × ℝ → MeridC}
    (hh : Differentiable ℝ h) (z v : ℝ × ℝ) :
    fderiv ℝ (fun w : ℝ × ℝ => L (h w)) z v = L (fderiv ℝ h z v) := by
  have hA : HasFDerivAt (fun w : ℝ × ℝ => L (h w)) (L.comp (fderiv ℝ h z)) z :=
    L.hasFDerivAt.comp z (hh z).hasFDerivAt
  rw [hA.fderiv]
  rfl

theorem heatSliceDivZero : HeatSliceDivZero := by
  intro c hc F hF hzero σ z
  obtain ⟨hFc, hFper, s₁, s₂, R, hs₁, hz⟩ := hF
  -- the periodized slice is `σ⁻¹ • F (σ, w)`
  have hslice : ∀ σ : ℝ, ∀ w : ℝ × ℝ, heatSlice c F σ w = σ⁻¹ • F (σ, w) := by
    intro σ w
    unfold heatSlice UnforcedLeray.B0220.periodize
    have hq : UnforcedLeray.B0220.QPeriodic c (fun q : Profile => q.1⁻¹ • F q) := by
      intro p
      show p.1⁻¹ • F (p.1, p.2.1 + c, p.2.2) = p.1⁻¹ • F p
      rw [hFper p]
    exact UnforcedLeray.B0220.periodic_reduceIoc_eq _ hq σ w.1 w.2
  have hF1 : ContDiff ℝ 1 F := hFc.of_le (by simp)
  have hFd : Differentiable ℝ F := hF1.differentiable (by norm_num)
  have hFσ : ∀ w : ℝ × ℝ, DifferentiableAt ℝ (fun w' : ℝ × ℝ => F (σ, w')) w := fun w =>
    (hFd (σ, w)).comp w (hasFDerivAt_prodMk_right σ w).differentiableAt
  have hHσ : Differentiable ℝ (fun w : ℝ × ℝ => σ⁻¹ • F (σ, w)) := fun w =>
    (hFσ w).const_smul σ⁻¹
  have hH : (fun w : ℝ × ℝ => heatSlice c F σ w) = fun w : ℝ × ℝ => σ⁻¹ • F (σ, w) :=
    funext fun w => hslice σ w
  have hH' : Differentiable ℝ (fun w : ℝ × ℝ => heatSlice c F σ w) := by
    rw [hH]
    exact hHσ
  have hFσ' : Differentiable ℝ (fun w : ℝ × ℝ => F (σ, w)) := fun w => hFσ w
  -- each component divergence term
  have hterm : ∀ j : Fin 2,
      fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w j) z (UnforcedLeray.B0579.dir j) =
        σ⁻¹ • fderiv ℝ (fun w : ℝ × ℝ => F (σ, w) j) z (UnforcedLeray.B0579.dir j) := by
    intro j
    let Lj : MeridC →L[ℝ] ℂ :=
      (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 2 => ℂ) j).restrictScalars ℝ
    have e1 : (fun w : ℝ × ℝ => heatSlice c F σ w j) =
        fun w : ℝ × ℝ => Lj (heatSlice c F σ w) := rfl
    have e2 : (fun w : ℝ × ℝ => F (σ, w) j) = fun w : ℝ × ℝ => Lj (F (σ, w)) := rfl
    have hd : fderiv ℝ (fun w : ℝ × ℝ => σ⁻¹ • F (σ, w)) z =
        σ⁻¹ • fderiv ℝ (fun w : ℝ × ℝ => F (σ, w)) z :=
      fderiv_fun_const_smul (hFσ z) _
    rw [e1, hsd_fderiv_clm_comp Lj hH' z (UnforcedLeray.B0579.dir j), hH, hd,
      smul_apply, map_smul, e2,
      hsd_fderiv_clm_comp Lj hFσ' z (UnforcedLeray.B0579.dir j)]
  have hsum : ∑ j : Fin 2, fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w j) z
      (UnforcedLeray.B0579.dir j) =
      σ⁻¹ • ∑ j : Fin 2, fderiv ℝ (fun w : ℝ × ℝ => F (σ, w) j) z
        (UnforcedLeray.B0579.dir j) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  have h0 : (∑ j : Fin 2, fderiv ℝ (fun w : ℝ × ℝ => F (σ, w) j) z
      (UnforcedLeray.B0579.dir j)) = 0 := hzero σ z
  rw [hsum, h0, smul_zero]

end UnforcedLeray.Short.PartIIa.N01
