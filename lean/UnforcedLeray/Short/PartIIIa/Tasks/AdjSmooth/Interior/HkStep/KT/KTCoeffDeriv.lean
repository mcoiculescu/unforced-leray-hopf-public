import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs

/-!
# `KTCoeffDeriv`: the derivative of a coefficient is a coefficient

Source: `the November 2 reference manuscript` lines 3052-3058.
Smoothness and periodicity of `∂_k B_l` follow as in `B0579.IsCylTest.pd`. The decay bound
uses `∂_k B_l = (apply (dir k)) ∘ fderiv B_l`, the Bounds lemma
`norm_iteratedFDeriv_clm_apply_const`, `norm_iteratedFDeriv_fderiv`, and `‖dir k‖ ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem ktCoeffDeriv : UnforcedLeray.Short.IIIa.KTCoeffDeriv := by
  intro m c j B A k hBs hBp hBb
  have hsm : ∀ l, ContDiff ℝ ∞ (UnforcedLeray.B0579.pd k (B l)) := fun l =>
    ((contDiff_infty_iff_fderiv.1 (hBs l)).2).clm_apply contDiff_const
  have hper : ∀ l (x : ℝ × ℝ), UnforcedLeray.B0579.pd k (B l) (x.1 + c, x.2) =
      UnforcedLeray.B0579.pd k (B l) x := by
    intro l x
    have hfun : (fun y : ℝ × ℝ => B l (y + ((c, 0) : ℝ × ℝ))) = B l := by
      funext y
      have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
      rw [hy]
      exact hBp l y
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := B l) (x := x) ((c, 0) : ℝ × ℝ)
    rw [hfun] at h
    have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
    rw [hx] at h
    simp only [UnforcedLeray.B0579.pd]
    rw [← h]
  refine ⟨hsm, hper, ?_⟩
  intro l i hi x
  dsimp only
  have hdir : ‖UnforcedLeray.B0579.dir k‖ ≤ 1 := by
    fin_cases k <;> simp [UnforcedLeray.B0579.dir, Prod.norm_def]
  have hcda : ContDiffAt ℝ ∞ (fderiv ℝ (B l)) x :=
    ((contDiff_infty_iff_fderiv.1 (hBs l)).2).contDiffAt
  have h1 := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ (B l))
    (c := UnforcedLeray.B0579.dir k) (x := x) (N := ∞) (n := i) hcda (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h1
  have h2 : ‖iteratedFDeriv ℝ i (fun y => UnforcedLeray.B0579.pd k (B l) y) x‖ ≤
      ‖iteratedFDeriv ℝ (i + 1) (B l) x‖ := by
    have e : (fun y => UnforcedLeray.B0579.pd k (B l) y) =
        fun y => fderiv ℝ (B l) y (UnforcedLeray.B0579.dir k) := rfl
    rw [e]
    calc ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ (B l) y (UnforcedLeray.B0579.dir k)) x‖
        ≤ ‖UnforcedLeray.B0579.dir k‖ * ‖iteratedFDeriv ℝ (i + 1) (B l) x‖ := h1
      _ ≤ 1 * ‖iteratedFDeriv ℝ (i + 1) (B l) x‖ := by gcongr
      _ = ‖iteratedFDeriv ℝ (i + 1) (B l) x‖ := one_mul _
  have hw : 0 ≤ (1 + x.2 ^ 2) ^ ((m + 1) / 2) := by positivity
  have hb := hBb l (i + 1) (by omega) x
  calc (1 + x.2 ^ 2) ^ ((m + 1) / 2) *
        ‖iteratedFDeriv ℝ i (fun y => UnforcedLeray.B0579.pd k (B l) y) x‖
      ≤ (1 + x.2 ^ 2) ^ ((m + 1) / 2) * ‖iteratedFDeriv ℝ (i + 1) (B l) x‖ :=
        mul_le_mul_of_nonneg_left h2 hw
    _ ≤ A := hb
