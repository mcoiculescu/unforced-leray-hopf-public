import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellConvBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellConvDeriv

/-!
# `PartIII-a:T21/2/7/2/1/1/5/10`: the mollified field is smooth, periodic, with every partial in `X_{-m,c}`

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061.

Proof: `CellConvDeriv` with `K = molKer n` gives smoothness, periodicity, and
`adjSpatial w (cellMoll n f) = cellConv (pdWordR w (molKer n)) f`. The kernel `pdWordR w (molKer n)`
is smooth (iterated `B0579.pd` of a smooth function) and its support lies in the support of
`molKer n`, the closed ball of radius `1/(n+1) ≤ 1`. So `CellConvBound` applies to it and gives the
`X_{-m,c}` membership.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Iterated classical partials of a smooth real kernel are smooth. -/
theorem cms_pdWordR_contDiff : ∀ (w : List (Fin 2)) (K : ℝ × ℝ → ℝ), ContDiff ℝ ∞ K →
    ContDiff ℝ ∞ (pdWordR w K)
  | [], K, hK => hK
  | j :: w, K, hK => by
    show ContDiff ℝ ∞ (B0579.pd j (pdWordR w K))
    exact pd_contDiff_cellConvDeriv (cms_pdWordR_contDiff w K hK)

/-- The partial derivative of a function vanishes outside the closed support of the function. -/
theorem cms_pd_eq_zero (g : ℝ × ℝ → ℝ) (y : ℝ × ℝ) (j : Fin 2) (hy : y ∉ tsupport g) :
    B0579.pd j g y = 0 := by
  show fderiv ℝ g y (B0579.dir j) = 0
  rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]
  simp

/-- Iterated partials have support inside the support of the kernel. -/
theorem cms_tsupport_pdWordR : ∀ (w : List (Fin 2)) (K : ℝ × ℝ → ℝ),
    tsupport (pdWordR w K) ⊆ tsupport K
  | [], K => subset_rfl
  | j :: w, K => by
    have h := cms_tsupport_pdWordR w K
    have h2 : tsupport (fun x => fderiv ℝ (pdWordR w K) x (B0579.dir j)) ⊆ tsupport (pdWordR w K) :=
      tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := pdWordR w K) (B0579.dir j)
    show tsupport (fun x => fderiv ℝ (pdWordR w K) x (B0579.dir j)) ⊆ tsupport K
    exact h2.trans h

/-- Iterated partials vanish outside the support of the kernel. -/
theorem cms_pdWordR_eq_zero : ∀ (w : List (Fin 2)) (K : ℝ × ℝ → ℝ) (y : ℝ × ℝ),
    y ∉ tsupport K → pdWordR w K y = 0
  | [], K, y, hy => image_eq_zero_of_notMem_tsupport hy
  | j :: w, K, y, hy => by
    show B0579.pd j (pdWordR w K) y = 0
    apply cms_pd_eq_zero
    exact fun h => hy (cms_tsupport_pdWordR w K h)

/-- The support of the mollifier `molKer n` misses the complement of the unit sup-norm ball. -/
theorem cms_molKer_notMem_tsupport (n : ℕ) (y : ℝ × ℝ) (hy : 1 < ‖y‖) :
    y ∉ tsupport (molKer n) := by
  intro h
  have hts : tsupport (molKer n) = Metric.closedBall (0 : ℝ × ℝ) (molBump n).rOut :=
    (molBump n).tsupport_normed_eq (μ := volume)
  rw [hts, mem_closedBall_zero_iff] at h
  have hr : (molBump n).rOut ≤ 1 := by
    show 1 / ((n : ℝ) + 1) ≤ 1
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_one (by positivity)]
    linarith
  linarith

/-- **The mollified field is smooth, periodic, with every partial in `X_{-m,c}`** (SP 3060-3061). -/
theorem cellMollSmooth : UnforcedLeray.Short.IIIa.CellMollSmooth := by
  intro c m n f hc hper hf
  obtain ⟨hcd, hcper, hadj⟩ := cellConvDeriv c m (molKer n) f hc
    ((molBump n).contDiff_normed (μ := volume)) ((molBump n).hasCompactSupport_normed (μ := volume))
    hper hf
  refine ⟨hcd, hcper, fun w => ?_⟩
  show MemLp (adjSpatial w (cellConv (molKer n) f)) 2 (B0579.cellMeasure c (-m))
  rw [hadj w]
  have hK : ContDiff ℝ ∞ (pdWordR w (molKer n)) :=
    cms_pdWordR_contDiff w (molKer n) ((molBump n).contDiff_normed (μ := volume))
  have hcont : Continuous (pdWordR w (molKer n)) := hK.continuous
  have hzero : ∀ y : ℝ × ℝ, 1 < ‖y‖ → pdWordR w (molKer n) y = 0 :=
    fun y hy => cms_pdWordR_eq_zero w (molKer n) y (cms_molKer_notMem_tsupport n y hy)
  obtain ⟨_, _, hC⟩ := cellConvBound c m hc
  obtain ⟨hmem, _⟩ := hC (pdWordR w (molKer n)) f hcont hzero hper hf
  exact hmem

end UnforcedLeray.Short.IIIa
