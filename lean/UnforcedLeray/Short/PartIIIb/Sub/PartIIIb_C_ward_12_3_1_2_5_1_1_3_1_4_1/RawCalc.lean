import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1
import UnforcedLeray.Cons.C03Background.RawLift
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Helpers for `RawProfSmoothGen` and `RawProfJetGen` (generic calculus, no train data)

Source `the November 2 reference manuscript` 1206-1222 (`b_raw = (v₁, v₂ + εH)`,
`H = ψ - η∂_ηψ - 2s∂_sψ`).  Let `F x = ψ x.1 x.2` on `ℝ × (ℝ × ℝ)` and `U = {m | 0 < m.1}`.
The one-variable `deriv`s of `ψ` in `η` and `s` are the partial `fderiv`s of `F`, and
`rawProfile ε v ψ m = v m.1 m.2 + (ε * R m) • e₁` on `U` with
`R m = F m - (m.2.2 * ∂_η F m + 2 * m.1 * ∂_s F m)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The open set `{m | 0 < m.1}` (the region `s > 0`). -/
theorem isOpen_ageSet : IsOpen {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
  isOpen_lt continuous_const continuous_fst

/-- `∂_η` of a function on `ℝ × (ℝ × ℝ)` at a differentiability point is the `fderiv` in
the direction `(0,(0,1))`. -/
theorem deriv_eta_eq_fderiv {F : ℝ × (ℝ × ℝ) → ℝ} {x : ℝ × (ℝ × ℝ)} (hd : DifferentiableAt ℝ F x) :
    deriv (fun t => F (x.1, (x.2.1, t))) x.2.2 = fderiv ℝ F x (0, (0, 1)) := by
  have hline : HasDerivAt (fun e : ℝ => ((x.1, (x.2.1, e)) : ℝ × (ℝ × ℝ)))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) x.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  exact (hd.hasFDerivAt.comp_hasDerivAt x.2.2 hline).deriv

/-- `∂_s` of a function on `ℝ × (ℝ × ℝ)` at a differentiability point is the `fderiv` in
the direction `(1,(0,0))`. -/
theorem deriv_age_eq_fderiv {F : ℝ × (ℝ × ℝ) → ℝ} {x : ℝ × (ℝ × ℝ)} (hd : DifferentiableAt ℝ F x) :
    deriv (fun t => F (t, x.2)) x.1 = fderiv ℝ F x (1, (0, 0)) := by
  have hline : HasDerivAt (fun e : ℝ => ((e, x.2) : ℝ × (ℝ × ℝ)))
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) x.1 :=
    (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
  exact (hd.hasFDerivAt.comp_hasDerivAt x.1 hline).deriv

/-- A fixed-direction `fderiv` of a jointly `C^∞` function on an open set is `C^∞` there. -/
theorem fderiv_dir_contDiffOn {F : ℝ × (ℝ × ℝ) → ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (w : ℝ × (ℝ × ℝ)) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x w) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (m := ∞) (by simp)
  exact h1.clm_apply contDiffOn_const

/-- On the region `s > 0`, the raw profile is `v + (ε R) • e₁` with `R` written through the
`fderiv`s of `F = ψ` (the one-variable derivatives of `ψ` are the partial `fderiv`s). -/
theorem rawProfile_eq_fderiv (ε : ℝ) (v : ℝ → ℝ × ℝ → EuclideanSpace ℝ (Fin 2))
    (ψ : ℝ → ℝ × ℝ → ℝ)
    (hψ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    {m : ℝ × (ℝ × ℝ)} (hm : 0 < m.1) :
    UnforcedLeray.Cons.C03.rawProfile ε v ψ m =
      v m.1 m.2 + (ε * ((fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) m -
        (m.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) m (0, (0, 1)) +
          2 * m.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) m (1, (0, 0))))) •
        EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  have hmem : m ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hm
  have hca : ContDiffAt ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) m :=
    hψ.contDiffAt (isOpen_ageSet.mem_nhds hmem)
  have hd : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) m :=
    hca.differentiableAt (by simp)
  have he := deriv_eta_eq_fderiv hd
  have ha := deriv_age_eq_fderiv hd
  unfold UnforcedLeray.Cons.C03.rawProfile UnforcedLeray.Cons.C03.raisedStream
  rw [he, ha]

end UnforcedLeray.Short.PartIIIb.Concrete
