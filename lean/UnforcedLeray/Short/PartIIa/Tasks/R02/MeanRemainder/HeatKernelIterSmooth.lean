import UnforcedLeray.Short.PartIIa.Sub.R02_3
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part II-a, task `PartII-a:R02/3/2`: joint smoothness of the heat-kernel `η`-derivatives

Source of record: `the November 2 reference manuscript`, lines 447-449
(`sct:expansion`: the finite sum `∑ a_{2j} ∂_η^{2j} G_{νs}` in the expansion of `S`).

For `ν > 0` and `k : ℕ`, the map `(s, η) ↦ ∂_η^k G_{νs}(η)` is `C^∞` on `(0, ∞) × ℝ`.
Two steps: `heatKernel1` is jointly `C^∞` on the open set `(0, ∞) × ℝ` (elementary calculus),
and the `η`-derivative of a jointly `C^∞` function is jointly `C^∞` (induction on `k`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- **Joint smoothness of the scaled heat kernel**: for `ν > 0`, `(s, η) ↦ G_{νs}(η)` is `C^∞`
on `(0, ∞) × ℝ`. -/
theorem heatKernel1_contDiffOn_scaled {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.heatKernel1 (ν * x.1) x.2)
      (Ioi 0 ×ˢ univ) := by
  have hx1 : ∀ x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), 0 < x.1 := fun x hx => hx.1
  have h4 : ∀ x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), 0 < 4 * Real.pi * (ν * x.1) :=
    fun x hx => mul_pos (by positivity) (mul_pos hν (hx1 x hx))
  have hA : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => 4 * Real.pi * (ν * x.1)) (Ioi 0 ×ˢ univ) := by
    fun_prop
  have hsq : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => Real.sqrt (4 * Real.pi * (ν * x.1)))
      (Ioi 0 ×ˢ univ) :=
    hA.sqrt (fun x hx => (h4 x hx).ne')
  have hinv : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => (Real.sqrt (4 * Real.pi * (ν * x.1)))⁻¹)
      (Ioi 0 ×ˢ univ) :=
    hsq.inv (fun x hx => (Real.sqrt_pos.2 (h4 x hx)).ne')
  have hnum : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => -(x.2 ^ 2)) (Ioi 0 ×ˢ univ) := by
    fun_prop
  have hden : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => 4 * (ν * x.1)) (Ioi 0 ×ˢ univ) := by
    fun_prop
  have hden_ne : ∀ x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), 4 * (ν * x.1) ≠ 0 :=
    fun x hx => (mul_pos (by norm_num) (mul_pos hν (hx1 x hx))).ne'
  have harg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => -(x.2 ^ 2) / (4 * (ν * x.1)))
      (Ioi 0 ×ˢ univ) :=
    hnum.div hden hden_ne
  have hexp : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => Real.exp (-(x.2 ^ 2) / (4 * (ν * x.1))))
      (Ioi 0 ×ˢ univ) :=
    harg.exp
  have hprod := hinv.mul hexp
  simp only [UnforcedLeray.Short.PartI.heatKernel1]
  exact hprod

/-- **`η`-derivatives of a jointly smooth function are jointly smooth** (calculus): if
`f(s, η)` is `C^∞` on `(0, ∞) × ℝ`, then so is `(s, η) ↦ ∂_η^k f(s, η)`, for every `k`.
Same induction as `ageDerivIter_contDiffOn` (`Tasks/R02/FluctuationProfile/AgeDerivSmooth.lean`),
with the differentiated variable in the second slot. -/
theorem etaDerivIter_contDiffOn (f : ℝ → ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => f x.1 x.2) (Ioi 0 ×ˢ univ)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv k (fun e => f x.1 e) x.2)
      (Ioi 0 ×ˢ univ) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have hderiv : ∀ x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        iteratedDeriv (k + 1) (fun e => f x.1 e) x.2 =
          fderiv ℝ (fun y : ℝ × ℝ => iteratedDeriv k (fun e => f y.1 e) y.2) x (0, 1) := by
      rintro ⟨s, e⟩ hx
      have hdiff : DifferentiableAt ℝ
          (fun y : ℝ × ℝ => iteratedDeriv k (fun e' => f y.1 e') y.2) (s, e) :=
        (ih.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      have hline : HasDerivAt (fun r : ℝ => ((s, r) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) e :=
        (hasDerivAt_const e s).prodMk (hasDerivAt_id' e)
      have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt e hline
      rw [iteratedDeriv_succ]
      exact hcomp.deriv
    have hsm : ContDiffOn ℝ ∞
        (fun y : ℝ × ℝ =>
          fderiv ℝ (fun z : ℝ × ℝ => iteratedDeriv k (fun e' => f z.1 e') z.2) y (0, 1))
        (Ioi 0 ×ˢ univ) :=
      (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    exact hsm.congr fun x hx => hderiv x hx

/-- **`HeatKernelIterSmooth`** (`Sub/R02_3.lean`; source lines 447-449): for `ν > 0` and `k : ℕ`,
`(s, η) ↦ ∂_η^k G_{νs}(η)` is `C^∞` on `(0, ∞) × ℝ`. -/
theorem heatKernelIterSmooth : UnforcedLeray.Short.PartIIa.HeatKernelIterSmooth := by
  unfold UnforcedLeray.Short.PartIIa.HeatKernelIterSmooth
  intro ν hν k
  exact etaDerivIter_contDiffOn (fun s e => UnforcedLeray.Short.PartI.heatKernel1 (ν * s) e)
    (heatKernel1_contDiffOn_scaled hν) k

end UnforcedLeray.Short.PartIIa
