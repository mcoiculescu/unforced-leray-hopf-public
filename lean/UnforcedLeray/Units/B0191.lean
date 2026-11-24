import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# B0191 — exact `K`-homogeneity of heat derivatives

Blueprint unit `B0191`, label `eq:st18-t00194`, `paper/main.tex` lines 2927–2932
(the heat kernel `G_{νs}` is defined at line 2738, the age Euler operator
`K = η∂_η + 2s∂_s` at line 2805).

Statement in words.  Let `G_{νs}(η) = (4πνs)^{-1/2} e^{-η²/(4νs)}` be the one-dimensional heat
kernel at age `s` and let `K = η∂_η + 2s∂_s` be the age Euler operator.  For every `j ≥ 0` and
every age `s > 0`, the `j`-th `η`-derivative of the heat kernel is an exact eigenfunction of `K`:
`K ∂_η^j G_{νs} = -(j+1) ∂_η^j G_{νs}` at every `η`.  The proof is the scaling calculus: by
self-similarity `∂_η^j G_{νs}(η) = s^{-(j+1)/2} g_j(η/√s)` with `g_j = ∂^j G_ν`, so the function
`(η,s) ↦ ∂_η^j G_{νs}(η)` is homogeneous of degree `-(j+1)` under `(η,s) ↦ (λη, λ²s)`, and `K`
is the Euler operator of that scaling.

Lean conventions.  The partial derivatives in `K` are one-variable derivatives `deriv` of the
sections `y ↦ F y s` and `t ↦ F η t`.  To rule out the junk value `deriv = 0`, the file also
proves that both sections are differentiable, with explicit derivatives
(`hasDerivAt_heatDeriv_eta`, `hasDerivAt_heatDeriv_age`).  The identity holds for every real `ν`
(for `ν ≤ 0` the formula for `G_{νs}` degenerates to `0` in Lean, and the identity is then
trivial); the manuscript's standing hypothesis `ν > 0` is therefore not needed.  The Hermite
form of `g_j` is not needed either: only smoothness of the profile `G_ν` is used.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.B0191

open Filter Topology

/-- The one-dimensional heat kernel `G_{νs}(η) = (4πνs)^{-1/2} e^{-η²/(4νs)}`
(`paper/main.tex`, line 2738). -/
def heatKernel (ν s η : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * ν * s))⁻¹ * Real.exp (-η ^ 2 / (4 * ν * s))

/-- The unit-age profile `G_ν = G_{ν·1}`. -/
def profile (ν : ℝ) : ℝ → ℝ := heatKernel ν 1

/-- The derivatives `g_j = ∂^j G_ν` of the unit-age profile. -/
def profileDeriv (ν : ℝ) (j : ℕ) : ℝ → ℝ := iteratedDeriv j (profile ν)

/-- The heat derivative `(η, s) ↦ ∂_η^j G_{νs}(η)`. -/
def heatDeriv (ν : ℝ) (j : ℕ) (η s : ℝ) : ℝ := iteratedDeriv j (heatKernel ν s) η

/-- The age Euler operator `K F = η ∂_η F + 2 s ∂_s F` (`paper/main.tex`, line 2805), acting on a
function `F η s` of the similarity variable `η` and the age `s` through its partial
derivatives. -/
def ageEuler (F : ℝ → ℝ → ℝ) (η s : ℝ) : ℝ :=
  η * deriv (fun y => F y s) η + 2 * s * deriv (fun t => F η t) s

/-- Non-degeneracy check: for `ν > 0` and `s > 0` the kernel is strictly positive, so the
definition is the manuscript's Gaussian and not a junk value. -/
theorem heatKernel_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (η : ℝ) : 0 < heatKernel ν s η := by
  unfold heatKernel
  have : 0 < Real.sqrt (4 * Real.pi * ν * s) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- At every fixed age the heat kernel is a smooth function of `η`. -/
theorem contDiff_heatKernel (ν s : ℝ) : ContDiff ℝ ⊤ (heatKernel ν s) := by
  unfold heatKernel
  fun_prop

theorem contDiff_profile (ν : ℝ) : ContDiff ℝ ⊤ (profile ν) :=
  contDiff_heatKernel ν 1

/-- Each `g_j` is differentiable, with derivative `g_{j+1}`. -/
theorem hasDerivAt_profileDeriv (ν : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (profileDeriv ν j) (profileDeriv ν (j + 1) x) x := by
  have hd : Differentiable ℝ (iteratedDeriv j (profile ν)) :=
    (contDiff_profile ν).differentiable_iteratedDeriv j (WithTop.coe_lt_top _)
  have h := (hd x).hasDerivAt
  rw [← iteratedDeriv_succ] at h
  exact h

/-- Self-similarity `G_{νs}(η) = s^{-1/2} G_ν(η/√s)` for `s > 0`. -/
theorem heatKernel_selfSimilar (ν : ℝ) {s : ℝ} (hs : 0 < s) :
    heatKernel ν s = fun η => (Real.sqrt s)⁻¹ * profile ν ((Real.sqrt s)⁻¹ * η) := by
  funext η
  unfold profile heatKernel
  have h1 : Real.sqrt (4 * Real.pi * ν * s) = Real.sqrt (4 * Real.pi * ν) * Real.sqrt s :=
    Real.sqrt_mul' _ hs.le
  have h2 : -η ^ 2 / (4 * ν * s) = -((Real.sqrt s)⁻¹ * η) ^ 2 / (4 * ν * 1) := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hs.le]
    ring
  rw [h1, h2, mul_inv]
  simp only [mul_one]
  ring

/-- Self-similarity of the heat derivatives:
`∂_η^j G_{νs}(η) = s^{-(j+1)/2} g_j(η/√s)` for `s > 0` (the proof outline of
`eq:st18-t00194`, `paper/main.tex` lines 2927–2932). -/
theorem heatDeriv_selfSimilar (ν : ℝ) (j : ℕ) (η : ℝ) {s : ℝ} (hs : 0 < s) :
    heatDeriv ν j η s =
      ((Real.sqrt s)⁻¹) ^ (j + 1) * profileDeriv ν j ((Real.sqrt s)⁻¹ * η) := by
  unfold heatDeriv profileDeriv
  rw [heatKernel_selfSimilar ν hs, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul ((contDiff_profile ν).of_le le_top)]
  ring

/-- Exact homogeneity of degree `-(j+1)`: for `λ > 0` and `s > 0`,
`∂_η^j G_{ν λ² s}(λη) = λ^{-(j+1)} ∂_η^j G_{νs}(η)`. -/
theorem heatDeriv_homogeneous (ν : ℝ) (j : ℕ) (η : ℝ) {s lam : ℝ} (hs : 0 < s)
    (hlam : 0 < lam) :
    heatDeriv ν j (lam * η) (lam ^ 2 * s) = (lam⁻¹) ^ (j + 1) * heatDeriv ν j η s := by
  have hs' : 0 < lam ^ 2 * s := by positivity
  rw [heatDeriv_selfSimilar ν j _ hs', heatDeriv_selfSimilar ν j _ hs,
    Real.sqrt_mul (by positivity) s, Real.sqrt_sq hlam.le]
  have hl : lam ≠ 0 := hlam.ne'
  have hq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have harg : (lam * Real.sqrt s)⁻¹ * (lam * η) = (Real.sqrt s)⁻¹ * η := by
    field_simp
  rw [harg, mul_inv, mul_pow, mul_assoc]

/-- The `η`-section of `∂_η^j G_{νs}` is differentiable, with derivative `∂_η^{j+1} G_{νs}`. -/
theorem hasDerivAt_heatDeriv_eta (ν : ℝ) (j : ℕ) (η s : ℝ) :
    HasDerivAt (fun y => heatDeriv ν j y s) (heatDeriv ν (j + 1) η s) η := by
  have hd : Differentiable ℝ (iteratedDeriv j (heatKernel ν s)) :=
    (contDiff_heatKernel ν s).differentiable_iteratedDeriv j (WithTop.coe_lt_top _)
  have h := (hd η).hasDerivAt
  rw [← iteratedDeriv_succ] at h
  exact h

/-- For `s > 0` the age section of `∂_η^j G_{νs}(η)` is differentiable, with
`2s ∂_s ∂_η^j G_{νs} = -(j+1) ∂_η^j G_{νs} - η ∂_η^{j+1} G_{νs}`. -/
theorem hasDerivAt_heatDeriv_age (ν : ℝ) (j : ℕ) (η : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => heatDeriv ν j η t)
      (-(((j : ℝ) + 1) * heatDeriv ν j η s + η * heatDeriv ν (j + 1) η s) / (2 * s)) s := by
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  -- derivative of `r(t) = t^{-1/2}`
  have hr : HasDerivAt (fun t => (Real.sqrt t)⁻¹)
      (-(1 / (2 * Real.sqrt s)) / Real.sqrt s ^ 2) s :=
    (Real.hasDerivAt_sqrt hs.ne').fun_inv hq.ne'
  have hg := hasDerivAt_profileDeriv ν j ((Real.sqrt s)⁻¹ * η)
  have hmain := (hr.fun_pow (j + 1)).mul (hg.comp s (hr.mul_const η))
  have hev : (fun t => heatDeriv ν j η t) =ᶠ[𝓝 s]
      (fun t => ((Real.sqrt t)⁻¹) ^ (j + 1) *
        (profileDeriv ν j ∘ fun t => (Real.sqrt t)⁻¹ * η) t) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact heatDeriv_selfSimilar ν j η ht
  refine (hmain.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [heatDeriv_selfSimilar ν j η hs, heatDeriv_selfSimilar ν (j + 1) η hs]
  have h2s : (2 : ℝ) * s = 2 * Real.sqrt s ^ 2 := by rw [Real.sq_sqrt hs.le]
  rw [h2s]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Function.comp_apply]
  generalize Real.sqrt s = q at hq ⊢
  generalize profileDeriv ν j (q⁻¹ * η) = A
  generalize profileDeriv ν (j + 1) (q⁻¹ * η) = B
  simp only [pow_succ]
  generalize q⁻¹ ^ j = P
  have hq0 : q ≠ 0 := hq.ne'
  field_simp
  ring

/-- **Exact `K`-homogeneity of heat derivatives** (`paper/main.tex`, lines 2927–2932,
`eq:st18-t00194`): for every `j ≥ 0`, every age `s > 0` and every `η`,
`K ∂_η^j G_{νs} = -(j+1) ∂_η^j G_{νs}`, where `K = η∂_η + 2s∂_s`. -/
theorem ageEuler_heatDeriv (ν : ℝ) (j : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    ageEuler (heatDeriv ν j) η s = -((j : ℝ) + 1) * heatDeriv ν j η s := by
  unfold ageEuler
  rw [(hasDerivAt_heatDeriv_eta ν j η s).deriv, (hasDerivAt_heatDeriv_age ν j η hs).deriv]
  field_simp
  ring

/-- The same identity written out with the partial derivatives:
`η ∂_η(∂_η^j G_{νs})(η) + 2s ∂_s(∂_η^j G_{νs})(η) = -(j+1) ∂_η^j G_{νs}(η)` for `s > 0`
(`paper/main.tex`, line 2930). -/
theorem K_iteratedDeriv_heatKernel (ν : ℝ) (j : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    η * deriv (fun y => iteratedDeriv j (heatKernel ν s) y) η +
        2 * s * deriv (fun t => iteratedDeriv j (heatKernel ν t) η) s =
      -((j : ℝ) + 1) * iteratedDeriv j (heatKernel ν s) η :=
  ageEuler_heatDeriv ν j hs η

end UnforcedLeray.B0191
