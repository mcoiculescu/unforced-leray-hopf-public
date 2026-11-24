import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_of
import UnforcedLeray.Lib.LerayLp.Helmholtz
import UnforcedLeray.Lib.LerayC.Complex
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# `PartII-b:T10/org/2/3/3` (`LerayCDensity`): decomposition

Source `the November 2 reference manuscript` lines 1409-1412: `𝐏F = curl A` with
`A = N ∗ curl F` (`A = O(|x|⁻²)`, `DA = O(|x|⁻³)`), the cutoffs `curl(χ(·/n) A)` are compactly
supported solenoidal smooth fields and converge to `curl A` in `L^r`, `r > 1`.

Real part: `𝐏f = f + ∇ψ` for a real test field (`ψ = N ∗ div f`, `RealLerayTestFormula`), and
`f + ∇ψ = curl (N ∗ curl f)` (`NewtonCurlIdentity`) with decay (`NewtonCurlDecay`); complex lift
(`CurlPotentialC`); cutoff solenoidality (`CutoffCurlSolTest`) and `L^r` convergence
(`CutoffCurlConverge`).  `lerayCDensity_of` assembles `LerayCDensity` from the last three.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- Complex curl `(curl A)ᵢ = ∂_{i+1} A_{i+2} - ∂_{i+2} A_{i+1}` of `A : ℝ³ → ℂ³`. -/
def curlC (A : Space → CVec3) (x : Space) : CVec3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    fderiv ℝ A x (EuclideanSpace.single (i + 1) (1 : ℝ)) (i + 2) -
      fderiv ℝ A x (EuclideanSpace.single (i + 2) (1 : ℝ)) (i + 1)

/-- Real curl `(curl A)ᵢ = ∂_{i+1} A_{i+2} - ∂_{i+2} A_{i+1}` of a component family. -/
def curlR (A : Fin 3 → Space → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  spatialTestDerivative (i + 1) (A (i + 2)) x - spatialTestDerivative (i + 2) (A (i + 1)) x

/-- The real `curl f` as a component family: `(curl f)ᵢ = curlR f i`. -/
def curlComp (f : Fin 3 → Space → ℝ) : Fin 3 → Space → ℝ := fun i x => curlR f i x

/-- The projected Newton potential `A = N ∗ curl f` (componentwise). -/
def newtonCurlPotential (f : Fin 3 → Space → ℝ) : Fin 3 → Space → ℝ :=
  fun i => newtonConv (curlComp f i)

/-- **Real Leray formula on test fields** (`1 < r < ∞`): for `f` a smooth compactly supported real
field, `𝐏f = f + ∇ψ` a.e., `ψ = N ∗ div f` (`lerayPotential`).  Route: `f + ∇ψ` is solenoidal
(`isSolenoidal_vecField_add_gradField`) and in `L^r` (`memLp_gradField_lerayPotential'`), so fixed
by `lerayLp_eq_self`; `𝐏∇ψ = 0` (`lerayLp_gradient_eq_zero`); linearity. -/
def RealLerayTestFormula : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h2 : r ≠ ⊤) (f : Fin 3 → Space → ℝ),
    (∀ j, IsSpatialTest (f j)) → ∀ hm : MemLp (vecField f) r (volume : Measure Space),
      (⇑(lerayLp r h1 h2 (hm.toLp (vecField f))) : Space → Space) =ᵐ[volume]
        vecField f + gradField (lerayPotential f)

/-- **`f + ∇(N ∗ div f) = curl (N ∗ curl f)`** for a smooth compactly supported real field
(`curl curl = ∇ div - Δ`, `newtonConv_laplacian_test`, `newtonConv_partial`). -/
def NewtonCurlIdentity : Prop :=
  ∀ f : Fin 3 → Space → ℝ, (∀ j, IsSpatialTest (f j)) →
    ∀ (i : Fin 3) (x : Space),
      f i x + spatialTestDerivative i (lerayPotential f) x = curlR (newtonCurlPotential f) i x

/-- **Smoothness and decay of the Newton curl potential**: `A = N ∗ curl f` is smooth,
`|Aᵢ| ≲ (1+|x|)⁻²` and `|∂ⱼ Aᵢ| ≲ (1+|x|)⁻³` (`curl f` has mean zero; second-order Newton
kernels decay like `|x|⁻³`, `rieszPairTest_decay`, `abs_newtonPair_le_of_far`). -/
def NewtonCurlDecay : Prop :=
  ∀ f : Fin 3 → Space → ℝ, (∀ j, IsSpatialTest (f j)) →
    (∀ i, ContDiff ℝ ∞ (newtonCurlPotential f i)) ∧
    (∃ C : ℝ, ∀ (i : Fin 3) (x : Space), |newtonCurlPotential f i x| ≤ C * (1 + ‖x‖) ^ (-2 : ℝ)) ∧
    (∃ C : ℝ, ∀ (i j : Fin 3) (x : Space),
      |spatialTestDerivative j (newtonCurlPotential f i) x| ≤ C * (1 + ‖x‖) ^ (-3 : ℝ))

/-- **Complex Leray projection of a test field is the curl of a decaying potential**
(`lerayC_apply`: split `F` into real and imaginary parts, apply `RealLerayTestFormula`,
`NewtonCurlIdentity`, `NewtonCurlDecay`; `A = ofReV (A_re) + i ofImV (A_im)`). -/
def CurlPotentialC : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h2 : r ≠ ⊤) (F : Space → CVec3),
    ContDiff ℝ ∞ F → HasCompactSupport F → ∀ hF : MemLp F r (volume : Measure Space),
      ∃ A : Space → CVec3, ContDiff ℝ ∞ A ∧
        (∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (1 + ‖x‖) ^ (-2 : ℝ)) ∧
        (∃ C : ℝ, ∀ x, ‖fderiv ℝ A x‖ ≤ C * (1 + ‖x‖) ^ (-3 : ℝ)) ∧
        (⇑(lerayC r h1 h2 (hF.toLp F)) : Space → CVec3) =ᵐ[volume] curlC A

/-- **Cutoff curls are `SpatialSolTest`s**: for smooth `A` and smooth compactly supported `χ`,
`curl (χ(·/n) A)` is smooth, compactly supported and divergence free (`n ≥ 1`; symmetry of second
derivatives). -/
def CutoffCurlSolTest : Prop :=
  ∀ A : Space → CVec3, ContDiff ℝ ∞ A → ∀ χ : Space → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∀ n : ℕ, 1 ≤ n → SpatialSolTest (curlC fun x => χ ((n : ℝ)⁻¹ • x) • A x)

/-- **`L^r` convergence of the cutoff curls** (`r > 1`): with `A = O(|x|⁻²)`, `DA = O(|x|⁻³)` and
`χ = 1` on the unit ball, `curl(χ(·/n) A) - curl A = ∇χ(·/n)/n × A + (1 - χ(·/n)) curl A` is
bounded by `C (1+|x|)⁻³ 1_{|x| ≥ n}`, which is in `L^r` for `r > 1` and tends to `0`
(dominated convergence, `memLp_powWeight`). -/
def CutoffCurlConverge : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (_ : 1 < r) (_ : r ≠ ⊤) (A : Space → CVec3), ContDiff ℝ ∞ A →
    (∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (1 + ‖x‖) ^ (-2 : ℝ)) →
    (∃ C : ℝ, ∀ x, ‖fderiv ℝ A x‖ ≤ C * (1 + ‖x‖) ^ (-3 : ℝ)) →
    ∀ χ : Space → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ x, ‖x‖ ≤ 1 → χ x = 1) →
      ∃ (hc : MemLp (curlC A) r (volume : Measure Space))
        (hn : ∀ n : ℕ, MemLp (curlC fun x => χ ((n : ℝ)⁻¹ • x) • A x) r (volume : Measure Space)),
        Tendsto (fun n : ℕ => (hn n).toLp (curlC fun x => χ ((n : ℝ)⁻¹ • x) • A x)) atTop
          (𝓝 (hc.toLp (curlC A)))

theorem lerayCDensity_of (ha : CurlPotentialC) (hb : CutoffCurlSolTest)
    (hc : CutoffCurlConverge) : LerayCDensity := by
  intro r _ h1 h2 F hFs hFc hF
  obtain ⟨A, hAs, hA2, hA3, hae⟩ := ha r h1 h2 F hFs hFc hF
  let χb : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, by norm_num⟩
  obtain ⟨hcm, hn, ht⟩ := hc r h1 h2 A hAs hA2 hA3 (fun x => χb x) χb.contDiff
    χb.hasCompactSupport (fun x hx => χb.one_of_mem_closedBall (by simpa using hx))
  have heq : lerayC r h1 h2 (hF.toLp F) = hcm.toLp (curlC A) :=
    Lp.ext (hae.trans hcm.coeFn_toLp.symm)
  rw [heq]
  refine mem_closure_of_tendsto ht (eventually_atTop.2 ⟨1, fun n hn1 => ?_⟩)
  exact ⟨_, hn n, hb A hAs _ χb.contDiff χb.hasCompactSupport n hn1, rfl⟩

end UnforcedLeray.Short.IIb
