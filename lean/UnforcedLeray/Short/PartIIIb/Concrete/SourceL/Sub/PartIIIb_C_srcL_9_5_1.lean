import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5

/-!
# Decomposition of `scPsiSmooth` (source 4178-4186, 4917-4937)

`Ψ_Z(y) = -∫_{ρ>r} ρ Z_z(rayPt y ρ) dρ`; substituting `ρ = r t` gives
`Ψ_Z(y) = -r² ∫_1^∞ t Z_z(t y₀, t y₁, y₂) dt` (`SCPsiSubst`).  The integrand
`F t y = t Z_z(t y₀,t y₁,y₂)` is `C^7` in `y` on `U = {eucSq > 11ν/12, r > 0}` (`SCPsiF_smooth`),
has measurable jets (`SCPsiF_meas`) and a local `t^{-3}` dominating bound for the jets of order
`≤ 7` (`SCPsiF_dom`); the finite-order differentiation under the integral (`SCParamInt7`) then
gives `SCPsiSmooth`.
Source: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The integrand after `ρ = r t`. -/
def psiF (Z : Vec3 → Vec3) (t : ℝ) (y : Vec3) : ℝ := t * Z ![t * y 0, t * y 1, y 2] 2

/-- The region of smoothness. -/
def psiU (ν : ℝ) : Set Vec3 := {y | ν * (11 / 12) < eucSq y ∧ 0 < cylR y}

/-- Change of variables `ρ = r t` (`MeasureTheory.integral_comp_mul_left_Ioi`, valid with no
integrability hypothesis; `rayPt y (r t) = (t y₀, t y₁, y₂)`, `r² = y₀²+y₁²`). -/
def SCPsiSubst : Prop :=
  ∀ (Z : Vec3 → Vec3) (y : Vec3), 0 < cylR y →
    streamPsi Z y = -(y 0 ^ 2 + y 1 ^ 2) * ∫ t in Ioi (1 : ℝ), psiF Z t y

/-- Differentiation under the integral to order 7 (generic; `∫ F t x dt` over `Ioi 1`): if each
`F t` is `C^7` on the open `U`, the jets `t ↦ D^k (F t) x` (`k ≤ 7`) are a.e.-strongly measurable,
and locally in `x ∈ U` they are dominated by one integrable function of `t`, then
`x ↦ ∫ F t x` is `C^7` on `U`. -/
def SCParamInt7 : Prop :=
  ∀ (U : Set Vec3) (F : ℝ → Vec3 → ℝ), IsOpen U →
    (∀ t : ℝ, 1 < t → ContDiffOn ℝ 7 (F t) U) →
    (∀ k : ℕ, k ≤ 7 → ∀ x ∈ U,
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (F t) x) (volume.restrict (Ioi (1 : ℝ)))) →
    (∀ x₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ bd : ℝ → ℝ, IntegrableOn bd (Ioi (1 : ℝ)) ∧
      ∀ k : ℕ, k ≤ 7 → ∀ t : ℝ, 1 < t → ∀ x ∈ U ∩ ball x₀ ε,
        ‖iteratedFDeriv ℝ k (F t) x‖ ≤ bd t) →
    ContDiffOn ℝ 7 (fun x => ∫ t in Ioi (1 : ℝ), F t x) U

/-- `y ↦ t Z_z(t y₀, t y₁, y₂)` is `C^7` on `psiU ν` for `t > 1` (`Z` is `C^7` on
`{eucSq > 11ν/12}`, which contains the image of `psiU ν` under `y ↦ (t y₀,t y₁,y₂)` as
`eucSq (t y₀,t y₁,y₂) ≥ eucSq y`). -/
def SCPsiF_smooth : Prop :=
  ∀ (ν B : ℝ) (Z : Vec3 → Vec3), 0 < ν → 0 ≤ B → SCZHyp ν B Z →
    ∀ t : ℝ, 1 < t → ContDiffOn ℝ 7 (psiF Z t) (psiU ν)

/-- Measurability in `t` of the jets of `psiF Z t` at `x ∈ psiU ν` (they are continuous in `t`
on `(1,∞)`: the jet of `y ↦ Z_z(L_t y)` is `D^k Z_z(L_t y) ∘ L_t^{⊗k}`, with `L_t` linear in `t`
and `D^k Z` continuous on the open set `{eucSq > 11ν/12}`). -/
def SCPsiF_meas : Prop :=
  ∀ (ν B : ℝ) (Z : Vec3 → Vec3), 0 < ν → 0 ≤ B → SCZHyp ν B Z →
    ∀ k : ℕ, k ≤ 7 → ∀ x ∈ psiU ν,
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (psiF Z t) x)
        (volume.restrict (Ioi (1 : ℝ)))

/-- Local domination: for `x₀ ∈ psiU ν` there are `ε>0` and an integrable `bd` on `(1,∞)` with
`‖D^k (psiF Z t) x‖ ≤ bd t` for `k ≤ 7`, `t > 1`, `x ∈ psiU ν ∩ B(x₀,ε)`.  (Take `ε` so that
`cylR ≥ r₀ = cylR x₀/2` on the ball; `L_t` has operator norm `≤ t`; `|L_t x| ≥ t r₀`; so the
`k`-th jet is `≤ C B t · t^k (t r₀)^{-4-k} = C B r₀^{-4-k} t^{-3}`, integrable on `(1,∞)`;
Faà di Bruno / `ContinuousLinearMap.norm_iteratedFDeriv_comp_right` and the product rule with `t`.) -/
def SCPsiF_dom : Prop :=
  ∀ (ν B : ℝ) (Z : Vec3 → Vec3), 0 < ν → 0 ≤ B → SCZHyp ν B Z →
    ∀ x₀ ∈ psiU ν, ∃ ε : ℝ, 0 < ε ∧ ∃ bd : ℝ → ℝ, IntegrableOn bd (Ioi (1 : ℝ)) ∧
      ∀ k : ℕ, k ≤ 7 → ∀ t : ℝ, 1 < t → ∀ x ∈ psiU ν ∩ ball x₀ ε,
        ‖iteratedFDeriv ℝ k (psiF Z t) x‖ ≤ bd t

theorem psiU_isOpen (ν : ℝ) : IsOpen (psiU ν) := by
  have h1 : Continuous fun y : Vec3 => eucSq y := by
    unfold eucSq; fun_prop
  have h2 : Continuous fun y : Vec3 => cylR y := by
    unfold cylR; fun_prop
  exact (isOpen_lt continuous_const h1).inter (isOpen_lt continuous_const h2)

theorem scPsiSmooth_of (hS : SCPsiSubst) (hI : SCParamInt7) (hF : SCPsiF_smooth)
    (hM : SCPsiF_meas) (hD : SCPsiF_dom) : SCPsiSmooth := by
  intro ν B Z hν hB hZ
  have hint : ContDiffOn ℝ 7 (fun x => ∫ t in Ioi (1 : ℝ), psiF Z t x) (psiU ν) :=
    hI (psiU ν) (psiF Z) (psiU_isOpen ν) (hF ν B Z hν hB hZ)
      (hM ν B Z hν hB hZ) (hD ν B Z hν hB hZ)
  have hpoly : ContDiff ℝ 7 (fun y : Vec3 => -(y 0 ^ 2 + y 1 ^ 2)) := by fun_prop
  have hprod : ContDiffOn ℝ 7
      (fun y : Vec3 => -(y 0 ^ 2 + y 1 ^ 2) * ∫ t in Ioi (1 : ℝ), psiF Z t y) (psiU ν) :=
    hpoly.contDiffOn.mul hint
  exact hprod.congr (fun y hy => hS Z y hy.2)

end UnforcedLeray.Short.PartIIIb.Concrete
