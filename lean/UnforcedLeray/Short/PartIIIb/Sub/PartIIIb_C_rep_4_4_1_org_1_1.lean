import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_4_1_org_1_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1`: the young-region body velocity of the old repair response

Source `the November 2 reference manuscript`
3611-3621 (`sep:resolvent`), 3600-3603 and 4165-4170 (the local distributional part of `K_0` is
"retained by the operator, but vanishes at a separated receiver"), 4163-4194, 5169-5176.

## Findings of the design check

1. `wardW = sepWre` of the separated representative `T` holds at **every** `(τ, y)`
   (`wardW_eq_sepWre`, proved below): it is an identity between two evaluations of `IIIa.sepW`,
   `oldPhys (g₁+g₂)` and `T`, and does not depend on the region.
2. `IIIa.sepW` is the *Lebesgue* integral of `∇K_{ν(1-λ²)}(y - λz) : T`.  It is the true field
   `-S_μ T` only at separated receivers `|y'| > r_o`, i.e. ages `s < 1.2/ν` (the old source is
   supported at `s ≥ 1.2/ν`, source 4163-4166); inside the old disk the kernel `|x|^{-4}` is not
   integrable and the operator's local distributional part (4165-4170) is missing, so `sepW` is
   junk there (a Bochner integral of a non-integrable function is `0`).  The paper itself only
   claims `X, DX, Y ∈ Y_2` for the *cut* field `𝒞_y X₀` supported at `s ≤ 1/ν` (4187-4194).
3. Consequently `SepRepBodyAt` (global body velocity `B = -coefOf (wardW ..)` a.e. on the whole body
   measure), `SepNegSolenoidalAt` and `SepNegEquationAt` (global weak equation of `-W_μ` against
   all solenoidal tests) of `PartIII-b_C_rep_4_4_1_org_1(_2)` are not source facts.  The
   source fact, and what `SepYoungRepAt` states, is a **young-region** identity
   `S_μ(χ_oT) = -W_μ` a.e. on `ν s ≤ 1`.  The honest route is the one designed for the thin
   source in `PartIII-b_C_rep_4_2_org_1_1_2`: `S` is the weak stress inverse (a global
   `Y_2` solution), it agrees with `-sepW` on the young region for smooth compactly supported
   old sources, and density plus continuity of both sides in the repair source norm
   `L²_τL^{22/19}` passes to the limit.  The continuity of the `sepW` side is exactly the content
   of this file: the young-region `Y_2` bound of `W_μ` by `‖T‖_{L²_τL^{22/19}}`
   (`SepRepair`, third clause with `j = 0`, `D = r_i - r_o = R√ν(1-√(5/6))`).

This file defines the young-region body-velocity statement `SepRepBodyYoungAt`, proves it from the
measurability and `L²` finiteness of the cut field, and states the transport from young-point
`ltauAt`/`ltauLq` norms to the chart body measure (`ChartYoungTransport`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`wardW = sepWre` on the whole of `ℝ × ℝ³`** (source 3611-3621, 4163-4174): `W_μ` of the
old repair source `g₁ + g₂` is `Re` of the separated response `IIIa.sepW` of the separated
representative `T` (`srRep_sepT`), at every phase and every point.  This is an identity of the
two Lebesgue integrals; that it equals `-S_μ(χ_oT)` is true only at separated receivers. -/
theorem wardW_eq_sepWre (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (w : LVel Pl L)
    {g₁ g₂ : Chart → Ten3} (hg : IsRep Pl K L (oldRep Pl K L w) g₁ g₂) :
    ∃ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) T ∧
      SepMoment (2 * L.ε * cOf L.ν) T ∧
      ∀ (τ : ℝ) (y : Space),
        wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) τ y = sepWre L.ν μ T τ y := by
  obtain ⟨T, h1, h2, h3⟩ := srRep_sepT Pl K L hC0 hmZ w hg
  refine ⟨T, h1, h2, fun τ y => ?_⟩
  simp only [wardW, sepWre, h3]

/-- The cut field of Lemma A: `-W_μ` read in the chart on the young region `ν s ≤ 1`, `0`
elsewhere. -/
def youngWCoef (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (g : Chart → Ten3) : Chart → Merid :=
  fun p => if L.ν * p.1 ≤ 1 then -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) g) p else 0

/-- **Lemma A, restated on the young region** (source 4187-4194): there is a body velocity
`B ∈ VelG` equal to `-W_μ` (in the chart) at body-a.e. young point `ν s ≤ 1`. -/
def SepRepBodyYoungAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    ∃ B : LVel Pl L, ∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν), L.ν * p.1 ≤ 1 →
      (B : Chart → Merid) p = -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p

/-- **Finiteness** (source 4187-4194, 5169-5176): the cut field is in `L²(bodyMeasure)`.  This is
`SepRepair` (third clause, `j = 0`) plus `repair:source` plus the chart transport below. -/
def SepRepYoungMemLpAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    MemLp (youngWCoef Pl K L μ (g₁ + g₂)) 2 (bodyMeasure (cOf L.ν) (gRate Pl) L.ν)

/-- Lemma A on the young region from the `L²` membership of the cut field. -/
theorem sepRepBodyYoungAt_of {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (h : SepRepYoungMemLpAt Pl K L μ) : SepRepBodyYoungAt Pl K L μ := by
  intro w g₁ g₂ hg
  refine ⟨(h w g₁ g₂ hg).toLp _, ?_⟩
  filter_upwards [(h w g₁ g₂ hg).coeFn_toLp] with p hp hy
  rw [hp]
  simp [youngWCoef, hy]

/-- **Transport from young-point norms to the chart body measure** (source 2666-2668, 2683,
5143): for a `2c/R`-periodic axisymmetric swirl-free field `F`, the unweighted chart norm of
`p ↦ coefOf R F p` on the young region `ν s ≤ 1` (`|y'| = R/√s ≥ R√ν`) under `ageμ c (-3/2)`
equals `(πR²)⁻¹` times the normalized `L²_τL²_y` norm squared of `F` on `|y'| ≥ R√ν` (change of
variables `r = R s^{-1/2}`, `z = η s^{-1/2}`, `τ = 2q/R + log s`; `dy = π R² s^{-5/2} ds dη`,
`dq = (R/2)dτ`; stated as `≤`, equality holds). -/
def ChartYoungTransport (R c ν : ℝ) : Prop :=
  ∀ F : ℝ → Space → Space, Measurable (fun x : ℝ × Space => F x.1 x.2) → AxiNoSwirl F →
    (∀ τ y, F (τ + 2 * c / R) y = F τ y) →
      ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R F p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
        ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
          IIIa.ltauLq (2 * c / R) 2
            (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then ‖F τ y‖ₑ else 0) ^
              (2 : ℝ)

end UnforcedLeray.Short.PartIIIb.Concrete
end
