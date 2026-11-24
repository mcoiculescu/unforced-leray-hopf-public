import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntAll
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3b
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3c

/-!
# `WardXrSmoothData` decomposed (`PartIII-b:IIIb-D2/3/2/11/2`, source 4161-4186, 3604-3621)

Source of record: `the November 2 reference manuscript`.
The target `WardXrSmoothData` is `wardXrSmoothData_of` from the source facts

* `SmoothOldSource` (the physical source of smooth old data is a separated source with finite
  `Y₂` moment, 4155-4163),
* `WardX0SmoothInf` (joint `C^∞` of `X₀` on the young region, 3604-3621),
* `WardX0DecayInf` (decay for the outward primitive, 4177-4179),
* `WardX0DivFree` (`X₀` solenoidal on the young region, 3600-3610),
* `OutPrimSmoothInf` (joint `C^∞` of the outward primitive, 4177-4179),
* `WardXrSmoothOfParts` (joint `C^∞` of `wardXr`, 4180-4186),
* `WardXrAxiOfX0` (the symmetry of `wardXr`, 121-124, 4171-4178),

and the accepted `wardX0_periodic`, `sepIntegrableOfSource_all`, `wardX0Axi_all`,
`outPrimDerivR`, `outPrimDerivZ`, `wardStreamCutDivFree_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **(A)** The physical source of smooth old data is an `IIIa.IsSepSource` of period `2c/R`
supported in `ϱ ≤ R√(5ν/6)` (measurable because `g` is smooth, periodic by `oldPhysPeriodic`,
support by `IsSmoothOld.old`) with finite `Y₂` moment (bounded, compactly supported in `z`)
(source 4155-4166). -/
def SmoothOldSource : Prop :=
  ∀ (ν R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → IsSmoothOld c ν g →
    IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6)) (oldPhys R c g) ∧
      SepMoment (2 * c / R) (oldPhys R c g)

/-- **(B1)** `X₀ = wardX0` is jointly `C^∞` on `ℝ × {ϱ > R√(5ν/6)}` for smooth old data
(source 3604-3621: differentiate `sep:resolvent` under the integral to every order with
`|D^j∇K_t(x)| ≤ C_j|x|^{-4-j}`, `IIIa.SepKernelBounds`, the gap `|y - λz| ≥ ϱ(y) - λϱ(z)`, the
`τ`-derivatives falling on `T(z, τ + 2 log λ)`; `T = oldPhys R c g` is jointly `C^∞` since `g` vanishes
near the seam and near `s = 0`). -/
def WardX0SmoothInf : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → IsSmoothOld c ν g →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => wardX0 ν μ R c g x.1 x.2)
      {x | x.2 ∈ youngOpen ν R}

/-- **(B2)** Decay of `X₀` for the outward primitive (`StreamDecay`, source 4177-4179: the bounds
`|∂^α X₀(τ,y)| ≤ C_α|y|^{-4}` for `|y| ≥ 2ρ₀` of (B1) give the integrable majorant on `(r, ∞)` and
`ρ X₀,r → 0`). -/
def WardX0DecayInf : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → IsSmoothOld c ν g →
    ∀ τ, StreamDecay ν R (wardX0 ν μ R c g) τ

/-- **(B3)** `X₀` is divergence free on the young region (source 3600-3610, 3611-3621: the
accepted `sepWDivFree_all` for `sepW`, with the real parts of the differentiable `sepW`
(`SepWSmoothOn`, source of `OldSource`: `SmoothOldSource`) in `wardX0`). -/
def WardX0DivFree : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → IsSmoothOld c ν g →
    ∀ τ, ∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (wardX0 ν μ R c g τ) j y j = 0

/-- **(B4)** The outward primitive of `X₀` is jointly `C^∞` on `r > R√(5ν/6)` (source 4177-4179:
differentiate `-∫_r^∞ ρ X₀,z(τ, ρ, 0, z) dρ` under the integral using the decay `|∂^αX₀| ≤ C_α|y|^{-4}`
of (B1) and the fundamental theorem of calculus for the lower limit). -/
def OutPrimSmoothInf : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → IsSmoothOld c ν g →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ × ℝ => outPrim (wardX0 ν μ R c g) x.1 x.2.1 x.2.2)
      {x | R * Real.sqrt (5 * ν / 6) < x.2.1}

/-- **(C)** `wardXr` is jointly `C^∞` (source 4180-4186, 4182-4183): it is `0` on the open set
`{ϱ < R√ν}` (`wardXr_eq_zero_of_sq_le`) and equals `wardStreamCut ν R χy X₀` on the open set
`youngOpen ν R` off the axis (`wardXr_of_not_mem`), a composition of smooth maps there
(`χy`, `deriv χy` smooth; `ϱ`, `age` smooth off the axis, `contDiffOn_ϱ`,
`Lib/Axisymmetric/Cylindrical.lean:245`; `X₀` and `outPrim X₀` smooth by (B1), (B4)); the two open
sets cover `Space` since `5/6 < 1`. -/
def WardXrSmoothOfParts : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → IsYoungCutoff χy →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => wardX0 ν μ R c g x.1 x.2)
      {x | x.2 ∈ youngOpen ν R} →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ × ℝ => outPrim (wardX0 ν μ R c g) x.1 x.2.1 x.2.2)
      {x | R * Real.sqrt (5 * ν / 6) < x.2.1} →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => wardXr ν μ R c χy g x.1 x.2)

/-- **(D)** Symmetry of `wardXr` (source 121-124, 4171-4178): from the frame form of `X₀` on the
young region, `wardXr τ` is axisymmetric without swirl: off the axis `wardXr = χy(ν age)X₀ +
(…)Ψ e_z` with `χy(ν age)`, `ϱ`, `y₃` and `Ψ(ϱ, y₃)` invariant under every orthogonal `g` fixing
`e₃` (`ϱ_symm_apply`, `symm_apply_two`), `X₀` the frame lift of its trace
(`map_eR_symm`, `map_hor_symm`), `e_z` fixed; on the axis `wardXr = 0` (and `g` fixes the axis, so
both sides are `0`). -/
def WardXrAxiOfX0 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → IsYoungCutoff χy →
    AxiNoSwirlOn (youngOpen ν R) (wardX0 ν μ R c g) →
    ∀ τ, AxiNoSwirlPt (wardXr ν μ R c χy g τ)

/-! ## Proved here -/

theorem wardXr_periodic_of (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    wardXr ν μ R c χy g (τ + 2 * c / R) y = wardXr ν μ R c χy g τ y := by
  have hZ : wardX0 ν μ R c g (τ + 2 * c / R) = wardX0 ν μ R c g τ :=
    funext (wardX0_periodic oldPhysPeriodic ν μ R c g τ)
  have key : wardStreamCut ν R χy (wardX0 ν μ R c g) (τ + 2 * c / R) =
      wardStreamCut ν R χy (wardX0 ν μ R c g) τ := by
    funext y'
    simp only [wardStreamCut, outPrim, hZ]
  simp only [wardXr, wardX, key]

theorem wardX0_axi_of (hS : SmoothOldSource) {ν μ R c : ℝ} {g : Chart → Ten3} (hν : 0 < ν)
    (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hg : IsSmoothOld c ν g) :
    AxiNoSwirlOn (youngOpen ν R) (wardX0 ν μ R c g) := by
  obtain ⟨hS1, hS2⟩ := hS ν R c g hν hR hc hg
  intro τ y hy hax
  have hyo : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
  have hro : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hm : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y) := by rw [varrho_meridPt]; exact hyo
  refine wardX0Axi_all ν μ R c g τ y hax ?_ ?_
  · exact sepIntegrableOfSource_all ν (μ : ℂ) _ _ _ hν (by simpa using hμ) hro hP hS1 hS2 τ _ hm
  · exact sepIntegrableOfSource_all ν ((μ : ℂ) + 1) _ _ _ hν (by simp; linarith) hro hP hS1 hS2
      τ _ hm

theorem wardXr_solenoidal_of (hS : SmoothOldSource) (h2 : WardX0SmoothInf)
    (h3 : WardX0DecayInf) (h7 : WardX0DivFree) {ν μ R c : ℝ} {χy : ℝ → ℝ} {g : Chart → Ten3}
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hχy : IsYoungCutoff χy)
    (hg : IsSmoothOld c ν g) (τ : ℝ) (y : Space) :
    ∑ j : Fin 3, physPd (wardXr ν μ R c χy g τ) j y j = 0 := by
  by_cases hy : y ∈ axis
  · have hs : IsOpen {y : Space | ϱ y < R * Real.sqrt ν} :=
      isOpen_lt (by unfold ϱ; fun_prop) continuous_const
    have hy' : y ∈ {y : Space | ϱ y < R * Real.sqrt ν} := by
      show ϱ y < R * Real.sqrt ν
      rw [(mem_axis_iff y).1 hy]
      positivity
    have hev : wardXr ν μ R c χy g τ =ᶠ[𝓝 y] (0 : Space → Space) := by
      filter_upwards [hs.mem_nhds hy'] with z hz
      refine wardXr_eq_zero_of_sq_le hχy g τ ?_
      have h0 : 0 ≤ ϱ z := Real.sqrt_nonneg _
      have hz' : ϱ z < R * Real.sqrt ν := hz
      have hsq : (R * Real.sqrt ν) ^ 2 = ν * R ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hν.le]
        ring
      nlinarith
    simp [physPd_congr_nhds hev, physPd_zero_fun]
  · have hev := wardXr_eventuallyEq (ν := ν) (μ := μ) (R := R) (c := c) (χy := χy) (g := g) τ hy
    simp only [physPd_congr_nhds hev]
    have hC : ContDiffOn ℝ 2 (wardX0 ν μ R c g τ) (youngOpen ν R) := by
      have := ((h2 ν μ R c g hν hR hc hμ hg).of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp
        (contDiff_prodMk_right τ).contDiffOn (fun y hy => hy)
      exact this
    have hD := h7 ν μ R c g hν hR hc hμ hg τ
    have hA := wardX0_axi_of hS hν hR hc hμ hg
    have hdec := h3 ν μ R c g hν hR hc hμ hg τ
    exact wardStreamCutDivFree_of ν R χy hχy hν hR (wardX0 ν μ R c g) τ hC hD hA
      (fun r z hr => ⟨outPrimDerivR ν R _ τ hC hdec r z hr,
        outPrimDerivZ ν R _ τ hC hD hA hdec r z hr⟩) y hy

/-- **`WardXrSmoothData` from the source facts** (source 4161-4186, 3604-3621). -/
theorem wardXrSmoothData_of (hS : SmoothOldSource) (h2 : WardX0SmoothInf)
    (h3 : WardX0DecayInf) (h7 : WardX0DivFree) (h4 : OutPrimSmoothInf)
    (h5 : WardXrSmoothOfParts) (h6 : WardXrAxiOfX0) : WardXrSmoothData := by
  intro ν μ R c χy hν hR hc hμ hχy g hg
  refine ⟨h5 ν μ R c χy g hν hR hχy (h2 ν μ R c g hν hR hc hμ hg)
    (h4 ν μ R c g hν hR hc hμ hg), wardXr_periodic_of ν μ R c χy g, ?_, ?_⟩
  · exact fun τ y => wardXr_solenoidal_of hS h2 h3 h7 hν hR hc hμ hχy hg τ y
  · exact h6 ν μ R c χy g hν hR hχy (wardX0_axi_of hS hν hR hc hμ hg)

end UnforcedLeray.Short.PartIIIb.Concrete
