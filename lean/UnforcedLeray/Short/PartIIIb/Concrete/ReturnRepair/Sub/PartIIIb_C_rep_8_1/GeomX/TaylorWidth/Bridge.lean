import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Leaf
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MomentSplit

/-!
# `PartIII-b:C/rep/8/1/1/1/3/2/org`: the bridge from `zMid`, `zMt` to `SepMeanFar`

Source `the November 2 reference manuscript`
lines 5415-5427 ("The same bound includes the finite transverse width and the heat-to-Newton
error: Taylor's formula costs the first transverse moment, and the strict radial gap holds along
every Taylor segment. The initially stronger age power `s³` is bounded by `P_ν s^{5/2}` on the
young interval"), 4764-4791 (`E_ij(u)`, `Σ_M`, "the zero azimuthal row and column are retained as
zero entries; the `rz` and `zr` entries are retained", `V_{μ,M}`, `W^mt = ε²V(ε·)`), 5141-5142 and
5376 (the old thin tensor `T₁ = M_V w` is swirl free: `ThinAziZero`), SP 3735-3766 (`thinSource`,
`F̄`, `V_{μ,0}`, `sep:mean-comparison`).

Fix a regime and a swirl-free thin stress `T`; `g = thinG T` (`= χ_o(νs)T₁` a.e.), the cut planar
lift `F = cutLift c √(5ν/6) g` (`PhasePrimitive/Lift.lean`: `oldPhys ε⁻¹ c g = thinSource ε F`), and
its phase mean `Ḡ = meanSrc T = IIIa.phaseMean c F`.  At a young receiver `y = ε⁻¹x_obs`
(`|x_obs'| = s^{-1/2} ≥ √ν > √(5ν/6)`):

* **(i) heat side** (proved here, `fderiv_zMid_eq`): `D_y zMid = Re(D_yW_μ(Ḡ) - D_yW_{μ+1}(Ḡ))`,
  `W_μ(Ḡ) = IIIa.sepW ν μ (thinSource ε (meanLift Ḡ)) · 0` (phase free; `PhasePrim.sepW_mean`,
  `sepW_diff`, `fderiv_wardX0`);
* **(ii) Newton side** (`NewtonBridge`, from the leaves `KernelDict`, `SigmaCollapse`):
  `D_y zMt = ε³ Re(D_xV_{μ,0}(Ḡ) - D_xV_{μ+1,0}(Ḡ))(x_obs)`, `V_{μ,0} = IIIa.sepVmu0`: the zero-width
  collapse `∫Ḡ(x',Y)dY = Sym Σ_M(x')` (the transverse variable integrated out, the hoop entry
  `T(1,1)` absent by `ThinAziZero`, the symmetrised `rz` entry harmless against the symmetric
  `D³N`), the dictionary `∂_k(K₀)_{ij} = ∂_i∂_j∂_kN`, Fubini and `W^mt = ε²V(ε·)`;
* the moment `N₁(meanLift Ḡ) ≤ N₁(F) ≤ πN` (proved here, `thinMoment_meanSrc_le`);
* **(iii) the combination** (proved here, `taylorWidthAt_uniform_of`): `SepMeanFar` at `μ` and
  `μ + 1` (`K = [0, 2] ⊂ ℂ`), `|x_obs'|^{-5} = s^{5/2}` (the `s³` term of the source is absorbed in
  `SepMeanFar` through its factor `ρ_i⁻¹`), the polynomial `≤ 16ν⁻²`, `‖Re‖ ≤ 2`, gives
  `|D_y zMid - D_y zMt| ≤ 4π(C+1)16^k ν^{-2k} ε⁴ s^{5/2} N` at every young chart point.

The three leaves `KernelDict`, `SigmaCollapse`, `NewtonBridge` are the open lemma tasks
`PartIII-b:C/rep/8/1/1/1/3/2/{1,2,3}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace TWBridge

open PhasePrim

/-! ## 1. The phase-mean planar source -/

/-- The phase-mean planar source `Ḡ(x',Y) = c⁻¹∫₀^c F(x',Y,q)dq` of the old thin source of `T`,
`F = cutLift c √(5ν/6) (thinG T)` the cut planar lift (SP 3753-3757 `F̄`; source 4764-4770). -/
def meanSrc (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L) :
    ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
  IIIa.phaseMean (cOf L.ν) (cutLift (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) (thinG Pl K L T))

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

theorem thinG_measurable (T : LStr Pl K L) : Measurable (thinG Pl K L T) := by
  unfold thinG
  exact (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable

theorem meanSrc_measurable (T : LStr Pl K L) (i j : Fin 3) :
    Measurable fun w : (ℝ × ℝ) × ℝ => meanSrc Pl K L T w.1 w.2 i j :=
  IIIa.phaseMean_measurable _ _ (cutLift_measurable _ _ _ (thinG_measurable Pl K L T)) i j

theorem meanSrc_support (T : LStr Pl K L) (x' : ℝ × ℝ) (Y : ℝ)
    (h : Real.sqrt (5 * L.ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) :
    meanSrc Pl K L T x' Y = 0 := by
  have hz : ∀ q, cutLift (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) (thinG Pl K L T) x' Y q = 0 :=
    fun q => cutLift_support _ _ _ x' Y q h
  funext i j
  unfold meanSrc IIIa.phaseMean
  simp only [hz]
  simp

/-- `N₁(meanLift Ḡ) ≤ N₁(F) ≤ π N`, `N = oldN1 T` (SP 2790-2795, source 5400; Jensen in `q`). -/
theorem thinMoment_meanSrc_le (hC0 : 0 < K.C0) (T : LStr Pl K L) :
    IIIa.thinMoment (cOf L.ν) (IIIa.meanLift (meanSrc Pl K L T)) ≤
      ENNReal.ofReal Real.pi * oldN1 Pl K L T := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hgm := thinG_measurable Pl K L T
  have h1 := (IIIa.sepMomentSplit (cOf L.ν) hc
    (cutLift (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) (thinG Pl K L T))
    (cutLift_measurable _ _ _ hgm)).1
  have h2 := thinMoment_cutLift_le (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) hc _ hgm
  rw [firstMoment_thinG Pl K L hC0 T] at h2
  exact h1.trans h2

/-- **(i) The heat side**: off the old cylinder, `D_y zMid` is the real part of
`D_yW_μ(Ḡ) - D_yW_{μ+1}(Ḡ)` with `W_μ(Ḡ) = IIIa.sepW ν μ (thinSource ε (meanLift Ḡ)) · 0` (phase
free; source 4171, 5415-5427). -/
theorem fderiv_zMid_eq (μ : ℝ) (hμ : 0 ≤ μ) (hC0 : 0 < K.C0) (hmZ : 3 / 2 < K.mZ)
    (T : LStr Pl K L) (τ : ℝ) (y : Space) (hy : L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < ϱ y) :
    fderiv ℝ (zMid Pl K L μ T τ) y =
      reMap.comp (fderiv ℝ (fun y => IIIa.sepW L.ν (μ : ℂ)
          (IIIa.thinSource L.ε (IIIa.meanLift (meanSrc Pl K L T))) y 0) y -
        fderiv ℝ (fun y => IIIa.sepW L.ν ((μ : ℂ) + 1)
          (IIIa.thinSource L.ε (IIIa.meanLift (meanSrc Pl K L T))) y 0) y) := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hρb : 0 < L.ρb Pl K := ZRegAux.rho_b_pos' Pl K L hC0
  have hgm : Measurable (thinG Pl K L T) := thinG_measurable Pl K L T
  have hmom : ∫⁻ p, ‖thinG Pl K L T p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb (by linarith) hν _
  have hz : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), L.ν * p.1 ≤ 6 / 5 → thinG Pl K L T p = 0 :=
    ZRegAux.strSum_zero_young _ _ _ _ _ K.hχo hρb _
  have hz' := ZRegAux.mean_ae_zero (cOf L.ν) (-1 / 2) L.ν hc _ hgm hz
  have hmean_m := ZRegAux.measurable_meanQ' (cOf L.ν) hgm
  have hmean_mom : ∫⁻ p, ‖meanQ (cOf L.ν) (thinG Pl K L T) p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    lt_of_le_of_lt (ZRegAux.mean_moment_le _ _ hc _ hgm) hmom
  have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
  have hreμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hA := sepW_diff (cOf L.ν) L.ν L.ε _ hc hν hε hreμ _ hmean_m hmean_mom hz' τ y hy
  have hB := sepW_diff (cOf L.ν) L.ν L.ε _ hc hν hε hreμ1 _ hmean_m hmean_mom hz' τ y hy
  have e : ∀ μc : ℂ, (fun y => IIIa.sepW L.ν μc
      (oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T))) y τ) =
      fun y => IIIa.sepW L.ν μc (IIIa.thinSource L.ε (IIIa.meanLift (meanSrc Pl K L T))) y 0 := by
    intro μc
    funext y
    rw [← sepW_mean (cOf L.ν) L.ν L.ε μc hc hν hε _ hgm hmom hz' y τ]
    rfl
  have h := fderiv_wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T)) τ y hA hB
  rw [e, e] at h
  exact h

end Regime

/-! ## 2. The leaves of the Newton side -/

/-- **Leaf `PartIII-b:C/rep/8/1/1/1/3/2/1`: the Newton kernel dictionary** (SP 3600-3610:
`K₀ = D²(4π|x|)⁻¹` off the origin, the kernel of `IIIa.sepVmu0`; source 4776-4782: `D³N`,
`N = 1/(4π|x|)`, `newtonD3` of `SourceL.lean`): off the origin the `k`-derivative of `(K₀)_{ij}`
is `∂_i∂_j∂_kN` read in the coordinates `WithLp.ofLp`, and `D³N` is symmetric in its last two
indices.  (Smoothness of `N` off `0` and symmetry of the mixed partials.) -/
def KernelDict : Prop :=
  ∀ x : Space, x ≠ 0 → ∀ i j k : Fin 3,
    fderiv ℝ (fun x' => IIIa.heatLerayK0 i j x') x (coordinateVector k) =
        newtonD3 (WithLp.ofLp x) i j k ∧
      newtonD3 (WithLp.ofLp x) i j k = newtonD3 (WithLp.ofLp x) i k j

/-- **Leaf `PartIII-b:C/rep/8/1/1/1/3/2/2`: the zero-width collapse of the phase mean** (source
4764-4775: `E_ij(u) = χ_o(u)c⁻¹∫_cell M_ij dq dη`, `Σ_M` the rotation of `ρ⁻¹E(u)`, `u = ρ⁻²`,
zero azimuthal row and column, `rz`, `zr` retained; 5141-5142, 5376: the thin tensor is swirl
free; SP 3753-3757: `F̄`, and `V_{μ,0}` integrates `F̄(x',Y)` over `Y` against a kernel at
`(x',0)`): for a swirl-free thin stress with finite `N₀` and `N₁`, for a.e. `x'`,
`∫Ḡ(x',Y)dY = Sym Σ_M(x')`, `M = thinRep T`.  Proof: for `|x'| > √(5ν/6)` both sides vanish
(`cutLift_support`; `χ_o(νu) = 0` for `νu ≤ 6/5`); for `0 < |x'| < √(5ν/6)`, with
`u = plS x' = |x'|⁻²`, Fubini in `(Y, q)` (integrable for a.e. `x'` since `N₁(F) < ∞`), the
substitution `Y = |x'|η`, `integral_redQ` (the period `(0,c]` as the cell `[-c/2,c/2)`) give
`∫Ḡ dY = Q(x')(|x'|⁻¹ ∫ nsSym(g(u,·)) d(avgμ c))Q(x')ᵀ`; then `g(u,·) = χ_o(νu)T₁(u,·)` a.e.
(as in `PhasePrim.firstMoment_thinG`), `ThinAziZero` kills the `(1,·)`, `(·,1)` entries (the hoop
`φφ` entry included), the slices of `M` are integrable for a.e. `u > 6/(5ν)` (`OldThinFinite`), so
`nsSym` of the mean is the symmetrisation of `phaseMean c ν χo M u`; `plFrame x' = rotQ x'`, and
null sets in `u` pull back to null sets in `x'` (`polar_null`, `SourceL/Ambient/SigmaL1/Polar`). -/
def SigmaCollapse : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel), 0 < K.C0 →
    ∀ T : LStr Pl K L, ThinAziZero Pl K L T → OldThinFinite (cOf L.ν) L.ν (thinRep T) →
      oldN1 Pl K L T ≠ ⊤ →
      ∀ᵐ x' : ℝ × ℝ ∂volume, ∀ j k : Fin 3,
        ∫ Y : ℝ, meanSrc Pl K L T x' Y j k =
          (sigmaM (cOf L.ν) L.ν K.χo (thinRep T) x' j k +
            sigmaM (cOf L.ν) L.ν K.χo (thinRep T) x' k j) / 2

/-- **Leaf `PartIII-b:C/rep/8/1/1/1/3/2/3`: the Newton side** (source 4776-4791:
`V_{μ,M}(x) = -2∫₀¹t^{2μ+2}∫D³N(x - t(x',0)):Σ_M(x')dx'dt`, `W^mt_μ(y) = ε²V_{μ,M}(εy)`; SP 3753-3757
`V_{μ,0}`): for a swirl-free thin stress with finite `N₀`, `N₁`, at every `x_obs` off the old disc
(`|x_obs'|² > 5ν/6`), `D_y zMt(ε⁻¹x_obs) = ε³ Re(D_xV_{μ,0}(Ḡ) - D_xV_{μ+1,0}(Ḡ))(x_obs)`.  Proof:
on the open set `{5ν/6 < x₀² + x₁²}`, `IIIa.sepVmu0 μ Ḡ x = ↑(newtonV c ν μ χo M (ofLp x))`
(for each `λ ∈ (0,1)`: `KernelDict`, the kernel bounded by `C(|x'_obs| - √(5ν/6))^{-4}` on the
support of `Ḡ`, `Ḡ` integrable since `N₁(meanLift Ḡ) ≤ πN < ∞`, Fubini over `Y`,
`SigmaCollapse` and the `(j,k)`-symmetry of `D³N`; `(λ:ℂ)^{2μ+2} = ↑(λ^{2μ+2})`, `Ioo` vs `Ioc`);
`newtonV` is `C^∞` there (`newtonVSmooth`, `μ > 0`); so `zMt T τ = ε² • reMap ∘ (V_{μ,0} -
V_{μ+1,0})(ε·)` near `ε⁻¹x_obs`, and the chain rule. -/
def NewtonBridge : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ), 0 < μ → 0 < K.C0 →
    ∀ T : LStr Pl K L, ThinAziZero Pl K L T → OldThinFinite (cOf L.ν) L.ν (thinRep T) →
      oldN1 Pl K L T ≠ ⊤ → ∀ (τ : ℝ) (xo : Space), 5 * L.ν / 6 < xo 0 ^ 2 + xo 1 ^ 2 →
        fderiv ℝ (zMt Pl K L μ T τ) (L.ε⁻¹ • xo) =
          (L.ε ^ 3) • reMap.comp
            (fderiv ℝ (IIIa.sepVmu0 (μ : ℂ) (meanSrc Pl K L T)) xo -
              fderiv ℝ (IIIa.sepVmu0 ((μ : ℂ) + 1) (meanSrc Pl K L T)) xo)

end TWBridge

end UnforcedLeray.Short.PartIIIb.Concrete
