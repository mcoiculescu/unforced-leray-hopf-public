import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub3

/-!
# Decomposition of `LiftFullOutTest` (source 1675, 1688-1689, 2681-2691, 3916-3921)

Source: `the November 2 reference manuscript`.

`LiftFullOutTest` is the conjunction of
* `FullOutMemH`: the chart field `merC (fullOut m (cellPt p))` of a box test has a representative in
  `H` (it is `fullOut` of a box tensor with `tv4 m` in `L²(s^{-1/2})`, bounded by `FullOutLip`
  with `g = 0`, transported by `CellPtH`/`CellPtHT` exactly as in `densityBox_of`);
* `LiftKernelIdentity`: for any such representative `G`, `liftVec G` is `(√(2π))⁻¹ · kernelField`
  (`B0223.coeFn_liftVec`, the chart `B0220.chart`, and the symmetry of `W_μ[𝒩_T m]`:
  rotation equivariance `SepWRotEquiv`, reality and absence of swirl `SepWRealNoSwirl`, 3586-3626).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- **Leaf A** (source 3916-3921, 1688-1689): the chart field of a box test lies in `H`. -/
def FullOutMemH : Prop :=
  ∀ (ν ε c : ℝ), 0 < ν → 0 < ε → 0 < c → ∀ (μ : ℝ), -(1 / 4) < μ → ∀ m : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)) → IsBoxTensor m →
    ∃ G : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
          =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => merC (fullOut ε⁻¹ c ν μ m (cellPt c p)))

/-- **Leaf B** (source 3916-3921, 2681-2691, 3586-3626): any representative `G` of the chart field
of a box test lifts to `(√(2π))⁻¹ · kernelField ν μ ε⁻¹ (cartLift ε⁻¹ c m)`. -/
def LiftKernelIdentity : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)], 0 < ν → ∀ (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (μ : ℝ), -(1 / 4) < μ → ∀ m : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)) → IsBoxTensor m →
    ∀ G : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
          =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => merC (fullOut ε⁻¹ c ν μ m (cellPt c p))) →
        (UnforcedLeray.B0223.liftVec hε hc hP G :
            UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
          (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) • kernelField ν (μ : ℂ) ε⁻¹ (cartLift ε⁻¹ c m)

theorem liftFullOutTest_of (h1 : FullOutMemH) (h2 : LiftKernelIdentity) : LiftFullOutTest := by
  intro ν ε c P _ hν hε hc hP μ hμ m hm hbox
  obtain ⟨G, hG⟩ := h1 ν ε c hν hε hc μ hμ m hm hbox
  exact ⟨G, hG, h2 ν ε c P hν hε hc hP μ hμ m hm hbox G hG⟩

/-- **Rotation equivariance of `W_μ`** (source 3586-3626, 2683), for `μ > -1/4` (3611-3621; for
smaller `μ` the `l`-integral of `l^(2μ+2)` need not converge and the Bochner junk value breaks the
component mixing): for the axisymmetric tensor
`cartLift R c m` (`T(τ, Qz) = Q T(τ, z) Qᵀ` for rotations `Q` about the vertical axis, since
`chartOf`, `hRad` are rotation invariant and `cylFrame (Qz) = Q cylFrame z`) and the rotation
invariance of `heatLerayK` (`K(Qx) = Q K(x) Qᵀ`), `W_μ(y) = cylFrame(y) · W_μ(ϱ, 0, y₃)`. -/
def SepWRotEquiv : Prop :=
  ∀ (ν R c μ : ℝ), 0 < ν → 0 < R → 0 < c → -(1 / 4 : ℝ) < μ → ∀ m : Chart → Ten3,
    IsBoxTensor m → ∀ (τ : ℝ) (y : Space),
    0 < hRad y →
      UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (cartLift R c m) y τ =
        fun i => ∑ j : Fin 3, ((cylFrame y i j : ℝ) : ℂ) *
          UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (cartLift R c m)
            (WithLp.toLp 2 ![hRad y, 0, y 2]) τ j

/-- **Reality and absence of swirl** (source 3586-3626): for real `μ` the response `W_μ[𝒩_T m]` of
the axisymmetric no-swirl tensor is real and, at azimuth `0` (`y₂ = 0`, `y₁ > 0`), has vanishing
`y₂`-component (reflection `y₂ ↦ -y₂` leaves `cartLift` and `heatLerayK` equivariant). -/
def SepWRealNoSwirl : Prop :=
  ∀ (ν R c μ : ℝ), 0 < ν → 0 < R → 0 < c → ∀ m : Chart → Ten3, IsBoxTensor m → ∀ (τ : ℝ) (ρ z : ℝ),
    0 < ρ →
      (∀ i : Fin 3, (UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (cartLift R c m)
          (WithLp.toLp 2 ![ρ, 0, z]) τ i).im = 0) ∧
        UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (cartLift R c m)
          (WithLp.toLp 2 ![ρ, 0, z]) τ 1 = 0

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
