import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.DivEpsReal

/-!
# Decomposition of `ChartConjSmooth` (source 1639-1675, 2681-2691, 3893-3906)

Source of record: `the November 2 reference manuscript`.

"The finite-curvature free inverse is the conjugate of the Cartesian weak-stress inverse. In
particular its divergence and pressure are not replaced by planar ones" (3893-3895).  With
`J_ε = B0223.liftVec` (the velocity lift `𝒩_v b = √s b` of 2682 times `(√(2π)ε)⁻¹`, in the outer
variables) and a smooth chart tensor test `m`, `G` a representative of `s div_ε m`:

`J_ε T_ε G = J_ε R_ε^vec P_ε G = (μ - A)^{-1} J_ε P_ε G` (`B0223.J_RepsVec`)
`= (μ - A)^{-1} P_3D J_ε G` (`P_ε` the conjugated Cartesian Leray projection, 1669:
`PepsCCplx` and `B0226.J_Peps`; `G` is real, `Masked.smul_divEps_im`)
`= (2π)^{-1/2}(μ - A)^{-1} P_3D div 𝒩_T m` (`DivLiftPoint`: the Cartesian differentiation of
1655-1665, `div(s m) = s^{3/2} div_ε m` with the hoop traction).

Leaf Props (each a self-contained true statement):
* `CartLiftIsTest` : `𝒩_T m = cartLift ε⁻¹ c m` is a smooth Cartesian tensor (1639-1650, 2666-2668).
* `CartTestDivMemLp` : the divergence of a smooth Cartesian tensor is in `L²(dx dτ)`.
* `PepsCCplx` : `PartIIa.PepsC` on complexified real fields is the complexified `B0226.Peps`.
* `LiftVecCplx` : `B0223.liftVec` on complexified real fields is the complexified `B0220.J`.
* `DivLiftPoint` : off the axis, `div_x 𝒩_T m = ε⁻¹ a³ (div_ε m)_r e_r + ε⁻¹ a³ (div_ε m)_z e_z`,
  `a = 1/r = √s` (1655-1665, chart 1639-1642).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-! ## Complexification of real meridional fields -/

/-- `merC` as a real-linear map `ℝ² → ℂ²`. -/
def merCLin : UnforcedLeray.B0220.Merid →ₗ[ℝ] UnforcedLeray.B0223.MeridC where
  toFun := merC
  map_add' u v := by
    ext i
    simp [merC]
  map_smul' a v := by
    ext i
    simp [merC]

/-- `merC` as a continuous real-linear map. -/
def merCL : UnforcedLeray.B0220.Merid →L[ℝ] UnforcedLeray.B0223.MeridC :=
  LinearMap.toContinuousLinearMap merCLin

theorem merCL_apply (b : UnforcedLeray.B0220.Merid) : merCL b = merC b := rfl

/-- The complexification `H(ℝ²) → H(ℂ²)` of real meridional fields. -/
def cplxH (c : ℝ) :
    UnforcedLeray.B0220.HSpace c UnforcedLeray.B0220.Merid →L[ℝ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC :=
  merCL.compLpL 2 (UnforcedLeray.B0220.measureH c)

/-- The real part `H(ℂ²) → H(ℝ²)`. -/
def reHC (c : ℝ) :
    UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC →L[ℝ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0220.Merid :=
  merReL.compLpL 2 (UnforcedLeray.B0220.measureH c)

theorem cplxH_ae (c : ℝ) (g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0220.Merid) :
    (cplxH c g : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
      =ᵐ[UnforcedLeray.B0220.measureH c] fun p => merC ((g : UnforcedLeray.B0220.Profile →
        UnforcedLeray.B0220.Merid) p) :=
  merCL.coeFn_compLpL g

theorem reHC_ae (c : ℝ) (G : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) :
    (reHC c G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0220.Merid)
      =ᵐ[UnforcedLeray.B0220.measureH c] fun p => merReL ((G : UnforcedLeray.B0220.Profile →
        UnforcedLeray.B0223.MeridC) p) :=
  merReL.coeFn_compLpL G

/-- A complex field with zero imaginary parts is the complexification of its real part. -/
theorem cplxH_reHC {c : ℝ} {G : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC}
    (h : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
      ∀ i, ((G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i).im = 0) :
    cplxH c (reHC c G) = G := by
  apply Lp.ext
  filter_upwards [cplxH_ae c (reHC c G), reHC_ae c G, h] with p h1 h2 h3
  rw [h1, h2, merC_merReL h3]

/-! ## The leaves -/

/-- **The tensor lift of a smooth test is a smooth Cartesian tensor** (source 1639-1650, 2666-2668,
2682): for `ε, c > 0`, `P = 2εc` and a chart tensor `m` whose components `tv4 ∘ m` form a smooth
tensor test (`PartIIa.IsTensorTest`: smooth, `c`-periodic in `q`, band support `s₀ ≤ s ≤ s₁`,
`|η| ≤ L`, `s₀ > 0`), `𝒩_T m = cartLift ε⁻¹ c m` is smooth in `(z, τ)` (the floor reduction of
`chartOf` is invisible to the `c`-periodic `m`; `cartLift` vanishes near the axis `s > s₁`),
`P`-periodic in `τ` (`R P/2 = c`), with bounded support (`ρ ≤ R/√s₀`, `|z₃| ≤ Lρ/R`). -/
def CartLiftIsTest : Prop :=
  ∀ (ε c P : ℝ), 0 < ε → 0 < c → P = 2 * ε * c → ∀ m : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)) →
      IsCartTest P (cartLift ε⁻¹ c m)

/-- **The divergence of a smooth Cartesian tensor is in `L²(dx dτ)`** over one period: the outer
field `T(τ, ε⁻¹x)` is smooth with bounded spatial support, so its divergence is continuous and
vanishes outside a compact set of `ℝ³ × [0, P]` (`B0226.memLp_of_continuous_of_ae_vanish`). -/
def CartTestDivMemLp : Prop :=
  ∀ (ε c P : ℝ), 0 < ε → 0 < c → P = 2 * ε * c →
    ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IsCartTest P T →
      MemLp (cartDiv (outerField ε⁻¹ T)) 2 (UnforcedLeray.B0220.physMeasure ε c)

/-- **`P_ε` on real fields** (source 1669, B0226 tex 3394-3402): the complex projection
`PartIIa.PepsC ε c` (onto the orthogonal complement of the complex span of the profile gradients
`(D_εΦ, ∂_ηΦ)`) acts on a complexified real field as the complexified real projection
`B0226.Peps` (`= (solenoidalH ε c).starProjection`, `B0226.Peps_eq_starProjection`): the
complexified real projection lies in the complex solenoidal subspace, and the complexified
remainder lies in the closure of the complex span of the gradients. -/
def PepsCCplx : Prop :=
  ∀ (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0220.Merid),
    UnforcedLeray.Short.PartIIa.PepsC ε c (cplxH c g) =
      cplxH c (UnforcedLeray.B0226.Peps hε hc g)

/-- **The complex lift on real fields** (B0223 `coeFn_liftVec`, B0220 `coeFn_J`): `B0223.liftVec`
of a complexified real field is the complexification of `B0220.J`, moved to the periodic space by
`B0223.toCell` (`toX`). -/
def LiftVecCplx : Prop :=
  ∀ (ε c P : ℝ) [Fact (0 < P)] (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0220.Merid),
    UnforcedLeray.B0223.liftVec hε hc hP (cplxH c g) = toX hP (UnforcedLeray.B0220.J hε hc g)

/-- **The Cartesian divergence of the tensor lift** (source 1655-1665: "Direct Cartesian
differentiation gives ... `(div_ε T)_r = Q_ε T_rr + ∂_η T_rz - ε T_φφ`,
`(div_ε T)_z = Q_ε T_zr + ∂_η T_zz`"; chart 1639-1642, lifts 2682): off the axis,
`div_x(𝒩_T m)(x, τ) = ε⁻¹ a³ [(div_ε m)_r e_r + (div_ε m)_z e_z]` at the chart point, `a = 1/r`
(`B0220.liftA`), `e_r, e_z` the frame `B0220.frame x`; `div_ε` of the components `tv4 ∘ m`
(`PartIIa.divEps`), real part, at the cell chart point `B0220.cellChart` (the same as at the
unreduced point by `c`-periodicity).  Derivation: `∂_r = (εr)⁻¹(∂_q - εK)`, `∂_{x₃} = (εr)⁻¹∂_η`,
`∂_r s = -2s/r`, and the cylindrical divergence `(div N)_r = ∂_rN_rr + ∂_zN_rz + (N_rr - N_φφ)/r`,
`(div N)_z = ∂_rN_rz + ∂_zN_zz + N_rz/r` of `N = s m`. -/
def DivLiftPoint : Prop :=
  ∀ (ε c : ℝ), 0 < ε → 0 < c → ∀ m : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)) →
    ∀ x : Space, UnforcedLeray.B0220.radius x ≠ 0 → ∀ τ : ℝ,
      cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m)) (x, τ) =
        (ε⁻¹ * UnforcedLeray.B0220.liftA x ^ 3) • UnforcedLeray.B0220.frame x
          (merReL (UnforcedLeray.Short.PartIIa.divEps ε (fun p => tv4 (m p))
            (UnforcedLeray.B0220.cellChart ε c (x, τ))))

/-! ## The assembly -/

theorem tv4_im (T : Ten3) (i : Fin 4) : (tv4 T i).im = 0 := by
  fin_cases i <;> simp [tv4]

theorem merReL_ofReal_smul (r : ℝ) (v : UnforcedLeray.B0223.MeridC) :
    merReL ((r : ℂ) • v) = r • merReL v := by
  ext i
  simp [merReL_apply]

/-- **`ChartConjSmooth` from the leaves.** -/
theorem chartConjSmooth_of (hC1 : CartLiftIsTest) (hC2 : CartTestDivMemLp) (hC3 : PepsCCplx)
    (hC4 : LiftVecCplx) (hC5 : DivLiftPoint) : ChartConjSmooth := by
  intro ν ε c P _ hν hε hc hP μ hμ m hm
  have hT := hC1 ε c P hε hc hP m hm
  have hM := hC2 ε c P hε hc hP _ hT
  refine ⟨hT, hM, fun G hG => ?_⟩
  -- `G` is real
  have hreal : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
      ∀ i, ((G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i).im = 0 := by
    filter_upwards [hG] with p hp i
    rw [hp]
    exact smul_divEps_im ε _ (fun p i => tv4_im (m p) i) p i
  set g := reHC c G with hgdef
  have hGg : G = cplxH c g := (cplxH_reHC hreal).symm
  have hgb : (g : UnforcedLeray.B0220.Profile → UnforcedLeray.B0220.Merid)
      =ᵐ[UnforcedLeray.B0220.measureH c] fun p =>
        merReL ((p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε (fun p => tv4 (m p)) p) := by
    filter_upwards [reHC_ae c G, hG] with p h1 h2
    rw [h1, h2]
  -- `J_ε g = (2π)^{-1/2} div 𝒩_T m`
  set k : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ with hk
  have hJae : (UnforcedLeray.B0220.J hε hc g : Space × ℝ → Space)
      =ᵐ[UnforcedLeray.B0220.physMeasure ε c]
        fun y => k • cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m)) y := by
    have h1 : (UnforcedLeray.B0220.J hε hc g : Space × ℝ → Space)
        =ᵐ[UnforcedLeray.B0220.physMeasure ε c]
          (UnforcedLeray.B0220.jComp hε hc).compFun g :=
      (UnforcedLeray.B0220.jComp hε hc).coeFn_toLI g
    have h2 := (UnforcedLeray.B0220.jComp hε hc).compFun_congr hgb
    filter_upwards [h1, h2, UnforcedLeray.B0220.ae_physMeasure ε c] with y hy1 hy2 hy3
    rw [hy1, hy2]
    obtain ⟨x, τ⟩ := y
    have hd := hC5 ε c hε hc m hm x hy3.1 τ
    simp only [UnforcedLeray.B0220.WeightedComp.compFun, UnforcedLeray.B0220.jComp,
      LinearMap.smul_apply]
    rw [hd, merReL_ofReal_smul, map_smul, smul_smul, smul_smul]
    congr 1
    have hs : (UnforcedLeray.B0220.cellChart ε c (x, τ)).1 = UnforcedLeray.B0220.liftA x ^ 2 :=
      (UnforcedLeray.B0220.liftA_sq x).symm
    rw [hs, hk]
    unfold UnforcedLeray.B0220.jConst
    rw [mul_inv]
    ring
  have hJ : UnforcedLeray.B0220.J hε hc g =
      k • hM.toLp (cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m))) := by
    apply Lp.ext
    filter_upwards [hJae, Lp.coeFn_smul k (hM.toLp (cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m)))),
      hM.coeFn_toLp] with y h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3]
  have hγ : 0 < μ.re + 1 / 4 := by linarith
  calc UnforcedLeray.B0223.liftVec hε hc hP (UnforcedLeray.Short.PartIIa.Teps hν hε hc hP μ G)
      = UnforcedLeray.B0223.liftVec hε hc hP (UnforcedLeray.B0223.RepsVec hν hε hc hP μ
          (UnforcedLeray.Short.PartIIa.PepsC ε c G)) := rfl
    _ = UnforcedLeray.B0223.physRes hν ε μ (UnforcedLeray.B0223.liftVec hε hc hP
          (UnforcedLeray.Short.PartIIa.PepsC ε c G)) :=
        UnforcedLeray.B0223.J_RepsVec hν hε hc hP hγ _
    _ = UnforcedLeray.B0223.physRes hν ε μ (toX hP (UnforcedLeray.B0226.P3D ε c
          (k • hM.toLp (cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m)))))) := by
        rw [hGg, hC3 ε c hε hc g, hC4 ε c P hε hc hP, UnforcedLeray.B0226.J_Peps hε hc, hJ]
    _ = (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) •
          CartStress hν hP μ (outerField ε⁻¹ (cartLift ε⁻¹ c m)) hM := by
        rw [map_smul, map_smul, ContinuousLinearMap.map_smul_of_tower, Complex.coe_smul]
        rfl

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
