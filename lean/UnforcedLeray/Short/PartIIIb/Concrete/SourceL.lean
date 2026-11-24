import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps
import UnforcedLeray.Short.PartIIIb.Concrete.YoungFlat

/-!
# The complete old-thin-to-young-jet map `𝓛` and the flat-return data (source 4753-4815, 4917-4937)

Source of record: `the November 2 reference manuscript`.

Pointwise objects (style of `Concrete/ReturnAff.lean`), for an old thin tensor
`M : Chart → Mat3` (age `u`, cell coordinates `(q, η)`, components `(r, φ, z)`):

* `phaseMean` : `E_ij(u) = χ_o(u)/c ∫_cell M_ij(u,q,η) dq dη` (4766-4770), `χ_o(u) = χ̂_o(νu)`;
  the azimuthal row and column are entered as zeros (4773-4774);
* `sigmaM` : `Σ_M(x')`, the Cartesian rotation of `ρ⁻¹ E(u)`, `u = ρ⁻²`, on `x₃ = 0` (4771-4775);
* `newtonN`, `newtonD3`, `newtonV` : `N = 1/(4π|x|)` and the zero-width Newton field
  `V_{μ,M}(x) = -2∫₀¹ t^{2μ+2} ∫_{ℝ²} D³N(x - t(x',0)) : Σ_M(x') dx' dt` (4776-4782);
* `youngW`, `chiYr`, `streamPsi`, `streamCut`, `Xmt` : `W^mt(y) = ε²V(εy)`, the stream cutoff
  `χ_y` (4161-4166, 4755-4757), the outward primitive `Ψ_Z` and
  `𝒞_y Z = χ_y Z + (χ_y'/r) Ψ_Z e_z` (4178-4186), `X^mt = 𝒞_y(W^mt_μ - W^mt_{μ+1})` (4783-4791);
* `Lpt` : `(𝓛M)(s) = D_y X^mt(R/√s, 0, 0)` in the `(r,φ,z)` frame (4792-4796), `R = ε⁻¹`;
* `thinRep`, `LjFun` : `𝓛` on the concrete stress space `StrG` through the a.e. representative of
  the thin (`Z_1`) component (4930-4937: "This estimate uses only the thin component");
* `aMuFun`, `LamFun`, `frakT`, `KflatFun` : `a_μ`, `Λ_{μ,ν}`, `𝔗_{μ,ν}`, `𝒦^flat = 𝓛𝔗`
  (4761-4763, 4804-4815);
* `IsSourceLPinned` : the fields `Lj, aMu, Lam, Kflat` of a `ReturnBase` are these objects.

Facts of 4797-4803 and 4917-4937 (as Props, proved downstream): on the stress space
`SourceLSmooth`, `SourceLTraceFree`, `SourceLAzimuthal`, `SourceLYoung`, `SourceLLinear`,
`SourceLN0`, `AMuInAff`; for arbitrary old tensors with finite `N₀` (`OldThinFinite`)
`SourceLAmbient` and the receiver-level facts `XmtSmooth`, `XmtSolenoidal`, `XmtLinear`,
`XmtCongr`, `XmtReflect`; and `OldMeasureAC`.  Proved here: `sourceLInAff_of` (membership in `𝒜`),
`sourceLBounded_of` (`‖𝓛T‖_𝒜 ≤ P_ν ε³ e^{γ/ν} ‖T‖`), `ay_LjFun_of` (`χ_f 𝓛T = 𝓛T`),
`isStreamCutoff_std`.

Conventions.  Points of `ℝ³` are `Vec3 = Fin 3 → ℝ`; the Euclidean length is written out
(`√(Σ xᵢ²)`), since the norm of `Fin 3 → ℝ` is the sup norm.  At the receiver `(r, 0, 0)`, `r > 0`,
the frame `(e_r, e_φ, e_z)` is the Cartesian frame, so the `(r,φ,z)` components of `D_y X` are
its Cartesian Jacobian entries `(D_y X)_{ij} = ∂_j X_i` (the convention of `Concrete/ReturnAff.lean`,
where `A` acts as `DU`).  `𝓛M` is set to zero for `s ≤ 0` (`IsAffElem.zeroOff`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The stream cutoff and the standing hypotheses -/

/-- The stream cutoff profile `χ̂_y` (source 4161-4166, 4755-4757): `χ_y(s) = χ̂_y(νs)` equals one
for `s ≤ 4/(5ν)` and vanishes for `s ≥ 1/ν`; `C^∞` (`(⊤ : ℕ∞)`, not the analytic `ω`). -/
structure IsStreamCutoff (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  one : ∀ t, t ≤ 4 / 5 → χ t = 1
  zero : ∀ t, 1 ≤ t → χ t = 0
  range : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1

/-- A standard stream cutoff profile, `t ↦ smoothTransition (5 - 5t)`. -/
def streamCutoffStd (t : ℝ) : ℝ := Real.smoothTransition (5 - 5 * t)

/-- `IsStreamCutoff` is satisfiable. -/
theorem isStreamCutoff_std : IsStreamCutoff streamCutoffStd where
  smooth := Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul contDiff_id))
  one t ht := Real.smoothTransition.one_of_one_le (by linarith)
  zero t ht := Real.smoothTransition.zero_of_nonpos (by linarith)
  range t := ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- Standing hypotheses of the source map (source 4753-4757, 4161-4166, 4557): cell size `c > 0`,
`0 < ν ≤ 1`, `ε = R⁻¹ > 0`, `μ ∈ (0, 1/4)`, the outward cutoff `χ̂_o` and the stream cutoff
`χ̂_y`. -/
structure LHyp (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) : Prop where
  c_pos : 0 < c
  nu_pos : 0 < ν
  nu_le : ν ≤ 1
  eps_pos : 0 < ε
  mu_pos : 0 < μ
  mu_lt : μ < 1 / 4
  chiO : IsOutwardCutoff χo
  chiY : IsStreamCutoff χy

/-! ## 2. The phase-mean old tensor and its Cartesian source (source 4764-4775) -/

/-- The normalized phase mean `E_ij(u) = χ_o(u)/c ∫_cell M_ij(u,q,η) dq dη` (source 4766-4770),
`χ_o(u) = χ̂_o(νu)`, with `Cyl.avgμ c = c⁻¹ dq dη` on the cell.  The azimuthal (`φ = 1`) row and
column are entered as zeros (source 4773-4774: "The zero azimuthal row and column are retained as
zero entries"; a physical old tensor `M_U w` with swirl-free `U, w` has them zero, 5141-5142). -/
def phaseMean (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (u : ℝ) : Mat3 :=
  fun i j => if i = 1 ∨ j = 1 then 0 else χo (ν * u) * ∫ x, M (u, x) i j ∂(Cyl.avgμ c)

/-- The rotation `Q(φ)` with columns `e_r = (cos φ, sin φ, 0)`, `e_φ = (-sin φ, cos φ, 0)`,
`e_z = (0,0,1)` at `x' = (ρ cos φ, ρ sin φ)`. -/
def rotQ (x' : ℝ × ℝ) : Mat3 :=
  let ρ := Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)
  ![![x'.1 / ρ, -(x'.2 / ρ), 0], ![x'.2 / ρ, x'.1 / ρ, 0], ![0, 0, 1]]

/-- `Σ_M(x') = Q(φ) (ρ⁻¹ E(u)) Q(φ)ᵀ`, `ρ = |x'|`, `u = ρ⁻²`: the Cartesian rotation of the
cylindrical tensor `ρ⁻¹E(u)`, embedded on `x₃ = 0`; the `rz`, `zr` entries are kept
(source 4771-4775). -/
def sigmaM (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (x' : ℝ × ℝ) : Mat3 :=
  fun a b => ∑ i, ∑ j, rotQ x' a i *
    ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i j) *
      rotQ x' b j

/-! ## 3. The zero-width Newton field (source 4776-4782) -/

/-- The Newton kernel `N(x) = 1/(4π|x|)`. -/
def newtonN (x : Vec3) : ℝ := 1 / (4 * Real.pi * Real.sqrt (∑ i, x i ^ 2))

/-- `∂_i ∂_j ∂_k N(x)`. -/
def newtonD3 (x : Vec3) (i j k : Fin 3) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ newtonN z (Pi.single k 1)) y
    (Pi.single j 1)) x (Pi.single i 1)

/-- The embedding `x' ↦ (x', 0)` of the plane `x₃ = 0`. -/
def embPlane (x' : ℝ × ℝ) : Vec3 := ![x'.1, x'.2, 0]

/-- The exact zero-width Newton field (source 4776-4782):
`V_{μ,M}(x)_i = -2 ∫₀¹ t^{2μ+2} ∫_{ℝ²} Σ_{j,k} ∂_i∂_j∂_k N(x - t(x',0)) Σ_M(x')_{jk} dx' dt`.
The free index is the gradient index of `∇K₀`, `K₀ = D²N` (velocity contraction, 4780-4782). -/
def newtonV (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (x : Vec3) : Vec3 :=
  fun i => -2 * ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * μ + 2) *
    ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo M x' j k

/-! ## 4. The young field and its outward stream cutoff (source 4178-4186, 4783-4791) -/

/-- `W^mt_{μ,M}(y) = ε² V_{μ,M}(εy)` (source 4784). -/
def youngW (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : Vec3) : Vec3 :=
  ε ^ 2 • newtonV c ν μ χo M (ε • y)

/-- The cylindrical radius `r = |y'|`. -/
def cylR (y : Vec3) : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)

/-- The stream cutoff as a function of `r = |y'|`: `χ_y = χ̂_y(ν s)`, `s = R²/r² = 1/(εr)²`
(source 4161-4166); it vanishes on the old region `r ≤ R√ν`, in particular on the axis. -/
def chiYr (ν ε : ℝ) (χy : ℝ → ℝ) (r : ℝ) : ℝ := if r = 0 then 0 else χy (ν / (ε * r) ^ 2)

/-- The point at radius `ρ` on the outward ray through `y` (same azimuth, same height). -/
def rayPt (y : Vec3) (ρ : ℝ) : Vec3 := ![ρ * (y 0 / cylR y), ρ * (y 1 / cylR y), y 2]

/-- The outward primitive `Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,z) dρ` (source 4180-4182), along the outward
ray through `y`. -/
def streamPsi (Z : Vec3 → Vec3) (y : Vec3) : ℝ := -∫ ρ in Ioi (cylR y), ρ * Z (rayPt y ρ) 2

/-- The stream cutoff `𝒞_y Z = χ_y Z + (χ_y'/r) Ψ_Z e_z` (source 4182-4183), `χ_y' = ∂_r χ_y`. -/
def streamCut (ν ε : ℝ) (χy : ℝ → ℝ) (Z : Vec3 → Vec3) (y : Vec3) : Vec3 :=
  chiYr ν ε χy (cylR y) • Z y +
    (deriv (chiYr ν ε χy) (cylR y) / cylR y * streamPsi Z y) • (![0, 0, 1] : Vec3)

/-- `X^mt_{μ,M} = 𝒞_{χ_y}(W^mt_{μ,M} - W^mt_{μ+1,M})`, the same tensor `M` in the shifted field
(source 4785-4791). -/
def Xmt (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) : Vec3 → Vec3 :=
  streamCut ν ε χy (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)

/-! ## 5. The map `𝓛` (source 4792-4796) -/

/-- `(𝓛_{μ,ν}M)(s) = D_y X^mt_{μ,M}(R/√s, 0, 0)` in the `(r,φ,z)` frame, `R = ε⁻¹`
(`source-class:L`, 4792-4796), with `(D_y X)_{ij} = ∂_j X_i`; zero for `s ≤ 0`. -/
def Lpt (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (s : ℝ) : Mat3 :=
  if 0 < s then
    fun i j => fderiv ℝ (Xmt c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i
  else 0

theorem Lpt_of_nonpos (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) {s : ℝ} (hs : s ≤ 0) :
    Lpt c ν ε μ χo χy M s = 0 := by
  unfold Lpt
  rw [if_neg (not_lt.2 hs)]

/-- The a.e. representative of the thin (`Z_1`) component of a stress `T ∈ StrG`, as a matrix
field. -/
def thinRep {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) : Chart → Mat3 :=
  fun p => Ten3.toMatrix ((WithLp.ofLp T).1 p)

/-- `𝓛T` for a stress of the concrete space: `𝓛` applied to its thin component (source 4792-4796,
4930-4937). -/
def LjFun (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) (T : StrG c mZ ρb γ ν) : ℝ → Mat3 :=
  Lpt c ν ε μ χo χy (thinRep T)

/-! ## 6. Unit displacement, real row and flat return (source 4761-4763, 4804-4815) -/

/-- The unit displacement `a_μ(s) = s^{5/2}/(μ+5/2) D₀`, `D₀ = diag(12,-3,-9)` (source 4807-4811);
zero for `s ≤ 0`. -/
def aMuFun (μ : ℝ) (s : ℝ) : Mat3 :=
  if 0 < s then (s ^ (5 / 2 : ℝ) / (μ + 5 / 2)) • (fun i j => Dzero i j) else 0

/-- The real row `Λ_{μ,ν}(A) = -(3π/16) ε³ ν^{5+2μ} Re[i N_ν J(μ) a₀(B_{μ,ν}[A])]`
(source 4812-4815), `B_{μ,ν}[A] = (A^y)' + μA^y/s` (`Bmat`, 4757-4758), `a₀` the limiting
amplitude (`aZero`, 4614-4618) with `ell = ℓ₊(H₀)`. -/
def LamFun (lam κ ell : ℂ) (J : ℂ → ℂ) (ε ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : ℝ :=
  -(3 * Real.pi / 16) * ε ^ 3 * ν ^ (5 + 2 * μ) *
    (Complex.I * Nnu lam κ ν * J (μ : ℂ) * aZero lam ell (μ : ℂ) (Bmat ν μ χf A)).re

/-- `𝔗_{μ,ν}A`: the complete flat stress of the zero-entrance forced column with Gaussian age
force `f_{B_{μ,ν}[A]}` (source 4761-4763), i.e. the stress readout `M_B = v ⊗ K_cξ_B + K_cξ_B ⊗ v`
of the Duhamel state `ξ_B` of the flat setting `S` (`Concrete/YoungFlat.lean`, 4605-4610). -/
def frakT (S : ConcreteYF.FlatSetting) (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Mat3 :=
  fun p => S.Mcell p.1 (S.xi (μ : ℂ) (Bmat ν μ χf A) p.1) p.2

/-- The fixed-space flat return `𝒦^flat_{μ,ν} = 𝓛_{μ,ν} 𝔗_{μ,ν}` (source 4804-4806). -/
def KflatFun (S : ConcreteYF.FlatSetting) (c ν ε μ : ℝ) (χo χy χf : ℝ → ℝ) (A : ℝ → Mat3) :
    ℝ → Mat3 :=
  Lpt c ν ε μ χo χy (frakT S ν μ χf A)

/-! ## 7. The pin -/

/-- The fields `Lj`, `aMu`, `Lam`, `Kflat` of a concrete `ReturnBase` are the source objects
(source 4792-4815), read through the inclusion `ι : 𝒜 → (ℝ → Mat3)`: `𝓛T = LjFun T`,
`a_μ = aMuFun μ`, `Λ(A) = LamFun (ι A)`, `𝒦^flat A = 𝓛(𝔗(ι A))`.  `S` is the flat setting
carrying `𝔗`; `χo, χy, χf` are the outward, stream and source cutoff profiles. -/
def IsSourceLPinned {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (ι : Aff →ₗ[ℝ] (ℝ → Mat3))
    (S : ConcreteYF.FlatSetting) (lam κ ell : ℂ) (J : ℂ → ℂ) (ε μ : ℝ) (χo χy χf : ℝ → ℝ) :
    Prop :=
  (∀ T, ι (B.Lj T) = LjFun c mZ ρb γ ν ε μ χo χy T) ∧
  ι B.aMu = aMuFun μ ∧
  (∀ A, B.Lam A = LamFun lam κ ell J ε ν μ χf (ι A)) ∧
  (∀ A, ι (B.Kflat A) = KflatFun S c ν ε μ χo χy χf (ι A))

/-! ## 8. The old moment and the receiver-level facts (source 4766-4791, 4917-4937) -/

/-- The old moment `N₀(M) = ∫_{1.2/ν}^∞ u^{-3/2} (1/c)∫_cell |M| dq dη du` (source 4924-4927). -/
def oldN0 (c ν : ℝ) (M : Chart → Mat3) : ℝ :=
  ∫ u in Ioi (6 / 5 / ν), u ^ (-(3 / 2 : ℝ)) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)

/-- The measure `du × dq/c dη` on the old region `u > 1.2/ν`, where `N₀` is computed. -/
def oldMeasure (c ν : ℝ) : Measure Chart :=
  (volume.restrict (Ioi (6 / 5 / ν))).prod (Cyl.avgμ c)

/-- An old thin tensor with finite `N₀` (source 4917-4927: "arbitrary old thin tensors" with
`N₀(M) < ∞`): measurable on the old region with integrable `u^{-3/2}|M|`. -/
def OldThinFinite (c ν : ℝ) (M : Chart → Mat3) : Prop :=
  AEStronglyMeasurable M (oldMeasure c ν) ∧
    Integrable (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * frob (M p)) (oldMeasure c ν)

/-- The old-region measure is absolutely continuous with respect to the gain measure of `Z₁`
(source 2666-2700: the densities `g⁻² W² s^{-1/2}` are positive on `s > 0`). -/
def OldMeasureAC : Prop :=
  ∀ (c mZ γ ν : ℝ), 0 < ν → oldMeasure c ν ≪ gainZ1Measure c mZ γ ν

/-- The reflection `(y₁, y₂, y₃) ↦ (y₁, -y₂, y₃)` across the meridian plane `φ = 0`. -/
def reflY (y : Vec3) : Vec3 := ![y 0, -y 1, y 2]

/-- `X^mt` commutes with the reflection across `φ = 0` (source 4771-4791: `Σ_M` is the rotation of a
`u`-dependent tensor with zero azimuthal row and column, so the field is swirl free).  No
hypotheses: this is algebra and the measure-preserving substitution `x' ↦ (x'₁, -x'₂)`. -/
def XmtReflect : Prop :=
  ∀ (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (y : Vec3),
    Xmt c ν ε μ χo χy M (reflY y) = reflY (Xmt c ν ε μ χo χy M y)

/-- `X^mt` depends only on the a.e. class of `M` on the old region (source 4766-4770: `E` is a phase
mean; outside `u > 1.2/ν` the cutoff `χ_o` vanishes). -/
def XmtCongr : Prop :=
  ∀ (c ν ε μ : ℝ) (χo χy : ℝ → ℝ), IsOutwardCutoff χo → 0 < ν →
    ∀ M M' : Chart → Mat3, M =ᵐ[oldMeasure c ν] M' →
      Xmt c ν ε μ χo χy M = Xmt c ν ε μ χo χy M'

/-- `X^mt` is smooth on `ℝ³` for old tensors with finite `N₀` (source 4776-4791, 4917-4937): it vanishes
on the open set `(ε|y'|)² < ν` where `χ_y ≡ 0`, and on `(ε|y'|)² > 5ν/6` the Newton kernel is
separated from the old source disk and the outward primitive converges with its derivatives. -/
def XmtSmooth : Prop :=
  ∀ (c ν ε μ : ℝ) (χo χy : ℝ → ℝ), LHyp c ν ε μ χo χy →
    ∀ M : Chart → Mat3, OldThinFinite c ν M → ContDiff ℝ 7 (Xmt c ν ε μ χo χy M)

/-- `X^mt` is solenoidal (source 4184-4186: the outward stream cutoff is solenoidal; 4797-4800: the
uncut field is a harmonic gradient). -/
def XmtSolenoidal : Prop :=
  ∀ (c ν ε μ : ℝ) (χo χy : ℝ → ℝ), LHyp c ν ε μ χo χy →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ∀ y : Vec3, ∑ i, fderiv ℝ (Xmt c ν ε μ χo χy M) y (Pi.single i 1) i = 0

/-- `M ↦ X^mt` is linear on old tensors with finite `N₀` (source 4766-4791; the integrals converge
absolutely on the receiver region, 4917-4937). -/
def XmtLinear : Prop :=
  ∀ (c ν ε μ : ℝ) (χo χy : ℝ → ℝ), LHyp c ν ε μ χo χy →
    ∀ M M' : Chart → Mat3, OldThinFinite c ν M → OldThinFinite c ν M' → ∀ r : ℝ,
      Xmt c ν ε μ χo χy (M + M') = Xmt c ν ε μ χo χy M + Xmt c ν ε μ χo χy M' ∧
        Xmt c ν ε μ χo χy (r • M) = r • Xmt c ν ε μ χo χy M

/-! ## 9. The source facts for `𝓛` on the stress space (source 4797-4803, 4917-4937) -/

/-- `𝓛T` is `C^6` (indeed smooth) on `(0,∞)` (source 4797-4800, 4920-4937: the receiver acts only on
the smooth separated kernel and on the outward primitive; the Z₁-gain norm controls `N₀`). -/
def SourceLSmooth (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) : Prop :=
  LHyp c ν ε μ χo χy → 3 / 2 < mZ → 0 < γ →
    ∀ T : StrG c mZ ρb γ ν, ContDiffOn ℝ 6 (LjFun c mZ ρb γ ν ε μ χo χy T) (Ioi 0)

/-- `𝓛T` is trace free (source 4798: `tr D_y X = div X = 0`; the uncut field is a harmonic gradient
and the outward stream cutoff is solenoidal, 4184-4186). -/
def SourceLTraceFree (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) : Prop :=
  LHyp c ν ε μ χo χy → 3 / 2 < mZ → 0 < γ →
    ∀ (T : StrG c mZ ρb γ ν) (s : ℝ), 0 < s →
      LjFun c mZ ρb γ ν ε μ χo χy T s 0 0 + LjFun c mZ ρb γ ν ε μ χo χy T s 1 1 +
        LjFun c mZ ρb γ ν ε μ χo χy T s 2 2 = 0

/-- `𝓛T` has the azimuthal symmetry of `𝒜`: no entry with exactly one azimuthal index
(source 4798-4799; `X^mt` is axisymmetric without swirl since `Σ_M` is rotation equivariant with
zero azimuthal row and column). -/
def SourceLAzimuthal (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) : Prop :=
  LHyp c ν ε μ χo χy → 3 / 2 < mZ → 0 < γ →
    ∀ (T : StrG c mZ ρb γ ν) (s : ℝ), 0 < s →
      LjFun c mZ ρb γ ν ε μ χo χy T s 0 1 = 0 ∧ LjFun c mZ ρb γ ν ε μ χo χy T s 1 0 = 0 ∧
        LjFun c mZ ρb γ ν ε μ χo χy T s 1 2 = 0 ∧ LjFun c mZ ρb γ ν ε μ χo χy T s 2 1 = 0

/-- `𝓛T` vanishes for `s ≥ 1/ν` (source 4799: the stream cutoff vanishes on `r ≤ R√ν`, and at
`s = 1/ν` all derivatives of `χ̂_y` vanish). -/
def SourceLYoung (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) : Prop :=
  LHyp c ν ε μ χo χy → 3 / 2 < mZ → 0 < γ →
    ∀ (T : StrG c mZ ρb γ ν) (s : ℝ), 1 / ν ≤ s → LjFun c mZ ρb γ ν ε μ χo χy T s = 0

/-- `𝓛` is linear on the stress space (source 4792-4796: `E`, `Σ_M`, `V`, `W`, `𝒞_y` and `D_y` are
linear; all integrals converge absolutely by the separated-kernel bounds, 4917-4937). -/
def SourceLLinear (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) : Prop :=
  LHyp c ν ε μ χo χy → 3 / 2 < mZ → 0 < γ →
    ∀ (T T' : StrG c mZ ρb γ ν) (r : ℝ),
      LjFun c mZ ρb γ ν ε μ χo χy (T + T') =
          LjFun c mZ ρb γ ν ε μ χo χy T + LjFun c mZ ρb γ ν ε μ χo χy T' ∧
        LjFun c mZ ρb γ ν ε μ χo χy (r • T) = r • LjFun c mZ ρb γ ν ε μ χo χy T

/-- `source-class:ambient-L` (source 4920-4933), pointwise in the age: for every old thin tensor
with finite `N₀`, `e^{-a_s s} s^{-5/2} Σ_{j≤6}|(s∂_s)^j 𝓛M(s)| ≤ C_{K,k,a_s} ε³ N₀(M)`, uniformly in
`c, ν, ε` and `μ ∈ K` (each fixed `r∂_r` costs `r^{-5}`; the fractional radial gap is fixed on the
young-old rectangle; conormal derivatives of `χ̂_y(νs)` are uniformly bounded). -/
def SourceLAmbient (as : ℝ) (K : Set ℝ) (χo χy : ℝ → ℝ) : Prop :=
  0 < as → IsCompact K → K ⊆ Ioo 0 (1 / 4) →
    ∃ C : ℝ, ∀ (c ν ε μ : ℝ), LHyp c ν ε μ χo χy → μ ∈ K →
      ∀ M : Chart → Mat3, OldThinFinite c ν M →
        ∀ s, 0 < s → affTerm as 6 (Lpt c ν ε μ χo χy M) s ≤ C * ε ^ 3 * oldN0 c ν M

/-- `N₀(M) ≤ P_ν e^{γ/ν} ‖g⁻¹M‖_Z` for the thin component of a gain stress (source 4934-4936;
Cauchy-Schwarz against `g² W⁻² u^{-5/2}` on `u > 1.2/ν`, `g ≤ e^{γ/ν}`, `∫ W⁻² dη ≲ √(1+u)` for
`m_Z > 1/2`), together with the measurability and integrability that make `N₀` finite. -/
def SourceLN0 (mZ γ : ℝ) : Prop :=
  3 / 2 < mZ → 0 < γ →
    ∃ (C : ℝ) (k : ℕ), ∀ (c ν ρb : ℝ), 0 < c → 0 < ν → ν ≤ 1 → ∀ T : StrG c mZ ρb γ ν,
      OldThinFinite c ν (thinRep T) ∧ oldN0 c ν (thinRep T) ≤ C * ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖

/-- `a_μ ∈ 𝒜` (source 4807-4811, 4833: `‖a_μ‖_𝒜 ≤ C`). -/
def AMuInAff (as μ : ℝ) : Prop := 0 ≤ as → 0 < μ → IsAffElem as (aMuFun μ)

/-- `𝓛T ∈ 𝒜` (source 4797-4799): `C^6`, trace free, azimuthal symmetry, finite `𝒜` norm. -/
def SourceLInAff (as c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) : Prop :=
  0 < as → LHyp c ν ε μ χo χy → 3 / 2 < mZ → 0 < γ →
    ∀ T : StrG c mZ ρb γ ν, IsAffElem as (LjFun c mZ ρb γ ν ε μ χo χy T)

/-- `‖𝓛T‖_𝒜 ≤ P_ν ε³ e^{γ/ν} ‖T‖` uniformly for `μ ∈ K` (source 4930-4937; on the loop-gain band
`ε³ e^{γ/ν}` is polynomial, which is the second clause `‖L‖_{𝓔_ν→𝒜} ≤ P_ν` of
`closure:source-and-extraction`, 5883-5890). -/
def SourceLBounded (as mZ γ : ℝ) (K : Set ℝ) (χo χy : ℝ → ℝ) : Prop :=
  0 < as → IsCompact K → K ⊆ Ioo 0 (1 / 4) → 3 / 2 < mZ → 0 < γ →
    ∃ (C : ℝ) (k : ℕ), ∀ (c ρb ν ε μ : ℝ), LHyp c ν ε μ χo χy → μ ∈ K →
      ∀ T : StrG c mZ ρb γ ν,
        affNorm as (LjFun c mZ ρb γ ν ε μ χo χy T) ≤
          C * ν⁻¹ ^ k * (ε ^ 3 * Real.exp (γ / ν)) * ‖T‖

/-! ## 10. Consequences proved here -/

theorem oldN0_nonneg (c ν : ℝ) (hν : 0 < ν) (M : Chart → Mat3) : 0 ≤ oldN0 c ν M := by
  unfold oldN0
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := lt_trans (by positivity) hu
  exact mul_nonneg (Real.rpow_nonneg hu0.le _)
    (integral_nonneg fun x => Real.sqrt_nonneg _)

theorem affTerm_six_nonneg (as : ℝ) (A : ℝ → Mat3) {s : ℝ} (hs : 0 < s) :
    0 ≤ affTerm as 6 A s := by
  unfold affTerm affSum
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs.le _))
    (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _)

/-- `χ_f 𝓛T = 𝓛T` exactly (source 4801-4803), from the vanishing for `s ≥ 1/ν`. -/
theorem ay_LjFun_of {c mZ ρb γ ν ε μ : ℝ} {χo χy χf : ℝ → ℝ}
    (hY : SourceLYoung c mZ ρb γ ν ε μ χo χy) (hf : IsSourceCutoffC χf)
    (h : LHyp c ν ε μ χo χy) (hmZ : 3 / 2 < mZ) (hγ : 0 < γ) (T : StrG c mZ ρb γ ν) :
    Ay ν χf (LjFun c mZ ρb γ ν ε μ χo χy T) = LjFun c mZ ρb γ ν ε μ χo χy T := by
  funext s
  unfold Ay
  by_cases hs : s < 1 / ν
  · have hνs : ν * s ≤ 1 := by
      have := mul_lt_mul_of_pos_left hs h.nu_pos
      rw [mul_one_div_cancel h.nu_pos.ne'] at this
      exact this.le
    rw [hf.one _ hνs, one_smul]
  · rw [hY h hmZ hγ T s (not_lt.1 hs), smul_zero]

/-- `𝓛T ∈ 𝒜` from smoothness, trace, symmetry, the ambient bound and the `N₀` bound. -/
theorem sourceLInAff_of {as c mZ ρb γ ν ε μ : ℝ} {χo χy : ℝ → ℝ}
    (hs : SourceLSmooth c mZ ρb γ ν ε μ χo χy) (ht : SourceLTraceFree c mZ ρb γ ν ε μ χo χy)
    (ha : SourceLAzimuthal c mZ ρb γ ν ε μ χo χy) (hb : SourceLAmbient as {μ} χo χy)
    (hN : SourceLN0 mZ γ) : SourceLInAff as c mZ ρb γ ν ε μ χo χy := by
  intro has h hmZ hγ T
  have hK : ({μ} : Set ℝ) ⊆ Ioo 0 (1 / 4) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨h.mu_pos, h.mu_lt⟩
  obtain ⟨C, hC⟩ := hb has isCompact_singleton hK
  obtain ⟨C2, k, hC2⟩ := hN hmZ hγ
  obtain ⟨hfin, -⟩ := hC2 c ν ρb h.c_pos h.nu_pos h.nu_le T
  refine ⟨hs h hmZ hγ T, ht h hmZ hγ T, ha h hmZ hγ T, fun s hs0 => ?_, ?_⟩
  · exact Lpt_of_nonpos c ν ε μ χo χy _ hs0
  · refine ⟨C * ε ^ 3 * oldN0 c ν (thinRep T), ?_⟩
    rintro _ ⟨s, hs0, rfl⟩
    exact hC c ν ε μ h (Set.mem_singleton μ) (thinRep T) hfin s hs0

/-- `‖𝓛T‖_𝒜 ≤ P_ν ε³ e^{γ/ν}‖T‖` from the ambient bound and the `N₀` bound. -/
theorem sourceLBounded_of {as mZ γ : ℝ} {K : Set ℝ} {χo χy : ℝ → ℝ}
    (hb : SourceLAmbient as K χo χy) (hN : SourceLN0 mZ γ) :
    SourceLBounded as mZ γ K χo χy := by
  intro has hKc hK hmZ hγ
  obtain ⟨C1, hC1⟩ := hb has hKc hK
  obtain ⟨C2, k, hC2⟩ := hN hmZ hγ
  refine ⟨|C1| * C2, k, fun c ρb ν ε μ h hμ T => ?_⟩
  obtain ⟨hfin, hn⟩ := hC2 c ν ρb h.c_pos h.nu_pos h.nu_le T
  have hN0 := oldN0_nonneg c ν h.nu_pos (thinRep T)
  have he : 0 ≤ ε ^ 3 := pow_nonneg h.eps_pos.le 3
  have key : ∀ s, 0 < s → affTerm as 6 (LjFun c mZ ρb γ ν ε μ χo χy T) s ≤
      |C1| * C2 * ν⁻¹ ^ k * (ε ^ 3 * Real.exp (γ / ν)) * ‖T‖ := by
    intro s hs
    have h1 := hC1 c ν ε μ h hμ (thinRep T) hfin s hs
    have h2 : C1 * ε ^ 3 * oldN0 c ν (thinRep T) ≤ |C1| * ε ^ 3 * oldN0 c ν (thinRep T) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C1) he) hN0
    have h3 : |C1| * ε ^ 3 * oldN0 c ν (thinRep T) ≤
        |C1| * ε ^ 3 * (C2 * ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (abs_nonneg _) he)
    have h4 : |C1| * ε ^ 3 * (C2 * ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖) =
        |C1| * C2 * ν⁻¹ ^ k * (ε ^ 3 * Real.exp (γ / ν)) * ‖T‖ := by ring
    unfold LjFun
    linarith
  unfold affNorm
  exact csSup_le ⟨_, ⟨1, Set.mem_Ioi.2 (one_pos : (0 : ℝ) < 1), rfl⟩⟩ (by rintro _ ⟨s, hs, rfl⟩; exact key s hs)

end UnforcedLeray.Short.PartIIIb.Concrete
