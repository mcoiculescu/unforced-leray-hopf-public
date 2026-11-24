import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs

/-!
# The exact unprojected residual `𝔯_A` and its source leaves (source 4371, 4951-5079)

Source of record: `the November 2 reference manuscript` (73 pages).

Part (a) of `ORG:return-concrete/instance-3/affine-source`: the objects and the leaves of
Lemma `ret:physical-affine` (source 5001-5008) with the second line of
`ret:general-affine-bounds` (5014-5016), proof 5022-5079.  The reductions are in
`RAPin.lean` (the pin `IsRAOp`) and `RABound.lean` (the bound and `RABoundExists`).

## The physical fields of one regime (`ν, μ, ε = R⁻¹`, `c`, source cutoff `χ_f`, `A : ℝ → Mat3`)

* `hLift` : `ĥ_A` as a physical field, the lift `𝒩_v` of its chart coefficient `hAcoef`
  (source 4979-4980; `velPhys R c (hAcoef …) = realCf (hLift …)` by definition);
* `feLift` : `F_A + E_A` (source 4981), the lift of `FAcoef + EAcoef`;
* `psiLift` : `sΨ_A`, `Ψ_A = Σ_j (A^y_mer x_j)·∇p_j` (source 5024, 5040-5043; `sPsiPhys`);
* `rAPhys … U A` : **the exact unprojected residual** (source 5001-5008, 5022-5050)
  `𝔯_A = D_μĥ_A + div(U⊗ĥ_A + ĥ_A⊗U) - F_A - E_A - ∇_y(sΨ_A)` on the background `U`;
* `rAcoef` : its chart coefficient `s^{-1/2}(𝔯_r, 𝔯_z)` (`coefOf`, the convention of `SrcG`).

## The decomposition of the proof (source 5022-5079)

* `rPer` : the Cartesian bracket residual `r_per` of source 5023-5028 in the cell variables
  `x = (q, η)`, with the planar train `v` of the level:
  `r_per = (∂_s + μ/s - νΔ)h^p_A + (v·∇)h^p_A + (h^p_A·∇)v - f_A - e_A - ∇Ψ_A`;
  `rPerCoef = s·r_per` is its coefficient (`𝔯 = s^{3/2}r_per + …`, coefficient `s^{-1/2}·`);
* `geoCoef p μ χf A = rAcoef(U_raw) - rPerCoef` : the geometric remainder of the ring-chart rules,
  the stream completion and the pressure completion (source 5034-5044) on the raw background
  `U_raw = p.raw` (source 2076-2077, `Params.raw`);
* `convCoef p μ χf U A = rAcoef(U) - rAcoef(U_raw)` : the convection difference
  `(U-U_raw)·∇ĥ_A + ĥ_A·∇(U-U_raw)` (source 5045-5050);
* `rAcoef_decomp` : `rAcoef(U) = rPerCoef + geoCoef + convCoef` (algebra).

## Leaves (tasks; each a statement of the source or a calculus lemma)

* integration by parts at finite smoothness (the identity `IsRAOp` against phase tests, source
  5001-5008; `ĥ_A` is only `C^5` since `A ∈ 𝒜` is `C^6`, source 5076-5079): `IBPAdjointC2`,
  `IBPDivC1`, `IBPGradC1`, `IBPContC` (the `C^∞` versions are proved in
  `Sub/IIIb-D2_3_2/Sub/IIIb-D2_3_2_8_*.lean`);
* `AffineLiftReg` : `ĥ_A` is `C²`, `sΨ_A` is `C¹`, `F_A + E_A` is continuous on `ℝ × ℝ³`
  (source 4978, 4991, 5076-5079);
* `RAPhysAxi` : `𝔯_A` is axisymmetric without swirl and `2εc`-periodic in the phase (source
  2666-2668, 4995-4997);
* `RALinear` : `A ↦ 𝔯_A` is linear (source 4985);
* `RPerBound` : `‖r_per(s)‖_{cell} ≤ C δ_base M(A) s^{5/2}` on `0 < s ≤ 1.1/ν`, `δ_base` as in 4371
  (source 5023-5032);
* `RAGeoBound` : the geometric remainder has cell norm `≤ P_ν ε M(A)(s^{5/2} + s^{7/2})`
  (source 5034-5044, "age size at most `C(s^{3/2}+s^{5/2})` in age-force units");
* `RAConvBound` : `‖convCoef‖ ≤ P_ν δ_U M(A)` (source 5045-5050 with the first line 5009-5013).

The body conversion (source 5055-5060) is the accepted `ChartL2Conv` (`PartIII-b:C/inst/9/5`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The physical fields of one regime -/

/-- **`ĥ_A` as a physical field** (source 4979-4980): the lift `𝒩_v b = √s(b_r e_r + b_z e_z)` of
its chart coefficient `b = hAcoef`, `R = ε⁻¹`, periodically extended in `q` (`perExt`). -/
def hLift (ν ε c : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → Space → Space :=
  fun τ y => Nv ε⁻¹ (perExt c (hAcoef ν ε χf A)) τ y

/-- **`F_A + E_A` as a physical field** (source 4981): the lift of `FAcoef + EAcoef`. -/
def feLift (ν μ ε c : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → Space → Space :=
  fun τ y => Nv ε⁻¹ (perExt c (FAcoef ν μ χf A + EAcoef ν μ χf A)) τ y

/-- **`sΨ_A`** (source 5024, 5040-5043), the global pressure scalar of `IsRAOp`. -/
def psiLift (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → Space → ℝ :=
  fun τ y => sPsiPhys ν ε⁻¹ χf A (τ, y)

/-- **The exact unprojected residual** `𝔯_A = D_μĥ_A + div(U⊗ĥ_A + ĥ_A⊗U) - F_A - E_A - ∇_y(sΨ_A)`
on the background `U` (source 5001-5008, 5022-5050; `D_μ = ∂_τ - y·∇/2 - νΔ + μ - 1/2`). -/
def rAPhys (ν μ ε c : ℝ) (χf : ℝ → ℝ) (U : ℝ → SpatialField) (A : ℝ → Mat3) :
    ℝ → Space → Space :=
  fun τ y => physDmu ν μ (hLift ν ε c χf A) τ y + physDivSym (U τ) (hLift ν ε c χf A τ) y -
    feLift ν μ ε c χf A τ y - physGrad (psiLift ν ε χf A τ) y

/-- The chart coefficient `s^{-1/2}(𝔯_r, 𝔯_z)` of `𝔯_A` (the convention of `SrcG`). -/
def rAcoef (ν μ ε c : ℝ) (χf : ℝ → ℝ) (U : ℝ → SpatialField) (A : ℝ → Mat3) : Chart → Merid :=
  coefOf ε⁻¹ (rAPhys ν μ ε c χf U A)

/-! ## 2. The Cartesian bracket residual (source 5023-5028) -/

/-- The planar train `v(s, q, η)` (source 5022: "Write `v` for the planar train"). -/
def trainPl {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (tr.v s x 0, tr.v s x 1)

/-- `Δ_{q,η}` of a planar vector field. -/
def lapPl (f : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ∑ a : Fin 2, fderiv ℝ (fun y => fderiv ℝ f y (ei a)) x (ei a)

/-- The meridional `(r, z) ↔ (q, η)` part of a vector in the order `(r, φ, z)`. -/
def merPl (v : Vec3) : ℝ × ℝ := (v 0, v 2)

/-- `(a, b) ↦ (a, b)` as a meridional vector. -/
def toMer (v : ℝ × ℝ) : Merid := !₂[v.1, v.2]

/-- **The Cartesian bracket residual** `r_per` (source 5023-5028):
`(∂_s + μ/s - νΔ)h^p_A + (v·∇)h^p_A + (h^p_A·∇)v = f_A + e_A + ∇Ψ_A + r_per`, at the cell point
`(s, x)`, with the planar train `v = tr.v` of the level. -/
def rPer {ν c : ℝ} (μ : ℝ) (χf : ℝ → ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (A : ℝ → Mat3)
    (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  deriv (fun s' => hpA ν χf A s' x) s + (μ / s) • hpA ν χf A s x - ν • lapPl (hpA ν χf A s) x +
    fderiv ℝ (hpA ν χf A s) x (trainPl tr s x) + fderiv ℝ (trainPl tr s) x (hpA ν χf A s x) -
    merPl (fA ν μ χf A s x) - merPl (eA ν μ χf A s x) - mgrad (PsiA ν χf A s) x

/-- The coefficient `s·r_per` (the physical field is `s^{3/2}r_per`, source 5034-5039). -/
def rPerCoef {ν c : ℝ} (μ : ℝ) (χf : ℝ → ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (A : ℝ → Mat3) : Chart → Merid :=
  fun p => p.1 • toMer (rPer μ χf tr A p.1 p.2)

/-! ## 3. The three parts of the residual at a level `p` -/

/-- **The geometric remainder** (source 5034-5044): the residual on the raw background
`U_raw = p.raw` minus `s·r_per`. -/
def geoCoef (p : Params) (μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  rAcoef p.ν μ p.ε p.c χf p.raw A - rPerCoef μ χf p.train A

/-- **The convection difference** (source 5045-5050): the residual on `U` minus the residual on
`U_raw`, i.e. the coefficient of `div((U-U_raw)⊗ĥ_A + ĥ_A⊗(U-U_raw))`. -/
def convCoef (p : Params) (μ : ℝ) (χf : ℝ → ℝ) (U : ℝ → SpatialField) (A : ℝ → Mat3) :
    Chart → Merid :=
  rAcoef p.ν μ p.ε p.c χf U A - rAcoef p.ν μ p.ε p.c χf p.raw A

theorem rAcoef_decomp (p : Params) (μ : ℝ) (χf : ℝ → ℝ) (U : ℝ → SpatialField)
    (A : ℝ → Mat3) :
    rAcoef p.ν μ p.ε p.c χf U A =
      rPerCoef μ χf p.train A + geoCoef p μ χf A + convCoef p μ χf U A := by
  unfold geoCoef convCoef
  abel

/-! ## 4. Leaves: integration by parts at finite smoothness (source 5001-5008) -/

/-- **`L₀ᵗ + μ` is the transpose of `D_μ` on `C²` periodic fields** (source 4140-4141, 5001-5008):
for a jointly `C²` field `u`, `P`-periodic in `τ`, and a phase test `Φ`,
`⟨L₀ᵗΦ + μΦ, u⟩ = ⟨Φ, D_μu⟩`.  (`IBPAdjoint` and `IBPBridge` of `Sub/IIIb-D2_3_2/Sub/IIIb-D2_3_2_8.lean`
are the `C^∞` versions.) -/
def IBPAdjointC2 : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → ∀ u : ℝ → Space → Space,
    ContDiff ℝ 2 (fun x : ℝ × Space => u x.1 x.2) → (∀ τ y, u (τ + P) y = u τ y) →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
      pairF P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (realCf u) = pairF P Φ (realCf (physDmu ν μ u))

/-- **`⟨Φ, div(a⊗b + b⊗a)⟩ = -⟨a⊗b + b⊗a, ∇Φ⟩` for `C¹` fields** (source 5001-5008; `IBPDiv` is the
`C^∞` version). -/
def IBPDivC1 : Prop :=
  ∀ (P : ℝ) (U W : ℝ → Space → Space),
    ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2) → ContDiff ℝ 1 (fun x : ℝ × Space => W x.1 x.2) →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
      pairF P Φ (realCf (fun τ y => physDivSym (U τ) (W τ) y)) =
        -stressPair P (fun x => symProd (U x.1 x.2) (W x.1 x.2)) Φ

/-- **`⟨Φ, ∇q⟩ = -⟨q, div Φ⟩` for `C¹` scalars and every phase test** (source 5001-5008,
5040-5043: the gradient term of `𝔯_A` is tested against all phase tests). -/
def IBPGradC1 : Prop :=
  ∀ (P : ℝ) (q : ℝ → Space → ℝ), ContDiff ℝ 1 (fun x : ℝ × Space => q x.1 x.2) →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
      pairF P Φ (realCf (fun τ y => physGrad (q τ) y)) = -scalarPair P (fun x => q x.1 x.2) Φ

/-- Continuity of `D_μu` (`u ∈ C²`), `div(a⊗b + b⊗a)` (`a, b ∈ C¹`) and `∇q` (`q ∈ C¹`); `IBPCont`
is the `C^∞` version. -/
def IBPContC : Prop :=
  (∀ (ν μ : ℝ) (u : ℝ → Space → Space), ContDiff ℝ 2 (fun x : ℝ × Space => u x.1 x.2) →
      Continuous (realCf (physDmu ν μ u))) ∧
  (∀ U W : ℝ → Space → Space, ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2) →
      ContDiff ℝ 1 (fun x : ℝ × Space => W x.1 x.2) →
      Continuous (realCf (fun τ y => physDivSym (U τ) (W τ) y))) ∧
  (∀ q : ℝ → Space → ℝ, ContDiff ℝ 1 (fun x : ℝ × Space => q x.1 x.2) →
      Continuous (realCf (fun τ y => physGrad (q τ) y)))

/-! ## 5. Leaves: regularity, symmetry and linearity of the affine fields -/

/-- **Regularity of the affine lift** (source 4978 "The sums and their required derivatives converge
by Gaussian decay", 4991, 5076-5079 derivative budget): for `A ∈ 𝒜`, `ν, ε > 0`, `c = ν⁻²`, the
physical `ĥ_A` is jointly `C²` and `sΨ_A` is jointly `C¹` on `ℝ × ℝ³`, and `F_A + E_A` is
continuous.  All three vanish near the axis (`χ_f(νs) = 0` for `s ≥ 1.1/ν`, `s = R²/ϱ²`), and the
lattice sums are `c`-periodic in `q`, so `perExt` introduces no seam. -/
def AffineLiftReg (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ ε : ℝ), 0 < ν → 0 < ε → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiff ℝ 2 (fun x : ℝ × Space => hLift ν ε (cOf ν) χf A x.1 x.2) ∧
    ContDiff ℝ 1 (fun x : ℝ × Space => psiLift ν ε χf A x.1 x.2) ∧
    Continuous (fun x : ℝ × Space => feLift ν μ ε (cOf ν) χf A x.1 x.2)

/-- **`𝔯_A` is axisymmetric without swirl and periodic** (source 2666-2668, 4995-4997): on an
axisymmetric swirl-free `C¹` background `U`, `2εc`-periodic in the phase, the residual is
axisymmetric without swirl (`AxiNoSwirl`, the lift of its trace on `φ = 0`) and `2c/R`-periodic,
`R = ε⁻¹`, `c = ν⁻²` (`ĥ_A, F_A+E_A` are lifts, `sΨ_A` is axisymmetric and `c`-periodic in `q`, and
`D_μ`, `div`, `∇` commute with the orthogonal maps fixing the axis). -/
def RAPhysAxi (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ ε : ℝ), 0 < ν → 0 < ε → ∀ U : ℝ → SpatialField,
    (∀ τ, AxiNoSwirlPt (U τ)) → ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2) →
    (∀ τ y, U (τ + 2 * ε * cOf ν) y = U τ y) → ∀ A : ℝ → Mat3, IsAffElem as A →
      AxiNoSwirl (rAPhys ν μ ε (cOf ν) χf U A) ∧
        ∀ τ y, rAPhys ν μ ε (cOf ν) χf U A (τ + 2 * cOf ν / ε⁻¹) y =
          rAPhys ν μ ε (cOf ν) χf U A τ y

/-- **`A ↦ 𝔯_A` is linear on `𝒜`** (source 4985 "All these maps depend linearly on `A`"), at every
chart point with `s > 0`, on a `C¹` background `U` (the lifts are linear by `HhatCoefLinear`,
`FACoefLinear`, `EACoefLinear` and the linearity of `Ψ_A`; `D_μ`, `div`, `∇` are linear on the
`C²`/`C¹` fields of `AffineLiftReg`). -/
def RALinear (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ ε : ℝ), 0 < ν → 0 < ε → ∀ U : ℝ → SpatialField,
    ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2) →
    ∀ (A A' : ℝ → Mat3) (r : ℝ), IsAffElem as A → IsAffElem as A' → ∀ p : Chart, 0 < p.1 →
      rAcoef ν μ ε (cOf ν) χf U (A + A') p =
          rAcoef ν μ ε (cOf ν) χf U A p + rAcoef ν μ ε (cOf ν) χf U A' p ∧
        rAcoef ν μ ε (cOf ν) χf U (r • A) p = r • rAcoef ν μ ε (cOf ν) χf U A p

/-! ## 6. Leaves: the three estimates (source 5023-5050) -/

/-- **The Cartesian bracket residual** (source 5023-5032, `δ_base` of 4371): `r_per` consists of
distinct-center convection products and `(v - Σ_jV_j)` terms; Gaussian summation and the fixed-band
train comparison bound its cell norms by `C δ_base M(A) s^{5/2}` on `0 < s ≤ 1.1/ν`,
`δ_base = P_ν e^{C_Σ/ν - b_Σc²}` (`deltaBase`, `c = ν⁻²`), uniformly at the levels of the
background regime with `ν ≤ ν₀` and `μ ∈ K ⋐ (0,1/4)`.  The cell measure is the normalized
`dq/c dη` (`Cyl.avgμ`); `r_per = 0` for `s > 1.1/ν` (`A^y = 0` there), and `s·r_per` is a.e.
strongly measurable. -/
def RPerBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ (Csig bsig C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < bsig ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ K, ∀ A : ℝ → Mat3, IsAffElem as A →
        AEStronglyMeasurable (rPerCoef μ χf p.train A) (srcMeasure p.c) ∧
        (∀ s : ℝ, (11 / 10) / p.ν < s → ∀ x : ℝ × ℝ, rPer μ χf p.train A s x = 0) ∧
        ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
          ∫⁻ x, ENNReal.ofReal (‖toMer (rPer μ χf p.train A s x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
            ≤ ENNReal.ofReal ((C * p.ν⁻¹ ^ k * deltaBase Csig bsig p.ν * affM p.ν χf A *
                s ^ (5 / 2 : ℝ)) ^ 2)

/-- **The geometric errors** (source 5034-5044): the exact ring-chart rules
`∂_r = √s(∂_q - ε𝒦)`, `∂_z = √s∂_η`, `(∂_τ - y·∇/2 - 1/2)(√s b) = s^{3/2}∂_sb`, the physical
Laplacian `s^{3/2}[(Δ_{q,η} - 2ε(𝒦+1)∂_q + ε²(𝒦+1)²)b - ε²b_re_r]`, the stream completions of `ĥ_A`
and of `U_raw`, and the pressure completion `s^{3/2}∇_{q,η}Ψ_A = ∇_y(sΨ_A) + εs^{3/2}(𝒦+2)Ψ_Ae_r`
put every geometric difference of the residual on the raw background into `εM(A)` times a fixed
Gaussian polynomial of age size `C(s^{3/2}+s^{5/2})` in age-force units: the coefficient
`geoCoef = rAcoef(U_raw) - s·r_per` has cell norm `≤ P_ν ε M(A)(s^{5/2} + s^{7/2})` on
`0 < s ≤ 1.1/ν`, vanishes for `s > 1.1/ν` and is a.e. strongly measurable. -/
def RAGeoBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ K, ∀ A : ℝ → Mat3, IsAffElem as A →
        AEStronglyMeasurable (geoCoef p μ χf A) (srcMeasure p.c) ∧
        (∀ s : ℝ, (11 / 10) / p.ν < s → ∀ x : ℝ × ℝ, geoCoef p μ χf A (s, x) = 0) ∧
        ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
          ∫⁻ x, ENNReal.ofReal (‖geoCoef p μ χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
            ≤ ENNReal.ofReal ((C * p.ν⁻¹ ^ k * p.ε * affM p.ν χf A *
                (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2)

/-- **The convection difference** (source 5045-5050 with the first line of
`ret:general-affine-bounds`, 5009-5013): on an exact profile `U` of the level with
`|U - U_raw| ≤ δ_U` and `‖∇(U - U_raw)‖ ≤ δ_U` everywhere, the coefficient of
`(U-U_raw)·∇ĥ_A + ĥ_A·∇(U-U_raw)` is in `L²(π s^{-3/2} dς)` with norm `≤ P_ν δ_U M(A)`
(pointwise `≤ Cδ_U(|ĥ_A| + |∇ĥ_A|)`, then `HhatCoefBound` and `GradCoefBound`). -/
def RAConvBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ K, ∀ (U : ℝ → SpatialField) (pr : ℝ → Space → ℝ), IsExactProfile p.ν p.period U pr →
      ∀ δU : ℝ, (∀ (τ : ℝ) (y : Space), ‖U τ y - p.raw τ y‖ ≤ δU ∧
          ‖fderiv ℝ (fun y' => U τ y' - p.raw τ y') y‖ ≤ δU) →
      ∀ A : ℝ → Mat3, IsAffElem as A →
        MemLp (convCoef p μ χf U A) 2 (srcMeasure p.c) ∧
        eLpNorm (convCoef p μ χf U A) 2 (srcMeasure p.c) ≤
          ENNReal.ofReal (C * p.ν⁻¹ ^ k * δU * affM p.ν χf A)

end UnforcedLeray.Short.PartIIIb.Concrete
