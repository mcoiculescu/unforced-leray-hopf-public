import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_4_1_org_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.Trans

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/inv`: `SepYoungRep` by density (design)

Source `the November 2 reference manuscript`
3596-3626 (`sep:kernel`, `sep:resolvent`: `W_μ = -S_μT`; the kernel `K_0` has a local
distributional part that is "retained by the operator, but vanishes at a separated receiver"),
4145, 4163-4174 (`W_μ = -S_μ(χ_oT)`, old disk `|z'| ≤ r_o`, ages `s ≥ 1.2/ν`), 4187-4194, 5169-5176.

## Why density

`IIIa.sepW` is a Lebesgue integral of `∇K(y-λz) : T(z)`; it is the true `-S_μT` only at separated
receivers (young region `ν s ≤ 1`).  The global weak stress inverse `Sop` is a bounded linear map on
`StrG`.  The young-region identity is therefore proved for a dense class of old sources, where a
genuine global response exists (local part of `K_0` retained), and passes to the limit:

1. `SepSmoothResponseAt` : for an old bounded band-supported source `F` the global weak solution
   `B ∈ VelG` of `D_μ w = ℙ div 𝒩_T F` is `-W_μ` on the young region.  With free weak uniqueness
   (closed) this gives `Sop F = -W_μ` there (`sepSmoothAgree`, proved).
2. `SepOldSrcFiniteAt` : the old repair source `oldRep w` has a separated representative `T` of
   finite `L²_τL^{22/19}` norm (source 5169-5176 `repair:source`).
3. `SepOldDensityAt` : such `oldRep w` is the `StrG`-limit of old bounded band-supported sources
   whose separated representatives converge in `L²_τL^{22/19}` simultaneously.
4. `SepYoungContAt` : the young-region map `g ↦ -W_μ` is Lipschitz from the source norm
   `L²_τL^{22/19}` into `L²(bodyMeasure)` (source 3648-3668, `sep:repair-energy`, `j = 0`; this is
   `sepWreYoungL2` + chart transport, tasks `.../org/1/1/1..6`).

`sepYoungRepAtInv_of` (Of.lean) proves `SepYoungRepAt` from these and free weak uniqueness.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `T` is a **separated representative** of the chart source `g` (source 4155-4174, 5169-5176):
a separated source with period `P = 2εc`, old disk `|z'| ≤ ε⁻¹√(5ν/6)`, equal to the physical
source `oldPhys ε⁻¹ c g` almost everywhere in `(τ, z)`, with `W_μ(g) = Re sepW T` at every
`(τ, y)` and finite `L²_τL^{22/19}` norm. -/
def SepRepOf (L : ReturnLevel) (μ : ℝ) (g : Chart → Ten3)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) T ∧
  (∀ᵐ x : ℝ × Space, T x.1 x.2 = oldPhys L.ε⁻¹ (cOf L.ν) g x.1 x.2) ∧
  (∀ (τ : ℝ) (y : Space), wardW L.ν μ L.ε⁻¹ (cOf L.ν) g τ y = sepWre L.ν μ T τ y) ∧
  IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T) < ⊤

/-- The dense class: `F` is an **old bounded band-supported stress** (source 4163-4166: old ages
`s ≥ 1.2/ν`, i.e. `|z'| ≤ r_o`): both components have bounded measurable chart representatives
supported in a compact band of the chart (`NearInst.IsBoxTensor`) and vanishing for `ν s < 6/5`. -/
def OldBoxAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (F : LStr Pl K L)
    (f₁ f₂ : Chart → Ten3) : Prop :=
  IsRep Pl K L F f₁ f₂ ∧ NearInst.IsBoxTensor f₁ ∧ NearInst.IsBoxTensor f₂ ∧
    ∀ p : Chart, L.ν * p.1 < 6 / 5 → f₁ p = 0 ∧ f₂ p = 0

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **(i) The global response of an old bounded source** (source 3596-3626, 4145, 4163-4174,
1556-1572): for an old bounded band-supported stress `F` there is a body velocity `B` that is a
weakly solenoidal distributional `Y_2` solution of `D_μ w = ℙ div 𝒩_T(F₁ + F₂)` (the heat--Leray
resolvent of the bounded compactly supported source, with the local distributional part of `K_0`,
i.e. after the integration by parts `∇K : F ↦ K : ∇F` in the weak sense) and which equals the
separated-kernel field `-W_μ` at body-a.e. young point (there `y - λz` stays away from `0`, so the
Lebesgue integral of `sepW` converges and agrees with the distributional one). -/
def SepSmoothResponseAt : Prop :=
  ∀ (F : LStr Pl K L) (f₁ f₂ : Chart → Ten3), OldBoxAt Pl K L F f₁ f₂ →
    ∃ B : LVel Pl L,
      IsWeakDmu L.ν μ (2 * L.ε * cOf L.ν) (velPhys L.ε⁻¹ (cOf L.ν) B)
        (fun Φ => -stressPair (2 * L.ε * cOf L.ν)
          (strPhys L.ε⁻¹ (cOf L.ν) (strSum F)) Φ) ∧
      ∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν), L.ν * p.1 ≤ 1 →
        (B : Chart → Merid) p =
          -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (f₁ + f₂)) p

/-- **(ii) A finite separated representative of the old repair source** (source 5169-5176
`repair:source`: `F_r = ‖χ_o(r_b×w + w×r_b)‖_{L²_τL^{22/19}} < ∞`; the extraction of
`wardW_eq_sepWre`, task `.../org/1/1/4` `sepRepSrcFinite`, with the a.e. identification
`T = oldPhys` from `repairSepBridge`/`oldSourceReg_of`). -/
def SepOldSrcFiniteAt : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    ∃ T, SepRepOf L μ (g₁ + g₂) T

/-- **(iii) Density of old bounded sources** (source 5169-5176, 4163-4166; truncate the chart
representative to a band `s₁ ≤ s ≤ s₂`, `|η| ≤ Λ`, `ν s ≥ 6/5`, and to `‖g‖ ≤ B`, then let
`s₁ ↓ 6/(5ν)`... `B, Λ, s₂ → ∞`: dominated convergence in the gain norm of `StrG` and in the
physical source norm `L²_τL^{22/19}`; the physical cut sources are separated representatives):
for the old repair source with representatives `g₁ g₂` and separated representative `T`, there are
old bounded band-supported stresses `Fn → oldRep w` in `StrG` whose separated representatives `Tn`
converge to `T` in `L²_τL^{22/19}`. -/
def SepOldDensityAt : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    IsRep Pl K L (oldRep Pl K L w) g₁ g₂ → SepRepOf L μ (g₁ + g₂) T →
    ∃ (Fn : ℕ → LStr Pl K L) (f₁ f₂ : ℕ → Chart → Ten3)
      (Tn : ℕ → ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
      (∀ n, OldBoxAt Pl K L (Fn n) (f₁ n) (f₂ n) ∧ SepRepOf L μ (f₁ n + f₂ n) (Tn n)) ∧
      Tendsto Fn atTop (𝓝 (oldRep Pl K L w)) ∧
      Tendsto (fun n => IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19)
          (IIIa.srcNorm (fun τ z => Tn n τ z - T τ z))) atTop (𝓝 0)

/-- **(iv) Continuity of the young-region response in the source norm** (source 3648-3668
`sep:repair-energy` with `j = 0`, `D = r_i - r_o = R√ν(1 - √(5/6))`, kernel linearity for
absolutely convergent integrals; chart transport 2666-2668, 5143; gain `≤ e^{2|γ|/ν}` on `ν s ≤ 1`):
the cut field `youngWCoef` of two separated sources is a.e. strongly measurable and
`‖youngWCoef g - youngWCoef g'‖_{L²(body)} ≤ C ‖T - T'‖_{L²_τL^{22/19}}` with `C` independent of the
sources. -/
def SepYoungContAt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (g g' : Chart → Ten3) (T T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    SepRepOf L μ g T → SepRepOf L μ g' T' →
      AEStronglyMeasurable (youngWCoef Pl K L μ g) (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) ∧
      AEStronglyMeasurable (youngWCoef Pl K L μ g') (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) ∧
      eLpNorm (fun p => youngWCoef Pl K L μ g p - youngWCoef Pl K L μ g' p) 2
          (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) ≤
        ENNReal.ofReal C * IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19)
          (IIIa.srcNorm (fun τ z => T τ z - T' τ z))

end UnforcedLeray.Short.PartIIIb.Concrete
