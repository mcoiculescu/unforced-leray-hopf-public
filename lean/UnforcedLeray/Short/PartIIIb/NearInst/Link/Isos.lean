import UnforcedLeray.Short.PartIIIb.NearInst
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps
import UnforcedLeray.Short.PartIIIb.NearInst.Link.SqrtDensity

/-!
# The near operators on the gain-normed return spaces (source 3866-3880, 5116-5143, 5536-5547,
5609, 5777-5787)

Source of record: `the November 2 reference manuscript` (73 pages).

The near layer (`NearInst.lean`) works on the ungained spaces `H`, `Z = Z_1 ⊕ ρ_b^{-1/2}H_T`
(`Concrete/Spaces.lean`, source 3866-3872) and measures operators after conjugation by the gain
`𝖦T = gT`, `g(s) = e^{γs/(1+νs)}` (source 3875-3880): `‖G⁻¹D_N⁻¹G‖_{Z→Z}`, `‖g⁻¹S_N g‖_{H_T→H}`.
The return layer (`Concrete/ReturnOps.lean`) puts the gain into the norms (source 5116-5128, 5143,
5609): `‖T‖_Str = ‖g⁻¹T‖_Z`, `‖w‖_Vel = R⁻¹‖g⁻¹𝒩_v w‖_{Y_2} = √π‖g⁻¹w‖_H`, and body forces
carry the ungained `‖f‖_Src = R⁻¹‖𝒩_v f‖_{Y_2} = √π‖f‖_H` (source 2683-2689).  Both layers use
the same chart functions (the coefficient `b` of `𝒩_v b = √s b`, the chart stress `T`).

## The isometries

* `strIso : StrG ≃ₗᵢ Zsp`, `T ↦ g⁻¹T` (componentwise; source 5609, 2698-2700);
* `velIso : VelG ≃ₗᵢ Hsp`, `w ↦ √π g⁻¹w` (source 5143, 2685-2689);
* `srcIso : SrcG ≃ₗᵢ Hsp`, `f ↦ √π f` (source 2683-2689).

With them the *same function* in both layers is `gainEquiv (strIso T)` (a stress),
`(√π)⁻¹ gainH (velIso w)` (a velocity) and `(√π)⁻¹ srcIso f` (a body force)
(`coeFn_zOfStr_fst/snd`, `coeFn_hOfVel`, `coeFn_hOfSrc`).

## The transported near operators (source 3875-3880, 3911-3920, 5785-5787)

* `NearOps.MG o γ hν = (√π)⁻¹ · strIso⁻¹ ∘ (g⁻¹ M_U g) ∘ velIso : VelG → StrG` (`M_U` acting on
  the same functions, `coeFn_MG_fst/snd`);
* `NearOps.SNG o γ hν = √π · velIso⁻¹ ∘ (g⁻¹ S_N g) ∘ strIso : StrG → VelG` (`coeFn_SNG`);
* `NearOps.DNinvG o γ hν = strIso⁻¹ ∘ (G⁻¹ D_N⁻¹ G) ∘ strIso`, `D_N⁻¹ = Ring.inverse D_N`;
* `bodyG Reps γ hν = velIso⁻¹ ∘ gainH⁻¹ ∘ R_ε ∘ srcIso : SrcG → VelG` (the body inverse acting on
  the same functions, source 4084-4086);
* `NearOps.flatColG o R0 γ hν = (√π)⁻¹ · strIso⁻¹ ∘ G⁻¹ ∘ D₀⁻¹ ∘ M₀ ∘ R₀ ∘ srcIso : SrcG → StrG`
  (the flat forced column `T₀ = D₀⁻¹M₀R₀f`, source 4109-4111).

Norms (all exact transfers): `norm_DNinvG_le` (`‖D_N⁻¹‖_{Str} ≤ ‖G⁻¹D_N⁻¹G‖_Z`), `norm_SNG_le`
(`‖S_N‖_{Str→Vel} ≤ √π‖g⁻¹S_N g‖`).  Algebra: `one_add_MG_SNG`
(`I + M S_N = strIso⁻¹ (G⁻¹D_N G) strIso`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The inverse gain and the density roots -/

theorem ginv_eq_gainInvFun (γ ν : ℝ) : Concrete.ginv γ ν = gainInvFun γ ν := rfl

theorem ginv_pos' (γ ν : ℝ) (p : Chart) : 0 < Concrete.ginv γ ν p :=
  inv_pos.2 (gainFun_pos γ ν p)

theorem ginv_measurable' (γ ν : ℝ) : Measurable (Concrete.ginv γ ν) :=
  (gainFun_measurable γ ν).inv

theorem ginv_mul_gainFun (γ ν : ℝ) (p : Chart) : Concrete.ginv γ ν p * gainFun γ ν p = 1 :=
  gainInvFun_mul p

theorem gainFun_mul_ginv (γ ν : ℝ) (p : Chart) : gainFun γ ν p * Concrete.ginv γ ν p = 1 := by
  rw [mul_comm]; exact ginv_mul_gainFun γ ν p

theorem sqrtPi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos

/-- `g⁻² W² s^{-1/2} dς = (g⁻¹)² · (W² s^{-1/2} dς)`. -/
theorem root_gainZ1 (c mZ γ ν : ℝ) :
    IsDensityRoot (gainZ1Measure c mZ γ ν) (z1Measure c mZ) (Concrete.ginv γ ν) :=
  ⟨ginv_measurable' γ ν, ginv_pos' γ ν, rfl⟩

/-- `g⁻² ρ_b⁻¹ s^{-1/2} dς = (g⁻¹)² · (ρ_b⁻¹ s^{-1/2} dς)`. -/
theorem root_gainHT (c ρb γ ν : ℝ) :
    IsDensityRoot (gainHTMeasure c ρb γ ν) (htRhoMeasure c ρb) (Concrete.ginv γ ν) :=
  ⟨ginv_measurable' γ ν, ginv_pos' γ ν, rfl⟩

/-- `π g⁻² s^{-3/2} dς = (√π g⁻¹)² · s^{-3/2} dς`. -/
theorem root_body (c γ ν : ℝ) :
    IsDensityRoot (bodyMeasure c γ ν) (ageμ c (-3 / 2))
      (fun p => Real.sqrt Real.pi * Concrete.ginv γ ν p) := by
  refine ⟨measurable_const.mul (ginv_measurable' γ ν),
    fun p => mul_pos sqrtPi_pos (ginv_pos' γ ν p), ?_⟩
  unfold bodyMeasure
  congr 1
  funext p
  rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]

/-- `π s^{-3/2} dς = (√π)² · s^{-3/2} dς`. -/
theorem root_src (c : ℝ) :
    IsDensityRoot (srcMeasure c) (ageμ c (-3 / 2)) (fun _ => Real.sqrt Real.pi) := by
  refine ⟨measurable_const, fun _ => sqrtPi_pos, ?_⟩
  show srcMeasure c = (ageμ c (-3 / 2)).withDensity fun _ => ENNReal.ofReal (Real.sqrt Real.pi ^ 2)
  rw [Real.sq_sqrt Real.pi_pos.le, withDensity_const]
  rfl

/-! ## 2. The isometries -/

/-- `StrG ≃ₗᵢ Z`, `T ↦ g⁻¹T` componentwise: `‖T‖_Str = ‖g⁻¹T₁‖_{Z_1} + ρ_b^{-1/2}‖g⁻¹T₂‖_{H_T}`
(source 5609, 2698-2700). -/
def strIso (c mZ ρb γ ν : ℝ) : StrG c mZ ρb γ ν ≃ₗᵢ[ℝ] Zsp c mZ ρb :=
  prodL1Iso (root_gainZ1 c mZ γ ν).rootEquiv (root_gainHT c ρb γ ν).rootEquiv

/-- `VelG ≃ₗᵢ H`, `w ↦ √π g⁻¹w`: `G(w) = R⁻¹‖g⁻¹𝒩_v w‖_{Y_2} = √π‖g⁻¹w‖_H`
(source 5143, 2685-2689). -/
def velIso (c γ ν : ℝ) : VelG c γ ν ≃ₗᵢ[ℝ] Hsp c := (root_body c γ ν).rootEquiv

/-- `SrcG ≃ₗᵢ H`, `f ↦ √π f`: `R⁻¹‖𝒩_v f‖_{Y_2} = √π‖f‖_H` (source 2683-2689). -/
def srcIso (c : ℝ) : SrcG c ≃ₗᵢ[ℝ] Hsp c := (root_src c).rootEquiv

section Coe

variable {c mZ ρb γ ν : ℝ}

theorem coeFn_strIso_fst (T : StrG c mZ ρb γ ν) :
    ((strIso c mZ ρb γ ν T).fst : Chart → Ten3) =ᵐ[z1Measure c mZ]
      fun p => Concrete.ginv γ ν p • (T.fst : Chart → Ten3) p :=
  (root_gainZ1 c mZ γ ν).coeFn_rootEquiv T.fst

theorem coeFn_strIso_snd (T : StrG c mZ ρb γ ν) :
    ((strIso c mZ ρb γ ν T).snd : Chart → Ten3) =ᵐ[htRhoMeasure c ρb]
      fun p => Concrete.ginv γ ν p • (T.snd : Chart → Ten3) p :=
  (root_gainHT c ρb γ ν).coeFn_rootEquiv T.snd

theorem coeFn_strIso_symm_fst (F : Zsp c mZ ρb) :
    (((strIso c mZ ρb γ ν).symm F).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      fun p => (Concrete.ginv γ ν p)⁻¹ • (F.fst : Chart → Ten3) p :=
  (root_gainZ1 c mZ γ ν).coeFn_rootEquiv_symm F.fst

theorem coeFn_strIso_symm_snd (F : Zsp c mZ ρb) :
    (((strIso c mZ ρb γ ν).symm F).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
      fun p => (Concrete.ginv γ ν p)⁻¹ • (F.snd : Chart → Ten3) p :=
  (root_gainHT c ρb γ ν).coeFn_rootEquiv_symm F.snd

theorem coeFn_velIso (w : VelG c γ ν) :
    (velIso c γ ν w : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      fun p => (Real.sqrt Real.pi * Concrete.ginv γ ν p) • (w : Chart → Merid) p :=
  (root_body c γ ν).coeFn_rootEquiv w

theorem coeFn_velIso_symm (u : Hsp c) :
    ((velIso c γ ν).symm u : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
      fun p => (Real.sqrt Real.pi * Concrete.ginv γ ν p)⁻¹ • (u : Chart → Merid) p :=
  (root_body c γ ν).coeFn_rootEquiv_symm u

theorem coeFn_srcIso (f : SrcG c) :
    (srcIso c f : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      fun p => Real.sqrt Real.pi • (f : Chart → Merid) p :=
  (root_src c).coeFn_rootEquiv f

end Coe

/-! ## 3. The gain maps on functions -/

section Gain

variable {c mZ ρb : ℝ}

theorem gainEquiv_fst (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (F : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν F).fst = gainLp (z1Measure c mZ) γ hν F.fst := rfl

theorem gainEquiv_snd (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (F : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν F).snd = gainLp (htRhoMeasure c ρb) γ hν F.snd := rfl

theorem coeFn_gainLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : Measure Chart)
    (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (f : Lp E 2 m) :
    (gainLp m γ hν f : Chart → E) =ᵐ[m] fun p => gainFun γ ν p • (f : Chart → E) p :=
  mulBdd_apply_ae (gainFun γ ν) (gainFun_measurable γ ν) (Real.exp (|γ| / ν)) (gainFun_le hν) f

theorem coeFn_gainLp_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : Measure Chart) (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (f : Lp E 2 m) :
    ((gainLp m γ hν).symm f : Chart → E) =ᵐ[m] fun p => gainInvFun γ ν p • (f : Chart → E) p :=
  mulBdd_apply_ae (gainInvFun γ ν) ((gainFun_measurable γ ν).inv) (Real.exp (|γ| / ν))
    (gainInvFun_le hν) f

theorem coeFn_gainH (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (u : Hsp c) :
    (gainH c γ hν u : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      fun p => gainFun γ ν p • (u : Chart → Merid) p :=
  coeFn_gainLp _ γ hν u

theorem coeFn_gainH_symm (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (u : Hsp c) :
    ((gainH c γ hν).symm u : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      fun p => gainInvFun γ ν p • (u : Chart → Merid) p :=
  coeFn_gainLp_symm _ γ hν u

/-- The stress `gainEquiv (strIso T) ∈ Z` is the function `T` itself (thin component). -/
theorem coeFn_zOfStr_fst (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (T : StrG c mZ ρb γ ν) :
    ((gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T)).fst : Chart → Ten3) =ᵐ[z1Measure c mZ]
      (T.fst : Chart → Ten3) := by
  rw [gainEquiv_fst]
  filter_upwards [coeFn_gainLp (z1Measure c mZ) γ hν (strIso c mZ ρb γ ν T).fst,
    coeFn_strIso_fst T] with p h1 h2
  rw [h1, h2, smul_smul, gainFun_mul_ginv, one_smul]

/-- The stress `gainEquiv (strIso T) ∈ Z` is the function `T` itself (repair component). -/
theorem coeFn_zOfStr_snd (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (T : StrG c mZ ρb γ ν) :
    ((gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T)).snd : Chart → Ten3) =ᵐ[htRhoMeasure c ρb]
      (T.snd : Chart → Ten3) := by
  rw [gainEquiv_snd]
  filter_upwards [coeFn_gainLp (htRhoMeasure c ρb) γ hν (strIso c mZ ρb γ ν T).snd,
    coeFn_strIso_snd T] with p h1 h2
  rw [h1, h2, smul_smul, gainFun_mul_ginv, one_smul]

/-- The velocity `(√π)⁻¹ gainH (velIso w) ∈ H` is the function `w` itself. -/
theorem coeFn_hOfVel (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (w : VelG c γ ν) :
    (((Real.sqrt Real.pi)⁻¹ • gainH c γ hν (velIso c γ ν w) : Hsp c) : Chart → Merid)
      =ᵐ[ageμ c (-3 / 2)] (w : Chart → Merid) := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt Real.pi)⁻¹ (gainH c γ hν (velIso c γ ν w)),
    coeFn_gainH γ hν (velIso c γ ν w), coeFn_velIso w] with p h1 h2 h3
  rw [h1, Pi.smul_apply, h2, h3, smul_smul, smul_smul]
  have h4 : (Real.sqrt Real.pi)⁻¹ * gainFun γ ν p * (Real.sqrt Real.pi * Concrete.ginv γ ν p)
      = 1 := by
    have := gainFun_mul_ginv γ ν p
    field_simp [sqrtPi_pos.ne']
    linarith
  rw [h4, one_smul]

/-- The force `(√π)⁻¹ srcIso f ∈ H` is the function `f` itself. -/
theorem coeFn_hOfSrc (f : SrcG c) :
    (((Real.sqrt Real.pi)⁻¹ • srcIso c f : Hsp c) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      (f : Chart → Merid) := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt Real.pi)⁻¹ (srcIso c f), coeFn_srcIso f] with p h1 h2
  rw [h1, Pi.smul_apply, h2, smul_smul, inv_mul_cancel₀ sqrtPi_pos.ne', one_smul]

end Gain

/-! ## 4. The transported operators -/

section Ops

variable {c mZ ρb : ℝ}

/-- `g⁻¹ M g : H → Z` for a velocity-to-stress map `M` (source 3875-3880). -/
def gainConjM (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (M : Hsp c →L[ℝ] Zsp c mZ ρb) :
    Hsp c →L[ℝ] Zsp c mZ ρb :=
  ((gainEquiv c mZ ρb γ hν).symm : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb) ∘L M ∘L
    (gainH c γ hν : Hsp c →L[ℝ] Hsp c)

/-- An operator on `Z` read on `StrG` through `strIso`: `strIso⁻¹ X strIso`. -/
def strConj (γ ν : ℝ) (X : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb) :
    StrG c mZ ρb γ ν →L[ℝ] StrG c mZ ρb γ ν :=
  ((strIso c mZ ρb γ ν).symm.toContinuousLinearEquiv : Zsp c mZ ρb →L[ℝ] StrG c mZ ρb γ ν) ∘L X ∘L
    ((strIso c mZ ρb γ ν).toContinuousLinearEquiv : StrG c mZ ρb γ ν →L[ℝ] Zsp c mZ ρb)

theorem strConj_apply (γ ν : ℝ) (X : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb) (T : StrG c mZ ρb γ ν) :
    strConj γ ν X T = (strIso c mZ ρb γ ν).symm (X (strIso c mZ ρb γ ν T)) := rfl

theorem norm_strConj_le (γ ν : ℝ) (X : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb) (T : StrG c mZ ρb γ ν) :
    ‖strConj γ ν X T‖ ≤ ‖X‖ * ‖T‖ := by
  rw [strConj_apply, LinearIsometryEquiv.norm_map]
  calc ‖X (strIso c mZ ρb γ ν T)‖ ≤ ‖X‖ * ‖strIso c mZ ρb γ ν T‖ := X.le_opNorm _
    _ = ‖X‖ * ‖T‖ := by rw [LinearIsometryEquiv.norm_map]

theorem strConj_one (γ ν : ℝ) : strConj (c := c) (mZ := mZ) (ρb := ρb) γ ν 1 = 1 := by
  ext1 T
  rw [strConj_apply]
  simp

theorem strConj_add (γ ν : ℝ) (X Y : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb) :
    strConj γ ν (X + Y) = strConj γ ν X + strConj γ ν Y := by
  ext1 T
  simp [strConj_apply]

/-- The body inverse `R_ε` (real form on `H`) acting on the same functions, `SrcG → VelG`
(source 4084-4086: `u_ε = M_U R_ε f`). -/
def bodyG (Reps : Hsp c →L[ℝ] Hsp c) (γ : ℝ) {ν : ℝ} (hν : 0 < ν) : SrcG c →L[ℝ] VelG c γ ν :=
  ((velIso c γ ν).symm.toContinuousLinearEquiv : Hsp c →L[ℝ] VelG c γ ν) ∘L
    ((gainH c γ hν).symm : Hsp c →L[ℝ] Hsp c) ∘L Reps ∘L
    ((srcIso c).toContinuousLinearEquiv : SrcG c →L[ℝ] Hsp c)

namespace NearOps

variable (o : NearOps c mZ ρb) (γ : ℝ) {ν : ℝ} (hν : 0 < ν)

/-- `M_U` on the return spaces: `(√π)⁻¹ strIso⁻¹ (g⁻¹M_U g) velIso` (the exact multiplier acting on
the same functions, source 3876-3878, 5779-5782). -/
def MG : VelG c γ ν →L[ℝ] StrG c mZ ρb γ ν :=
  (Real.sqrt Real.pi)⁻¹ •
    (((strIso c mZ ρb γ ν).symm.toContinuousLinearEquiv : Zsp c mZ ρb →L[ℝ] StrG c mZ ρb γ ν) ∘L
      gainConjM γ hν o.MU ∘L
      ((velIso c γ ν).toContinuousLinearEquiv : VelG c γ ν →L[ℝ] Hsp c))

/-- `S_N` on the return spaces: `√π velIso⁻¹ (g⁻¹S_N g) strIso` (source 3911-3920, 5785). -/
def SNG : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν :=
  Real.sqrt Real.pi •
    (((velIso c γ ν).symm.toContinuousLinearEquiv : Hsp c →L[ℝ] VelG c γ ν) ∘L
      gainConjS γ hν o.SN ∘L
      ((strIso c mZ ρb γ ν).toContinuousLinearEquiv : StrG c mZ ρb γ ν →L[ℝ] Zsp c mZ ρb))

/-- `D_N⁻¹` on the return spaces: `strIso⁻¹ (G⁻¹ D_N⁻¹ G) strIso`, `D_N⁻¹ = Ring.inverse D_N`
(source 3914-3917, 5787). -/
def DNinvG : StrG c mZ ρb γ ν →L[ℝ] StrG c mZ ρb γ ν :=
  strConj γ ν (conjG (gainEquiv c mZ ρb γ hν) (Ring.inverse o.DN))

/-- The flat forced column `T₀ = D₀⁻¹M₀R₀f` on the return spaces, `SrcG → StrG`, acting on the same
functions: `(√π)⁻¹ strIso⁻¹ G⁻¹ D₀⁻¹ M₀ R₀ srcIso` (source 4109-4111). -/
def flatColG (R0 : Hsp c →L[ℝ] Hsp c) : SrcG c →L[ℝ] StrG c mZ ρb γ ν :=
  (Real.sqrt Real.pi)⁻¹ •
    (((strIso c mZ ρb γ ν).symm.toContinuousLinearEquiv : Zsp c mZ ρb →L[ℝ] StrG c mZ ρb γ ν) ∘L
      ((gainEquiv c mZ ρb γ hν).symm : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb) ∘L
      Ring.inverse o.D0 ∘L o.M0 ∘L R0 ∘L
      ((srcIso c).toContinuousLinearEquiv : SrcG c →L[ℝ] Hsp c))

theorem MG_apply (w : VelG c γ ν) :
    o.MG γ hν w = (Real.sqrt Real.pi)⁻¹ • (strIso c mZ ρb γ ν).symm
      ((gainEquiv c mZ ρb γ hν).symm (o.MU (gainH c γ hν (velIso c γ ν w)))) := rfl

theorem SNG_apply (T : StrG c mZ ρb γ ν) :
    o.SNG γ hν T = Real.sqrt Real.pi • (velIso c γ ν).symm
      ((gainH c γ hν).symm (o.SN (gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T)))) := rfl

theorem DNinvG_apply (T : StrG c mZ ρb γ ν) :
    o.DNinvG γ hν T = (strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm
      (Ring.inverse o.DN (gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T)))) := rfl

theorem flatColG_apply (R0 : Hsp c →L[ℝ] Hsp c) (f : SrcG c) :
    o.flatColG γ hν R0 f = (Real.sqrt Real.pi)⁻¹ • (strIso c mZ ρb γ ν).symm
      ((gainEquiv c mZ ρb γ hν).symm (Ring.inverse o.D0 (o.M0 (R0 (srcIso c f))))) := rfl

/-- `‖D_N⁻¹T‖_Str ≤ ‖G⁻¹D_N⁻¹G‖_{Z→Z} ‖T‖_Str`. -/
theorem norm_DNinvG_le (T : StrG c mZ ρb γ ν) :
    ‖o.DNinvG γ hν T‖ ≤ ‖conjG (gainEquiv c mZ ρb γ hν) (Ring.inverse o.DN)‖ * ‖T‖ :=
  norm_strConj_le γ ν _ T

/-- `‖S_N T‖_Vel ≤ √π ‖g⁻¹S_N g‖_{Z→H} ‖T‖_Str`. -/
theorem norm_SNG_le (T : StrG c mZ ρb γ ν) :
    ‖o.SNG γ hν T‖ ≤ Real.sqrt Real.pi * ‖gainConjS γ hν o.SN‖ * ‖T‖ := by
  rw [SNG_apply, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    LinearIsometryEquiv.norm_map, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have h : (gainH c γ hν).symm (o.SN (gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T))) =
      gainConjS γ hν o.SN (strIso c mZ ρb γ ν T) := rfl
  rw [h]
  calc ‖gainConjS γ hν o.SN (strIso c mZ ρb γ ν T)‖
      ≤ ‖gainConjS γ hν o.SN‖ * ‖strIso c mZ ρb γ ν T‖ := (gainConjS γ hν o.SN).le_opNorm _
    _ = ‖gainConjS γ hν o.SN‖ * ‖T‖ := by rw [LinearIsometryEquiv.norm_map]

/-- `M_U S_N` on the return spaces is `strIso⁻¹ (G⁻¹ M_U S_N G) strIso` (the `√π` factors cancel). -/
theorem MG_comp_SNG :
    (o.MG γ hν).comp (o.SNG γ hν) = strConj γ ν (conjG (gainEquiv c mZ ρb γ hν) (o.MU.comp o.SN)) := by
  ext1 T
  rw [ContinuousLinearMap.comp_apply, SNG_apply, MG_apply, strConj_apply]
  simp only [map_smul, LinearIsometryEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    smul_smul, inv_mul_cancel₀ sqrtPi_pos.ne', one_smul]
  rfl

/-- `I + M S_N = strIso⁻¹ (G⁻¹ D_N G) strIso` on the return spaces (source 3914, 5785). -/
theorem one_add_MG_SNG :
    1 + (o.MG γ hν).comp (o.SNG γ hν) = strConj γ ν (conjG (gainEquiv c mZ ρb γ hν) o.DN) := by
  rw [MG_comp_SNG]
  have h : conjG (gainEquiv c mZ ρb γ hν) o.DN =
      1 + conjG (gainEquiv c mZ ρb γ hν) (o.MU.comp o.SN) := by
    ext1 F
    simp [conjG, NearOps.DN]
  rw [h, strConj_add, strConj_one]

end NearOps

end Ops

end UnforcedLeray.Short.PartIIIb.NearInst
