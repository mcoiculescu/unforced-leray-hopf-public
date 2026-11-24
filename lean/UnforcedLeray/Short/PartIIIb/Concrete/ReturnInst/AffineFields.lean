import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets
import UnforcedLeray.Short.PartIIIb.Concrete.AffineBoundSpaces

/-!
# The physical affine fields `ĥ_A, F_A, E_A` as continuous linear maps (source 4951-5016)

Source of record: `the November 2 reference manuscript` (73 pages).

Step (1) of `ORG:return-concrete/instance`, in the part that does not depend on the concrete
space `AffSp` (task `PartIII-b:C/ret/1`) nor on the physical layer: the fields of
`Concrete/ReturnAff.lean` become continuous linear maps
`hA : Aff →L VelG`, `FA, EA : Aff →L SrcG` for any normed `Aff` with a linear inclusion
`ι : Aff →ₗ (ℝ → Mat3)` into `𝒜` (`∀ A, IsAffElem a_s (ι A)`), and these maps satisfy
`IsAffinePinned` by construction.  At the instance, `Aff = AffSp a_s` and `ι` is the subtype map.

## Construction

* `IsL2Family m F` : `x ↦ F x` is `L²(m)`, linear a.e. and bounded; `IsL2Family.toCLM` is the
  continuous linear map `x ↦ [F x]` into `Lp E 2 m` (`toCLM_ae`, `norm_toCLM`).
* `hAcoef, FAcoef, EAcoef` : the coefficient fields `b = s^{-1/2}·(physical field)`,
  `(r,z)` components, exactly the right sides of `IsAffinePinned` (`Concrete/ReturnOps.lean`).
* `AffineFieldData as ν μ ε γ χf ι` : the three coefficient families are `L²` families, in the
  gained body measure for `ĥ_A` (`VelG`) and the ungained one for `F_A, E_A` (`SrcG`);
  `hAL, FAL, EAL` are the maps, `isAffinePinned_of` the pin.

## Source facts (leaves)

* linearity (source 4985, "All these maps depend linearly on `A`"; the lattice sums and their
  required derivatives converge by Gaussian decay, 4978): `HhatCoefLinear`, `FACoefLinear`,
  `EACoefLinear`, pointwise on `s > 0`, with the sub-facts `AyDiffAt`, `FATermSummable`,
  `EATermSummable`, `HpPsiTermSummable`, `PsipADiff`;
* the first line of `ret:general-affine-bounds` (source 5009-5016, proof 5063-5079), per field:
  `HhatCoefBound`, `FACoefBound`, `EACoefBound`
  (`R⁻¹‖F_A‖_{Y_2} = ‖FAcoef‖_{L²(π s^{-3/2} dς)} ≤ P_ν M(A)`, `M(A) = affM ν χ_f A`).

Proved here: `affineFieldData_of` (the data at one regime from the leaves and the generic
envelope `M(A) ≤ C‖A‖`, source 5089-5091, supplied as a hypothesis) and `affineFieldNorms_le`
(the `F_A, E_A, ĥ_A` part of `GeneralAffineBounds` for the constructed maps).  The gradient
`∇ĥ_A` (`ORG:stmt/PartIII-b/GeneralAffineBounds/grad-pin`) and `𝔯_A` (`IsRAPinned`,
`Concrete/PhysLayer.lean`) are not treated here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The chart measures live on `s > 0`; the gained body measure is below the ungained one -/

/-- `ageμ c a` is carried by `s > 0`. -/
theorem ae_ageμ_fst_pos (c a : ℝ) : ∀ᵐ p ∂(ageμ c a), 0 < p.1 := by
  have h1 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ a)), 0 < s :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  unfold ageμ
  exact Measure.quasiMeasurePreserving_fst.ae h1

theorem ae_srcMeasure_fst_pos (c : ℝ) : ∀ᵐ p ∂(srcMeasure c), 0 < p.1 :=
  Measure.ae_smul_measure (ae_ageμ_fst_pos c _) _

theorem ae_bodyMeasure_fst_pos (c γ ν : ℝ) : ∀ᵐ p ∂(bodyMeasure c γ ν), 0 < p.1 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_ageμ_fst_pos c _)

theorem ginv_nonneg (γ ν : ℝ) (p : Chart) : 0 ≤ ginv γ ν p := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  exact inv_nonneg.2 (Real.exp_pos _).le

/-- `g⁻¹ ≤ 1` on the age range (source 3875, 5117). -/
theorem ginv_le_one {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 ≤ ν) (p : Chart) : ginv γ ν p ≤ 1 := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  have hs : 0 ≤ max p.1 0 := le_max_right _ _
  have hd : 0 < 1 + ν * max p.1 0 := by nlinarith
  have h1 : 0 ≤ γ * max p.1 0 / (1 + ν * max p.1 0) := div_nonneg (mul_nonneg hγ hs) hd.le
  exact inv_le_one_of_one_le₀ (Real.one_le_exp h1)

/-- The gained body norm is at most the ungained one: `π g⁻² s^{-3/2} dς ≤ π s^{-3/2} dς`
(source 5009-5016 read in the gained norm of `Vel`, StatementsA module header). -/
theorem bodyMeasure_le_srcMeasure (c : ℝ) {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 ≤ ν) :
    bodyMeasure c γ ν ≤ srcMeasure c := by
  unfold bodyMeasure srcMeasure
  rw [← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards with p
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 := ginv_nonneg γ ν p
  have h1 := ginv_le_one hγ hν p
  have h2 : ginv γ ν p ^ 2 ≤ 1 := by nlinarith
  nlinarith [Real.pi_pos]

/-! ## 2. Continuous linear maps into `L²` from a.e.-linear bounded families -/

section L2Family

variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `x ↦ F x` is an `L²(m)` family, linear almost everywhere and bounded. -/
structure IsL2Family (m : Measure Chart) (F : X → Chart → E) : Prop where
  memLp : ∀ x, MemLp (F x) 2 m
  add : ∀ x y, F (x + y) =ᵐ[m] F x + F y
  smul : ∀ (r : ℝ) (x : X), F (r • x) =ᵐ[m] r • F x
  bound : ∃ C : ℝ, ∀ x, eLpNorm (F x) 2 m ≤ ENNReal.ofReal (C * ‖x‖)

namespace IsL2Family

variable {m : Measure Chart} {F : X → Chart → E}

/-- `x ↦ [F x]` as a linear map into `L²(m)`. -/
def toLinear (h : IsL2Family m F) : X →ₗ[ℝ] Lp E 2 m where
  toFun x := (h.memLp x).toLp (F x)
  map_add' x y := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (h.add x y)
  map_smul' r x := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (h.smul r x)

/-- `x ↦ [F x]` as a continuous linear map into `L²(m)`. -/
def toCLM (h : IsL2Family m F) : X →L[ℝ] Lp E 2 m :=
  h.toLinear.mkContinuous (max (Classical.choose h.bound) 0) fun x => by
    show ‖(h.memLp x).toLp (F x)‖ ≤ max (Classical.choose h.bound) 0 * ‖x‖
    rw [Lp.norm_toLp]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (Classical.choose_spec h.bound x)) ?_
    rw [ENNReal.toReal_ofReal']
    exact max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      (mul_nonneg (le_max_right _ _) (norm_nonneg _))

theorem toCLM_ae (h : IsL2Family m F) (x : X) : (h.toCLM x : Chart → E) =ᵐ[m] F x :=
  (h.memLp x).coeFn_toLp

theorem norm_toCLM (h : IsL2Family m F) (x : X) :
    ‖h.toCLM x‖ = (eLpNorm (F x) 2 m).toReal :=
  Lp.norm_toLp _ (h.memLp x)

/-- An `L²` family for a measure is one for every smaller measure. -/
theorem mono {m' : Measure Chart} (h : IsL2Family m F) (hm : m' ≤ m) : IsL2Family m' F where
  memLp x := (h.memLp x).mono_measure hm
  add x y := (h.add x y).filter_mono (ae_mono hm)
  smul r x := (h.smul r x).filter_mono (ae_mono hm)
  bound := by
    obtain ⟨C, hC⟩ := h.bound
    exact ⟨C, fun x => (eLpNorm_mono_measure _ hm).trans (hC x)⟩

end IsL2Family

end L2Family

/-! ## 3. The coefficient fields (source 4980-4985, convention of `IsAffinePinned`) -/

/-- `b = s^{-1/2} ĥ_A`, `(r,z)` components (source 4980). -/
def hAcoef (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (p : Chart) : Merid :=
  merOf ((Real.sqrt p.1)⁻¹ • hhatA ν ε χf A p.1 p.2)

/-- `b = s^{-1/2} F_A = s f_A`, `(r,z)` components (source 4981). -/
def FAcoef (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (p : Chart) : Merid :=
  merOf ((Real.sqrt p.1)⁻¹ • FA ν μ χf A p.1 p.2)

/-- `b = s^{-1/2} E_A = s e_A`, `(r,z)` components (source 4981). -/
def EAcoef (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (p : Chart) : Merid :=
  merOf ((Real.sqrt p.1)⁻¹ • EA ν μ χf A p.1 p.2)

theorem affMerOf_add (u v : Vec3) : merOf (u + v) = merOf u + merOf v := by
  ext i; fin_cases i <;> simp [merOf]

theorem affMerOf_smul (r : ℝ) (v : Vec3) : merOf (r • v) = r • merOf v := by
  ext i; fin_cases i <;> simp [merOf]

/-- `M(A) ≥ 0`. -/
theorem affM_nonneg (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : 0 ≤ affM ν χ A := by
  unfold affM
  apply Real.sSup_nonneg
  rintro _ ⟨s, hs, rfl⟩
  unfold affSum frob
  exact mul_nonneg (Real.rpow_nonneg hs.1.le _)
    (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _)

/-! ## 4. Source facts -/

/-- `A ↦ ĥ_A` is linear on `𝒜` (source 4985), at every chart point with `s > 0`. -/
def HhatCoefLinear (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν ε : ℝ), 0 < ν → ∀ (A A' : ℝ → Mat3) (r : ℝ), IsAffElem as A → IsAffElem as A' →
    ∀ p : Chart, 0 < p.1 →
      hAcoef ν ε χf (A + A') p = hAcoef ν ε χf A p + hAcoef ν ε χf A' p ∧
      hAcoef ν ε χf (r • A) p = r • hAcoef ν ε χf A p

/-- `A ↦ F_A` is linear on `𝒜` (source 4985), at every chart point with `s > 0`. -/
def FACoefLinear (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν μ : ℝ), 0 < ν → ∀ (A A' : ℝ → Mat3) (r : ℝ), IsAffElem as A → IsAffElem as A' →
    ∀ p : Chart, 0 < p.1 →
      FAcoef ν μ χf (A + A') p = FAcoef ν μ χf A p + FAcoef ν μ χf A' p ∧
      FAcoef ν μ χf (r • A) p = r • FAcoef ν μ χf A p

/-- `A ↦ E_A` is linear on `𝒜` (source 4985), at every chart point with `s > 0`. -/
def EACoefLinear (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν μ : ℝ), 0 < ν → ∀ (A A' : ℝ → Mat3) (r : ℝ), IsAffElem as A → IsAffElem as A' →
    ∀ p : Chart, 0 < p.1 →
      EAcoef ν μ χf (A + A') p = EAcoef ν μ χf A p + EAcoef ν μ χf A' p ∧
      EAcoef ν μ χf (r • A) p = r • EAcoef ν μ χf A p

/-- `A^y = χ_f A` is differentiable at every `s > 0` for `A ∈ 𝒜` (`A` is `C^6` on the open set
`(0,∞)`, source 4741-4745; `χ_f(s) = χ̂_f(νs)` is `C^∞`, 4953-4958). -/
def AyDiffAt (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν : ℝ) (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → DifferentiableAt ℝ (Ay ν χf A) s

/-- Gaussian decay of the lattice terms of `f_A` (source 4970, 4978): for `ν > 0`, `s > 0`
(age `a = 1 + νs > 1`, lattice spacing `c = ν⁻²`), `j ↦ fATerm … j` is summable; only the matrix
`B(s)` enters, so no condition on `A` is needed. -/
def FATermSummable : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
    Summable (fATerm ν μ χ A s x)

/-- Gaussian decay of the lattice terms of `e_A` (source 4971-4972, 4978). -/
def EATermSummable : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
    Summable (eATerm ν μ χ A s x)

/-- Gaussian decay of the lattice terms of `h^p_A` and `ψ^p_A` (source 4973-4975, 4978). -/
def HpPsiTermSummable : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
    Summable (hpATerm ν χ A s x) ∧ Summable (psipATerm ν χ A s x)

/-- `ψ^p_A` is differentiable in `x` and in `s` (source 4978: "The sums and their required
derivatives converge by Gaussian decay"; `A ∈ 𝒜` is `C^6` in `s`), as needed for
`𝒦ψ^p_A = η∂_ηψ^p_A + 2s∂_sψ^p_A` in `ĥ_A` (source 4979-4980). -/
def PsipADiff (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
    DifferentiableAt ℝ (psipA ν χf A s) x ∧ DifferentiableAt ℝ (fun s' => psipA ν χf A s' x) s

/-- First line of `ret:general-affine-bounds` for `ĥ_A` (source 5009-5016, proof 5063-5079):
for `0 < ε, ν ≤ 1`, `R⁻¹‖ĥ_A‖_{Y_2} = ‖hAcoef‖_{L²(π s^{-3/2} dς)} ≤ P_ν M(A)`, `P_ν = Cν^{-k}`,
`c = ν⁻²` (the ungained norm; the gained norm of `VelG` is smaller,
`bodyMeasure_le_srcMeasure`). -/
def HhatCoefBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (ν ε : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
    ∀ A : ℝ → Mat3, IsAffElem as A →
      MemLp (hAcoef ν ε χf A) 2 (srcMeasure (cOf ν)) ∧
      eLpNorm (hAcoef ν ε χf A) 2 (srcMeasure (cOf ν)) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * affM ν χf A)

/-- First line of `ret:general-affine-bounds` for `F_A` (source 5009-5016, proof 5063-5079),
uniformly for `0 < ν ≤ 1` and `μ ∈ K ⋐ (0,1/4)` (source 4962-4963):
`R⁻¹‖F_A‖_{Y_2} = ‖FAcoef‖_{L²(π s^{-3/2} dς)} ≤ P_ν M(A)`. -/
def FACoefBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) →
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (ν μ : ℝ), 0 < ν → ν ≤ 1 → μ ∈ K →
      ∀ A : ℝ → Mat3, IsAffElem as A →
        MemLp (FAcoef ν μ χf A) 2 (srcMeasure (cOf ν)) ∧
        eLpNorm (FAcoef ν μ χf A) 2 (srcMeasure (cOf ν)) ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k * affM ν χf A)

/-- First line of `ret:general-affine-bounds` for `E_A` (source 5009-5016, proof 5063-5079),
uniformly for `0 < ν ≤ 1` and `μ ∈ K ⋐ (0,1/4)`. -/
def EACoefBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) →
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (ν μ : ℝ), 0 < ν → ν ≤ 1 → μ ∈ K →
      ∀ A : ℝ → Mat3, IsAffElem as A →
        MemLp (EAcoef ν μ χf A) 2 (srcMeasure (cOf ν)) ∧
        eLpNorm (EAcoef ν μ χf A) 2 (srcMeasure (cOf ν)) ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k * affM ν χf A)

/-! ## 5. The fields at one regime -/

section Regime

variable {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]

/-- At one regime `(ν, μ, ε)` (gain rate `γ`, `c = ν⁻²`), the three affine coefficient families
are `L²` families on `Aff` through `ι`: `ĥ_A` in the gained body measure of `VelG`, `F_A, E_A` in
the ungained body measure of `SrcG`. -/
structure AffineFieldData (as ν μ ε γ : ℝ) (χf : ℝ → ℝ) (ι : Aff →ₗ[ℝ] (ℝ → Mat3)) : Prop where
  hA : IsL2Family (bodyMeasure (cOf ν) γ ν) fun A : Aff => hAcoef ν ε χf (ι A)
  FA : IsL2Family (srcMeasure (cOf ν)) fun A : Aff => FAcoef ν μ χf (ι A)
  EA : IsL2Family (srcMeasure (cOf ν)) fun A : Aff => EAcoef ν μ χf (ι A)

namespace AffineFieldData

variable {as ν μ ε γ : ℝ} {χf : ℝ → ℝ} {ι : Aff →ₗ[ℝ] (ℝ → Mat3)}

/-- `A ↦ ĥ_A` (source 4980). -/
def hAL (h : AffineFieldData as ν μ ε γ χf ι) : Aff →L[ℝ] VelG (cOf ν) γ ν := h.hA.toCLM

/-- `A ↦ F_A` (source 4981). -/
def FAL (h : AffineFieldData as ν μ ε γ χf ι) : Aff →L[ℝ] SrcG (cOf ν) := h.FA.toCLM

/-- `A ↦ E_A` (source 4981). -/
def EAL (h : AffineFieldData as ν μ ε γ χf ι) : Aff →L[ℝ] SrcG (cOf ν) := h.EA.toCLM

/-- A `ReturnBase` whose affine fields are the constructed maps satisfies `IsAffinePinned`. -/
theorem isAffinePinned_of [CompleteSpace Aff] {mZ ρb : ℝ} (h : AffineFieldData as ν μ ε γ χf ι)
    (B : ReturnBase (cOf ν) mZ ρb γ ν Aff) (e1 : B.hA = h.hAL) (e2 : B.FA = h.FAL)
    (e3 : B.EA = h.EAL) : IsAffinePinned B ι χf μ ε := fun A => by
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact h.hA.toCLM_ae A
  · rw [e2]; exact h.FA.toCLM_ae A
  · rw [e3]; exact h.EA.toCLM_ae A

end AffineFieldData

/-- From the leaves, the affine field data at one regime `0 < ν, ε ≤ 1`, `μ ∈ K ⋐ (0,1/4)`,
`γ ≥ 0`, given the generic envelope `M(ιA) ≤ C_env ‖A‖` (source 5089-5091:
`M(A) ≤ Ce^{1.1a_s/ν}‖A‖_𝒜`). -/
theorem affineFieldData_of {as ν μ ε γ : ℝ} {χf : ℝ → ℝ} {ι : Aff →ₗ[ℝ] (ℝ → Mat3)}
    (hι : ∀ A, IsAffElem as (ι A)) (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hγ : 0 ≤ γ) {K : Set ℝ} (hK : IsCompact K) (hK' : K ⊆ Ioo 0 (1 / 4)) (hμ : μ ∈ K)
    (Cenv : ℝ) (henv : ∀ A, affM ν χf (ι A) ≤ Cenv * ‖A‖)
    (lh : HhatCoefLinear as χf) (lF : FACoefLinear as χf) (lE : EACoefLinear as χf)
    (bh : HhatCoefBound as χf) (bF : FACoefBound as χf) (bE : EACoefBound as χf) :
    AffineFieldData as ν μ ε γ χf ι := by
  have hb : ∀ (C : ℝ) (k : ℕ), 0 ≤ C → ∀ A : Aff,
      ENNReal.ofReal (C * ν⁻¹ ^ k * affM ν χf (ι A)) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * Cenv * ‖A‖) := by
    intro C k hC A
    refine ENNReal.ofReal_le_ofReal ?_
    have hCk : 0 ≤ C * ν⁻¹ ^ k := mul_nonneg hC (pow_nonneg (inv_nonneg.2 hν.le) _)
    calc C * ν⁻¹ ^ k * affM ν χf (ι A) ≤ C * ν⁻¹ ^ k * (Cenv * ‖A‖) :=
          mul_le_mul_of_nonneg_left (henv A) hCk
      _ = C * ν⁻¹ ^ k * Cenv * ‖A‖ := by ring
  obtain ⟨Ch, kh, hCh, bh⟩ := bh
  obtain ⟨CF, kF, hCF, bF⟩ := bF K hK hK'
  obtain ⟨CE, kE, hCE, bE⟩ := bE K hK hK'
  have hsrc : ∀ᵐ p ∂(srcMeasure (cOf ν)), 0 < p.1 := ae_srcMeasure_fst_pos _
  refine ⟨?_, ?_, ?_⟩
  · have hA0 : IsL2Family (srcMeasure (cOf ν)) fun A : Aff => hAcoef ν ε χf (ι A) :=
      { memLp := fun A => (bh ν ε hν hν1 hε hε1 _ (hι A)).1
        add := fun A A' => by
          filter_upwards [hsrc] with p hp
          simp only [map_add, Pi.add_apply]
          exact (lh ν ε hν _ _ 1 (hι A) (hι A') p hp).1
        smul := fun r A => by
          filter_upwards [hsrc] with p hp
          simp only [map_smul, Pi.smul_apply]
          exact (lh ν ε hν _ _ r (hι A) (hι A) p hp).2
        bound := ⟨Ch * ν⁻¹ ^ kh * Cenv, fun A =>
          (bh ν ε hν hν1 hε hε1 _ (hι A)).2.trans (hb Ch kh hCh A)⟩ }
    exact hA0.mono (bodyMeasure_le_srcMeasure _ hγ hν.le)
  · exact
      { memLp := fun A => (bF ν μ hν hν1 hμ _ (hι A)).1
        add := fun A A' => by
          filter_upwards [hsrc] with p hp
          simp only [map_add, Pi.add_apply]
          exact (lF ν μ hν _ _ 1 (hι A) (hι A') p hp).1
        smul := fun r A => by
          filter_upwards [hsrc] with p hp
          simp only [map_smul, Pi.smul_apply]
          exact (lF ν μ hν _ _ r (hι A) (hι A) p hp).2
        bound := ⟨CF * ν⁻¹ ^ kF * Cenv, fun A =>
          (bF ν μ hν hν1 hμ _ (hι A)).2.trans (hb CF kF hCF A)⟩ }
  · exact
      { memLp := fun A => (bE ν μ hν hν1 hμ _ (hι A)).1
        add := fun A A' => by
          filter_upwards [hsrc] with p hp
          simp only [map_add, Pi.add_apply]
          exact (lE ν μ hν _ _ 1 (hι A) (hι A') p hp).1
        smul := fun r A => by
          filter_upwards [hsrc] with p hp
          simp only [map_smul, Pi.smul_apply]
          exact (lE ν μ hν _ _ r (hι A) (hι A) p hp).2
        bound := ⟨CE * ν⁻¹ ^ kE * Cenv, fun A =>
          (bE ν μ hν hν1 hμ _ (hι A)).2.trans (hb CE kE hCE A)⟩ }

end Regime

/-- The `F_A, E_A, ĥ_A` part of the first line of `ret:general-affine-bounds` (source 5009-5016)
for the constructed maps, uniformly for `0 < ν, ε ≤ 1`, `γ ≥ 0`, `μ ∈ K ⋐ (0,1/4)`:
`‖F_A‖ + ‖E_A‖ + ‖ĥ_A‖ ≤ Cν^{-k} M(A)` in the norms of `SrcG`, `SrcG`, `VelG`. -/
theorem affineFieldNorms_le {as : ℝ} {χf : ℝ → ℝ} (bh : HhatCoefBound as χf)
    (bF : FACoefBound as χf) (bE : EACoefBound as χf) {K : Set ℝ} (hK : IsCompact K)
    (hK' : K ⊆ Ioo 0 (1 / 4)) :
    ∃ (C : ℝ) (k : ℕ), ∀ (ν μ ε γ : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 ≤ γ → μ ∈ K →
      ∀ {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] (ι : Aff →ₗ[ℝ] (ℝ → Mat3)),
      (∀ A, IsAffElem as (ι A)) → ∀ (h : AffineFieldData as ν μ ε γ χf ι) (A : Aff),
        ‖h.FAL A‖ + ‖h.EAL A‖ + ‖h.hAL A‖ ≤ C * ν⁻¹ ^ k * affM ν χf (ι A) := by
  obtain ⟨Ch, kh, hCh, bh⟩ := bh
  obtain ⟨CF, kF, hCF, bF⟩ := bF K hK hK'
  obtain ⟨CE, kE, hCE, bE⟩ := bE K hK hK'
  refine ⟨CF + CE + Ch, kF + kE + kh, ?_⟩
  intro ν μ ε γ hν hν1 hε hε1 hγ hμ Aff _ _ ι hι h A
  have hM := affM_nonneg ν χf (ι A)
  have h1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  have hpow : ∀ j : ℕ, j ≤ kF + kE + kh → ν⁻¹ ^ j ≤ ν⁻¹ ^ (kF + kE + kh) :=
    fun j hj => pow_le_pow_right₀ h1 hj
  have hP : ∀ j : ℕ, 0 ≤ ν⁻¹ ^ j := fun j => pow_nonneg (inv_nonneg.2 hν.le) _
  have eF : ‖h.FAL A‖ ≤ CF * ν⁻¹ ^ kF * affM ν χf (ι A) := by
    rw [AffineFieldData.FAL, IsL2Family.norm_toCLM]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hCF (hP _)) hM)
      (bF ν μ hν hν1 hμ _ (hι A)).2
  have eE : ‖h.EAL A‖ ≤ CE * ν⁻¹ ^ kE * affM ν χf (ι A) := by
    rw [AffineFieldData.EAL, IsL2Family.norm_toCLM]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hCE (hP _)) hM)
      (bE ν μ hν hν1 hμ _ (hι A)).2
  have eh : ‖h.hAL A‖ ≤ Ch * ν⁻¹ ^ kh * affM ν χf (ι A) := by
    rw [AffineFieldData.hAL, IsL2Family.norm_toCLM]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hCh (hP _)) hM)
      ((eLpNorm_mono_measure _ (bodyMeasure_le_srcMeasure _ hγ hν.le)).trans
        (bh ν ε hν hν1 hε hε1 _ (hι A)).2)
  have sF := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hpow kF (by omega)) hCF) hM
  have sE := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hpow kE (by omega)) hCE) hM
  have sh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hpow kh (by omega)) hCh) hM
  calc ‖h.FAL A‖ + ‖h.EAL A‖ + ‖h.hAL A‖
      ≤ CF * ν⁻¹ ^ kF * affM ν χf (ι A) + CE * ν⁻¹ ^ kE * affM ν χf (ι A) +
          Ch * ν⁻¹ ^ kh * affM ν χf (ι A) := by linarith
    _ ≤ CF * ν⁻¹ ^ (kF + kE + kh) * affM ν χf (ι A) +
          CE * ν⁻¹ ^ (kF + kE + kh) * affM ν χf (ι A) +
          Ch * ν⁻¹ ^ (kF + kE + kh) * affM ν χf (ι A) := by linarith
    _ = (CF + CE + Ch) * ν⁻¹ ^ (kF + kE + kh) * affM ν χf (ι A) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
