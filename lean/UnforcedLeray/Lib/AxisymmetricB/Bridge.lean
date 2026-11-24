import UnforcedLeray.Lib.AxisymmetricB.Unitary
import UnforcedLeray.Lib.FreeStressCouplings.ProdLp
import UnforcedLeray.Lib.PhaseSpace.Test

/-!
# AX04 (bridge): the joint phase space `L²(phaseμ P; ℝ³)` inside D2's Bochner `Y₂`


§5 Layer 3, target AX04 (`Jv : … →ₗᵢ[ℝ] Y2 P`), decision D2 of `scoping/README.md` §3
(`Y_q = L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))`, `PhaseSpace.Yq`). Blueprint units served: B0417
(`eq:m4-free-spaces`, tex 7272–7297: `J_v` maps into the period-averaged `Y₂`), B0219
(tex 3256–3268: normalized phase measure, period `P = 2εc`). The phase space `Y₂` is defined at
tex 7313–7317 (`L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))`, normalized Haar measure in the phase).

`Jv.lean` builds `J_v` into the joint space `L²(phaseμ P; ℝ³)`, `phaseμ P = P⁻¹ dτ|_{(0,P]} ⊗ dy`.
This file identifies that space isometrically with a real subspace of `Y₂ = Yq P 2`:

* `cplxV : ℝ³ →L[ℝ] ℂ³` (`v ↦ v + 0i`, `norm_cplxV`) and `cplxLp P`, its action on
  `L²(phaseμ P)`; adapted from `cplxL` of

* `phaseRep P : ℝ/Pℤ → (0, P]` and `measurePreserving_phaseRep` (Haar probability measure to
  `P⁻¹ dτ|_{(0,P]}`), adapted from the same file (lines 203–229) and from
  `measurePreserving_phase` of `Units/B0005/Spaces.lean` (lines 66–74);
* `toY2 P : L²(phaseμ P; ℝ³) →ₗᵢ[ℝ] Y₂`, the composite of the complexification, the change of
  phase variable `(θ, y) ↦ (phaseRep θ, y)` and the Fubini isometry
  `FreeStress.prodLpEquiv : L²(ν ⊗ μ) ≃ L²(ν; L²(μ))`, with the slice formulas `toY2_ae`
  (phase on the circle) and `toY2_ae_Ioc` (phase time `t ∈ (0, P]`):
  `(toY2 U)(t mod P) = U(t, ·)` (complexified) a.e., for a.e. `t ∈ (0, P]`;
* `JvY2 : H →ₗᵢ[ℝ] Y₂`, `J_v` read in `Y₂` (B0417), with `JvY2_ae`.

Only real-linearity is claimed: `Y₂` is complex, the image of `toY2` is the real subspace of
fields with real values. Status: infrastructure; Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace UnforcedLeray.Axi

open UnforcedLeray.PhaseSpace (CVec3 Yq)

/-! ### Complexification -/

/-- The complexification `v ↦ v + 0i` of `ℝ³` into `ℂ³`, a real-linear isometry
(adapted from `Units/B0005/Bridge/Realize.lean`, `cplxL`). -/
def cplxV : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => (v i : ℂ))
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

@[simp] theorem cplxV_apply (v : Space) (i : Fin 3) : cplxV v i = (v i : ℂ) := rfl

theorem norm_cplxV (v : Space) : ‖cplxV v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [cplxV_apply, Complex.norm_real]

/-- The complexification on `L²(phaseμ P)`, a real-linear isometry. -/
def cplxLp (P : ℝ) : Lp Space 2 (phaseμ P) →ₗᵢ[ℝ] Lp CVec3 2 (phaseμ P) where
  toLinearMap := (cplxV.compLpL 2 (phaseμ P)).toLinearMap
  norm_map' U := by
    show ‖cplxV.compLpL 2 (phaseμ P) U‖ = ‖U‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [cplxV.coeFn_compLpL U] with x hx
    rw [hx, norm_cplxV]

theorem coeFn_cplxLp (P : ℝ) (U : Lp Space 2 (phaseμ P)) :
    (cplxLp P U : ℝ × Space → CVec3) =ᵐ[phaseμ P] fun x => cplxV (U x) :=
  cplxV.coeFn_compLpL U

/-! ### The phase circle -/

section Circle

variable (P : ℝ) [hP : Fact (0 < P)]

/-- The representative in `(0, P]` of a phase in `ℝ/Pℤ`. -/
def phaseRep (θ : AddCircle P) : ℝ := (AddCircle.equivIoc P 0 θ : ℝ)

theorem measurable_phaseRep : Measurable (phaseRep P) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc P 0).measurable

theorem phaseRep_coe {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) P) : phaseRep P (t : AddCircle P) = t := by
  have ht' : t ∈ Ioc (0 : ℝ) (0 + P) := by rwa [zero_add]
  simp only [phaseRep, AddCircle.equivIoc_coe_eq ht']

/-- `P⁻¹ dτ|_{(0,P]}` is carried to the Haar probability measure of `ℝ/Pℤ` (tex 7313–7317). -/
theorem measurePreserving_coe_addCircle :
    MeasurePreserving (fun t : ℝ => (t : AddCircle P))
      ((ENNReal.ofReal P)⁻¹ • volume.restrict (Ioc (0 : ℝ) P))
      (AddCircle.haarAddCircle (T := P)) := by
  have h := (AddCircle.measurePreserving_mk P 0).smul_measure (ENNReal.ofReal P)⁻¹
  rw [zero_add, AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hP.out).ne' ENNReal.ofReal_ne_top,
    one_smul] at h
  exact h

theorem measurePreserving_phaseRep :
    MeasurePreserving (phaseRep P) (AddCircle.haarAddCircle (T := P))
      ((ENNReal.ofReal P)⁻¹ • volume.restrict (Ioc (0 : ℝ) P)) := by
  have hmp := measurePreserving_coe_addCircle P
  refine ⟨measurable_phaseRep P, ?_⟩
  rw [← hmp.map_eq, Measure.map_map (measurable_phaseRep P) hmp.measurable]
  have hae : (phaseRep P ∘ fun t : ℝ => (t : AddCircle P)) =ᵐ[(ENNReal.ofReal P)⁻¹ •
      volume.restrict (Ioc (0 : ℝ) P)] id := by
    refine Measure.ae_smul_measure ?_ _
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact phaseRep_coe P ht
  rw [Measure.map_congr hae, Measure.map_id]

/-- `(θ, y) ↦ (phaseRep θ, y)` carries `haar ⊗ dy` to `phaseμ P`. -/
theorem measurePreserving_phaseRepProd :
    MeasurePreserving (Prod.map (phaseRep P) id)
      ((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)) (phaseμ P) :=
  (measurePreserving_phaseRep P).prod (MeasurePreserving.id volume)

end Circle

/-! ### The bridge `L²(phaseμ P; ℝ³) → Y₂` -/

section Bridge

variable (P : ℝ) [hP : Fact (0 < P)]

/-- The Fubini isometry `L²(haar ⊗ dy; ℂ³) ≃ Y₂` of `FreeStress.prodLpEquiv`, as a real-linear
isometry. -/
def prodLpR :
    Lp CVec3 2 ((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)) →ₗᵢ[ℝ]
      Yq P 2 where
  toLinearMap := (FreeStress.prodLpEquiv (F := CVec3) (q := 2)
    (ν := AddCircle.haarAddCircle (T := P)) (μ := (volume : Measure Space))).toLinearEquiv
    |>.toLinearMap.restrictScalars ℝ
  norm_map' f := (FreeStress.prodLpEquiv (F := CVec3) (q := 2)
    (ν := AddCircle.haarAddCircle (T := P)) (μ := (volume : Measure Space))).norm_map f

/-- **AX04, the bridge to D2's Bochner space** (tex 7313–7317; B0417, B0219). The joint
period-averaged `L²(phaseμ P; ℝ³)` embeds isometrically (real-linearly) into
`Y₂ = L²(ℝ/Pℤ; L²(ℝ³; ℂ³))`: complexify, move the phase from `(0, P]` to the circle, and curry. -/
def toY2 : Lp Space 2 (phaseμ P) →ₗᵢ[ℝ] Yq P 2 :=
  (prodLpR P).comp ((Lp.compMeasurePreservingₗᵢ ℝ (Prod.map (phaseRep P) id)
    (measurePreserving_phaseRepProd P)).comp (cplxLp P))

/-- The slice formula on the circle: for a.e. phase `θ`, `(toY2 U)(θ) = U(phaseRep θ, ·)`
(complexified) a.e. -/
theorem toY2_ae (U : Lp Space 2 (phaseμ P)) :
    ∀ᵐ θ ∂AddCircle.haarAddCircle (T := P),
      ((toY2 P U θ : Lp CVec3 2 (volume : Measure Space)) : Space → CVec3) =ᵐ[volume]
        fun y => cplxV (U (phaseRep P θ, y)) := by
  set f := Lp.compMeasurePreserving (Prod.map (phaseRep P) id)
    (measurePreserving_phaseRepProd P) (cplxLp P U) with hf
  have h1 : (f : AddCircle P × Space → CVec3) =ᵐ[(AddCircle.haarAddCircle (T := P)).prod
      (volume : Measure Space)] fun z => cplxV (U (phaseRep P z.1, z.2)) := by
    have e1 := Lp.coeFn_compMeasurePreserving (cplxLp P U) (measurePreserving_phaseRepProd P)
    have e2 := (measurePreserving_phaseRepProd P).quasiMeasurePreserving.ae_eq_comp
      (coeFn_cplxLp P U)
    exact e1.trans e2
  have h2 := FreeStress.prodLpEquiv_ae (F := CVec3) (q := 2)
    (ν := AddCircle.haarAddCircle (T := P)) (μ := (volume : Measure Space)) f
  filter_upwards [h2, Measure.ae_ae_of_ae_prod h1] with θ hθ hθ'
  exact hθ.trans hθ'

/-- **The slice formula in the phase time** (tex 7313–7317): for a.e. `t ∈ (0, P]`,
`(toY2 U)(t mod P) = U(t, ·)` (complexified) a.e. on `ℝ³`. -/
theorem toY2_ae_Ioc (U : Lp Space 2 (phaseμ P)) :
    ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioc (0 : ℝ) P)),
      ((toY2 P U (t : AddCircle P) : Lp CVec3 2 (volume : Measure Space)) : Space → CVec3)
        =ᵐ[volume] fun y => cplxV (U (t, y)) := by
  have h := (measurePreserving_coe_addCircle P).quasiMeasurePreserving.ae (toY2_ae P U)
  have hne : (ENNReal.ofReal P)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have h' := (Measure.ae_ennreal_smul_measure_iff hne).1 h
  filter_upwards [h', ae_restrict_mem measurableSet_Ioc] with t ht ht'
  rw [phaseRep_coe P ht'] at ht
  exact ht

end Bridge

/-! ### `J_v` in `Y₂` -/

/-- **AX04 `Jv` into `Y₂`** (B0417, tex 7276–7280: `J_v = (√π R)⁻¹ N_v` into the
period-averaged `Y₂`). The ring lift read in D2's Bochner space, a real-linear isometry. -/
def JvY2 {R c P : ℝ} [Fact (0 < P)] (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) :
    Lp Merid 2 (ageμ c (-3 / 2)) →ₗᵢ[ℝ] Yq P 2 :=
  (toY2 P).comp (Jv hR hc hP)

/-- For a.e. `t ∈ (0, P]`, `(J_v b)(t mod P) = (√π R)⁻¹ N_v b(t, ·)` (complexified) a.e. -/
theorem JvY2_ae {R c P : ℝ} [Fact (0 < P)] (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : Lp Merid 2 (ageμ c (-3 / 2))) :
    ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioc (0 : ℝ) P)),
      ((JvY2 hR hc hP b (t : AddCircle P) : Lp CVec3 2 (volume : Measure Space)) :
        Space → CVec3) =ᵐ[volume] fun y => cplxV ((√π * R)⁻¹ • Nv R (perExt c b) t y) := by
  filter_upwards [toY2_ae_Ioc P (Jv hR hc hP b), ae_slice (coeFn_Jv hR hc hP b)]
    with t h1 h2
  refine h1.trans ?_
  filter_upwards [h2] with y hy
  rw [hy]

end UnforcedLeray.Axi
