import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.NewtonComm.FastCut
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.CutEq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.StreamCutEq

/-!
# `PartIII-b:C/rep/8/1/1/2/5/2/2`: the zero-width commutator bridge `YBWidth.newtonCommBridge`

Source of record: `the November 2 reference manuscript`, lines 5427-5432,
5380-5387, 4764-4782, and 4178-4186.

At young receivers `y = ε⁻¹ • xo` with `L.ν ≤ xo 0 ^ 2 + xo 1 ^ 2`, we prove
`fderiv ℝ (mnYB Pl K L μ T τ) (L.ε⁻¹ • xo) =
  fderiv ℝ (comm L.ν μ L.ε⁻¹ K.χy (newtonX0 L.ε μ (meanSrc Pl K L T)) τ) (L.ε⁻¹ • xo)`
by establishing equality of the two fields on the open neighborhood
`U = {y : Space | 5 * L.ν / 6 < (L.ε • y) 0 ^ 2 + (L.ε • y) 1 ^ 2}` of `L.ε⁻¹ • xo`:

1. `mtField (dmuFree ν μ' F) = physDmu ν μ' (mtField F)` for any phase-free field `F : Vec3 → Vec3`;
2. `dmuFree L.ν (μ + 1) (W_μ - W_{μ+1}) = W_μ` outside `{65/72 * L.ν ≤ (εy)₀² + (εy)₁²}` via the
   fast-cutoff representation `cutRep` (`FastCut.lean`) and the harmonic / radial-shift identities of
   `MeanShift.lean`;
3. `mnYB Pl K L μ T τ y = comm L.ν μ L.ε⁻¹ K.χy (zMt Pl K L μ T) τ y` off the axis (`0 < ϱ y`),
   combining `mnX_eq_wardStreamCut` and `GeomYACut.mtField_streamCut_eq`;
4. `comm L.ν μ L.ε⁻¹ K.χy (zMt Pl K L μ T) τ y =
    comm L.ν μ L.ε⁻¹ K.χy (newtonX0 L.ε μ (meanSrc Pl K L T)) τ y` for `y ∈ U`, since `zMt` and
   `newtonX0` agree on `ℝ × U` (`zMt_eq_newtonX0_of_gt`) and `U` is invariant along outward rays
   `ρ > ϱ y` on the half-plane `φ = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace YBWidth

open YBComm PhasePrim
open TWBridge hiding meanSrc

/-! ## 1. Dictionary between `dmuFree` on `Vec3` and `physDmu` on `Space` -/

theorem fderiv_mtField_apply (F : Vec3 → Vec3) (τ : ℝ) (y v : Space) :
    fderiv ℝ (mtField F τ) y v =
      WithLp.toLp 2 (fderiv ℝ F (WithLp.ofLp y) (WithLp.ofLp v)) := by
  let e : Space ≃L[ℝ] Vec3 := EuclideanSpace.equiv (Fin 3) ℝ
  change fderiv ℝ (⇑e.symm ∘ (F ∘ ⇑e)) y v = e.symm (fderiv ℝ F (e y) (e v))
  rw [e.symm.comp_fderiv, ContinuousLinearMap.comp_apply, e.comp_right_fderiv,
    ContinuousLinearMap.comp_apply]
  rfl

theorem physPd_mtField (F : Vec3 → Vec3) (τ : ℝ) (j : Fin 3) :
    (fun y => physPd (mtField F τ) j y) = mtField (fun x => fderiv ℝ F x (Pi.single j 1)) τ := by
  funext y
  unfold physPd
  rw [fderiv_mtField_apply]
  rfl

theorem physPd2_mtField (F : Vec3 → Vec3) (τ : ℝ) (j l : Fin 3) (y : Space) :
    physPd2 (mtField F τ) j l y =
      WithLp.toLp 2 (fderiv ℝ (fun x => fderiv ℝ F x (Pi.single l 1))
        (WithLp.ofLp y) (Pi.single j 1)) := by
  unfold physPd2
  rw [physPd_mtField, physPd, fderiv_mtField_apply]
  rfl

theorem physLap_mtField (F : Vec3 → Vec3) (τ : ℝ) (y : Space) :
    physLap (mtField F τ) y = WithLp.toLp 2 (vecLap F (WithLp.ofLp y)) := by
  ext i
  unfold physLap vecLap
  simp only [physPd2_mtField]
  change (∑ j : Fin 3, WithLp.toLp 2
      (fderiv ℝ (fun x => fderiv ℝ F x (Pi.single j 1)) (WithLp.ofLp y) (Pi.single j 1))) i =
    (∑ j : Fin 3,
      fderiv ℝ (fun x => fderiv ℝ F x (Pi.single j 1)) (WithLp.ofLp y) (Pi.single j 1)) i
  simp only [Finset.sum_apply]
  rfl

theorem mtField_dmuFree_eq_physDmu (ν μ' : ℝ) (F : Vec3 → Vec3) (τ : ℝ) (y : Space) :
    mtField (dmuFree ν μ' F) τ y = physDmu ν μ' (mtField F) τ y := by
  have hderiv : deriv (fun t => mtField F t y) τ = 0 := by
    change deriv (fun _ : ℝ => WithLp.toLp 2 (F (WithLp.ofLp y))) τ = 0
    exact deriv_const τ _
  ext i
  unfold physDmu dmuFree
  rw [hderiv, zero_sub, fderiv_mtField_apply, physLap_mtField]
  simp only [mtField, PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mtField_dmuFree_eq_physDmu_fun (ν μ' : ℝ) (F : Vec3 → Vec3) :
    mtField (dmuFree ν μ' F) = physDmu ν μ' (mtField F) := by
  funext τ y
  exact mtField_dmuFree_eq_physDmu ν μ' F τ y

/-! ## 2. Local congruence of `physDmu`, `wardStreamCut`, and `comm` on open ray-closed sets -/

theorem physDmu_congr_nhds (ν μ' : ℝ) {X₁ X₂ : ℝ → Space → Space} {τ : ℝ} {y : Space}
    (ht : ∀ t, X₁ t y = X₂ t y) (hy : X₁ τ =ᶠ[𝓝 y] X₂ τ) :
    physDmu ν μ' X₁ τ y = physDmu ν μ' X₂ τ y := by
  have h1 : deriv (fun t => X₁ t y) τ = deriv (fun t => X₂ t y) τ := by
    congr 1; funext t; exact ht t
  have h2 : fderiv ℝ (X₁ τ) y = fderiv ℝ (X₂ τ) y := hy.fderiv_eq
  have h3 : physLap (X₁ τ) y = physLap (X₂ τ) y := by
    unfold physLap physPd2
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpd : physPd (X₁ τ) j =ᶠ[𝓝 y] physPd (X₂ τ) j := by
      filter_upwards [hy.eventuallyEq_nhds] with y' hy'
      unfold physPd
      rw [hy'.fderiv_eq]
    change fderiv ℝ (physPd (X₁ τ) j) y (coordinateVector j) =
      fderiv ℝ (physPd (X₂ τ) j) y (coordinateVector j)
    rw [hpd.fderiv_eq]
  unfold physDmu
  rw [h1, h2, h3, ht τ]

theorem physDmu_eq_on_of_isOpen (ν μ' : ℝ) {X₁ X₂ : ℝ → Space → Space} {U : Set Space}
    (hU : IsOpen U) (hX : ∀ t : ℝ, ∀ y ∈ U, X₁ t y = X₂ t y) (τ : ℝ) {y : Space} (hy : y ∈ U) :
    physDmu ν μ' X₁ τ y = physDmu ν μ' X₂ τ y := by
  refine physDmu_congr_nhds ν μ' (fun t => hX t y hy) ?_
  filter_upwards [hU.mem_nhds hy] with y' hy'
  exact hX τ y' hy'

theorem wardStreamCut_eq_on_of_rayClosed (ν R : ℝ) (χy : ℝ → ℝ)
    {X₁ X₂ : ℝ → Space → Space} {U : Set Space}
    (hray : ∀ y ∈ U, ∀ ρ ∈ Ioi (ϱ y), (!₂[ρ, 0, y 2] : Space) ∈ U)
    (hX : ∀ t : ℝ, ∀ y ∈ U, X₁ t y = X₂ t y) (τ : ℝ) {y : Space} (hy : y ∈ U) :
    wardStreamCut ν R χy X₁ τ y = wardStreamCut ν R χy X₂ τ y := by
  have hout : outPrim X₁ τ (ϱ y) (y 2) = outPrim X₂ τ (ϱ y) (y 2) := by
    unfold outPrim
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    rw [hX τ _ (hray y hy ρ hρ)]
  unfold wardStreamCut
  rw [hX τ y hy, hout]

theorem comm_eq_on_of_isOpen_rayClosed (ν μ R : ℝ) (χy : ℝ → ℝ)
    {X₁ X₂ : ℝ → Space → Space} {U : Set Space} (hU : IsOpen U)
    (hray : ∀ y ∈ U, ∀ ρ ∈ Ioi (ϱ y), (!₂[ρ, 0, y 2] : Space) ∈ U)
    (hX : ∀ t : ℝ, ∀ y ∈ U, X₁ t y = X₂ t y) (τ : ℝ) {y : Space} (hy : y ∈ U) :
    comm ν μ R χy X₁ τ y = comm ν μ R χy X₂ τ y := by
  have hw : ∀ t : ℝ, ∀ y' ∈ U,
      wardStreamCut ν R χy X₁ t y' = wardStreamCut ν R χy X₂ t y' :=
    fun t _ hy' => wardStreamCut_eq_on_of_rayClosed ν R χy hray hX t hy'
  have hd : ∀ t : ℝ, ∀ y' ∈ U,
      physDmu ν (μ + 1) X₁ t y' = physDmu ν (μ + 1) X₂ t y' :=
    fun t _ hy' => physDmu_eq_on_of_isOpen ν (μ + 1) hU hX t hy'
  unfold YBComm.comm
  rw [physDmu_eq_on_of_isOpen ν (μ + 1) hU hw τ hy,
    wardStreamCut_eq_on_of_rayClosed ν R χy hray hd τ hy]

/-! ## 3. Shifted dilation identity for `youngW (thinRep T)` under `oldN1 ≠ ⊤` -/

theorem dmuFree_youngW_diff_eq (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hL : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy) (hC0 : 0 < K.C0) (T : LStr Pl K L)
    (hN1 : oldN1 Pl K L T ≠ ⊤) {y : Vec3}
    (hx : 5 * (13 / 12 * L.ν) / 6 < (L.ε • y) 0 ^ 2 + (L.ε • y) 1 ^ 2) :
    dmuFree L.ν (μ + 1) (youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) -
      youngW (cOf L.ν) L.ν L.ε (μ + 1) K.χo (thinRep T)) y =
      youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) y := by
  rw [← youngW_cutRep Pl K L μ T, ← youngW_cutRep Pl K L (μ + 1) T]
  set c := cOf L.ν
  set ν' := 13 / 12 * L.ν
  set ε := L.ε
  set M := cutRep Pl K L T
  have hc : 0 < c := hL.c_pos
  have hν : 0 < L.ν := hL.nu_pos
  have hν' : 0 < ν' := by positivity
  have hμ : 0 < μ := hL.mu_pos
  have hχ' : IsOutwardCutoff χo_fast := isOutwardCutoff_fast
  have hM : OldThinFinite c ν' M := oldThinFinite_cutRep Pl K L hC0 T hN1 hν'
  set U : Set Vec3 := {x : Vec3 | 5 * ν' / 6 < x 0 ^ 2 + x 1 ^ 2}
  have hU : IsOpen U := isOpen_newtonRegion ν'
  have hxU : ε • y ∈ U := hx
  have hVS : ∀ p : ℝ, 0 < p → ContDiffOn ℝ ∞ (newtonV c ν' p χo_fast M) U := fun p hp =>
    newtonVSmooth_of newtonFamSmooth newtonFamMeas newtonFamDom c ν' p χo_fast M hc hν' hp hχ' hM
  have hVd : ∀ p : ℝ, 0 < p → DifferentiableAt ℝ (newtonV c ν' p χo_fast M) (ε • y) := fun p hp =>
    ((hVS p hp).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hZ : youngW c ν' ε μ χo_fast M - youngW c ν' ε (μ + 1) χo_fast M =
      fun z => ε ^ 2 • (newtonV c ν' μ χo_fast M (ε • z) -
        newtonV c ν' (μ + 1) χo_fast M (ε • z)) := by
    funext z
    simp [youngW, smul_sub]
  have hshift := fun i => newtonV_shift_component hc hν' hμ hχ' hM i hx
  funext i
  have hB : fderiv ℝ (youngW c ν' ε μ χo_fast M - youngW c ν' ε (μ + 1) χo_fast M) y y i =
      ε ^ 2 * (fderiv ℝ (newtonV c ν' μ χo_fast M) (ε • y) (ε • y) i -
        fderiv ℝ (newtonV c ν' (μ + 1) χo_fast M) (ε • y) (ε • y) i) := by
    rw [hZ]
    have hVdiff : HasFDerivAt
        (fun w => newtonV c ν' μ χo_fast M w - newtonV c ν' (μ + 1) χo_fast M w)
        (fderiv ℝ (newtonV c ν' μ χo_fast M) (ε • y) -
          fderiv ℝ (newtonV c ν' (μ + 1) χo_fast M) (ε • y))
        (ε • y) := (hVd μ hμ).hasFDerivAt.sub (hVd (μ + 1) (by linarith)).hasFDerivAt
    have hZ' : HasFDerivAt
        (fun z => ε ^ 2 • (newtonV c ν' μ χo_fast M (ε • z) -
          newtonV c ν' (μ + 1) χo_fast M (ε • z)))
        (ε ^ 2 • ((fderiv ℝ (newtonV c ν' μ χo_fast M) (ε • y) -
          fderiv ℝ (newtonV c ν' (μ + 1) χo_fast M) (ε • y)).comp
            (ε • ContinuousLinearMap.id ℝ Vec3)))
        y :=
      (hVdiff.comp y ((hasFDerivAt_id y).const_smul ε)).const_smul (ε ^ 2)
    rw [hZ'.fderiv]
    simp [mul_sub]
  have hC : vecLap (youngW c ν' ε μ χo_fast M - youngW c ν' ε (μ + 1) χo_fast M) y i = 0 := by
    rw [hZ]
    set U' : Set Vec3 := {z : Vec3 | ε • z ∈ U}
    have hU' : IsOpen U' := hU.preimage (continuous_const_smul ε)
    have hyU' : y ∈ U' := hxU
    have hsm : ContDiffOn ℝ ∞
        (fun w => newtonV c ν' μ χo_fast M w - newtonV c ν' (μ + 1) χo_fast M w) U :=
      (hVS μ hμ).sub (hVS (μ + 1) (by linarith))
    have hX : ContDiffOn ℝ ∞
        (fun z => ε ^ 2 • (newtonV c ν' μ χo_fast M (ε • z) -
          newtonV c ν' (μ + 1) χo_fast M (ε • z))) U' := by
      refine ContDiffOn.const_smul (ε ^ 2) ?_
      exact hsm.comp (contDiff_const_smul ε).contDiffOn (fun z hz => hz)
    rw [vecLap_apply hU' hX hyU' i]
    set hs : Vec3 → ℝ := fun w => newtonV c ν' μ χo_fast M w i -
      newtonV c ν' (μ + 1) χo_fast M w i with hhs
    have hs_sm : ContDiffOn ℝ ∞ hs U := by
      have h1 : ∀ p : ℝ, 0 < p → ContDiffOn ℝ ∞ (fun w => newtonV c ν' p χo_fast M w i) U :=
        fun p hp => (contDiffOn_pi.1 (hVS p hp)) i
      exact (h1 μ hμ).sub (h1 (μ + 1) (by linarith))
    have hfun : (fun z : Vec3 => (ε ^ 2 • (newtonV c ν' μ χo_fast M (ε • z) -
        newtonV c ν' (μ + 1) χo_fast M (ε • z))) i) = (ε ^ 2) • (fun z => hs (ε • z)) := by
      funext z
      simp [hhs]
    have hcomp : ContDiffAt ℝ 2 (fun z => hs (ε • z)) y :=
      ((hs_sm.contDiffAt (hU.mem_nhds hxU)).of_le (by norm_cast)).comp y
        (contDiff_const_smul ε).contDiffAt
    rw [hfun]
    simp only [iteratedFDeriv_const_smul_apply hcomp, smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [trace_scale hU hs_sm hxU]
    have hc1 : ∀ p : ℝ, 0 < p → ContDiffAt ℝ 2 (fun w => newtonV c ν' p χo_fast M w i) (ε • y) :=
      fun p hp => (((contDiffOn_pi.1 (hVS p hp)) i).contDiffAt (hU.mem_nhds hxU)).of_le
        (by norm_cast)
    have hsub : ∀ l : Fin 3, iteratedFDeriv ℝ 2 hs (ε • y) ![Pi.single l 1, Pi.single l 1] =
        iteratedFDeriv ℝ 2 (fun w => newtonV c ν' μ χo_fast M w i) (ε • y)
          ![Pi.single l 1, Pi.single l 1] -
        iteratedFDeriv ℝ 2 (fun w => newtonV c ν' (μ + 1) χo_fast M w i) (ε • y)
          ![Pi.single l 1, Pi.single l 1] := by
      intro l
      rw [show hs = (fun w => newtonV c ν' μ χo_fast M w i) -
          (fun w => newtonV c ν' (μ + 1) χo_fast M w i) from rfl,
        iteratedFDeriv_sub_apply (hc1 μ hμ) (hc1 (μ + 1) (by linarith))]
      rfl
    simp only [hsub, Finset.sum_sub_distrib]
    rw [newtonV_trace hc hν' hμ hχ' hM i hx, newtonV_trace hc hν' (by linarith) hχ' hM i hx]
    ring
  have hW : ∀ p : ℝ, youngW c ν' ε p χo_fast M y i = ε ^ 2 * newtonV c ν' p χo_fast M (ε • y) i := by
    intro p
    simp [youngW]
  unfold dmuFree
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hB, hC, hW μ, hW (μ + 1)]
  have := hshift i
  linear_combination ε ^ 2 * this

/-! ## 4. Identification `mnYB = comm zMt` off the axis -/

theorem youngW_ray_two (c ν ε μ' : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (y : Vec3) (hy : 0 < cylR y) (ρ : ℝ) :
    youngW c ν ε μ' χo M (rayPt y ρ) 2 = youngW c ν ε μ' χo M ![ρ, 0, y 2] 2 := by
  set θ : ℝ := Complex.arg ⟨y 0, y 1⟩ with hθ
  have hnorm : ‖(⟨y 0, y 1⟩ : ℂ)‖ = cylR y := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [cylR]
    congr 1
    ring
  have hz : (⟨y 0, y 1⟩ : ℂ) ≠ 0 := by
    intro h
    have : ‖(⟨y 0, y 1⟩ : ℂ)‖ = 0 := by rw [h]; simp
    rw [hnorm] at this
    exact hy.ne' this
  have hc : Real.cos θ = y 0 / cylR y := by
    rw [hθ, Complex.cos_arg hz, hnorm]
  have hs : Real.sin θ = y 1 / cylR y := by
    rw [hθ, Complex.sin_arg, hnorm]
  have hray : rayPt y ρ = rotAx θ ![ρ, 0, y 2] := by
    funext i
    fin_cases i <;> simp [rayPt, rotAx, hc, hs] <;> ring
  simp only [hray, youngW, Pi.smul_apply, smul_eq_mul]
  rw [← rotAx_smul, newtonV_rotAx_two c ν μ' χo M hν hχ]

theorem isOpen_rho_pos : IsOpen {y : Space | 0 < ϱ y} := by
  let e : Space →L[ℝ] Vec3 := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
  have hc0 : Continuous (fun y : Space => y 0) := (continuous_apply 0).comp e.continuous
  have hc1 : Continuous (fun y : Space => y 1) := (continuous_apply 1).comp e.continuous
  exact isOpen_lt continuous_const (Real.continuous_sqrt.comp ((hc0.pow 2).add (hc1.pow 2)))

theorem mnYB_eq_comm_zMt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hL : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy) (hC0 : 0 < K.C0) (T : LStr Pl K L)
    (hN1 : oldN1 Pl K L T ≠ ⊤) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    mnYB Pl K L μ T τ y = comm L.ν μ L.ε⁻¹ K.χy (zMt Pl K L μ T) τ y := by
  set W := youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) -
    youngW (cOf L.ν) L.ν L.ε (μ + 1) K.χo (thinRep T)
  have hterm1 : mtField (dmuFree L.ν (μ + 1) (streamCut L.ν L.ε K.χy W)) τ y =
      physDmu L.ν (μ + 1) (wardStreamCut L.ν L.ε⁻¹ K.χy (zMt Pl K L μ T)) τ y := by
    rw [mtField_dmuFree_eq_physDmu]
    exact physDmu_eq_on_of_isOpen L.ν (μ + 1) isOpen_rho_pos
      (fun t y' hy' => mnX_eq_wardStreamCut Pl K L μ T t y' hy') τ hy
  have hF : ∀ w : Vec3, 0 < cylR w → ∀ ρ : ℝ, L.ν < (L.ε * ρ) ^ 2 →
      dmuFree L.ν (μ + 1) W (rayPt w ρ) 2 = dmuFree L.ν (μ + 1) W ![ρ, 0, w 2] 2 := by
    intro w hw ρ hρ
    have hν : 0 < L.ν := hL.nu_pos
    have h65 : 5 * (13 / 12 * L.ν) / 6 < (L.ε * ρ) ^ 2 := by linarith
    have hr2 : cylR w ^ 2 = w 0 ^ 2 + w 1 ^ 2 := Real.sq_sqrt (by positivity)
    have hray_sq : (L.ε • rayPt w ρ) 0 ^ 2 + (L.ε • rayPt w ρ) 1 ^ 2 = (L.ε * ρ) ^ 2 := by
      simp only [rayPt, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
      have h1 : (L.ε * (ρ * (w 0 / cylR w))) ^ 2 + (L.ε * (ρ * (w 1 / cylR w))) ^ 2 =
          (L.ε * ρ) ^ 2 * ((w 0 ^ 2 + w 1 ^ 2) / cylR w ^ 2) := by ring
      rw [h1, ← hr2, div_self (pow_ne_zero 2 hw.ne'), mul_one]
    have hax_sq : (L.ε • (![ρ, 0, w 2] : Vec3)) 0 ^ 2 +
        (L.ε • (![ρ, 0, w 2] : Vec3)) 1 ^ 2 = (L.ε * ρ) ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    have hray_gt : 5 * (13 / 12 * L.ν) / 6 <
        (L.ε • rayPt w ρ) 0 ^ 2 + (L.ε • rayPt w ρ) 1 ^ 2 := by linarith
    have hax_gt : 5 * (13 / 12 * L.ν) / 6 <
        (L.ε • (![ρ, 0, w 2] : Vec3)) 0 ^ 2 + (L.ε • (![ρ, 0, w 2] : Vec3)) 1 ^ 2 := by linarith
    rw [dmuFree_youngW_diff_eq Pl K L μ hL hC0 T hN1 hray_gt,
      dmuFree_youngW_diff_eq Pl K L μ hL hC0 T hN1 hax_gt,
      youngW_ray_two (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) hν K.hχo w hw ρ]
  have hterm2 : mtField (streamCut L.ν L.ε K.χy (dmuFree L.ν (μ + 1) W)) τ y =
      wardStreamCut L.ν L.ε⁻¹ K.χy (physDmu L.ν (μ + 1) (zMt Pl K L μ T)) τ y := by
    rw [GeomYACut.mtField_streamCut_eq hL.nu_pos hL.eps_pos hL.chiY
      (dmuFree L.ν (μ + 1) W) hF τ y hy, mtField_dmuFree_eq_physDmu_fun]
    rfl
  change mtField (dmuFree L.ν (μ + 1) (streamCut L.ν L.ε K.χy W)) τ y -
      mtField (streamCut L.ν L.ε K.χy (dmuFree L.ν (μ + 1) W)) τ y =
    comm L.ν μ L.ε⁻¹ K.χy (zMt Pl K L μ T) τ y
  rw [hterm1, hterm2]
  rfl

/-! ## 5. The open separated region and proof of `YBWidth.newtonCommBridge` -/

/-- The open spatial receiver region `{y : Space | 5ν/6 < (εy)₀² + (εy)₁²}`. -/
def sepRegion (ν ε : ℝ) : Set Space :=
  {y : Space | 5 * ν / 6 < (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2}

theorem isOpen_sepRegion (ν ε : ℝ) : IsOpen (sepRegion ν ε) := by
  let e : Space →L[ℝ] Vec3 := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
  have hc0 : Continuous (fun y : Space => (ε • y) 0) :=
    (continuous_apply 0).comp (e.continuous.comp (continuous_const_smul ε))
  have hc1 : Continuous (fun y : Space => (ε • y) 1) :=
    (continuous_apply 1).comp (e.continuous.comp (continuous_const_smul ε))
  exact isOpen_lt continuous_const ((hc0.pow 2).add (hc1.pow 2))

theorem rho_pos_of_mem_sepRegion {ν ε : ℝ} (hν : 0 < ν) {y : Space} (hy : y ∈ sepRegion ν ε) :
    0 < ϱ y := by
  have h1 : 0 < (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 :=
    lt_trans (by positivity) hy
  have h2 : (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 = ε ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h2] at h1
  have h3 : 0 < y 0 ^ 2 + y 1 ^ 2 := pos_of_mul_pos_right h1 (sq_nonneg ε)
  exact Real.sqrt_pos.2 h3

theorem sepRegion_rayClosed {ν ε : ℝ} (hν : 0 < ν) {y : Space} (hy : y ∈ sepRegion ν ε)
    {ρ : ℝ} (hρ : ρ ∈ Ioi (ϱ y)) :
    (!₂[ρ, 0, y 2] : Space) ∈ sepRegion ν ε := by
  have hrpos : 0 < ϱ y := rho_pos_of_mem_sepRegion hν hy
  have hρ' : ϱ y < ρ := hρ
  have hsq : y 0 ^ 2 + y 1 ^ 2 < ρ ^ 2 := by
    calc y 0 ^ 2 + y 1 ^ 2 = ϱ y ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ < ρ ^ 2 := sq_lt_sq.2 (by rw [abs_of_pos hrpos, abs_of_pos (hrpos.trans hρ')]; exact hρ')
  have h1 : (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 ≤
      (ε • (!₂[ρ, 0, y 2] : Space)) 0 ^ 2 + (ε • (!₂[ρ, 0, y 2] : Space)) 1 ^ 2 := by
    have lhs_eq : (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 = ε ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by
      simp only [PiLp.smul_apply, smul_eq_mul]; ring
    have rhs_eq : (ε • (!₂[ρ, 0, y 2] : Space)) 0 ^ 2 +
        (ε • (!₂[ρ, 0, y 2] : Space)) 1 ^ 2 = ε ^ 2 * ρ ^ 2 := by
      change (ε * (![ρ, 0, y 2] : Vec3) 0) ^ 2 + (ε * (![ρ, 0, y 2] : Vec3) 1) ^ 2 = ε ^ 2 * ρ ^ 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [lhs_eq, rhs_eq]
    exact mul_le_mul_of_nonneg_left hsq.le (sq_nonneg ε)
  exact lt_of_lt_of_le hy h1

/-- **The zero-width commutator bridge** (`PartIII-b:C/rep/8/1/1/2/5/2/2`). -/
theorem newtonCommBridge : NewtonCommBridge := by
  intro Pl K L μ hL hC0 T hAzi hN1 τ xo hxo
  have hν : 0 < L.ν := hL.nu_pos
  have hε : 0 < L.ε := hL.eps_pos
  have hy0_mem : L.ε⁻¹ • xo ∈ sepRegion L.ν L.ε := by
    show 5 * L.ν / 6 < (L.ε • (L.ε⁻¹ • xo)) 0 ^ 2 + (L.ε • (L.ε⁻¹ • xo)) 1 ^ 2
    rw [smul_inv_smul₀ hε.ne']
    linarith
  have hev : mnYB Pl K L μ T τ =ᶠ[𝓝 (L.ε⁻¹ • xo)]
      comm L.ν μ L.ε⁻¹ K.χy (newtonX0 L.ε μ (meanSrc Pl K L T)) τ := by
    filter_upwards [(isOpen_sepRegion L.ν L.ε).mem_nhds hy0_mem] with y hy
    rw [mnYB_eq_comm_zMt Pl K L μ hL hC0 T hN1 τ (rho_pos_of_mem_sepRegion hν hy)]
    exact comm_eq_on_of_isOpen_rayClosed L.ν μ L.ε⁻¹ K.χy
      (isOpen_sepRegion L.ν L.ε)
      (fun _ hy' _ hρ => sepRegion_rayClosed hν hy' hρ)
      (fun t _ hy' => zMt_eq_newtonX0_of_gt Pl K L μ hC0 T hAzi hN1 t hy')
      τ hy
  exact hev.fderiv_eq

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete
