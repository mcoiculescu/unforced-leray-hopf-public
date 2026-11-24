import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Pieces
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonInnerRot
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3.Helpers

/-!
# `PartIII-b:C/rep/8/1/1/1/1` (`streamCutEq`): `mnX = 𝒞_y W^mt` in the `Space` form

Source `shorter-proof-2026-11-02.tex` lines 4178-4186, 4783-4791.  The `Vec3` stream cutoff
`streamCut` of `Concrete/SourceL.lean` (outward primitive along the ray through `y`) agrees with
`wardStreamCut` (outward primitive on the half plane `φ = 0`) for the field `Z = W^mt_μ - W^mt_{μ+1}`:
only the `z`-component of `Z` enters the primitive, and the `z`-component of the Newton field is
invariant under rotations about the axis.  No outward-region hypothesis and no sign of `μ` is
needed for the `z`-component: the inner integral changes variables by the rotation of the source
plane (the kernel is rotation covariant off `0`, and `0` is hit at one source point only).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- The `z` component of the inner integral is invariant under rotation about the axis, for every
`x` (no outward-region hypothesis). -/
theorem newtonInner_two_rot (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (θ t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (x : Vec3) :
    ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (rotAx θ x - t • embPlane x') 2 j k *
        sigmaM c ν χo M x' j k =
      ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (x - t • embPlane x') 2 j k * sigmaM c ν χo M x' j k := by
  have hemb : MeasurableEmbedding (rotPl θ) := (rotPlHomeo θ).measurableEmbedding
  have hnull : ∀ᵐ a : ℝ × ℝ, x - t • embPlane a ≠ 0 := by
    have hsub : {a : ℝ × ℝ | ¬ (x - t • embPlane a ≠ 0)}.Subsingleton := by
      intro a ha b hb
      have ha' : x - t • embPlane a = 0 := not_not.1 ha
      have hb' : x - t • embPlane b = 0 := not_not.1 hb
      have h : t • embPlane a = t • embPlane b := by
        rw [sub_eq_zero] at ha' hb'
        rw [← ha', ← hb']
      have h2 := smul_right_injective Vec3 ht.1.ne' h
      have e0 := congrArg (fun w : Vec3 => w 0) h2
      have e1 := congrArg (fun w : Vec3 => w 1) h2
      simp only [embPlane, Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      exact Prod.ext e0 e1
    have h0 : volume {a : ℝ × ℝ | ¬ (x - t • embPlane a ≠ 0)} = 0 := hsub.measure_zero _
    exact h0
  have hpt : ∀ a : ℝ × ℝ, x - t • embPlane a ≠ 0 →
      ∑ j, ∑ k, newtonD3 (rotAx θ x - t • embPlane (rotPl θ a)) 2 j k *
          sigmaM c ν χo M (rotPl θ a) j k =
        ∑ j, ∑ k, newtonD3 (x - t • embPlane a) 2 j k * sigmaM c ν χo M a j k := by
    intro a hw
    by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
    · have hrw : rotAx θ x - t • embPlane (rotPl θ a) = rotAx θ (x - t • embPlane a) := by
        rw [rotAx_sub, rotAx_smul, rotAx_embPlane]
      have hS : ∀ j k, sigmaM c ν χo M (rotPl θ a) j k =
          ∑ p, ∑ q, rotMat θ j p * sigmaM c ν χo M a p q * rotMat θ k q :=
        fun j k => sigmaMRot c ν χo M θ a j k
      rw [hrw]
      simp only [newtonD3Rot θ (x - t • embPlane a) hw, hS]
      have := kerContractRot θ (fun p q r => newtonD3 (x - t • embPlane a) p q r)
        (fun p q => sigmaM c ν χo M a p q) 2
      rw [this]
      simp [rotMat, Fin.sum_univ_three]
    · have h0 : ∀ j k, sigmaM c ν χo M a j k = 0 := by
        intro j k
        rw [sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 ha)]
        rfl
      have h1 : ∀ j k, sigmaM c ν χo M (rotPl θ a) j k = 0 := by
        intro j k
        rw [sigmaM_eq_zero_of_ge c ν χo M hν hχ (rotPl θ a)
          (by rw [rotPl_sq]; exact not_lt.1 ha)]
        rfl
      simp only [h0, h1, mul_zero, Finset.sum_const_zero]
  calc ∫ x', ∑ j, ∑ k, newtonD3 (rotAx θ x - t • embPlane x') 2 j k *
          sigmaM c ν χo M x' j k
      = ∫ y, ∑ j, ∑ k, newtonD3 (rotAx θ x - t • embPlane (rotPl θ y)) 2 j k *
          sigmaM c ν χo M (rotPl θ y) j k :=
        ((rotPlMP θ).integral_comp hemb (fun x' => ∑ j, ∑ k,
          newtonD3 (rotAx θ x - t • embPlane x') 2 j k * sigmaM c ν χo M x' j k)).symm
    _ = _ := integral_congr_ae (hnull.mono fun a ha => hpt a ha)

/-- The `z` component of the zero-width Newton field is invariant under rotation about the axis. -/
theorem newtonV_rotAx_two (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (θ : ℝ) (x : Vec3) :
    newtonV c ν μ χo M (rotAx θ x) 2 = newtonV c ν μ χo M x 2 := by
  simp only [newtonV]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  rw [newtonInner_two_rot c ν χo M hν hχ θ t ht x]

/-- Derivative of `chiYr` for `r > 0` (chain rule; if `χy` is not differentiable at `ν/(εr)²`
both sides vanish, since the substitution is a local diffeomorphism there). -/
theorem deriv_chiYr_pos (ν ε : ℝ) (χy : ℝ → ℝ) (hν : 0 < ν) (hε : 0 < ε)
    {r : ℝ} (hr : 0 < r) :
    deriv (chiYr ν ε χy) r = deriv χy (ν / (ε * r) ^ 2) * (-2 * ν / (ε ^ 2 * r ^ 3)) := by
  have hev : chiYr ν ε χy =ᶠ[𝓝 r] fun r => χy (ν / (ε * r) ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hr.ne'] with s hs
    simp [chiYr, hs]
  rw [hev.deriv_eq]
  have hne : (ε * r) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_pos hε hr).ne'
  have h1 : HasDerivAt (fun r : ℝ => (ε * r) ^ 2) (2 * (ε * r) * ε) r := by
    have h : HasDerivAt (fun r : ℝ => ε * r) ε r := by
      simpa using (hasDerivAt_id r).const_mul ε
    have e : (fun r : ℝ => (ε * r) ^ 2) = fun r => (ε * r) * (ε * r) := by
      funext r; ring
    rw [e]
    exact (h.mul h).congr_deriv (by ring)
  have h2 : HasDerivAt (fun r : ℝ => ν / (ε * r) ^ 2)
      ((0 * (ε * r) ^ 2 - ν * (2 * (ε * r) * ε)) / ((ε * r) ^ 2) ^ 2) r :=
    (hasDerivAt_const r ν).div h1 hne
  set u0 : ℝ := ν / (ε * r) ^ 2 with hu0
  have hu0pos : 0 < u0 := by positivity
  have hcoef : (0 * (ε * r) ^ 2 - ν * (2 * (ε * r) * ε)) / ((ε * r) ^ 2) ^ 2 =
      -2 * ν / (ε ^ 2 * r ^ 3) := by
    field_simp
    ring
  by_cases hd : DifferentiableAt ℝ χy u0
  · have h3 : HasDerivAt (fun r : ℝ => χy (ν / (ε * r) ^ 2))
        (deriv χy u0 * ((0 * (ε * r) ^ 2 - ν * (2 * (ε * r) * ε)) / ((ε * r) ^ 2) ^ 2)) r :=
      hd.hasDerivAt.comp r h2
    rw [h3.deriv, hcoef]
  · rw [deriv_zero_of_not_differentiableAt hd, zero_mul]
    apply deriv_zero_of_not_differentiableAt
    intro hcomp
    -- χy = (χy ∘ g) ∘ h near u0, with h the inverse branch
    let h : ℝ → ℝ := fun u => Real.sqrt (ν / u) / ε
    have hinv : ∀ u : ℝ, 0 < u → ν / (ε * h u) ^ 2 = u := by
      intro u hu
      have hq : 0 < ν / u := by positivity
      have : ε * h u = Real.sqrt (ν / u) := by
        simp only [h]; field_simp
      rw [this, Real.sq_sqrt hq.le]
      field_simp
    have hhr : h u0 = r := by
      simp only [h, hu0]
      have : ν / (ν / (ε * r) ^ 2) = (ε * r) ^ 2 := by field_simp
      rw [this, Real.sqrt_sq (mul_pos hε hr).le]
      field_simp
    have hhd : DifferentiableAt ℝ h u0 := by
      have hq : ν / u0 ≠ 0 := by positivity
      have : DifferentiableAt ℝ (fun u : ℝ => ν / u) u0 :=
        (differentiableAt_const ν).div differentiableAt_id hu0pos.ne'
      exact (this.sqrt hq).div_const ε
    have hcomp' : DifferentiableAt ℝ (fun r => χy (ν / (ε * r) ^ 2)) (h u0) := by
      rw [hhr]; exact hcomp
    have hfin : DifferentiableAt ℝ (fun u => χy (ν / (ε * h u) ^ 2)) u0 := hcomp'.comp u0 hhd
    apply hd
    refine hfin.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hu0pos] with u hu
    rw [hinv u hu]

/-- The `z` component of `Z = W^mt_μ - W^mt_{μ+1}` at a point of the outward ray equals its value on
the half plane `φ = 0`. -/
theorem youngDiff_ray_two (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (y : Vec3) (hy : 0 < cylR y) (ρ : ℝ) :
    (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (rayPt y ρ) 2 =
      (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) ![ρ, 0, y 2] 2 := by
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
  have key : ∀ μ' : ℝ, youngW c ν ε μ' χo M (rotAx θ (![ρ, 0, y 2])) 2 =
      youngW c ν ε μ' χo M ![ρ, 0, y 2] 2 := by
    intro μ'
    simp only [youngW, Pi.smul_apply, smul_eq_mul]
    rw [← rotAx_smul, newtonV_rotAx_two c ν μ' χo M hν hχ]
  simp only [Pi.sub_apply, hray, key]

/-- `streamPsi` is the primitive on the half plane `φ = 0`. -/
theorem streamPsi_eq_outPrim (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (T : LStr Pl K L) (τ : ℝ) (y : Space) (hy : 0 < ϱ y) :
    streamPsi (youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) -
      youngW (cOf L.ν) L.ν L.ε (μ + 1) K.χo (thinRep T)) (WithLp.ofLp y) =
      outPrim (zMt Pl K L μ T) τ (ϱ y) (y 2) := by
  have hcyl : cylR (WithLp.ofLp y) = ϱ y := rfl
  have hy' : 0 < cylR (WithLp.ofLp y) := hcyl ▸ hy
  unfold streamPsi outPrim
  rw [hcyl]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun ρ _ => ?_)
  rw [youngDiff_ray_two _ _ _ _ _ _ L.ν_pos K.hχo _ hy' ρ]
  rfl

theorem mnX_eq_wardStreamCut (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (T : LStr Pl K L) (τ : ℝ) (y : Space) (hy : 0 < ϱ y) :
    mnX Pl K L μ T τ y = wardStreamCut L.ν L.ε⁻¹ K.χy (zMt Pl K L μ T) τ y := by
  have hcyl : cylR (WithLp.ofLp y) = ϱ y := rfl
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hpsi := streamPsi_eq_outPrim Pl K L μ T τ y hy
  have hage : L.ν * age L.ε⁻¹ y = L.ν / (L.ε * ϱ y) ^ 2 := by
    unfold age
    field_simp
  have hchi : chiYr L.ν L.ε K.χy (ϱ y) = K.χy (L.ν * age L.ε⁻¹ y) := by
    rw [hage]
    simp [chiYr, hy.ne']
  have hder : deriv (chiYr L.ν L.ε K.χy) (ϱ y) =
      deriv K.χy (L.ν * age L.ε⁻¹ y) * (-2 * L.ν * L.ε⁻¹ ^ 2 / ϱ y ^ 3) := by
    rw [deriv_chiYr_pos L.ν L.ε K.χy hν hε hy, hage]
    congr 1
    field_simp
  unfold mnX Xmean Xmt wardStreamCut
  ext i
  simp only [streamCut, hcyl, hder, hpsi, hchi]
  fin_cases i <;> simp [zMt, coordinateVector]

end UnforcedLeray.Short.PartIIIb.Concrete
