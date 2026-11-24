import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_2

/-!
# `PartIII-b:C/rep/8/2/2/5`: the mean Y-Taylor estimate `MeanYTaylor`

Source `the November 2 reference manuscript`
5438-5448 (`|D_yY^mt(s,η) - s B_j(s)| ≤ P_ν ε⁴ s^{5/2} |η| N`, `B_j = s⁻¹ D_yY^mt(R/√s,0,0)`).

The estimate is the mean value inequality along the segment `t ↦ (R/√s, 0, t/√s)`, applied to
`t ↦ ∂_j Y^mt(chartY (s,(q,t)))`, whose derivative is `(1/√s) ∂_2 ∂_j Y^mt` (bounded by the
Y-Hessian hypothesis `MeanYHessAt`).  At `t = 0`, `∂_j Y^mt` is `s B_{·j}(s)` (the definition of
`Bjet`).  `Y^mt = YmtFun` is `C²` at the receiver since `Xmt` is `C⁴` there (`MeanSmoothAt`).
The constant of `MeanYHessAt` is reused unchanged, since `(1/√s) s³ = s^{5/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace MeanYTaylorP

/-- Mean value inequality in `ℝ≥0∞` form along the segment from `0` to `η`. -/
theorem enn_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f f' : ℝ → E) (η : ℝ) (B : ℝ≥0∞)
    (hf : ∀ t ∈ uIcc (0 : ℝ) η, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ uIcc (0 : ℝ) η, ‖f' t‖ₑ ≤ B) :
    ‖f η - f 0‖ₑ ≤ ENNReal.ofReal |η| * B := by
  by_cases hB : B = ⊤
  · by_cases hη : η = 0
    · subst hη; simp
    · rw [hB, ENNReal.mul_top (by simpa using hη)]
      exact le_top
  · have hreal : ∀ t ∈ uIcc (0 : ℝ) η, ‖f' t‖ ≤ B.toReal := by
      intro t ht
      have h := hb t ht
      rw [← ofReal_norm (f' t)] at h
      exact (ENNReal.ofReal_le_iff_le_toReal hB).1 h
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hf t ht).hasDerivWithinAt) hreal (convex_uIcc (0 : ℝ) η)
      left_mem_uIcc right_mem_uIcc
    rw [sub_zero, Real.norm_eq_abs] at hmv
    calc ‖f η - f 0‖ₑ = ENNReal.ofReal ‖f η - f 0‖ := (ofReal_norm (f η - f 0)).symm
      _ ≤ ENNReal.ofReal (B.toReal * |η|) := ENNReal.ofReal_le_ofReal hmv
      _ = ENNReal.ofReal |η| * B := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hB, mul_comm]

/-- The derivative of the vertical-segment restriction of `∂_j F` is `(1/√s) ∂_2 ∂_j F`. -/
theorem physPd_line_hasDeriv (F : Space → Space) (j : Fin 3) (R s q : ℝ) (_hs : 0 < s) (t : ℝ)
    (hF : ContDiffAt ℝ 2 F (NearInst.chartY R (s, (q, t)))) :
    HasDerivAt (fun t' => physPd F j (NearInst.chartY R (s, (q, t'))))
      ((1 / Real.sqrt s) • physPd2 F 2 j (NearInst.chartY R (s, (q, t)))) t := by
  have hd : DifferentiableAt ℝ (fun y' => physPd F j y') (NearInst.chartY R (s, (q, t))) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) (NearInst.chartY R (s, (q, t))) :=
      hF.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun y' => fderiv ℝ F y' (coordinateVector j))
        (NearInst.chartY R (s, (q, t))) := h1.clm_apply contDiffAt_const
    exact h2.differentiableAt (by norm_num)
  have hlin : ∀ t' : ℝ, NearInst.chartY R (s, (q, t')) =
      NearInst.chartY R (s, (q, 0)) + (t' / Real.sqrt s) • coordinateVector 2 := by
    intro t'
    ext i
    fin_cases i <;> simp [NearInst.chartY, coordinateVector]
  have hL : HasDerivAt (fun t' : ℝ => NearInst.chartY R (s, (q, t')))
      ((1 / Real.sqrt s) • coordinateVector 2) t := by
    have h0 := (((hasDerivAt_id t).div_const (Real.sqrt s)).smul_const (coordinateVector 2)).const_add
      (NearInst.chartY R (s, (q, 0)))
    have h1 : (fun t' : ℝ => NearInst.chartY R (s, (q, t'))) =
        fun t' => NearInst.chartY R (s, (q, 0)) + (t' / Real.sqrt s) • coordinateVector 2 :=
      funext hlin
    rw [h1]
    simpa using h0
  have h3 := hd.hasFDerivAt.comp_hasDerivAt t hL
  have key : fderiv ℝ (fun y' => physPd F j y') (NearInst.chartY R (s, (q, t)))
      ((1 / Real.sqrt s) • coordinateVector 2) =
      (1 / Real.sqrt s) • physPd2 F 2 j (NearInst.chartY R (s, (q, t))) := by
    rw [map_smul]
    rfl
  exact h3.congr_deriv key

/-- `YmtFun` is `C²` at `y` when `Xmt` is `C⁴` at `y`: `Y^mt = -½ y·∇X - νΔX + (μ+½)X`. -/
theorem ymtFun_contDiffAt (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (y : Vec3)
    (hX : ContDiffAt ℝ 4 (Xmt c ν ε μ χo χy M) y) :
    ContDiffAt ℝ 2 (YmtFun c ν ε μ χo χy M) y := by
  have hF3 : ContDiffAt ℝ 3 (fderiv ℝ (Xmt c ν ε μ χo χy M)) y :=
    hX.fderiv_right (m := 3) (by norm_num)
  have hF2 : ContDiffAt ℝ 2 (fderiv ℝ (Xmt c ν ε μ χo χy M)) y :=
    hF3.of_le (by norm_num)
  have hG : ∀ j : Fin 3, ContDiffAt ℝ 3
      (fun y' => fderiv ℝ (Xmt c ν ε μ χo χy M) y' (Pi.single j 1)) y :=
    fun j => hF3.clm_apply contDiffAt_const
  have hA : ContDiffAt ℝ 2 (fun y' => fderiv ℝ (Xmt c ν ε μ χo χy M) y' y') y :=
    hF2.clm_apply contDiffAt_id
  have hV : ContDiffAt ℝ 2 (fun y' => vecLap (Xmt c ν ε μ χo χy M) y') y := by
    unfold vecLap
    apply ContDiffAt.sum
    intro j _
    have hGd : ContDiffAt ℝ 2 (fderiv ℝ (fun y' => fderiv ℝ (Xmt c ν ε μ χo χy M) y'
        (Pi.single j 1))) y :=
      (hG j).fderiv_right (m := 2) (by norm_num)
    exact hGd.clm_apply contDiffAt_const
  have hX2 : ContDiffAt ℝ 2 (Xmt c ν ε μ χo χy M) y := hX.of_le (by norm_num)
  unfold YmtFun
  exact (((contDiffAt_const (𝕜 := ℝ) (c := -(1 / 2 : ℝ))).smul hA).sub
    ((contDiffAt_const (𝕜 := ℝ) (c := ν)).smul hV)).add
    ((contDiffAt_const (𝕜 := ℝ) (c := μ + 1 / 2)).smul hX2)

/-- `Ymean` is `C²` at `y` when `Xmt` is `C⁴` at `ofLp y`. -/
theorem ymean_contDiffAt (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (τ : ℝ) (y : Space)
    (hX : ContDiffAt ℝ 4 (Xmt c ν ε μ χo χy M) (WithLp.ofLp y)) :
    ContDiffAt ℝ 2 (Ymean c ν ε μ χo χy M τ) y :=
  (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (n := 2)).contDiffAt.comp y
    ((ymtFun_contDiffAt c ν ε μ χo χy M _ hX).comp y
      (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (n := 2)).contDiffAt)

/-- The base column: `∂_j Y^mt` at the young point with zero transverse coordinate is
`vecSp (∂_j YmtFun)` at `(ε⁻¹/√s, 0, 0)`. -/
theorem ymean_physPd_base (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (τ s q : ℝ)
    (_hs : 0 < s) (j : Fin 3)
    (hd : DifferentiableAt ℝ (YmtFun c ν ε μ χo χy M)
      (WithLp.ofLp (NearInst.chartY ε⁻¹ (s, (q, 0))))) :
    physPd (Ymean c ν ε μ χo χy M τ) j (NearInst.chartY ε⁻¹ (s, (q, 0))) =
      vecSp (fun i => fderiv ℝ (YmtFun c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0]
        (Pi.single j 1) i) := by
  have e1 := hd.hasFDerivAt.comp (NearInst.chartY ε⁻¹ (s, (q, 0)))
    (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (NearInst.chartY ε⁻¹ (s, (q, 0))))
  have e2 := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2
    (YmtFun c ν ε μ χo χy M (WithLp.ofLp (NearInst.chartY ε⁻¹ (s, (q, 0)))))).comp
    (NearInst.chartY ε⁻¹ (s, (q, 0))) e1
  have hYm : Ymean c ν ε μ χo χy M τ =
      fun y' => WithLp.toLp 2 (YmtFun c ν ε μ χo χy M (WithLp.ofLp y')) := rfl
  have hpt : WithLp.ofLp (NearInst.chartY ε⁻¹ (s, (q, 0))) = ![ε⁻¹ / Real.sqrt s, 0, 0] := by
    ext i
    fin_cases i <;> simp [NearInst.chartY]
  rw [physPd, hYm, show (fun y' => WithLp.toLp 2 (YmtFun c ν ε μ χo χy M (WithLp.ofLp y'))) =
      WithLp.toLp 2 ∘ YmtFun c ν ε μ χo χy M ∘ WithLp.ofLp from rfl, e2.fderiv]
  have hv : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))
      (EuclideanSpace.single j 1) = Pi.single j 1 := by
    ext k
    simp [Pi.single_apply]
  ext i
  simp [vecSp, hpt, coordinateVector, hv]

/-- Pulling the factor `s` of `B_j(s) = s⁻¹ D_yY^mt` into the vector: `s • vecSp (s⁻¹ a) = vecSp a`. -/
theorem vecSp_eq_smul_inv {s : ℝ} (hs : 0 < s) (a : Vec3) :
    vecSp a = s • vecSp (fun i => s⁻¹ * a i) := by
  ext i
  simp [vecSp, hs.ne']

/-- The power identity `(1/√s) s³ = s^{5/2}` in the form used by the Taylor estimate. -/
theorem sqrt_inv_mul_pow3 {s : ℝ} (hs : 0 < s) :
    (1 / Real.sqrt s) * s ^ (3 : ℝ) = s ^ (5 / 2 : ℝ) := by
  rw [one_div, Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le, ← Real.rpow_add hs]
  norm_num

/-- **The pointwise mean Y-Taylor estimate** (source 5438-5443): the Hessian bound along the
vertical segment and the smoothness at its points give the Taylor bound with the same constants. -/
theorem meanYTaylor_at (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ) (k : ℕ)
    (hH : MeanYHessAt Pl K L μ C k) (hS : MeanSmoothAt Pl K L μ) :
    MeanYTaylorAt Pl K L μ C k := by
  intro T p hp0 hp1 j
  obtain ⟨s, q, η⟩ := p
  have hs0 : 0 < s := hp0
  have hs1 : s ≤ 1 / L.ν := hp1
  set F : Space → Space := Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 with hFdef
  show ‖physPd F j (NearInst.chartY L.ε⁻¹ (s, (q, η))) -
      s • vecSp (fun i => Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s i j)‖ₑ ≤
    ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (5 / 2 : ℝ) * |η|) * oldN1 Pl K L T
  have hbase : physPd F j (NearInst.chartY L.ε⁻¹ (s, (q, 0))) =
      s • vecSp (fun i => Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s i j) := by
    have hS0 := hS T (s, (q, 0)) hs0 hs1
    have hd := (ymtFun_contDiffAt (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) _ hS0).differentiableAt
      (by norm_num)
    have h0 := ymean_physPd_base (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 s q hs0 j hd
    rw [hFdef, h0]
    exact vecSp_eq_smul_inv hs0 _
  have hcont : ∀ t ∈ uIcc (0 : ℝ) η, ContDiffAt ℝ 2 F (NearInst.chartY L.ε⁻¹ (s, (q, t))) := by
    intro t _
    have hS' := hS T (s, (q, t)) hs0 hs1
    exact ymean_contDiffAt _ _ _ _ _ _ _ 0 _ hS'
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) η, HasDerivAt
      (fun t' => physPd F j (NearInst.chartY L.ε⁻¹ (s, (q, t'))))
      ((1 / Real.sqrt s) • physPd2 F 2 j (NearInst.chartY L.ε⁻¹ (s, (q, t)))) t :=
    fun t ht => physPd_line_hasDeriv F j L.ε⁻¹ s q hs0 t (hcont t ht)
  have hbd : ∀ t ∈ uIcc (0 : ℝ) η,
      ‖physPd2 F 2 j (NearInst.chartY L.ε⁻¹ (s, (q, t)))‖ₑ ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (3 : ℝ)) * oldN1 Pl K L T :=
    fun t _ => hH T (s, (q, t)) hs0 hs1 2 j
  have hbound : ∀ t ∈ uIcc (0 : ℝ) η,
      ‖(1 / Real.sqrt s) • physPd2 F 2 j (NearInst.chartY L.ε⁻¹ (s, (q, t)))‖ₑ ≤
        ENNReal.ofReal (1 / Real.sqrt s) *
          (ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (3 : ℝ)) * oldN1 Pl K L T) := by
    intro t ht
    calc ‖(1 / Real.sqrt s) • physPd2 F 2 j (NearInst.chartY L.ε⁻¹ (s, (q, t)))‖ₑ
        ≤ ‖1 / Real.sqrt s‖ₑ * ‖physPd2 F 2 j (NearInst.chartY L.ε⁻¹ (s, (q, t)))‖ₑ :=
          enorm_smul_le
      _ ≤ ENNReal.ofReal (1 / Real.sqrt s) *
          (ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (3 : ℝ)) * oldN1 Pl K L T) := by
          rw [Real.enorm_eq_ofReal (by positivity)]
          exact mul_le_mul' le_rfl (hbd t ht)
  have hmv := enn_line (fun t => physPd F j (NearInst.chartY L.ε⁻¹ (s, (q, t))))
    (fun t => (1 / Real.sqrt s) • physPd2 F 2 j (NearInst.chartY L.ε⁻¹ (s, (q, t)))) η
    _ hderiv hbound
  rw [hbase] at hmv
  have hx : |η| * (1 / Real.sqrt s) * (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (3 : ℝ)) =
      C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (5 / 2 : ℝ) * |η| := by
    rw [← sqrt_inv_mul_pow3 hs0]
    ring
  refine hmv.trans (le_of_eq ?_)
  calc ENNReal.ofReal |η| * (ENNReal.ofReal (1 / Real.sqrt s) *
          (ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (3 : ℝ)) * oldN1 Pl K L T))
      = (ENNReal.ofReal |η| * ENNReal.ofReal (1 / Real.sqrt s) *
          ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (3 : ℝ))) * oldN1 Pl K L T := by ring
    _ = ENNReal.ofReal (|η| * (1 / Real.sqrt s) * (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (3 : ℝ))) *
          oldN1 Pl K L T := by
          rw [ENNReal.ofReal_mul (p := |η| * (1 / Real.sqrt s)) (by positivity),
            ENNReal.ofReal_mul (p := |η|) (abs_nonneg η)]
    _ = ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (5 / 2 : ℝ) * |η|) * oldN1 Pl K L T := by
          rw [hx]

end MeanYTaylorP


/-- **Mean Y-Taylor estimate** (source 5438-5443): the sequence-level statement from the
Y-Hessian estimate `MeanYHessSeq` and the smoothness `MeanSmoothSeq` (same constants). -/
theorem meanYTaylor (D : SeqData) {dm dp : ℝ} (hH : D.MeanYHessSeq dm dp)
    (hS : D.MeanSmoothSeq dm dp) : D.MeanYTaylorSeq dm dp := by
  intro hst
  obtain ⟨C, k, eH⟩ := hH hst
  have eS := hS hst
  refine ⟨C, k, ?_⟩
  filter_upwards [eH, eS] with n hn hsn z hz
  exact MeanYTaylorP.meanYTaylor_at D.Pl D.K (D.level n) (D.mu n z) C k (hn z hz) (hsn z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
