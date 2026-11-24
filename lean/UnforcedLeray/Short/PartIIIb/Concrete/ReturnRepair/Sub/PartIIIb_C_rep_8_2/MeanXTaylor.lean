import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_2

/-!
# `PartIII-b:C/rep/8/2/2/4`: the mean transverse Taylor estimate `MeanXTaylor`

Source `the November 2 reference manuscript`
5438-5448 (mean transverse Taylor estimate along the vertical segment of constant radius), 5380-5387.

The estimate is the mean value inequality along the segment `t ↦ (R/√s, 0, t/√s)`, `t` between
`0` and `η`, applied to `t ↦ ∂_j X^mt(chartY (s,(q,t)))`, whose derivative is
`(1/√s) ∂_2 ∂_j X^mt` (bounded by the Hessian hypothesis `MeanXHessAt`), together with the identity
`∂_j X^mt(chartY (s,(q,0))) = 𝓛T₁(s)` (the column `LjFun`).  The constant of `MeanXHessAt` is reused
unchanged, since `(1/√s) s³ = s^{5/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace MeanXTaylorP

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

/-- `Xmean` is `C⁴` at `y` when `Xmt` is `C⁴` at `ofLp y`. -/
theorem xmean_contDiffAt (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (τ : ℝ) (y : Space)
    (hX : ContDiffAt ℝ 4 (Xmt c ν ε μ χo χy M) (WithLp.ofLp y)) :
    ContDiffAt ℝ 4 (Xmean c ν ε μ χo χy M τ) y :=
  (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (n := 4)).contDiffAt.comp y
    (hX.comp y (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (n := 4)).contDiffAt)

/-- The base column: `∂_j X^mt` at the young point with zero transverse coordinate is `𝓛T₁(s)`. -/
theorem xmean_physPd_base (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (τ s q : ℝ)
    (hs : 0 < s) (j : Fin 3)
    (hd : DifferentiableAt ℝ (Xmt c ν ε μ χo χy M) (WithLp.ofLp (NearInst.chartY ε⁻¹ (s, (q, 0))))) :
    physPd (Xmean c ν ε μ χo χy M τ) j (NearInst.chartY ε⁻¹ (s, (q, 0))) =
      vecSp (fun i => Lpt c ν ε μ χo χy M s i j) := by
  have e1 := hd.hasFDerivAt.comp (NearInst.chartY ε⁻¹ (s, (q, 0)))
    (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (NearInst.chartY ε⁻¹ (s, (q, 0))))
  have e2 := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2
    (Xmt c ν ε μ χo χy M (WithLp.ofLp (NearInst.chartY ε⁻¹ (s, (q, 0)))))).comp
    (NearInst.chartY ε⁻¹ (s, (q, 0))) e1
  have hXm : Xmean c ν ε μ χo χy M τ =
      fun y' => WithLp.toLp 2 (Xmt c ν ε μ χo χy M (WithLp.ofLp y')) := rfl
  have hpt : WithLp.ofLp (NearInst.chartY ε⁻¹ (s, (q, 0))) = ![ε⁻¹ / Real.sqrt s, 0, 0] := by
    ext i
    fin_cases i <;> simp [NearInst.chartY]
  rw [physPd, hXm, show (fun y' => WithLp.toLp 2 (Xmt c ν ε μ χo χy M (WithLp.ofLp y'))) =
      WithLp.toLp 2 ∘ Xmt c ν ε μ χo χy M ∘ WithLp.ofLp from rfl, e2.fderiv]
  simp only [Lpt, if_pos hs]
  have hv : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))
      (EuclideanSpace.single j 1) = Pi.single j 1 := by
    ext k
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  ext i
  simp [vecSp, hpt, coordinateVector, hv]

/-- The power identity `(1/√s) s³ = s^{5/2}` in the form used by the Taylor estimate. -/
theorem sqrt_inv_mul_pow3 {s : ℝ} (hs : 0 < s) :
    (1 / Real.sqrt s) * s ^ (3 : ℝ) = s ^ (5 / 2 : ℝ) := by
  rw [one_div, Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le, ← Real.rpow_add hs]
  norm_num

/-- **The pointwise mean transverse Taylor estimate** (source 5438-5443): the Hessian bound along
the vertical segment and the smoothness at its points give the Taylor bound with the same constants. -/
theorem meanXTaylor_at (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ) (k : ℕ)
    (hH : MeanXHessAt Pl K L μ C k) (hS : MeanSmoothAt Pl K L μ) :
    MeanXTaylorAt Pl K L μ C k := by
  intro T p hp0 hp1 j
  obtain ⟨s, q, η⟩ := p
  have hs0 : 0 < s := hp0
  have hs1 : s ≤ 1 / L.ν := hp1
  set F : Space → Space := Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 with hFdef
  show ‖physPd F j (NearInst.chartY L.ε⁻¹ (s, (q, η))) -
      vecSp (fun i => LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T s i j)‖ₑ ≤
    ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (5 / 2 : ℝ) * |η|) * oldN1 Pl K L T
  have hbase : physPd F j (NearInst.chartY L.ε⁻¹ (s, (q, 0))) =
      vecSp (fun i => LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T s i j) := by
    have hS0 := hS T (s, (q, 0)) hs0 hs1
    exact xmean_physPd_base _ _ _ _ _ _ _ 0 s q hs0 j (hS0.differentiableAt (by norm_num))
  have hcont : ∀ t ∈ uIcc (0 : ℝ) η, ContDiffAt ℝ 2 F (NearInst.chartY L.ε⁻¹ (s, (q, t))) := by
    intro t _
    have hS' := hS T (s, (q, t)) hs0 hs1
    exact (xmean_contDiffAt _ _ _ _ _ _ _ 0 _ hS').of_le (by norm_num)
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

end MeanXTaylorP


/-- **Mean transverse Taylor estimate** (source 5438-5443): the sequence-level statement from the
Hessian estimate `MeanXHessSeq` and the smoothness `MeanSmoothSeq` (same constants). -/
theorem meanXTaylor (D : SeqData) {dm dp : ℝ} (hH : D.MeanXHessSeq dm dp)
    (hS : D.MeanSmoothSeq dm dp) : D.MeanXTaylorSeq dm dp := by
  intro hst
  obtain ⟨C, k, eH⟩ := hH hst
  have eS := hS hst
  refine ⟨C, k, ?_⟩
  filter_upwards [eH, eS] with n hn hsn z hz
  exact MeanXTaylorP.meanXTaylor_at D.Pl D.K (D.level n) (D.mu n z) C k (hn z hz) (hsn z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
end
