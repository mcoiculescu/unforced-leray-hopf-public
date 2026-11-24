import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Profile
import UnforcedLeray.Short.PartIIIa.Clock.Moving
import UnforcedLeray.Units.B0146

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: the comparison function

Source: SP 2861-2863 (`w(s,x) = a^{-2} W(z, x/√a)`, `W_z = θ⁻¹DW + L_{ν,c}W`), 2954-2956.

For a profile `Φ(z, y)` in moving variables, `cmp Φ ν s σ x = a(σ) Φ(z(σ) - z(s), x/√a(σ))`.
We compute its spatial derivatives (`pd_cmp`, `lapP_cmp`) and its age derivative
(`hasDerivAt_cmp`), and the residual `cmpRes = ∂_σ cmp + νΔ cmp + v·∇cmp` for a transported
profile (`cmpRes_eq`): `cmpRes = ν Q + √a (v - V_iso)·∇_y Φ` with `V_iso` the central vortex.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

/-- The `y`-partial derivative `∂_{y_j} Φ`. -/
def dY (Φ : ℝ × (ℝ × ℝ) → ℝ) (j : Fin 2) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ Φ p (0, B0579.dir j)

/-- The second `y`-partial derivative `∂²_{y_j} Φ`. -/
def dYY (Φ : ℝ × (ℝ × ℝ) → ℝ) (j : Fin 2) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ (dY Φ j) p (0, B0579.dir j)

/-- The `z`-partial derivative `∂_z Φ`. -/
def dZ (Φ : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ := fderiv ℝ Φ p (1, 0)

/-- The point `(z(σ) - z(s), x/√a(σ))` of the moving variables. -/
def cpt (ν s σ : ℝ) (x : ℝ × ℝ) : ℝ × (ℝ × ℝ) :=
  (movingZ ν σ - movingZ ν s, (Real.sqrt (clockA ν σ))⁻¹ • x)

/-- The comparison function `a(σ) Φ(z(σ) - z(s), x/√a(σ))`. -/
def cmp (Φ : ℝ × (ℝ × ℝ) → ℝ) (ν s σ : ℝ) (x : ℝ × ℝ) : ℝ :=
  clockA ν σ * Φ (cpt ν s σ x)

/-- Its age derivative. -/
def cmpDt (Φ : ℝ × (ℝ × ℝ) → ℝ) (ν s σ : ℝ) (x : ℝ × ℝ) : ℝ :=
  ν * Φ (cpt ν s σ x) + (clockA ν σ)⁻¹ * dZ Φ (cpt ν s σ x) -
    ν / 2 * fderiv ℝ Φ (cpt ν s σ x) (0, (cpt ν s σ x).2)

/-- The residual `∂_σ cmp + νΔ cmp + v·∇cmp`. -/
def cmpRes (Φ : ℝ × (ℝ × ℝ) → ℝ) (v : ℝ → ℝ × ℝ → UnforcedLeray.Train.Vec) (ν s σ : ℝ)
    (x : ℝ × ℝ) : ℝ :=
  cmpDt Φ ν s σ x + ν * lapP (cmp Φ ν s σ) x +
    (v σ x 0 * B0579.pd 0 (cmp Φ ν s σ) x + v σ x 1 * B0579.pd 1 (cmp Φ ν s σ) x)

/-- The bracket `Φ + Δ_yΦ - ½ y·∇_yΦ`. -/
def bracketQ (Φ : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  Φ p + (dYY Φ 0 p + dYY Φ 1 p) - 1 / 2 * fderiv ℝ Φ p (0, p.2)

theorem clockA_pos {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ) : 0 < clockA ν σ := by
  unfold clockA; nlinarith [mul_nonneg hν hσ]

/-! ## Spatial derivatives -/

theorem hasFDerivAt_slice_smul {F : ℝ × (ℝ × ℝ) → ℝ} (z r : ℝ) (x : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F (z, r • x)) :
    HasFDerivAt (fun x : ℝ × ℝ => F (z, r • x))
      ((fderiv ℝ F (z, r • x)).comp (r • ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x := by
  have h1 := hasFDerivAt_prodMk_right (𝕜 := ℝ) z (r • x)
  have h2 : HasFDerivAt (fun x : ℝ × ℝ => r • x) (r • ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_id x).const_smul r
  have h3 := h1.comp x h2
  have h4 : (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).comp (r • ContinuousLinearMap.id ℝ (ℝ × ℝ)) =
      r • ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) := by
    ext w <;> simp
  rw [h4] at h3
  exact hF.hasFDerivAt.comp x h3

theorem pd_slice_smul {F : ℝ × (ℝ × ℝ) → ℝ} (hF : Differentiable ℝ F) (z r : ℝ) (j : Fin 2)
    (x : ℝ × ℝ) :
    B0579.pd j (fun x : ℝ × ℝ => F (z, r • x)) x =
      r * fderiv ℝ F (z, r • x) (0, B0579.dir j) := by
  unfold B0579.pd
  rw [(hasFDerivAt_slice_smul z r x (hF _)).fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.inr_apply]
  rw [show (r • ((0 : ℝ), B0579.dir j) : ℝ × (ℝ × ℝ)) = r • ((0 : ℝ), B0579.dir j) from rfl,
    ContinuousLinearMap.map_smul, smul_eq_mul]

theorem differentiable_slice_smul {F : ℝ × (ℝ × ℝ) → ℝ} (hF : Differentiable ℝ F) (z r : ℝ) :
    Differentiable ℝ (fun x : ℝ × ℝ => F (z, r • x)) := fun x =>
  (hasFDerivAt_slice_smul z r x (hF _)).differentiableAt

theorem differentiable_dY {Φ : ℝ × (ℝ × ℝ) → ℝ} (hΦ : ContDiff ℝ 2 Φ) (j : Fin 2) :
    Differentiable ℝ (dY Φ j) := by
  have h : ContDiff ℝ 1 (fun p => fderiv ℝ Φ p) := hΦ.fderiv_right (by norm_num)
  exact (h.clm_apply contDiff_const).differentiable (by norm_num)

theorem contDiff_dY {Φ : ℝ × (ℝ × ℝ) → ℝ} (hΦ : ContDiff ℝ 2 Φ) (j : Fin 2) :
    ContDiff ℝ 1 (dY Φ j) := by
  have h : ContDiff ℝ 1 (fun p => fderiv ℝ Φ p) := hΦ.fderiv_right (by norm_num)
  exact h.clm_apply contDiff_const

theorem pd_cmp {Φ : ℝ × (ℝ × ℝ) → ℝ} (hΦ : Differentiable ℝ Φ) (ν s σ : ℝ) (j : Fin 2) :
    B0579.pd j (cmp Φ ν s σ) = fun x =>
      clockA ν σ * (Real.sqrt (clockA ν σ))⁻¹ * dY Φ j (cpt ν s σ x) := by
  funext x
  have h := pd_slice_smul hΦ (movingZ ν σ - movingZ ν s) (Real.sqrt (clockA ν σ))⁻¹ j x
  have hd := differentiable_slice_smul hΦ (movingZ ν σ - movingZ ν s) (Real.sqrt (clockA ν σ))⁻¹
  unfold B0579.pd at h ⊢
  have e : cmp Φ ν s σ = fun x => clockA ν σ *
      (fun x : ℝ × ℝ => Φ (movingZ ν σ - movingZ ν s, (Real.sqrt (clockA ν σ))⁻¹ • x)) x := rfl
  rw [e, fderiv_const_mul (hd x), ContinuousLinearMap.smul_apply, h, smul_eq_mul]
  simp only [dY, cpt]
  ring

theorem lapP_cmp {Φ : ℝ × (ℝ × ℝ) → ℝ} (hΦ : ContDiff ℝ 2 Φ) {ν s σ : ℝ} (hν : 0 ≤ ν)
    (hσ : 0 ≤ σ) (x : ℝ × ℝ) :
    lapP (cmp Φ ν s σ) x = dYY Φ 0 (cpt ν s σ x) + dYY Φ 1 (cpt ν s σ x) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have ha := clockA_pos hν hσ
  have hsq : Real.sqrt (clockA ν σ) ^ 2 = clockA ν σ := Real.sq_sqrt ha.le
  have hsq0 : Real.sqrt (clockA ν σ) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have key : ∀ j : Fin 2, B0579.pd j (B0579.pd j (cmp Φ ν s σ)) x = dYY Φ j (cpt ν s σ x) := by
    intro j
    rw [pd_cmp hΦd]
    have hdY := differentiable_dY hΦ j
    have h := pd_slice_smul hdY (movingZ ν σ - movingZ ν s) (Real.sqrt (clockA ν σ))⁻¹ j x
    have hd := differentiable_slice_smul hdY (movingZ ν σ - movingZ ν s)
      (Real.sqrt (clockA ν σ))⁻¹
    unfold B0579.pd at h ⊢
    have e : (fun x => clockA ν σ * (Real.sqrt (clockA ν σ))⁻¹ * dY Φ j (cpt ν s σ x)) =
        fun x => clockA ν σ * (Real.sqrt (clockA ν σ))⁻¹ *
          (fun x : ℝ × ℝ => dY Φ j (movingZ ν σ - movingZ ν s,
            (Real.sqrt (clockA ν σ))⁻¹ • x)) x := rfl
    rw [e, fderiv_const_mul (hd x), ContinuousLinearMap.smul_apply, h, smul_eq_mul]
    have hk : clockA ν σ * (Real.sqrt (clockA ν σ))⁻¹ * (Real.sqrt (clockA ν σ))⁻¹ = 1 := by
      rw [mul_assoc, ← mul_inv, ← sq, hsq, mul_inv_cancel₀ ha.ne']
    simp only [dYY, cpt]
    rw [← mul_assoc, hk, one_mul]
  unfold lapP
  rw [key 0, key 1]

/-! ## The age derivative -/

theorem hasDerivAt_clockA (ν σ : ℝ) : HasDerivAt (fun σ => clockA ν σ) ν σ := by
  unfold clockA
  simpa using ((hasDerivAt_id' σ).const_mul ν).const_add 1

theorem hasDerivAt_movingZ {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ) :
    HasDerivAt (fun σ => movingZ ν σ) ((clockA ν σ)⁻¹ ^ 2) σ := by
  have ha := clockA_pos hν hσ
  have h2 := (hasDerivAt_id' σ).div (hasDerivAt_clockA ν σ) ha.ne'
  have ha' : 1 + ν * σ ≠ 0 := by unfold clockA at ha; exact ha.ne'
  have e : (1 * clockA ν σ - σ * ν) / clockA ν σ ^ 2 = (clockA ν σ)⁻¹ ^ 2 := by
    unfold clockA; field_simp; ring
  rw [e] at h2
  exact h2

theorem hasDerivAt_invSqrtA {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ) :
    HasDerivAt (fun σ => (Real.sqrt (clockA ν σ))⁻¹)
      (-(ν / (2 * Real.sqrt (clockA ν σ))) / Real.sqrt (clockA ν σ) ^ 2) σ := by
  have ha := clockA_pos hν hσ
  have h1 := (hasDerivAt_clockA ν σ).sqrt ha.ne'
  have h2 := h1.inv (Real.sqrt_pos.2 ha).ne'
  exact h2

theorem hasDerivAt_cpt {ν s σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (x : ℝ × ℝ) :
    HasDerivAt (fun σ => cpt ν s σ x)
      ((clockA ν σ)⁻¹ ^ 2,
        (-(ν / (2 * Real.sqrt (clockA ν σ))) / Real.sqrt (clockA ν σ) ^ 2) • x) σ := by
  have hz := (hasDerivAt_movingZ hν hσ).sub_const (movingZ ν s)
  have hr := (hasDerivAt_invSqrtA hν hσ).smul_const x
  exact hz.prodMk hr

theorem hasDerivAt_cmp {Φ : ℝ × (ℝ × ℝ) → ℝ} (hΦ : Differentiable ℝ Φ) {ν s σ : ℝ}
    (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (x : ℝ × ℝ) :
    HasDerivAt (fun σ => cmp Φ ν s σ x) (cmpDt Φ ν s σ x) σ := by
  have ha := clockA_pos hν hσ
  have hsa := Real.sqrt_pos.2 ha
  have hsq : Real.sqrt (clockA ν σ) ^ 2 = clockA ν σ := Real.sq_sqrt ha.le
  have hc := hasDerivAt_cpt (s := s) hν hσ x
  have hΦc := (hΦ (cpt ν s σ x)).hasFDerivAt.comp_hasDerivAt σ hc
  have hprod := (hasDerivAt_clockA ν σ).mul hΦc
  -- algebra
  have hsa' : Real.sqrt (clockA ν σ) ≠ 0 := hsa.ne'
  have hsplit : ((clockA ν σ)⁻¹ ^ 2,
      (-(ν / (2 * Real.sqrt (clockA ν σ))) / Real.sqrt (clockA ν σ) ^ 2) • x) =
      ((clockA ν σ)⁻¹ ^ 2) • ((1 : ℝ), (0 : ℝ × ℝ)) +
        (-(ν / (2 * Real.sqrt (clockA ν σ))) / Real.sqrt (clockA ν σ) ^ 2 *
          Real.sqrt (clockA ν σ)) • ((0 : ℝ), (cpt ν s σ x).2) := by
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add, cpt, smul_smul]
      congr 1
      field_simp
  have hval : ν * (Φ ∘ fun σ => cpt ν s σ x) σ + clockA ν σ * fderiv ℝ Φ (cpt ν s σ x)
      ((clockA ν σ)⁻¹ ^ 2,
        (-(ν / (2 * Real.sqrt (clockA ν σ))) / Real.sqrt (clockA ν σ) ^ 2) • x) =
      cmpDt Φ ν s σ x := by
    rw [hsplit, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    unfold cmpDt dZ
    simp only [Function.comp_apply]
    rw [hsq]
    field_simp
    ring
  rw [hval] at hprod
  exact hprod

/-! ## The residual for a transported profile -/

theorem vortV_eq_iso {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (x : ℝ × ℝ) :
    vortV ((Real.sqrt (clockA ν σ))⁻¹ • x) =
      (clockA ν σ * Real.sqrt (clockA ν σ)) • UnforcedLeray.B0146.isoVelocity ν σ x := by
  have ha := clockA_pos hν hσ
  have hsa := Real.sqrt_pos.2 ha
  have hsq : Real.sqrt (clockA ν σ) ^ 2 = clockA ν σ := Real.sq_sqrt ha.le
  rw [UnforcedLeray.B0146.isoVelocity_eq]
  have hw : UnforcedLeray.B0113.heatWidth ν σ = clockA ν σ := rfl
  rw [hw]
  have hg : omg ((Real.sqrt (clockA ν σ))⁻¹ • x) =
      UnforcedLeray.B0113.gw (clockA ν σ) x := by
    simp only [omg, UnforcedLeray.B0113.gw, UnforcedLeray.GaussianVortex.radiusSq,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    congr 1
    field_simp
    rw [hsq]
    ring
  simp only [vortV, UnforcedLeray.B0113.vExp, hg, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Prod.mk.injEq]
  constructor
  · field_simp
    rw [hsq]; ring
  · field_simp
    rw [hsq]; ring

/-- **The residual of the transported comparison function** (SP 2861-2863, 2954-2956):
`∂_σ cmp + νΔ cmp + v·∇cmp = ν Q + √a (v - V_iso)·∇_yΦ`, `Q = Φ + Δ_yΦ - ½ y·∇_yΦ`. -/
theorem cmpRes_eq {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {ν s σ : ℝ} (hν : 0 ≤ ν)
    (hσ : 0 ≤ σ) (v : ℝ → ℝ × ℝ → UnforcedLeray.Train.Vec) (x : ℝ × ℝ) :
    cmpRes (tprof g) v ν s σ x = ν * bracketQ (tprof g) (cpt ν s σ x) +
      Real.sqrt (clockA ν σ) *
        ((v σ x 0 - (UnforcedLeray.B0146.isoVelocity ν σ x).1) * dY (tprof g) 0 (cpt ν s σ x) +
          (v σ x 1 - (UnforcedLeray.B0146.isoVelocity ν σ x).2) *
            dY (tprof g) 1 (cpt ν s σ x)) := by
  have hΦ : ContDiff ℝ 2 (tprof g) := contDiff_infty.1 (contDiff_tprof hg) 2
  have hΦd : Differentiable ℝ (tprof g) := hΦ.differentiable (by norm_num)
  have ha := clockA_pos hν hσ
  have hsa := Real.sqrt_pos.2 ha
  have hsq : Real.sqrt (clockA ν σ) ^ 2 = clockA ν σ := Real.sq_sqrt ha.le
  set y := (Real.sqrt (clockA ν σ))⁻¹ • x with hy
  set p := cpt ν s σ x with hp
  have hp' : p = (movingZ ν σ - movingZ ν s, y) := rfl
  set L := fderiv ℝ (tprof g) p with hL
  -- the transport identity at `p`
  have hT : L ((1 : ℝ), vortV y) = 0 := by
    rw [hL, hp']
    exact fderiv_tprof_vort (hΦd _)
  have hsplitV : ((1 : ℝ), vortV y) = ((1 : ℝ), (0 : ℝ × ℝ)) +
      (vortV y).1 • ((0 : ℝ), B0579.dir 0) + (vortV y).2 • ((0 : ℝ), B0579.dir 1) := by
    refine Prod.ext ?_ ?_
    · simp
    · refine Prod.ext ?_ ?_ <;> simp [B0579.dir]
  rw [hsplitV, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hT
  have hV := vortV_eq_iso hν hσ x
  rw [← hy] at hV
  have hV1 : (vortV y).1 = clockA ν σ * Real.sqrt (clockA ν σ) *
      (UnforcedLeray.B0146.isoVelocity ν σ x).1 := by rw [hV]; rfl
  have hV2 : (vortV y).2 = clockA ν σ * Real.sqrt (clockA ν σ) *
      (UnforcedLeray.B0146.isoVelocity ν σ x).2 := by rw [hV]; rfl
  rw [hV1, hV2] at hT
  have hdZ : dZ (tprof g) p = L (1, 0) := rfl
  have hdY0 : dY (tprof g) 0 p = L (0, B0579.dir 0) := rfl
  have hdY1 : dY (tprof g) 1 p = L (0, B0579.dir 1) := rfl
  unfold cmpRes cmpDt bracketQ
  rw [lapP_cmp hΦ hν hσ, pd_cmp hΦd, pd_cmp hΦd]
  simp only []
  rw [← hp, hdZ, hdY0, hdY1]
  have hpy : p.2 = y := rfl
  rw [hpy, ← hL]
  have hka : clockA ν σ * (Real.sqrt (clockA ν σ))⁻¹ = Real.sqrt (clockA ν σ) := by
    field_simp
    rw [hsq]
  rw [hka]
  have hinv : (clockA ν σ)⁻¹ * (clockA ν σ * Real.sqrt (clockA ν σ)) =
      Real.sqrt (clockA ν σ) := by
    field_simp
  have hai : clockA ν σ * (clockA ν σ)⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  linear_combination (clockA ν σ)⁻¹ * hT - Real.sqrt (clockA ν σ) *
    (L (0, B0579.dir 0) * (UnforcedLeray.B0146.isoVelocity ν σ x).1 +
      L (0, B0579.dir 1) * (UnforcedLeray.B0146.isoVelocity ν σ x).2) * hai

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
