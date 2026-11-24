import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelExteriorBlockBound.Density

/-!
# The exterior block of the relative Duhamel evolution (helper for `RelExteriorBlockBound`)

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2945
(`\overline F(z,t)=I_zF(z,t)R_t+S(z,t)(I-\Pi_t)`, `Sf(y)=\rho^4f(\rho y)`) and 2974-2980 (the
localized interaction reads only the cell).

* `movDampedComplInt_eq_zero`, `dampedInt_apply_eq_zero`: `A_rel τ` kills data vanishing on the cell
  `d(r)` (all its integrals run over `B0579.cell d(r)`; density of smooth data,
  `RelExteriorSub.exists_smooth_approx_vanishing`).
* `freeBlock_exterior_vanish`, `freeBlock_exterior_eq_smul`: with `f = 0`, `ω₀ = 0`, the pin
  `IsPeriodizedRelFreeBlockEvol` gives `F_rel τ 0 W = 0` on the cell `d(r)` and
  `F_rel B 0 W = (clockN)⁻¹ • extDilW W` for `W` vanishing on the entrance cell.
* `duhamel_eq_free_of_kill`: Gronwall, `U(t,0)x = F(t,0)x` when `A(r) F(r,0) x = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open CompactDuhamelGapSub BlockPropagatorSub BlockPropagatorInteriorSub OrgSplit

namespace RelExteriorSub

/-! ### The localized interaction reads only the cell -/

theorem movDampedComplInt_eq_zero (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) {Φ : ℝ × ℝ → ℂ}
    (hΦ : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)), Φ y = 0) (y : ℝ × ℝ) :
    movDampedComplInt κ P tr r Φ y = 0 := by
  have hK : ∀ k : Fin 2, kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) Φ y k = 0 := by
    intro k
    unfold kerVelCx
    exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [hΦ z hz, zero_mul]
  have hL : ∀ j : Fin 2, movLamPair κ ν r j Φ = 0 := by
    intro j
    unfold movLamPair movingCell
    exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [hΦ z hz, mul_zero]
  have hH : ∀ i : Fin 2, movH0 κ tr r i Φ = 0 := by
    intro i
    unfold movH0 movingCell
    rw [setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [hΦ z hz, mul_zero], mul_zero]
  unfold movDampedComplInt movLInt movFrameRankPert
  simp only [hK, hL, hH]
  simp

/-- `A_rel τ` vanishes on data vanishing a.e. on the cell `d(r)`, `r = ageAt ν t₁ τ`. -/
theorem dampedInt_apply_eq_zero {κ : PlanarFrameKernels} {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hA : IsDampedComplBlockInt κ P ν m tr t₁ B A_rel) {τ : ℝ} (hτ : τ ∈ Icc 0 B)
    (hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (V : Planar.L2w m)
    (hV : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) →
        (V : ℂ → ℂ) z = 0) :
    A_rel τ V = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖A_rel τ V‖ ≤ ‖A_rel τ‖ * ε := by
    intro ε hε
    obtain ⟨Φ, hΦs, hΦc, hΦ0, W, hW, hWV⟩ := exists_smooth_approx_vanishing hd V hV hε
    have hAW : A_rel τ W = 0 := by
      have h := hA τ hτ Φ hΦs hΦc W hW
      have hz0 : movDampedComplInt κ P tr (ageAt ν t₁ τ) Φ = fun _ => 0 :=
        funext (movDampedComplInt_eq_zero κ P tr _ hΦ0)
      have h' : ⇑(A_rel τ W) =ᵐ[Planar.wMeasure m] fun z : ℂ =>
          cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
            (movDampedComplInt κ P tr (ageAt ν t₁ τ) Φ) (cToPlane z) :=
        (Planar.wMeasure_ac m).ae_le h
      have h0 : ⇑(A_rel τ W) =ᵐ[Planar.wMeasure m] ⇑(0 : Planar.L2w m) := by
        refine h'.trans ?_
        refine (Filter.EventuallyEq.trans ?_ (Lp.coeFn_zero _ _ _).symm)
        refine Eventually.of_forall fun z => ?_
        simp [hz0, cellZeroExt]
      exact Lp.ext h0
    calc ‖A_rel τ V‖ = ‖A_rel τ (V - W)‖ := by rw [map_sub, hAW, sub_zero]
      _ ≤ ‖A_rel τ‖ * ‖V - W‖ := (A_rel τ).le_opNorm _
      _ ≤ ‖A_rel τ‖ * ε := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_left hWV.le (norm_nonneg _)
  have hn : ‖A_rel τ V‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    by_contra hpos
    have hx : 0 < ‖A_rel τ V‖ := lt_of_not_ge hpos
    have ha : 0 ≤ ‖A_rel τ‖ := norm_nonneg _
    have h1 := key (‖A_rel τ V‖ / (‖A_rel τ‖ + 1)) (by positivity)
    have h2 : ‖A_rel τ‖ * (‖A_rel τ V‖ / (‖A_rel τ‖ + 1)) < ‖A_rel τ V‖ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  exact norm_eq_zero.1 hn

/-! ### The zero cylinder datum and its free flow -/

theorem isCylTest_zero (c : ℝ) : B0579.IsCylTest c (fun _ => (0 : ℝ)) where
  smooth := contDiff_const
  periodic _ := rfl
  band := ⟨0, fun _ _ => rfl⟩

theorem cylFreeIntegrand_zero {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ)
    (φ : B0579.Plane → ℝ) :
    UnforcedLeray.Short.IIb.cylFreeIntegrand tr (fun _ => (0 : ℝ)) r φ = fun _ => 0 := by
  funext x
  simp [UnforcedLeray.Short.IIb.cylFreeIntegrand]

theorem isFreeCylFlow_zero {ν c : ℝ} (m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t₀ : ℝ) :
    UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t₀ (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) where
  initial := EventuallyEq.rfl
  memX _ _ := MemLp.zero'
  strongCont _ _ := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) _ _)
  integrable _ _ _ _ := by
    simp only [cylFreeIntegrand_zero]
    exact integrableOn_zero
  timeIntegrable _ _ _ _ := by
    simp [cylFreeIntegrand_zero]
  weak _ _ _ _ := by
    simp [cylFreeIntegrand_zero]

/-! ### Ages and cells along the block -/

theorem ageAt_nonneg {ν t₁ t₂ τ : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hB : 0 ≤ τ) (hτ : τ ≤ movingZ ν t₂ - movingZ ν t₁) : 0 ≤ ageAt ν t₁ τ := by
  unfold ageAt
  have ha₁ : 0 < clockA ν t₁ := by unfold clockA; positivity
  have ha₂ : 0 < clockA ν t₂ := by unfold clockA; positivity
  have hz₁ : 0 ≤ movingZ ν t₁ := by unfold movingZ; positivity
  have hz₂ : ν * movingZ ν t₂ < 1 := by
    unfold movingZ
    rw [mul_div_assoc', div_lt_one ha₂]
    unfold clockA
    linarith
  refine FrameStableSub.moveAgeOfZ_nonneg (by linarith) ?_
  nlinarith

theorem cellLen_pos {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by
  unfold cellLen
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  exact div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha)

/-! ### The free block on exterior data -/

/-- The pin of `IsPeriodizedRelFreeBlockEvol` at `σ = 0` with `f = 0`, `ω₀ = 0`. -/
theorem freeBlock_exterior_ae {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτB : τ ≤ B) (W : Planar.L2w m)
    (hW : IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W) :
    ⇑(F_rel τ 0 W) =ᵐ[volume] fun z : ℂ =>
      ((clockN P ν t₁ (ageAt ν t₁ τ) : ℂ)⁻¹) *
        periodizedExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))
          (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
          (fun _ => 0) (fun y => (W : ℂ → ℂ) (planeToC y)) (cToPlane z) := by
  have h0 : ageAt ν t₁ 0 = t₁ := ageAt_zero hν ht₁
  have hcell : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ 0))) →
        (W : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ 0))
          (fun x => (((fun _ : B0579.Plane => (0 : ℝ)) x : ℝ) : ℂ)) (cToPlane z) := by
    rw [h0]
    filter_upwards [hW] with z hz hmem
    rw [hz hmem]
    simp [JscaleInv]
  have h := hF 0 τ le_rfl hτ0 hτB (fun _ => 0) (isCylTest_zero _) (fun _ _ => 0)
    (isFreeCylFlow_zero m tr _) W hcell
  filter_upwards [h] with z hz
  rw [hz]
  have hJ : JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((((fun _ _ => (0 : ℝ)) :
      ℝ → B0579.Plane → ℝ) (ageAt ν t₁ τ) x : ℝ) : ℂ)) = fun _ => 0 := by
    funext y
    simp [JscaleInv]
  simp only [h0, hJ]

/-- `F_rel τ 0 W` vanishes on the cell `d(r)`, `r = ageAt ν t₁ τ`, for `W` vanishing on the
entrance cell. -/
theorem freeBlock_exterior_vanish {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτB : τ ≤ B)
    (hdτ : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (W : Planar.L2w m)
    (hW : IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) →
        (F_rel τ 0 W : ℂ → ℂ) z = 0 := by
  have hd₁ : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁) := cellLen_pos hν ht₁
  filter_upwards [freeBlock_exterior_ae hF hν ht₁ hτ0 hτB W hW] with z hz hmem
  rw [hz, periodizedExt_apply_of_mem hd₁ hdτ _ _ hmem, mul_zero]

/-- On data vanishing on the entrance cell, `F_rel B 0 W = (clockN)⁻¹ • S(t₂, t₁) W`. -/
theorem freeBlock_exterior_eq_smul {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ t₂ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    (hB : 0 ≤ B) (ht₂B : ageAt ν t₁ B = t₂) (hm : 1 < m)
    (hd₁ : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))
    (hd₂ : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) (W : Planar.L2w m)
    (hW : IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W) :
    F_rel B 0 W = ((clockN P ν t₁ t₂ : ℂ)⁻¹) • extDilW hm hd₁ hd₂ W := by
  set d₁ := cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁) with hd₁def
  set d₂ := cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂) with hd₂def
  set ρ : ℝ := d₁ / d₂ with hρdef
  have hρ : 0 < ρ := div_pos hd₁ hd₂
  have hpin := freeBlock_exterior_ae hF hν ht₁ hB le_rfl W hW
  rw [ht₂B] at hpin
  -- the exterior vanishing transported by the dilation `z ↦ ρ • z`
  have hW' : ∀ᵐ z ∂(volume : Measure ℂ), cToPlane (ρ • z) ∈ B0579.cell d₁ →
      (W : ℂ → ℂ) (ρ • z) = 0 :=
    (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℂ)) hρ.ne').ae hW
  -- the dilation constants
  set a : ℝ := ((d₁ / d₂) ^ 2)⁻¹ with hadef
  have ha : 0 < a := inv_pos.2 (sq_pos_of_pos hρ)
  have hsa : (√a)⁻¹ = ρ := by
    rw [hadef, Real.sqrt_inv, inv_inv, Real.sqrt_sq hρ.le]
  have ha2 : (a ^ 2)⁻¹ = ρ ^ 4 := by
    rw [hadef, inv_pow, inv_inv, ← pow_mul]
  have hdil := Planar.coeFn_dilW hm ha W
  have hsm := Lp.coeFn_smul ((clockN P ν t₁ t₂ : ℂ)⁻¹) (extDilW hm hd₁ hd₂ W)
  refine Lp.ext ?_
  refine (Planar.wMeasure_ac m).ae_le ?_
  have hdil' := (Planar.volume_ac m).ae_le hdil
  have hsm' := (Planar.volume_ac m).ae_le hsm
  filter_upwards [hpin, hdil', hsm', hW'] with z h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, smul_eq_mul]
  have h2' : (extDilW hm hd₁ hd₂ W : ℂ → ℂ) z = (((a ^ 2)⁻¹ : ℝ) : ℂ) * (W : ℂ → ℂ) ((√a)⁻¹ • z) :=
    h2
  rw [h2', hsa, ha2]
  congr 1
  have hpl : planeToC (ρ * z.re, ρ * z.im) = ρ • z := by
    apply Complex.ext <;> simp [planeToC]
  have hcp : cToPlane (ρ • z) = (ρ * z.re, ρ * z.im) := by
    simp [cToPlane]
  have hzero : ∀ (s : Set (ℝ × ℝ)) (y : ℝ × ℝ), s.indicator (fun _ => (0 : ℂ)) y = 0 :=
    fun s y => by simp [Set.indicator_apply]
  unfold periodizedExt extDilCocycle
  simp only [cellZeroExt, hzero, zero_add, cToPlane]
  rw [← hρdef]
  by_cases hmem : (ρ * z.re, ρ * z.im) ∈ B0579.cell d₁
  · rw [Set.indicator_of_mem hmem, sub_self, mul_zero]
    have := h4 (by rw [hcp]; exact hmem)
    rw [this, mul_zero]
  · rw [Set.indicator_of_notMem hmem, sub_zero, hpl]

/-! ### Gronwall: the evolution is free when the interaction kills the free orbit -/

theorem duhamel_eq_free_of_kill {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {B M K : ℝ} {F : ℝ → ℝ → H →L[ℂ] H} {A : ℝ → H →L[ℂ] H}
    {U : ℝ → ℝ → H →L[ℂ] H}
    (hU : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => F) (fun _ => A)
      (fun _ => U))
    (hF : ∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F τ σ‖ ≤ M) (hA : ∀ τ, ‖A τ‖ ≤ K) (x : H)
    (hkill : ∀ r, 0 ≤ r → r ≤ B → A r (F r 0 x) = 0) :
    ∀ t, 0 ≤ t → t ≤ B → U t 0 x = F t 0 x := by
  intro t ht0 htB
  have hB0 : 0 ≤ B := ht0.trans htB
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF 0 0 le_rfl (by linarith))
  have hK : 0 ≤ K := (norm_nonneg _).trans (hA 0)
  obtain ⟨C, hC⟩ := hU.bounded () 0
  have G := UnforcedLeray.B0104.gronwall_family (I := Unit) (fun _ t => ‖U t 0 x - F t 0 x‖)
    (s := 0) (B := B) (a := 0) (L := M * K) (C := C * ‖x‖ + M * ‖x‖) le_rfl (by positivity)
    (fun _ t h1 h2 => (norm_sub_le _ _).trans (add_le_add
      (((U t 0).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hC t h1 h2) (norm_nonneg _)))
      (((F t 0).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hF 0 t h1 h2) (norm_nonneg _)))))
    (fun g hg t h1 h2 _ hφ _ => by
      have hd : U t 0 x = F t 0 x + ∫ r in (0 : ℝ)..t, F t r (A r (U r 0 x)) :=
        hU.duhamel () 0 t h1 h2 x
      have h2' : t ≤ B := by linarith
      show ‖U t 0 x - F t 0 x‖ ≤ 0 + M * K * ∫ r in (0 : ℝ)..t, g r
      rw [hd, add_sub_cancel_left, zero_add]
      have hcongr : EqOn (fun r => F t r (A r (U r 0 x)))
          (fun r => F t r (A r (U r 0 x - F r 0 x))) (uIcc 0 t) := by
        intro r hr
        rw [uIcc_of_le h1] at hr
        simp only
        rw [map_sub (A r), hkill r hr.1 (hr.2.trans h2'), sub_zero]
      rw [intervalIntegral.integral_congr hcongr, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.norm_integral_le_of_norm_le h1 (ae_of_all _ fun r hr => ?_)
        ((hg.const_mul _).intervalIntegrable _ _)
      calc ‖F t r (A r (U r 0 x - F r 0 x))‖ ≤ M * K * ‖U r 0 x - F r 0 x‖ :=
            UnforcedLeray.B0104.norm_apply_apply_le (hF r t hr.2 (by linarith [hr.1])) (hA r) _
        _ ≤ M * K * g r :=
            mul_le_mul_of_nonneg_left (hφ () r hr.1.le hr.2) (by positivity))
    () t ht0 (by linarith)
  have h0 : ‖U t 0 x - F t 0 x‖ ≤ 0 := by simpa using G
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end RelExteriorSub

end UnforcedLeray.Short.IIIa
