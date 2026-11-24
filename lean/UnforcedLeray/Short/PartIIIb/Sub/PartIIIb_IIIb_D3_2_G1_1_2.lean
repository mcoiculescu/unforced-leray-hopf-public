import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFactsBlocks
import UnforcedLeray.Short.PartIIIa.T06_ScalingJa
import UnforcedLeray.Short.PartIIIa.T08_ScalingJaInvDual
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.PhysFromMoving

/-!
# Decomposition of `PartIII-b:IIIb-D3/2/G1/1/2` (`retainedBlocksActual`)

Source of record: `the November 2 reference manuscript`:
* lines 4365-4396 (finite-band retained block estimates for `A_j = ampN` and `R = cmpN` on
  `0 ≤ t ≤ s ≤ H = 2/ν` with `c = ν⁻²`, `δ_c = C_Σ(c⁻² + P_ν e^{C_Σ/ν - b_Σ c²})`);
* lines 2894-2935 and 2975-3004 (`prop:short-full-clock`: periodized moving frame, damped complement
  stability, and amplitude equation in moving coordinates).

What is proved in this file:
1. **Residual simplification and Gaussian-tail absorption** (`deltaC_zero_eq_pow_four`,
   `deltaC_le_pow_four`): at `CS = 1, bS = 1, K = 0, p = 0`,
   `deltaC (0 * ν⁻¹ ^ 0) 1 1 ν (ν ^ (-2 : ℝ)) = ν ^ 4`, and for any `CS, bS > 0, K, p`, the general
   residual `deltaC (K * ν⁻¹ ^ p) CS bS ν (ν ^ (-2 : ℝ))` is bounded by `C₀ * ν ^ 4` for small `ν`.
2. **Finite-band clock and moving-coordinate bounds** (`movingZ_sub_bounds`,
   `clockTheta_inv_bounds`): on `0 ≤ t ≤ s ≤ 2/ν`, `(s - t) / 9 ≤ movingZ ν s - movingZ ν t ≤ s - t`
   and `ν ≤ (clockTheta ν s)⁻¹ ≤ 3 * ν` (`1 / (3 * ν) ≤ clockTheta ν s`).
3. **Moving-frame complement identification and norm equivalence on the finite band**
   (`xFn_Pc_actualPk_ae_eq_Jscale_compl`, `norm_Pc_actualPk_le_compl`, `compl_le_norm_Pc_actualPk`):
   on `0 ≤ s ≤ 2/ν`, `xFn (Pc (actualPk FI) s ((actualPk FI).Uev s t x))` equals
   `Jscale (clockA ν s) (compl F w s)` a.e. on `cell (cOf ν)`, so `‖Pc (actualPk FI) s ...‖` and
   `xNorm d_s m (compl F w s)` are uniformly equivalent with constants `3^{(m-3)/2}` and `3^{3/2}`.
4. **Decomposition into the two variation-of-constants integral inequalities**
   (`ActualComplIntegralBound`, `ActualAmpIntegralBound`, `actualBlockIntegralBounds_of`,
   `retainedBlocksActual_of_parts`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF FlatSettingInst

/-! ## 1. Residual simplification and Gaussian-tail absorption -/

/-- At `CS = 1, bS = 1, K = 0, p = 0`, the residual `deltaC` at `c = ν⁻²` is `ν^4 = c⁻²`. -/
theorem deltaC_zero_eq_pow_four {ν : ℝ} (hν : 0 < ν) :
    deltaC (0 * ν⁻¹ ^ (0 : ℕ)) 1 1 ν (ν ^ (-2 : ℝ)) = ν ^ 4 := by
  rw [ConcreteYF.deltaC_eq_explicit 0 1 1 0 ν hν]
  ring

/-- Any residual `deltaC (K * ν⁻¹ ^ p) CS bS ν (ν ^ (-2 : ℝ))` with `0 < bS` is bounded by
`C₀ * ν ^ 4` for small `ν > 0` (absorbing the super-exponential Gaussian tail into `c⁻² = ν^4`,
source 4370-4372, 3001-3004). -/
theorem deltaC_le_pow_four (CS bS K : ℝ) (p : ℕ) (hb : 0 < bS) :
    ∃ (C₀ ν₀ : ℝ), 0 < C₀ ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      deltaC (K * ν⁻¹ ^ p) CS bS ν (ν ^ (-2 : ℝ)) ≤ C₀ * ν ^ 4 := by
  have hdiv : 0 ≤ 2 * |CS| / bS := div_nonneg (by positivity) hb.le
  set M : ℝ := 1 + 2 * |CS| / bS
  have hM : 0 < M := by linarith
  set D : ℝ := (Nat.factorial (p + 4) : ℝ) / (bS / 2) ^ (p + 4)
  set C₀ : ℝ := |CS| * (1 + |K| * D) + 1
  have hC₀ : 0 < C₀ := by positivity
  refine ⟨C₀, M⁻¹, hC₀, inv_pos.mpr hM, fun ν hν hνle => ?_⟩
  have hu : 1 + 2 * |CS| / bS ≤ ν⁻¹ := by
    have := inv_anti₀ hν hνle
    rwa [inv_inv] at this
  rw [ConcreteYF.deltaC_eq_explicit K CS bS p ν hν]
  set u : ℝ := ν⁻¹
  have hkey := ConcreteYF.key_exp_bound CS bS hb (p + 2) u hu
  have hkey' : u ^ (p + 2) * Real.exp (CS * u - bS * u ^ 4) * u ^ 2 ≤ D := by
    rw [le_div_iff₀ (by positivity)]
    exact hkey
  have hu_pow : u ^ (p + 2) * Real.exp (CS * u - bS * u ^ 4) * u ^ 2 =
      (u ^ p * Real.exp (CS / ν - bS * u ^ 4)) * u ^ 4 := by
    have : CS / ν = CS * u := by rw [div_eq_mul_inv]
    rw [this]
    ring
  rw [hu_pow] at hkey'
  have huν4 : u ^ 4 * ν ^ 4 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hν.ne', one_pow]
  have htail : u ^ p * Real.exp (CS / ν - bS * u ^ 4) ≤ D * ν ^ 4 := by
    calc u ^ p * Real.exp (CS / ν - bS * u ^ 4)
        = (u ^ p * Real.exp (CS / ν - bS * u ^ 4) * u ^ 4) * ν ^ 4 := by
          rw [mul_assoc, huν4, mul_one]
      _ ≤ D * ν ^ 4 := mul_le_mul_of_nonneg_right hkey' (by positivity)
  have hKtail : K * u ^ p * Real.exp (CS / ν - bS * u ^ 4) ≤ |K| * D * ν ^ 4 := by
    calc K * u ^ p * Real.exp (CS / ν - bS * u ^ 4)
        ≤ |K| * (u ^ p * Real.exp (CS / ν - bS * u ^ 4)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ |K| * (D * ν ^ 4) := mul_le_mul_of_nonneg_left htail (abs_nonneg K)
      _ = |K| * D * ν ^ 4 := by ring
  have hsum : ν ^ 4 + K * u ^ p * Real.exp (CS / ν - bS * u ^ 4) ≤ (1 + |K| * D) * ν ^ 4 := by
    nlinarith
  have hsum_abs : |ν ^ 4 + K * u ^ p * Real.exp (CS / ν - bS * u ^ 4)| ≤ (1 + |K| * D) * ν ^ 4 := by
    have h1 := abs_add_le (ν ^ 4) (K * u ^ p * Real.exp (CS / ν - bS * u ^ 4))
    have hu_nonneg : 0 ≤ u ^ p * Real.exp (CS / ν - bS * u ^ 4) :=
      mul_nonneg (pow_nonneg (inv_nonneg.2 hν.le) _) (Real.exp_pos _).le
    have h2 : |K * u ^ p * Real.exp (CS / ν - bS * u ^ 4)| =
        |K| * (u ^ p * Real.exp (CS / ν - bS * u ^ 4)) := by
      rw [mul_assoc, abs_mul, abs_of_nonneg hu_nonneg]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ν ^ 4), h2] at h1
    nlinarith [mul_le_mul_of_nonneg_left htail (abs_nonneg K)]
  calc CS * (ν ^ 4 + K * u ^ p * Real.exp (CS / ν - bS * u ^ 4))
      ≤ |CS * (ν ^ 4 + K * u ^ p * Real.exp (CS / ν - bS * u ^ 4))| := le_abs_self _
    _ = |CS| * |ν ^ 4 + K * u ^ p * Real.exp (CS / ν - bS * u ^ 4)| := abs_mul _ _
    _ ≤ |CS| * ((1 + |K| * D) * ν ^ 4) :=
        mul_le_mul_of_nonneg_left hsum_abs (abs_nonneg CS)
    _ ≤ C₀ * ν ^ 4 := by
        have : 0 ≤ ν ^ 4 := by positivity
        nlinarith

/-! ## 2. Finite-band clock and moving-coordinate bounds (source 4375-4382) -/

/-- On the finite band `0 ≤ t ≤ s ≤ 2/ν`, `(s - t) / 9 ≤ movingZ ν s - movingZ ν t ≤ s - t`
(source 4380: `z(s) - z(t) ≥ (s - t) / (1 + Σ)²` with `Σ = 2`). -/
theorem movingZ_sub_bounds {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s)
    (hs : s ≤ 2 / ν) :
    (s - t) / 9 ≤ IIIa.movingZ ν s - IIIa.movingZ ν t ∧
      IIIa.movingZ ν s - IIIa.movingZ ν t ≤ s - t := by
  have hs0 : 0 ≤ s := ht.trans hts
  have hat1 : 1 ≤ IIIa.clockA ν t := by unfold IIIa.clockA; nlinarith
  have has1 : 1 ≤ IIIa.clockA ν s := by unfold IIIa.clockA; nlinarith
  have hat3 : IIIa.clockA ν t ≤ 3 := by
    unfold IIIa.clockA
    have : ν * t ≤ ν * (2 / ν) := mul_le_mul_of_nonneg_left (hts.trans hs) hν.le
    rw [mul_div_cancel₀ 2 hν.ne'] at this
    linarith
  have has3 : IIIa.clockA ν s ≤ 3 := by
    unfold IIIa.clockA
    have : ν * s ≤ ν * (2 / ν) := mul_le_mul_of_nonneg_left hs hν.le
    rw [mul_div_cancel₀ 2 hν.ne'] at this
    linarith
  have hat_pos : 0 < IIIa.clockA ν t := lt_of_lt_of_le one_pos hat1
  have has_pos : 0 < IIIa.clockA ν s := lt_of_lt_of_le one_pos has1
  have hprod1 : 1 ≤ IIIa.clockA ν s * IIIa.clockA ν t := one_le_mul_of_one_le_of_one_le has1 hat1
  have hprod9 : IIIa.clockA ν s * IIIa.clockA ν t ≤ 9 := by nlinarith
  have hprod_pos : 0 < IIIa.clockA ν s * IIIa.clockA ν t := mul_pos has_pos hat_pos
  have hdiff : IIIa.movingZ ν s - IIIa.movingZ ν t =
      (s - t) / (IIIa.clockA ν s * IIIa.clockA ν t) := by
    unfold IIIa.movingZ IIIa.clockA
    have h1 : 1 + ν * s ≠ 0 := has_pos.ne'
    have h2 : 1 + ν * t ≠ 0 := hat_pos.ne'
    field_simp
    ring
  rw [hdiff]
  have hst : 0 ≤ s - t := sub_nonneg.2 hts
  exact ⟨div_le_div_of_nonneg_left hst hprod_pos hprod9, div_le_self hst hprod1⟩

/-- On the finite band `0 ≤ s ≤ 2/ν`, `ν ≤ (clockTheta ν s)⁻¹ ≤ 3 * ν` and
`1 / (3 * ν) ≤ clockTheta ν s` (source 4376: `θ⁻¹ = ν a`, `1 ≤ a ≤ 3`). -/
theorem clockTheta_inv_bounds {ν s : ℝ} (hν : 0 < ν) (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    ν ≤ (IIIa.clockTheta ν s)⁻¹ ∧ (IIIa.clockTheta ν s)⁻¹ ≤ 3 * ν ∧
      1 / (3 * ν) ≤ IIIa.clockTheta ν s := by
  have ha1 : 1 ≤ IIIa.clockA ν s := by unfold IIIa.clockA; linarith [ mul_nonneg hν.le hs.1 ]
  have ha3 : IIIa.clockA ν s ≤ 3 := by
    unfold IIIa.clockA
    have : ν * s ≤ ν * (2 / ν) := mul_le_mul_of_nonneg_left hs.2 hν.le
    rw [mul_div_cancel₀ 2 hν.ne'] at this
    linarith
  unfold IIIa.clockTheta
  rw [inv_inv]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [one_div]
  exact inv_anti₀ (by positivity) (by nlinarith)

/-! ## 3. Moving-frame complement identification on the finite band `[0, 2/ν]` -/

/-- `J_a (J_a⁻¹ f) = f` for `a > 0`. -/
theorem jscale_jscaleInv {a : ℝ} (ha : 0 < a) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    IIIa.Jscale a (IIIa.JscaleInv a f) x = f x := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  simp only [IIIa.Jscale, IIIa.JscaleInv]
  rw [mul_div_cancel₀ _ hs, mul_div_cancel₀ _ hs, ← mul_assoc, ← Complex.ofReal_mul]
  have : a ^ (-2 : ℝ) * a ^ 2 = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, inv_mul_cancel₀ (by positivity)]
  rw [this, Complex.ofReal_one, one_mul]

/-- The weighted norm of the planar function of `w ∈ X_{m,c}` is `ENNReal.ofReal ‖w‖`. -/
private theorem xNorm_xFn_eq' {c m : ℝ} [Fact (1 < m)] (w : Xmc c m) :
    IIIa.xNorm c m (xFn w) = ENNReal.ofReal ‖w‖ := by
  have h1 : ‖w‖ = ‖(w : XAmb c m)‖ := (Submodule.coe_norm w).symm
  rw [h1, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top (w : XAmb c m)).ne]
  rfl

/-- On `0 ≤ s ≤ 2/ν`, the planar representative of `Pc (actualPk FI) s ((actualPk FI).Uev s t x)`
equals `Jscale (clockA ν s) (compl F w s)` almost everywhere on `cell (cOf ν)`. -/
theorem xFn_Pc_actualPk_ae_eq_Jscale_compl {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (t : ℝ) (x : Xmc (cOf ν) m)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    xFn (Pc (actualPk FI) s ((actualPk FI).Uev s t x))
      =ᵐ[volume.restrict (B0579.cell (cOf ν))]
      IIIa.Jscale (IIIa.clockA ν s)
        (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
          (fun r => xFn (FI.ev.U r t x)) s) := by
  set y : Xmc (cOf ν) m := (actualPk FI).Uev s t x
  set F := IIIa.periodizedFrame κ ν m b K hν hPF
  set w : ℝ → ℝ × ℝ → ℂ := fun r => xFn (FI.ev.U r t x)
  have ha0 : 0 < IIIa.clockA ν s := by unfold IIIa.clockA; linarith [mul_nonneg hν.le hs.1]
  have hPc : Pc (actualPk FI) s y =
      y - ((actualPk FI).ell true s y • FI.pair.q true s +
        (actualPk FI).ell false s y • FI.pair.q false s) := by
    simp [Pc]
    rfl
  have hell_t := ell_actualPk_eq_ampl hν hPF FI t x true hs
  have hell_f := ell_actualPk_eq_ampl hν hPF FI t x false hs
  have hq_t := FI.pair.q_pin true s
  have hq_f := FI.pair.q_pin false s
  have hsub := xFn_sub y ((actualPk FI).ell true s y • FI.pair.q true s +
    (actualPk FI).ell false s y • FI.pair.q false s)
  have hadd := xFn_add ((actualPk FI).ell true s y • FI.pair.q true s)
    ((actualPk FI).ell false s y • FI.pair.q false s)
  have hsm_t := xFn_smul ((actualPk FI).ell true s y) (FI.pair.q true s)
  have hsm_f := xFn_smul ((actualPk FI).ell false s y) (FI.pair.q false s)
  rw [hPc]
  filter_upwards [hsub, hadd, hsm_t, hsm_f, hq_t, hq_f] with p hp_sub hp_add hp_t hp_f hqt hqf
  rw [hp_sub, hp_add, hp_t, hp_f, hqt, hqf]
  change xFn y p -
      ((actualPk FI).ell true s ((actualPk FI).Uev s t x) * frozenQ κ ν (cOf ν) true s p +
        (actualPk FI).ell false s ((actualPk FI).Uev s t x) * frozenQ κ ν (cOf ν) false s p) =
    IIIa.Jscale (IIIa.clockA ν s) (IIIa.compl F w s) p
  rw [hell_t, hell_f]
  have hwy : xFn y p = IIIa.Jscale (IIIa.clockA ν s) (IIIa.movingW ν w s) p := by
    unfold IIIa.movingW
    exact (jscale_jscaleInv ha0 (w s) p).symm
  have hfq : ∀ j : Bool, frozenQ κ ν (cOf ν) j s p =
      IIIa.Jscale (IIIa.clockA ν s) (F.E s (pmIdx j)) p := by
    intro j
    unfold frozenQ
    rw [bandA_eq_clockA_of_mem_Icc hs, bandD_eq_cellLen_of_mem_Icc hs, cOf_eq_rpow hν]
    rfl
  rw [hwy, hfq true, hfq false]
  change IIIa.Jscale (IIIa.clockA ν s) (IIIa.movingW ν w s) p -
      (IIIa.ampl F w s 0 * IIIa.Jscale (IIIa.clockA ν s) (F.E s 0) p +
        IIIa.ampl F w s 1 * IIIa.Jscale (IIIa.clockA ν s) (F.E s 1) p) =
    IIIa.Jscale (IIIa.clockA ν s) (IIIa.compl F w s) p
  unfold IIIa.Jscale IIIa.compl
  rw [Fin.sum_univ_two]
  ring

/-- On `0 ≤ s ≤ 2/ν`, `JscaleInv (clockA ν s) (xFn (Pc (actualPk FI) s ((actualPk FI).Uev s t x)))`
equals `compl F w s` almost everywhere on `cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))`. -/
theorem jscaleInv_xFn_Pc_actualPk_ae_eq_compl {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (t : ℝ) (x : Xmc (cOf ν) m)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    IIIa.JscaleInv (IIIa.clockA ν s) (xFn (Pc (actualPk FI) s ((actualPk FI).Uev s t x)))
      =ᵐ[volume.restrict (B0579.cell (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s)))]
      IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
        (fun r => xFn (FI.ev.U r t x)) s := by
  have ha0 : 0 < IIIa.clockA ν s := by unfold IIIa.clockA; linarith [mul_nonneg hν.le hs.1]
  have hae := xFn_Pc_actualPk_ae_eq_Jscale_compl hν hPF FI t x hs
  have h1 := IIIa.jscale_ae_of_ae (cOf ν) (IIIa.clockA ν s) ha0 _ _ hae
  have hvol : volume.restrict (B0579.cell (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s))) =
      volume.restrict (B0579.cell (IIIa.cellLen (cOf ν) (IIIa.clockA ν s))) := by
    rw [cOf_eq_rpow hν]
  rw [hvol]
  filter_upwards [h1] with q hq
  rw [hq, Pair.jscaleInv_jscale ha0]

/-- **Upper bound on `‖Pc (actualPk FI) s ((actualPk FI).Uev s t x)‖` by the moving-frame
complement `compl`** on `0 ≤ s ≤ 2/ν` (source 4380-4381). -/
theorem norm_Pc_actualPk_le_compl {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ}
    [Fact (1 < m)] (hm : 8 < m) (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (t : ℝ) (x : Xmc (cOf ν) m)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    ENNReal.ofReal ‖Pc (actualPk FI) s ((actualPk FI).Uev s t x)‖ ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((m - 3) / 2)) *
        IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s)) m
          (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
            (fun r => xFn (FI.ev.U r t x)) s) := by
  have ha1 : 1 ≤ IIIa.clockA ν s := by unfold IIIa.clockA; linarith [mul_nonneg hν.le hs.1]
  have ha0 : 0 < IIIa.clockA ν s := lt_of_lt_of_le one_pos ha1
  have ha3 : IIIa.clockA ν s ≤ 3 := by
    unfold IIIa.clockA
    have : ν * s ≤ ν * (2 / ν) := mul_le_mul_of_nonneg_left hs.2 hν.le
    rw [mul_div_cancel₀ 2 hν.ne'] at this
    linarith
  have hc0 : 0 < cOf ν := cOf_pos hν
  have hd0 : 0 < IIIa.cellLen (cOf ν) (IIIa.clockA ν s) :=
    div_pos hc0 (Real.sqrt_pos.2 ha0)
  have hdc : IIIa.cellLen (cOf ν) (IIIa.clockA ν s) * Real.sqrt (IIIa.clockA ν s) = cOf ν :=
    div_mul_cancel₀ (cOf ν) (Real.sqrt_pos.2 ha0).ne'
  have h1 : ENNReal.ofReal ‖Pc (actualPk FI) s ((actualPk FI).Uev s t x)‖ =
      IIIa.xNorm (cOf ν) m (xFn (Pc (actualPk FI) s ((actualPk FI).Uev s t x))) :=
    (xNorm_xFn_eq' _).symm
  have h2 := IIIa.xNorm_scale_le
    (IIIa.scalingBounds_of_parts IIIa.scalingJa IIIa.scalingJaInv IIIa.scalingJaInvDual)
    (by linarith : 0 ≤ m) ha1 hd0 hdc
    (xFn_memLp (Pc (actualPk FI) s ((actualPk FI).Uev s t x)))
  have hlen : IIIa.cellLen (cOf ν) (IIIa.clockA ν s) =
      IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s) := by
    rw [cOf_eq_rpow hν]
  have h3 : IIIa.xNorm (IIIa.cellLen (cOf ν) (IIIa.clockA ν s)) m
        (IIIa.JscaleInv (IIIa.clockA ν s)
          (xFn (Pc (actualPk FI) s ((actualPk FI).Uev s t x)))) =
      IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s)) m
        (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
          (fun r => xFn (FI.ev.U r t x)) s) := by
    rw [hlen]
    exact eLpNorm_congr_ae
      (ae_cellMeasure_of_ae_cell (jscaleInv_xFn_Pc_actualPk_ae_eq_compl hν hPF FI t x hs))
  have hpow : IIIa.clockA ν s ^ ((m - 3) / 2) ≤ (3 : ℝ) ^ ((m - 3) / 2) :=
    Real.rpow_le_rpow ha0.le ha3 (by linarith)
  rw [h1]
  refine h2.trans ?_
  rw [h3]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpow) zero_le

/-- **Upper bound on the moving-frame complement `compl` by
`‖Pc (actualPk FI) s ((actualPk FI).Uev s t x)‖`** on `0 ≤ s ≤ 2/ν` (source 4380-4381). -/
theorem compl_le_norm_Pc_actualPk {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ}
    [Fact (1 < m)] (hm : 8 < m) (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (t : ℝ) (x : Xmc (cOf ν) m)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s)) m
        (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
          (fun r => xFn (FI.ev.U r t x)) s) ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2)) *
        ENNReal.ofReal ‖Pc (actualPk FI) s ((actualPk FI).Uev s t x)‖ := by
  have ha1 : 1 ≤ IIIa.clockA ν s := by unfold IIIa.clockA; linarith [mul_nonneg hν.le hs.1]
  have ha0 : 0 < IIIa.clockA ν s := lt_of_lt_of_le one_pos ha1
  have ha3 : IIIa.clockA ν s ≤ 3 := by
    unfold IIIa.clockA
    have : ν * s ≤ ν * (2 / ν) := mul_le_mul_of_nonneg_left hs.2 hν.le
    rw [mul_div_cancel₀ 2 hν.ne'] at this
    linarith
  have hlen : IIIa.cellLen (cOf ν) (IIIa.clockA ν s) =
      IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s) := by
    rw [cOf_eq_rpow hν]
  have h1 : IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s)) m
        (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
          (fun r => xFn (FI.ev.U r t x)) s) =
      IIIa.xNorm (IIIa.cellLen (cOf ν) (IIIa.clockA ν s)) m
        (IIIa.JscaleInv (IIIa.clockA ν s)
          (xFn (Pc (actualPk FI) s ((actualPk FI).Uev s t x)))) := by
    rw [hlen]
    exact (eLpNorm_congr_ae
      (ae_cellMeasure_of_ae_cell (jscaleInv_xFn_Pc_actualPk_ae_eq_compl hν hPF FI t x hs))).symm
  have h2 := IIIa.xNorm_JscaleInv_le (cOf ν) m (IIIa.clockA ν s) (by linarith : 0 ≤ m) ha1
    (xFn (Pc (actualPk FI) s ((actualPk FI).Uev s t x)))
    (xFn_memLp (Pc (actualPk FI) s ((actualPk FI).Uev s t x)))
  have hxEq : IIIa.xNorm (cOf ν) m (xFn (Pc (actualPk FI) s ((actualPk FI).Uev s t x))) =
      ENNReal.ofReal ‖Pc (actualPk FI) s ((actualPk FI).Uev s t x)‖ :=
    xNorm_xFn_eq' _
  rw [hxEq] at h2
  have hpow : IIIa.clockA ν s ^ ((3 : ℝ) / 2) ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow ha0.le ha3 (by norm_num)
  rw [h1]
  exact h2.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpow) zero_le)

/-! ## 4. The two variation-of-constants integral leaves and their assembly -/

/-- **(Leaf 1) Finite-band complementary integral inequality on `actualPk FI`** (source lines
4366-4394 and 2975-3004 `prop:short-full-clock`): on `0 ≤ t ≤ 1.1 / ν_n` and `t ≤ s ≤ 2 / ν_n`,
variation of constants for the normalised complement `cmpN` gives
`cmpN(s) ≤ C e^{-g(s-t)} cmpN(t) + C (ν_n + ν_n^4) ∫_t^s e^{-g(s-r)} (‖ampN true r‖ + ‖ampN false r‖) dr`.
Target of `PartIII-b:IIIb-D3/2/G1/1/2/1`, composed by `PartIII-b:IIIb-D3/2/G1/1/2`. -/
def ActualComplIntegralBound (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ∀ κ : IIIa.PlanarFrameKernels, SeedLink D κ →
    ∀ (m : ℝ) [Fact (1 < m)], 8 < m →
      ∃ (C g : ℝ) (N : ℕ), 0 < C ∧ 0 < g ∧
        ∀ n ≥ N, ∀ (FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n)),
          ∀ t ∈ Icc (0 : ℝ) (1.1 / nu D n), ∀ x : Xmc (cOf (nu D n)) m,
            ∀ s ∈ Icc t (2 / nu D n),
              cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x s ≤
                C * Real.exp (-g * (s - t)) *
                    cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x t +
                  C * (nu D n + (nu D n) ^ 4) * ∫ r in t..s, Real.exp (-g * (s - r)) *
                    (‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x true r‖ +
                      ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x false r‖)

/-- **(Leaf 2) Finite-band amplitude integral inequality on `actualPk FI`** (source lines
4366-4396 and 2991-3000 `prop:short-full-clock`): on `0 ≤ t ≤ 1.1 / ν_n` and `t ≤ s ≤ 2 / ν_n`,
the normalised amplitudes `ampN` satisfy
`‖ampN j s - ampN j t‖ ≤ ∫_t^s (C ν_n^4 (‖ampN true r‖ + ‖ampN false r‖) + C (ν_n + ν_n^4) cmpN r) dr`.
Target of `PartIII-b:IIIb-D3/2/G1/1/2/2`, composed by `PartIII-b:IIIb-D3/2/G1/1/2`. -/
def ActualAmpIntegralBound (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ∀ κ : IIIa.PlanarFrameKernels, SeedLink D κ →
    ∀ (m : ℝ) [Fact (1 < m)], 8 < m →
      ∃ (C : ℝ) (N : ℕ), 0 < C ∧
        ∀ n ≥ N, ∀ (FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n)),
          ∀ t ∈ Icc (0 : ℝ) (1.1 / nu D n), ∀ x : Xmc (cOf (nu D n)) m,
            ∀ j, ∀ s ∈ Icc t (2 / nu D n),
              ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x j s -
                  ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x j t‖ ≤
                ∫ r in t..s, (C * (nu D n) ^ 4 *
                    (‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x true r‖ +
                      ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x false r‖) +
                  C * (nu D n + (nu D n) ^ 4) *
                    cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x r)

/-- Pointwise nonnegativity of `cmpN`. -/
private theorem cmpN_nonneg (pk : YoungPkg) (lam κ : ℂ) (ν t : ℝ) (x : pk.X) (s : ℝ) :
    0 ≤ cmpN pk lam κ ν t x s := by
  unfold cmpN
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **Assembly of `ActualBlockIntegralBounds D`** from the complementary and amplitude integral
leaves (`ActualComplIntegralBound D` and `ActualAmpIntegralBound D`). -/
theorem actualBlockIntegralBounds_of (D : SeqData) (hCompl : ActualComplIntegralBound D)
    (hAmp : ActualAmpIntegralBound D) : ActualBlockIntegralBounds D := by
  intro dm dp hD κ hκ m hfact hm
  obtain ⟨C₁, g, N₁, hC₁, hg, hB₁⟩ := hCompl dm dp hD κ hκ m hm
  obtain ⟨C₂, N₂, hC₂, hB₂⟩ := hAmp dm dp hD κ hκ m hm
  set C : ℝ := max C₁ C₂
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  have hC₁_le : C₁ ≤ C := le_max_left _ _
  have hC₂_le : C₂ ≤ C := le_max_right _ _
  refine ⟨1, 1, 0, 0, C, g, max N₁ N₂, one_pos, zero_le_one, le_rfl, hC, hg, ?_⟩
  intro n hn FI
  dsimp only
  intro t ht x
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hδ : deltaC (0 * (nu D n)⁻¹ ^ (0 : ℕ)) 1 1 (nu D n) (nu D n ^ (-2 : ℝ)) = (nu D n) ^ 4 :=
    deltaC_zero_eq_pow_four hν
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hcont_amp : ∀ j, ContinuousOn
      (fun r => ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x j r‖)
      (Icc t (2 / nu D n)) := fun j =>
    (continuousOn_ampN_actualPk FI D.Pl.eigenvalue D.Pl.kappa hν ht.1 x j).norm
  have hcont_sum : ContinuousOn
      (fun r => ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x true r‖ +
        ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x false r‖)
      (Icc t (2 / nu D n)) :=
    (hcont_amp true).add (hcont_amp false)
  have hcont_cmp : ContinuousOn
      (cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x)
      (Icc t (2 / nu D n)) :=
    continuousOn_cmpN_actualPk FI D.Pl.eigenvalue D.Pl.kappa hν ht.1 x
  refine ⟨fun s hs => ?_, fun j s hs => ?_⟩
  · have h1 := hB₁ n hn₁ FI t ht x s hs
    have hint_nonneg : 0 ≤ ∫ r in t..s, Real.exp (-g * (s - r)) *
        (‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x true r‖ +
          ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x false r‖) := by
      refine intervalIntegral.integral_nonneg hs.1 fun r _ => ?_
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg (norm_nonneg _) (norm_nonneg _))
    have hcmp_t : 0 ≤ cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x t :=
      cmpN_nonneg _ _ _ _ _ _ _
    have hνδ : C₁ * (nu D n + (nu D n) ^ 4) ≤
        C * (nu D n + deltaC (0 * (nu D n)⁻¹ ^ (0 : ℕ)) 1 1 (nu D n) (nu D n ^ (-2 : ℝ))) := by
      rw [hδ]
      exact mul_le_mul_of_nonneg_right hC₁_le (by positivity)
    refine h1.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₁_le (Real.exp_pos _).le) hcmp_t
    · exact mul_le_mul_of_nonneg_right hνδ hint_nonneg
  · have h2 := hB₂ n hn₂ FI t ht x j s hs
    have hsub : Icc t s ⊆ Icc t (2 / nu D n) := Icc_subset_Icc_right hs.2
    have hcont_2 : ContinuousOn
        (fun r => C₂ * (nu D n) ^ 4 *
            (‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x true r‖ +
              ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x false r‖) +
          C₂ * (nu D n + (nu D n) ^ 4) *
            cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x r)
        (Icc t s) :=
      ((continuousOn_const.mul (hcont_sum.mono hsub)).add
        (continuousOn_const.mul (hcont_cmp.mono hsub)))
    have hcont_C : ContinuousOn
        (fun r => C * deltaC (0 * (nu D n)⁻¹ ^ (0 : ℕ)) 1 1 (nu D n) (nu D n ^ (-2 : ℝ)) *
            (‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x true r‖ +
              ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x false r‖) +
          C * (nu D n + deltaC (0 * (nu D n)⁻¹ ^ (0 : ℕ)) 1 1 (nu D n) (nu D n ^ (-2 : ℝ))) *
            cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x r)
        (Icc t s) :=
      ((continuousOn_const.mul (hcont_sum.mono hsub)).add
        (continuousOn_const.mul (hcont_cmp.mono hsub)))
    refine h2.trans (intervalIntegral.integral_mono_on hs.1
      (hcont_2.intervalIntegrable_of_Icc hs.1)
      (hcont_C.intervalIntegrable_of_Icc hs.1) fun r _ => ?_)
    have hA_nonneg : 0 ≤ ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x true r‖ +
        ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x false r‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hR_nonneg : 0 ≤ cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x r :=
      cmpN_nonneg _ _ _ _ _ _ _
    have hc1 : C₂ * (nu D n) ^ 4 ≤
        C * deltaC (0 * (nu D n)⁻¹ ^ (0 : ℕ)) 1 1 (nu D n) (nu D n ^ (-2 : ℝ)) := by
      rw [hδ]
      exact mul_le_mul_of_nonneg_right hC₂_le (by positivity)
    have hc2 : C₂ * (nu D n + (nu D n) ^ 4) ≤
        C * (nu D n + deltaC (0 * (nu D n)⁻¹ ^ (0 : ℕ)) 1 1 (nu D n) (nu D n ^ (-2 : ℝ))) := by
      rw [hδ]
      exact mul_le_mul_of_nonneg_right hC₂_le (by positivity)
    exact add_le_add
      (mul_le_mul_of_nonneg_right hc1 hA_nonneg)
      (mul_le_mul_of_nonneg_right hc2 hR_nonneg)

/-- **Reduction of `G1.RetainedBlocksActual D`** to the two variation-of-constants integral
leaves (`ActualComplIntegralBound D` and `ActualAmpIntegralBound D`). -/
theorem retainedBlocksActual_of_parts (D : SeqData) (hCompl : ActualComplIntegralBound D)
    (hAmp : ActualAmpIntegralBound D) : G1.RetainedBlocksActual D :=
  retainedBlocksActual_of D (actualBlockIntegralBounds_of D hCompl hAmp)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

end
