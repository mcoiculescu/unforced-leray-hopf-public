import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_1.Window

/-!
# `PartIII-b:IIIb-D3/1`: clauses 2-4 of `FlatLimit` (source 4709-4730, 4821-4916)

Source of record: `the November 2 reference manuscript` (73 pages).

* clause 2, `‖a_μ‖_𝒜 ≤ C` (4807-4811, 4833): `AMuNorm.lean` (`affNorm` of `s^{5/2}/(μ+5/2) D₀`);
* clause 3, `‖Λ‖ ≤ C A_*` (4863-4864): `BmatSharp.lean` (pointwise conormal bound of `B` with the
  weight `e^{a_s t}`), `ZeroSharp.lean` (Laplace integral `Γ(μ+5/2)(γ-a_s)^{-μ-5/2}`),
  `Point.lean` (`lam_apply_le`); this is the only place where the budget `a_s < γ = Re λ` enters
  (the Laplace integrand is `t^{μ+3/2}e^{-(γ-a_s)t}`, source 4863-4864);
* clause 4, `Λ(a_μ) = unitResp + O(·)` (4709-4730): `bmat_aMuFun` (`B[a_μ] = B_μ`),
  `a0Unit_uniform` (`T_a0Unit` with constants uniform for `μ` in a compact window of `(0,1]`),
  `lamFun_sub_unitResp` (the algebra `-(3π/16)·(-(21/4)L) = 2·(63π/128)L`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `a₀(B[a_μ]) = a₀(B_μ)`: `aZero` only sees `B` on `s > 0`. -/
theorem aZero_bmat_aMuFun {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) (lam ell : ℂ) (ν μ : ℝ)
    (hμ : 0 < μ) :
    aZero lam ell (μ : ℂ) (Bmat ν μ χ (aMuFun μ)) =
      aZero lam ell (μ : ℂ) (Bmu χ (deriv χ) ν μ) := by
  unfold aZero
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [bmat_aMuFun hχ ν μ hμ ht]

/-- **Clauses 2-4 of `FlatLimit`** under the budget `a_s < γ` (source 4863-4864). -/
theorem flatLimitCoefPart_of_lt (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hlt : D.K.as < D.Pl.eigenvalue.re)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) : FlatLimitCoefPart D G := by
  have hγ : 0 < D.Pl.eigenvalue.re := hst.gamma_pos
  have has : 0 ≤ D.K.as := hst.as_pos.le
  have hσ0 := hst.sigma_pos
  have hσ1 := hst.sigma_lt
  set lo : ℝ := D.σ₀ / 2 with hlo
  set hi : ℝ := (D.σ₀ + 1 / 4) / 2 with hhi
  have hlo0 : 0 < lo := by rw [hlo]; linarith
  have hhi1 : hi ≤ 1 := by rw [hhi]; linarith
  have hlohi : lo ≤ hi := by rw [hlo, hhi]; linarith
  -- constants
  obtain ⟨C0, hC0, hsh⟩ := aZero_sharp (χ := D.K.χf) hst.chiF
  obtain ⟨Cj, hCj, hJ⟩ := mellinJ_bound (hi := hi) hst.planar hlo0
  obtain ⟨Cg, hCg, hG⟩ := gamFac_bound (r := D.Pl.eigenvalue.re - D.K.as) (by linarith)
    (hi := hi) hlo0
  have hd : ∀ x, HasDerivAt D.K.χf (deriv D.K.χf x) x := fun x =>
    ((hst.chiF.smooth.differentiable (by simp)) x).hasDerivAt
  have hdc : Continuous (deriv D.K.χf) :=
    (contDiff_infty_iff_deriv.1 hst.chiF.smooth).2.continuous
  obtain ⟨C4a, hC4a⟩ := a0Unit_uniform (lam := D.Pl.eigenvalue) (ell := D.Pl.strainCoupling)
    hγ hd hdc hst.chiF.one (fun x hx => hst.chiF.zero x (by linarith [hx])) hlo0 hlohi hhi1
  set C2 : ℝ := (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
    (frob (fun i j => Dzero i j) / (5 / 2)) with hC2
  have hC20 : 0 ≤ C2 := by
    rw [hC2]
    exact mul_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg (by norm_num) _)
      (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
  set C3 : ℝ := (3 * Real.pi / 16) * Cj * (‖D.Pl.strainCoupling‖ * (C0 * Cg)) with hC3
  have hC30 : 0 ≤ C3 := by rw [hC3]; positivity
  set C4 : ℝ := (3 * Real.pi / 16) * Cj * max C4a 0 with hC4
  have hC40 : 0 ≤ C4 := by rw [hC4]; positivity
  -- eventual facts
  have E1 := hst.near
  have E2 := hst.pins
  have E3 := mu_eventually_mem D hst.omega_ne hσ0 hσ1
  have E4 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds one_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (E1.and (E2.and (E3.and E4)))
  refine ⟨1 + C2 + C3 + C4, D.Pl.eigenvalue.re / 2, N, 0, by positivity, by positivity, ?_⟩
  intro k _ n hn z hz
  obtain ⟨hnear, hpins, hmu, hν1⟩ := hN n hn
  have hnear := hnear z hz
  have hpins := hpins z hz
  have hmu := hmu z hz
  set ν := retNu D.Pl D.σ₀ n with hνdef
  have hν : 0 < ν := retNu_pos _ _ _
  set μ := D.mu n z with hμdef
  have hμ0 : 0 < μ := by linarith [hmu.1]
  have hμlo : lo ≤ μ := hmu.1
  have hμhi : μ ≤ hi := hmu.2
  have hμw : μ ∈ Icc lo hi := ⟨hμlo, hμhi⟩
  -- the amplitude
  set Ast : ℝ := Astar D.Pl.eigenvalue D.Pl.kappa (mellinC D.Pl.eigenvalue D.Pl.strainCoupling
    (planarJ D.Pl) (D.σ₀ : ℂ)) D.σ₀ ν z with hAst
  have hAst0 : 0 ≤ Ast := by
    rw [hAst]; unfold Astar epsCube
    have : 0 ≤ ν ^ (5 + 2 * muWin D.σ₀ ν z) := Real.rpow_nonneg hν.le _
    have h2 : 0 ≤ ν ^ (D.Pl.kappa.re - 5 - 2 * D.σ₀) := Real.rpow_nonneg hν.le _
    positivity
  have hAeq : retEps D.Pl D.σ₀ n ^ 3 * ν ^ (5 + 2 * μ) * ‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ =
      Ast := by
    have hμm : μ = muWin D.σ₀ ν z := rfl
    rw [hAst, retEps_cube_eq, ← hνdef, hμm]
    unfold Astar
    ring
  have hν1' : 1 ≤ ν⁻¹ ^ k := one_le_pow₀ (by rw [one_le_inv₀ hν]; exact hν1.le)
  have hmain : ∀ x : ℝ, 0 ≤ x → ∀ c : ℝ, 0 ≤ c → c ≤ 1 + C2 + C3 + C4 → c * x ≤ (1 + C2 + C3 + C4) * x :=
    fun x hx c _ hc => mul_le_mul_of_nonneg_right hc hx
  refine ⟨?_, ?_, ?_⟩
  · -- clause 2
    show ‖(concreteOps D.Pl D.K (D.level n) (D.mu n z)).aMu‖ ≤ _
    rw [concreteOps_aMu _ _ _ _ hnear]
    refine (norm_aMuOp_le D.K has hμ0).trans ?_
    linarith [hC20, hC30, hC40]
  · -- clause 3
    show ‖(concreteOps D.Pl D.K (D.level n) (D.mu n z)).Lam‖ ≤ _
    have hbound : ‖(concreteOps D.Pl D.K (D.level n) (D.mu n z)).Lam‖ ≤ C3 * Ast := by
      refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC30 hAst0) fun A => ?_
      rw [Real.norm_eq_abs]
      refine (lam_apply_le hnear hpins (C0 := C0) hsh hlt hμ0.le A).trans ?_
      have hJμ := hJ μ hμw
      have hGμ := hG μ hμw
      have hlev : (D.level n).ε ^ 3 * (D.level n).ν ^ (5 + 2 * μ) *
          ‖Nnu D.Pl.eigenvalue D.Pl.kappa (D.level n).ν‖ = Ast := hAeq
      rw [hlev]
      have hnA := norm_nonneg A
      have hq : (1 + μ) * C0 * gamFac μ (D.Pl.eigenvalue.re - D.K.as) ≤ C0 * Cg := by
        calc (1 + μ) * C0 * gamFac μ (D.Pl.eigenvalue.re - D.K.as)
            = C0 * ((1 + μ) * gamFac μ (D.Pl.eigenvalue.re - D.K.as)) := by ring
          _ ≤ C0 * Cg := mul_le_mul_of_nonneg_left hGμ hC0
      have hq0 : 0 ≤ (1 + μ) * C0 * gamFac μ (D.Pl.eigenvalue.re - D.K.as) := by
        have : 0 ≤ gamFac μ (D.Pl.eigenvalue.re - D.K.as) := by
          unfold gamFac
          exact mul_nonneg (Real.rpow_nonneg (by
            have : 0 < D.Pl.eigenvalue.re - D.K.as := by linarith
            positivity) _) (Real.Gamma_pos_of_pos (by linarith)).le
        positivity
      calc (3 * Real.pi / 16) * Ast * ‖D.Pl.mellinJ μ‖ *
            (‖D.Pl.strainCoupling‖ * ((1 + μ) * C0 * gamFac μ (D.Pl.eigenvalue.re - D.K.as))) *
              ‖A‖
          ≤ (3 * Real.pi / 16) * Ast * Cj * (‖D.Pl.strainCoupling‖ * (C0 * Cg)) * ‖A‖ := by
            gcongr
        _ = C3 * Ast * ‖A‖ := by rw [hC3]; ring
    calc ‖(concreteOps D.Pl D.K (D.level n) (D.mu n z)).Lam‖ ≤ C3 * Ast := hbound
      _ ≤ (1 + C2 + C3 + C4) * Ast :=
        mul_le_mul_of_nonneg_right (by linarith) hAst0
  · -- clause 4
    have hE := hC4a μ hμlo hμhi ν hν hν1.le
    have hEn : ‖aZero D.Pl.eigenvalue D.Pl.strainCoupling (μ : ℂ) (Bmu D.K.χf (deriv D.K.χf) ν μ) +
        (21 / 4 : ℂ) * LCoeff D.Pl.eigenvalue D.Pl.strainCoupling (μ : ℂ)‖ ≤
        max C4a 0 * Real.exp (-(D.Pl.eigenvalue.re / 2) / ν) :=
      hE.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hL : (concreteOps D.Pl D.K (D.level n) (D.mu n z)).Lam
        (concreteOps D.Pl D.K (D.level n) (D.mu n z)).aMu =
        -(3 * Real.pi / 16) * retEps D.Pl D.σ₀ n ^ 3 * ν ^ (5 + 2 * μ) *
          (Complex.I * Nnu D.Pl.eigenvalue D.Pl.kappa ν * planarJ D.Pl (μ : ℂ) *
            aZero D.Pl.eigenvalue D.Pl.strainCoupling (μ : ℂ)
              (Bmu D.K.χf (deriv D.K.χf) ν μ)).re := by
      rw [concreteOps_aMu _ _ _ _ hnear, lam_apply_eq hnear hpins, affIota_aMuOp has hμ0]
      unfold LamFun
      show -(3 * Real.pi / 16) * retEps D.Pl D.σ₀ n ^ 3 * ν ^ (5 + 2 * μ) *
          (Complex.I * Nnu D.Pl.eigenvalue D.Pl.kappa ν * planarJ D.Pl (μ : ℂ) *
            aZero D.Pl.eigenvalue D.Pl.strainCoupling (μ : ℂ)
              (Bmat ν μ D.K.χf (aMuFun μ))).re = _
      rw [aZero_bmat_aMuFun hst.chiF _ _ ν μ hμ0]
    have e := lamFun_sub_unitResp D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling (planarJ D.Pl)
      (retEps D.Pl D.σ₀ n) ν μ (aZero D.Pl.eigenvalue D.Pl.strainCoupling (μ : ℂ)
        (Bmu D.K.χf (deriv D.K.χf) ν μ))
    have hEps : epsCube D.Pl.eigenvalue.re D.Pl.kappa D.σ₀
        (mellinC D.Pl.eigenvalue D.Pl.strainCoupling (planarJ D.Pl) (D.σ₀ : ℂ)) ν =
        retEps D.Pl D.σ₀ n ^ 3 := (retEps_cube_eq D n).symm
    have key : |(concreteOps D.Pl D.K (D.level n) (D.mu n z)).Lam
        (concreteOps D.Pl D.K (D.level n) (D.mu n z)).aMu -
        unitResp D.Pl.eigenvalue D.Pl.kappa (mellinC D.Pl.eigenvalue D.Pl.strainCoupling
          (planarJ D.Pl)) (epsCube D.Pl.eigenvalue.re D.Pl.kappa D.σ₀
            (mellinC D.Pl.eigenvalue D.Pl.strainCoupling (planarJ D.Pl) (D.σ₀ : ℂ)) ν) ν μ| ≤
        C4 * Ast * Real.exp (-(D.Pl.eigenvalue.re / 2) / ν) := by
      rw [hL, hEps, e]
      have hk : 0 ≤ (3 * Real.pi / 16) * retEps D.Pl D.σ₀ n ^ 3 * ν ^ (5 + 2 * μ) := by
        have := Real.rpow_nonneg hν.le (5 + 2 * μ)
        have := (retEps_pos D.coeff_ne n).le
        positivity
      rw [abs_mul, show -(3 * Real.pi / 16) * retEps D.Pl D.σ₀ n ^ 3 * ν ^ (5 + 2 * μ) =
        -((3 * Real.pi / 16) * retEps D.Pl D.σ₀ n ^ 3 * ν ^ (5 + 2 * μ)) by ring, abs_neg,
        abs_of_nonneg hk]
      have hre := Complex.abs_re_le_norm (Complex.I * Nnu D.Pl.eigenvalue D.Pl.kappa ν *
        planarJ D.Pl (μ : ℂ) * (aZero D.Pl.eigenvalue D.Pl.strainCoupling (μ : ℂ)
          (Bmu D.K.χf (deriv D.K.χf) ν μ) + (21 / 4 : ℂ) *
            LCoeff D.Pl.eigenvalue D.Pl.strainCoupling (μ : ℂ)))
      have hJμ : ‖planarJ D.Pl (μ : ℂ)‖ ≤ Cj := hJ μ hμw
      have hnorm : ‖Complex.I * Nnu D.Pl.eigenvalue D.Pl.kappa ν * planarJ D.Pl (μ : ℂ) *
          (aZero D.Pl.eigenvalue D.Pl.strainCoupling (μ : ℂ)
            (Bmu D.K.χf (deriv D.K.χf) ν μ) + (21 / 4 : ℂ) *
              LCoeff D.Pl.eigenvalue D.Pl.strainCoupling (μ : ℂ))‖ ≤
          ‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ * Cj *
            (max C4a 0 * Real.exp (-(D.Pl.eigenvalue.re / 2) / ν)) := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul]
        gcongr
      have hfin := mul_le_mul_of_nonneg_left (hre.trans hnorm) hk
      refine hfin.trans (le_of_eq ?_)
      rw [hC4, ← hAeq]
      ring
    have hkey : C4 * Ast * Real.exp (-(D.Pl.eigenvalue.re / 2) / ν) ≤
        (1 + C2 + C3 + C4) * Ast * ν⁻¹ ^ k * Real.exp (-(D.Pl.eigenvalue.re / 2) / ν) := by
      have he := (Real.exp_pos (-(D.Pl.eigenvalue.re / 2) / ν)).le
      have h1 : C4 * Ast ≤ (1 + C2 + C3 + C4) * Ast * ν⁻¹ ^ k := by
        have : (1 + C2 + C3 + C4) * Ast ≤ (1 + C2 + C3 + C4) * Ast * ν⁻¹ ^ k :=
          le_mul_of_one_le_right (mul_nonneg (by linarith) hAst0) hν1'
        exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hAst0) this
      exact mul_le_mul_of_nonneg_right h1 he
    exact key.trans hkey

/-- **Flat-limit coefficient clauses 2-4** (source 4709-4730, 4821-4916): the budget `a_s < γ` is
automatic under `RepairStanding`. -/
theorem flatLimitCoefPart_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) : FlatLimitCoefPart D G :=
  flatLimitCoefPart_of_lt D hst hst.as_lt_gamma G

end UnforcedLeray.Short.PartIIIb.Concrete
