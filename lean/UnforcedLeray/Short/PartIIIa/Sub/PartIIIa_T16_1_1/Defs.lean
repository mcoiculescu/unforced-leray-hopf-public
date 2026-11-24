import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral

/-!
# `PartIII-a:T16/1/1` : `SepWDiffUnder` from six analytic leaves (and one generic lemma)

Source `the November 2 reference manuscript` lines 3597-3623 (`K_t`, `sep:kernel`,
`sep:resolvent`, the radial gap `|y - λz| ≥ |y'| - λ|z'| ≥ D`).

`sepW` is a nested Bochner integral over `λ ∈ (0,1)` and `z ∈ ℝ³`.  On the product measure
`ρ = (vol|_{(0,1)}) ⊗ vol` it is `∫ F(p, y) dρ(p)` with the explicit `Fin 3 → ℂ`-valued integrand
`sepDiffF` (`SepDiffWEqIntegral`, Fubini), as soon as `F(·, y)` is `ρ`-integrable.  Fix a receiver
`y` (`|y'| ≥ r_i`) at which the order-`0` majorant is finite, `D = r_i - r_o`, `U = B(y, D/2)`.
On the support `|z'| ≤ r_o` and for `y' ∈ U`: `|y - λz| ≥ D` and `|y - λz| ≤ 2|y' - λz|`, so by
`sep:kernel` (`SepDiffFDerivBound`) `|D^n_{y'}F(p,y')| ≤ C_n 2^{4+n}D^{-n} λ^{2Re μ+2}|y-λz|^{-4}|T|`;
off the support `F(p,·) = 0`.  The right side is `ρ`-integrable (`SepDiffMajIntegrable`), so the
family is locally dominated on `U` at every order and the generic lemma
`UnforcedLeray.L09.iteratedFDeriv_integral_eq` (smoothness `HeatLerayKSmoothAll`, measurability
`SepDiffFMeas`) differentiates `sepW` `j` times under the integral at `y`; the order-`j` kernel
bound at `y` itself gives the asserted majorant with `C0 = 3 C_j` (the factor `3` is the
`Fin 3`-component sum).  The composition `sepWDiffUnder_of` is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The product measure `(vol|_{(0,1)}) ⊗ vol` on `p = (λ, z) ∈ ℝ × Space`. -/
def sepDiffRho : Measure (ℝ × Space) := (volume.restrict (Ioo (0 : ℝ) 1)).prod volume

/-- The integrand of `sepW` (`sep:resolvent`, SP 3611-3617) at `p = (λ, z)` and receiver `y`,
including the factor `-2`: component `i` is
`-2 λ^{2μ+2} ∑_{j,k} ∂_kK_{ν(1-λ²),ij}(y - λz) T_{jk}(z, τ + 2 log λ)`. -/
def sepDiffF (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (p : ℝ × Space) (y : Space) : Fin 3 → ℂ :=
  fun i => -2 * ((p.1 : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
    ((fderiv ℝ (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y - p.1 • p.2)
      (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log p.1) p.2 j k : ℝ) : ℂ))

/-- The order-`0` majorant integrand `λ^{2Re μ+2}|y - λz|^{-4}|T(z, τ + 2 log λ)|` at `p = (λ, z)`. -/
def sepDiffMaj (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space)
    (p : ℝ × Space) : ℝ :=
  p.1 ^ (2 * μ.re + 2) * ‖y - p.1 • p.2‖ ^ (-4 : ℝ) * tensorNorm (T (τ + 2 * Real.log p.1) p.2)

/-! ## The six leaves -/

/-- **(L1) Smoothness of the heat-Leray kernel** (SP 3597-3603): for `t > 0`, `K_t` is `C^∞` on
`ℝ³` (`G_t` is a Gaussian; `∫_t^∞ G_a(x) da = Ψ(|x|²/4)` with
`Ψ(r) = ∫_t^∞ (4πa)^{-3/2}e^{-r/a} da` smooth in `r ∈ ℝ` by differentiation under the integral,
dominated by `C_k e^{R/t} a^{-3/2}` on `a ≥ t`, `|r| ≤ R`). -/
def HeatLerayKSmoothAll : Prop :=
  ∀ t : ℝ, 0 < t → ∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => heatLerayK t i j x)

/-- **(L2) Joint measurability of the kernel derivatives** (SP 3597-3610): for every order `m`,
`(t, x) ↦ D^m_xK_t(x)` (extended by `0` for `t ≤ 0`) is strongly measurable; on `t > 0`,
`K_t(x) = t^{-3/2}K_1(x/√t)` (parabolic scaling of `G_t` and of `∫_t^∞ G_a`), so
`D^m_xK_t(x) = t^{-3/2}(√t)^{-m}(D^mK_1)(x/√t)` is continuous in `(t, x)` on `t > 0`. -/
def HeatLerayKJointMeas : Prop :=
  ∀ (i j : Fin 3) (m : ℕ), StronglyMeasurable (fun q : ℝ × Space =>
    if 0 < q.1 then iteratedFDeriv ℝ m (fun x => heatLerayK q.1 i j x) q.2 else 0)

/-- **(L3) Measurability of the derivatives of the integrand** (SP 3611-3617): for `ν > 0` and a
separated source, each `p ↦ D^n_y F_i(p, y)` is `ρ`-a.e. strongly measurable (on `λ ∈ (0,1)` it
is a finite sum of measurable coefficients `-2λ^{2μ+2}T_{jk}(z, τ + 2 log λ)` times a fixed
continuous linear image of `D^{n+1}_xK_{ν(1-λ²),ij}(y - λz)`, measurable by (L2)). -/
def SepDiffFMeas : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 < ν →
    IsSepSource P rOut T → ∀ (τ : ℝ) (i : Fin 3) (n : ℕ) (y : Space),
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (fun y' => sepDiffF ν μ T τ p y' i) y)
        sepDiffRho

/-- **(L4a) Derivatives of a shifted directional derivative** (generic; used for (L4)): for a
`C^∞` function `f : ℝ³ → ℝ`, `|D^n_y ∂_vf(y - w)| ≤ |D^{n+1}f(y - w)| |v|` (as a `ℂ`-valued map;
`iteratedFDeriv_comp_sub`, `norm_iteratedFDeriv_fderiv`, composition with the continuous linear
maps `apply v` and `Complex.ofRealCLM` of norm `≤ ‖v‖`, `≤ 1`). -/
def FDerivApplyShiftBound : Prop :=
  ∀ f : Space → ℝ, ContDiff ℝ ∞ f → ∀ (n : ℕ) (v w y : Space),
    ‖iteratedFDeriv ℝ n (fun y' => ((fderiv ℝ f (y' - w) v : ℝ) : ℂ)) y‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f (y - w)‖ * ‖v‖

/-- **(L4) `sep:kernel` for the integrand** (SP 3604-3610): there is `C_n` with
`|D^n_y F_i((λ, z), y)| ≤ C_n λ^{2Re μ+2}|y - λz|^{-4-n}|T(z, τ + 2 log λ)|` whenever
`λ ∈ (0,1)`, `y ≠ λz` (`|D^n_y ∂_kK_t(y - λz)| ≤ |D^{n+1}K_t(y - λz)|`, the bound
`|D^{n+1}K_t(x)| ≤ C|x|^{-4-n}` of `SepKernelBounds` at `t = ν(1-λ²) > 0`,
`|λ^{2μ+2}| = λ^{2Re μ+2}`, `|T_{jk}| ≤ |T|`, nine terms, the factor `2`). -/
def SepDiffFDerivBound : Prop :=
  SepKernelBounds → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : ℝ) (μ : ℂ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ), 0 < ν → ∀ (l : ℝ) (z y : Space),
      l ∈ Ioo (0 : ℝ) 1 → y - l • z ≠ 0 → ∀ i : Fin 3,
        ‖iteratedFDeriv ℝ n (fun y' => sepDiffF ν μ T τ (l, z) y' i) y‖ ≤
          C * (l ^ (2 * μ.re + 2) * ‖y - l • z‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log l) z))

/-- **(L5) Fubini for `sep:resolvent`** (SP 3611-3617): if `F(·, y)` is `ρ`-integrable then the
nested integral `sepW` equals the product integral `∫ F(p, y) dρ(p)` (componentwise:
`MeasureTheory.eval_integral`, `integral_prod`, `integral_const_mul`). -/
def SepDiffWEqIntegral : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    Integrable (fun p => sepDiffF ν μ T τ p y) sepDiffRho →
      sepW ν μ T y τ = ∫ p, sepDiffF ν μ T τ p y ∂sepDiffRho

/-- **(L6) Integrability of the order-`0` majorant** (SP 3618-3623): at a receiver `|y'| ≥ r_i`
where the gap-truncated order-`0` majorant `sepDom (2Re μ+2) 0 D (srcNorm T) τ y` is finite,
`sepDiffMaj` is `ρ`-integrable (Tonelli `lintegral_prod`; on the support `|z'| ≤ r_o` the radial
gap `radial_gap` gives `|y - λz| ≥ D`, so the truncation `sepKd` is inactive; off the support
`T = 0`). -/
def SepDiffMajIntegrable : Prop :=
  ∀ (μ : ℂ) (rOut rIn P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 ≤ rOut → rOut < rIn →
    IsSepSource P rOut T → ∀ (τ : ℝ) (y : Space), rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
      sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y < ⊤ →
        Integrable (sepDiffMaj μ T τ y) sepDiffRho

/-! ## Proved helpers -/

theorem sepDiffRho_ae_mem : ∀ᵐ p ∂sepDiffRho, p.1 ∈ Ioo (0 : ℝ) 1 := by
  have h : sepDiffRho {p : ℝ × Space | p.1 ∉ Ioo (0 : ℝ) 1} = 0 := by
    have : {p : ℝ × Space | p.1 ∉ Ioo (0 : ℝ) 1} = (Ioo (0 : ℝ) 1)ᶜ ×ˢ (univ : Set Space) := by
      ext p; simp
    rw [this, sepDiffRho, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioo.compl]
    simp
  exact measure_eq_zero_iff_ae_notMem.mp h |> fun h' => by
    filter_upwards [h'] with p hp
    simpa using hp

theorem sepDiffF_contDiff (h1 : HeatLerayKSmoothAll) (ν : ℝ) (μ : ℂ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (hν : 0 < ν) (p : ℝ × Space)
    (hp : p.1 ∈ Ioo (0 : ℝ) 1) (i : Fin 3) : ContDiff ℝ ∞ (fun y => sepDiffF ν μ T τ p y i) := by
  have ht : 0 < ν * (1 - p.1 ^ 2) := by
    have := hp.1; have := hp.2
    exact mul_pos hν (by nlinarith)
  unfold sepDiffF
  refine contDiff_const.mul (contDiff_const.mul (ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_))
  refine ContDiff.mul ?_ contDiff_const
  have h1' : ContDiff ℝ ∞ (fderiv ℝ (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x)) :=
    (contDiff_infty_iff_fderiv.1 (h1 _ ht i j)).2
  have h3 : ContDiff ℝ ∞ (fun y : Space => y - p.1 • p.2) := contDiff_id.sub contDiff_const
  exact Complex.ofRealCLM.contDiff.comp ((h1'.comp h3).clm_apply contDiff_const)

/-- The `n`-th derivative of a `Fin 3 → ℂ`-valued map is the sum of the derivatives of its
components, placed in their slots. -/
theorem sepDiff_iteratedFDeriv_pi {n : ℕ} {f : Space → Fin 3 → ℂ} {y : Space}
    (hf : ∀ i, ContDiffAt ℝ n (fun y' => f y' i) y) :
    iteratedFDeriv ℝ n f y = ∑ i : Fin 3,
      (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun y' => f y' i) y) := by
  have hfun : f = fun y' => ∑ i : Fin 3,
      (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i) (f y' i) := by
    funext y' k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hfun]
  rw [iteratedFDeriv_fun_sum_apply
    (f := fun i y' => (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i) (f y' i))
    (u := Finset.univ) (fun i _ =>
    (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).contDiff.contDiffAt.comp y (hf i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).iteratedFDeriv_comp_left (hf i) le_rfl

/-- The order-`n` weight at a nearby receiver: if `D ≤ u ≤ 2w` then
`w^{-4-n} ≤ 2^{4+n} D^{-n} u^{-4}`. -/
theorem sepDiff_gapWeight (D u w : ℝ) (n : ℕ) (hD : 0 < D) (hu : D ≤ u) (huw : u ≤ 2 * w) :
    w ^ (-4 - (n : ℝ)) ≤ 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ)) * u ^ (-4 : ℝ) := by
  have hu0 : 0 < u := lt_of_lt_of_le hD hu
  have hw0 : 0 < u / 2 := by positivity
  have h1 : w ^ (-4 - (n : ℝ)) ≤ (u / 2) ^ (-4 - (n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hw0 (by linarith) (by have := n.cast_nonneg (α := ℝ); linarith)
  have h2 : (u / 2) ^ (-4 - (n : ℝ)) = 2 ^ (4 + (n : ℝ)) * (u ^ (-4 : ℝ) * u ^ (-(n : ℝ))) := by
    rw [Real.div_rpow hu0.le (by norm_num), ← Real.rpow_add hu0, div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num)]
    have e1 : (-4 : ℝ) + -(n : ℝ) = -4 - (n : ℝ) := by ring
    have e2 : -(-4 - (n : ℝ)) = 4 + (n : ℝ) := by ring
    rw [e1, e2, mul_comm]
  have h3 : u ^ (-(n : ℝ)) ≤ D ^ (-(n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hD hu (by have := n.cast_nonneg (α := ℝ); linarith)
  have h4 : 0 ≤ u ^ (-4 : ℝ) := Real.rpow_nonneg hu0.le _
  have h5 : 0 ≤ (2 : ℝ) ^ (4 + (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc w ^ (-4 - (n : ℝ)) ≤ 2 ^ (4 + (n : ℝ)) * (u ^ (-4 : ℝ) * u ^ (-(n : ℝ))) := h1.trans h2.le
    _ ≤ 2 ^ (4 + (n : ℝ)) * (u ^ (-4 : ℝ) * D ^ (-(n : ℝ))) := by gcongr
    _ = 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ)) * u ^ (-4 : ℝ) := by ring

theorem sepDiffF_eq_zero (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (p : ℝ × Space) (h : T (τ + 2 * Real.log p.1) p.2 = 0) : sepDiffF ν μ T τ p = 0 := by
  funext y i
  simp [sepDiffF, h]

/-! ## Composition -/

set_option maxHeartbeats 1000000 in
/-- **`SepWDiffUnder` from the six leaves** (L2 enters through L3). -/
theorem sepWDiffUnder_of (h1 : HeatLerayKSmoothAll) (h3 : SepDiffFMeas)
    (h4 : SepDiffFDerivBound) (h5 : SepDiffWEqIntegral) (h6 : SepDiffMajIntegrable) :
    SepWDiffUnder := by
  intro hK j
  choose C hC0 hC using h4 hK
  refine ⟨3 * C j, by linarith [hC0 j], ?_⟩
  intro ν hν μ hμ rOut rIn P hrO hrr hP T hT τ y hy hfin
  have hD : 0 < rIn - rOut := by linarith
  set D := rIn - rOut with hDdef
  set U : Set Space := Metric.ball y (D / 2) with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hyU : y ∈ U := Metric.mem_ball_self (by linarith)
  set F := sepDiffF ν μ T τ with hFdef
  have hsm : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → ∀ i, ContDiff ℝ ∞ (fun y' => F p y' i) :=
    fun p hp i => sepDiffF_contDiff h1 ν μ T τ hν p hp i
  have hsmAt : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ (y' : Space) (i : Fin 3),
      ContDiffAt ℝ n (fun y' => F p y' i) y' := fun n p hp y' i =>
    ((hsm p hp i).of_le (by exact_mod_cast le_top)).contDiffAt
  have hoff : ∀ p : ℝ × Space, rOut < Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) → F p = 0 :=
    fun p hp => sepDiffF_eq_zero ν μ T τ p (hT.support _ _ hp)
  -- the `Fin 3`-valued derivative bound off the singularity
  have hpi : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' : Space,
      y' - p.1 • p.2 ≠ 0 → ‖iteratedFDeriv ℝ n (F p) y'‖ ≤ 3 * C n *
        (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
          tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    intro n p hp y' hne
    rw [sepDiff_iteratedFDeriv_pi (fun i => hsmAt n p hp y' i)]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun y'' => F p y'' i) y')‖ ≤ C n *
          (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
      intro i
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      have h1i := ContinuousLinearMap.norm_single_le_one ℝ (E := fun _ : Fin 3 => ℂ) i
      have h2i := hC n ν μ T τ hν p.1 p.2 y' hp hne i
      calc ‖ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i‖ *
            ‖iteratedFDeriv ℝ n (fun y'' => F p y'' i) y'‖
          ≤ 1 * ‖iteratedFDeriv ℝ n (fun y'' => F p y'' i) y'‖ := by gcongr
        _ ≤ _ := by rw [one_mul]; exact h2i
    calc ∑ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun y'' => F p y'' i) y')‖
        ≤ ∑ _i : Fin 3, C n * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp [Finset.sum_const]; ring
  -- the gap on `U`
  have hgapU : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut →
      ∀ y' ∈ U, D ≤ ‖y - p.1 • p.2‖ ∧ ‖y - p.1 • p.2‖ ≤ 2 * ‖y' - p.1 • p.2‖ := by
    intro p hp hz y' hy'
    have hg := radial_gap y p.2 p.1 rOut rIn hp hz hy
    have hd : ‖y - y'‖ < D / 2 := by
      rw [← dist_eq_norm, dist_comm]; exact hy'
    have ht := norm_sub_le_norm_sub_add_norm_sub y y' (p.1 • p.2)
    exact ⟨hg, by linarith⟩
  -- local domination at every order
  have hdom : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' ∈ U,
      ‖iteratedFDeriv ℝ n (F p) y'‖ ≤
        (3 * C n * 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ))) * sepDiffMaj μ T τ y p := by
    intro n p hp y' hy'
    have hl0 : 0 ≤ p.1 ^ (2 * μ.re + 2) := Real.rpow_nonneg hp.1.le _
    have htn : 0 ≤ tensorNorm (T (τ + 2 * Real.log p.1) p.2) := Real.sqrt_nonneg _
    by_cases hz : Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut
    · obtain ⟨hg1, hg2⟩ := hgapU p hp hz y' hy'
      have hne : y' - p.1 • p.2 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hg2; linarith
      have hw := sepDiff_gapWeight D ‖y - p.1 • p.2‖ ‖y' - p.1 • p.2‖ n hD hg1 hg2
      refine (hpi n p hp y' hne).trans ?_
      unfold sepDiffMaj
      have hC3 : 0 ≤ 3 * C n := by linarith [hC0 n]
      calc 3 * C n * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ≤ 3 * C n * (p.1 ^ (2 * μ.re + 2) * (2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ)) *
              ‖y - p.1 • p.2‖ ^ (-4 : ℝ)) * tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
            gcongr
        _ = _ := by ring
    · push_neg at hz
      rw [hoff p hz]
      have h0 : iteratedFDeriv ℝ n (0 : Space → Fin 3 → ℂ) y' = 0 := by
        simpa using congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := Space) (F := Fin 3 → ℂ) (n := n)) y'
      rw [h0, norm_zero]
      have hTz : T (τ + 2 * Real.log p.1) p.2 = 0 := hT.support _ _ hz
      unfold sepDiffMaj
      rw [hTz]
      simp [tensorNorm]
  have hInt : Integrable (sepDiffMaj μ T τ y) sepDiffRho :=
    h6 μ rOut rIn P T hrO hrr hT τ y hy hfin
  have hLoc : L09.LocDominated sepDiffRho F U := by
    intro n x hx
    refine ⟨U, hU.mem_nhds hx,
      fun p => (3 * C n * 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ))) * sepDiffMaj μ T τ y p,
      hInt.const_mul _, ?_⟩
    filter_upwards [sepDiffRho_ae_mem] with p hp y' hy'
    exact hdom n p hp y' hy'
  have hsmooth : ∀ᵐ p ∂sepDiffRho, ContDiffOn ℝ ∞ (F p) U := by
    filter_upwards [sepDiffRho_ae_mem] with p hp
    exact (contDiff_pi.2 (hsm p hp)).contDiffOn
  have hmeas : ∀ (n : ℕ), ∀ x ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (F p) x) sepDiffRho := by
    intro n x _
    have hR : AEStronglyMeasurable (fun p => ∑ i : Fin 3,
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℂ
          (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
          (iteratedFDeriv ℝ n (fun y' => F p y' i) x)) sepDiffRho := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℂ
        (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i)).continuous
          |>.comp_aestronglyMeasurable (h3 ν μ P rOut T hν hT τ i n x)
    refine hR.congr ?_
    filter_upwards [sepDiffRho_ae_mem] with p hp
    rw [sepDiff_iteratedFDeriv_pi (fun i => hsmAt n p hp x i)]
    rfl
  have hFint : ∀ y' ∈ U, Integrable (fun p => F p y') sepDiffRho := by
    intro y' hy'
    have hm : AEStronglyMeasurable (fun p => F p y') sepDiffRho := by
      have := (continuousMultilinearCurryFin0 ℝ Space (Fin 3 → ℂ)).continuous
        |>.comp_aestronglyMeasurable (hmeas 0 y' hy')
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp
    refine Integrable.mono' (hInt.const_mul (3 * C 0 * 2 ^ (4 + ((0 : ℕ) : ℝ)) *
      D ^ (-((0 : ℕ) : ℝ)))) hm ?_
    filter_upwards [sepDiffRho_ae_mem] with p hp
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hdom 0 p hp y' hy'
  have hEq : (fun y' => sepW ν μ T y' τ) =ᶠ[𝓝 y] fun y' => ∫ p, F p y' ∂sepDiffRho := by
    filter_upwards [hU.mem_nhds hyU] with y' hy' using h5 ν μ T τ y' (hFint y' hy')
  have hderiv : iteratedFDeriv ℝ j (fun y' => sepW ν μ T y' τ) y =
      ∫ p, iteratedFDeriv ℝ j (F p) y ∂sepDiffRho := by
    rw [(hEq.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    exact L09.iteratedFDeriv_integral_eq hU hsmooth hmeas hLoc j hyU
  have hmB : AEMeasurable (fun p : ℝ × Space => ENNReal.ofReal (p.1 ^ (2 * μ.re + 2) *
      ‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) * tensorNorm (T (τ + 2 * Real.log p.1) p.2)))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
    refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
    have hφ : Measurable fun q : ℝ × Space => (τ + 2 * Real.log q.1, q.2) :=
      (measurable_const.add (measurable_const.mul
        (Real.measurable_log.comp measurable_fst))).prodMk measurable_snd
    have hTn : Measurable fun q : ℝ × Space => tensorNorm (T (τ + 2 * Real.log q.1) q.2) := by
      unfold tensorNorm
      refine Measurable.sqrt ?_
      refine Finset.measurable_sum _ fun i _ => ?_
      refine Finset.measurable_sum _ fun j _ => ?_
      exact ((hT.measurable i j).comp hφ).pow_const 2
    exact ((measurable_fst.pow_const _).mul
      ((measurable_const.sub (measurable_fst.smul measurable_snd)).norm.pow_const _)).mul hTn
  unfold wDerivNorm
  rw [hderiv]
  calc ‖∫ p, iteratedFDeriv ℝ j (F p) y ∂sepDiffRho‖ₑ
      ≤ ∫⁻ p, ‖iteratedFDeriv ℝ j (F p) y‖ₑ ∂sepDiffRho := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ p, ENNReal.ofReal (3 * C j) * ENNReal.ofReal (p.1 ^ (2 * μ.re + 2) *
          ‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) * tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ∂sepDiffRho := by
        refine lintegral_mono_ae ?_
        filter_upwards [sepDiffRho_ae_mem] with p hp
        rw [← ENNReal.ofReal_mul (by linarith [hC0 j]), ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        by_cases hz : Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut
        · have hg := radial_gap y p.2 p.1 rOut rIn hp hz hy
          have hne : y - p.1 • p.2 ≠ 0 := by
            intro h0; rw [h0, norm_zero] at hg; linarith
          exact hpi j p hp y hne
        · push_neg at hz
          have hTz : T (τ + 2 * Real.log p.1) p.2 = 0 := hT.support _ _ hz
          rw [hoff p hz, hTz]
          have h0 : iteratedFDeriv ℝ j (0 : Space → Fin 3 → ℂ) y = 0 := by
            simpa using congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := Space) (F := Fin 3 → ℂ)
              (n := j)) y
          rw [h0, norm_zero]
          simp [tensorNorm]
    _ = ENNReal.ofReal (3 * C j) * ∫⁻ p, ENNReal.ofReal (p.1 ^ (2 * μ.re + 2) *
          ‖y - p.1 • p.2‖ ^ (-4 - (j : ℝ)) * tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ∂sepDiffRho := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (3 * C j) * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
          ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 - (j : ℝ))) *
            srcNorm T (τ + 2 * Real.log l) z := by
        congr 1
        rw [show sepDiffRho = (volume.restrict (Ioo (0 : ℝ) 1)).prod volume from rfl,
          lintegral_prod _ hmB]
        refine setLIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
        simp only
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        unfold srcNorm
        rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hl.1.le _)
          (Real.rpow_nonneg (norm_nonneg _) _)),
          ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _), mul_assoc]

end UnforcedLeray.Short.IIIa

end
