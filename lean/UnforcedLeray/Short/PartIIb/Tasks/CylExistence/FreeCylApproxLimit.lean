import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T23
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy

/-!
# Part II-b, task `PartII-b:T23/2`: `FreeCylApproxLimit`

Source of record: `the November 2 reference manuscript`, lines 2105-2118.
Passage to the limit in `X_{m,c} = L²(B0579.cellMeasure c m)` from smooth cylinder test approximants
`fn n → f` and their regular cylinder flows `ωn n`, using the `X_{m,c}` energy bound for differences
of regular flows (`t22_dissipation` + `cyl_gronwall_of_rate` on `ωn n - ωn k`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

private theorem pd_sub_eq {f g : B0579.Plane → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j (fun y => f y - g y) x = B0579.pd j f x - B0579.pd j g x := by
  have h := congrFun
    (mp_pd_sub (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)) 0 j) x
  simpa only [sub_zero] using h

private theorem lapP_sub_eq {f g : B0579.Plane → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : B0579.Plane) :
    lapP (fun y => f y - g y) x = lapP f x - lapP g x := by
  have h := mp_lapP_sub hf hg 0 x
  simpa only [sub_zero] using h

/-- The difference of two `CylSmoothDecay` functions is in `CylSmoothDecay`. -/
private theorem cylSmoothDecay_sub {c : ℝ} {g₁ g₂ : B0579.Plane → ℝ}
    (h₁ : CylSmoothDecay c g₁) (h₂ : CylSmoothDecay c g₂) :
    CylSmoothDecay c (fun x => g₁ x - g₂ x) where
  smooth := h₁.smooth.sub h₂.smooth
  periodic x := by simp only [h₁.periodic x, h₂.periodic x]
  decay N := by
    obtain ⟨C₁, hC₁⟩ := h₁.decay N
    obtain ⟨C₂, hC₂⟩ := h₂.decay N
    refine ⟨C₁ + C₂, fun x => ?_⟩
    rw [pd_sub_eq h₁.smooth h₂.smooth 0 x, pd_sub_eq h₁.smooth h₂.smooth 1 x,
      lapP_sub_eq h₁.smooth h₂.smooth x]
    have hw : 0 ≤ (1 + x.2 ^ 2) ^ N := Real.rpow_nonneg (by positivity) N
    have a0 : |g₁ x - g₂ x| ≤ |g₁ x| + |g₂ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (g₁ x) (-g₂ x)
    have a1 : |B0579.pd 0 g₁ x - B0579.pd 0 g₂ x| ≤ |B0579.pd 0 g₁ x| + |B0579.pd 0 g₂ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (B0579.pd 0 g₁ x) (-B0579.pd 0 g₂ x)
    have a2 : |B0579.pd 1 g₁ x - B0579.pd 1 g₂ x| ≤ |B0579.pd 1 g₁ x| + |B0579.pd 1 g₂ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (B0579.pd 1 g₁ x) (-B0579.pd 1 g₂ x)
    have a3 : |lapP g₁ x - lapP g₂ x| ≤ |lapP g₁ x| + |lapP g₂ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (lapP g₁ x) (-lapP g₂ x)
    have hle := mul_le_mul_of_nonneg_right (by linarith :
      |g₁ x - g₂ x| + |B0579.pd 0 g₁ x - B0579.pd 0 g₂ x| +
        |B0579.pd 1 g₁ x - B0579.pd 1 g₂ x| + |lapP g₁ x - lapP g₂ x| ≤
      (|g₁ x| + |B0579.pd 0 g₁ x| + |B0579.pd 1 g₁ x| + |lapP g₁ x|) +
        (|g₂ x| + |B0579.pd 0 g₂ x| + |B0579.pd 1 g₂ x| + |lapP g₂ x|)) hw
    linarith [hC₁ x, hC₂ x]

/-- The difference of two regular cylinder flows on `[s, T]` is a regular cylinder flow. -/
private theorem isRegularCylFlow_sub {c ν s T : ℝ}
    {v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec}
    {u₁ u₂ : ℝ → B0579.Plane → ℝ}
    (hu₁ : IsRegularCylFlow c ν v s T u₁)
    (hu₂ : IsRegularCylFlow c ν v s T u₂) :
    IsRegularCylFlow c ν v s T (fun r x => u₁ r x - u₂ r x) where
  jointCont := hu₁.jointCont.sub hu₂.jointCont
  slice σ hσ := cylSmoothDecay_sub (hu₁.slice σ hσ) (hu₂.slice σ hσ)
  decay N := by
    obtain ⟨C₁, hC₁⟩ := hu₁.decay N
    obtain ⟨C₂, hC₂⟩ := hu₂.decay N
    refine ⟨C₁ + C₂, fun σ hσ x => ?_⟩
    have s1 := (hu₁.slice σ hσ).smooth
    have s2 := (hu₂.slice σ hσ).smooth
    rw [pd_sub_eq s1 s2 0 x, pd_sub_eq s1 s2 1 x, lapP_sub_eq s1 s2 x]
    have hw : 0 ≤ (1 + x.2 ^ 2) ^ N := Real.rpow_nonneg (by positivity) N
    have a0 : |u₁ σ x - u₂ σ x| ≤ |u₁ σ x| + |u₂ σ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (u₁ σ x) (-u₂ σ x)
    have a1 : |B0579.pd 0 (u₁ σ) x - B0579.pd 0 (u₂ σ) x| ≤
        |B0579.pd 0 (u₁ σ) x| + |B0579.pd 0 (u₂ σ) x| := by
      simpa [sub_eq_add_neg] using abs_add_le (B0579.pd 0 (u₁ σ) x) (-B0579.pd 0 (u₂ σ) x)
    have a2 : |B0579.pd 1 (u₁ σ) x - B0579.pd 1 (u₂ σ) x| ≤
        |B0579.pd 1 (u₁ σ) x| + |B0579.pd 1 (u₂ σ) x| := by
      simpa [sub_eq_add_neg] using abs_add_le (B0579.pd 1 (u₁ σ) x) (-B0579.pd 1 (u₂ σ) x)
    have a3 : |lapP (u₁ σ) x - lapP (u₂ σ) x| ≤ |lapP (u₁ σ) x| + |lapP (u₂ σ) x| := by
      simpa [sub_eq_add_neg] using abs_add_le (lapP (u₁ σ) x) (-lapP (u₂ σ) x)
    have hle := mul_le_mul_of_nonneg_right (by linarith :
      |u₁ σ x - u₂ σ x| + |B0579.pd 0 (u₁ σ) x - B0579.pd 0 (u₂ σ) x| +
        |B0579.pd 1 (u₁ σ) x - B0579.pd 1 (u₂ σ) x| + |lapP (u₁ σ) x - lapP (u₂ σ) x| ≤
      (|u₁ σ x| + |B0579.pd 0 (u₁ σ) x| + |B0579.pd 1 (u₁ σ) x| + |lapP (u₁ σ) x|) +
        (|u₂ σ x| + |B0579.pd 0 (u₂ σ) x| + |B0579.pd 1 (u₂ σ) x| + |lapP (u₂ σ) x|)) hw
    linarith [hC₁ σ hσ x, hC₂ σ hσ x]
  pde σ hσ x := by
    have s1 := (hu₁.slice σ hσ).smooth
    have s2 := (hu₂.slice σ hσ).smooth
    refine ((hu₁.pde σ hσ x).sub (hu₂.pde σ hσ x)).congr_deriv ?_
    rw [pd_sub_eq s1 s2 0 x, pd_sub_eq s1 s2 1 x, lapP_sub_eq s1 s2 x]
    ring

/-- Uniform `X_{m,c}` Gronwall bound on `[s, T]` for any regular cylinder flow of a BUC train. -/
private theorem regular_energy_bound_of_buc {m ν c s T : ℝ} (hm : 0 < m) (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hs : 0 ≤ s) (hsT : s ≤ T) :
    ∃ C_T : ℝ, 0 < C_T ∧ ∀ (u : ℝ → B0579.Plane → ℝ),
      IsRegularCylFlow c ν tr.v s T u →
      ∀ t ∈ Icc s T,
        eLpNorm (u t) 2 (B0579.cellMeasure c m) ≤
          ENNReal.ofReal C_T * eLpNorm (u s) 2 (B0579.cellMeasure c m) := by
  obtain ⟨Cd, hCd⟩ := cylDiffusionBound m hm
  obtain ⟨V, hV0, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu (le_trans hs hsT)
  set K : ℝ := (|Cd| + 1) * ν + m * V with hK_def
  have hK_pos : 0 < K := by positivity
  refine ⟨Real.exp (K * (T - s)), Real.exp_pos _, fun u hu t ht => ?_⟩
  have hM : ∀ σ ∈ Icc s T, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ 2 * V := by
    intro σ hσ x
    have hσ0 : σ ∈ Icc 0 T := ⟨le_trans hs hσ.1, hσ.2⟩
    linarith [(hV σ hσ0 x 0).1, (hV σ hσ0 x 1).1]
  obtain ⟨hcont, hderiv⟩ := regularEnergyDeriv c ν m s T tr.v u hc hu ⟨2 * V, hM⟩
  have hdiss : ∀ τ ∈ Ico s T,
      2 * ∫ x in B0579.cell c, u τ x * (ν * lapP (u τ) x -
          (tr.v τ x 0 * B0579.pd 0 (u τ) x + tr.v τ x 1 * B0579.pd 1 (u τ) x)) *
            (B0579.density m x : ℝ)
        ≤ 2 * K * cylEnergy c m (u τ) := by
    intro τ hτ
    have hτI : τ ∈ Icc s T := ⟨hτ.1, hτ.2.le⟩
    have hsd := hu.slice τ hτI
    obtain ⟨hE, hI1, hD⟩ := hCd c hc (u τ) hsd
    obtain ⟨hT1, hT2, hT⟩ := cylTransportIBP ν c tr τ (le_trans hs hτ.1) hc
      ⟨2 * V, hM τ hτI⟩ m (u τ) hsd
    have key := t22_dissipation (c := c) (m := m) (Cd := Cd) (U := 2 * V)
      hν hm.le (tr.v τ) (fun _ => (0, 0)) (fun _ => by simp)
      (fun x _ => by simpa using hM τ hτI x) (u τ) hE hI1 hD hT1 hT2 hT
    have hEnn := t22_energy_nonneg c m (u τ)
    have hK_le : Cd * ν + m * (2 * V) ≤ 2 * K := by
      dsimp [K]
      nlinarith [le_abs_self Cd, abs_nonneg Cd, hν]
    exact key.trans (mul_le_mul_of_nonneg_right hK_le hEnn)
  have hrate : CylEnergyRate c m K (Ico s t) u :=
    ⟨fun τ => 2 * ∫ x in B0579.cell c, u τ x * (ν * lapP (u τ) x -
        (tr.v τ x 0 * B0579.pd 0 (u τ) x + tr.v τ x 1 * B0579.pd 1 (u τ) x)) *
          (B0579.density m x : ℝ),
      fun τ hτ => ⟨hderiv τ ⟨hτ.1, lt_of_lt_of_le hτ.2 ht.2⟩,
        hdiss τ ⟨hτ.1, lt_of_lt_of_le hτ.2 ht.2⟩⟩⟩
  have hgr := cyl_gronwall_of_rate (hcont.mono (Icc_subset_Icc le_rfl ht.2)) hrate ht.1
  have hexp_mono : Real.exp (2 * K * (t - s)) ≤ Real.exp (2 * K * (T - s)) := by
    apply Real.exp_le_exp.2
    nlinarith [ht.2, hK_pos]
  have hgrT : cylEnergy c m (u t) ≤ Real.exp (2 * K * (T - s)) * cylEnergy c m (u s) :=
    hgr.trans (mul_le_mul_of_nonneg_right hexp_mono (t22_energy_nonneg c m (u s)))
  have hut : MemLp (u t) 2 (B0579.cellMeasure c m) :=
    cylRegularMem ν c m s T tr.v u hc hm.le hu t ht
  have hus : MemLp (u s) 2 (B0579.cellMeasure c m) :=
    cylRegularMem ν c m s T tr.v u hc hm.le hu s ⟨le_rfl, hsT⟩
  have hsq : (eLpNorm (u t) 2 (B0579.cellMeasure c m)).toReal ^ 2 ≤
      Real.exp (2 * K * (T - s)) * (eLpNorm (u s) 2 (B0579.cellMeasure c m)).toReal ^ 2 := by
    rw [t22_energy_eq_sq_eLpNorm hut, t22_energy_eq_sq_eLpNorm hus]
    exact hgrT
  have hexp2 : Real.exp (2 * K * (T - s)) = Real.exp (K * (T - s)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hreal : (eLpNorm (u t) 2 (B0579.cellMeasure c m)).toReal ≤
      Real.exp (K * (T - s)) * (eLpNorm (u s) 2 (B0579.cellMeasure c m)).toReal := by
    have hnn : 0 ≤ Real.exp (K * (T - s)) * (eLpNorm (u s) 2 (B0579.cellMeasure c m)).toReal :=
      mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
    refine (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg hnn two_ne_zero).1 ?_
    rw [mul_pow, ← hexp2]
    exact hsq
  calc eLpNorm (u t) 2 (B0579.cellMeasure c m)
      = ENNReal.ofReal (eLpNorm (u t) 2 (B0579.cellMeasure c m)).toReal :=
        (ENNReal.ofReal_toReal hut.eLpNorm_lt_top.ne).symm
    _ ≤ ENNReal.ofReal (Real.exp (K * (T - s)) *
          (eLpNorm (u s) 2 (B0579.cellMeasure c m)).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Real.exp (K * (T - s))) * eLpNorm (u s) 2 (B0579.cellMeasure c m) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hus.eLpNorm_lt_top.ne]

private theorem norm_toLp_sub_eq {c m : ℝ} {g₁ g₂ : B0579.Plane → ℝ}
    (hg₁ : MemLp g₁ 2 (B0579.cellMeasure c m))
    (hg₂ : MemLp g₂ 2 (B0579.cellMeasure c m)) :
    ‖hg₁.toLp g₁ - hg₂.toLp g₂‖ = (eLpNorm (g₁ - g₂) 2 (B0579.cellMeasure c m)).toReal ∧
    eLpNorm (g₁ - g₂) 2 (B0579.cellMeasure c m) = ENNReal.ofReal ‖hg₁.toLp g₁ - hg₂.toLp g₂‖ := by
  have hae : (g₁ - g₂) =ᵐ[B0579.cellMeasure c m]
      ((hg₁.toLp g₁ - hg₂.toLp g₂ : B0579.X c m) : B0579.Plane → ℝ) := by
    filter_upwards [Lp.coeFn_sub (hg₁.toLp g₁) (hg₂.toLp g₂),
      MemLp.coeFn_toLp hg₁, MemLp.coeFn_toLp hg₂] with x h1 h2 h3
    rw [Pi.sub_apply, h1, Pi.sub_apply, h2, h3]
  rw [Lp.norm_def, eLpNorm_congr_ae hae]
  exact ⟨rfl, (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (hg₁.toLp g₁ - hg₂.toLp g₂))).symm⟩

private theorem norm_toLp_sub_lp_eq {c m : ℝ} {g : B0579.Plane → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) (G : B0579.X c m) :
    ‖hg.toLp g - G‖ =
      (eLpNorm (g - (G : B0579.Plane → ℝ)) 2 (B0579.cellMeasure c m)).toReal ∧
    eLpNorm (g - (G : B0579.Plane → ℝ)) 2 (B0579.cellMeasure c m) =
      ENNReal.ofReal ‖hg.toLp g - G‖ := by
  have hae : (g - (G : B0579.Plane → ℝ)) =ᵐ[B0579.cellMeasure c m]
      ((hg.toLp g - G : B0579.X c m) : B0579.Plane → ℝ) := by
    filter_upwards [Lp.coeFn_sub (hg.toLp g) G, MemLp.coeFn_toLp hg] with x h1 h2
    rw [Pi.sub_apply, h1, Pi.sub_apply, h2]
  rw [Lp.norm_def, eLpNorm_congr_ae hae]
  exact ⟨rfl, (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (hg.toLp g - G))).symm⟩

/-- **Main theorem (`PartII-b:T23/2`)**: `X_{m,c}` limit of regular cylinder flows from smooth test
approximants. -/
theorem freeCylApproxLimit_proof : UnforcedLeray.Short.IIb.FreeCylApproxLimit := by
  intro m ν c hm hν hc tr hbu s hs f hf fn ωn hfn hconv hωn
  have hm0 : 0 < m := by linarith
  have hm1 : 1 < m := by linarith
  set F : B0579.X c m := hf.toLp f
  let Fn : ℕ → B0579.X c m := fun n => ((hfn n).memLp m).toLp (fn n)
  have hFn_norm : ∀ n : ℕ, ‖Fn n - F‖ = (eLpNorm (fn n - f) 2 (B0579.cellMeasure c m)).toReal :=
    fun n => (norm_toLp_sub_eq ((hfn n).memLp m) hf).1
  have hFn_tendsto0 : Tendsto (fun n => ‖Fn n - F‖) atTop (𝓝 0) := by
    simp_rw [hFn_norm]
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  have hFn_lim : Tendsto Fn atTop (𝓝 F) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hFn_tendsto0
  have hFn_cauchy : CauchySeq Fn := hFn_lim.cauchySeq
  let Wn : ∀ (t : ℝ), s ≤ t → ℕ → B0579.X c m :=
    fun t hst n => ((hωn n).1.memX t hst).toLp (ωn n t)
  -- Uniform Cauchy / Lipschitz bound on [s, T]
  have hLip : ∀ (T : ℝ), s ≤ T → ∃ C_T : ℝ, 0 < C_T ∧
      ∀ (n k : ℕ) (t : ℝ) (hst : s ≤ t), t ≤ T →
        ‖Wn t hst n - Wn t hst k‖ ≤ C_T * ‖Fn n - Fn k‖ := by
    intro T hsT
    obtain ⟨C_T, hCT_pos, hCT⟩ := regular_energy_bound_of_buc (m := m) hm0 hν hc hbu hs hsT
    refine ⟨C_T, hCT_pos, fun n k t hst htT => ?_⟩
    have hreg_sub : IsRegularCylFlow c ν tr.v s T (fun r x => ωn n r x - ωn k r x) :=
      isRegularCylFlow_sub ((hωn n).2.2 T hsT) ((hωn k).2.2 T hsT)
    have hbd := hCT (fun r x => ωn n r x - ωn k r x) hreg_sub t ⟨hst, htT⟩
    have hinit : (fun x => ωn n s x - ωn k s x) = fn n - fn k := by
      funext x
      simp only [Pi.sub_apply, (hωn n).2.1, (hωn k).2.1]
    have hcur : (fun x => ωn n t x - ωn k t x) = ωn n t - ωn k t := rfl
    rw [hinit, hcur] at hbd
    have h1 := (norm_toLp_sub_eq ((hωn n).1.memX t hst) ((hωn k).1.memX t hst)).1
    have h2 := (norm_toLp_sub_eq ((hfn n).memLp m) ((hfn k).memLp m)).1
    have hfin : ENNReal.ofReal C_T * eLpNorm (fn n - fn k) 2 (B0579.cellMeasure c m) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (((hfn n).memLp m).sub ((hfn k).memLp m)).eLpNorm_lt_top.ne
    have htr := ENNReal.toReal_mono hfin hbd
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCT_pos.le] at htr
    change ‖Wn t hst n - Wn t hst k‖ ≤ C_T * ‖Fn n - Fn k‖
    rw [h1, h2]
    exact htr
  have hCauchy : ∀ (t : ℝ) (hst : s ≤ t), CauchySeq (Wn t hst) := by
    intro t hst
    obtain ⟨C_t, hCt_pos, hCt⟩ := hLip t hst
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hFn_cauchy (ε / C_t) (div_pos hε hCt_pos)
    refine ⟨N, fun n hn k hk => ?_⟩
    rw [dist_eq_norm]
    have h1 := hCt n k t hst le_rfl
    have h2 : ‖Fn n - Fn k‖ < ε / C_t := by simpa only [dist_eq_norm] using hN n hn k hk
    calc ‖Wn t hst n - Wn t hst k‖
        ≤ C_t * ‖Fn n - Fn k‖ := h1
      _ < C_t * (ε / C_t) := mul_lt_mul_of_pos_left h2 hCt_pos
      _ = ε := mul_div_cancel₀ ε hCt_pos.ne'
  choose W hW using fun (t : ℝ) (hst : s ≤ t) => cauchySeq_tendsto_of_complete (hCauchy t hst)
  let w : ℝ → B0579.Plane → ℝ := fun t =>
    if hst : s ≤ t then (W t hst : B0579.Plane → ℝ) else f
  have hw_eq : ∀ (t : ℝ) (hst : s ≤ t), w t = (W t hst : B0579.Plane → ℝ) :=
    fun t hst => dif_pos hst
  have hw_mem : ∀ (t : ℝ), s ≤ t → MemLp (w t) 2 (B0579.cellMeasure c m) := by
    intro t hst
    rw [hw_eq t hst]
    exact Lp.memLp (W t hst)
  have hw_conv : ∀ (t : ℝ), s ≤ t →
      Tendsto (fun n => eLpNorm (ωn n t - w t) 2 (B0579.cellMeasure c m)) atTop (𝓝 0) := by
    intro t hst
    rw [hw_eq t hst]
    have heq : ∀ n : ℕ, eLpNorm (ωn n t - (W t hst : B0579.Plane → ℝ)) 2 (B0579.cellMeasure c m) =
        ENNReal.ofReal ‖Wn t hst n - W t hst‖ :=
      fun n => (norm_toLp_sub_lp_eq ((hωn n).1.memX t hst) (W t hst)).2
    simp_rw [heq]
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_iff_norm_sub_tendsto_zero.1 (hW t hst))
  -- Uniform error bound against the limit on [s, T]
  have hUnif : ∀ (T : ℝ), s ≤ T → ∃ C_T : ℝ, 0 < C_T ∧
      ∀ (n : ℕ) (t : ℝ) (hst : s ≤ t), t ≤ T →
        (eLpNorm (ωn n t - w t) 2 (B0579.cellMeasure c m)).toReal ≤ C_T * ‖Fn n - F‖ := by
    intro T hsT
    obtain ⟨C_T, hCT_pos, hCT⟩ := hLip T hsT
    refine ⟨C_T, hCT_pos, fun n t hst htT => ?_⟩
    rw [hw_eq t hst, ← (norm_toLp_sub_lp_eq ((hωn n).1.memX t hst) (W t hst)).1]
    have hlim_lhs : Tendsto (fun k => ‖Wn t hst n - Wn t hst k‖) atTop
        (𝓝 ‖Wn t hst n - W t hst‖) :=
      ((tendsto_const_nhds.sub (hW t hst)).norm)
    have hlim_rhs : Tendsto (fun k => C_T * ‖Fn n - Fn k‖) atTop (𝓝 (C_T * ‖Fn n - F‖)) :=
      ((tendsto_const_nhds.sub hFn_lim).norm).const_mul C_T
    exact le_of_tendsto_of_tendsto hlim_lhs hlim_rhs
      (Eventually.of_forall fun k => hCT n k t hst htT)
  -- Initial condition w s =ᵐ f
  have hw_init : w s =ᵐ[volume.restrict (B0579.cell c)] f := by
    rw [hw_eq s le_rfl]
    have hWs_eq : W s le_rfl = F := by
      refine tendsto_nhds_unique (hW s le_rfl) ?_
      have heq_seq : Wn s le_rfl = Fn := by
        funext n
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((hωn n).1.memX s le_rfl),
          MemLp.coeFn_toLp ((hfn n).memLp m)] with x h1 h2
        dsimp [Wn, Fn]
        rw [h1, h2, (hωn n).2.1]
      rwa [heq_seq]
    rw [hWs_eq]
    exact (B0579.ac_cellMeasure c m).ae_le (MemLp.coeFn_toLp hf)
  -- Helper: convergence in X_{m,c} implies convergence of pairing against any cylinder test φ
  have hPair_lim : ∀ (φ : B0579.Plane → ℝ), B0579.IsCylTest c φ →
      ∀ (un : ℕ → B0579.Plane → ℝ) (u : B0579.Plane → ℝ),
        (∀ n, MemLp (un n) 2 (B0579.cellMeasure c m)) →
        MemLp u 2 (B0579.cellMeasure c m) →
        Tendsto (fun n => eLpNorm (un n - u) 2 (B0579.cellMeasure c m)) atTop (𝓝 0) →
        Tendsto (fun n => ∫ x in B0579.cell c, un n x * φ x) atTop
          (𝓝 (∫ x in B0579.cell c, u x * φ x)) := by
    intro φ hφ un u hun hu hulim
    obtain ⟨B0, hB0⟩ := lztCylBounded hc hφ
    have hφ_mem : MemLp φ 2 (B0579.cellMeasure c (-m)) :=
      cylLhs_memLp_neg hm1 c hφ.continuous hB0
    have htoReal : Tendsto (fun n => (eLpNorm (un n - u) 2 (B0579.cellMeasure c m)).toReal)
        atTop (𝓝 0) := by
      rw [← ENNReal.toReal_zero]
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hulim
    have h0 : Tendsto (fun n => (∫ x in B0579.cell c, un n x * φ x) -
        (∫ x in B0579.cell c, u x * φ x)) atTop (𝓝 0) := by
      refine squeeze_zero_norm ?_ (by simpa using htoReal.const_mul (cylLhsK c m * B0))
      intro n
      rw [Real.norm_eq_abs]
      have hi1 := cylLhs_integrableOn (un n) φ (hun n) hφ_mem
      have hi2 := cylLhs_integrableOn u φ hu hφ_mem
      have hsub : (∫ x in B0579.cell c, un n x * φ x) - (∫ x in B0579.cell c, u x * φ x) =
          ∫ x in B0579.cell c, (un n - u) x * φ x := by
        rw [← integral_sub hi1 hi2]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Pi.sub_apply, sub_mul]
      rw [hsub]
      exact cylLhs_pair hm1 hc (un n - u) φ B0 ((hun n).sub hu)
        hφ.continuous.aestronglyMeasurable (fun x _ => hB0 x)
    simpa using (tendsto_const_nhds (x := ∫ x in B0579.cell c, u x * φ x)).add h0
  -- Combined time-integrability of the tested RHS for w and convergence of its time integral
  have hw_time_and_lim : ∀ (φ : B0579.Plane → ℝ), B0579.IsCylTest c φ →
      ∀ (t₁ : ℝ), s ≤ t₁ →
        IntervalIntegrable (fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (w r) r φ x)
          volume s t₁ ∧
        Tendsto (fun n => ∫ r in s..t₁, ∫ x in B0579.cell c, cylFreeIntegrand tr (ωn n r) r φ x)
          atTop (𝓝 (∫ r in s..t₁, ∫ x in B0579.cell c, cylFreeIntegrand tr (w r) r φ x)) := by
    intro φ hφ t₁ hst₁
    have ht10 : 0 ≤ t₁ := le_trans hs hst₁
    obtain ⟨V, _, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu ht10
    obtain ⟨B1, hB1⟩ := lztCylBounded hc (hφ.pd 0)
    obtain ⟨B2, hB2⟩ := lztCylBounded hc (hφ.pd 1)
    obtain ⟨B3, hB3⟩ := lztCylBounded hc ((hφ.pd 0).pd 0)
    obtain ⟨B4, hB4⟩ := lztCylBounded hc ((hφ.pd 1).pd 1)
    obtain ⟨C_T, hCT_pos, hCT⟩ := hUnif t₁ hst₁
    set A : ℝ := |ν| * (|B3| + |B4|) + |V| * (|B1| + |B2|)
    let g : ℝ → B0579.Plane → ℝ := fun r x =>
      ν * lapP φ x + (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)
    have hg_prop : ∀ r ∈ Icc s t₁, Continuous (g r) ∧ ∀ x : B0579.Plane, |g r x| ≤ A := by
      intro r hr
      have hr0 : 0 ≤ r := le_trans hs hr.1
      have hvr : ContDiff ℝ ∞ (tr.v r) := by
        have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
          (s := univ) (fun z _ => ⟨mem_Ici.2 hr0, mem_univ z⟩)
        exact contDiffOn_univ.1 h
      have hv0_cont : Continuous (fun x => tr.v r x 0) :=
        (PiLp.continuous_apply 2 _ 0).comp hvr.continuous
      have hv1_cont : Continuous (fun x => tr.v r x 1) :=
        (PiLp.continuous_apply 2 _ 1).comp hvr.continuous
      have hlap_cont : Continuous (lapP φ) :=
        ((hφ.pd 0).pd 0).continuous.add ((hφ.pd 1).pd 1).continuous
      refine ⟨(continuous_const.mul hlap_cont).add
        ((hv0_cont.mul (hφ.pd 0).continuous).add (hv1_cont.mul (hφ.pd 1).continuous)), fun x => ?_⟩
      have hv0 := (hV r ⟨hr0, hr.2⟩ x 0).1.trans (le_abs_self V)
      have hv1 := (hV r ⟨hr0, hr.2⟩ x 1).1.trans (le_abs_self V)
      have hp1 := (hB1 x).trans (le_abs_self B1)
      have hp2 := (hB2 x).trans (le_abs_self B2)
      have hp3 := (hB3 x).trans (le_abs_self B3)
      have hp4 := (hB4 x).trans (le_abs_self B4)
      have hL : |lapP φ x| ≤ |B3| + |B4| := by
        unfold lapP
        exact (abs_add_le _ _).trans (add_le_add hp3 hp4)
      have t1 : |ν * lapP φ x| ≤ |ν| * (|B3| + |B4|) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hL (abs_nonneg _)
      have t2 : |tr.v r x 0 * B0579.pd 0 φ x| ≤ |V| * |B1| := by
        rw [abs_mul]; exact mul_le_mul hv0 hp1 (abs_nonneg _) (abs_nonneg _)
      have t3 : |tr.v r x 1 * B0579.pd 1 φ x| ≤ |V| * |B2| := by
        rw [abs_mul]; exact mul_le_mul hv1 hp2 (abs_nonneg _) (abs_nonneg _)
      have a1 := abs_add_le (ν * lapP φ x)
        (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)
      have a2 := abs_add_le (tr.v r x 0 * B0579.pd 0 φ x) (tr.v r x 1 * B0579.pd 1 φ x)
      dsimp [g, A]
      linarith
    let Hn : ℕ → ℝ → ℝ := fun n r => ∫ x in B0579.cell c, cylFreeIntegrand tr (ωn n r) r φ x
    let H : ℝ → ℝ := fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (w r) r φ x
    have hdiff_bd : ∀ (n : ℕ), ∀ r ∈ Icc s t₁,
        |Hn n r - H r| ≤ cylLhsK c m * A * (C_T * ‖Fn n - F‖) := by
      intro n r hr
      obtain ⟨hgc, hgb⟩ := hg_prop r hr
      have hg_mem := cylLhs_memLp_neg hm1 c hgc hgb
      have hi1 : IntegrableOn (cylFreeIntegrand tr (ωn n r) r φ) (B0579.cell c) :=
        (hωn n).1.integrable φ hφ r hr.1
      have hi2 : IntegrableOn (cylFreeIntegrand tr (w r) r φ) (B0579.cell c) :=
        cylLhs_integrableOn (w r) (g r) (hw_mem r hr.1) hg_mem
      have hsub_eq : Hn n r - H r = ∫ x in B0579.cell c, (ωn n r x - w r x) * g r x := by
        dsimp [Hn, H]
        rw [← integral_sub hi1 hi2]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp [cylFreeIntegrand, g]
        ring
      rw [hsub_eq]
      have hpair := cylLhs_pair hm1 hc (ωn n r - w r) (g r) A
        (((hωn n).1.memX r hr.1).sub (hw_mem r hr.1)) hgc.aestronglyMeasurable
        (fun x _ => hgb x)
      have hA0 : 0 ≤ A := by dsimp [A]; positivity
      have hK0 : 0 ≤ cylLhsK c m := ENNReal.toReal_nonneg
      exact hpair.trans (mul_le_mul_of_nonneg_left (hCT n r hr.1 hr.2) (mul_nonneg hK0 hA0))
    have hpt_lim : ∀ r ∈ Icc s t₁, Tendsto (fun n => Hn n r) atTop (𝓝 (H r)) := by
      intro r hr
      have h0 : Tendsto (fun n => Hn n r - H r) atTop (𝓝 0) := by
        refine squeeze_zero_norm ?_
          (by simpa using (hFn_tendsto0.const_mul C_T).const_mul (cylLhsK c m * A))
        intro n
        rw [Real.norm_eq_abs]
        exact hdiff_bd n r hr
      simpa using (tendsto_const_nhds (x := H r)).add h0
    have hmeasH : AEStronglyMeasurable H (volume.restrict (Ioc s t₁)) := by
      refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := Hn) ?_ ?_
      · intro n
        exact ((hωn n).1.timeIntegrable φ hφ t₁ hst₁).1.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hpt_lim r ⟨hr.1.le, hr.2⟩
    have hH0_int : IntervalIntegrable (Hn 0) volume s t₁ :=
      (hωn 0).1.timeIntegrable φ hφ t₁ hst₁
    have hsub_int : IntervalIntegrable (fun r => H r - Hn 0 r) volume s t₁ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst₁]
      refine Integrable.mono'
        (integrableOn_const (C := cylLhsK c m * A * (C_T * ‖Fn 0 - F‖)) measure_Ioc_lt_top.ne)
        (hmeasH.sub hH0_int.1.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hdiff_bd 0 r ⟨hr.1.le, hr.2⟩
    have hH_int : IntervalIntegrable H volume s t₁ := by
      have hsum := hsub_int.add hH0_int
      have hfun : (fun r => H r - Hn 0 r + Hn 0 r) = H := by funext r; ring
      rwa [hfun] at hsum
    refine ⟨hH_int, ?_⟩
    have hInt0 : Tendsto (fun n => (∫ r in s..t₁, Hn n r) - (∫ r in s..t₁, H r)) atTop (𝓝 0) := by
      have hbound_zero : Tendsto
          (fun n => cylLhsK c m * A * (C_T * ‖Fn n - F‖) * |t₁ - s|) atTop (𝓝 0) := by
        simpa using
          (((hFn_tendsto0.const_mul C_T).const_mul (cylLhsK c m * A)).mul_const |t₁ - s|)
      refine squeeze_zero_norm ?_ hbound_zero
      intro n
      rw [← intervalIntegral.integral_sub ((hωn n).1.timeIntegrable φ hφ t₁ hst₁) hH_int]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
      rw [uIoc_of_le hst₁] at hr
      rw [Real.norm_eq_abs]
      exact hdiff_bd n r ⟨hr.1.le, hr.2⟩
    simpa using (tendsto_const_nhds (x := ∫ r in s..t₁, H r)).add hInt0
  refine ⟨w, ⟨hw_init, hw_mem, ?_, ?_, ?_, ?_⟩, hw_conv⟩
  -- 1. strongCont
  · intro t hst
    obtain ⟨C_T, hCT_pos, hCT⟩ := hUnif (t + 1) (by linarith)
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    set εr : ℝ := (min ε 1).toReal / 4 with hεr_def
    have hmin_pos : 0 < min ε 1 := lt_min hε zero_lt_one
    have hmin_top : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    have hεr_pos : 0 < εr := div_pos (ENNReal.toReal_pos hmin_pos.ne' hmin_top) (by norm_num)
    obtain ⟨N, hN⟩ := (tendsto_order.1 hFn_tendsto0).2 (εr / C_T) (div_pos hεr_pos hCT_pos) |>.exists
    have hN_bound : C_T * ‖Fn N - F‖ < εr := by
      calc C_T * ‖Fn N - F‖ < C_T * (εr / C_T) := mul_lt_mul_of_pos_left hN hCT_pos
        _ = εr := mul_div_cancel₀ εr hCT_pos.ne'
    have hscN := (ENNReal.tendsto_nhds_zero.1 ((hωn N).1.strongCont t hst))
      (ENNReal.ofReal εr) (ENNReal.ofReal_pos.2 hεr_pos)
    have hnhds1 : Icc s (t + 1) ∈ 𝓝[Ici s] t := by
      refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith : t < t + 1)))) ?_
      intro σ hσ
      exact ⟨hσ.1, le_of_lt hσ.2⟩
    filter_upwards [hnhds1, hscN] with t' ht' ht'N
    have hdecomp : w t' - w t = (w t' - ωn N t') + ((ωn N t' - ωn N t) + (ωn N t - w t)) := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    have hm1' : AEStronglyMeasurable (w t' - ωn N t') (B0579.cellMeasure c m) :=
      ((hw_mem t' ht'.1).sub ((hωn N).1.memX t' ht'.1)).aestronglyMeasurable
    have hm2' : AEStronglyMeasurable (ωn N t' - ωn N t) (B0579.cellMeasure c m) :=
      (((hωn N).1.memX t' ht'.1).sub ((hωn N).1.memX t hst)).aestronglyMeasurable
    have hm3' : AEStronglyMeasurable (ωn N t - w t) (B0579.cellMeasure c m) :=
      (((hωn N).1.memX t hst).sub (hw_mem t hst)).aestronglyMeasurable
    have htri1 := eLpNorm_add_le (p := 2) hm1' (hm2'.add hm3') one_le_two
    have htri2 := eLpNorm_add_le (p := 2) hm2' hm3' one_le_two
    have hsym : eLpNorm (w t' - ωn N t') 2 (B0579.cellMeasure c m) =
        eLpNorm (ωn N t' - w t') 2 (B0579.cellMeasure c m) := by
      rw [show w t' - ωn N t' = -(ωn N t' - w t') by funext x; simp, eLpNorm_neg]
    have hb1 : eLpNorm (ωn N t' - w t') 2 (B0579.cellMeasure c m) ≤ ENNReal.ofReal εr := by
      have hfin := (((hωn N).1.memX t' ht'.1).sub (hw_mem t' ht'.1)).eLpNorm_lt_top.ne
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal ((hCT N t' ht'.1 ht'.2).trans hN_bound.le)
    have hb3 : eLpNorm (ωn N t - w t) 2 (B0579.cellMeasure c m) ≤ ENNReal.ofReal εr := by
      have hfin := (((hωn N).1.memX t hst).sub (hw_mem t hst)).eLpNorm_lt_top.ne
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal ((hCT N t hst (by linarith)).trans hN_bound.le)
    calc eLpNorm (w t' - w t) 2 (B0579.cellMeasure c m)
        ≤ eLpNorm (w t' - ωn N t') 2 (B0579.cellMeasure c m) +
            (eLpNorm (ωn N t' - ωn N t) 2 (B0579.cellMeasure c m) +
              eLpNorm (ωn N t - w t) 2 (B0579.cellMeasure c m)) := by
          rw [hdecomp]
          exact htri1.trans (add_le_add le_rfl htri2)
      _ ≤ ENNReal.ofReal εr + (ENNReal.ofReal εr + ENNReal.ofReal εr) := by
          rw [hsym]
          exact add_le_add hb1 (add_le_add ht'N hb3)
      _ = ENNReal.ofReal (3 * εr) := by
          rw [← ENNReal.ofReal_add hεr_pos.le hεr_pos.le,
            ← ENNReal.ofReal_add hεr_pos.le (by positivity)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (min ε 1).toReal := by
          apply ENNReal.ofReal_le_ofReal
          dsimp [εr]
          linarith [ENNReal.toReal_nonneg (a := min ε 1)]
      _ = min ε 1 := ENNReal.ofReal_toReal hmin_top
      _ ≤ ε := min_le_left _ _
  -- 2. integrable
  · intro φ hφ r hsr
    have hr0 : 0 ≤ r := le_trans hs hsr
    obtain ⟨V, _, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu hr0
    obtain ⟨B1, hB1⟩ := lztCylBounded hc (hφ.pd 0)
    obtain ⟨B2, hB2⟩ := lztCylBounded hc (hφ.pd 1)
    obtain ⟨B3, hB3⟩ := lztCylBounded hc ((hφ.pd 0).pd 0)
    obtain ⟨B4, hB4⟩ := lztCylBounded hc ((hφ.pd 1).pd 1)
    have hvr : ContDiff ℝ ∞ (tr.v r) := by
      have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (s := univ) (fun z _ => ⟨mem_Ici.2 hr0, mem_univ z⟩)
      exact contDiffOn_univ.1 h
    have hv0_cont : Continuous (fun x => tr.v r x 0) :=
      (PiLp.continuous_apply 2 _ 0).comp hvr.continuous
    have hv1_cont : Continuous (fun x => tr.v r x 1) :=
      (PiLp.continuous_apply 2 _ 1).comp hvr.continuous
    have hlap_cont : Continuous (lapP φ) :=
      ((hφ.pd 0).pd 0).continuous.add ((hφ.pd 1).pd 1).continuous
    have hg_cont : Continuous (fun x => ν * lapP φ x +
        (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)) :=
      (continuous_const.mul hlap_cont).add
        ((hv0_cont.mul (hφ.pd 0).continuous).add (hv1_cont.mul (hφ.pd 1).continuous))
    have hg_bd : ∀ x : B0579.Plane,
        |ν * lapP φ x + (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)| ≤
          |ν| * (|B3| + |B4|) + |V| * (|B1| + |B2|) := by
      intro x
      have hv0 := (hV r ⟨hr0, le_rfl⟩ x 0).1.trans (le_abs_self V)
      have hv1 := (hV r ⟨hr0, le_rfl⟩ x 1).1.trans (le_abs_self V)
      have hp1 := (hB1 x).trans (le_abs_self B1)
      have hp2 := (hB2 x).trans (le_abs_self B2)
      have hp3 := (hB3 x).trans (le_abs_self B3)
      have hp4 := (hB4 x).trans (le_abs_self B4)
      have hL : |lapP φ x| ≤ |B3| + |B4| := by
        unfold lapP
        exact (abs_add_le _ _).trans (add_le_add hp3 hp4)
      have t1 : |ν * lapP φ x| ≤ |ν| * (|B3| + |B4|) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hL (abs_nonneg _)
      have t2 : |tr.v r x 0 * B0579.pd 0 φ x| ≤ |V| * |B1| := by
        rw [abs_mul]; exact mul_le_mul hv0 hp1 (abs_nonneg _) (abs_nonneg _)
      have t3 : |tr.v r x 1 * B0579.pd 1 φ x| ≤ |V| * |B2| := by
        rw [abs_mul]; exact mul_le_mul hv1 hp2 (abs_nonneg _) (abs_nonneg _)
      have a1 := abs_add_le (ν * lapP φ x)
        (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)
      have a2 := abs_add_le (tr.v r x 0 * B0579.pd 0 φ x) (tr.v r x 1 * B0579.pd 1 φ x)
      linarith
    have hg_mem := cylLhs_memLp_neg hm1 c hg_cont hg_bd
    exact cylLhs_integrableOn (w r) _ (hw_mem r hsr) hg_mem
  -- 3. timeIntegrable
  · intro φ hφ t₁ hst₁
    exact (hw_time_and_lim φ hφ t₁ hst₁).1
  -- 4. weak
  · intro φ hφ t₁ hst₁
    have hL_lim : Tendsto (fun n => ∫ x in B0579.cell c, ωn n t₁ x * φ x) atTop
        (𝓝 (∫ x in B0579.cell c, w t₁ x * φ x)) :=
      hPair_lim φ hφ (fun n => ωn n t₁) (w t₁) (fun n => (hωn n).1.memX t₁ hst₁)
        (hw_mem t₁ hst₁) (hw_conv t₁ hst₁)
    have hR1_lim : Tendsto (fun n => ∫ x in B0579.cell c, fn n x * φ x) atTop
        (𝓝 (∫ x in B0579.cell c, f x * φ x)) :=
      hPair_lim φ hφ fn f (fun n => (hfn n).memLp m) hf hconv
    have hR2_lim := (hw_time_and_lim φ hφ t₁ hst₁).2
    have hR_lim : Tendsto (fun n => (∫ x in B0579.cell c, fn n x * φ x) +
        ∫ r in s..t₁, ∫ x in B0579.cell c, cylFreeIntegrand tr (ωn n r) r φ x) atTop
        (𝓝 ((∫ x in B0579.cell c, f x * φ x) +
          ∫ r in s..t₁, ∫ x in B0579.cell c, cylFreeIntegrand tr (w r) r φ x)) :=
      hR1_lim.add hR2_lim
    have heq_seq : (fun n => ∫ x in B0579.cell c, ωn n t₁ x * φ x) =
        (fun n => (∫ x in B0579.cell c, fn n x * φ x) +
          ∫ r in s..t₁, ∫ x in B0579.cell c, cylFreeIntegrand tr (ωn n r) r φ x) := by
      funext n
      exact (hωn n).1.weak φ hφ t₁ hst₁
    rw [heq_seq] at hL_lim
    exact tendsto_nhds_unique hL_lim hR_lim

end UnforcedLeray.Short.IIb

end
