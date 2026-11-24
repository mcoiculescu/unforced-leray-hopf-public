import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy

/-!
# Positive-age band Steklov difference bound for causal flat energy solutions

Source of record: `the November 2 reference manuscript`,
lines 1758–1764, 1785–1788, 3427–3440, 3541–3552.

For any standing causal energy solution `(b, Gr)` of the flat cylinder equation
`∂_s b + (μ / s) b - ν Δ_{q,η} b = 𝒫₀ div F` (`FreeSolData c ν μ F b Gr`) and any positive shift
`0 < δ ≤ min 1 (σ / 2)`, this file bounds the unweighted band difference integral
`∫⁻ s in Icc (σ / 2) H1, ∫⁻ x in B0579.cell c, ofReal (vnorm2 (b (s + δ, x) - b (s, x)) ^ 2)`
linearly in `δ` in terms of the band integrals of `energyE c b`, `energyN c Gr`, and `energyN c F`
on `Icc (σ / 2) (H1 + 1)`.

## Proof route
1. Apply `flatWeakFromDensity divFreeCutoffDensity` and `hasLMMollifier` to obtain `ExtWeakH1` and
   a cylinder mollifier family `J`.
2. For each `k : ℕ`, construct the `LMWeakDeriv` representative `u'(t) = -(μ / t) u_k(t) + Yt(t)`
   of `u_k(t) = J_k b(t)` as in `LMDerivRepAEH1`, and prove the two-slice pairing bound
   `|(LMIp c (u' t) (u_k r)).re| ≤ A_sq t + B_sq r` uniformly in `k` for good slices `t, r > 0`
   with `σ / 2 ≤ t` (`lmP0CAdj`, `lmP0CFix`, `lmAntiSymm`, `lmMoll_pd2_eq`, `IsLMMollifier.contr`).
3. Lift `(u_k, u')` to `HasWeakDerivTime (σ / 4) (H1 + 2) U U'` on `LMH c` (`lmRepExists`,
   `lmRepIdentity`, `lmRepPair`), write
   `‖rep (s + δ) - rep s‖² = ∫ t in Ioc s (s + δ), ⟪U' t, rep (s + δ) - rep s⟫`,
   and integrate over `s ∈ Icc (σ / 2) H1` via Tonelli (`lintegral_prod_symm`).
4. Pass `k → ∞` on a.e. slice via `IsLMMollifier.tendsto` (`lm_tendsto_vsq`) and Fatou's lemma
   (`lintegral_liminf_le`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open UnforcedLeray.BochnerTime
open scoped ENNReal ContDiff RealInnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N05_4_2Steklov

open UnforcedLeray.Short.IIIa

/-! ### 1. Explicit weak derivative construction for `u_k = LMMollU J b k` -/

/-- Explicit `Yt` and `LMWeakDeriv` witness for `u_k = LMMollU J b k`, exposing the a.e. slice
identification `Yt (s, ·) =ᵐ P0C c (lmDivJ J k (lmTens ν F G (s, ·)))` on good slices. -/
theorem exists_lmWeakDeriv_explicit {c ν : ℝ} {μ : ℂ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hS : FreeSolData c ν μ F b G)
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    (hE : ExtWeakH1 c ν μ F b G) (k : ℕ) :
    ∃ Yt : ℝ × (ℝ × ℝ) → Fin 2 → ℂ,
      (∀ i, Measurable fun p => Yt p i) ∧
      (∀ s, LMGoodSlice c F G b s →
        ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
          Yt (s, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i) ∧
      LMWeakDeriv c (LMMollU J b k) (lmUDer μ (LMMollU J b k) Yt) := by
  have hc : 0 < c := hS.pos_c
  have hX : LMMollH1 c J := ⟨hJ.gradL2, hJ.divFreeWeak⟩
  have hTm : ∀ i j, Measurable fun p => lmTens ν F G p i j := fun i j =>
    (measurable_const.mul (hS.sol.gradMeasurable i j)).add (hS.meas i j)
  obtain ⟨Y, hYm, hYe⟩ := lmDivJMeasRep c hc J hJ k (lmTens ν F G) hTm
  obtain ⟨Yt, hYtm, hYte⟩ := lmP0Rep c hc Y hYm
  have hgood : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), LMGoodSlice c F G b s :=
    lmAeGoodSlice c ν μ F b G hS
  have hYg : ∀ s, LMGoodSlice c F G b s → ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      Yt (s, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i := by
    intro s hs
    have e : (fun y => Y (s, y)) = lmDivJ J k (fun y => lmTens ν F G (s, y)) := by
      funext x i
      exact hYe s (fun j => lmTens_col_cellL2 hs j) x i
    rw [← e]
    exact hYte s
  have hYae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ∀ i : Fin 2, Yt (s, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i := by
    filter_upwards [hgood] with s hs using hYg s hs
  set u : ℝ → LMSpField := LMMollU J b k
  have hum : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i := fun i =>
    hJ.measurable k b hS.sol.measurable i
  have huL := lmUkL2Loc c ν μ F b G hS J hJ k
  have hYL := lmYtL2Loc c ν μ F b G hS J hJ hX k Yt hYtm hYae
  have hu'm : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => lmUDer μ u Yt p.1 p.2 i := fun i =>
    (((measurable_const.div (Complex.measurable_ofReal.comp measurable_fst)).neg).mul
      (hum i)).add (hYtm i)
  have hu'L : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => lmUDer μ u Yt p.1 p.2 i) ^ 2) < ⊤ := fun s₁ s₂ h1 h2 =>
    lmUDerL2Loc c μ u Yt hum hYtm s₁ s₂ h1 h2 (huL s₁ s₂ h1 h2) (hYL s₁ s₂ h1 h2)
  have huc : ∀ s, LMGoodSlice c F G b s → LMCellL2 c (u s) := fun s hs =>
    hJ.memL2 k _ hs.1
  have hYc : ∀ s, LMGoodSlice c F G b s → LMCellL2 c (fun x i => Yt (s, x) i) := by
    intro s hs i
    refine (lmP0C_cellL2 c (lmDivJ J k (fun y => lmTens ν F G (s, y))) i).ae_eq ?_
    filter_upwards [hYg s hs] with x hx
    exact (hx i).symm
  refine ⟨Yt, hYtm, hYg, ⟨hum, hu'm, huL, hu'L, ?_⟩⟩
  intro ψ hψ hcs hts χ hχ
  have hP0χ : LMWeakDivFree c (P0C c χ) := fun ψ' hψ' =>
    UnforcedLeray.Short.IIIa.p0DivFreeC c hc χ ψ' hψ'
  obtain ⟨hre, him⟩ := lmH1Test c hc J hJ hX k (P0C c χ) (lmP0C_cellL2 c χ) hP0χ
  have H0 := lmSliceTested c ν μ F b G hS hE ψ hψ hcs hts (J k (P0C c χ)) hre him
  have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hsdψ : tsupport (deriv ψ) ⊆ Ioi (0 : ℝ) :=
    (tsupport_deriv_subset (𝕜 := ℝ)).trans hts
  have hI1 := lmIpWeightedInt c χ u (deriv ψ) hχ hum huL hdψ hcs.deriv hsdψ
  have hI2 := lmIpWeightedInt c χ (lmUDer μ u Yt) ψ hχ hu'm hu'L hψ.continuous hcs hts
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      (-(((deriv ψ s : ℝ) : ℂ) * LMIp c (J k (P0C c χ)) (fun y => b (s, y))) +
        ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) * LMIp c (J k (P0C c χ)) (fun y => b (s, y))) +
        ((ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in B0579.cell c,
          starRingEnd ℂ (LMPd j (fun y => J k (P0C c χ) y i) x) * lmTens ν F G (s, x) i j) =
      -(((deriv ψ s : ℝ) : ℂ) * LMIp c χ (u s)) -
        ((ψ s : ℝ) : ℂ) * LMIp c χ (lmUDer μ u Yt s) := by
    filter_upwards [hgood, ae_restrict_mem measurableSet_Ioi] with s hs hs0
    have hs0' : (0 : ℝ) < s := hs0
    have hP1 : LMIp c (J k (P0C c χ)) (fun y => b (s, y)) = LMIp c χ (u s) :=
      lmSliceScalar lmP0CAdj lmP0CFix lmJWeakDiv hc hJ hX k hχ hs.1
        (fun ψ' hψ' => hS.sol.divFree s hs0' ψ' hψ')
    have hQ := lmSliceTensor c hc J hJ hX k χ (fun y => lmTens ν F G (s, y)) hχ
      (fun j => lmTens_col_cellL2 hs j)
    have hYp : LMIp c χ (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) =
        LMIp c χ (fun x i => Yt (s, x) i) :=
      lmIp_congr_right (by
        filter_upwards [hYg s hs] with x hx i
        exact (hx i).symm)
    have hsplit : LMIp c χ (lmUDer μ u Yt s) =
        -(μ / (s : ℂ)) * LMIp c χ (u s) + LMIp c χ (fun x i => Yt (s, x) i) := by
      have h1 : lmUDer μ u Yt s = fun x i => -(μ / (s : ℂ)) * u s x i + Yt (s, x) i := rfl
      have hsm : LMCellL2 c (fun x i => -(μ / (s : ℂ)) * u s x i) := fun i =>
        (huc s hs i).const_mul _
      rw [h1, lmIp_add_right hχ hsm (hYc s hs), lmIp_smul_right]
    rw [hP1, hQ, hYp, hsplit]
    ring
  rw [integral_congr_ae hae, integral_sub hI1.fun_neg hI2, integral_neg] at H0
  linear_combination -H0

/-! ### 2. Uniform two-slice pairing bound `|(LMIp c (u' t) (u_k r)).re| ≤ A_sq t + B_sq r` -/

/-- Band time-derivative constituent density at age `t`. -/
def bandASq (c ν σ M : ℝ) (F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (t : ℝ) : ℝ :=
  (2 * M * σ⁻¹) ^ 2 * energyE c b t + ν ^ 2 * energyN c G t + energyN c F t

/-- Band spatial `H¹` constituent density at age `r`. -/
def bandBSq (c : ℝ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (r : ℝ) : ℝ :=
  energyE c b r + energyN c G r

theorem norm_lmIp_le_half_sum {c : ℝ} {f g : LMSpField} (hf : LMCellL2 c f) (hg : LMCellL2 c g) :
    ‖LMIp c f g‖ ≤
      ((∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2) +
        (∫ x in B0579.cell c, ∑ i : Fin 2, ‖g x i‖ ^ 2)) / 2 := by
  have hfi : Integrable (fun x => ∑ i : Fin 2, ‖f x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
    domR_integrable_sum hf
  have hgi : Integrable (fun x => ∑ i : Fin 2, ‖g x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
    domR_integrable_sum hg
  have hbi : Integrable (fun x => (vnorm2 (f x) ^ 2 + vnorm2 (g x) ^ 2) / 2)
      (volume.restrict (B0579.cell c)) := by
    simp only [vnorm2_sq_eq]
    exact (hfi.add hgi).div_const 2
  unfold LMIp
  calc ‖∫ x in B0579.cell c, ∑ i : Fin 2, starRingEnd ℂ (f x i) * g x i‖
      ≤ ∫ x in B0579.cell c, (vnorm2 (f x) ^ 2 + vnorm2 (g x) ^ 2) / 2 :=
        norm_integral_le_of_norm_le hbi
          (Eventually.of_forall fun x => norm_conj_sum_le (f x) (g x))
    _ = ((∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2) +
          (∫ x in B0579.cell c, ∑ i : Fin 2, ‖g x i‖ ^ 2)) / 2 := by
        simp only [vnorm2_sq_eq]
        rw [integral_div, integral_add hfi hgi]

/-- Uniform-in-`k` pairing bound between `u'(t)` (`t ≥ σ / 2` good) and `u_k(r)` (`r > 0` good). -/
theorem abs_lmIp_uder_le {c ν σ M : ℝ} {μ : ℂ}
    {F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hS : FreeSolData c ν μ F b G) (hσ : 0 < σ) (hμM : ‖μ‖ ≤ M)
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J) (k : ℕ)
    {Yt : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {t r : ℝ}
    (hYg_t : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      Yt (t, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (t, y))) x i)
    (ht_band : σ / 2 ≤ t) (hr0 : 0 < r)
    (hgt : LMGoodSlice c F G b t) (hgr : LMGoodSlice c F G b r) :
    |(LMIp c (lmUDer μ (LMMollU J b k) Yt t) (LMMollU J b k r)).re| ≤
      bandASq c ν σ M F G b t + bandBSq c G b r := by
  have hc : 0 < c := hS.pos_c
  have hX : LMMollH1 c J := ⟨hJ.gradL2, hJ.divFreeWeak⟩
  have ht0 : 0 < t := lt_of_lt_of_le (half_pos hσ) ht_band
  set u := LMMollU J b k
  have hut : LMCellL2 c (u t) := hJ.memL2 k _ hgt.1
  have hur : LMCellL2 c (u r) := hJ.memL2 k _ hgr.1
  have hur_div : LMWeakDivFree c (u r) :=
    lmJWeakDiv c hc J hJ hX k _ hgr.1 fun ψ hψ => hS.sol.divFree r hr0 ψ hψ
  have hTc : ∀ j : Fin 2, LMCellL2 c (fun y i => lmTens ν F G (t, y) i j) :=
    fun j => lmTens_col_cellL2 hgt j
  have hZ := lmDivJ_cellL2 hX k hTc
  have hYt_L2 : LMCellL2 c (fun x i => Yt (t, x) i) := by
    intro i
    refine (lmP0C_cellL2 c (lmDivJ J k (fun y => lmTens ν F G (t, y))) i).ae_eq ?_
    filter_upwards [hYg_t] with x hx
    exact (hx i).symm
  have hsm : LMCellL2 c (fun x i => -(μ / (t : ℂ)) * u t x i) :=
    fun i => (hut i).const_mul _
  -- Split `lmUDer` into drift + divergence-projection parts
  have hsplit_ip : LMIp c (lmUDer μ u Yt t) (u r) =
      LMIp c (fun x i => -(μ / (t : ℂ)) * u t x i) (u r) +
        LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (t, y)))) (u r) := by
    have h1 : lmUDer μ u Yt t = fun x i => -(μ / (t : ℂ)) * u t x i + Yt (t, x) i := rfl
    rw [h1, lmIp_add_left hsm hYt_L2 hur, lmIp_congr_left hYg_t]
  -- Bound Part 1 (drift)
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hcoef : ‖-(μ / (t : ℂ))‖ ≤ 2 * M * σ⁻¹ := by
    rw [norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have h1 : t⁻¹ ≤ (σ / 2)⁻¹ := inv_anti₀ (half_pos hσ) ht_band
    have h2 : (σ / 2)⁻¹ = 2 * σ⁻¹ := by ring
    calc ‖μ‖ / t = ‖μ‖ * t⁻¹ := div_eq_mul_inv _ _
      _ ≤ M * (2 * σ⁻¹) := by
          rw [← h2]
          exact mul_le_mul hμM h1 (inv_nonneg.2 ht0.le) hM0
      _ = 2 * M * σ⁻¹ := by ring
  have hcoef_sq : ‖-(μ / (t : ℂ))‖ ^ 2 ≤ (2 * M * σ⁻¹) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcoef 2
  have hE_ut : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖u t x i‖ ^ 2 ≤ energyE c b t := by
    have hcontr := hJ.contr k (fun y => b (t, y)) hgt.1
    refine hcontr.trans (le_of_eq ?_)
    unfold energyE
    exact integral_congr_ae (ae_of_all _ fun x => (vnorm2_sq_eq _).symm)
  have hE_ur : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖u r x i‖ ^ 2 ≤ energyE c b r := by
    have hcontr := hJ.contr k (fun y => b (r, y)) hgr.1
    refine hcontr.trans (le_of_eq ?_)
    unfold energyE
    exact integral_congr_ae (ae_of_all _ fun x => (vnorm2_sq_eq _).symm)
  have hE_sm : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖-(μ / (t : ℂ)) * u t x i‖ ^ 2 ≤
      (2 * M * σ⁻¹) ^ 2 * energyE c b t := by
    have heq : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖-(μ / (t : ℂ)) * u t x i‖ ^ 2 =
        ‖-(μ / (t : ℂ))‖ ^ 2 * ∫ x in B0579.cell c, ∑ i : Fin 2, ‖u t x i‖ ^ 2 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_mul, mul_pow]
    rw [heq]
    have h0 : 0 ≤ ∫ x in B0579.cell c, ∑ i : Fin 2, ‖u t x i‖ ^ 2 :=
      integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
    exact mul_le_mul hcoef_sq hE_ut h0 (sq_nonneg _)
  have hdrift : |(LMIp c (fun x i => -(μ / (t : ℂ)) * u t x i) (u r)).re| ≤
      ((2 * M * σ⁻¹) ^ 2 * energyE c b t + energyE c b r) / 2 := by
    calc |(LMIp c (fun x i => -(μ / (t : ℂ)) * u t x i) (u r)).re|
        ≤ ‖LMIp c (fun x i => -(μ / (t : ℂ)) * u t x i) (u r)‖ := Complex.abs_re_le_norm _
      _ ≤ ((∫ x in B0579.cell c, ∑ i : Fin 2, ‖-(μ / (t : ℂ)) * u t x i‖ ^ 2) +
            (∫ x in B0579.cell c, ∑ i : Fin 2, ‖u r x i‖ ^ 2)) / 2 :=
          norm_lmIp_le_half_sum hsm hur
      _ ≤ ((2 * M * σ⁻¹) ^ 2 * energyE c b t + energyE c b r) / 2 := by linarith
  -- Bound Part 2 (viscous + forcing divergence)
  obtain ⟨C_g, hCg⟩ := hX.gradL2 k
  have hA_col : ∀ (h : LMSpField) (j : Fin 2), LMCellL2 c h →
      LMCellL2 c (fun x i => LMPd j (fun y => J k h y i) x) := fun h j hh i => (hCg h hh i j).1
  have e1 : LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (t, y)))) (u r) =
      LMIp c (lmDivJ J k (fun y => lmTens ν F G (t, y))) (u r) := by
    rw [lmP0CAdj c hc _ _ hZ hur]
    exact lmIp_congr_right (lmP0CFix c hc _ hur hur_div)
  have e2 : lmDivJ J k (fun y => lmTens ν F G (t, y)) = fun x i =>
      LMPd 0 (fun y => J k (fun y' i' => lmTens ν F G (t, y') i' 0) y i) x +
        LMPd 1 (fun y => J k (fun y' i' => lmTens ν F G (t, y') i' 1) y i) x := by
    funext x i
    simp only [lmDivJ, Fin.sum_univ_two]
  have hGW_r : ∀ i j : Fin 2, HasWeakCellDerivC c j (fun x => b (r, x) i)
      (fun x => (fun j y i => G (r, y) i j) j x i) := fun i j => hS.sol.weakGrad r hr0 i j
  have hpd2 : ∀ j : Fin 2, (fun x i => LMPd j (fun y => J k (u r) y i) x) =
      J k (J k (fun y i => G (r, y) i j)) := fun j => by
    funext x i
    exact lmMoll_pd2_eq lmSmoothWeakPd hc hJ (f := fun y => b (r, y))
      (g := fun j y i => G (r, y) i j) hgr.1 hgr.2.1 hGW_r k i j x
  have e3 : ∀ j : Fin 2, LMIp c
      (fun x i => LMPd j (fun y => J k (fun y' i' => lmTens ν F G (t, y') i' j) y i) x) (u r) =
      -LMIp c (fun y i => lmTens ν F G (t, y) i j) (J k (J k (fun y i => G (r, y) i j))) := by
    intro j
    rw [← lmIp_conj c (u r), lmAntiSymm c hc J hJ hX k j _ _ hur (hTc j), map_neg,
      lmIp_conj, hpd2 j]
  have hcol_bound : ∀ j : Fin 2,
      ‖LMIp c (fun y i => lmTens ν F G (t, y) i j) (J k (J k (fun y i => G (r, y) i j)))‖ ≤
        ((∫ x in B0579.cell c, ∑ i : Fin 2, ‖lmTens ν F G (t, x) i j‖ ^ 2) +
          (∫ x in B0579.cell c, ∑ i : Fin 2, ‖G (r, x) i j‖ ^ 2)) / 2 := by
    intro j
    have hJ2G : LMCellL2 c (J k (J k (fun y i => G (r, y) i j))) :=
      hJ.memL2 k _ (hJ.memL2 k _ (hgr.2.1 j))
    have hcontr2 : ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖J k (J k (fun y' i' => G (r, y') i' j)) x i‖ ^ 2 ≤
        ∫ x in B0579.cell c, ∑ i : Fin 2, ‖G (r, x) i j‖ ^ 2 :=
      (hJ.contr k _ (hJ.memL2 k _ (hgr.2.1 j))).trans (hJ.contr k _ (hgr.2.1 j))
    exact (norm_lmIp_le_half_sum (hTc j) hJ2G).trans (by linarith)
  have hsum_G : ∑ j : Fin 2, (∫ x in B0579.cell c, ∑ i : Fin 2, ‖G (r, x) i j‖ ^ 2) =
      energyN c G r := by
    rw [← integral_finsetSum Finset.univ (fun j _ => domR_integrable_sum (hgr.2.1 j))]
    unfold energyN
    simp only [domR_tnorm2_sq]
    exact integral_congr_ae (ae_of_all _ fun x => Finset.sum_comm)
  have hsum_T : ∑ j : Fin 2, (∫ x in B0579.cell c, ∑ i : Fin 2, ‖lmTens ν F G (t, x) i j‖ ^ 2) ≤
      2 * ν ^ 2 * energyN c G t + 2 * energyN c F t := by
    rw [← integral_finsetSum Finset.univ (fun j _ => domR_integrable_sum (hTc j))]
    have hG_int : Integrable (fun x => tnorm2 (G (t, x)) ^ 2) (volume.restrict (B0579.cell c)) := by
      simp only [domR_tnorm2_sq]
      refine (integrable_finsetSum Finset.univ (fun j _ => domR_integrable_sum (hgt.2.1 j))).congr ?_
      exact ae_of_all _ fun x => Finset.sum_comm
    have hF_int : Integrable (fun x => tnorm2 (F (t, x)) ^ 2) (volume.restrict (B0579.cell c)) := by
      simp only [domR_tnorm2_sq]
      refine (integrable_finsetSum Finset.univ (fun j _ => domR_integrable_sum (hgt.2.2 j))).congr ?_
      exact ae_of_all _ fun x => Finset.sum_comm
    have hpt : ∀ x : ℝ × ℝ,
        ∑ j : Fin 2, ∑ i : Fin 2, ‖lmTens ν F G (t, x) i j‖ ^ 2 ≤
          2 * ν ^ 2 * tnorm2 (G (t, x)) ^ 2 + 2 * tnorm2 (F (t, x)) ^ 2 := by
      intro x
      rw [domR_tnorm2_sq, domR_tnorm2_sq, Finset.sum_comm (s := Finset.univ) (t := Finset.univ),
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      unfold lmTens
      have htri : ‖(ν : ℂ) * G (t, x) i j + F (t, x) i j‖ ≤
          |ν| * ‖G (t, x) i j‖ + ‖F (t, x) i j‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      have habs : |ν| ^ 2 = ν ^ 2 := sq_abs ν
      nlinarith [sq_nonneg (|ν| * ‖G (t, x) i j‖ - ‖F (t, x) i j‖)]
    have hRHS_int : Integrable (fun x => 2 * ν ^ 2 * tnorm2 (G (t, x)) ^ 2 +
        2 * tnorm2 (F (t, x)) ^ 2) (volume.restrict (B0579.cell c)) :=
      (hG_int.const_mul (2 * ν ^ 2)).add (hF_int.const_mul 2)
    have hmono := integral_mono
      (integrable_finsetSum Finset.univ (fun j _ => domR_integrable_sum (hTc j)))
      hRHS_int hpt
    refine hmono.trans (le_of_eq ?_)
    rw [integral_add (hG_int.const_mul (2 * ν ^ 2)) (hF_int.const_mul 2),
      integral_const_mul, integral_const_mul]
    rfl
  have hdiv : |(LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (t, y)))) (u r)).re| ≤
      ν ^ 2 * energyN c G t + energyN c F t + energyN c G r / 2 := by
    rw [e1, e2, lmIp_add_left (hA_col _ 0 (hTc 0)) (hA_col _ 1 (hTc 1)) hur, e3 0, e3 1]
    have hre_le : |((-LMIp c (fun y i => lmTens ν F G (t, y) i 0)
          (J k (J k (fun y i => G (r, y) i 0)))) +
        (-LMIp c (fun y i => lmTens ν F G (t, y) i 1)
          (J k (J k (fun y i => G (r, y) i 1))))).re| ≤
        ‖LMIp c (fun y i => lmTens ν F G (t, y) i 0) (J k (J k (fun y i => G (r, y) i 0)))‖ +
          ‖LMIp c (fun y i => lmTens ν F G (t, y) i 1) (J k (J k (fun y i => G (r, y) i 1)))‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_neg]
    have hb0 := hcol_bound 0
    have hb1 := hcol_bound 1
    rw [Fin.sum_univ_two] at hsum_G hsum_T
    linarith
  -- Combine drift + divergence
  have hre_split : (LMIp c (lmUDer μ u Yt t) (u r)).re =
      (LMIp c (fun x i => -(μ / (t : ℂ)) * u t x i) (u r)).re +
        (LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (t, y)))) (u r)).re := by
    rw [hsplit_ip, Complex.add_re]
  rw [hre_split]
  have habs_add := abs_add_le
    ((LMIp c (fun x i => -(μ / (t : ℂ)) * u t x i) (u r)).re)
    ((LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (t, y)))) (u r)).re)
  have hE_t0 : 0 ≤ (2 * M * σ⁻¹) ^ 2 * energyE c b t :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hE_r0 : 0 ≤ energyE c b r := integral_nonneg fun _ => sq_nonneg _
  have hN_r0 : 0 ≤ energyN c G r := integral_nonneg fun _ => sq_nonneg _
  unfold bandASq bandBSq
  linarith

/-! ### 3. 1D Tonelli shift inequalities on `ℝ≥0∞` -/

theorem lintegral_Ioc_shift_eq {g : ℝ → ℝ≥0∞} (s δ : ℝ) :
    ∫⁻ t in Ioc s (s + δ), g t = ∫⁻ r in Ioc 0 δ, g (s + r) := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
  rw [← lintegral_add_left_eq_self (fun t => (Ioc s (s + δ)).indicator g t) s]
  refine lintegral_congr fun r => ?_
  by_cases hr : r ∈ Ioc 0 δ
  · have hsr : s + r ∈ Ioc s (s + δ) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    rw [indicator_of_mem hsr, indicator_of_mem hr]
  · have hsr : s + r ∉ Ioc s (s + δ) := fun h => hr ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [indicator_of_notMem hsr, indicator_of_notMem hr]

theorem lintegral_Icc_shift_le {g : ℝ → ℝ≥0∞} {a₀ b₀ r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∫⁻ s in Icc a₀ b₀, g (s + r) ≤ ∫⁻ t in Icc a₀ (b₀ + 1), g t := by
  rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
  calc ∫⁻ s, (Icc a₀ b₀).indicator (fun s => g (s + r)) s
      ≤ ∫⁻ s, (Icc a₀ (b₀ + 1)).indicator g (s + r) := by
        refine lintegral_mono fun s => ?_
        by_cases hs : s ∈ Icc a₀ b₀
        · have hsr : s + r ∈ Icc a₀ (b₀ + 1) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
          rw [indicator_of_mem hs, indicator_of_mem hsr]
        · rw [indicator_of_notMem hs]
          exact zero_le
    _ = ∫⁻ t, (Icc a₀ (b₀ + 1)).indicator g t :=
        lintegral_add_right_eq_self (fun t => (Icc a₀ (b₀ + 1)).indicator g t) r

theorem lintegral_band_window_le {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {a₀ b₀ δ : ℝ} (_hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫⁻ s in Icc a₀ b₀, (∫⁻ t in Ioc s (s + δ), g t) ≤
      ENNReal.ofReal δ * ∫⁻ t in Icc a₀ (b₀ + 1), g t := by
  have h1 : ∀ s : ℝ, ∫⁻ t in Ioc s (s + δ), g t = ∫⁻ r in Ioc 0 δ, g (s + r) :=
    fun s => lintegral_Ioc_shift_eq s δ
  simp_rw [h1]
  have hgm : Measurable (fun p : ℝ × ℝ => g (p.1 + p.2)) :=
    hg.comp (measurable_fst.add measurable_snd)
  rw [lintegral_lintegral_swap hgm.aemeasurable]
  calc ∫⁻ r in Ioc 0 δ, ∫⁻ s in Icc a₀ b₀, g (s + r)
      ≤ ∫⁻ r in Ioc 0 δ, ∫⁻ t in Icc a₀ (b₀ + 1), g t := by
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
        exact lintegral_Icc_shift_le hr.1.le (hr.2.trans hδ1)
    _ = volume (Ioc 0 δ) * ∫⁻ t in Icc a₀ (b₀ + 1), g t := by
        rw [setLIntegral_const, mul_comm]
    _ = ENNReal.ofReal δ * ∫⁻ t in Icc a₀ (b₀ + 1), g t := by
        rw [Real.volume_Ioc, sub_zero]

/-! ### 4. Uniform band Steklov bound for `u_k` and `k → ∞` Fatou limit -/

/-- For each fixed `k : ℕ`, the mollified field `u_k = LMMollU J b k` satisfies the `O(δ)` band
difference bound with constant independent of `k`. -/
theorem lintegral_moll_band_diff_le {c ν σ H1 M δ : ℝ} {μ : ℂ}
    {F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hS : FreeSolData c ν μ F b G) (hE : ExtWeakH1 c ν μ F b G)
    (hσ : 0 < σ) (hσH : σ ≤ H1) (hμM : ‖μ‖ ≤ M)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J) (k : ℕ) :
    ∫⁻ s in Icc (σ / 2) H1,
        ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (vnorm2 (fun i => LMMollU J b k (s + δ) x i - LMMollU J b k s x i) ^ 2) ≤
      ENNReal.ofReal (δ * ((2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F G b t) +
        2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c G b r)) := by
  have hc : 0 < c := hS.pos_c
  obtain ⟨Yt, _hYtm, hYg, hWD⟩ := exists_lmWeakDeriv_explicit hS hJ hE k
  set u := LMMollU J b k
  set u' := lmUDer μ u Yt
  obtain ⟨U, U', hU, hU', hint⟩ := lmRepExists c hc u u' hWD
  set a := σ / 4
  set b_end := H1 + 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b_end := by dsimp [a, b_end]; linarith
  have hweak : HasWeakDerivTime a b_end U U' :=
    ⟨(hint a b_end ha hab).1, (hint a b_end ha hab).2,
      fun ψ hψ hψc hψt => lmRepIdentity c hc u u' hWD U U' hU hU' hint a b_end ha hab ψ hψ hψc hψt⟩
  -- Good slice predicate on `r : ℝ`
  let Good (r : ℝ) : Prop :=
    0 < r →
      LMGoodSlice c F G b r ∧
      (r ∈ Ioo a b_end → U r = hweak.rep r) ∧
      (∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (U r : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x = lmReal (u r x)) ∧
      (∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (U' r : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x = lmReal (u' r x))
  have hGood_ae : ∀ᵐ r : ℝ, Good r := by
    have h1 := (ae_restrict_iff' measurableSet_Ioi).1 (lmAeGoodSlice c ν μ F b G hS)
    have h2 := (ae_restrict_iff' measurableSet_Ioo).1 hweak.ae_eq_rep
    have h3 := (ae_restrict_iff' measurableSet_Ioi).1 hU
    have h4 := (ae_restrict_iff' measurableSet_Ioi).1 hU'
    filter_upwards [h1, h2, h3, h4] with r hr1 hr2 hr3 hr4 hr0
    exact ⟨hr1 hr0, hr2, hr3 hr0, hr4 hr0⟩
  have hGood_shift : ∀ᵐ s : ℝ, Good (s + δ) :=
    (measurePreserving_add_right volume δ).quasiMeasurePreserving.ae hGood_ae
  -- Integrability and measurability of `bandASq` and `bandBSq`
  have hσ2_pos : 0 < σ / 2 := half_pos hσ
  have hband_lt : σ / 2 < H1 + 1 := by linarith
  obtain ⟨hIntE, hIntN, hIntF⟩ := lmEnergyLocInt c ν μ F b G hS (σ / 2) (H1 + 1) hσ2_pos hband_lt
  have hIntA : IntegrableOn (bandASq c ν σ M F G b) (Icc (σ / 2) (H1 + 1)) :=
    ((hIntE.const_mul _).add (hIntN.const_mul _)).add hIntF
  have hIntB : IntegrableOn (bandBSq c G b) (Icc (σ / 2) (H1 + 1)) :=
    hIntE.add hIntN
  have hMeasE : Measurable (energyE c b) :=
    ((loc_measurable_vnorm2 hS.sol.measurable).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hMeasN : Measurable (energyN c G) :=
    ((loc_measurable_tnorm2 hS.sol.gradMeasurable).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hMeasF : Measurable (energyN c F) :=
    ((loc_measurable_tnorm2 hS.meas).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hMeasA : Measurable (bandASq c ν σ M F G b) :=
    ((hMeasE.const_mul _).add (hMeasN.const_mul _)).add hMeasF
  have hMeasB : Measurable (bandBSq c G b) := hMeasE.add hMeasN
  have hA_nonneg : ∀ t, 0 ≤ bandASq c ν σ M F G b t := fun t => by
    unfold bandASq
    have h1 : 0 ≤ energyE c b t := integral_nonneg fun _ => sq_nonneg _
    have h2 : 0 ≤ energyN c G t := integral_nonneg fun _ => sq_nonneg _
    have h3 : 0 ≤ energyN c F t := integral_nonneg fun _ => sq_nonneg _
    positivity
  have hB_nonneg : ∀ r, 0 ≤ bandBSq c G b r := fun r => by
    unfold bandBSq
    have h1 : 0 ≤ energyE c b r := integral_nonneg fun _ => sq_nonneg _
    have h2 : 0 ≤ energyN c G r := integral_nonneg fun _ => sq_nonneg _
    positivity
  -- Pointwise a.e. slice bound on `s ∈ Icc (σ / 2) H1`
  have hae_slice : ∀ᵐ s ∂(volume.restrict (Icc (σ / 2) H1)),
      ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (vnorm2 (fun i => u (s + δ) x i - u s x i) ^ 2) ≤
        (∫⁻ t in Ioc s (s + δ), ENNReal.ofReal (2 * bandASq c ν σ M F G b t)) +
          ENNReal.ofReal δ * ENNReal.ofReal (bandBSq c G b (s + δ) + bandBSq c G b s) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hGood_ae, hGood_shift] with s hGs hGsd hsIcc
    have hs0 : 0 < s := lt_of_lt_of_le hσ2_pos hsIcc.1
    have hsd0 : 0 < s + δ := by linarith
    have hs_Ioo : s ∈ Ioo a b_end := ⟨by dsimp [a]; linarith [hsIcc.1], by dsimp [b_end]; linarith [hsIcc.2]⟩
    have hsd_Ioo : s + δ ∈ Ioo a b_end :=
      ⟨by dsimp [a]; linarith [hsIcc.1], by dsimp [b_end]; linarith [hsIcc.2]⟩
    obtain ⟨hgood_s, hUs_rep, hUs_ae, _⟩ := hGs hs0
    obtain ⟨hgood_sd, hUsd_rep, hUsd_ae, _⟩ := hGsd hsd0
    let v : LMH c := hweak.rep (s + δ) - hweak.rep s
    have hv_eq_U : v = U (s + δ) - U s := by
      dsimp [v]
      rw [hUsd_rep hsd_Ioo, hUs_rep hs_Ioo]
    let d_k : LMSpField := fun x i => u (s + δ) x i - u s x i
    have hdk_L2 : LMCellL2 c d_k := fun i =>
      (hJ.memL2 k _ hgood_sd.1 i).sub (hJ.memL2 k _ hgood_s.1 i)
    have hv_ae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x = lmReal (d_k x) := by
      rw [hv_eq_U]
      filter_upwards [Lp.coeFn_sub (U (s + δ)) (U s), hUsd_ae, hUs_ae] with x hsub h1 h2
      rw [hsub, Pi.sub_apply, h1, h2]
      ext j
      fin_cases j <;> simp [lmReal, d_k]
    -- Relate `∫⁻ ofReal (vnorm2 d_k ^ 2)` to `‖v‖ ^ 2`
    have hdk_int : Integrable (fun x => vnorm2 (d_k x) ^ 2) (volume.restrict (B0579.cell c)) :=
      integrable_vnorm2_sq hdk_L2
    have hnorm_v : ‖v‖ ^ 2 = ∫ x in B0579.cell c, vnorm2 (d_k x) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hv_ae] with x hx
      rw [hx, real_inner_self_eq_norm_sq, norm_lmReal_sq]
    have hlint_eq : ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (d_k x) ^ 2) =
        ENNReal.ofReal (‖v‖ ^ 2) := by
      rw [hnorm_v, ofReal_integral_eq_lintegral_ofReal hdk_int
        (Eventually.of_forall fun _ => sq_nonneg _)]
    -- FTC inner product representation `‖v‖ ^ 2 = ∫ t in Ioc s (s + δ), ⟪U' t, v⟫`
    have hsub_Ioc_Ioo : Ioc s (s + δ) ⊆ Ioo a b_end := fun t ht =>
      ⟨lt_trans hs_Ioo.1 ht.1, lt_of_le_of_lt ht.2 hsd_Ioo.2⟩
    have hIntU'_Ioc : IntegrableOn U' (Ioc s (s + δ)) := hweak.int'.mono_set hsub_Ioc_Ioo
    have hv_ftc : v = ∫ t in Ioc s (s + δ), U' t := by
      have hrep := hweak.rep_sub_rep (Ioo_subset_Icc_self hs_Ioo) (Ioo_subset_Icc_self hsd_Ioo)
      rwa [intervalIntegral.integral_of_le (by linarith : s ≤ s + δ)] at hrep
    have hftc_sq : ‖v‖ ^ 2 = ∫ t in Ioc s (s + δ), ⟪U' t, v⟫ := by
      calc ‖v‖ ^ 2 = ⟪v, v⟫ := (real_inner_self_eq_norm_sq v).symm
        _ = ⟪v, ∫ t in Ioc s (s + δ), U' t⟫ := by nth_rw 2 [hv_ftc]
        _ = ∫ t in Ioc s (s + δ), ⟪v, U' t⟫ := (integral_inner hIntU'_Ioc v).symm
        _ = ∫ t in Ioc s (s + δ), ⟪U' t, v⟫ :=
            integral_congr_ae (ae_of_all _ fun t => real_inner_comm _ _)
    -- Bound `⟪U' t, v⟫` for a.e. `t ∈ Ioc s (s + δ)`
    have hae_t : ∀ᵐ t ∂(volume.restrict (Ioc s (s + δ))),
        ⟪U' t, v⟫ ≤ 2 * bandASq c ν σ M F G b t + (bandBSq c G b (s + δ) + bandBSq c G b s) := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hGood_ae] with t hGt htIoc
      have ht_band : σ / 2 ≤ t := le_trans hsIcc.1 htIoc.1.le
      have ht0 : 0 < t := lt_of_lt_of_le hσ2_pos ht_band
      obtain ⟨hgood_t, _, _, hU't_ae⟩ := hGt ht0
      have hut' : LMCellL2 c (u' t) := by
        have h1 : u' t = fun x i => -(μ / (t : ℂ)) * u t x i + Yt (t, x) i := rfl
        rw [h1]
        intro i
        refine ((hJ.memL2 k _ hgood_t.1 i).const_mul _).add ?_
        refine (lmP0C_cellL2 c (lmDivJ J k (fun y => lmTens ν F G (t, y))) i).ae_eq ?_
        filter_upwards [hYg t hgood_t] with x hx
        exact (hx i).symm
      have hinner_eq : ⟪U' t, v⟫ = (LMIp c (u' t) d_k).re := by
        have hre : (LMIp c (u' t) d_k).re =
            ∫ x in B0579.cell c, (∑ i : Fin 2, starRingEnd ℂ (u' t x i) * d_k x i).re := by
          unfold LMIp
          exact (integral_re (integrable_LMIp_integrand hut' hdk_L2)).symm
        rw [hre, L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [hU't_ae, hv_ae] with x hx1 hx2
        rw [hx1, hx2, lmReal_inner]
      have hdk_split : LMIp c (u' t) d_k = LMIp c (u' t) (u (s + δ)) - LMIp c (u' t) (u s) := by
        have hd_eq : d_k = fun x i => u (s + δ) x i + (-1 : ℂ) * u s x i := by
          funext x i; simp [d_k, sub_eq_add_neg]
        have husd : LMCellL2 c (u (s + δ)) := hJ.memL2 k _ hgood_sd.1
        have hneg_L2 : LMCellL2 c (fun x i => (-1 : ℂ) * u s x i) :=
          fun i => (hJ.memL2 k _ hgood_s.1 i).const_mul _
        rw [hd_eq, lmIp_add_right hut' husd hneg_L2, lmIp_smul_right]
        ring
      have hb1 := abs_lmIp_uder_le hS hσ hμM hJ k (hYg t hgood_t) ht_band hsd0 hgood_t hgood_sd
      have hb2 := abs_lmIp_uder_le hS hσ hμM hJ k (hYg t hgood_t) ht_band hs0 hgood_t hgood_s
      rw [hinner_eq, hdk_split, Complex.sub_re]
      linarith [le_abs_self ((LMIp c (u' t) (u (s + δ))).re),
        neg_le_abs ((LMIp c (u' t) (u s)).re)]
    -- Integrate over `t ∈ Ioc s (s + δ)`
    have hsub_Ioc_band : Ioc s (s + δ) ⊆ Icc (σ / 2) (H1 + 1) := fun t ht =>
      ⟨le_trans hsIcc.1 ht.1.le, by linarith [ht.2, hsIcc.2]⟩
    have hInt_inner : IntegrableOn (fun t => ⟪U' t, v⟫) (Ioc s (s + δ)) :=
      (((innerSL ℝ v : LMH c →L[ℝ] ℝ).integrable_comp hIntU'_Ioc).congr
        (ae_of_all _ fun t => (real_inner_comm v (U' t)).symm))
    have hInt_A_Ioc : IntegrableOn (fun t => 2 * bandASq c ν σ M F G b t) (Ioc s (s + δ)) :=
      (hIntA.mono_set hsub_Ioc_band).const_mul 2
    have hInt_const_Ioc : IntegrableOn (fun _ : ℝ => bandBSq c G b (s + δ) + bandBSq c G b s)
        (Ioc s (s + δ)) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have h_v_le : ‖v‖ ^ 2 ≤ (∫ t in Ioc s (s + δ), 2 * bandASq c ν σ M F G b t) +
        δ * (bandBSq c G b (s + δ) + bandBSq c G b s) := by
      rw [hftc_sq]
      calc ∫ t in Ioc s (s + δ), ⟪U' t, v⟫
          ≤ ∫ t in Ioc s (s + δ),
              (2 * bandASq c ν σ M F G b t + (bandBSq c G b (s + δ) + bandBSq c G b s)) :=
            integral_mono_ae hInt_inner (hInt_A_Ioc.add hInt_const_Ioc) hae_t
        _ = (∫ t in Ioc s (s + δ), 2 * bandASq c ν σ M F G b t) +
              δ * (bandBSq c G b (s + δ) + bandBSq c G b s) := by
            rw [integral_add hInt_A_Ioc hInt_const_Ioc, setIntegral_const, smul_eq_mul,
              Measure.real, Real.volume_Ioc, add_sub_cancel_left, ENNReal.toReal_ofReal hδ0.le]
    rw [hlint_eq]
    calc ENNReal.ofReal (‖v‖ ^ 2)
        ≤ ENNReal.ofReal ((∫ t in Ioc s (s + δ), 2 * bandASq c ν σ M F G b t) +
            δ * (bandBSq c G b (s + δ) + bandBSq c G b s)) :=
          ENNReal.ofReal_le_ofReal h_v_le
      _ = ENNReal.ofReal (∫ t in Ioc s (s + δ), 2 * bandASq c ν σ M F G b t) +
            ENNReal.ofReal δ * ENNReal.ofReal (bandBSq c G b (s + δ) + bandBSq c G b s) := by
          rw [ENNReal.ofReal_add (integral_nonneg fun t => mul_nonneg zero_le_two (hA_nonneg t))
            (mul_nonneg hδ0.le (add_nonneg (hB_nonneg _) (hB_nonneg _))),
            ENNReal.ofReal_mul hδ0.le]
      _ = (∫⁻ t in Ioc s (s + δ), ENNReal.ofReal (2 * bandASq c ν σ M F G b t)) +
            ENNReal.ofReal δ * ENNReal.ofReal (bandBSq c G b (s + δ) + bandBSq c G b s) := by
          rw [ofReal_integral_eq_lintegral_ofReal hInt_A_Ioc
            (Eventually.of_forall fun t => mul_nonneg zero_le_two (hA_nonneg t))]
  -- Integrate `hae_slice` over `s ∈ Icc (σ / 2) H1`
  have hm1 : Measurable (fun s : ℝ =>
      ∫⁻ t in Ioc s (s + δ), ENNReal.ofReal (2 * bandASq c ν σ M F G b t)) := by
    have h_eq : (fun s : ℝ => ∫⁻ t in Ioc s (s + δ), ENNReal.ofReal (2 * bandASq c ν σ M F G b t)) =
        fun s => ∫⁻ r in Ioc 0 δ, ENNReal.ofReal (2 * bandASq c ν σ M F G b (s + r)) :=
      funext fun s => lintegral_Ioc_shift_eq s δ
    rw [h_eq]
    exact ((ENNReal.measurable_ofReal.comp (hMeasA.const_mul 2)).comp
      (measurable_fst.add measurable_snd)).lintegral_prod_right'
  have hwinA := lintegral_band_window_le
    (ENNReal.measurable_ofReal.comp (hMeasA.const_mul 2)) (a₀ := σ / 2) (b₀ := H1) hδ0 hδ1
  have hIntA_lint : ∫⁻ t in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (2 * bandASq c ν σ M F G b t) =
      ENNReal.ofReal (2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F G b t) := by
    rw [← integral_const_mul, ← ofReal_integral_eq_lintegral_ofReal (hIntA.const_mul 2)
      (Eventually.of_forall fun t => mul_nonneg zero_le_two (hA_nonneg t))]
  have hB_shift_le : ∫⁻ s in Icc (σ / 2) H1,
      ENNReal.ofReal (bandBSq c G b (s + δ) + bandBSq c G b s) ≤
      ENNReal.ofReal (2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c G b r) := by
    have hsplit_B : ∀ s : ℝ, ENNReal.ofReal (bandBSq c G b (s + δ) + bandBSq c G b s) =
        ENNReal.ofReal (bandBSq c G b (s + δ)) + ENNReal.ofReal (bandBSq c G b s) :=
      fun s => ENNReal.ofReal_add (hB_nonneg _) (hB_nonneg _)
    simp_rw [hsplit_B]
    have hmB_shift : Measurable (fun s : ℝ => ENNReal.ofReal (bandBSq c G b (s + δ))) :=
      ENNReal.measurable_ofReal.comp (hMeasB.comp (measurable_id.add_const δ))
    rw [lintegral_add_left hmB_shift]
    have hb1 : ∫⁻ s in Icc (σ / 2) H1, ENNReal.ofReal (bandBSq c G b (s + δ)) ≤
        ∫⁻ r in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (bandBSq c G b r) :=
      lintegral_Icc_shift_le hδ0.le hδ1
    have hb2 : ∫⁻ s in Icc (σ / 2) H1, ENNReal.ofReal (bandBSq c G b s) ≤
        ∫⁻ r in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (bandBSq c G b r) :=
      lintegral_mono_set (Icc_subset_Icc_right (by linarith))
    have hIntB_lint : ∫⁻ r in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (bandBSq c G b r) =
        ENNReal.ofReal (∫ r in Icc (σ / 2) (H1 + 1), bandBSq c G b r) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hIntB (Eventually.of_forall hB_nonneg)]
    calc (∫⁻ s in Icc (σ / 2) H1, ENNReal.ofReal (bandBSq c G b (s + δ))) +
            ∫⁻ s in Icc (σ / 2) H1, ENNReal.ofReal (bandBSq c G b s)
        ≤ (∫⁻ r in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (bandBSq c G b r)) +
            ∫⁻ r in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (bandBSq c G b r) :=
          add_le_add hb1 hb2
      _ = ENNReal.ofReal (2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c G b r) := by
          rw [hIntB_lint, ← ENNReal.ofReal_add (integral_nonneg fun r => hB_nonneg r)
            (integral_nonneg fun r => hB_nonneg r), two_mul]
  have hmB_sum : Measurable (fun s : ℝ =>
      ENNReal.ofReal (bandBSq c G b (s + δ) + bandBSq c G b s)) :=
    ENNReal.measurable_ofReal.comp ((hMeasB.comp (measurable_id.add_const δ)).add hMeasB)
  calc ∫⁻ s in Icc (σ / 2) H1,
          ∫⁻ x in B0579.cell c,
            ENNReal.ofReal (vnorm2 (fun i => u (s + δ) x i - u s x i) ^ 2)
      ≤ ∫⁻ s in Icc (σ / 2) H1,
          ((∫⁻ t in Ioc s (s + δ), ENNReal.ofReal (2 * bandASq c ν σ M F G b t)) +
            ENNReal.ofReal δ * ENNReal.ofReal (bandBSq c G b (s + δ) + bandBSq c G b s)) :=
        lintegral_mono_ae hae_slice
    _ = (∫⁻ s in Icc (σ / 2) H1,
          ∫⁻ t in Ioc s (s + δ), ENNReal.ofReal (2 * bandASq c ν σ M F G b t)) +
          ENNReal.ofReal δ * ∫⁻ s in Icc (σ / 2) H1,
            ENNReal.ofReal (bandBSq c G b (s + δ) + bandBSq c G b s) := by
        rw [lintegral_add_left hm1, lintegral_const_mul _ hmB_sum]
    _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F G b t) +
          ENNReal.ofReal δ * ENNReal.ofReal (2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c G b r) := by
        rw [← hIntA_lint]
        have hwinA' : ∫⁻ s in Icc (σ / 2) H1,
            ∫⁻ t in Ioc s (s + δ), ENNReal.ofReal (2 * bandASq c ν σ M F G b t) ≤
            ENNReal.ofReal δ * ∫⁻ t in Icc (σ / 2) (H1 + 1),
              ENNReal.ofReal (2 * bandASq c ν σ M F G b t) := hwinA
        gcongr
    _ = ENNReal.ofReal (δ * ((2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F G b t) +
          2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c G b r)) := by
        have hA_int0 : 0 ≤ 2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F G b t :=
          mul_nonneg zero_le_two (integral_nonneg fun t => hA_nonneg t)
        have hB_int0 : 0 ≤ 2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c G b r :=
          mul_nonneg zero_le_two (integral_nonneg fun r => hB_nonneg r)
        rw [← mul_add, ← ENNReal.ofReal_add hA_int0 hB_int0,
          ← ENNReal.ofReal_mul hδ0.le]

/-- **Main positive-age band Steklov bound** for any standing causal energy solution
`FreeSolData c ν μ F b G` and any positive shift `0 < δ ≤ 1`: passes `k → ∞` in
`lintegral_moll_band_diff_le` via `IsLMMollifier.tendsto` (`lm_tendsto_vsq`) and Fatou's lemma. -/
theorem lintegral_band_diff_le {c ν σ H1 M δ : ℝ} {μ : ℂ}
    {F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hS : FreeSolData c ν μ F b G) (hσ : 0 < σ) (hσH : σ ≤ H1) (hμM : ‖μ‖ ≤ M)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫⁻ s in Icc (σ / 2) H1,
        ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (vnorm2 (fun i => b (s + δ, x) i - b (s, x) i) ^ 2) ≤
      ENNReal.ofReal (δ * ((2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F G b t) +
        2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c G b r)) := by
  have hE : ExtWeakH1 c ν μ F b G := flatWeakFromDensity divFreeCutoffDensity c ν μ F b G hS
  obtain ⟨J, hJ⟩ := hasLMMollifier c hS.pos_c
  let fk (k : ℕ) (s : ℝ) : ℝ≥0∞ :=
    ∫⁻ x in B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => LMMollU J b k (s + δ) x i - LMMollU J b k s x i) ^ 2)
  let f0 (s : ℝ) : ℝ≥0∞ :=
    ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => b (s + δ, x) i - b (s, x) i) ^ 2)
  have hfk_meas : ∀ k : ℕ, Measurable (fk k) := fun k => by
    have hum : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => LMMollU J b k p.1 p.2 i :=
      fun i => hJ.measurable k b hS.sol.measurable i
    have hdiff : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) =>
        LMMollU J b k (p.1 + δ) p.2 i - LMMollU J b k p.1 p.2 i := fun i =>
      ((hum i).comp ((measurable_fst.add_const δ).prodMk measurable_snd)).sub (hum i)
    have hv : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (vnorm2 (fun i =>
          LMMollU J b k (p.1 + δ) p.2 i - LMMollU J b k p.1 p.2 i) ^ 2) :=
      ENNReal.measurable_ofReal.comp ((loc_measurable_vnorm2 hdiff).pow_const 2)
    exact hv.lintegral_prod_right'
  -- Pointwise convergence `fk k s → f0 s` on a.e. `s ∈ Icc (σ / 2) H1`
  have hgood_ae : ∀ᵐ r : ℝ, 0 < r → LMGoodSlice c F G b r :=
    (ae_restrict_iff' measurableSet_Ioi).1 (lmAeGoodSlice c ν μ F b G hS)
  have hgood_shift : ∀ᵐ s : ℝ, 0 < s + δ → LMGoodSlice c F G b (s + δ) :=
    (measurePreserving_add_right volume δ).quasiMeasurePreserving.ae hgood_ae
  have hae_lim : ∀ᵐ s ∂(volume.restrict (Icc (σ / 2) H1)), f0 s ≤ liminf (fun k => fk k s) atTop := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hgood_ae, hgood_shift] with s hs hsd hsIcc
    have hs0 : 0 < s := lt_of_lt_of_le (half_pos hσ) hsIcc.1
    have hsd0 : 0 < s + δ := by linarith
    have hbs : LMCellL2 c (fun y => b (s, y)) := (hs hs0).1
    have hbsd : LMCellL2 c (fun y => b (s + δ, y)) := (hsd hsd0).1
    let d : LMSpField := fun y i => b (s + δ, y) i - b (s, y) i
    have hd : LMCellL2 c d := fun i => (hbsd i).sub (hbs i)
    have hJk_eq : ∀ (k : ℕ) (x : ℝ × ℝ),
        (fun i => LMMollU J b k (s + δ) x i - LMMollU J b k s x i) = J k d x := by
      intro k x
      have hd' : d = fun y i => b (s + δ, y) i + (-1 : ℂ) * b (s, y) i := by
        funext y i; simp [d, sub_eq_add_neg]
      have hneg : LMCellL2 c (fun y i => (-1 : ℂ) * b (s, y) i) := fun i => (hbs i).const_mul _
      have h1 := congr_fun (by rw [hd', hJ.add k _ _ hbsd hneg, hJ.smul k (-1 : ℂ) _ hbs] :
        J k d = _) x
      rw [h1]
      funext i
      simp [LMMollU, sub_eq_add_neg]
    have htend_real : Tendsto (fun k : ℕ => ∫ x in B0579.cell c, vnorm2 (J k d x) ^ 2) atTop
        (𝓝 (∫ x in B0579.cell c, vnorm2 (d x) ^ 2)) :=
      lm_tendsto_vsq (fun k => hJ.memL2 k d hd) hd (hJ.tendsto d hd)
    have htend_enn : Tendsto (fun k : ℕ => fk k s) atTop (𝓝 (f0 s)) := by
      have hf0_eq : f0 s = ENNReal.ofReal (∫ x in B0579.cell c, vnorm2 (d x) ^ 2) := by
        dsimp [f0, d]
        rw [ofReal_integral_eq_lintegral_ofReal (integrable_vnorm2_sq hd)
          (Eventually.of_forall fun _ => sq_nonneg _)]
      have hfk_eq : ∀ k : ℕ, fk k s =
          ENNReal.ofReal (∫ x in B0579.cell c, vnorm2 (J k d x) ^ 2) := by
        intro k
        dsimp [fk]
        simp_rw [hJk_eq k]
        rw [ofReal_integral_eq_lintegral_ofReal (integrable_vnorm2_sq (hJ.memL2 k d hd))
          (Eventually.of_forall fun _ => sq_nonneg _)]
      rw [hf0_eq]
      simp_rw [hfk_eq]
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp htend_real
    exact le_of_eq htend_enn.liminf_eq.symm
  -- Apply Fatou (`lintegral_liminf_le`)
  calc ∫⁻ s in Icc (σ / 2) H1, f0 s
      ≤ ∫⁻ s in Icc (σ / 2) H1, liminf (fun k => fk k s) atTop :=
        lintegral_mono_ae hae_lim
    _ ≤ liminf (fun k => ∫⁻ s in Icc (σ / 2) H1, fk k s) atTop :=
        lintegral_liminf_le (fun k => (hfk_meas k))
    _ ≤ ENNReal.ofReal (δ * ((2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F G b t) +
          2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c G b r)) := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
        exact lintegral_moll_band_diff_le hS hE hσ hσH hμM hδ0 hδ1 hJ k

end UnforcedLeray.Short.PartIIa.N05_4_2Steklov
