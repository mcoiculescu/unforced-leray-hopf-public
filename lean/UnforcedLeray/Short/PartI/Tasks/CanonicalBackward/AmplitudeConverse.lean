import UnforcedLeray.Short.PartI.Sub.PartI_C08_1_3

/-!
# `PartI:C08/1/3/3`: proof of `AmplitudeConverse`

Source lines 1094-1125.  Write `E(x,τ) = e^{(log τ - log x)D}` (base `x`, `x ≤ τ`), `ℓ = ⟪qd,·⟫`.
From the free Duhamel form of `W` at base `x` and the self-adjointness of `E`,
`ℓ(W x) = ⟪E(x,τ)qd, W τ⟫ + ∫_x^τ ℓ(E(x,σ)K_σW_σ)`.  With `E(x,τ)qd = qd + ∫_x^τ σ⁻¹E(x,σ)Dqd`
(`hasDerivAt_expD_logSub_domain`), `ℓ L₀ = λℓ` and `ℓ(D qd-pairing) = κ`, the right derivative of
`A(τ) = ℓ(W τ)` at `x` is `-x⁻¹ ℓ(Dr(x))`, and the fundamental theorem of calculus on `[θ,s₀]`
gives the claim.  (`expD a` clamps negative `a` to `0`, so only `a ≥ 0` is used.)
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set Filter Topology

/-- Self-adjointness of the free evolution `e^{aD}`, `a ≥ 0`. -/
theorem amp_adj {a : ℝ} (ha : 0 ≤ a) (u v : B0010.XG) :
    inner ℂ (B0123.expD a u) v = inner ℂ u (B0123.expD a v) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, Cons.G3b.expD_adjoint_eq_self ha]

/-- Continuity of `t ↦ log t - log x` on a set of positive reals. -/
theorem amp_log_sub_cont {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) (x : ℝ) :
    ContinuousOn (fun t : ℝ => Real.log t - Real.log x) s :=
  ContinuousOn.sub (ContinuousOn.log continuousOn_id fun t ht => (hs t ht).ne') continuousOn_const

/-- The integrand `t ↦ t⁻¹ e^{(log t - log x)D} y` is continuous on a set of positive reals. -/
theorem amp_h_cont {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) (x : ℝ) (y : B0010.XG) :
    ContinuousOn (fun t : ℝ => t⁻¹ • B0123.expD (Real.log t - Real.log x) y) s :=
  (continuousOn_id.inv₀ fun t ht => (hs t ht).ne').smul
    ((Cons.G3b.continuous_expD_apply y).comp_continuousOn (amp_log_sub_cont hs x))

/-- The normalized coefficient `t ↦ canonicalFullGen λ κ t (W t)` is continuous on a set of
positive reals where `W` is continuous. -/
theorem amp_K_cont (lam κ : ℂ) {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) {W : ℝ → B0010.XG}
    (hW : ContinuousOn W s) :
    ContinuousOn (fun t => canonicalFullGen lam κ t (W t)) s := by
  have hinv : ContinuousOn (fun t : ℝ => (t : ℂ)⁻¹) s :=
    Complex.continuous_ofReal.continuousOn.inv₀ fun t ht =>
      Complex.ofReal_ne_zero.mpr (hs t ht).ne'
  have h1 : ContinuousOn (fun t => Planar.L0 (W t)) s :=
    Planar.L0.continuous.comp_continuousOn hW
  have h2 : ContinuousOn (fun t : ℝ => lam • W t) s :=
    (continuous_const_smul lam).comp_continuousOn hW
  have h3 : ContinuousOn (fun t : ℝ => (κ * (t : ℂ)⁻¹) • W t) s :=
    (continuousOn_const.mul hinv).smul hW
  have heq : (fun t => canonicalFullGen lam κ t (W t)) =
      fun t : ℝ => (Planar.L0 (W t) - lam • W t) - (κ * (t : ℂ)⁻¹) • W t := by
    funext t
    simp only [canonicalFullGen, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
  rw [heq]
  exact (h1.sub h2).sub h3

/-- The free-evolution FTC: `∫_x^τ t⁻¹ e^{(log t - log x)D} Dz = e^{(log τ - log x)D}z - z`. -/
theorem amp_ftc {x τ : ℝ} (hx : 0 < x) (hxτ : x ≤ τ) {qd : B0010.XG}
    (hqd : qd ∈ B0094.D.domain) :
    ∫ t in x..τ, t⁻¹ • B0123.expD (Real.log t - Real.log x) (B0094.D ⟨qd, hqd⟩) =
      B0123.expD (Real.log τ - Real.log x) qd - B0123.expD (Real.log x - Real.log x) qd := by
  have hsub : ∀ t ∈ Icc x τ, 0 < t := fun t ht => lt_of_lt_of_le hx ht.1
  have hcg : ContinuousOn (fun t : ℝ => B0123.expD (Real.log t - Real.log x) qd) (Icc x τ) :=
    (Cons.G3b.continuous_expD_apply qd).comp_continuousOn (amp_log_sub_cont hsub x)
  have hderiv : ∀ t ∈ Ioo x τ,
      HasDerivWithinAt (fun t : ℝ => B0123.expD (Real.log t - Real.log x) qd)
        (t⁻¹ • B0123.expD (Real.log t - Real.log x) (B0094.D ⟨qd, hqd⟩)) (Ioi t) t :=
    fun t ht => (hasDerivAt_expD_logSub_domain hx ht.1 ⟨qd, hqd⟩).hasDerivWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hxτ hcg hderiv
    ((amp_h_cont hsub x _).intervalIntegrable_of_Icc hxτ)

theorem amplitudeConverse_proof : UnforcedLeray.Short.PartI.AmplitudeConverse := by
  intro lam q l hI qd hl hq hqd b hb W hWc hW θ s₀ hθ hθs
  have hθ0 : 0 < θ := lt_of_lt_of_le hb hθ
  -- the left eigen-relation `ℓ L₀ = λ ℓ`, from the rank-one spectral projection
  have hL : ∀ w, l (Planar.L0 w) = lam * l w := by
    intro w
    have h1 : (Infra.Dunford.rankOneProj l q * Planar.L0) w = (lam • Infra.Dunford.rankOneProj l q) w := by
      rw [hI.proj.proj_mul]
    simp only [Infra.Dunford.rankOneProj, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply] at h1
    have h2 : (l (Planar.L0 w)) • q = (lam * l w) • q := by
      rw [h1, mul_smul]
    exact smul_left_injective ℂ hI.ne_zero h2
  -- `⟪Dqd, q⟫ = κ`
  have hDsymm : inner ℂ (B0094.D ⟨qd, hqd⟩) q = seedKappa l q hq := by
    have h : inner ℂ (B0094.D ⟨qd, hqd⟩) q = inner ℂ qd (B0094.D ⟨q, hq⟩) :=
      B0094.D_symm ⟨qd, hqd⟩ ⟨q, hq⟩
    rw [h, seedKappa, hl]
  -- the coefficient at the base point
  have hKl : ∀ x : ℝ, l (canonicalFullGen lam (seedKappa l q hq) x (W x)) =
      -((seedKappa l q hq * (x : ℂ)⁻¹) * l (W x)) := by
    intro x
    simp only [canonicalFullGen, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, map_sub, map_smul, hL, smul_eq_mul]
    ring
  -- the Duhamel identity at base `x`, paired with `ℓ`
  have hK1 : ∀ x τ : ℝ, b ≤ x → x ≤ τ → l (W x) =
      inner ℂ (B0123.expD (Real.log τ - Real.log x) qd) (W τ) +
        ∫ σ in x..τ, l (B0123.expD (Real.log σ - Real.log x)
          (canonicalFullGen lam (seedKappa l q hq) σ (W σ))) := by
    intro x τ hx hxτ
    have hx0 : 0 < x := lt_of_lt_of_le hb hx
    obtain ⟨hi, he⟩ := hW x τ hx hxτ
    simp only [Pi.zero_apply, add_zero] at hi he
    have hlog : 0 ≤ Real.log τ - Real.log x := sub_nonneg.mpr (Real.log_le_log hx0 hxτ)
    rw [he, map_add, ContinuousLinearMap.intervalIntegral_comp_comm l hi, hl,
      amp_adj hlog]
  -- the derivative of `τ ↦ ℓ(W τ)` on the right of each interior point
  have hA_deriv : ∀ x ∈ Ioo θ s₀, HasDerivWithinAt (fun τ => l (W τ))
      (-(seedLD qd hqd (W x - l (W x) • q) / (x : ℂ))) (Ioi x) x := by
    intro x hx
    have hxb : b < x := lt_of_le_of_lt hθ hx.1
    have hx0 : 0 < x := lt_trans hb hxb
    have hWx : ContinuousOn W (Ioi b) := hWc.mono fun t ht => Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp ht))
    have hKc := amp_K_cont lam (seedKappa l q hq) (fun t ht => lt_trans hb ht) hWx
    have hhc := amp_h_cont (s := Ioi b) (fun t ht => lt_trans hb ht) x
      (B0094.D ⟨qd, hqd⟩)
    have hFc : ContinuousOn (fun t : ℝ => l (B0123.expD (Real.log t - Real.log x)
        (canonicalFullGen lam (seedKappa l q hq) t (W t)))) (Ioi b) :=
      l.continuous.comp_continuousOn
        (Short.Spine.CanonicalMild.continuousOn_expD_pair (amp_log_sub_cont
          (fun t ht => lt_trans hb ht) x) hKc)
    -- integrability on `[x, τ]`
    have hhint : ∀ τ, x ≤ τ → IntervalIntegrable
        (fun t : ℝ => t⁻¹ • B0123.expD (Real.log t - Real.log x) (B0094.D ⟨qd, hqd⟩))
        volume x τ := fun τ hτ =>
      (hhc.mono (fun t ht => lt_of_lt_of_le hxb ht.1)).intervalIntegrable_of_Icc hτ
    have hFint : ∀ τ, x ≤ τ → IntervalIntegrable
        (fun t : ℝ => l (B0123.expD (Real.log t - Real.log x)
          (canonicalFullGen lam (seedKappa l q hq) t (W t)))) volume x τ := fun τ hτ =>
      (hFc.mono (fun t ht => lt_of_lt_of_le hxb ht.1)).intervalIntegrable_of_Icc hτ
    -- one-sided derivatives of the two primitives at `x`
    have hIhD : HasDerivAt (fun τ => ∫ t in x..τ,
        t⁻¹ • B0123.expD (Real.log t - Real.log x) (B0094.D ⟨qd, hqd⟩))
        (x⁻¹ • B0123.expD (Real.log x - Real.log x) (B0094.D ⟨qd, hqd⟩)) x :=
      intervalIntegral.integral_hasDerivAt_right (hhint x le_rfl)
        (hhc.stronglyMeasurableAtFilter isOpen_Ioi x hxb) (hhc.continuousAt (Ioi_mem_nhds hxb))
    have hIFD : HasDerivAt (fun τ => ∫ t in x..τ,
        l (B0123.expD (Real.log t - Real.log x) (canonicalFullGen lam (seedKappa l q hq) t (W t))))
        (l (B0123.expD (Real.log x - Real.log x)
          (canonicalFullGen lam (seedKappa l q hq) x (W x)))) x :=
      intervalIntegral.integral_hasDerivAt_right (hFint x le_rfl)
        (hFc.stronglyMeasurableAtFilter isOpen_Ioi x hxb) (hFc.continuousAt (Ioi_mem_nhds hxb))
    have hIhS := (hasDerivWithinAt_iff_tendsto_slope' (fun h => lt_irrefl x h)).mp
      hIhD.hasDerivWithinAt
    have hIFS := (hasDerivWithinAt_iff_tendsto_slope' (fun h => lt_irrefl x h)).mp
      hIFD.hasDerivWithinAt
    have hWt : Tendsto W (𝓝[Ioi x] x) (𝓝 (W x)) :=
      ((hWx.continuousAt (Ioi_mem_nhds hxb)).tendsto).mono_left nhdsWithin_le_nhds
    -- the slope identity at `τ > x`
    have hid : ∀ τ ∈ Ioi x, slope (fun τ => l (W τ)) x τ =
        -(inner ℂ (slope (fun τ => ∫ t in x..τ,
            t⁻¹ • B0123.expD (Real.log t - Real.log x) (B0094.D ⟨qd, hqd⟩)) x τ) (W τ)) -
          slope (fun τ => ∫ t in x..τ,
            l (B0123.expD (Real.log t - Real.log x)
              (canonicalFullGen lam (seedKappa l q hq) t (W t)))) x τ := by
      intro τ hτ
      have hxτ : x ≤ τ := le_of_lt hτ
      have hK := hK1 x τ (le_of_lt hxb) hxτ
      have hF := amp_ftc hx0 hxτ hqd
      have hE0 : B0123.expD (Real.log x - Real.log x) qd = qd := by
        rw [sub_self, B0123.expD_zero, ContinuousLinearMap.one_apply]
      have hEτ : B0123.expD (Real.log τ - Real.log x) qd =
          (∫ t in x..τ, t⁻¹ • B0123.expD (Real.log t - Real.log x) (B0094.D ⟨qd, hqd⟩)) + qd := by
        rw [hF, hE0, sub_add_cancel]
      have hkey : l (W x) = l (W τ) + inner ℂ (∫ t in x..τ,
            t⁻¹ • B0123.expD (Real.log t - Real.log x) (B0094.D ⟨qd, hqd⟩)) (W τ) +
          ∫ σ in x..τ, l (B0123.expD (Real.log σ - Real.log x)
            (canonicalFullGen lam (seedKappa l q hq) σ (W σ))) := by
        rw [hK, hEτ, inner_add_left, hl (W τ)]
        abel
      have hIh0 : (∫ t in x..x, t⁻¹ • B0123.expD (Real.log t - Real.log x)
          (B0094.D ⟨qd, hqd⟩)) = 0 := intervalIntegral.integral_same
      have hIF0 : (∫ t in x..x, l (B0123.expD (Real.log t - Real.log x)
          (canonicalFullGen lam (seedKappa l q hq) t (W t)))) = 0 :=
        intervalIntegral.integral_same
      simp only [slope_def_module, hIh0, hIF0, sub_zero]
      have hin : ∀ (c : ℝ) (v w : B0010.XG), inner ℂ (c • v) w = c • inner ℂ v w := by
        intro c v w
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c v, inner_smul_real_left]
      rw [hkey, hin]
      have hz : l (W τ) - (l (W τ) + inner ℂ (∫ t in x..τ,
            t⁻¹ • B0123.expD (Real.log t - Real.log x) (B0094.D ⟨qd, hqd⟩)) (W τ) +
          ∫ σ in x..τ, l (B0123.expD (Real.log σ - Real.log x)
            (canonicalFullGen lam (seedKappa l q hq) σ (W σ)))) =
          -(inner ℂ (∫ t in x..τ, t⁻¹ • B0123.expD (Real.log t - Real.log x)
            (B0094.D ⟨qd, hqd⟩)) (W τ) + ∫ σ in x..τ, l (B0123.expD (Real.log σ - Real.log x)
            (canonicalFullGen lam (seedKappa l q hq) σ (W σ)))) := by
        ring
      rw [hz, smul_neg, smul_add, neg_add]
      exact (sub_eq_add_neg _ _).symm
    have hT1 := Filter.Tendsto.inner (𝕜 := ℂ) hIhS hWt
    have hT := (hT1.neg).sub hIFS
    have hT' := hT.congr' (eventually_of_mem self_mem_nhdsWithin
      (fun τ hτ => (hid τ hτ).symm))
    have hD := (hasDerivWithinAt_iff_tendsto_slope' (fun h => lt_irrefl x h)).mpr hT'
    refine hD.congr_deriv ?_
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    simp only [sub_self, B0123.expD_zero, ContinuousLinearMap.one_apply]
    rw [hKl x]
    simp only [seedLD, innerSL_apply_apply, inner_sub_right, inner_smul_right, hDsymm,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left]
    try simp only [map_inv₀, Complex.conj_ofReal, Complex.conj_inv, Complex.coe_algebraMap,
      Complex.ofReal_inv]
    field_simp
    ring
  have hcontA : ContinuousOn (fun τ => l (W τ)) (Icc θ s₀) :=
    l.continuous.comp_continuousOn (hWc.mono fun t ht => Set.mem_Ici.mpr (le_trans hθ ht.1))
  have hrc : ContinuousOn (fun x => W x - l (W x) • q) (Icc θ s₀) :=
    (hWc.mono fun t ht => Set.mem_Ici.mpr (le_trans hθ ht.1)).sub
      (hcontA.smul continuousOn_const)
  have hsd : ContinuousOn (fun x => seedLD qd hqd (W x - l (W x) • q)) (Icc θ s₀) :=
    (seedLD qd hqd).continuous.comp_continuousOn hrc
  have hfc : ContinuousOn (fun x => -(seedLD qd hqd (W x - l (W x) • q) / (x : ℂ)))
      (Icc θ s₀) :=
    (hsd.div Complex.continuous_ofReal.continuousOn fun x hx =>
      Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hθ0 hx.1).ne').neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hθs hcontA
    (fun x hx => hA_deriv x hx) (hfc.intervalIntegrable_of_Icc hθs)
  rw [intervalIntegral.integral_neg] at hftc
  linear_combination hftc

end UnforcedLeray.Short.PartI
