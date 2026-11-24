import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1.Equations
import UnforcedLeray.Lib.BochnerTime.Basic

/-!
# `PartIII-a:T19/2/3/2/1` helpers: the weak time derivative of `H(r) = r^μ ⟨w(r), Ψ⟩`

Testing the two causal equations (SP 3426-3440) with `Φ = Re/Im(r^μ θ(r)) Ψ(x)`, `Ψ = (∂_η φ, -∂_q φ)`,
the `μ/r` terms cancel against the derivative of `r^μ` and
`∫ θ' H = -∫ θ J`, `J(r) = r^μ ∫ (ν w · ΔΨ + (v⊗b + b⊗v) : ∇Ψ)` (SP 3489-3491: conjugation by `r^μ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.V1

open UnforcedLeray.Short.IIIa

variable {ν c : ℝ}

theorem flat_diff (tr : UnforcedLeray.B0140.TrainSol ν c) (μ : ℂ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (α : ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) :
    flatIntegrand ν μ (trainVel tr) F b_sol (fun s x i => α s * perpF φ x i) p -
      flatIntegrand ν μ (fun _ _ _ => 0) F b₀ (fun s x i => α s * perpF φ x i) p =
    ((deriv α p.1 : ℝ) : ℂ) * (-hInt (wF b₀ b_sol) φ p) +
      ((α p.1 : ℝ) : ℂ) * ((μ / (p.1 : ℂ)) * hInt (wF b₀ b_sol) φ p -
        jInt tr b_sol (wF b₀ b_sol) φ p) := by
  have hΨ := perpF_isFlatSpatialTest hφ
  have hD : ∀ (s : ℝ) (x : ℝ × ℝ) (i : Fin 2),
      flatDt (fun s x i => α s * perpF φ x i) s x i = deriv α s * perpF φ x i := by
    intro s x i
    unfold flatDt
    exact deriv_mul_const_field _
  have hL : ∀ (s : ℝ) (x : ℝ × ℝ) (i : Fin 2),
      flatLap (fun s x i => α s * perpF φ x i) s x i = α s * lapP (fun y => perpF φ y i) x := by
    intro s x i
    unfold flatLap
    exact lapP_const_mul (isCylTest_component hΨ i) (α s) x
  have hG : ∀ (s : ℝ) (x : ℝ × ℝ) (i j : Fin 2),
      flatGrad (fun s x i => α s * perpF φ x i) s x i j =
        α s * B0579.pd j (fun y => perpF φ y i) x := by
    intro s x i j
    simp only [flatGrad]
    rw [pd_const_mul_fun (isCylTest_component hΨ i).differentiable j (α s)]
  simp only [flatIntegrand, hD, hL, hG, Fin.sum_univ_two, hInt, jInt, wF]
  push_cast
  ring

section TimeWeak

variable {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
  {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}

/-- **The weak time equation** `∫ θ' H = -∫ θ J` for `θ ∈ C^∞_c(0, T)`. -/
theorem timeWeak (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hfree : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b₀ G₀)
    (hsol : IsCausalEnergySolution c ν μ (trainVel tr) F b_sol G_sol) (hμ0 : μ ≠ 0)
    (hμre : -5 / 4 < μ.re) {T : ℝ} (hT : 0 < T) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθs : HasCompactSupport θ) (hθt : tsupport θ ⊆ Ioo 0 T) :
    ∫ t, deriv θ t • Hf c μ (wF b₀ b_sol) φ t = -∫ t, θ t • Jf c μ tr b_sol (wF b₀ b_sol) φ t := by
  set w := wF b₀ b_sol with hw
  set S : Set (ℝ × (ℝ × ℝ)) := Ioi (0 : ℝ) ×ˢ B0579.cell c with hS
  have hSm : MeasurableSet S := measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hts0 : tsupport θ ⊆ Ioi 0 := hθt.trans (fun t ht => ht.1)
  have hΨ := perpF_isFlatSpatialTest hφ
  set E : (ℂ →L[ℝ] ℝ) → ℝ × (ℝ × ℝ) → ℂ := fun F' p =>
    ((deriv (fun t : ℝ => F' ((t : ℂ) ^ μ * (θ t : ℂ))) p.1 : ℝ) : ℂ) * (-hInt w φ p) +
      ((F' ((p.1 : ℂ) ^ μ * (θ p.1 : ℂ)) : ℝ) : ℂ) *
        ((μ / (p.1 : ℂ)) * hInt w φ p - jInt tr b_sol w φ p) with hE
  have key : ∀ F' : ℂ →L[ℝ] ℝ, IntegrableOn (E F') S ∧ ∫ p in S, E F' p = 0 := by
    intro F'
    set α : ℝ → ℝ := fun t => F' ((t : ℂ) ^ μ * (θ t : ℂ)) with hα_def
    have hα : ContDiff ℝ ∞ α := F'.contDiff.comp (weight_contDiff hθ hts0 μ)
    have hαs : HasCompactSupport α := weight_hasCompactSupport hθs μ F'
    have hαt : tsupport α ⊆ Ioi 0 := (weight_tsupport_subset θ μ F').trans hts0
    have hΦ := isFlatTest_mul_spatial hα hαs hαt hΨ
    have h1 := hsol.integrable _ hΦ
    have h2 := hfree.integrable _ hΦ
    have hpt : ∀ p, flatIntegrand ν μ (trainVel tr) F b_sol (fun s x i => α s * perpF φ x i) p -
        flatIntegrand ν μ (fun _ _ _ => 0) F b₀ (fun s x i => α s * perpF φ x i) p = E F' p :=
      fun p => flat_diff tr μ F b₀ b_sol hφ α p
    refine ⟨IntegrableOn.congr_fun (h1.sub h2) (fun p _ => hpt p) hSm, ?_⟩
    rw [← setIntegral_congr_fun hSm (fun p _ => hpt p), integral_sub h1 h2, hsol.weak _ hΦ,
      hfree.weak _ hΦ, sub_zero]
  obtain ⟨hre_i, hre⟩ := key Complex.reCLM
  obtain ⟨him_i, him⟩ := key Complex.imCLM
  set f₁ : ℝ × (ℝ × ℝ) → ℂ := fun p => ((deriv θ p.1 : ℝ) : ℂ) * ((p.1 : ℂ) ^ μ * hInt w φ p)
    with hf₁_def
  set f₂ : ℝ × (ℝ × ℝ) → ℂ := fun p => ((θ p.1 : ℝ) : ℂ) * ((p.1 : ℂ) ^ μ * jInt tr b_sol w φ p)
    with hf₂_def
  have reim : ∀ z : ℂ, (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := fun z => by
    rw [mul_comm]; exact Complex.re_add_im z
  have hcomb : ∀ p ∈ S, E Complex.reCLM p + Complex.I * E Complex.imCLM p = -f₁ p - f₂ p := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    simp only [hE, hf₁_def, hf₂_def]
    rw [(weight_part_hasDerivAt hθ hμ0 hp1 Complex.reCLM).deriv,
      (weight_part_hasDerivAt hθ hμ0 hp1 Complex.imCLM).deriv]
    simp only [Complex.reCLM_apply, Complex.imCLM_apply]
    set D : ℂ := μ / (p.1 : ℂ) * (p.1 : ℂ) ^ μ * (θ p.1 : ℂ) + (p.1 : ℂ) ^ μ * ((deriv θ p.1 : ℝ) : ℂ)
    set W : ℂ := (p.1 : ℂ) ^ μ * (θ p.1 : ℂ)
    set h := hInt w φ p
    set j := jInt tr b_sol w φ p
    calc (D.re : ℂ) * -h + (W.re : ℂ) * (μ / (p.1 : ℂ) * h - j) +
          Complex.I * ((D.im : ℂ) * -h + (W.im : ℂ) * (μ / (p.1 : ℂ) * h - j))
        = ((D.re : ℂ) + Complex.I * (D.im : ℂ)) * -h +
            ((W.re : ℂ) + Complex.I * (W.im : ℂ)) * (μ / (p.1 : ℂ) * h - j) := by ring
      _ = D * -h + W * (μ / (p.1 : ℂ) * h - j) := by rw [reim, reim]
      _ = _ := by simp only [D, W]; ring
  have hzero : ∫ p in S, (-f₁ p - f₂ p) = 0 := by
    rw [← setIntegral_congr_fun hSm hcomb, integral_add hre_i (him_i.const_mul _),
      integral_const_mul, hre, him, mul_zero, add_zero]
  -- integrability of the two pieces on `S`
  obtain ⟨C₁, hC₁⟩ := (hθ.continuous_deriv (by simp)).bounded_above_of_compact_support hθs.deriv
  obtain ⟨C₂, hC₂⟩ := hθ.continuous.bounded_above_of_compact_support hθs
  have hS' : ∀ p ∈ S \ (Ioo 0 T ×ˢ B0579.cell c), p.1 ∉ tsupport θ := by
    intro p hp h
    exact hp.2 ⟨hθt h, hp.1.2⟩
  have hf₁ : IntegrableOn f₁ S := by
    have hj := joint_hInt hc hfree hsol hμre T hφ
    have h1 : IntegrableOn f₁ (Ioo 0 T ×ˢ B0579.cell c) := by
      refine Integrable.bdd_mul (c := C₁) hj ?_ (Eventually.of_forall fun p => ?_)
      · exact (Complex.measurable_ofReal.comp
          ((measurable_deriv θ).comp measurable_fst)).aestronglyMeasurable
      · rw [Complex.norm_real]; exact hC₁ p.1
    refine h1.of_forall_sdiff_eq_zero hSm (fun p hp => ?_)
    simp [hf₁_def, deriv_of_notMem_tsupport (hS' p hp)]
  have hf₂ : IntegrableOn f₂ S := by
    have hj := joint_jInt hc tr hbuc hfree hsol hμre hT.le hφ
    have h1 : IntegrableOn f₂ (Ioo 0 T ×ˢ B0579.cell c) := by
      refine Integrable.bdd_mul (c := C₂) hj ?_ (Eventually.of_forall fun p => ?_)
      · exact (Complex.measurable_ofReal.comp
          (hθ.continuous.measurable.comp measurable_fst)).aestronglyMeasurable
      · rw [Complex.norm_real]; exact hC₂ p.1
    refine h1.of_forall_sdiff_eq_zero hSm (fun p hp => ?_)
    simp [hf₂_def, image_eq_zero_of_notMem_tsupport (hS' p hp)]
  have hsplit : ∫ p in S, (-f₁ p - f₂ p) = -(∫ p in S, f₁ p) - ∫ p in S, f₂ p := by
    have := integral_sub hf₁.neg hf₂
    simp only [Pi.neg_apply, integral_neg] at this
    exact this
  -- Fubini
  have hF1 : ∫ p in S, f₁ p = ∫ t in Ioi 0, ((deriv θ t : ℝ) : ℂ) * Hf c μ w φ t := by
    have e := setIntegral_prod f₁ (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ))) hf₁
    rw [← Measure.volume_eq_prod] at e
    rw [hS, e]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [hf₁_def, Hf]
    rw [integral_const_mul, integral_const_mul]
  have hF2 : ∫ p in S, f₂ p = ∫ t in Ioi 0, ((θ t : ℝ) : ℂ) * Jf c μ tr b_sol w φ t := by
    have e := setIntegral_prod f₂ (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ))) hf₂
    rw [← Measure.volume_eq_prod] at e
    rw [hS, e]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [hf₂_def, Jf]
    rw [integral_const_mul, integral_const_mul]
  have hW1 : ∫ t, deriv θ t • Hf c μ w φ t = ∫ t in Ioi 0, ((deriv θ t : ℝ) : ℂ) * Hf c μ w φ t := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)]
    · simp only [Complex.real_smul]
    · have : t ∉ tsupport θ := fun h => ht (hts0 h)
      simp [deriv_of_notMem_tsupport this]
  have hW2 : ∫ t, θ t • Jf c μ tr b_sol w φ t = ∫ t in Ioi 0, ((θ t : ℝ) : ℂ) * Jf c μ tr b_sol w φ t := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)]
    · simp only [Complex.real_smul]
    · have : t ∉ tsupport θ := fun h => ht (hts0 h)
      simp [image_eq_zero_of_notMem_tsupport this]
  rw [hW1, hW2, ← hF1, ← hF2]
  have := hsplit.symm.trans hzero
  linear_combination -this

/-- `H` has weak time derivative `J` on `(0, T)`. -/
theorem hasWeakDeriv (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hfree : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b₀ G₀)
    (hsol : IsCausalEnergySolution c ν μ (trainVel tr) F b_sol G_sol) (hμ0 : μ ≠ 0)
    (hμre : -5 / 4 < μ.re) {T : ℝ} (hT : 0 < T) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    UnforcedLeray.BochnerTime.HasWeakDerivTime 0 T (Hf c μ (wF b₀ b_sol) φ)
      (Jf c μ tr b_sol (wF b₀ b_sol) φ) :=
  ⟨Hf_int hc hfree hsol hμre T hφ, Jf_int hc tr hbuc hfree hsol hμre hT.le hφ,
    fun θ hθ hθs hθt => timeWeak hc tr hbuc hfree hsol hμ0 hμre hT hφ hθ hθs hθt⟩

end TimeWeak

end UnforcedLeray.Short.IIIa.V1

end
