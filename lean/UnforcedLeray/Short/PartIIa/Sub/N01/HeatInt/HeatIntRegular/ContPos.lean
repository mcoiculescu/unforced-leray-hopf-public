import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.PlaneHeatCont
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatSliceBounds
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_3

/-!
# `PartII-a:N01/9/1/2/4/3` (helper): continuity of the heat integral on `s > 0`

Substitute `σ = s t` in `smoothHeatInt`: for `s > 0`,
`smoothHeatInt (s,y) = s • ∫₀¹ t^μ • planeHeat (ν s (1-t)) (heatSlice (s t)) y dt`.
The slice `heatSlice c F σ = σ⁻¹ • F(σ,·)` is jointly continuous, bounded and vanishes for
`σ < s₁`; dominated convergence in `t` (on `s` near `s₀`, the integrand vanishes unless
`t > s₁ / (2 s₀)`) gives continuity of the parametric integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

/-- A map into `MeridC` with continuous components is continuous. -/
theorem hcp_continuous_meridC {X : Type*} [TopologicalSpace X]
    (h : X → UnforcedLeray.B0223.MeridC) (hj : ∀ j : Fin 2, Continuous fun x => h x j) :
    Continuous h := by
  have e : h = fun x => (WithLp.toLp 2 (fun j : Fin 2 => h x j) : UnforcedLeray.B0223.MeridC) := by
    funext x
    rfl
  rw [e]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp (continuous_pi hj)

/-- Two component bounds give a norm bound on `MeridC`. -/
theorem hcp_norm_le_two {v : UnforcedLeray.B0223.MeridC} {K : ℝ} (h0 : ‖v 0‖ ≤ K)
    (h1 : ‖v 1‖ ≤ K) : ‖v‖ ≤ 2 * K := by
  have hK : 0 ≤ K := (norm_nonneg _).trans h0
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  nlinarith [norm_nonneg (v 0), norm_nonneg (v 1)]

/-- The planar heat of a function bounded by `K` is bounded by `K`. -/
theorem hcp_planeHeat_norm_le (u : ℝ × ℝ → UnforcedLeray.B0223.MeridC) (K : ℝ)
    (hu : ∀ y, ‖u y‖ ≤ K) (θ : ℝ) (x : ℝ × ℝ) :
    ‖UnforcedLeray.B0224.planeHeat θ u x‖ ≤ K := by
  rw [planeHeat_eq_dilate]
  have hint : MeasureTheory.Integrable (fun z : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 1 z * K) :=
    (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) one_pos).mul_const K
  refine (MeasureTheory.norm_integral_le_of_norm_le hint (ae_of_all _ fun z => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg one_pos z)]
    exact mul_le_mul_of_nonneg_left (hu _) (UnforcedLeray.Gaussian.gaussKernel_nonneg one_pos z)
  · rw [integral_mul_const, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) one_pos, one_mul]

/-- Joint continuity of the planar heat in `(θ, σ, x)` when the profile `G σ` is jointly
continuous and uniformly bounded. -/
theorem hcp_planeHeat_cont (G : ℝ → ℝ × ℝ → UnforcedLeray.B0223.MeridC)
    (hG : Continuous (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2)) (K : ℝ)
    (hK : ∀ σ w, ‖G σ w‖ ≤ K) :
    Continuous (fun q : ℝ × ℝ × (ℝ × ℝ) =>
      UnforcedLeray.B0224.planeHeat q.1 (G q.2.1) q.2.2) := by
  have hK' : (fun q : ℝ × ℝ × (ℝ × ℝ) => UnforcedLeray.B0224.planeHeat q.1 (G q.2.1) q.2.2) =
      fun q => ∫ z : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 1 z •
        G q.2.1 (q.2.2 - UnforcedLeray.B0224.planeι (Real.sqrt (max q.1 0) • z)) :=
    funext fun q => planeHeat_eq_dilate (G q.2.1) q.1 q.2.2
  rw [hK']
  have hG1 : Continuous (UnforcedLeray.Gaussian.gaussKernel 2 1) :=
    UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1
  have hG1nn : ∀ z : UnforcedLeray.Gaussian.Euc 2, 0 ≤ UnforcedLeray.Gaussian.gaussKernel 2 1 z :=
    fun z => UnforcedLeray.Gaussian.gaussKernel_nonneg one_pos z
  have hσ : Continuous fun q : ℝ × ℝ × (ℝ × ℝ) => q.2.1 := continuous_fst.comp continuous_snd
  have hx : Continuous fun q : ℝ × ℝ × (ℝ × ℝ) => q.2.2 := continuous_snd.comp continuous_snd
  have hsq : ∀ z : UnforcedLeray.Gaussian.Euc 2, Continuous fun q : ℝ × ℝ × (ℝ × ℝ) =>
      q.2.2 - UnforcedLeray.B0224.planeι (Real.sqrt (max q.1 0) • z) := fun z =>
    hx.sub (UnforcedLeray.B0224.continuous_planeι.comp
      ((Real.continuous_sqrt.comp (continuous_fst.max continuous_const)).smul continuous_const))
  refine MeasureTheory.continuous_of_dominated
    (bound := fun z => UnforcedLeray.Gaussian.gaussKernel 2 1 z * K) (fun q => ?_)
    (fun q => ae_of_all _ fun z => ?_)
    ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) one_pos).mul_const K)
    (ae_of_all _ fun z => ?_)
  · have hGw : Continuous (G q.2.1) := hG.comp (continuous_const.prodMk continuous_id)
    have hw : Continuous fun z : UnforcedLeray.Gaussian.Euc 2 =>
        q.2.2 - UnforcedLeray.B0224.planeι (Real.sqrt (max q.1 0) • z) :=
      continuous_const.sub (UnforcedLeray.B0224.continuous_planeι.comp
        (continuous_id.const_smul (Real.sqrt (max q.1 0))))
    have hz : Continuous fun z : UnforcedLeray.Gaussian.Euc 2 =>
        G q.2.1 (q.2.2 - UnforcedLeray.B0224.planeι (Real.sqrt (max q.1 0) • z)) :=
      hGw.comp hw
    exact ((hG1.smul hz)).aestronglyMeasurable
  · rw [norm_smul, Real.norm_of_nonneg (hG1nn z)]
    exact mul_le_mul_of_nonneg_left (hK _ _) (hG1nn z)
  · exact Continuous.smul (continuous_const (y := UnforcedLeray.Gaussian.gaussKernel 2 1 z))
      (hG.comp (hσ.prodMk (hsq z)))

/-- The integrand after substitution `σ = s t`, times `1`: `Φ(p,t)`. -/
def hcpPhi (c ν : ℝ) (μ : ℂ) (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (p : ℝ × (ℝ × ℝ)) (t : ℝ) : UnforcedLeray.B0223.MeridC :=
  (((t : ℝ) : ℂ) ^ μ) • UnforcedLeray.B0224.planeHeat (ν * (p.1 - p.1 * t))
    (fun z => heatSlice c F (p.1 * t) z) p.2

/-- `t`-continuity of the planar heat part of `hcpPhi`. -/
theorem hcp_Q_cont_t (c ν : ℝ) (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (K : ℝ) (hb : ∀ σ w, ‖heatSlice c F σ w‖ ≤ K)
    (hGc : Continuous (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2))
    (p : ℝ × (ℝ × ℝ)) :
    Continuous fun t : ℝ => UnforcedLeray.B0224.planeHeat (ν * (p.1 - p.1 * t))
      (fun z => heatSlice c F (p.1 * t) z) p.2 := by
  have hP := hcp_planeHeat_cont (fun σ w => heatSlice c F σ w) hGc K hb
  have hmap : Continuous fun t : ℝ => ((ν * (p.1 - p.1 * t), p.1 * t, p.2) : ℝ × ℝ × (ℝ × ℝ)) :=
    Continuous.prodMk (continuous_const.mul (continuous_const.sub
      (continuous_const.mul continuous_id)))
      (Continuous.prodMk (continuous_const.mul continuous_id) continuous_const)
  exact hP.comp hmap

/-- `p`-continuity of the planar heat part of `hcpPhi`, for fixed `t`. -/
theorem hcp_Q_cont_p (c ν : ℝ) (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (K : ℝ) (hb : ∀ σ w, ‖heatSlice c F σ w‖ ≤ K)
    (hGc : Continuous (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2)) (t : ℝ) :
    Continuous fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0224.planeHeat (ν * (p.1 - p.1 * t))
      (fun z => heatSlice c F (p.1 * t) z) p.2 := by
  have hP := hcp_planeHeat_cont (fun σ w => heatSlice c F σ w) hGc K hb
  have hmap : Continuous fun p : ℝ × (ℝ × ℝ) =>
      ((ν * (p.1 - p.1 * t), p.1 * t, p.2) : ℝ × ℝ × (ℝ × ℝ)) :=
    Continuous.prodMk (continuous_const.mul (continuous_fst.sub (continuous_fst.mul continuous_const)))
      (Continuous.prodMk (continuous_fst.mul continuous_const) continuous_snd)
  exact hP.comp hmap

theorem hcp_Phi_contOn_t (c ν : ℝ) (μ : ℂ) (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (K : ℝ) (hb : ∀ σ w, ‖heatSlice c F σ w‖ ≤ K)
    (hGc : Continuous (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2))
    (p : ℝ × (ℝ × ℝ)) : ContinuousOn (fun t => hcpPhi c ν μ F p t) (Ioi 0) := by
  have h1 : ContinuousOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ μ) (Ioi 0) := fun t ht =>
    (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 (Set.mem_Ioi.1 ht))).continuousWithinAt
  exact h1.smul (hcp_Q_cont_t c ν F K hb hGc p).continuousOn

theorem hcp_Phi_contAt_p (c ν : ℝ) (μ : ℂ) (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (K : ℝ) (hb : ∀ σ w, ‖heatSlice c F σ w‖ ≤ K)
    (hGc : Continuous (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2)) (t : ℝ)
    (p₀ : ℝ × (ℝ × ℝ)) : ContinuousAt (fun p => hcpPhi c ν μ F p t) p₀ :=
  (Continuous.smul (continuous_const (y := (((t : ℝ) : ℂ)) ^ μ))
    (hcp_Q_cont_p c ν F K hb hGc t)).continuousAt

/-- Pointwise bound for `hcpPhi` when `0 < p.1 < 2 s₀`. -/
theorem hcp_Phi_norm_le (c ν : ℝ) (μ : ℂ) (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (s₁ K : ℝ) (hs₁ : 0 < s₁) (hK : 0 ≤ K)
    (hb : ∀ σ w, ‖heatSlice c F σ w‖ ≤ K) (hz : ∀ σ, σ < s₁ → ∀ w, heatSlice c F σ w = 0)
    (s₀ : ℝ) (hs₀ : 0 < s₀) (p : ℝ × (ℝ × ℝ)) (hp0 : 0 < p.1) (hp1 : p.1 < 2 * s₀)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖hcpPhi c ν μ F p t‖ ≤ (1 + (s₁ / (2 * s₀)) ^ μ.re) * K := by
  have hδ : 0 < s₁ / (2 * s₀) := div_pos hs₁ (by linarith)
  have hnn : 0 ≤ (s₁ / (2 * s₀)) ^ μ.re := Real.rpow_nonneg hδ.le _
  unfold hcpPhi
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  by_cases hc : p.1 * t < s₁
  · have hfun : (fun z => heatSlice c F (p.1 * t) z) = fun _ => (0 : UnforcedLeray.B0223.MeridC) :=
      funext fun z => hz _ hc z
    have h0 : UnforcedLeray.B0224.planeHeat (ν * (p.1 - p.1 * t))
        (fun z => heatSlice c F (p.1 * t) z) p.2 = 0 := by
      rw [hfun]
      simp [UnforcedLeray.B0225.planeHeat_zero]
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg (by linarith) hK
  · push_neg at hc
    have h2 : p.1 * t < 2 * s₀ * t := mul_lt_mul_of_pos_right hp1 ht0
    have hlt : s₁ < t * (2 * s₀) := by linarith [mul_comm t (2 * s₀)]
    have hδt : s₁ / (2 * s₀) < t := by
      rw [div_lt_iff₀ (by linarith)]
      exact hlt
    have hpow : t ^ μ.re ≤ 1 + (s₁ / (2 * s₀)) ^ μ.re := by
      rcases le_total 0 μ.re with h | h
      · have := Real.rpow_le_one ht0.le ht1 h
        linarith
      · have := Real.rpow_le_rpow_of_nonpos hδ hδt.le h
        linarith
    have hn := hcp_planeHeat_norm_le (fun z => heatSlice c F (p.1 * t) z) K
      (fun y => hb _ y) (ν * (p.1 - p.1 * t)) p.2
    exact mul_le_mul hpow hn (norm_nonneg _) (by linarith)

/-- Key identity: the substituted form of `smoothHeatInt` for `s > 0`. -/
theorem hcp_smooth_eq (c ν : ℝ) (μ : ℂ)
    (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (p : ℝ × (ℝ × ℝ)) (hp : 0 < p.1) :
    UnforcedLeray.Short.PartIIa.N01.smoothHeatInt c ν μ F p
      = p.1 • ∫ t in (0 : ℝ)..1, hcpPhi c ν μ F p t := by
  have hs0 : p.1 ≠ 0 := hp.ne'
  have e1 : UnforcedLeray.Short.PartIIa.N01.smoothHeatInt c ν μ F p = ∫ σ in (0 : ℝ)..p.1,
      (((σ / p.1 : ℝ) : ℂ) ^ μ • UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
        (fun z => heatSlice c F σ z) p.2) := rfl
  have e2 := intervalIntegral.integral_comp_mul_left
    (f := fun σ : ℝ => (((σ / p.1 : ℝ) : ℂ) ^ μ • UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
        (fun z => heatSlice c F σ z) p.2)) (a := 0) (b := 1) hs0
  simp only [mul_zero, mul_one] at e2
  have e3 : ∫ t in (0 : ℝ)..1, (((p.1 * t / p.1 : ℝ) : ℂ) ^ μ •
      UnforcedLeray.B0224.planeHeat (ν * (p.1 - p.1 * t))
        (fun z => heatSlice c F (p.1 * t) z) p.2)
      = ∫ t in (0 : ℝ)..1, hcpPhi c ν μ F p t := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hcpPhi]
    rw [mul_div_cancel_left₀ t hs0]
  rw [e1, ← e3, e2, smul_smul, mul_inv_cancel₀ hs0, one_smul]

/-- Continuity of the parametric integral at `p₀` with `p₀.1 > 0`. -/
theorem hcp_integral_contAt (c ν : ℝ) (μ : ℂ)
    (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (s₁ K : ℝ) (hs₁ : 0 < s₁) (hK : 0 ≤ K)
    (hb : ∀ σ w, ‖heatSlice c F σ w‖ ≤ K) (hz : ∀ σ, σ < s₁ → ∀ w, heatSlice c F σ w = 0)
    (hGc : Continuous (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2))
    (p₀ : ℝ × (ℝ × ℝ)) (hp₀ : 0 < p₀.1) :
    ContinuousAt (fun p => ∫ t in (0 : ℝ)..1, hcpPhi c ν μ F p t) p₀ := by
  have hev1 : ∀ᶠ p in 𝓝 p₀, p.1 < 2 * p₀.1 :=
    (continuous_fst.tendsto p₀).eventually (Iio_mem_nhds (by linarith))
  have hev2 : ∀ᶠ p in 𝓝 p₀, 0 < p.1 :=
    (continuous_fst.tendsto p₀).eventually (lt_mem_nhds hp₀)
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => (1 + (s₁ / (2 * p₀.1)) ^ μ.re) * K) ?_ ?_ intervalIntegrable_const ?_
  · refine Filter.Eventually.of_forall fun p => ?_
    have hsub : Set.uIoc (0 : ℝ) 1 ⊆ Ioi 0 := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact ht.1
    exact ((hcp_Phi_contOn_t c ν μ F K hb hGc p).mono hsub).aestronglyMeasurable
      measurableSet_uIoc
  · filter_upwards [hev1, hev2] with p hp1 hp0
    refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact hcp_Phi_norm_le c ν μ F s₁ K hs₁ hK hb hz p₀.1 hp₀ p hp0 hp1 t ht.1 ht.2
  · refine ae_of_all _ fun t ht => ?_
    exact (hcp_Phi_contAt_p c ν μ F K hb hGc t p₀)

theorem heatIntContPos : UnforcedLeray.Short.PartIIa.N01.HeatIntContPos := by
  intro c ν hc hν μ F hF
  obtain ⟨⟨s₁, hs₁, hzero⟩, hCj, K, hKv, _⟩ := heatSliceBounds c hc F hF
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hKv 0 0 (0, 0))
  have hb : ∀ σ w, ‖heatSlice c F σ w‖ ≤ 2 * K := fun σ w =>
    hcp_norm_le_two (hKv 0 σ w) (hKv 1 σ w)
  have hGc : Continuous (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2) :=
    hcp_continuous_meridC (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2)
      (fun j => (hCj j).continuous)
  intro p hp
  have hp0 : (0 : ℝ) < p.1 := hp.1
  apply ContinuousAt.continuousWithinAt
  have hA := hcp_integral_contAt c ν μ F s₁ (2 * K) hs₁ (by linarith) hb hzero hGc p hp0
  have hB : ContinuousAt (fun q : ℝ × (ℝ × ℝ) => q.1 • ∫ t in (0 : ℝ)..1, hcpPhi c ν μ F q t) p :=
    continuous_fst.continuousAt.smul hA
  refine hB.congr ?_
  have hev : ∀ᶠ q in 𝓝 p, 0 < q.1 := (continuous_fst.tendsto p).eventually (lt_mem_nhds hp0)
  filter_upwards [hev] with q hq
  exact (hcp_smooth_eq c ν μ F q hq).symm

end UnforcedLeray.Short.PartIIa.N01
