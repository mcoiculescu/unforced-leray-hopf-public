import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4b.Param
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4b.Gap

/-!
# `WardX0FarAllOrder` (helper of `B4b`, source 3604-3621, 4177-4179)

For smooth old data with `T = oldPhys R c g`, every `(τ, y)`-derivative of the component
`(wardX0)_z` is `O(ϱ(y)^{-4})` for `ϱ(y) ≥ 4 rOut + 2`, uniformly in `τ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

set_option maxHeartbeats 1000000 in
theorem sepWFarIter (ν : ℝ) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hν : 0 < ν) (hμ : -(1 / 4) < μ.re)
    (hr : 0 ≤ rOut) (hP : 0 < P) (hS : IIIa.IsSepSource P rOut T)
    (hT : ∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => T x.1 x.2 j k))
    (Z : ℝ) (hZ : ∀ τ z, Z < ‖z‖ → T τ z = 0) (i : Fin 3) (n : ℕ) :
    ∃ C : ℝ, ∀ x0 : ℝ × Space, 4 * rOut + 2 ≤ ϱ x0.2 →
      ‖iteratedFDeriv ℝ n (fun x : ℝ × Space => IIIa.sepW ν μ T x.2 x.1 i) x0‖ ≤
        C * (ϱ x0.2 ^ 4)⁻¹ := by
  choose C hC0 hCb using fun k : ℕ => sepGapDecayTop IIIa.sepKernelBounds ν μ rOut P T hν hP hS hT
    Z hZ i k
  have ha : (-1 : ℝ) < 2 * μ.re + 2 := by linarith
  have hmaj := sepTopMajorant_integrable (2 * μ.re + 2) Z ha
  refine ⟨16 * (C n * ∫ p, (p.1 ^ (2 * μ.re + 2) * (if ‖p.2‖ ≤ Z then (1 : ℝ) else 0)) ∂sepRho),
    fun x0 hx0 => ?_⟩
  set ρ0 : ℝ := ϱ x0.2 with hρ0def
  have hρ2 : 2 ≤ ρ0 := by linarith
  set ρ' : ℝ := ρ0 / 2 with hρ'def
  have hρ'1 : 1 ≤ ρ' := by rw [hρ'def]; linarith
  have hρ'r : 2 * rOut ≤ ρ' := by rw [hρ'def]; linarith
  set U : Set (ℝ × Space) := Metric.ball x0 ρ' with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball
  have hxU : ∀ x ∈ U, ρ' ≤ ϱ x.2 := by
    intro x hx
    have hd : dist x x0 < ρ' := Metric.mem_ball.mp hx
    rw [dist_eq_norm] at hd
    have hsnd : ‖x.2 - x0.2‖ ≤ ‖x - x0‖ := by
      rw [← Prod.snd_sub]; exact norm_snd_le _
    have h1 := gapRho_sub_le x0.2 x.2
    have h2 := gapRho_le_norm (x0.2 - x.2)
    rw [norm_sub_rev] at h2
    linarith
  set g : ℕ → ℝ × Space → ℝ := fun k p =>
    C k * (p.1 ^ (2 * μ.re + 2) * (if ‖p.2‖ ≤ Z then (1 : ℝ) else 0)) * (ρ' ^ 4)⁻¹ with hgdef
  have hint : ∀ k, Integrable (g k) sepRho := fun k =>
    (hmaj.const_mul (C k)).mul_const ((ρ' ^ 4)⁻¹)
  have hbound : ∀ k, ∀ᵐ p ∂sepRho, ∀ x ∈ U, ‖iteratedFDeriv ℝ k (sepPhiJ ν μ T i p) x‖ ≤ g k p := by
    intro k
    filter_upwards [ae_mem_Ioo_sepRho] with p hp x hx
    exact (hCb k) ρ' hρ'1 hρ'r x (hxU x hx) p.1 hp p.2
  have hF : ∀ᵐ p ∂sepRho, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sepPhiJ ν μ T i p) U := by
    filter_upwards [ae_mem_Ioo_sepRho] with p hp
    exact (sepPhiJ_contDiff heatLerayKSmoothTop ν μ T i p.1 p.2 hν hp hT).contDiffOn
  have hmeas : ∀ k, ∀ x ∈ U, AEStronglyMeasurable (fun p => iteratedFDeriv ℝ k (sepPhiJ ν μ T i p) x)
      sepRho := fun k x _ => sepPhiMeasurableTop ν μ P rOut T hν hS hT i k x
  have hmain := paramIterBound n sepRho (sepPhiJ ν μ T i) U g hUo hF hint hbound hmeas x0
    (Metric.mem_ball_self (by linarith))
  -- identify `sepW` with the integral on `U`
  have hEq : (fun x : ℝ × Space => IIIa.sepW ν μ T x.2 x.1 i) =ᶠ[𝓝 x0]
      (fun y => ∫ p, sepPhiJ ν μ T i p y ∂sepRho) := by
    filter_upwards [hUo.mem_nhds (Metric.mem_ball_self (by linarith : (0:ℝ) < ρ'))] with x hx
    apply sepW_eq_integral
    have hm : AEStronglyMeasurable (fun p => sepPhiJ ν μ T i p x) sepRho := by
      have := (continuousMultilinearCurryFin0 ℝ (ℝ × Space) ℂ).continuous.comp_aestronglyMeasurable
        (sepPhiMeasurableTop ν μ P rOut T hν hS hT i 0 x)
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp [iteratedFDeriv_zero_eq_comp]
    refine Integrable.mono' (hint 0) hm ?_
    filter_upwards [hbound 0] with p hp
    have := hp x hx
    simpa [norm_iteratedFDeriv_zero, sepPhiJ] using this
  rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds]
  refine hmain.trans (le_of_eq ?_)
  simp only [hgdef]
  rw [integral_mul_const, integral_const_mul, hρ'def, div_pow]
  have h4 : (ρ0 ^ 4 / 2 ^ 4)⁻¹ = 16 * (ρ0 ^ 4)⁻¹ := by
    rw [inv_div]; field_simp; norm_num
  rw [h4]
  ring

set_option maxHeartbeats 1000000 in
theorem wardX0FarIter (ν μ R c : ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4) < μ) (hg : IsSmoothOld c ν g) (n : ℕ) :
    ∃ C : ℝ, ∀ x0 : ℝ × Space, 4 * (R * Real.sqrt (5 * ν / 6)) + 2 ≤ ϱ x0.2 →
      ‖iteratedFDeriv ℝ n (fun x : ℝ × Space => wardX0 ν μ R c g x.1 x.2 2) x0‖ ≤
        C * (ϱ x0.2 ^ 4)⁻¹ := by
  obtain ⟨hS1, hS2⟩ := smoothOldSource_proved ν R c g hν hR hc hg
  obtain ⟨hT, Z, hZ⟩ := oldPhysSmooth_proved ν R c g hν hR hc hg
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hμ0 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  obtain ⟨C0, h0⟩ := sepWFarIter ν (μ : ℂ) _ _ (oldPhys R c g) hν hμ0 hr hP hS1 hT Z hZ 2 n
  obtain ⟨C1, h1⟩ := sepWFarIter ν ((μ : ℂ) + 1) _ _ (oldPhys R c g) hν hμ1 hr hP hS1 hT Z hZ 2 n
  refine ⟨C0 + C1, fun x0 hx0 => ?_⟩
  have hopen : IsOpen {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hx0' : R * Real.sqrt (5 * ν / 6) < ϱ x0.2 := by linarith
  have hsm0 := sepWSmoothTop_proved ν (μ : ℂ) _ _ (oldPhys R c g) hν hμ0 hr hP hS1 hS2 hT ⟨Z, hZ⟩ 2
  have hsm1 := sepWSmoothTop_proved ν ((μ : ℂ) + 1) _ _ (oldPhys R c g) hν hμ1 hr hP hS1 hS2 hT
    ⟨Z, hZ⟩ 2
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) x.2 x.1 2) x0 :=
    hsm0.contDiffAt (hopen.mem_nhds hx0')
  have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) x.2 x.1 2) x0 :=
    hsm1.contDiffAt (hopen.mem_nhds hx0')
  have hn : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hfun : (fun x : ℝ × Space => wardX0 ν μ R c g x.1 x.2 2) =
      Complex.reCLM ∘ ((fun x : ℝ × Space => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) x.2 x.1 2) -
        (fun x : ℝ × Space => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) x.2 x.1 2)) := by
    funext x
    simp [wardX0]
  have hAB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun x : ℝ × Space => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) x.2 x.1 2) -
        (fun x : ℝ × Space => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) x.2 x.1 2)) x0 :=
    hA.sub hB
  rw [hfun]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hAB hn).trans ?_
  rw [Complex.reCLM_norm, one_mul, iteratedFDeriv_sub_apply (hA.of_le hn) (hB.of_le hn)]
  refine (norm_sub_le _ _).trans ?_
  have := h0 x0 hx0
  have := h1 x0 hx0
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
