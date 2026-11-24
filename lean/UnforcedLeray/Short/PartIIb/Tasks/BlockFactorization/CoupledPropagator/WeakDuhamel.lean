import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_2
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.WeakDuhamel.Grid
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.WeakDuhamel.LFree

/-!
# `PartII-b:F2/2/3`: Weak coupled cylinder vorticity equation for the mild Duhamel propagator

Source of record: `the November 2 reference manuscript` (SP), lines 2076–2083,
2147–2155 (`short-bg:coupled-prop`).

Proves `mildDuhamelWeakStep_proof : UnforcedLeray.Short.IIb.MildDuhamelWeakStep` by combining:
1. `WeakDuhamelLF.freeTestCLM` (`WeakDuhamel/LFree.lean`), realizing the tested free cylinder
   operator `w ↦ ∫_{cell c} cylFreeIntegrand p.train w r φ` as an operator-norm continuous family
   of continuous linear functionals on `[0, p.H]`;
2. `WeakDuhamelGrid.aesm_diag` and `WeakDuhamelGrid.aesm_tri` (`WeakDuhamel/Grid.lean`), giving
   1-variable and triangle 2-variable strong measurability from `hMild.duhamel_integrable` and
   right-hand strong continuity of `Sc`;
3. Fubini (`MeasureTheory.integral_integral_swap`) on `(Ioc s t) × (Ioc s t)` restricted to
   `{z | z.1 ≤ z.2}`, feeding `IsMildDuhamelPropagator.weak_of_fubini`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb.WeakDuhamelProof

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411 in
open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.PartIIbF22Aux in
private theorem aesm_cutoff_propagator
    {m K₀ M_A : ℝ} {p : Params}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ p.H)
    (hMild : IsMildDuhamelPropagator m p K₀ M_A Sc Ac U)
    (f : Xmc p.c m) (ψ : Xmc p.c m →L[ℝ] ℝ)
    {q : ℝ} (hq : q ∈ Icc s t) :
    AEStronglyMeasurable
      (fun τ => if τ ≤ q then ψ (Sc q τ (Ac τ (U τ s f))) else 0)
      (volume.restrict (Ioc s t)) := by
  have h_duh : IntegrableOn (fun τ => Sc q τ (Ac τ (U τ s f))) (Ioc s q) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hq.1).1
      (hMild.duhamel_integrable s q hs hq.1 (hq.2.trans ht) f)
  have h_comp : AEStronglyMeasurable
      (fun τ => ψ (Sc q τ (Ac τ (U τ s f)))) (volume.restrict (Ioc s q)) :=
    ψ.continuous.comp_aestronglyMeasurable h_duh.aestronglyMeasurable
  have h_ind : AEStronglyMeasurable
      ((Ioc s q).indicator (fun τ => ψ (Sc q τ (Ac τ (U τ s f))))) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioc).2 h_comp
  refine h_ind.restrict.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
  by_cases hτq : τ ≤ q
  · have hmem : τ ∈ Ioc s q := ⟨hτ.1, hτq⟩
    simp [hmem, hτq]
  · have hnmem : τ ∉ Ioc s q := fun h => hτq h.2
    simp [hnmem, hτq]

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411 in
open UnforcedLeray.Short.IIb in
private theorem norm_interaction_orbit_le
    {m K₀ M_A : ℝ} {p : Params}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hK₀ : 0 < K₀) (hMA : 0 ≤ M_A)
    (hAc_bd : ∀ r ∈ Icc 0 p.H, ‖Ac r‖ ≤ M_A)
    (hMild : IsMildDuhamelPropagator m p K₀ M_A Sc Ac U)
    {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ p.H) (f : Xmc p.c m)
    {τ : ℝ} (hτ : τ ∈ Icc s t) :
    ‖Ac τ (U τ s f)‖ ≤ M_A * (Real.exp ((K₀ + M_A) * p.H) * ‖f‖) := by
  have hτ_Icc : τ ∈ Icc 0 p.H := ⟨hs.trans hτ.1, hτ.2.trans ht⟩
  have hexp : Real.exp ((K₀ + M_A) * (τ - s)) ≤ Real.exp ((K₀ + M_A) * p.H) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (by linarith [hs, hτ.2, ht]) (by linarith)
  calc ‖Ac τ (U τ s f)‖
      ≤ ‖Ac τ‖ * ‖U τ s f‖ := (Ac τ).le_opNorm _
    _ ≤ M_A * (‖U τ s‖ * ‖f‖) :=
        mul_le_mul (hAc_bd τ hτ_Icc) ((U τ s).le_opNorm f) (norm_nonneg _) hMA
    _ ≤ M_A * (Real.exp ((K₀ + M_A) * (τ - s)) * ‖f‖) := by
        gcongr
        exact hMild.norm_le s τ hs hτ.1 hτ_Icc.2
    _ ≤ M_A * (Real.exp ((K₀ + M_A) * p.H) * ‖f‖) := by gcongr

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411 in
open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.PartIIbF22Aux in
private theorem mildDuhamelWeakStep_proof_aux : MildDuhamelWeakStep := by
  intro m hm Sig _hSig p d dm dp _hbg _hν1 _hAge δ _hδ0 _hδ1 _hTCM
    K₀ Sc hK₀ hSc hSc_bd M_A Ac hMA hAc U hMild φ hφ s t hs hst ht f
  have hm_half : 1 / 2 < m := by linarith
  have hAc_op : ∀ r ∈ Icc 0 p.H, IsCylInteractionOp p.train m r (Ac r) :=
    fun r hr => (hAc r hr).1
  have hAc_bd : ∀ r ∈ Icc 0 p.H, ‖Ac r‖ ≤ M_A :=
    fun r hr => (hAc r hr).2
  set g : ℝ → Xmc p.c m := fun τ => Ac τ (U τ s f)
  set B_g : ℝ := M_A * (Real.exp ((K₀ + M_A) * p.H) * ‖f‖)
  have hBg0 : 0 ≤ B_g := by dsimp [B_g]; positivity
  -- 1. Construct L_free with uniform operator-norm bound and continuity on [0, p.H]
  set L_free : ℝ → (Xmc p.c m →L[ℝ] ℝ) := WeakDuhamelLF.freeTestCLM p.train m hφ
  have hL_free : ∀ r ∈ Icc s t, ∀ w : Xmc p.c m,
      L_free r w = ∫ x in B0579.cell p.c, cylFreeIntegrand p.train w r φ x :=
    fun r hr w => WeakDuhamelLF.freeTestCLM_apply p.train m hφ (hs.trans hr.1) w
  obtain ⟨⟨C_L, hCL0, hCL_bd⟩, hL_cont⟩ :=
    WeakDuhamelLF.freeTestCLM_bound_and_continuousOn (H := p.H) hm_half p.train hφ
  -- 2. Prove hAc_ti via WeakDuhamelGrid.aesm_diag
  set ψ : Xmc p.c m →L[ℝ] ℝ := cellTestCLM p.c m hφ
  set H₁ : ℝ → ℝ → ℝ := fun q τ => if τ ≤ q then ψ (Sc q τ (g τ)) else 0
  have h_aesm_Ac : AEStronglyMeasurable (fun τ => ψ (g τ)) (volume.restrict (Ioc s t)) := by
    refine WeakDuhamelGrid.aesm_diag hs hst H₁ (fun τ => ψ (g τ))
      (fun q hq => aesm_cutoff_propagator hs ht hMild f ψ hq) ?_
    intro τ hτ
    have hτ_Icc : τ ∈ Icc 0 p.H := ⟨hs.trans hτ.1.le, hτ.2.trans ht⟩
    have hsc_cont : ContinuousWithinAt (fun q => Sc q τ (g τ)) (Icc τ t) τ :=
      (hSc.strongCont τ hτ_Icc (g τ) τ ⟨le_rfl, hτ_Icc.2⟩).mono (Icc_subset_Icc_right ht)
    have hψ_lim : Tendsto (fun q => ψ (Sc q τ (g τ))) (𝓝[Icc τ t] τ) (𝓝 (ψ (g τ))) := by
      have h := (ψ.continuous.continuousAt.comp_continuousWithinAt hsc_cont).tendsto
      rwa [Function.comp_apply, hSc.id_self τ hτ_Icc, ContinuousLinearMap.id_apply] at h
    refine hψ_lim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp [H₁, hq.1]
  have hAc_ti : IntervalIntegrable (fun r => ψ (g r)) volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    refine (integrableOn_const (C := ‖ψ‖ * B_g) (hs := measure_Ioc_lt_top.ne)).mono' h_aesm_Ac ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    calc ‖ψ (g τ)‖
        ≤ ‖ψ‖ * ‖g τ‖ := ψ.le_opNorm (g τ)
      _ ≤ ‖ψ‖ * B_g := mul_le_mul_of_nonneg_left
          (norm_interaction_orbit_le hK₀ hMA hAc_bd hMild hs ht f ⟨hτ.1.le, hτ.2⟩) (norm_nonneg _)
  -- 3. Prove joint integrability on the triangle {τ ≤ r} inside (Ioc s t) × (Ioc s t)
  set G : ℝ → ℝ → ℝ := fun τ r => L_free r (Sc r τ (g τ))
  set H₂ : ℝ → ℝ → ℝ := fun q τ => if τ ≤ q then L_free q (Sc q τ (g τ)) else 0
  set μ : Measure ℝ := volume.restrict (Ioc s t)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set T_tri : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.1 ≤ z.2}
  have hT_meas : MeasurableSet T_tri := measurableSet_le measurable_fst measurable_snd
  have h_aesm_tri : AEStronglyMeasurable (fun z : ℝ × ℝ => G z.1 z.2)
      ((μ.prod μ).restrict T_tri) := by
    refine WeakDuhamelGrid.aesm_tri hs hst H₂ G
      (fun q hq => aesm_cutoff_propagator hs ht hMild f (L_free q) hq) ?_
    intro τ hτ r hτr hrt
    have hτ_Icc : τ ∈ Icc 0 p.H := ⟨hs.trans hτ.1.le, hτ.2.trans ht⟩
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hτ_Icc.1.trans hτr, hrt.trans ht⟩
    have hL_at : ContinuousWithinAt L_free (Icc r t) r :=
      (hL_cont r hr_Icc).mono (Icc_subset_Icc hr_Icc.1 ht)
    have hSc_at : ContinuousWithinAt (fun q => Sc q τ (g τ)) (Icc r t) r :=
      (hSc.strongCont τ hτ_Icc (g τ) r ⟨hτr, hr_Icc.2⟩).mono (Icc_subset_Icc hτr ht)
    have h_app : Tendsto (fun q => L_free q (Sc q τ (g τ))) (𝓝[Icc r t] r) (𝓝 (G τ r)) :=
      (hL_at.clm_apply hSc_at).tendsto
    refine h_app.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp [H₂, hτr.trans hq.1]
  set F_sq : ℝ × ℝ → ℝ := T_tri.indicator (fun z => G z.1 z.2)
  have h_aesm_sq : AEStronglyMeasurable F_sq (μ.prod μ) :=
    (aestronglyMeasurable_indicator_iff hT_meas).2 h_aesm_tri
  set B_sq : ℝ := C_L * (Real.exp (K₀ * p.H) * B_g)
  have hBsq0 : 0 ≤ B_sq := by dsimp [B_sq]; positivity
  have hae1 : ∀ᵐ z ∂(μ.prod μ), z.1 ∈ Ioc s t :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (ae_restrict_mem measurableSet_Ioc)
  have hae2 : ∀ᵐ z ∂(μ.prod μ), z.2 ∈ Ioc s t :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (ae_restrict_mem measurableSet_Ioc)
  have hInt_sq : Integrable F_sq (μ.prod μ) := by
    refine (integrable_const B_sq).mono' h_aesm_sq ?_
    filter_upwards [hae1, hae2] with z hz1 hz2
    by_cases hle : z.1 ≤ z.2
    · have hz2_Icc : z.2 ∈ Icc 0 p.H := ⟨hs.trans hz2.1.le, hz2.2.trans ht⟩
      have hz1_0 : 0 ≤ z.1 := hs.trans hz1.1.le
      have hSc_le : ‖Sc z.2 z.1‖ ≤ Real.exp (K₀ * p.H) := by
        refine (hSc_bd z.1 z.2 hz1_0 hle hz2_Icc.2).trans ?_
        rw [Real.exp_le_exp]
        exact mul_le_mul_of_nonneg_left (by linarith [hz1_0, hz2_Icc.2]) hK₀.le
      have hg_le : ‖g z.1‖ ≤ B_g :=
        norm_interaction_orbit_le hK₀ hMA hAc_bd hMild hs ht f ⟨hz1.1.le, hz1.2⟩
      have hzT : z ∈ T_tri := hle
      rw [show F_sq z = G z.1 z.2 from indicator_of_mem hzT _]
      calc ‖G z.1 z.2‖
          ≤ ‖L_free z.2‖ * ‖Sc z.2 z.1 (g z.1)‖ := (L_free z.2).le_opNorm _
        _ ≤ C_L * (‖Sc z.2 z.1‖ * ‖g z.1‖) :=
            mul_le_mul (hCL_bd z.2 hz2_Icc) ((Sc z.2 z.1).le_opNorm _) (norm_nonneg _) hCL0
        _ ≤ C_L * (Real.exp (K₀ * p.H) * B_g) := by
            gcongr
    · have hzT : z ∉ T_tri := hle
      rw [show F_sq z = 0 from indicator_of_notMem hzT _, norm_zero]
      exact hBsq0
  -- 4. Slice identities and Fubini swap on (Ioc s t) × (Ioc s t)
  have h_slice_r : ∀ r ∈ Ioc s t, (∫ τ, F_sq (τ, r) ∂μ) = ∫ τ in s..r, G τ r := by
    intro r hr
    have hfun : (fun τ => F_sq (τ, r)) = (Iic r).indicator (fun τ => G τ r) := rfl
    have hset : Ioc s t ∩ Iic r = Ioc s r := by
      ext τ
      simp only [mem_inter_iff, mem_Ioc, mem_Iic]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hr.2⟩, h.2⟩⟩
    change ∫ τ in Ioc s t, F_sq (τ, r) = ∫ τ in s..r, G τ r
    rw [hfun, setIntegral_indicator measurableSet_Iic, hset,
      ← intervalIntegral.integral_of_le hr.1.le]
  have h_slice_τ : ∀ τ ∈ Ioc s t, (∫ r, F_sq (τ, r) ∂μ) = ∫ r in τ..t, G τ r := by
    intro τ hτ
    have hfun : (fun r => F_sq (τ, r)) = (Ici τ).indicator (fun r => G τ r) := rfl
    have hset : Ioc s t ∩ Ici τ = Icc τ t := by
      ext r
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hτ.1.trans_le h.1, h.2⟩, h.1⟩⟩
    change ∫ r in Ioc s t, F_sq (τ, r) = ∫ r in τ..t, G τ r
    rw [hfun, setIntegral_indicator measurableSet_Ici, hset,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ.2]
  have hFub_ti : IntervalIntegrable (fun r => ∫ τ in s..r, G τ r) volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    refine hInt_sq.integral_prod_right.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using h_slice_r r hr
  have hFub_eq : (∫ τ in s..t, ∫ r in τ..t, G τ r) =
      ∫ r in s..t, ∫ τ in s..r, G τ r := by
    have hswap : (∫ τ, ∫ r, F_sq (τ, r) ∂μ ∂μ) = ∫ r, ∫ τ, F_sq (τ, r) ∂μ ∂μ :=
      integral_integral_swap (f := fun τ r => F_sq (τ, r)) hInt_sq
    have hlhs : (∫ τ, ∫ r, F_sq (τ, r) ∂μ ∂μ) = ∫ τ in s..t, ∫ r in τ..t, G τ r := by
      rw [intervalIntegral.integral_of_le hst]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ using h_slice_τ τ hτ
    have hrhs : (∫ r, ∫ τ, F_sq (τ, r) ∂μ ∂μ) = ∫ r in s..t, ∫ τ in s..r, G τ r := by
      rw [intervalIntegral.integral_of_le hst]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using h_slice_r r hr
    rw [← hlhs, ← hrhs, hswap]
  -- 5. Conclude via IsMildDuhamelPropagator.weak_of_fubini
  exact hMild.weak_of_fubini hSc hAc_op hφ hs hst ht f L_free hL_free hAc_ti hFub_ti hFub_eq

end UnforcedLeray.Short.IIb.WeakDuhamelProof

theorem mildDuhamelWeakStep_proof : UnforcedLeray.Short.IIb.MildDuhamelWeakStep :=
  UnforcedLeray.Short.IIb.WeakDuhamelProof.mildDuhamelWeakStep_proof_aux

end
