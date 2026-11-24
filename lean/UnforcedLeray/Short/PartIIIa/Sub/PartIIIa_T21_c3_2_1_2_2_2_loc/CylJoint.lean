import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.CylStart

/-!
# Joint continuity of free cylinder flows in (start age, time) (helper for `relB4loc_leaf`)

Source: `the November 2 reference manuscript` lines 2960-2970.  Let `ω(s)` be a free
cylinder flow started at age `s` from a cylinder test `f(s)`, with `f(s) → f(s₀)` in `X_{m,c}` and
`f(s₀)` vanishing near the cell boundary.  Then `ω(s)(t) → ω(s₀)(t₀)` in `X_{m,c}` as
`(s, t) → (s₀, t₀)` with `s ≤ t`: restart and linearity reduce the later start to the earlier one
(`diff_bound`), and the earlier start is controlled by the uniform start continuity
(`start_cont_bound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa.RelB4locAux

theorem eLpNorm_sub_tri {μ : Measure B0579.Plane} {u v w : B0579.Plane → ℝ}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hw : AEStronglyMeasurable w μ) :
    eLpNorm (u - w) 2 μ ≤ eLpNorm (u - v) 2 μ + eLpNorm (v - w) 2 μ := by
  have h : u - w = (u - v) + (v - w) := by simp [sub_add_sub_cancel]
  rw [h]; exact eLpNorm_add_le (hu.sub hv) (hv.sub hw) (by norm_num)

/-- **Joint continuity in (start age, time)** of free cylinder flows from moving cylinder tests. -/
theorem cyl_joint_tendsto {m ν c T : ℝ} (hm : 8 < m) (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr) (hT : 0 ≤ T)
    (f : ℝ → B0579.Plane → ℝ) (ω : ℝ → ℝ → B0579.Plane → ℝ) {s₀ t₀ : ℝ}
    (hs₀ : 0 ≤ s₀) (hst₀ : s₀ ≤ t₀) (ht₀ : t₀ ≤ T)
    (hf₀ : B0579.IsCylTest c (f s₀)) (hω₀ : IsFreeCylFlow m tr s₀ (f s₀) (ω s₀))
    {η : ℝ} (hη : 0 < η) (hηc : η < c)
    (hvan : ∀ x : B0579.Plane, c / 2 - η < |x.1| → |x.1| ≤ c / 2 → f s₀ x = 0)
    (l : Filter (ℝ × ℝ)) (hl : l ≤ 𝓝 (s₀, t₀))
    (hev : ∀ᶠ p in l, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ T ∧ B0579.IsCylTest c (f p.1) ∧
      IsFreeCylFlow m tr p.1 (f p.1) (ω p.1))
    (hfc : Tendsto (fun p : ℝ × ℝ => eLpNorm (f p.1 - f s₀) 2 (B0579.cellMeasure c m)) l
      (𝓝 0)) :
    Tendsto (fun p : ℝ × ℝ => eLpNorm (ω p.1 p.2 - ω s₀ t₀) 2 (B0579.cellMeasure c m)) l
      (𝓝 0) := by
  set μ := B0579.cellMeasure c m with hμ
  obtain ⟨C, hC1, hD⟩ := diff_bound hm hν hc hbu hT
  obtain ⟨K, M, hK, hM, hU⟩ := start_cont_bound hm hν hc hbu hT hf₀ hη hηc hvan
  set Eg := cylEnergy c m (f s₀) with hEg_def
  have hEg : 0 ≤ Eg := t22_energy_nonneg c m _
  set Uf : ℝ → ℝ≥0∞ := fun h =>
    ENNReal.ofReal (Real.sqrt ((Real.exp (2 * K * h) - 1) * Eg + 2 * h * M)) with hUf
  have hUmono : ∀ h₁ h₂ : ℝ, 0 ≤ h₁ → h₁ ≤ h₂ → Uf h₁ ≤ Uf h₂ := by
    intro h₁ h₂ h0 h12
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    have he : Real.exp (2 * K * h₁) ≤ Real.exp (2 * K * h₂) := Real.exp_le_exp.2 (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_right he hEg]
  have hs₀T : s₀ ≤ T := hst₀.trans ht₀
  set A : ℝ × ℝ → ℝ≥0∞ := fun p => eLpNorm (f p.1 - f s₀) 2 μ with hA_def
  set E : ℝ × ℝ → ℝ≥0∞ := fun p => eLpNorm (ω s₀ (max p.1 s₀) - ω s₀ s₀) 2 μ with hE_def
  set Bt : ℝ × ℝ → ℝ≥0∞ := fun p => eLpNorm (ω s₀ (max p.2 s₀) - ω s₀ t₀) 2 μ with hBt_def
  set U : ℝ × ℝ → ℝ≥0∞ := fun p => Uf (max (s₀ - p.1) 0) with hU_def
  set Cr : ℝ≥0∞ := ENNReal.ofReal C with hCr_def
  have hinit : ω s₀ s₀ =ᵐ[μ] f s₀ := (B0579.cellMeasure_ac c m).ae_le hω₀.initial
  have mf₀ : AEStronglyMeasurable (f s₀) μ := (hf₀.memLp m).1
  have key : ∀ᶠ p in l, eLpNorm (ω p.1 p.2 - ω s₀ t₀) 2 μ ≤
      Cr * (A p + E p) + Cr * (U p + Cr * A p) + (Cr * A p + U p) + Bt p := by
    filter_upwards [hev] with p hp
    obtain ⟨hs, hst, htT, hfs, hωs⟩ := hp
    obtain ⟨G, hG, hGs, -, -⟩ := exists_regular_of_test hm hν hc hbu hs hf₀
    have mfs : AEStronglyMeasurable (f p.1) μ := (hfs.memLp m).1
    have mωs : ∀ r, p.1 ≤ r → AEStronglyMeasurable (ω p.1 r) μ := fun r hr => (hωs.memX r hr).1
    have mω₀ : ∀ r, s₀ ≤ r → AEStronglyMeasurable (ω s₀ r) μ := fun r hr => (hω₀.memX r hr).1
    have mG : ∀ r, p.1 ≤ r → AEStronglyMeasurable (G r) μ := fun r hr => (hG.memX r hr).1
    have hGA : eLpNorm (f p.1 - G p.1) 2 μ = A p := by rw [hGs]
    rcases le_total s₀ p.1 with h1 | h1
    · -- later start: restart the flow from `s₀` at `p.1`
      have hmax1 : max p.1 s₀ = p.1 := max_eq_left h1
      have hmax2 : max p.2 s₀ = p.2 := max_eq_left (h1.trans hst)
      have step1 := eLpNorm_sub_tri (mωs p.2 hst) (mω₀ p.2 (h1.trans hst)) (mω₀ t₀ hst₀)
      have step2 := hD s₀ p.1 p.2 hs₀ h1 hst htT (f s₀) (f p.1) hf₀ hfs (ω s₀) (ω p.1) hω₀ hωs
      have step3 := eLpNorm_sub_tri mfs mf₀ (mω₀ p.1 h1)
      have step4 : eLpNorm (f s₀ - ω s₀ p.1) 2 μ = E p := by
        simp only [hE_def, hmax1]
        rw [eLpNorm_sub_comm]
        apply eLpNorm_congr_ae
        filter_upwards [hinit] with x hx
        simp only [Pi.sub_apply, hx]
      have hB : eLpNorm (ω s₀ p.2 - ω s₀ t₀) 2 μ = Bt p := by simp only [hBt_def, hmax2]
      calc eLpNorm (ω p.1 p.2 - ω s₀ t₀) 2 μ
          ≤ eLpNorm (ω p.1 p.2 - ω s₀ p.2) 2 μ + eLpNorm (ω s₀ p.2 - ω s₀ t₀) 2 μ := step1
        _ ≤ Cr * (A p + E p) + Bt p := by
            rw [hB]
            refine add_le_add (step2.trans ?_) le_rfl
            gcongr
            rw [← step4]
            exact step3
        _ ≤ _ := add_le_add (le_add_right (le_add_right le_rfl)) le_rfl
    · rcases le_total s₀ p.2 with h2 | h2
      · -- earlier start, later time
        have hmax2 : max p.2 s₀ = p.2 := max_eq_left h2
        have hmaxU : max (s₀ - p.1) 0 = s₀ - p.1 := max_eq_left (by linarith)
        have step1 := eLpNorm_sub_tri (mωs p.2 hst) (mω₀ p.2 h2) (mω₀ t₀ hst₀)
        have step2 := hD p.1 s₀ p.2 hs h1 h2 htT (f p.1) (f s₀) hfs hf₀ (ω p.1) (ω s₀) hωs hω₀
        have step3 := eLpNorm_sub_tri mf₀ (mG s₀ h1) (mωs s₀ h1)
        have step4 : eLpNorm (f s₀ - G s₀) 2 μ ≤ U p := by
          rw [eLpNorm_sub_comm]
          simp only [hU_def, hmaxU]
          exact hU p.1 s₀ hs h1 hs₀T G hG
        have step5 : eLpNorm (G s₀ - ω p.1 s₀) 2 μ ≤ Cr * A p := by
          rw [eLpNorm_sub_comm, ← hGA]
          exact hD p.1 p.1 s₀ hs le_rfl h1 hs₀T (f s₀) (f p.1) hf₀ hfs G (ω p.1) hG hωs
        have hB : eLpNorm (ω s₀ p.2 - ω s₀ t₀) 2 μ = Bt p := by simp only [hBt_def, hmax2]
        calc eLpNorm (ω p.1 p.2 - ω s₀ t₀) 2 μ
            ≤ eLpNorm (ω p.1 p.2 - ω s₀ p.2) 2 μ + eLpNorm (ω s₀ p.2 - ω s₀ t₀) 2 μ := step1
          _ ≤ Cr * (U p + Cr * A p) + Bt p := by
              rw [hB, eLpNorm_sub_comm]
              refine add_le_add (step2.trans ?_) le_rfl
              gcongr
              exact step3.trans (add_le_add step4 step5)
          _ ≤ _ := add_le_add (le_add_right (le_add_left le_rfl)) le_rfl
      · -- earlier start, earlier time (only near the diagonal)
        have hmax2 : max p.2 s₀ = s₀ := max_eq_right h2
        have hmaxU : max (s₀ - p.1) 0 = s₀ - p.1 := max_eq_left (by linarith)
        have step1 := eLpNorm_sub_tri (mωs p.2 hst) (mω₀ s₀ le_rfl) (mω₀ t₀ hst₀)
        have hB : eLpNorm (ω s₀ s₀ - ω s₀ t₀) 2 μ = Bt p := by simp only [hBt_def, hmax2]
        have step2 : eLpNorm (ω p.1 p.2 - ω s₀ s₀) 2 μ = eLpNorm (ω p.1 p.2 - f s₀) 2 μ := by
          apply eLpNorm_congr_ae
          filter_upwards [hinit] with x hx
          simp only [Pi.sub_apply, hx]
        have step3 := eLpNorm_sub_tri (mωs p.2 hst) (mG p.2 hst) mf₀
        have step4 : eLpNorm (ω p.1 p.2 - G p.2) 2 μ ≤ Cr * A p := by
          rw [← hGA]
          exact hD p.1 p.1 p.2 hs le_rfl hst htT (f s₀) (f p.1) hf₀ hfs G (ω p.1) hG hωs
        have step5 : eLpNorm (G p.2 - f s₀) 2 μ ≤ U p := by
          refine (hU p.1 p.2 hs hst htT G hG).trans ?_
          simp only [hU_def, hmaxU]
          exact hUmono _ _ (by linarith) (by linarith)
        calc eLpNorm (ω p.1 p.2 - ω s₀ t₀) 2 μ
            ≤ eLpNorm (ω p.1 p.2 - ω s₀ s₀) 2 μ + eLpNorm (ω s₀ s₀ - ω s₀ t₀) 2 μ := step1
          _ ≤ (Cr * A p + U p) + Bt p := by
              rw [hB, step2]
              exact add_le_add (step3.trans (add_le_add step4 step5)) le_rfl
          _ ≤ _ := add_le_add (le_add_left le_rfl) le_rfl
  -- the bound tends to zero
  have hA : Tendsto A l (𝓝 0) := hfc
  have hE : Tendsto E l (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ × ℝ => max p.1 s₀) l (𝓝[Ici s₀] s₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun p => mem_Ici.2 (le_max_right _ _)⟩
      have : Tendsto (fun p : ℝ × ℝ => max p.1 s₀) (𝓝 (s₀, t₀)) (𝓝 (max s₀ s₀)) :=
        (continuous_fst.max continuous_const).tendsto _
      rw [max_self] at this
      exact this.mono_left hl
    exact (hω₀.strongCont s₀ le_rfl).comp h1
  have hBt : Tendsto Bt l (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ × ℝ => max p.2 s₀) l (𝓝[Ici s₀] t₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun p => mem_Ici.2 (le_max_right _ _)⟩
      have : Tendsto (fun p : ℝ × ℝ => max p.2 s₀) (𝓝 (s₀, t₀)) (𝓝 (max t₀ s₀)) :=
        (continuous_snd.max continuous_const).tendsto _
      rw [max_eq_left hst₀] at this
      exact this.mono_left hl
    exact (hω₀.strongCont t₀ hst₀).comp h1
  have hUl : Tendsto U l (𝓝 0) := by
    have hh : Tendsto (fun p : ℝ × ℝ => max (s₀ - p.1) 0) l (𝓝 0) := by
      have : Tendsto (fun p : ℝ × ℝ => max (s₀ - p.1) 0) (𝓝 (s₀, t₀))
          (𝓝 (max (s₀ - s₀) 0)) :=
        ((continuous_const.sub continuous_fst).max continuous_const).tendsto _
      rw [sub_self, max_self] at this
      exact this.mono_left hl
    have hUc : Continuous Uf :=
      ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp (by fun_prop))
    have h0 : Uf 0 = 0 := by simp [hUf]
    have := (hUc.tendsto 0).comp hh
    rwa [h0] at this
  have hCr : Cr ≠ ⊤ := ENNReal.ofReal_ne_top
  have t0 : Tendsto (fun p => Cr * A p) l (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hA (Or.inr hCr)
    rwa [mul_zero] at h
  have t1 : Tendsto (fun p => Cr * (A p + E p)) l (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (hA.add hE) (Or.inr hCr)
    rwa [add_zero, mul_zero] at h
  have t2 : Tendsto (fun p => Cr * (U p + Cr * A p)) l (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (hUl.add t0) (Or.inr hCr)
    rwa [add_zero, mul_zero] at h
  have t3 : Tendsto (fun p => Cr * A p + U p) l (𝓝 0) := by
    have h := t0.add hUl
    rwa [add_zero] at h
  have hlim := ((t1.add t2).add t3).add hBt
  simp only [add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) key

end UnforcedLeray.Short.IIIa.RelB4locAux
