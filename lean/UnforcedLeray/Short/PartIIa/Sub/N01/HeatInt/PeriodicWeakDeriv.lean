import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4

/-!
# `PartII-a:N01/9/1/2/4` (decomposition): `PeriodicWeakDeriv`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430. A `C¹` `c`-periodic `φ` has its classical
partial derivatives as weak cell derivatives against cylinder tests `ψ` (periodic in `q`,
vanishing for `|η|` large): the product `G = φ ψ` is `C¹`, periodic in `q` and vanishes on a
band, so `∫_cell ∂_j G = 0` by the fundamental theorem in `q` (boundary terms cancel by
periodicity) and in `η` (compact support), with Fubini on the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

/-- A function vanishing on the open band `R < |η|` has vanishing derivatives there. -/
theorem fderiv_zero_of_band {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : ℝ}
    {f : ℝ × ℝ → E} (hf : ∀ x : ℝ × ℝ, R < |x.2| → f x = 0)
    {x : ℝ × ℝ} (hx : R < |x.2|) (v : ℝ × ℝ) : fderiv ℝ f x v = 0 := by
  have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : E) :=
    Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => hf y hy
  rw [hev.fderiv_eq]
  simp

/-- A continuous function vanishing for `R < |η|` is integrable on the cell. -/
theorem integrableOn_cell_of_band {c R : ℝ} {h : ℝ × ℝ → ℂ} (hh : Continuous h)
    (hz : ∀ x : ℝ × ℝ, R < |x.2| → h x = 0) :
    IntegrableOn h (UnforcedLeray.B0579.cell c) := by
  have hK : IntegrableOn h (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hh.continuousOn
  refine hK.of_forall_sdiff_eq_zero ?_ ?_
  · exact MeasurableSet.prod measurableSet_Ico MeasurableSet.univ
  · rintro x ⟨hxc, hxK⟩
    apply hz
    have hxc' := hxc
    simp only [UnforcedLeray.B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hxc'
    have h1 : x.1 ∈ Icc (-(c / 2)) (c / 2) := ⟨hxc'.1, hxc'.2.le⟩
    have h2 : x.2 ∉ Icc (-R) R := fun h => hxK (mem_prod.2 ⟨h1, h⟩)
    simp only [mem_Icc, not_and_or, not_le] at h2
    rw [lt_abs]
    rcases h2 with h | h
    · right; linarith
    · left; linarith

/-- Fubini and the `q`-fundamental theorem: `∫_cell ∂_q G = 0` for periodic `G`. -/
theorem cell_integral_dq {c : ℝ} (hc : 0 < c) {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ 1 G)
    (hper : ∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) {R : ℝ}
    (hz : ∀ x : ℝ × ℝ, R < |x.2| → G x = 0) :
    ∫ x in UnforcedLeray.B0579.cell c, fderiv ℝ G x (UnforcedLeray.B0579.dir 0) = 0 := by
  have hD : Continuous (fun x : ℝ × ℝ => fderiv ℝ G x (UnforcedLeray.B0579.dir 0)) :=
    (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hint := integrableOn_cell_of_band (c := c) hD
    (fun x hx => fderiv_zero_of_band hz hx _)
  have hf : Integrable (fun x : ℝ × ℝ => fderiv ℝ G x (UnforcedLeray.B0579.dir 0))
      ((volume.restrict (Ico (-(c / 2)) (c / 2))).prod (volume.restrict (univ : Set ℝ))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hint
  have inner : ∀ y : ℝ, ∫ x in Ico (-(c / 2)) (c / 2),
      fderiv ℝ G (x, y) (UnforcedLeray.B0579.dir 0) = 0 := by
    intro y
    have hderiv : ∀ x ∈ uIcc (-(c / 2)) (c / 2),
        HasDerivAt (fun t : ℝ => G (t, y)) (fderiv ℝ G (x, y) (UnforcedLeray.B0579.dir 0)) x := by
      intro x _
      have h1 : HasFDerivAt G (fderiv ℝ G (x, y)) (x, y) :=
        ((hG.differentiable (by norm_num)) (x, y)).hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => (t, y)) (UnforcedLeray.B0579.dir 0) x := by
        have : UnforcedLeray.B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := by
          simp [UnforcedLeray.B0579.dir]
        rw [this]
        exact (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
      exact h1.comp_hasDerivAt x h2
    have hcont : Continuous (fun t : ℝ => fderiv ℝ G (t, y) (UnforcedLeray.B0579.dir 0)) :=
      hD.comp (continuous_id.prodMk continuous_const)
    rw [integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -(c / 2) ≤ c / 2 by linarith)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f' := fun t => fderiv ℝ G (t, y) (UnforcedLeray.B0579.dir 0)) hderiv
      (hcont.intervalIntegrable _ _)]
    have e : G (-(c / 2) + c, y) = G (-(c / 2), y) := hper (-(c / 2), y)
    rw [show -(c / 2) + c = c / 2 by ring] at e
    show G (c / 2, y) - G (-(c / 2), y) = 0
    rw [e, sub_self]
  show ∫ x in (Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)),
      fderiv ℝ G x (UnforcedLeray.B0579.dir 0) = 0
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hf]
  simp only [inner, integral_zero]

/-- Fubini and the `η`-fundamental theorem: `∫_cell ∂_η G = 0` for `G` vanishing on the band. -/
theorem cell_integral_deta {c : ℝ} {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ 1 G) {R : ℝ}
    (hz : ∀ x : ℝ × ℝ, R < |x.2| → G x = 0) :
    ∫ x in UnforcedLeray.B0579.cell c, fderiv ℝ G x (UnforcedLeray.B0579.dir 1) = 0 := by
  have hD : Continuous (fun x : ℝ × ℝ => fderiv ℝ G x (UnforcedLeray.B0579.dir 1)) :=
    (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hint := integrableOn_cell_of_band (c := c) hD
    (fun x hx => fderiv_zero_of_band hz hx _)
  have hf : Integrable (fun x : ℝ × ℝ => fderiv ℝ G x (UnforcedLeray.B0579.dir 1))
      ((volume.restrict (Ico (-(c / 2)) (c / 2))).prod (volume.restrict (univ : Set ℝ))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hint
  have inner : ∀ q : ℝ, ∫ y in (univ : Set ℝ),
      fderiv ℝ G (q, y) (UnforcedLeray.B0579.dir 1) = 0 := by
    intro q
    set M : ℝ := |R| + 1 with hM
    have hM1 : R < M := by rw [hM]; linarith [le_abs_self R]
    have hM0 : 0 ≤ M := by rw [hM]; linarith [abs_nonneg R]
    have hout : ∀ y ∉ Ioc (-M) M, fderiv ℝ G (q, y) (UnforcedLeray.B0579.dir 1) = 0 := by
      intro y hy
      have hyR : R < |y| := by
        by_contra hcon
        push_neg at hcon
        apply hy
        rw [abs_le] at hcon
        exact ⟨by linarith [hcon.1], by linarith [hcon.2]⟩
      have hyR' : R < |(q, y).2| := hyR
      exact fderiv_zero_of_band hz hyR' _
    have hMpos : R < |M| := lt_of_lt_of_le hM1 (le_abs_self M)
    have hIoc : ∫ y in Ioc (-M) M, fderiv ℝ G (q, y) (UnforcedLeray.B0579.dir 1)
        = ∫ y, fderiv ℝ G (q, y) (UnforcedLeray.B0579.dir 1) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hout y hy)
    have hderiv : ∀ x ∈ uIcc (-M) M,
        HasDerivAt (fun t : ℝ => G (q, t)) (fderiv ℝ G (q, x) (UnforcedLeray.B0579.dir 1)) x := by
      intro x _
      have h1 : HasFDerivAt G (fderiv ℝ G (q, x)) (q, x) :=
        ((hG.differentiable (by norm_num)) (q, x)).hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => (q, t)) (UnforcedLeray.B0579.dir 1) x := by
        have : UnforcedLeray.B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := by
          simp [UnforcedLeray.B0579.dir]
        rw [this]
        exact (hasDerivAt_const x q).prodMk (hasDerivAt_id' x)
      exact h1.comp_hasDerivAt x h2
    have hcont : Continuous (fun t : ℝ => fderiv ℝ G (q, t) (UnforcedLeray.B0579.dir 1)) :=
      hD.comp (continuous_const.prodMk continuous_id)
    rw [Measure.restrict_univ, ← hIoc,
      ← intervalIntegral.integral_of_le (show -M ≤ M by linarith)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f' := fun t => fderiv ℝ G (q, t) (UnforcedLeray.B0579.dir 1)) hderiv
      (hcont.intervalIntegrable _ _)]
    show G (q, M) - G (q, -M) = 0
    rw [hz (q, M) (by show R < |M|; exact hMpos),
      hz (q, -M) (by show R < |-M|; rw [abs_neg]; exact hMpos)]
    simp
  show ∫ x in (Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)),
      fderiv ℝ G x (UnforcedLeray.B0579.dir 1) = 0
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hf]
  simp only [inner, integral_zero]

theorem periodicWeakDeriv : UnforcedLeray.Short.PartIIa.N01.PeriodicWeakDeriv := by
  unfold PeriodicWeakDeriv
  intro c hc φ hφ hper j
  have hφc : Continuous φ := hφ.continuous
  have hφd : ∀ x : ℝ × ℝ, HasFDerivAt φ (fderiv ℝ φ x) x := fun x =>
    ((hφ.differentiable (by norm_num)) x).hasFDerivAt
  have hgc : Continuous (fun x : ℝ × ℝ => fderiv ℝ φ x (UnforcedLeray.B0579.dir j)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  unfold UnforcedLeray.Short.IIIa.HasWeakCellDerivC
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨R, hR⟩ := hψ.band
    have hψz : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0 := fun x hx => hR x hx
    have hpdz : ∀ x : ℝ × ℝ, R < |x.2| → UnforcedLeray.B0579.pd j ψ x = 0 :=
      fun x hx => fderiv_zero_of_band hψz hx _
    have hψc : Continuous (fun x => ((ψ x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hψ.continuous
    have hpdc : Continuous (fun x => ((UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hψ.pd j).continuous
    have hA : IntegrableOn (fun x => φ x * ((UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      integrableOn_cell_of_band (R := R) (hφc.mul hpdc) (fun x hx => by simp [hpdz x hx])
    have hB : IntegrableOn (fun x => fderiv ℝ φ x (UnforcedLeray.B0579.dir j) * ((ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      integrableOn_cell_of_band (R := R) (hgc.mul hψc) (fun x hx => by simp [hψz x hx])
    exact ⟨hA, hB⟩
  · obtain ⟨R, hR⟩ := hψ.band
    have hψz : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0 := fun x hx => hR x hx
    have hψ1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
    have hψC1 : ContDiff ℝ 1 (fun x => ((ψ x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hψ1
    set G : ℝ × ℝ → ℂ := fun x => φ x * ((ψ x : ℝ) : ℂ) with hGdef
    have hGC : ContDiff ℝ 1 G := hφ.mul hψC1
    have hGper : ∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x := fun x => by
      simp only [hGdef, hper x, hψ.periodic x]
    have hGz : ∀ x : ℝ × ℝ, R < |x.2| → G x = 0 := fun x hx => by
      simp [hGdef, hψz x hx]
    have hsplit : ∀ x : ℝ × ℝ, fderiv ℝ G x (UnforcedLeray.B0579.dir j)
        = φ x * ((UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ)
          + fderiv ℝ φ x (UnforcedLeray.B0579.dir j) * ((ψ x : ℝ) : ℂ) := by
      intro x
      have h2 : HasFDerivAt (fun y => ((ψ y : ℝ) : ℂ))
          (Complex.ofRealCLM.comp (fderiv ℝ ψ x)) x :=
        Complex.ofRealCLM.hasFDerivAt.comp x
          ((hψ1.differentiable (by norm_num)) x).hasFDerivAt
      have h3 : HasFDerivAt (fun y => φ y * ((ψ y : ℝ) : ℂ)) _ x := (hφd x).mul h2
      rw [hGdef, h3.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
        UnforcedLeray.B0579.pd]
      ring
    have hD : Continuous (fun x : ℝ × ℝ => fderiv ℝ G x (UnforcedLeray.B0579.dir j)) :=
      (hGC.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have key : ∀ k : Fin 2, ∫ x in UnforcedLeray.B0579.cell c,
        fderiv ℝ G x (UnforcedLeray.B0579.dir k) = 0 := by
      intro k
      fin_cases k
      · exact cell_integral_dq hc hGC hGper hGz
      · exact cell_integral_deta hGC hGz
    have hpdz : ∀ x : ℝ × ℝ, R < |x.2| → UnforcedLeray.B0579.pd j ψ x = 0 :=
      fun x hx => fderiv_zero_of_band hψz hx _
    have hA : IntegrableOn (fun x => φ x * ((UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      integrableOn_cell_of_band (R := R) (hφc.mul (Complex.continuous_ofReal.comp (hψ.pd j).continuous))
        (fun x hx => by simp [hpdz x hx])
    have hB : IntegrableOn (fun x => fderiv ℝ φ x (UnforcedLeray.B0579.dir j) * ((ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      integrableOn_cell_of_band (R := R) (hgc.mul (Complex.continuous_ofReal.comp hψ.continuous))
        (fun x hx => by simp [hψz x hx])
    have e1 : ∫ x in UnforcedLeray.B0579.cell c,
        (φ x * ((UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ)
          + fderiv ℝ φ x (UnforcedLeray.B0579.dir j) * ((ψ x : ℝ) : ℂ)) = 0 := by
      rw [← key j]
      congr 1
      funext x
      exact (hsplit x).symm
    rw [integral_add hA hB] at e1
    dsimp only
    linear_combination e1

end UnforcedLeray.Short.PartIIa.N01
