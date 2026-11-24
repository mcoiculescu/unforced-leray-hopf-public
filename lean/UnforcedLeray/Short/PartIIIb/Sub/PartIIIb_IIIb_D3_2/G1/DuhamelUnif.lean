import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.Org

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1

open ConcreteYF

theorem youngDuhamelUnif (pk : ℕ → YoungPkg) (conjX : ∀ n, (pk n).X → (pk n).X) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : G1.YoungDuhamelUnifC pk conjX ν lam κ Sg α := by
  unfold YoungDuhamelUnifC
  intro hL hH hB hFP
  unfold YoungHyp at hH
  unfold YoungBounded at hB
  unfold YoungFrozenPair at hFP
  obtain ⟨hνpos, -, -, hα0, hαS⟩ := hH
  obtain ⟨Cb, hCb⟩ := hB
  obtain ⟨C, N, hC⟩ := hFP
  refine ⟨|C| * (1 + 2 * Cb ^ 2), N, fun μ => ?_⟩
  intro n hn f hf_hi _hf_lo hU hA1 hA2 hW
  have hνn : 0 < ν n := hνpos n
  have hSg : 0 < Sg := lt_trans hα0 hαS
  have hH0 : (0 : ℝ) ≤ Sg / ν n := div_nonneg hSg.le hνn.le
  have hTf0 : (0 : ℝ) ≤ α / ν n := div_nonneg hα0.le hνn.le
  have hTfH : α / ν n ≤ Sg / ν n := div_le_div_of_nonneg_right hαS.le hνn.le
  have hsub : Ioc (0 : ℝ) (α / ν n) ⊆ Ioc 0 (Sg / ν n) := Ioc_subset_Ioc_right hTfH
  -- the frozen-pair error operator
  set E : ℝ → (pk n).X →L[ℂ] (pk n).X := fun t => (pk n).Uev (Sg / ν n) t -
      ∑ j : Bool, Fpm j lam κ (ν n) (Sg / ν n) t •
        ((pk n).ell j t).smulRight ((pk n).q j (Sg / ν n)) with hEdef
  have hEapp : ∀ t (x : (pk n).X), E t x = (pk n).Uev (Sg / ν n) t x -
      (Fpm true lam κ (ν n) (Sg / ν n) t • ((pk n).ell true t x • (pk n).q true (Sg / ν n)) +
        Fpm false lam κ (ν n) (Sg / ν n) t •
          ((pk n).ell false t x • (pk n).q false (Sg / ν n))) := by
    intro t x
    simp [hEdef, ContinuousLinearMap.smulRight_apply]
  have hEb : ∀ t ∈ Icc (0 : ℝ) (α / ν n), ∀ x : (pk n).X,
      ‖E t x‖ ≤ |C| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ * ‖x‖ := by
    intro t ht x
    have h1 := hC n hn t ht
    have h2 : C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖
        ≤ |C| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hνn.le)
        (norm_nonneg _)
    exact (ContinuousLinearMap.le_opNorm (E t) x).trans
      (mul_le_mul_of_nonneg_right (h1.trans h2) (norm_nonneg x))
  -- step 1: the forcing vanishes on `(T_f, H]`
  have hD : duhamel (pk n) μ f (Sg / ν n)
      = ∫ t in Ioc 0 (α / ν n), ((t : ℂ) ^ μ) • ((pk n).Uev (Sg / ν n) t (f t)) := by
    unfold duhamel
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub ?_
    intro t ht
    have hlt : α / ν n < t := by
      rcases ht with ⟨⟨h0, _⟩, hnot⟩
      by_contra hc
      exact hnot ⟨h0, le_of_not_gt hc⟩
    rw [hf_hi t hlt, map_zero, smul_zero]
  -- step 2: the bare columns `φ_{ν,j}(H) = F_j(H,0) q_{j,H} + E(0) q_{j,0}`
  have hgram : ∀ i j : Bool, (pk n).ell i 0 ((pk n).q j 0) = if i = j then 1 else 0 :=
    fun i j => (hL n).gram 0 i j
  have hφ1 : (pk n).Uev (Sg / ν n) 0 ((pk n).q true 0)
      = Fpm true lam κ (ν n) (Sg / ν n) 0 • (pk n).q true (Sg / ν n) + E 0 ((pk n).q true 0) := by
    rw [hEapp, hgram, hgram]
    simp
  have hφ2 : conjX n ((pk n).Uev (Sg / ν n) 0 ((pk n).q true 0))
      = Fpm false lam κ (ν n) (Sg / ν n) 0 • (pk n).q false (Sg / ν n)
        + E 0 ((pk n).q false 0) := by
    rw [(hL n).conj_U, ← (hL n).conj_q, hEapp, hgram, hgram]
    simp
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) (α / ν n) := ⟨le_rfl, hTf0⟩
  have h0H : (0 : ℝ) ∈ Icc (0 : ℝ) (Sg / ν n) := ⟨le_rfl, hH0⟩
  have he : ∀ j : Bool, ‖E 0 ((pk n).q j 0)‖
      ≤ |C| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) 0‖ * Cb := by
    intro j
    exact (hEb 0 h0mem _).trans (mul_le_mul_of_nonneg_left (hCb n 0 h0H j).1
      (mul_nonneg (mul_nonneg (abs_nonneg _) hνn.le) (norm_nonneg _)))
  -- step 3: pointwise bounds on the source band
  have hcpow : ∀ t : ℝ, 0 < t → ‖((t : ℂ) ^ μ)‖ = t ^ μ.re :=
    fun t ht => Complex.norm_cpow_eq_rpow_re_of_pos ht μ
  have hpt : ∀ t ∈ Ioc (0 : ℝ) (α / ν n),
      ‖((t : ℂ) ^ μ) • ((pk n).Uev (Sg / ν n) t (f t)) -
        ((Fpm true lam κ (ν n) (Sg / ν n) 0 *
            (((t : ℂ) ^ μ) * (Fpm true lam κ (ν n) t 0)⁻¹ * ((pk n).ell true t) (f t))) •
              (pk n).q true (Sg / ν n) +
          (Fpm false lam κ (ν n) (Sg / ν n) 0 *
            (((t : ℂ) ^ μ) * (Fpm false lam κ (ν n) t 0)⁻¹ * ((pk n).ell false t) (f t))) •
              (pk n).q false (Sg / ν n))‖
        ≤ (|C| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) 0‖) *
          (t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ * ‖f t‖) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htI : t ∈ Icc (0 : ℝ) (α / ν n) := ⟨ht0, ht.2⟩
    have hcj : ∀ j : Bool, Fpm j lam κ (ν n) (Sg / ν n) 0 *
        (((t : ℂ) ^ μ) * (Fpm j lam κ (ν n) t 0)⁻¹ * ((pk n).ell j t) (f t))
        = ((t : ℂ) ^ μ) * (Fpm j lam κ (ν n) (Sg / ν n) t * ((pk n).ell j t) (f t)) := by
      intro j
      have hne : Fpm j lam κ (ν n) t 0 ≠ 0 := (fpm_facts (ν n) hνn lam κ t 0 ht0 le_rfl).2.1 j
      rw [← ydc_fpm_cocycle j lam κ (ν n) (Sg / ν n) t hνn hH0 ht0]
      calc Fpm j lam κ (ν n) (Sg / ν n) t * Fpm j lam κ (ν n) t 0 *
            (((t : ℂ) ^ μ) * (Fpm j lam κ (ν n) t 0)⁻¹ * ((pk n).ell j t) (f t))
          = ((t : ℂ) ^ μ) * (Fpm j lam κ (ν n) (Sg / ν n) t * ((pk n).ell j t) (f t)) *
              (Fpm j lam κ (ν n) t 0 * (Fpm j lam κ (ν n) t 0)⁻¹) := by ring
        _ = ((t : ℂ) ^ μ) * (Fpm j lam κ (ν n) (Sg / ν n) t * ((pk n).ell j t) (f t)) := by
            rw [mul_inv_cancel₀ hne, mul_one]
    have hid : ((t : ℂ) ^ μ) • ((pk n).Uev (Sg / ν n) t (f t)) -
        ((Fpm true lam κ (ν n) (Sg / ν n) 0 *
            (((t : ℂ) ^ μ) * (Fpm true lam κ (ν n) t 0)⁻¹ * ((pk n).ell true t) (f t))) •
              (pk n).q true (Sg / ν n) +
          (Fpm false lam κ (ν n) (Sg / ν n) 0 *
            (((t : ℂ) ^ μ) * (Fpm false lam κ (ν n) t 0)⁻¹ * ((pk n).ell false t) (f t))) •
              (pk n).q false (Sg / ν n))
        = ((t : ℂ) ^ μ) • E t (f t) := by
      rw [hcj true, hcj false, hEapp]
      module
    -- `|F_+(H,t)| = |F_+(H,0)| |F_+(t,0)|⁻¹`
    have hco := ydc_fpm_cocycle true lam κ (ν n) (Sg / ν n) t hνn hH0 ht0
    have hne : ‖Fpm true lam κ (ν n) t 0‖ ≠ 0 :=
      norm_ne_zero_iff.mpr ((fpm_facts (ν n) hνn lam κ t 0 ht0 le_rfl).2.1 true)
    have hFHt : ‖Fpm true lam κ (ν n) (Sg / ν n) t‖
        = ‖Fpm true lam κ (ν n) (Sg / ν n) 0‖ * ‖Fpm true lam κ (ν n) t 0‖⁻¹ := by
      rw [← hco, norm_mul, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rw [hid, norm_smul, hcpow t ht.1]
    have hb := hEb t htI (f t)
    rw [hFHt] at hb
    have hrp : 0 ≤ t ^ μ.re := Real.rpow_nonneg ht0 _
    calc t ^ μ.re * ‖E t (f t)‖
        ≤ t ^ μ.re * (|C| * ν n * (‖Fpm true lam κ (ν n) (Sg / ν n) 0‖ *
            ‖Fpm true lam κ (ν n) t 0‖⁻¹) * ‖f t‖) := mul_le_mul_of_nonneg_left hb hrp
      _ = (|C| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) 0‖) *
            (t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ * ‖f t‖) := by ring
  have hamp : ∀ j : Bool, ∀ t ∈ Ioc (0 : ℝ) (α / ν n),
      ‖((t : ℂ) ^ μ) * (Fpm j lam κ (ν n) t 0)⁻¹ * ((pk n).ell j t) (f t)‖
        ≤ Cb * (t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ * ‖f t‖) := by
    intro j t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htH : t ∈ Icc (0 : ℝ) (Sg / ν n) := ⟨ht0, ht.2.trans hTfH⟩
    have hmod : ‖Fpm j lam κ (ν n) t 0‖ = ‖Fpm true lam κ (ν n) t 0‖ := by
      cases j
      · exact (fpm_facts (ν n) hνn lam κ t 0 ht0 le_rfl).2.2
      · rfl
    have hl : ‖((pk n).ell j t) (f t)‖ ≤ Cb * ‖f t‖ :=
      ((pk n).ell j t).le_opNorm (f t) |>.trans
        (mul_le_mul_of_nonneg_right (hCb n t htH j).2 (norm_nonneg _))
    rw [norm_mul, norm_mul, norm_inv, hcpow t ht.1, hmod]
    have hrp : 0 ≤ t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ :=
      mul_nonneg (Real.rpow_nonneg ht0 _) (inv_nonneg.mpr (norm_nonneg _))
    calc t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ * ‖((pk n).ell j t) (f t)‖
        ≤ t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ * (Cb * ‖f t‖) :=
          mul_le_mul_of_nonneg_left hl hrp
      _ = Cb * (t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ * ‖f t‖) := by ring
  -- step 4: assemble
  have hUon : Integrable (fun t : ℝ => ((t : ℂ) ^ μ) • ((pk n).Uev (Sg / ν n) t (f t)))
      (volume.restrict (Ioc 0 (α / ν n))) := IntegrableOn.mono_set hU hsub
  have key := ydc_abstract (volume.restrict (Ioc 0 (α / ν n)))
    (fun t : ℝ => ((t : ℂ) ^ μ) • ((pk n).Uev (Sg / ν n) t (f t)))
    (fun t : ℝ => ((t : ℂ) ^ μ) * (Fpm true lam κ (ν n) t 0)⁻¹ * ((pk n).ell true t) (f t))
    (fun t : ℝ => ((t : ℂ) ^ μ) * (Fpm false lam κ (ν n) t 0)⁻¹ * ((pk n).ell false t) (f t))
    (fun t : ℝ => t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ * ‖f t‖)
    (Fpm true lam κ (ν n) (Sg / ν n) 0) (Fpm false lam κ (ν n) (Sg / ν n) 0)
    ((pk n).q true (Sg / ν n)) ((pk n).q false (Sg / ν n))
    (E 0 ((pk n).q true 0)) (E 0 ((pk n).q false 0))
    (|C| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) 0‖) Cb
    (|C| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) 0‖ * Cb)
    hUon hA1 hA2 hW
    (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
    (ae_restrict_of_forall_mem measurableSet_Ioc (hamp true))
    (ae_restrict_of_forall_mem measurableSet_Ioc (hamp false))
    (he true) (he false)
  rw [hD, hφ2, hφ1]
  unfold aFrozen testedNorm
  refine key.trans (le_of_eq ?_)
  ring
