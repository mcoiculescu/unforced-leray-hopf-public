import UnforcedLeray.Short.PartIIIb.Concrete.YoungFlat
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Fpm

/-!
# Young source theorem, Duhamel form, concrete version (source 4417-4426, 4463-4508)

Proves `ConcreteYF.YoungDuhamelC` from the frozen pair `YoungFrozenPair` (error relative to
`|F_+(H,t)|`, source 4407-4412), the laws, the bounds and the hypotheses. The argument of
4501-4508:

* the forcing vanishes on `(T_f, H]`, so `H^μ w(H) = ∫₀^{T_f} t^μ 𝒰(H,t) f(t) dt`;
* `F_j(H,t) = F_j(H,0) F_j(t,0)⁻¹` (`ydc_fpm_cocycle`), so the frozen part integrates exactly to
  `Σ_j F_j(H,0) a_{ν,j}(f) q_{j,H}`;
* the frozen-pair error `|F_+(H,t)| O(ν) = |F_+(H,0)| |F_+(t,0)|⁻¹ O(ν)` integrates against
  `t^{Re μ} ‖f(t)‖` to `|F_+(H,0)| O(ν) ‖f‖_𝓘`;
* the bare columns satisfy `φ_{ν,j}(H) = F_j(H,0) q_{j,H} + |F_+(H,0)| O(ν)` (4422-4426, the frozen
  pair at `t = 0` and the Gram law), and `|a_{ν,j}(f)| ≤ C ‖f‖_𝓘` (4488-4489).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

open ConcreteYF

/-- The cocycle `F_j(s,t) F_j(t,0) = F_j(s,0)` for `s, t ≥ 0`, `ν > 0` (source 4368-4372). -/
lemma ydc_fpm_cocycle (j : Bool) (lam κ : ℂ) (ν s t : ℝ) (hν : 0 < ν) (hs : 0 ≤ s)
    (ht : 0 ≤ t) : Fpm j lam κ ν s t * Fpm j lam κ ν t 0 = Fpm j lam κ ν s 0 := by
  have has := aOf_pos_of_nonneg ν s hν hs
  have hat := aOf_pos_of_nonneg ν t hν ht
  have ha0 : aOf ν 0 = 1 := by simp [aOf]
  have hdiv : aOf ν s / aOf ν t * (aOf ν t / aOf ν 0) = aOf ν s / aOf ν 0 := by
    rw [ha0, div_one, div_one]
    exact div_mul_cancel₀ _ hat.ne'
  have hpow : ∀ k : ℂ, ((aOf ν s / aOf ν t : ℝ) : ℂ) ^ k * ((aOf ν t / aOf ν 0 : ℝ) : ℂ) ^ k
      = ((aOf ν s / aOf ν 0 : ℝ) : ℂ) ^ k := by
    intro k
    have h2 : (0 : ℝ) ≤ aOf ν t / aOf ν 0 := by rw [ha0, div_one]; exact hat.le
    rw [← Complex.mul_cpow_ofReal_nonneg (div_pos has hat).le h2 k, ← Complex.ofReal_mul, hdiv]
  have hexp : ∀ l : ℂ, Complex.exp (l * ((zOf ν s - zOf ν t : ℝ) : ℂ))
      * Complex.exp (l * ((zOf ν t - zOf ν 0 : ℝ) : ℂ))
      = Complex.exp (l * ((zOf ν s - zOf ν 0 : ℝ) : ℂ)) := by
    intro l
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  cases j
  · rw [fpm_false_eq, fpm_false_eq, fpm_false_eq, ← hexp ((starRingEnd ℂ) lam),
      ← hpow ((starRingEnd ℂ) κ)]
    ring
  · rw [fpm_true_eq, fpm_true_eq, fpm_true_eq, ← hexp lam, ← hpow κ]
    ring

/-- Abstract form of the Duhamel estimate: an integrand `u` within `K w` of the frozen part
`Σ_j (c_j a_j) q_j`, amplitudes bounded by `B w`, and bare columns `c_j q_j + e_j` with
`‖e_j‖ ≤ K'`. -/
lemma ydc_abstract {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (m : Measure ℝ) (u : ℝ → X) (a1 a2 : ℝ → ℂ) (w : ℝ → ℝ) (c1 c2 : ℂ) (q1 q2 e1 e2 : X)
    (K B K' : ℝ)
    (hu : Integrable u m) (ha1 : Integrable a1 m) (ha2 : Integrable a2 m) (hw : Integrable w m)
    (hpt : ∀ᵐ t ∂m, ‖u t - ((c1 * a1 t) • q1 + (c2 * a2 t) • q2)‖ ≤ K * w t)
    (hb1 : ∀ᵐ t ∂m, ‖a1 t‖ ≤ B * w t) (hb2 : ∀ᵐ t ∂m, ‖a2 t‖ ≤ B * w t)
    (he1 : ‖e1‖ ≤ K') (he2 : ‖e2‖ ≤ K') :
    ‖∫ t, u t ∂m - ((∫ t, a1 t ∂m) • (c1 • q1 + e1) + (∫ t, a2 t ∂m) • (c2 • q2 + e2))‖
      ≤ (K + 2 * B * K') * ∫ t, w t ∂m := by
  have hg1 : Integrable (fun t => (c1 * a1 t) • q1) m := (ha1.const_mul c1).smul_const q1
  have hg2 : Integrable (fun t => (c2 * a2 t) • q2) m := (ha2.const_mul c2).smul_const q2
  have hI : ∫ t, (u t - ((c1 * a1 t) • q1 + (c2 * a2 t) • q2)) ∂m
      = ∫ t, u t ∂m - ((c1 * ∫ t, a1 t ∂m) • q1 + (c2 * ∫ t, a2 t ∂m) • q2) := by
    have hg12 : Integrable (fun t => (c1 * a1 t) • q1 + (c2 * a2 t) • q2) m := hg1.add hg2
    rw [integral_sub hu hg12, integral_add hg1 hg2, integral_smul_const,
      integral_smul_const, integral_const_mul, integral_const_mul]
  have hmain : ‖∫ t, u t ∂m - ((c1 * ∫ t, a1 t ∂m) • q1 + (c2 * ∫ t, a2 t ∂m) • q2)‖
      ≤ K * ∫ t, w t ∂m := by
    rw [← hI, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul K) hpt
  have hA1 : ‖∫ t, a1 t ∂m‖ ≤ B * ∫ t, w t ∂m := by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul B) hb1
  have hA2 : ‖∫ t, a2 t ∂m‖ ≤ B * ∫ t, w t ∂m := by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul B) hb2
  have hsplit : ∫ t, u t ∂m - ((∫ t, a1 t ∂m) • (c1 • q1 + e1) + (∫ t, a2 t ∂m) • (c2 • q2 + e2))
      = (∫ t, u t ∂m - ((c1 * ∫ t, a1 t ∂m) • q1 + (c2 * ∫ t, a2 t ∂m) • q2))
        - ((∫ t, a1 t ∂m) • e1 + (∫ t, a2 t ∂m) • e2) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, mul_comm (∫ t, a1 t ∂m) c1,
      mul_comm (∫ t, a2 t ∂m) c2]
    abel
  have hBW : 0 ≤ B * ∫ t, w t ∂m := le_trans (norm_nonneg _) hA1
  have hp1 : ‖(∫ t, a1 t ∂m) • e1‖ ≤ (B * ∫ t, w t ∂m) * K' := by
    rw [norm_smul]; exact mul_le_mul hA1 he1 (norm_nonneg _) hBW
  have hp2 : ‖(∫ t, a2 t ∂m) • e2‖ ≤ (B * ∫ t, w t ∂m) * K' := by
    rw [norm_smul]; exact mul_le_mul hA2 he2 (norm_nonneg _) hBW
  rw [hsplit]
  have hsum := norm_add_le ((∫ t, a1 t ∂m) • e1) ((∫ t, a2 t ∂m) • e2)
  have htot := norm_sub_le (∫ t, u t ∂m - ((c1 * ∫ t, a1 t ∂m) • q1 + (c2 * ∫ t, a2 t ∂m) • q2))
    ((∫ t, a1 t ∂m) • e1 + (∫ t, a2 t ∂m) • e2)
  have hring : (K + 2 * B * K') * ∫ t, w t ∂m
      = K * ∫ t, w t ∂m + 2 * ((B * ∫ t, w t ∂m) * K') := by ring
  rw [hring]
  linarith

/-- Young source theorem, Duhamel form (source 4463-4508), concrete version. -/
theorem youngDuhamelC_holds (pk : ℕ → YoungPkg) (conjX : ∀ n, (pk n).X → (pk n).X)
    (ν : ℕ → ℝ) (lam κ μ : ℂ) (Sg α : ℝ) :
    ConcreteYF.YoungDuhamelC pk conjX ν lam κ μ Sg α := by
  unfold ConcreteYF.YoungDuhamelC
  intro hL hH hB hFP
  unfold YoungHyp at hH
  unfold YoungBounded at hB
  unfold YoungFrozenPair at hFP
  obtain ⟨hνpos, -, -, hα0, hαS⟩ := hH
  obtain ⟨Cb, hCb⟩ := hB
  obtain ⟨C, N, hC⟩ := hFP
  refine ⟨|C| * (1 + 2 * Cb ^ 2), N, ?_⟩
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
