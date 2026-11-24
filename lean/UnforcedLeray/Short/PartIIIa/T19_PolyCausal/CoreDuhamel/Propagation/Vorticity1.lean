import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1.Lebesgue

/-!
# `PartIII-a:T19/2/3/2/1`: `coreVortWeakEq` (SP 3426-3440, 3462-3466, 3489-3491)

The perturbation `w = b_sol - b₀` of the train and free causal solutions solves
`w_s + (μ/s)w - νΔw + 𝒫 div(v⊗w + w⊗v) = -𝒫 div(v⊗b₀ + b₀⊗v)`. Testing both causal equations
with `Φ = Re/Im(r^μ θ(r)) Ψ(x)`, `Ψ = (∂_η φ, -∂_q φ)` the perpendicular gradient of a cylinder
test (`TimeWeak.lean`), the conjugation by `r^μ` removes `μ/r` and `H(r) = r^μ ⟨w(r), Ψ⟩` has weak
time derivative `J(r) = r^μ ∫ (ν w·ΔΨ + (v⊗b + b⊗v):∇Ψ)`. At ages with `L²` slices, `J` is the
integrand of `CoreVortWeakEqAt` (`Equations.lean`: the curl of the equation, the weak gradients
and the divergence-free constraints). The zero entrance `b ∈ 𝓗` forces the continuous
representative of `H` to vanish at `0` (`Lebesgue.lean`), and at the Lebesgue points of the
`L²(cell)`-valued slice path `H(s)` equals its representative for every test simultaneously.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace V1

open UnforcedLeray.BochnerTime

variable {ν c : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
  {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}

/-- At a Lebesgue point of the slice path with `L²` slice, `H(s)` is the continuous
representative, for every test. -/
theorem lebesgue_ident (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hfree : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b₀ G₀)
    (hsol : IsCausalEnergySolution c ν μ (trainVel tr) F b_sol G_sol) (hμ0 : μ ≠ 0)
    (hμpos : 0 < μ.re) {T : ℝ} (hT : 0 < T) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ)
    (hgood : ∀ᵐ r ∂volume, 0 < r →
      ∀ i, MemLp (fun x => wF b₀ b_sol (r, x) i) 2 (volume.restrict (B0579.cell c)))
    (hwm : ∀ i, Measurable fun p => wF b₀ b_sol p i)
    (hwEL : ∀ i, ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (‖wF b₀ b_sol p i‖ ^ 2) < ⊤)
    {s : ℝ} (hsT : s ∈ Ioo 0 T)
    (hs : ∀ i, MemLp (fun x => wF b₀ b_sol (s, x) i) 2 (volume.restrict (B0579.cell c)))
    (hl : ∀ i : Fin 2, ∀ a ∈ Ioo 0 s,
      HasDerivAt (fun x => ∫ t in a..x, pathZ c (fun p => wF b₀ b_sol p i) t)
        (pathZ c (fun p => wF b₀ b_sol p i) s) s) :
    Hf c μ (wF b₀ b_sol) φ s =
      (hasWeakDeriv hc tr hbuc hfree hsol hμ0 (by linarith) hT hφ).rep s := by
  set h := hasWeakDeriv hc tr hbuc hfree hsol hμ0 (by linarith) hT hφ with hh
  set w := wF b₀ b_sol with hw
  set a := s / 2 with ha_def
  have ha : a ∈ Ioo 0 s := ⟨by linarith [hsT.1], by linarith [hsT.1]⟩
  set P : ℝ → ℂ := fun t => ∫ x in B0579.cell c, hInt w φ (t, x) with hP
  have hm : ∀ i : Fin 2, MemLp (fun x => (perpF φ x i : ℂ)) 2 (volume.restrict (B0579.cell c)) :=
    fun i => memLp_test (perpF_cylTest hφ i)
  set ℓ : Fin 2 → (Lp ℂ 2 (volume.restrict (B0579.cell c)) →L[ℂ] ℂ) :=
    fun i => innerSL ℂ ((hm i).toLp _) with hℓ
  have hPgood : ∀ t, (∀ i, MemLp (fun x => w (t, x) i) 2 (volume.restrict (B0579.cell c))) →
      P t = ℓ 0 (pathZ c (fun p => w p 0) t) + ℓ 1 (pathZ c (fun p => w p 1) t) := by
    intro t ht
    have e0 := pair_eq (hm 0) (f := fun p => w p 0) (ht 0)
    have e1 := pair_eq (hm 1) (f := fun p => w p 1) (ht 1)
    simp only [hℓ]
    rw [e0, e1]
    obtain ⟨R0, hR0⟩ := (perpF_cylTest hφ 0).band
    obtain ⟨R1, hR1⟩ := (perpF_cylTest hφ 1).band
    have i0 := intL2 (ht 0) (perpF_cylTest hφ 0).continuous (R := R0) hR0
    have i1 := intL2 (ht 1) (perpF_cylTest hφ 1).continuous (R := R1) hR1
    simp only [hP, hInt, Fin.sum_univ_two]
    exact integral_add i0 i1
  have hII : ∀ i : Fin 2, ∀ x ∈ Ioo a T,
      IntervalIntegrable (pathZ c (fun p => w p i)) volume a x := fun i x hx =>
    pathZ_intervalIntegrable (hwm i) (hwEL i) ha.1 hx.1
  have hnhds : Ioo a T ∈ 𝓝 s := Ioo_mem_nhds ha.2 hsT.2
  -- derivative of `∫_a^x P` from the Lebesgue points
  have hD1 : HasDerivAt (fun x => ∫ t in a..x, P t)
      (ℓ 0 (pathZ c (fun p => w p 0) s) + ℓ 1 (pathZ c (fun p => w p 1) s)) s := by
    have d0 := ((ℓ 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hl 0 a ha)
    have d1 := ((ℓ 1).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hl 1 a ha)
    refine (d0.add d1).congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with x hx
    have iI : ∀ i : Fin 2, IntervalIntegrable (fun t => ℓ i (pathZ c (fun p => w p i) t))
        volume a x := fun i =>
      ⟨(ℓ i).integrable_comp (hII i x hx).1, (ℓ i).integrable_comp (hII i x hx).2⟩
    simp only [Pi.add_apply, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← (ℓ 0).intervalIntegral_comp_comm (hII 0 x hx),
      ← (ℓ 1).intervalIntegral_comp_comm (hII 1 x hx),
      ← intervalIntegral.integral_add (iI 0) (iI 1)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hgood] with t ht htI
    rw [uIoc_of_le hx.1.le] at htI
    exact hPgood t (ht (lt_trans ha.1 htI.1))
  -- the representative side
  have hpow_ne : ∀ t : ℝ, 0 < t → (t : ℂ) ^ μ ≠ 0 := fun t ht => by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h' => (Complex.ofReal_ne_zero.2 ht.ne') h'.1
  set Q : ℝ → ℂ := fun t => h.rep t / (t : ℂ) ^ μ with hQ
  have hQc : ContinuousOn Q (Ioo 0 T) := by
    refine (h.continuousOn_rep.mono Ioo_subset_Icc_self).div ?_ (fun t ht => hpow_ne t ht.1)
    exact fun t ht => (contDiffAt_cpow μ ht.1).continuousAt.continuousWithinAt
  have hD2 : HasDerivAt (fun x => ∫ t in a..x, Q t) (Q s) s := by
    have hsub : uIcc a s ⊆ Ioo 0 T := by
      rw [uIcc_of_le ha.2.le]
      exact fun t ht => ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hsT.2⟩
    exact intervalIntegral.integral_hasDerivAt_right ((hQc.mono hsub).intervalIntegrable)
      (hQc.stronglyMeasurableAtFilter isOpen_Ioo s hsT)
      (hQc.continuousAt (Ioo_mem_nhds hsT.1 hsT.2))
  have heq : (fun x => ∫ t in a..x, P t) =ᶠ[𝓝 s] fun x => ∫ t in a..x, Q t := by
    filter_upwards [hnhds] with x hx
    refine intervalIntegral.integral_congr_ae ?_
    have hae := h.ae_eq_rep
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo] at hae
    filter_upwards [hae] with t ht htI
    rw [uIoc_of_le hx.1.le] at htI
    have htT : t ∈ Ioo 0 T := ⟨lt_trans ha.1 htI.1, lt_of_le_of_lt htI.2 hx.2⟩
    have e := ht htT
    simp only [hQ, hP]
    rw [← e, Hf]
    field_simp [hpow_ne t htT.1]
  have hPQ := hD1.unique (hD2.congr_of_eventuallyEq heq)
  rw [← hPgood s hs] at hPQ
  have hfin : (s : ℂ) ^ μ * P s = h.rep s := by
    rw [hPQ, hQ]
    field_simp [hpow_ne s hsT.1]
  exact hfin

end V1

/-- **`PartIII-a:T19/2/3/2/1`** (SP 3426-3440, 3462-3466, 3489-3491): the gain-conjugated
perturbation vorticity `Ω = r^μ g ω` is a weak solution of the sourced linearised vorticity
equation with zero entrance. -/
theorem coreVortWeakEq : UnforcedLeray.Short.IIIa.CoreVortWeakEq := by
  intro P hP K hK b hb ν hν tr μ A_m F b₀ G₀ b_sol G_sol hd
  obtain ⟨hbuc, hμK, -, -, -, -, -, hfree, hsol⟩ := hd
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨hμpos, -⟩ := hK.2 μ hμK
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμpos
  by_cases hT : coreEnd ν b ≤ 0
  · exact Eventually.of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.2 hT)
  push Not at hT
  have hg0 := V1.ae_slice_memLp hfree
  have hg1 := V1.ae_slice_memLp hsol
  have hgood : ∀ᵐ r ∂volume, 0 < r → ∀ i, MemLp (fun x => V1.wF b₀ b_sol (r, x) i) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) := by
    filter_upwards [hg0, hg1] with r h0 h1 hr i
    exact (h1 hr i).sub (h0 hr i)
  have hwm : ∀ i, Measurable fun p => V1.wF b₀ b_sol p i := fun i =>
    (hsol.measurable i).sub (hfree.measurable i)
  have hwEL : ∀ i, ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell (ν ^ (-2 : ℝ)),
        ENNReal.ofReal (‖V1.wF b₀ b_sol p i‖ ^ 2) < ⊤ := by
    intro i s₁ s₂ h1 h12
    have e1 := V1.energyLoc_lint hsol h1 h12
    have e0 := V1.energyLoc_lint hfree h1 h12
    have hm1 : Measurable fun p => ENNReal.ofReal (vnorm2 (b_sol p) ^ 2) :=
      ((V1.measurable_vnorm2 hsol.measurable).pow_const 2).ennreal_ofReal
    calc ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell (ν ^ (-2 : ℝ)),
          ENNReal.ofReal (‖V1.wF b₀ b_sol p i‖ ^ 2)
        ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell (ν ^ (-2 : ℝ)),
          (ENNReal.ofReal 2 * ENNReal.ofReal (vnorm2 (b_sol p) ^ 2) +
            ENNReal.ofReal 2 * ENNReal.ofReal (vnorm2 (b₀ p) ^ 2)) := by
          refine lintegral_mono fun p => ?_
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have a1 := V1.norm_le_vnorm2 (b_sol p) i
          have a0 := V1.norm_le_vnorm2 (b₀ p) i
          have hsub := norm_sub_le (b_sol p i) (b₀ p i)
          simp only [V1.wF]
          have hw2 : ‖b_sol p i - b₀ p i‖ ^ 2 ≤ (‖b_sol p i‖ + ‖b₀ p i‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hsub 2
          have q1 : ‖b_sol p i‖ ^ 2 ≤ vnorm2 (b_sol p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a1 2
          have q0 : ‖b₀ p i‖ ^ 2 ≤ vnorm2 (b₀ p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a0 2
          nlinarith [sq_nonneg (‖b_sol p i‖ - ‖b₀ p i‖)]
      _ < ⊤ := by
          rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top e1,
            ENNReal.mul_lt_top ENNReal.ofReal_lt_top e0⟩
  have hL : ∀ i : Fin 2, ∀ᵐ s ∂volume, s ∈ Ioo 0 (coreEnd ν b) → ∀ a ∈ Ioo 0 s,
      HasDerivAt (fun x => ∫ t in a..x, V1.pathZ (ν ^ (-2 : ℝ)) (fun p => V1.wF b₀ b_sol p i) t)
        (V1.pathZ (ν ^ (-2 : ℝ)) (fun p => V1.wF b₀ b_sol p i) s) s := fun i =>
    V1.ae_lebesgue (hwm i) (hwEL i) hT
  filter_upwards [hgood, hL 0, hL 1] with s hsg hl0 hl1 hsT φ hφ
  have hs : 0 < s := hsT.1
  have hl : ∀ i : Fin 2, ∀ a ∈ Ioo 0 s,
      HasDerivAt (fun x => ∫ t in a..x, V1.pathZ (ν ^ (-2 : ℝ)) (fun p => V1.wF b₀ b_sol p i) t)
        (V1.pathZ (ν ^ (-2 : ℝ)) (fun p => V1.wF b₀ b_sol p i) s) s := by
    intro i
    fin_cases i
    · exact hl0 hsT
    · exact hl1 hsT
  have hid := V1.lebesgue_ident hc tr hbuc hfree hsol hμ0 hμpos hT hφ hgood hwm hwEL hsT
    (hsg hs) hl
  have hW := V1.hasWeakDeriv hc tr hbuc hfree hsol hμ0 (by linarith) hT hφ
  have h0 := V1.rep_zero hc tr hbuc hfree hsol hμ0 hμpos hT hφ
  have hrep := hW.rep_eq hT.le ⟨hs.le, hsT.2.le⟩
  have hJint : IntervalIntegrable (V1.Jf (ν ^ (-2 : ℝ)) μ tr b_sol (V1.wF b₀ b_sol) φ)
      volume 0 s :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hs.le).2
      ((V1.Jf_int hc tr hbuc hfree hsol (by linarith) hT.le hφ).mono_set
        (Ioo_subset_Ioo_right hsT.2.le))
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff] at hJint ⊢
    refine hJint.congr_fun_ae ?_
    rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hg0, hg1] with r h0' h1' hrI
    rw [uIoc_of_le hs.le] at hrI
    exact (V1.rep_TI tr hfree hsol hrI.1 (h0' hrI.1) (h1' hrI.1) hφ).symm
  · rw [V1.lhs_eq hfree hsol hs hφ, hid, hrep, h0, zero_add]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hg0, hg1] with r h0' h1' hrI
    rw [uIoc_of_le hs.le] at hrI
    exact (V1.rep_TI tr hfree hsol hrI.1 (h0' hrI.1) (h1' hrI.1) hφ).symm

end UnforcedLeray.Short.IIIa

end
