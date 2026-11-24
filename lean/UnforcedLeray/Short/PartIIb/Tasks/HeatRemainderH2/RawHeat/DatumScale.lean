import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderH2.RawHeat.TrainZero

/-!
# Scaled-datum ring decomposition and bounded-radius ring-lift decay (helper for `PartII-b:B3/2/1/1`)

Source of record: `the November 2 reference manuscript`, lines 2593-2601
(`short-bg:raw-heat`: exact dilation identity for `p.datum α`, local cancellation of
`p.inlet i τ` against its age-zero frozen-stream datum lift on `Axi.age p.R y < p.H / 4`, and
bounded-radius cubic decay `(1 + ‖y‖)^{-3}` of all age-cutoff and age-zero ring lifts).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff BigOperators

namespace UnforcedLeray.Short.IIb.RawHeatAux

open UnforcedLeray UnforcedLeray.Cyl UnforcedLeray.Train UnforcedLeray.Blueprint
open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.IIb.RawAndInletL4
open UnforcedLeray.Short.IIb.DatumFactsAux

/-! ## 1. Exact phase-`τ` similarity dilation of `p.datum α` -/

/-- Exact pointwise decomposition of the similarity-dilated datum
`a_τ(x) = e^{τ/2} a(e^{τ/2} x)` into the ring lifts at phase `τ` of the age-zero train stream
profile and the two frozen-stream datum profiles, valid everywhere on `Space` (both on and off
`Axi.axis`). -/
theorem scaled_datum_eq_Nv_sum (p : Params)
    (hfro : ∀ i : Fin 2, ContDiff ℝ ∞ (p.frozenStream i))
    (α : Fin 2 → ℝ) (τ : ℝ) (x : Space) :
    Real.exp (τ / 2) • p.datum α (Real.exp (τ / 2) • x) =
      Axi.Nv p.R (fun m => datumProfile p.ε (p.train.ψ 0) m.2) τ x +
        ∑ i : Fin 2, α i • Axi.Nv p.R
          (fun m => datumProfile p.ε (p.frozenStream i) m.2) τ x := by
  have hdil : Real.exp (τ / 2) • p.datum α (Real.exp (τ / 2) • x) =
      Axi.Nv p.R (fun m => datumProfile p.ε (p.datumStream α) m.2) τ x := by
    set k : ℝ := Real.exp (τ / 2) with hk
    have hk0 : 0 < k := Real.exp_pos _
    by_cases hx : x ∈ Axi.axis
    · have h0 : Axi.ϱ x = 0 := (Axi.mem_axis_iff x).1 hx
      have h0' : Axi.ϱ (k • x) = 0 := by rw [Axi.ϱ_smul, h0, mul_zero]
      simp [Params.datum, Axi.Nv, Axi.age, h0, h0']
    · have hR := p.R_pos
      have hage := Axi.age_pos hR.ne' hx
      have hlog : Real.log (Axi.age p.R (k • x)) = Real.log (Axi.age p.R x) - τ := by
        rw [Params.age_smul hk0, Real.log_div hage.ne' (pow_pos hk0 2).ne', Real.log_pow, hk,
          Real.log_exp]
        push_cast
        ring
      have hphase : Axi.phase p.R 0 (k • x) = Axi.phase p.R τ x := by
        rw [Axi.phase, Axi.phase, hlog]
        ring
      have hsq : √(Axi.age p.R (k • x)) = k⁻¹ * √(Axi.age p.R x) := by
        rw [Params.age_smul hk0, Real.sqrt_div' _ (pow_nonneg hk0.le 2), Real.sqrt_sq hk0.le]
        ring
      simp only [Params.datum, Axi.Nv, Axi.chart]
      rw [hsq, hphase, Params.trans_smul hk0, Axi.frameL_smul hk0, smul_smul, ← mul_assoc,
        mul_inv_cancel₀ hk0.ne', one_mul]
  rw [hdil]
  have hψ0 : ContDiff ℝ ∞ (p.train.ψ 0) := contDiff_psi_slice p.train le_rfl
  have hprof_eq : (fun m : E3 => datumProfile p.ε (p.datumStream α) m.2) =
      fun m : E3 => datumProfile p.ε (p.train.ψ 0) m.2 +
        (α 0 • datumProfile p.ε (p.frozenStream 0) m.2 +
          α 1 • datumProfile p.ε (p.frozenStream 1) m.2) := by
    funext m
    have hd0 : DifferentiableAt ℝ (p.train.ψ 0) m.2 := hψ0.differentiable (by simp) m.2
    have hdf0 : DifferentiableAt ℝ (p.frozenStream 0) m.2 := (hfro 0).differentiable (by simp) m.2
    have hdf1 : DifferentiableAt ℝ (p.frozenStream 1) m.2 := (hfro 1).differentiable (by simp) m.2
    have hds : p.datumStream α = fun y =>
        p.train.ψ 0 y + (α 0 * p.frozenStream 0 y + α 1 * p.frozenStream 1 y) := by
      funext y
      unfold Params.datumStream
      rw [Fin.sum_univ_two]
    have ha1 := datumProfile_add p.ε (Ψ₁ := p.train.ψ 0)
      (Ψ₂ := fun y => α 0 * p.frozenStream 0 y + α 1 * p.frozenStream 1 y)
      hd0 ((hdf0.const_mul (α 0)).add (hdf1.const_mul (α 1)))
    have ha2 := datumProfile_add p.ε (Ψ₁ := fun y => α 0 * p.frozenStream 0 y)
      (Ψ₂ := fun y => α 1 * p.frozenStream 1 y)
      (hdf0.const_mul (α 0)) (hdf1.const_mul (α 1))
    rw [hds, ha1, ha2,
      datumProfile_const_mul p.ε (α 0) hdf0, datumProfile_const_mul p.ε (α 1) hdf1]
  rw [hprof_eq, Nv_add, Nv_add, Nv_const_smul, Nv_const_smul, Fin.sum_univ_two]

/-! ## 2. General bounded-radius cubic decay for ring lifts with rapid transverse decay -/

/-- On `s₀ ≤ Axi.age R y` (`ϱ(y) ≤ R / √s₀ =: r₀`) and `2 r₀ ≤ ‖y‖` (`|y₃| ≥ r₀`), any smooth
meridional profile `b` with rapid polynomial decay in `η` has cubic off-axis spatial decay
`(1 + ‖y‖)³ ‖D^j(Nv R b τ)(y)‖ ≤ K`, uniformly in `τ : ℝ`. -/
theorem nv_decay_of_age_ge {R s₀ : ℝ} (hR : 1 ≤ R) (hs₀ : 0 < s₀)
    {b : E3 → Axi.Merid} (hb : ContDiff ℝ ∞ b) (j : ℕ)
    (hbw : ∀ w : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ l ≤ j, ∀ m : E3,
      (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l b m‖ ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℝ) (y : Space),
      y ∉ Axi.axis → s₀ ≤ Axi.age R y → 2 * (R / √s₀) ≤ ‖y‖ →
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖ ≤ K := by
  obtain ⟨C, k, hC, hnv⟩ := nv_pointwise_jet j
  obtain ⟨B, hB0, hB⟩ := hbw (2 * k + 3)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  set u₀ : ℝ := √s₀
  have hu₀0 : 0 < u₀ := Real.sqrt_pos.2 hs₀
  set r₀ : ℝ := R / u₀
  have hr₀0 : 0 < r₀ := div_pos hR0 hu₀0
  refine ⟨C * (1 + r₀⁻¹) ^ (2 * k) * (2 * (1 + u₀⁻¹)) ^ 3 * B, by positivity,
    fun τ y hy hs_ge hynorm => ?_⟩
  have hr : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hs : 0 < Axi.age R y := Axi.age_pos hR0.ne' hy
  set u : ℝ := √(Axi.age R y)
  have hu_eq : u = R / Axi.ϱ y := Axi.sqrt_age hR0 hy
  have hu0 : 0 < u := Real.sqrt_pos.2 hs
  have hu_ge : u₀ ≤ u := Real.sqrt_le_sqrt hs_ge
  have hϱ_eq : Axi.ϱ y = R / u := by
    rw [hu_eq]
    field_simp [hr.ne', hR0.ne']
  have hϱ_le : Axi.ϱ y ≤ r₀ := by
    rw [hϱ_eq]
    exact div_le_div_of_nonneg_left hR0.le hu₀0 hu_ge
  have hny := RawAndInletL4.norm_le_ϱ_add y
  have hy2_ge : r₀ ≤ |y 2| := by linarith
  have hnorm_y2 : 1 + ‖y‖ ≤ 2 * (1 + |y 2|) := by linarith
  set η : ℝ := |Axi.trans R y| with hη_def
  have hη0 : 0 ≤ η := abs_nonneg _
  have hη_eq : η = u * |y 2| := by
    rw [hη_def]
    unfold Axi.trans
    rw [abs_div, abs_mul, abs_of_pos hR0, abs_of_pos hr, hu_eq]
    ring
  set w : ℝ := 1 + η with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  have hy2_le_η : |y 2| ≤ u₀⁻¹ * η := by
    have h1 : u₀ * |y 2| ≤ η := by
      rw [hη_eq]
      exact mul_le_mul_of_nonneg_right hu_ge (abs_nonneg _)
    exact (le_inv_mul_iff₀ hu₀0).2 h1
  have hw_norm : 1 + ‖y‖ ≤ 2 * (1 + u₀⁻¹) * w := by
    have h1 : 1 + |y 2| ≤ (1 + u₀⁻¹) * w := by
      rw [hw]
      nlinarith [inv_pos.2 hu₀0, hη0]
    linarith
  have hpow_norm : (1 + ‖y‖) ^ 3 ≤ (2 * (1 + u₀⁻¹)) ^ 3 * w ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hw_norm 3
  have hu_le_η : u ≤ r₀⁻¹ * η := by
    have h1 : r₀ * u ≤ η := by
      rw [hη_eq, mul_comm]
      exact mul_le_mul_of_nonneg_left hy2_ge hu0.le
    exact (le_inv_mul_iff₀ hr₀0).2 h1
  have hage_le : 1 + Axi.age R y ≤ (1 + r₀⁻¹) ^ 2 * w ^ 2 := by
    have hsq : Axi.age R y = u ^ 2 := (Real.sq_sqrt hs.le).symm
    have h1u : 1 + u ≤ (1 + r₀⁻¹) * w := by
      rw [hw]
      nlinarith [inv_pos.2 hr₀0, hη0]
    calc 1 + Axi.age R y = 1 + u ^ 2 := by rw [hsq]
      _ ≤ (1 + u) ^ 2 := by nlinarith [hu0.le]
      _ ≤ ((1 + r₀⁻¹) * w) ^ 2 := pow_le_pow_left₀ (by positivity) h1u 2
      _ = (1 + r₀⁻¹) ^ 2 * w ^ 2 := by ring
  have hpow_age : (1 + Axi.age R y) ^ k ≤ (1 + r₀⁻¹) ^ (2 * k) * w ^ (2 * k) := by
    calc (1 + Axi.age R y) ^ k
        ≤ ((1 + r₀⁻¹) ^ 2 * w ^ 2) ^ k := pow_le_pow_left₀ (by positivity) hage_le k
      _ = (1 + r₀⁻¹) ^ (2 * k) * w ^ (2 * k) := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have hMy0 : 0 ≤ B * (w ^ (2 * k + 3))⁻¹ := by positivity
  have hder : ∀ l ≤ j, (1 + |(Axi.chart R τ y).2.2|) ^ j *
      ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ B * (w ^ (2 * k + 3))⁻¹ := by
    intro l hl
    have hb' := hB l hl (Axi.chart R τ y)
    have hxy : |(Axi.chart R τ y).2.2| = η := rfl
    rw [hxy, ← hw, pow_add, mul_right_comm] at hb'
    exact (le_mul_inv_iff₀ (pow_pos hw0 _)).2 hb'
  have hj_bd := hnv (Axi.age R y) R τ (B * (w ^ (2 * k + 3))⁻¹) b hs hR hMy0 hb y hy le_rfl hder
  have hcancel : w ^ (2 * k + 3) * (w ^ (2 * k + 3))⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ hw0.ne')
  calc (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖
      ≤ ((2 * (1 + u₀⁻¹)) ^ 3 * w ^ 3) *
          (C * (1 + Axi.age R y) ^ k * (B * (w ^ (2 * k + 3))⁻¹)) :=
        mul_le_mul hpow_norm hj_bd (norm_nonneg _) (by positivity)
    _ ≤ ((2 * (1 + u₀⁻¹)) ^ 3 * w ^ 3) *
          (C * ((1 + r₀⁻¹) ^ (2 * k) * w ^ (2 * k)) * (B * (w ^ (2 * k + 3))⁻¹)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow_age hC.le) hMy0
    _ = C * (1 + r₀⁻¹) ^ (2 * k) * (2 * (1 + u₀⁻¹)) ^ 3 * B *
          ((w ^ (2 * k) * w ^ 3) * (w ^ (2 * k + 3))⁻¹) := by ring
    _ = C * (1 + r₀⁻¹) ^ (2 * k) * (2 * (1 + u₀⁻¹)) ^ 3 * B := by
        rw [← pow_add, hcancel, mul_one]

/-! ## 3. Inlet minus frozen-stream datum decay on `2 (p.R / √(p.H / 4)) ≤ ‖y‖` -/

/-- Off the axis for `2 * (p.R / √(p.H / 4)) ≤ ‖y‖`, `p.inlet i τ` minus its age-zero
frozen-stream datum lift vanishes identically on `Axi.age p.R y < p.H / 4` (where `ageCutoff = 1`)
and satisfies cubic decay `(1 + ‖y‖)³ ‖D^j(...)(y)‖ ≤ M_in` on `p.H / 4 ≤ Axi.age p.R y`. -/
theorem inlet_sub_frozenDatum_decay {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {dm dp : ℝ} {p : Params} {d : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q)
    {i : Fin 2} (hfro_cd : ContDiff ℝ ∞ (p.frozenStream i)) (j : ℕ) :
    ∃ M_in : ℝ, 0 ≤ M_in ∧ ∀ (τ : ℝ) (y : Space),
      y ∉ Axi.axis → 2 * (p.R / √(p.H / 4)) ≤ ‖y‖ →
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (fun z =>
        p.inlet i τ z - Axi.Nv p.R
          (fun m => datumProfile p.ε (p.frozenStream i) m.2) τ z) y‖ ≤ M_in := by
  have hR1 : 1 ≤ p.R := RawAndInletL4.one_le_R_of hreg
  have hR0 : p.R ≠ 0 := p.R_pos.ne'
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (pow_pos p.ν_pos 2)]
    nlinarith [p.ν_pos, hν1]
  have hcpos : 0 < p.c := lt_of_lt_of_le one_pos hc1
  have hH : 0 < p.H := p.H_pos
  have hH4 : 0 < p.H / 4 := by positivity
  obtain ⟨_, _, _, _, _, h0'⟩ := cutStreamJets lam q hq 1
  have hcutsm0 : ContDiff ℝ ∞ (p.cutStream i) := (h0' p hmode hc1 hH i).1
  have hinletsm : ContDiff ℝ ∞ (p.inletProfile i) := by
    unfold Params.inletProfile
    exact inletCD_ringStreamProfile hcutsm0
  set bf : E3 → Axi.Merid := fun m => datumProfile p.ε (p.frozenStream i) m.2
  have hbf_eq : bf = (p.inletProfile i) ∘ projZeroS :=
    funext fun m => datumProfile_frozenStream_eq_inletProfile p i m
  have hbf_sm : ContDiff ℝ ∞ bf := by
    rw [hbf_eq]
    exact hinletsm.comp projZeroS.contDiff
  have hbw_in : ∀ w : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ l ≤ j, ∀ m : E3,
      (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l (p.inletProfile i) m‖ ≤ B := by
    intro w
    obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := cutStreamJets lam q hq (j + 1)
    obtain ⟨C4, hC4, h4'⟩ := ringStreamJetsDecay j
    obtain ⟨hcutsm, hcut⟩ := h3' p hmode hc1 hH i
    set M : ℝ := C3 * (1 + p.H⁻¹) ^ (j + 1) * p.c ^ N
    have hM0 : 0 ≤ M := by positivity
    have hring := h4' p.R (p.H / 2) p.c κ M (p.cutStream i) hR1 (by positivity) hcpos hκ hM0
      hcutsm
      (fun x hx => by
        unfold Params.cutStream
        simp [ageCutoff_eq_zero hH hx.le])
      (fun x hx => cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
      (fun l hl x => hcut l hl x)
    set W : ℝ := Real.exp 1 * (j + w).factorial * (1 + (κ / 2 / p.c)⁻¹) ^ (j + w)
    set A : ℝ := C4 * (1 + p.H / 2) * (1 + p.c / κ) * M
    refine ⟨A * W, by positivity, fun l hl m => ?_⟩
    have hmain := hring l hl m
    have ha : 0 < κ / 2 / p.c := by positivity
    have hwt : (1 + |m.2.2|) ^ (j + w) * Real.exp (-((κ / 2) * |m.2.2| / p.c)) ≤ W := by
      have e : -((κ / 2) * |m.2.2| / p.c) = -((κ / 2 / p.c) * |m.2.2|) := by ring
      rw [e]
      exact InletWeightAux.one_add_pow_mul_exp_le (j + w) ha (abs_nonneg m.2.2)
    calc (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l (p.inletProfile i) m‖
        ≤ (1 + |m.2.2|) ^ (j + w) * (A * Real.exp (-((κ / 2) * |m.2.2| / p.c))) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = A * ((1 + |m.2.2|) ^ (j + w) * Real.exp (-((κ / 2) * |m.2.2| / p.c))) := by ring
      _ ≤ A * W := mul_le_mul_of_nonneg_left hwt (by positivity)
  have hbw_fro : ∀ w : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ l ≤ j, ∀ m : E3,
      (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l bf m‖ ≤ B := by
    intro w
    obtain ⟨B, hB0, hB⟩ := hbw_in w
    refine ⟨B, hB0, fun l hl m => ?_⟩
    have hcomp : ‖iteratedFDeriv ℝ l bf m‖ ≤
        ‖iteratedFDeriv ℝ l (p.inletProfile i) (projZeroS m)‖ := by
      rw [hbf_eq, projZeroS.iteratedFDeriv_comp_right hinletsm m (by exact_mod_cast le_top)]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      have hprod : ∏ _i : Fin l, ‖projZeroS‖ ≤ 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) norm_projZeroS_le
      calc _ ≤ ‖iteratedFDeriv ℝ l (p.inletProfile i) (projZeroS m)‖ * 1 :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = _ := mul_one _
    have hm2 : (projZeroS m).2.2 = m.2.2 := rfl
    exact (mul_le_mul_of_nonneg_left hcomp (by positivity)).trans (by simpa [hm2] using hB l hl (projZeroS m))
  obtain ⟨K₁, hK₁0, hK₁⟩ := nv_decay_of_age_ge hR1 hH4 hinletsm j hbw_in
  obtain ⟨K₂, hK₂0, hK₂⟩ := nv_decay_of_age_ge hR1 hH4 hbf_sm j hbw_fro
  refine ⟨K₁ + K₂, add_nonneg hK₁0 hK₂0, fun τ y hy hynorm => ?_⟩
  by_cases hs_lt : Axi.age p.R y < p.H / 4
  · -- Far-field region `Axi.age p.R y < p.H / 4`: difference vanishes on a neighborhood of `y`
    have hage_cont : ContinuousAt (Axi.age p.R) y :=
      ((ChartJetsAux.contDiffOn_age p.R).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).continuousAt
    have hev_zero : (fun z => p.inlet i τ z - Axi.Nv p.R bf τ z) =ᶠ[𝓝 y] fun _ => (0 : Space) := by
      filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy,
        hage_cont.eventually (gt_mem_nhds hs_lt)] with z _hz hza
      set m : E3 := Axi.chart p.R τ z
      have hm_lt : m.1 < p.H / 4 := hza
      have hev_cut : p.cutStream i =ᶠ[𝓝 m] fun n : E3 => p.frozenStream i n.2 := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hm_lt] with n hn
        unfold Params.cutStream
        rw [ageCutoff_eq_one hH (le_of_lt hn), one_mul]
      have hval_cut : p.cutStream i m = p.frozenStream i m.2 := hev_cut.eq_of_nhds
      have hfd_cut : fderiv ℝ (p.cutStream i) m =
          fderiv ℝ (fun n : E3 => p.frozenStream i n.2) m := hev_cut.fderiv_eq
      have hprof_eq : p.inletProfile i m = bf m := by
        have h1 : p.inletProfile i m =
            Axi.ringStreamProfile p.R (fun n : E3 => p.frozenStream i n.2) m := by
          unfold Params.inletProfile Axi.ringStreamProfile Axi.dEta Axi.dQ Axi.dS
          rw [hval_cut, hfd_cut]
        have h2 : bf m = Axi.ringStreamProfile p.R (fun n : E3 => p.frozenStream i n.2) m := by
          change datumProfile p.ε (p.frozenStream i) m.2 = _
          rw [(inv_inv p.ε).symm]
          exact datumProfile_eq_ringStreamProfile_snd hfro_cd m
        exact h1.trans h2.symm
      change Axi.Nv p.R (p.inletProfile i) τ z - Axi.Nv p.R bf τ z = 0
      unfold Axi.Nv
      rw [hprof_eq, sub_self]
    rw [RawAndInletL4.iteratedFDeriv_eq_zero_of_eventually hev_zero j, norm_zero, mul_zero]
    exact add_nonneg hK₁0 hK₂0
  · -- Near/transition region `p.H / 4 ≤ Axi.age p.R y`: bound each ring lift via `nv_decay_of_age_ge`
    have hs_ge : p.H / 4 ≤ Axi.age p.R y := not_lt.1 hs_lt
    have hin_on : ContDiffOn ℝ ∞ (Axi.Nv p.R (p.inletProfile i) τ) Axi.axisᶜ := by
      rw [ChartJetsAux.Nv_eq_fun]
      exact (ChartJetsAux.contDiffOn_sqrt_age hR0).smul
        (ChartJetsAux.contDiffOn_frameL.clm_apply (ChartJetsAux.contDiffOn_comp_chart hinletsm hR0 τ))
    have hbf_on : ContDiffOn ℝ ∞ (Axi.Nv p.R bf τ) Axi.axisᶜ := by
      rw [ChartJetsAux.Nv_eq_fun]
      exact (ChartJetsAux.contDiffOn_sqrt_age hR0).smul
        (ChartJetsAux.contDiffOn_frameL.clm_apply (ChartJetsAux.contDiffOn_comp_chart hbf_sm hR0 τ))
    have hc1_at : ContDiffAt ℝ j (p.inlet i τ) y :=
      (hin_on.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le (by exact_mod_cast le_top)
    have hc2_at : ContDiffAt ℝ j (Axi.Nv p.R bf τ) y :=
      (hbf_on.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le (by exact_mod_cast le_top)
    change (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (p.inlet i τ - Axi.Nv p.R bf τ) y‖ ≤ K₁ + K₂
    rw [iteratedFDeriv_sub_apply hc1_at hc2_at]
    have b1 : (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (p.inlet i τ) y‖ ≤ K₁ :=
      hK₁ τ y hy hs_ge hynorm
    have b2 : (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (Axi.Nv p.R bf τ) y‖ ≤ K₂ :=
      hK₂ τ y hy hs_ge hynorm
    calc (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (p.inlet i τ) y -
          iteratedFDeriv ℝ j (Axi.Nv p.R bf τ) y‖
        ≤ (1 + ‖y‖) ^ 3 * (‖iteratedFDeriv ℝ j (p.inlet i τ) y‖ +
            ‖iteratedFDeriv ℝ j (Axi.Nv p.R bf τ) y‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ = (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (p.inlet i τ) y‖ +
            (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (Axi.Nv p.R bf τ) y‖ := by ring
      _ ≤ K₁ + K₂ := add_le_add b1 b2

/-! ## 4. Near-axis cubic decay of the age-zero train datum lift (`1 ≤ Axi.age p.R y`, `2 p.R ≤ ‖y‖`) -/

/-- On `1 ≤ Axi.age p.R y` and `2 * p.R ≤ ‖y‖`, the age-zero train datum lift
`Axi.Nv p.R (fun m => datumProfile p.ε (p.train.ψ 0) m.2) τ` satisfies cubic off-axis decay
`(1 + ‖y‖)³ ‖D^j(...)(y)‖ ≤ B`, uniformly in `τ : ℝ`. -/
theorem train0Datum_near_decay3 :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (dm dp : ℝ) (p : Params) (d : ℝ),
      BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : ℝ) (y : Space),
        y ∉ Axi.axis → 1 ≤ Axi.age p.R y → 2 * p.R ≤ ‖y‖ →
        (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j
          (Axi.Nv p.R (fun m => datumProfile p.ε (p.train.ψ 0) m.2) τ) y‖ ≤ B := by
  obtain ⟨νS, hνS, HS⟩ := trainStreamWtdBdd_uncond 2 (by norm_num)
  refine ⟨νS, hνS, fun dm dp p d hreg hν j => ?_⟩
  have hν0 : 0 < p.ν := p.ν_pos
  have hc : p.c = UnforcedLeray.Short.PartI.trainPeriod 2 p.ν := by
    rw [hreg.c_eq]
    unfold UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν0.le, Real.rpow_two]
  have htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train := hreg.train_buc
  let Ψ : ℝ × Plane → ℝ := fun x => p.train.ψ x.1 x.2
  have hΨ : ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ univ) := hreg.train_stream_smooth
  have hR1 : 1 ≤ p.R := RawAndInletL4.one_le_R_of hreg
  have hψ0_cd : ContDiff ℝ ∞ (p.train.ψ 0) := contDiff_psi_slice p.train le_rfl
  let Ψ₀_ext : E3 → ℝ := fun n => p.train.ψ 0 n.2
  have hΨ₀_cd : ContDiff ℝ ∞ Ψ₀_ext := hψ0_cd.comp contDiff_snd
  set bt0 : E3 → Axi.Merid := fun m => datumProfile p.ε (p.train.ψ 0) m.2
  have hbt0_eq : bt0 = Axi.ringStreamProfile p.R Ψ₀_ext := by
    funext m
    change datumProfile p.ε (p.train.ψ 0) m.2 = _
    rw [(inv_inv p.ε).symm]
    exact datumProfile_eq_ringStreamProfile_snd hψ0_cd m
  have hbt0_sm : ContDiff ℝ ∞ bt0 := by
    rw [hbt0_eq]
    exact inletCD_ringStreamProfile hΨ₀_cd
  obtain ⟨C10_raw, hC10_raw⟩ := HS p.ν p.c hν0 hν hc p.train htr 1 0 1
  set C10 : ℝ := max C10_raw 0
  have hC10_nn : 0 ≤ C10 := le_max_right _ _
  have hb10 : ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) * ‖iteratedFDeriv ℝ 0 Ψ x‖ ≤ C10 :=
    fun x hx0 hx1 => by simpa only [pow_one] using (hC10_raw x hx0 hx1).trans (le_max_left _ _)
  have hbw : ∀ w : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ l ≤ j, ∀ m : E3,
      (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l bt0 m‖ ≤ B := by
    intro w
    set W : ℕ := j + w + 1
    have hSW : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ × Plane, 0 < x.1 → x.1 ≤ 1 →
        (1 + |x.2.2|) ^ W * ‖iteratedFDeriv ℝ i Ψ x‖ ≤ C := by
      intro i
      obtain ⟨Ci, hCi⟩ := HS p.ν p.c hν0 hν hc p.train htr W i 1
      exact ⟨max Ci 0, le_max_right _ _, fun x hx0 hx1 => (hCi x hx0 hx1).trans (le_max_left _ _)⟩
    choose CS hCS0 hCS using hSW
    have hψ0_wtd : ∀ i : ℕ, ∀ z : Plane,
        (1 + |z.2|) ^ W * ‖iteratedFDeriv ℝ i (p.train.ψ 0) z‖ ≤ CS i := fun i =>
      (psi_zero_and_sub_wtd_jet p.train hΨ hC10_nn (hCS0 i) (hCS0 (i + 1)) hb10
        (hCS i) (hCS (i + 1))).1
    have hΨ₀_wtd : ∀ i : ℕ, ∀ x : E3,
        (1 + |x.2.2|) ^ W * ‖iteratedFDeriv ℝ i Ψ₀_ext x‖ ≤ CS i := by
      intro i x
      have heq : Ψ₀_ext = (p.train.ψ 0) ∘ ContinuousLinearMap.snd ℝ ℝ Plane := rfl
      have hle : ‖iteratedFDeriv ℝ i Ψ₀_ext x‖ ≤ ‖iteratedFDeriv ℝ i (p.train.ψ 0) x.2‖ := by
        rw [heq, (ContinuousLinearMap.snd ℝ ℝ Plane).iteratedFDeriv_comp_right hψ0_cd x
          (by exact_mod_cast le_top)]
        have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
          (iteratedFDeriv ℝ i (p.train.ψ 0) x.2)
          (fun _ : Fin i => ContinuousLinearMap.snd ℝ ℝ Plane)
        have hsnd_le : ‖ContinuousLinearMap.snd ℝ ℝ Plane‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by
            simp [Prod.norm_def]
        have hprod : ∏ _j : Fin i, ‖ContinuousLinearMap.snd ℝ ℝ Plane‖ ≤ 1 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact pow_le_one₀ (norm_nonneg _) hsnd_le
        calc _ ≤ ‖iteratedFDeriv ℝ i (p.train.ψ 0) x.2‖ * 1 :=
              h1.trans (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
          _ = _ := mul_one _
      exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans (hψ0_wtd i x.2)
    choose CP hCP0 hCP using fun l => PartIIa.ringProfileMeridJet_unif l
    set C_cp : ℝ := ∑ l ∈ Finset.range (j + 1), CP l
    have hC_cp0 : 0 ≤ C_cp := Finset.sum_nonneg fun l _ => hCP0 l
    set S_ψ : ℝ := ∑ i ∈ Finset.range (j + 2), CS i
    have hS_ψ0 : 0 ≤ S_ψ := Finset.sum_nonneg fun i _ => hCS0 i
    refine ⟨C_cp * 2 * S_ψ, by positivity, fun l hl m => ?_⟩
    -- Shift `m` to `(1, m.2)` where `.1 = 1 > 0` without changing `bt0`
    have hshift_eq : bt0 = (fun n : E3 => bt0 (n + (1, (0 : Plane)))) ∘ projZeroS := by
      funext n
      simp [bt0, projZeroS_apply]
    have hshift_cd : ContDiff ℝ ∞ (fun n : E3 => bt0 (n + (1, (0 : Plane)))) :=
      hbt0_sm.comp (contDiff_id.add contDiff_const)
    have hnorm_shift : ‖iteratedFDeriv ℝ l bt0 m‖ ≤
        ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile p.R Ψ₀_ext) (1, m.2)‖ := by
      have h1 : ‖iteratedFDeriv ℝ l bt0 m‖ ≤ ‖iteratedFDeriv ℝ l bt0 (1, m.2)‖ := by
        have hlhs : iteratedFDeriv ℝ l bt0 m =
            (iteratedFDeriv ℝ l bt0 (1, m.2)).compContinuousLinearMap (fun _ => projZeroS) := by
          conv_lhs => rw [hshift_eq]
          rw [projZeroS.iteratedFDeriv_comp_right hshift_cd m (by exact_mod_cast le_top),
            iteratedFDeriv_comp_add_right]
          have hpt : projZeroS m + (1, (0 : Plane)) = (1, m.2) := by
            simp [projZeroS_apply]
          rw [hpt]
        rw [hlhs]
        have hle := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
          (iteratedFDeriv ℝ l bt0 (1, m.2)) (fun _ : Fin l => projZeroS)
        have hprod : ∏ _i : Fin l, ‖projZeroS‖ ≤ 1 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact pow_le_one₀ (norm_nonneg _) norm_projZeroS_le
        calc _ ≤ ‖iteratedFDeriv ℝ l bt0 (1, m.2)‖ * 1 :=
              hle.trans (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
          _ = _ := mul_one _
      rw [← hbt0_eq]
      exact h1
    have hmer_raw := (hCP l p.R Ψ₀_ext hR1 hΨ₀_cd.contDiffOn).2 (1, m.2) one_pos
    have hmer : ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile p.R Ψ₀_ext) (1, m.2)‖ ≤
        CP l * 2 * ((1 + |m.2.2|) *
          ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖) := by
      refine hmer_raw.trans ?_
      have habs : 1 + |((1 : ℝ), m.2).1| + |((1 : ℝ), m.2).2.2| ≤ 2 * (1 + |m.2.2|) := by
        have h1 : |((1 : ℝ), m.2).1| = 1 := by norm_num
        have h2 : ((1 : ℝ), m.2).2.2 = m.2.2 := rfl
        rw [h1, h2]
        linarith [abs_nonneg m.2.2]
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc CP l * (1 + |((1 : ℝ), m.2).1| + |((1 : ℝ), m.2).2.2|) *
            ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖
          ≤ CP l * (2 * (1 + |m.2.2|)) *
              ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs (hCP0 l)) hsum0
        _ = CP l * 2 * ((1 + |m.2.2|) *
              ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖) := by ring
    have hCP_le : CP l ≤ C_cp :=
      Finset.single_le_sum (fun r _ => hCP0 r) (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
    have hsum_le : (1 + |m.2.2|) ^ W *
        ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖ ≤ S_ψ := by
      rw [Finset.mul_sum]
      calc ∑ i ∈ Finset.range (l + 2), (1 + |m.2.2|) ^ W * ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖
          ≤ ∑ i ∈ Finset.range (j + 2),
              (1 + |m.2.2|) ^ W * ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
              (fun _ _ _ => by positivity)
        _ ≤ ∑ i ∈ Finset.range (j + 2), CS i :=
            Finset.sum_le_sum fun i _ => hΨ₀_wtd i (1, m.2)
    have hw_eq : (1 + |m.2.2|) ^ (j + w) * (1 + |m.2.2|) = (1 + |m.2.2|) ^ W := by
      rw [← pow_succ]
    calc (1 + |m.2.2|) ^ (j + w) * ‖iteratedFDeriv ℝ l bt0 m‖
        ≤ (1 + |m.2.2|) ^ (j + w) *
            (CP l * 2 * ((1 + |m.2.2|) *
              ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖)) :=
          mul_le_mul_of_nonneg_left (hnorm_shift.trans hmer) (by positivity)
      _ = CP l * 2 * (((1 + |m.2.2|) ^ (j + w) * (1 + |m.2.2|)) *
            ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖) := by ring
      _ = CP l * 2 * ((1 + |m.2.2|) ^ W *
            ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Ψ₀_ext (1, m.2)‖) := by rw [hw_eq]
      _ ≤ C_cp * 2 * S_ψ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hCP_le (by norm_num)) hsum_le
            (by positivity) (by positivity)
  obtain ⟨K, hK0, hK⟩ := nv_decay_of_age_ge hR1 one_pos hbt0_sm j hbw
  refine ⟨K, hK0, fun τ y hy hs1 hynorm => ?_⟩
  have hynorm' : 2 * (p.R / √1) ≤ ‖y‖ := by simpa using hynorm
  exact hK τ y hy hs1 hynorm'

end UnforcedLeray.Short.IIb.RawHeatAux
