import UnforcedLeray.Units.B0412.Action
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ChartLift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.InletJetAll

/-!
# Far-field homogeneity of the inlet column (organizer task
`PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1`, target `inletEFarHom : InletEFarHom`)

Source `the November 2 reference manuscript`,
lines 2542-2549 (complete sources, unprojected derivatives) and 1206-1222 (ring lift).

Proof outline. `E(τ, ·) = realC ∘ Nv_R (inletProfile i) τ`, where `realC` is a real linear
isometry (`efarRealCLI`, a local copy of `realCLI`), so the derivatives of `E` have the norms
of the derivatives of the lift. `ChartLiftJets` bounds the `k`-th derivative of the lift by
`K ϱ^{-1-k} (1+t)^k ∑_{l≤k} ‖D^l b (chart)‖` with `t = |y₃|/ϱ`. `inletJetAll` (order `3`) bounds
the chart-point derivatives of the inlet profile by `C exp(-κ|η|)` with `|η| = R t ≥ t`
(`R = ε⁻¹ ≥ 1`). Finally `exp(-κt)(1+t)^(3+N)` is bounded (`efar_exp_poly`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `realC` as a real linear isometry `ℝ³ → ℂ³` (local copy of `realCLI`). -/
def efarRealCLI : UnforcedLeray.Space →ₗᵢ[ℝ] UnforcedLeray.PhaseSpace.CVec3 where
  toFun := UnforcedLeray.B0412.realC
  map_add' x y := by
    ext i
    simp [UnforcedLeray.B0412.realC_apply]
  map_smul' c x := by
    ext i
    simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_three, UnforcedLeray.B0412.realC_apply, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]

/-- Composition with `realC` preserves the norms of the derivatives on the axis complement. -/
theorem efar_realC_norm (f : UnforcedLeray.Space → UnforcedLeray.Space)
    (hf : ContDiffOn ℝ ∞ f Axi.axisᶜ) {y : UnforcedLeray.Space} (hy : y ∈ Axi.axisᶜ)
    (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun x => efarRealCLI (f x)) y‖ = ‖iteratedFDeriv ℝ k f y‖ := by
  have hk : (k : WithTop ENat) ≤ ∞ := by exact_mod_cast le_top
  have h := efarRealCLI.norm_iteratedFDerivWithin_comp_left (hf.contDiffWithinAt hy)
    Axi.isOpen_compl_axis.uniqueDiffOn hy hk
  rw [iteratedFDerivWithin_of_isOpen k Axi.isOpen_compl_axis hy,
    iteratedFDerivWithin_of_isOpen k Axi.isOpen_compl_axis hy] at h
  exact h

/-- `exp(-κt)(1+t)^n` is bounded on `t ≥ 0`. -/
theorem efar_exp_poly {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    ∃ A : ℝ, ∀ t : ℝ, 0 ≤ t → Real.exp (-(κ * t)) * (1 + t) ^ n ≤ A := by
  refine ⟨(n.factorial : ℝ) * Real.exp κ / κ ^ n, fun t ht => ?_⟩
  have hx : 0 ≤ κ * (1 + t) := mul_nonneg hκ.le (by linarith)
  have h1 := Real.pow_div_factorial_le_exp _ hx n
  rw [div_le_iff₀ (by exact_mod_cast n.factorial_pos)] at h1
  have hexp : Real.exp (κ * (1 + t)) = Real.exp κ * Real.exp (κ * t) := by
    rw [← Real.exp_add]
    ring_nf
  have hinv : Real.exp (-(κ * t)) * Real.exp (κ * t) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_pow, hexp] at h1
  rw [le_div_iff₀ (pow_pos hκ n)]
  calc Real.exp (-(κ * t)) * (1 + t) ^ n * κ ^ n
      = Real.exp (-(κ * t)) * (κ ^ n * (1 + t) ^ n) := by ring
    _ ≤ Real.exp (-(κ * t)) * (Real.exp κ * Real.exp (κ * t) * (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * Real.exp κ := by
        have e : Real.exp (-(κ * t)) * (Real.exp κ * Real.exp (κ * t) * (n.factorial : ℝ))
            = (Real.exp (-(κ * t)) * Real.exp (κ * t)) * (Real.exp κ * (n.factorial : ℝ)) := by
          ring
        rw [e, hinv]
        ring

/-- **Far-field homogeneity of the inlet column** (source 2542-2549, 1206-1222). -/
theorem inletEFarHom : InletEFarHom := by
  intro lam q hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hmode z g _hdat i N
  have hν0 : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq]
    exact (one_le_inv₀ (pow_pos hν0 2)).2 (by nlinarith)
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq]
    apply Real.exp_le_one_iff.2
    have hneg : -d / p.ν < 0 := div_neg_of_neg_of_pos (by linarith [hreg.dm_pos, hreg.dm_le]) hν0
    exact hneg.le
  have hR1 : 1 ≤ p.R := (one_le_inv₀ p.ε_pos).2 hε1
  have hRpos : 0 < p.R := lt_of_lt_of_le one_pos hR1
  obtain ⟨Cb, κ, hκ, hsm, hbd⟩ := inletJetAll lam q hq p hmode hc1 hR1 i 3
  obtain ⟨K, hK0, hKb⟩ := chartLiftJets p.R hRpos
  obtain ⟨A, hA⟩ := efar_exp_poly hκ (3 + N)
  have hsmb : ContDiffOn ℝ ∞ (p.inletProfile i) {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hsm.contDiffOn
  have hCb0 : 0 ≤ Cb := by
    by_contra hneg
    have hneg' : Cb < 0 := not_le.mp hneg
    have h := hbd 0 (Nat.zero_le _) ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
    have hE : 0 < Real.exp (-(κ * |((1 : ℝ), ((0 : ℝ), (0 : ℝ))).2.2|)) := Real.exp_pos _
    have h0 := norm_nonneg (iteratedFDeriv ℝ 0 (p.inletProfile i) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))
    linarith [mul_neg_of_neg_of_pos hneg' hE]
  have hA0 : 0 ≤ A := by
    have h := hA 0 le_rfl
    norm_num at h
    linarith
  refine ⟨4 * K * Cb * A, p.R, hRpos, ?_⟩
  intro τ y hy k hk
  have hp : 0 < Axi.ϱ y := lt_trans hRpos hy
  have hyax : y ∉ Axi.axis := by
    intro h
    rw [Axi.mem_axis_iff] at h
    linarith
  have hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hyax
  have hRy : p.R ≤ Axi.ϱ y := le_of_lt hy
  have ht0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have h1t0 : 0 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  have hpos1 : 0 < 1 + |y 2| / Axi.ϱ y := by linarith
  have hgS : ContDiffOn ℝ ∞ (fun z => (p.inletProfile i) (Axi.chart p.R τ z)) Axi.axisᶜ :=
    hsmb.comp (clf_chart_contDiffOn p.R τ hRpos) (clf_chart_mapsTo p.R τ hRpos)
  have hNvS : ContDiffOn ℝ ∞ (Axi.Nv p.R (p.inletProfile i) τ) Axi.axisᶜ := by
    have hEq : Axi.Nv p.R (p.inletProfile i) τ =
        fun z => liftFactor p.R z ((p.inletProfile i) (Axi.chart p.R τ z)) :=
      funext fun z => Nv_eq_liftFactor p.R (p.inletProfile i) τ z
    rw [hEq]
    exact (clf_lift_contDiffOn p.R hRpos).clm_apply hgS
  have hη : |y 2| / Axi.ϱ y ≤ |(Axi.chart p.R τ y).2.2| := by
    show |y 2| / Axi.ϱ y ≤ |Axi.trans p.R y|
    rw [Axi.trans, abs_div, abs_mul, abs_of_pos hRpos, abs_of_pos hp]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _) hR1) hp.le
  have hbdk : ∀ l : ℕ, l ≤ 3 →
      ‖iteratedFDeriv ℝ l (p.inletProfile i) (Axi.chart p.R τ y)‖ ≤
        Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) := by
    intro l hl
    refine (hbd l hl (Axi.chart p.R τ y)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hη hκ.le))) hCb0
  have hS : ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) (Axi.chart p.R τ y)‖
      ≤ 4 * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by
    have hk4 : ((k : ℝ) + 1) ≤ 4 := by
      have : (k : ℝ) ≤ 3 := by exact_mod_cast hk
      linarith
    calc ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) (Axi.chart p.R τ y)‖
        ≤ ∑ l ∈ Finset.range (k + 1), Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) :=
          Finset.sum_le_sum (fun l hl => hbdk l (by have := Finset.mem_range.1 hl; omega))
      _ = ((k : ℝ) + 1) * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 4 * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) :=
          mul_le_mul_of_nonneg_right hk4 (mul_nonneg hCb0 (Real.exp_pos _).le)
  have hD : ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ =
      ‖iteratedFDeriv ℝ k (Axi.Nv p.R (p.inletProfile i) τ) y‖ := by
    show ‖iteratedFDeriv ℝ k
      (fun x : UnforcedLeray.Space => efarRealCLI (Axi.Nv p.R (p.inletProfile i) τ x)) y‖ = _
    exact efar_realC_norm _ hNvS hyS k
  have hchart := hKb (p.inletProfile i) hsmb τ y hRy k hk
  have hkey : (1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) ≤
      A * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ)) := by
    rw [Real.rpow_neg h1t0, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos1 N)]
    calc (1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))
          * (1 + |y 2| / Axi.ϱ y) ^ N
        = Real.exp (-(κ * (|y 2| / Axi.ϱ y))) * (1 + |y 2| / Axi.ϱ y) ^ (k + N) := by ring
      _ ≤ Real.exp (-(κ * (|y 2| / Axi.ϱ y))) * (1 + |y 2| / Axi.ϱ y) ^ (3 + N) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by omega))
            (Real.exp_pos _).le
      _ ≤ A := hA _ ht0
  calc ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖
      = ‖iteratedFDeriv ℝ k (Axi.Nv p.R (p.inletProfile i) τ) y‖ := hD
    _ ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ k *
          (4 * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y))))) :=
        hchart.trans (mul_le_mul_of_nonneg_left hS
          (mul_nonneg (mul_nonneg hK0.le (Real.rpow_nonneg hp.le _)) (pow_nonneg h1t0 _)))
    _ = (4 * K * Cb) * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          ((1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by
        ring
    _ ≤ (4 * K * Cb) * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          (A * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0.le) hCb0)
            (Real.rpow_nonneg hp.le _))
    _ = 4 * K * Cb * A * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ))) := by
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
