import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFactsFinal
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.FrozenPairActual
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.DuhamelUnif
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.GBAdmissible
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutputSource

/-!
# `PartIII-b:IIIb-D3/2/G1`: `flatGroupYoung` (source 4386-4508)

Assembles `FlatUnif.GroupYoung D` (state at `H = 2/ν` and later output) for actual flat sequences:
- First conjunct (state at `H`): shifts `pk` by `M = max N0 N1` so `YoungBounded` and `YoungLaws`
  hold from `0`, applies `FlatUnif.G1.youngDuhamelUnif` at `Σ = 2`, `α = 1.1`, `μ = (D.mu n z : ℂ)`,
  `f = (S n).gB B` using `FlatUnif.G1.gBAdmissible`, and bounds the frozen combination via
  `testedNorm` and the frozen-pair error at `t = 0`.
- Second conjunct (later output): `FlatUnif.G1.laterOutputSource D`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

private theorem stateAtH_actual (D : SeqData) :
    FlatUnif.ForActual D fun S => ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B,
      IsBclass D.K.as (FlatUnif.nu D n) B →
      ‖duhamel (S n).pk (D.mu n z : ℂ) ((S n).gB B) (2 / FlatUnif.nu D n)‖ ≤
        C * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (FlatUnif.nu D n) (2 / FlatUnif.nu D n) 0‖ *
          testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (FlatUnif.nu D n) (D.mu n z : ℂ)
            (1.1 / FlatUnif.nu D n) ((S n).gB B) := by
  intro dm dp hst κ hκ m hfact hm S hS
  have hSF := FlatUnif.youngSourceFacts D
  obtain ⟨N0, _δ, ⟨Cb, hb⟩, -, -⟩ := hSF dm dp hst κ hκ m hm S hS
  obtain ⟨Cfp, Nfp, hCfp⟩ :=
    FlatUnif.G1.youngFrozenPair_actual D hSF dm dp hst κ hκ m hm S hS
  obtain ⟨NgB, hNgB⟩ := FlatUnif.G1.gBAdmissible D dm dp hst κ hκ m hm S hS
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hS
  have hν_tend : Tendsto (FlatUnif.nu D) atTop (𝓝 0) :=
    retNu_tendsto (Pl := D.Pl) D.σ₀ hst.omega_ne
  obtain ⟨Nnu, hNnu⟩ := Filter.eventually_atTop.mp
    (hν_tend.eventually (Iic_mem_nhds zero_lt_one))
  set M : ℕ := max N0 N1
  have hM0 : N0 ≤ M := le_max_left _ _
  have hM1 : N1 ≤ M := le_max_right _ _
  let pk' : ℕ → YoungPkg := fun k => (S (k + M)).pk
  let ν' : ℕ → ℝ := fun k => FlatUnif.nu D (k + M)
  set lam : ℂ := D.Pl.eigenvalue
  set κc : ℂ := D.Pl.kappa
  have hLaw : ∀ k, ∃ f : (pk' k).X → (pk' k).X, ConcreteYF.YoungLaws (pk' k) f := by
    intro k
    obtain ⟨FI, hFI⟩ := hN1 (k + M) (by omega)
    have hpk : (S (k + M)).pk = FlatSettingInst.actualPk FI :=
      congrArg ConcreteYF.FlatSetting.pk hFI
    dsimp only [pk']
    rw [hpk]
    exact ⟨FlatSettingInst.conjX, FlatSettingInst.youngLaws_actualPk FI⟩
  choose conjX hconj using hLaw
  have hνpos : ∀ k, 0 < ν' k := fun k => retNu_pos D.Pl D.σ₀ (k + M)
  have hνlim : Tendsto ν' atTop (𝓝 0) := hν_tend.comp (tendsto_add_atTop_nat M)
  have hHyp : ConcreteYF.YoungHyp ν' lam 2 1.1 :=
    ⟨hνpos, hνlim, hst.gamma_pos, by norm_num, by norm_num⟩
  have hBd : ConcreteYF.YoungBounded pk' ν' 2 :=
    ⟨Cb, fun k s hs j => hb (k + M) (by omega) s hs j⟩
  have hFP' : YoungFrozenPair pk' ν' lam κc 2 1.1 :=
    ⟨Cfp, Nfp, fun k hk t ht => hCfp (k + M) (by omega) t ht⟩
  obtain ⟨Cduh, Nduh, hDuh⟩ :=
    FlatUnif.G1.youngDuhamelUnif pk' conjX ν' lam κc 2 1.1 hconj hHyp hBd hFP'
  have hCb0 : 0 ≤ Cb := by
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) (2 / ν' 0) :=
      ⟨le_rfl, div_nonneg (by norm_num) (hνpos 0).le⟩
    exact (norm_nonneg ((pk' 0).q true 0)).trans (hb (0 + M) (by omega) 0 h0mem true).1
  refine ⟨|Cduh| + 2 * Cb * (Cb + |Cfp| * Cb),
    max (max (Nduh + M) Nfp) (max NgB Nnu), ?_⟩
  intro n hn
  have hn_duhM : Nduh + M ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hn_fp : Nfp ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hn_gB : NgB ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn_nu : Nnu ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + M := ⟨n - M, by omega⟩
  have hk_duh : Nduh ≤ k := by omega
  intro z hz B hB
  obtain ⟨hsupp1, hsupp2, hint1, hint_true, hint_false, hint_tested⟩ :=
    hNgB (k + M) hn_gB z hz B hB
  set μ : ℂ := (D.mu (k + M) z : ℂ)
  have hμ_re : μ.re = D.mu (k + M) z := Complex.ofReal_re (D.mu (k + M) z)
  have hint_tested' : Integrable (fun t : ℝ =>
      t ^ μ.re * ‖Fpm true lam κc (ν' k) t 0‖⁻¹ * ‖(S (k + M)).gB B t‖)
      (volume.restrict (Ioc 0 (1.1 / ν' k))) := by
    simpa only [hμ_re] using hint_tested
  have hrem := hDuh μ k hk_duh ((S (k + M)).gB B) hsupp1 hsupp2 hint1 hint_true hint_false
    hint_tested'
  set ν : ℝ := ν' k
  set f : ℝ → (pk' k).X := (S (k + M)).gB B
  set H : ℝ := 2 / ν
  set Tf : ℝ := 1.1 / ν
  set FH0 : ℝ := ‖Fpm true lam κc ν H 0‖
  set TN : ℝ := testedNorm (pk' k) lam κc ν μ Tf f
  have hν : 0 < ν := hνpos k
  have hν1 : ν ≤ 1 := hNnu (k + M) hn_nu
  have hH0 : (0 : ℝ) ≤ H := div_nonneg (by norm_num) hν.le
  have hTf0 : (0 : ℝ) ≤ Tf := div_nonneg (by norm_num) hν.le
  have hTfH : Tf ≤ H := div_le_div_of_nonneg_right (by norm_num) hν.le
  have hFH0 : 0 ≤ FH0 := norm_nonneg _
  have hTN0 : 0 ≤ TN := by
    refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (inv_nonneg.2 (norm_nonneg _)))
      (norm_nonneg _)
  have haF : ∀ j : Bool, ‖aFrozen (pk' k) j lam κc ν μ Tf f‖ ≤ Cb * TN := by
    intro j
    change ‖∫ t in Ioc 0 Tf, ((t : ℂ) ^ μ) * (Fpm j lam κc ν t 0)⁻¹ * ((pk' k).ell j t) (f t)‖ ≤
      Cb * ∫ t in Ioc 0 Tf, t ^ μ.re * ‖Fpm true lam κc ν t 0‖⁻¹ * ‖f t‖
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hint_tested'.const_mul Cb) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 ≤ t := ht.1.le
    have htH : t ∈ Icc (0 : ℝ) H := ⟨ht0, ht.2.trans hTfH⟩
    have hmod : ‖Fpm j lam κc ν t 0‖ = ‖Fpm true lam κc ν t 0‖ := by
      cases j
      · exact (fpm_facts ν hν lam κc t 0 ht0 le_rfl).2.2
      · rfl
    have hl : ‖((pk' k).ell j t) (f t)‖ ≤ Cb * ‖f t‖ :=
      (((pk' k).ell j t).le_opNorm (f t)).trans
        (mul_le_mul_of_nonneg_right (hb (k + M) (by omega) t htH j).2 (norm_nonneg _))
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos ht.1 μ, hmod]
    have hrp : 0 ≤ t ^ μ.re * ‖Fpm true lam κc ν t 0‖⁻¹ :=
      mul_nonneg (Real.rpow_nonneg ht0 _) (inv_nonneg.2 (norm_nonneg _))
    calc t ^ μ.re * ‖Fpm true lam κc ν t 0‖⁻¹ * ‖((pk' k).ell j t) (f t)‖
        ≤ t ^ μ.re * ‖Fpm true lam κc ν t 0‖⁻¹ * (Cb * ‖f t‖) :=
          mul_le_mul_of_nonneg_left hl hrp
      _ = Cb * (t ^ μ.re * ‖Fpm true lam κc ν t 0‖⁻¹ * ‖f t‖) := by ring
  set E0 : (pk' k).X →L[ℂ] (pk' k).X :=
    (pk' k).Uev H 0 -
      ∑ j : Bool, Fpm j lam κc ν H 0 • ((pk' k).ell j 0).smulRight ((pk' k).q j H) with hE0def
  have hE0app : ∀ x : (pk' k).X, E0 x = (pk' k).Uev H 0 x -
      (Fpm true lam κc ν H 0 • ((pk' k).ell true 0 x • (pk' k).q true H) +
        Fpm false lam κc ν H 0 • ((pk' k).ell false 0 x • (pk' k).q false H)) := by
    intro x
    simp [hE0def, ContinuousLinearMap.smulRight_apply]
  have hgram : ∀ i j : Bool, (pk' k).ell i 0 ((pk' k).q j 0) = if i = j then 1 else 0 :=
    fun i j => (hconj k).gram 0 i j
  have hφ1 : (pk' k).Uev H 0 ((pk' k).q true 0) =
      Fpm true lam κc ν H 0 • (pk' k).q true H + E0 ((pk' k).q true 0) := by
    rw [hE0app, hgram, hgram]
    simp
  have hE0_op : ‖E0‖ ≤ |Cfp| * FH0 := by
    have h1 : ‖E0‖ ≤ Cfp * ν * FH0 := hCfp (k + M) hn_fp 0 ⟨le_rfl, hTf0⟩
    have h2 : Cfp * ν * FH0 ≤ |Cfp| * 1 * FH0 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (le_abs_self Cfp) hν1 hν.le (abs_nonneg Cfp)) hFH0
    simpa only [mul_one] using h1.trans h2
  have hq0 : ‖(pk' k).q true 0‖ ≤ Cb :=
    (hb (k + M) (by omega) 0 ⟨le_rfl, hH0⟩ true).1
  have hqH : ‖(pk' k).q true H‖ ≤ Cb :=
    (hb (k + M) (by omega) H ⟨hH0, le_rfl⟩ true).1
  have hE0_q0 : ‖E0 ((pk' k).q true 0)‖ ≤ (|Cfp| * Cb) * FH0 := by
    calc ‖E0 ((pk' k).q true 0)‖
        ≤ ‖E0‖ * ‖(pk' k).q true 0‖ := E0.le_opNorm _
      _ ≤ (|Cfp| * FH0) * Cb :=
          mul_le_mul hE0_op hq0 (norm_nonneg _) (mul_nonneg (abs_nonneg Cfp) hFH0)
      _ = (|Cfp| * Cb) * FH0 := by ring
  have hFqH : ‖Fpm true lam κc ν H 0 • (pk' k).q true H‖ ≤ Cb * FH0 := by
    rw [norm_smul]
    calc FH0 * ‖(pk' k).q true H‖ ≤ FH0 * Cb := mul_le_mul_of_nonneg_left hqH hFH0
      _ = Cb * FH0 := mul_comm _ _
  have hU_q0 : ‖(pk' k).Uev H 0 ((pk' k).q true 0)‖ ≤ (Cb + |Cfp| * Cb) * FH0 := by
    rw [hφ1]
    calc ‖Fpm true lam κc ν H 0 • (pk' k).q true H + E0 ((pk' k).q true 0)‖
        ≤ ‖Fpm true lam κc ν H 0 • (pk' k).q true H‖ + ‖E0 ((pk' k).q true 0)‖ := norm_add_le _ _
      _ ≤ Cb * FH0 + (|Cfp| * Cb) * FH0 := add_le_add hFqH hE0_q0
      _ = (Cb + |Cfp| * Cb) * FH0 := by ring
  set φ : (pk' k).X := (pk' k).Uev H 0 ((pk' k).q true 0)
  set v1 : (pk' k).X := aFrozen (pk' k) true lam κc ν μ Tf f • φ
  set v2 : (pk' k).X := aFrozen (pk' k) false lam κc ν μ Tf f • conjX k φ
  have hrem' : ‖duhamel (pk' k) μ f H - (v1 + v2)‖ ≤ |Cduh| * FH0 * TN := by
    have h2 : Cduh * ν * FH0 * TN ≤ |Cduh| * 1 * FH0 * TN :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul (le_abs_self Cduh) hν1 hν.le (abs_nonneg Cduh)) hFH0) hTN0
    simpa only [mul_one] using hrem.trans h2
  have hv1 : ‖v1‖ ≤ Cb * (Cb + |Cfp| * Cb) * FH0 * TN := by
    rw [norm_smul]
    calc ‖aFrozen (pk' k) true lam κc ν μ Tf f‖ * ‖φ‖
        ≤ (Cb * TN) * ((Cb + |Cfp| * Cb) * FH0) :=
          mul_le_mul (haF true) hU_q0 (norm_nonneg _) (mul_nonneg hCb0 hTN0)
      _ = Cb * (Cb + |Cfp| * Cb) * FH0 * TN := by ring
  have hv2 : ‖v2‖ ≤ Cb * (Cb + |Cfp| * Cb) * FH0 * TN := by
    rw [norm_smul, (hconj k).conj_norm]
    calc ‖aFrozen (pk' k) false lam κc ν μ Tf f‖ * ‖φ‖
        ≤ (Cb * TN) * ((Cb + |Cfp| * Cb) * FH0) :=
          mul_le_mul (haF false) hU_q0 (norm_nonneg _) (mul_nonneg hCb0 hTN0)
      _ = Cb * (Cb + |Cfp| * Cb) * FH0 * TN := by ring
  have hsplit : duhamel (pk' k) μ f H = (duhamel (pk' k) μ f H - (v1 + v2)) + v1 + v2 := by abel
  calc ‖duhamel (pk' k) μ f H‖
      = ‖(duhamel (pk' k) μ f H - (v1 + v2)) + v1 + v2‖ := by rw [← hsplit]
    _ ≤ ‖duhamel (pk' k) μ f H - (v1 + v2)‖ + ‖v1‖ + ‖v2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |Cduh| * FH0 * TN + Cb * (Cb + |Cfp| * Cb) * FH0 * TN +
          Cb * (Cb + |Cfp| * Cb) * FH0 * TN :=
        add_le_add (add_le_add hrem' hv1) hv2
    _ = (|Cduh| + 2 * Cb * (Cb + |Cfp| * Cb)) * FH0 * TN := by ring

/-- Group G1 (state at `H = 2/ν` and later output, source 4386-4508). -/
theorem flatGroupYoung (D : SeqData) : FlatUnif.GroupYoung D := by
  intro dm dp hst κ hκ m hfact hm S hS
  exact ⟨stateAtH_actual D dm dp hst κ hκ m hm S hS,
    FlatUnif.G1.laterOutputSource D dm dp hst κ hκ m hm S hS⟩

end UnforcedLeray.Short.PartIIIb.Concrete
