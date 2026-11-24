import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.RawAndInletL4.SqrtLift
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.RawAndInletL4.HeatDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.RawStreamProfile
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.HeatTermSmooth
import UnforcedLeray.Short.PartIIb.Defs

/-!
# All-order inverse-distance decay of the raw lift, from the weighted train bounds
(helper for `PartII-b:S2/3`)

Source of record: `the November 2 reference manuscript`, lines 2543-2551
("in the large-radius region their unprojected derivatives are bounded by
`C_{k,N}ϱ^{-3-k}(1+|y_3|/ϱ)^{-N}` ... On `ϱ<R`, take the all-age heat expansion to a sufficiently
high finite order: its even radial powers extend smoothly through the axis and its weighted
remainder gives arbitrary axial decay"), 2593-2595, 2607-2608.

Off the axis `U_raw(τ) = N_v(ringStreamProfile R Ψ)`, `Ψ` the train stream (`rawStreamProfile`).
* `s ≤ 1`: `nvDecayFar` and the transverse weights of the train at bounded ages
  (`PartIIIb.Concrete.TrainStreamWtdBdd`, SP 439-467 at fixed parameters).
* `s > 1` (`ϱ < R`): `U_raw = heatSum + N_v(ringStreamProfile R Φ_N)` (`Nv_heat_decomp`); the heat
  fields decay axially (`heatSumDec`), and the weighted remainder bound
  (`PartIIIb.Concrete.TrainHeatRemWtd`, SP 439-458) with `N = K + k + 3` absorbs `(1+s)^{K+1}`;
  `1+|y| ≤ (1+R)(1+|y₃|)` and `|y₃| ≤ |η|` on `ϱ ≤ R`.

The two train inputs are the fixed-parameter (one threshold `ν₀` for all orders) weighted forms of
`sct:fluctuation`, `sct:expansion`, `sct:transverse`; the Part I statements in Lean
(`TrainFluctuationDecay`, `TrainMeanExpansion`, `TrainTransverseTails`) have thresholds depending on
the derivative orders, which does not give one `ν₀` for every order `k`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.RawAndInletL4

open UnforcedLeray UnforcedLeray.Short.IIb

/-- `|y| ≤ ϱ + |y₃|`. -/
theorem norm_le_ϱ_add (y : Space) : ‖y‖ ≤ Axi.ϱ y + |y 2| := by
  have h := Axi.norm_sq_eq_ϱ_sq_add y
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg y, abs_nonneg (y 2), sq_abs (y 2), Axi.ϱ_nonneg y]

/-- **All-order inverse-distance decay of `U_raw`**, from the weighted fixed-parameter train
bounds: one threshold `ν₀`, and for every order `k` a constant `B` with
`(1+|y|)‖D^k U_raw(τ, y)‖ ≤ B` off the axis, for all `τ`. -/
theorem rawDecayAll_of (hS : PartIIIb.Concrete.TrainStreamWtdBdd)
    (hN : PartIIIb.Concrete.TrainHeatRemWtd) (dm dp : ℝ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (p : UnforcedLeray.Cons.C03.Concrete.Params) (d : ℝ),
      BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
        (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤ B := by
  obtain ⟨νS, hνS, HS⟩ := hS 2 (by norm_num)
  obtain ⟨νN, hνN, HN⟩ := hN 2 (by norm_num)
  refine ⟨min νS νN, lt_min hνS hνN, fun p d hreg hν k => ?_⟩
  have hν0 : 0 < p.ν := p.ν_pos
  have hνS' : p.ν ≤ νS := hν.trans (min_le_left _ _)
  have hνN' : p.ν ≤ νN := hν.trans (min_le_right _ _)
  have hc : p.c = UnforcedLeray.Short.PartI.trainPeriod 2 p.ν := by
    rw [hreg.c_eq]
    unfold UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν0.le, Real.rpow_two]
  have htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train := hreg.train_buc
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℝ × (ℝ × ℝ) → ℝ, Ψ = fun x => p.train.ψ x.1 x.2 := ⟨_, rfl⟩
  have hΨ : ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ univ) := by
    rw [hΨdef]; exact hreg.train_stream_smooth
  have hε1 : p.ε ≤ 1 := by
    have hd0 : 0 ≤ d := le_trans hreg.dm_pos.le hreg.dm_le
    rw [hreg.eps_eq, Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (div_nonneg hd0 hν0.le)
  have hR1 : 1 ≤ p.R := by
    show 1 ≤ p.ε⁻¹
    exact (one_le_inv₀ p.ε_pos).2 hε1
  have hR0 : 0 < p.R := lt_of_lt_of_le one_pos hR1
  -- far field constants
  obtain ⟨Cf, Kf, hCf0, Hf⟩ := nvDecayFar k
  have hSb : ∀ i : ℕ, ∃ C : ℝ, ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 → x.1 ≤ 1 →
      (1 + |x.2.2|) ^ (k + 2) * ‖iteratedFDeriv ℝ i Ψ x‖ ≤ C := by
    intro i
    rw [hΨdef]
    exact HS p.ν p.c hν0 hνS' hc p.train htr (k + 2) i 1
  choose CS hCS using hSb
  -- near field constants
  obtain ⟨Cn, Kn, hCn0, Hn⟩ := PartIIa.nv_jet_le_unif k
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = Kn + k + 3 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = UnforcedLeray.Short.PartI.meanCoeff p.train := ⟨_, rfl⟩
  obtain ⟨ΦN, hΦNdef⟩ : ∃ Φ : ℝ × (ℝ × ℝ) → ℝ, Φ = heatRemainder p.ν a N Ψ := ⟨_, rfl⟩
  have hNb : ∀ i : ℕ, ∃ C : ℝ, ∀ x : ℝ × (ℝ × ℝ), 1 ≤ x.1 →
      (1 + |x.2.2|) ^ (k + 2) * ‖iteratedFDeriv ℝ i ΦN x‖ ≤
        C * x.1 ^ (((k + 2 : ℕ) : ℝ) / 2 - N - 3 / 2) := by
    intro i
    rw [hΦNdef, ha, hΨdef]
    exact HN p.ν p.c hν0 hνN' hc p.train htr N (k + 2) i
  choose CN hCN using hNb
  obtain ⟨CH, hCH0, hCH⟩ := heatSumDec hν0 p.R a N (p.R ^ 2) k
  obtain ⟨SF, hSF⟩ : ∃ x : ℝ, x = ∑ i ∈ Finset.range (k + 2), |CS i| := ⟨_, rfl⟩
  obtain ⟨SN, hSN⟩ : ∃ x : ℝ, x = ∑ i ∈ Finset.range (k + 2), |CN i| := ⟨_, rfl⟩
  have hSF0 : 0 ≤ SF := by rw [hSF]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSN0 : 0 ≤ SN := by rw [hSN]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hfar0 : 0 ≤ Cf * (1 + 1 + p.R) ^ (Kf + 2) * SF := by positivity
  have hnear0 : 0 ≤ (1 + p.R) * CH + (1 + p.R) * Cn * 2 ^ (Kn + 1) * SN := by positivity
  refine ⟨Cf * (1 + 1 + p.R) ^ (Kf + 2) * SF +
    ((1 + p.R) * CH + (1 + p.R) * Cn * 2 ^ (Kn + 1) * SN), add_nonneg hfar0 hnear0,
    fun τ y hy => ?_⟩
  have hs : 0 < Axi.age p.R y := PartIIIb.Concrete.age_pos_of hR0 hy
  have hεR : p.ε = p.R⁻¹ := by
    show p.ε = (p.ε⁻¹)⁻¹
    rw [inv_inv]
  have hprof : ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
      UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ x =
        Axi.ringStreamProfile p.R Ψ x := by
    intro x hx
    rw [hεR, hΨdef]
    exact rawStreamProfile p.ν p.c p.R p.train hR0 hreg.train_stream_smooth x hx
  have hev : p.raw τ =ᶠ[𝓝 y] Axi.Nv p.R (Axi.ringStreamProfile p.R Ψ) τ := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
    have e1 : p.raw τ z =
        Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ z :=
      p.raw_eq_off_axis τ z hz
    rw [e1]
    unfold Axi.Nv
    rw [hprof (Axi.chart p.R τ z) (PartIIIb.Concrete.age_pos_of hR0 hz)]
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  have hη0 : 0 ≤ |Axi.trans p.R y| := abs_nonneg _
  by_cases hs1 : Axi.age p.R y ≤ 1
  · -- far field `s ≤ 1`
    have h1 := Hf p.R 1 Ψ hR1 zero_le_one hΨ τ y hy hs1
    have hsum : (1 + |Axi.trans p.R y|) ^ (k + 2) *
        ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Ψ (Axi.chart p.R τ y)‖ ≤ SF := by
      rw [Finset.mul_sum, hSF]
      refine Finset.sum_le_sum fun i _ => ?_
      exact (hCS i (Axi.chart p.R τ y) hs hs1).trans (le_abs_self _)
    have hfar : (1 + ‖y‖) *
        ‖iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R Ψ) τ) y‖ ≤
        Cf * (1 + 1 + p.R) ^ (Kf + 2) * SF :=
      h1.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    linarith
  · -- near field `s > 1`, `ϱ < R`
    push Not at hs1
    have hϱ0 : 0 < Axi.ϱ y := Axi.ϱ_pos hy
    have hϱ2 : Axi.ϱ y ^ 2 < p.R ^ 2 := by
      have h1 : 1 < p.R ^ 2 / Axi.ϱ y ^ 2 := hs1
      rw [lt_div_iff₀ (pow_pos hϱ0 2)] at h1
      linarith
    have hϱR : Axi.ϱ y ≤ p.R := by nlinarith
    have hy2 : |y 2| ≤ |Axi.trans p.R y| := by
      have e : |Axi.trans p.R y| = p.R * |y 2| / Axi.ϱ y := by
        unfold Axi.trans
        rw [abs_div, abs_mul, abs_of_pos hR0, abs_of_pos hϱ0]
      rw [e, le_div_iff₀ hϱ0]
      nlinarith [abs_nonneg (y 2)]
    have hny := norm_le_ϱ_add y
    have hw1 : 1 + ‖y‖ ≤ (1 + p.R) * (1 + |y 2|) := by
      nlinarith [abs_nonneg (y 2)]
    have hw2 : 1 + ‖y‖ ≤ (1 + p.R) * (1 + |Axi.trans p.R y|) := by
      nlinarith [abs_nonneg (y 2)]
    have hΦN : ContDiffOn ℝ ∞ ΦN (Ioi 0 ×ˢ univ) := by
      rw [hΦNdef]
      exact hΨ.sub (ContDiffOn.sum fun l _ => contDiffOn_const.mul (heatTermSmooth p.ν hν0 l))
    have hBN : ContDiffOn ℝ ∞ (Axi.ringStreamProfile p.R ΦN) (Ioi 0 ×ˢ univ) :=
      (PartIIIb.Concrete.ringProfileMeridJet p.R ΦN hΦN).1
    have hev2 : Axi.Nv p.R (Axi.ringStreamProfile p.R Ψ) τ =ᶠ[𝓝 y]
        PartIIIb.Concrete.heatSum p.ν p.R a N + Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ := by
      filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
      rw [hΦNdef]
      exact PartIIIb.Concrete.Nv_heat_decomp hν0 hR0 a N hΨ τ hz
    obtain ⟨CJ, KJ, hCJ, HJ⟩ := PartIIIb.Concrete.ringLiftPtJet k
    have hNvc : ContDiffAt ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y :=
      (((HJ p.R τ _ hR1 hBN).1).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le
        (by exact_mod_cast le_top)
    have hHc : ContDiffAt ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y :=
      (PartIIIb.Concrete.contDiff_heatSum p.ν p.R a N).contDiffAt.of_le
        (by exact_mod_cast le_top)
    rw [(hev2.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_add_apply hHc hNvc]
    -- heat part
    have hheat : (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖ ≤
        (1 + p.R) * CH := by
      calc (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖
          ≤ ((1 + p.R) * (1 + |y 2|)) *
              ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖ :=
            mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
        _ = (1 + p.R) * ((1 + |y 2|) *
              ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖) := by ring
        _ ≤ (1 + p.R) * CH := mul_le_mul_of_nonneg_left (hCH y hϱ2.le) (by linarith)
    -- remainder part
    have h2 := Hn p.R ΦN hR1 hΦN τ y hy
    set s := Axi.age p.R y with hsdef
    set η := |Axi.trans p.R y| with hηdef
    have hs1' : 1 ≤ s := hs1.le
    set e : ℝ := ((k + 2 : ℕ) : ℝ) / 2 - N - 3 / 2 with hedef
    have hrpow0 : 0 ≤ s ^ e := Real.rpow_nonneg hs.le _
    have hsumN : (1 + η) ^ (k + 2) *
        ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i ΦN (Axi.chart p.R τ y)‖ ≤ SN * s ^ e := by
      rw [Finset.mul_sum, hSN, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      exact (hCN i (Axi.chart p.R τ y) hs1').trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) hrpow0)
    have he : e ≤ -((Kn + 1 : ℕ) : ℝ) := by
      rw [hedef, hNdef]; push_cast; linarith
    have hpow : (1 + s) ^ (Kn + 1) * s ^ e ≤ 2 ^ (Kn + 1) := by
      have h2s : (1 + s) ^ (Kn + 1) ≤ 2 ^ (Kn + 1) * s ^ (Kn + 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith) _
      have hle1 : s ^ (Kn + 1) * s ^ e ≤ 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hs]
        exact Real.rpow_le_one_of_one_le_of_nonpos hs1' (by push_cast at he ⊢; linarith)
      calc (1 + s) ^ (Kn + 1) * s ^ e ≤ 2 ^ (Kn + 1) * s ^ (Kn + 1) * s ^ e :=
            mul_le_mul_of_nonneg_right h2s hrpow0
        _ = 2 ^ (Kn + 1) * (s ^ (Kn + 1) * s ^ e) := by ring
        _ ≤ 2 ^ (Kn + 1) * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ = 2 ^ (Kn + 1) := mul_one _
    have hrem : (1 + ‖y‖) *
        ‖iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖ ≤
        (1 + p.R) * Cn * 2 ^ (Kn + 1) * SN := by
      have hS0 : 0 ≤ ∑ i ∈ Finset.range (k + 2),
          ‖iteratedFDeriv ℝ i ΦN (Axi.chart p.R τ y)‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc (1 + ‖y‖) *
            ‖iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖
          ≤ ((1 + p.R) * (1 + η)) * (Cn * (1 + s) ^ (Kn + 1) * ((1 + η) ^ (k + 1) *
              ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i ΦN (Axi.chart p.R τ y)‖)) :=
            mul_le_mul hw2 h2 (norm_nonneg _) (by positivity)
        _ = (1 + p.R) * Cn * (1 + s) ^ (Kn + 1) * ((1 + η) ^ (k + 2) *
              ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i ΦN (Axi.chart p.R τ y)‖) := by
            ring
        _ ≤ (1 + p.R) * Cn * (1 + s) ^ (Kn + 1) * (SN * s ^ e) :=
            mul_le_mul_of_nonneg_left hsumN (by positivity)
        _ = (1 + p.R) * Cn * SN * ((1 + s) ^ (Kn + 1) * s ^ e) := by ring
        _ ≤ (1 + p.R) * Cn * SN * 2 ^ (Kn + 1) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (1 + p.R) * Cn * 2 ^ (Kn + 1) * SN := by ring
    have hy0 : 0 ≤ 1 + ‖y‖ := by positivity
    calc (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y +
          iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖
        ≤ (1 + ‖y‖) * (‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖ +
            ‖iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hy0
      _ = (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖ +
            (1 + ‖y‖) *
              ‖iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖ := by ring
      _ ≤ (1 + p.R) * CH + (1 + p.R) * Cn * 2 ^ (Kn + 1) * SN := add_le_add hheat hrem
      _ ≤ _ := le_add_of_nonneg_left hfar0

end UnforcedLeray.Short.IIb.RawAndInletL4
