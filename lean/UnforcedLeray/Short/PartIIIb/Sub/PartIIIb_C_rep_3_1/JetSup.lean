import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_1
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Norm

/-!
# `PartIII-b:C/rep/3/1/1`: `sepJetPointwiseSup` (`SepJetPointwiseSup`)

Source of record: `the November 2 reference manuscript` (73 pages), lines
3603-3629 (`sep:kernel`, `sep:resolvent`), 5203-5210, 5238-5244.

For `0 ≤ rOut < rIn` and any `(τ, y)`, we combine `IIIa.sepWDominated` / `IIIa.sepKernelBounds`
with Hölder's inequality in `z` with exponents `(22/3, 22/19)` (`IIIa.kernelNorm`) and
`periodicDilationSum_proved` over `l ∈ (0, 1)` to bound `wgxJet j` (`j ≤ 2`) and `wgyWJet j`
(`j ≤ 1`) uniformly in `(τ, y)` by `(rIn - rOut) ^ (-4 - j + 9/22) * ‖T‖_{L²_τ L^{22/19}}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise `L^∞_{τ,y}` bound on the scalar dilation majorant `IIIa.sepDom` via Hölder `(22/3, 22/19)`
in `z` (`IIIa.kernelNorm`) and `periodicDilationSum_proved` in `l ∈ (0, 1)`. -/
theorem sepDomPointwiseSup (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : ℝ, (9 / 22 : ℝ) ≤ a →
        ∀ D P : ℝ, 0 < D → 0 < P → P ≤ 1 →
          ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
            (∀ τ z, g (τ + P) z = g τ z) →
            ∀ (τ : ℝ) (y : Space),
              IIIa.sepDom a j D g τ y ≤
                ENNReal.ofReal (C * D ^ (-4 - (j : ℝ) + 9 / 22)) *
                  IIIa.ltauLq P (22 / 19) g := by
  have hb1 : (1 : ℝ) < 22 / 3 := by norm_num
  have hb0 : (0 : ℝ) < 22 / 3 := by norm_num
  have hconj : (22 / 3 : ℝ).HolderConjugate (22 / 19) :=
    Real.holderConjugate_iff.mpr ⟨hb1, by norm_num⟩
  set I1 : ℝ≥0∞ := ∫⁻ x : Space, IIIa.sepKd j 1 x ^ (22 / 3 : ℝ) with hI1
  have hI1top : I1 ≠ ⊤ := IIIa.lintegral_sepKd_rpow_one_ne_top j (22 / 3) hb1
  obtain ⟨Cs, hCs, hS⟩ := periodicDilationSum_proved 1 one_pos
  refine ⟨I1.toReal ^ (1 / (22 / 3 : ℝ)) * Cs, by positivity, ?_⟩
  intro a ha D P hD hP hP1 g hgm hgper τ y
  have hc : (1 : ℝ) - 1 ≤ a - 3 / (22 / 3 : ℝ) := by linarith
  obtain ⟨G, hGdef⟩ :
      ∃ G : ℝ → ℝ≥0∞, ∀ s, G s = (∫⁻ z, g s z ^ (22 / 19 : ℝ)) ^ (1 / (22 / 19 : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  have hGm : Measurable G := by
    have h1 : Measurable fun q : ℝ × Space => g q.1 q.2 ^ (22 / 19 : ℝ) :=
      hgm.pow_const (22 / 19 : ℝ)
    have h2 := h1.lintegral_prod_right' (ν := (volume : Measure Space))
    have : G = fun s => (∫⁻ z, g s z ^ (22 / 19 : ℝ)) ^ (1 / (22 / 19 : ℝ)) := funext hGdef
    rw [this]
    exact h2.pow_const _
  have hGper : ∀ s, G (s + P) = G s := by
    intro s; rw [hGdef, hGdef]; simp only [hgper]
  have hGL : IIIa.ltauAt P G = IIIa.ltauLq P (22 / 19) g := by
    unfold IIIa.ltauAt IIIa.ltauLq
    have : ∀ s, G s ^ (2 : ℝ) = (∫⁻ z, g s z ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) := fun s => by
      rw [hGdef, ← ENNReal.rpow_mul]; congr 1; ring
    simp_rw [this]
  set M : ℝ≥0∞ :=
    ENNReal.ofReal (D ^ (-4 - (j : ℝ) + 3 / (22 / 3 : ℝ))) * I1 ^ (1 / (22 / 3 : ℝ)) with hM
  have hMtop : M ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hI1top)
  have hslice : ∫⁻ l in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (l ^ a) *
        ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z ≤
      ∫⁻ l in Ioo (0 : ℝ) 1,
        M * (ENNReal.ofReal (l ^ (a - 3 / (22 / 3 : ℝ))) * G (τ + 2 * Real.log l)) := by
    refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
    have hf : AEMeasurable (fun z : Space => IIIa.sepKd j D (y - l • z)) volume :=
      ((IIIa.sepKd_measurable j D).comp
        (measurable_const.sub (measurable_const_smul l))).aemeasurable
    have hg : AEMeasurable (g (τ + 2 * Real.log l)) volume :=
      (hgm.comp (measurable_prodMk_left (x := τ + 2 * Real.log l))).aemeasurable
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hf hg
    have hH' : ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z ≤
        (∫⁻ z : Space, IIIa.sepKd j D (y - l • z) ^ (22 / 3 : ℝ)) ^ (1 / (22 / 3 : ℝ)) *
          G (τ + 2 * Real.log l) := by
      rw [hGdef]; exact hH
    calc ENNReal.ofReal (l ^ a) *
          ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z
        ≤ ENNReal.ofReal (l ^ a) *
            ((∫⁻ z : Space, IIIa.sepKd j D (y - l • z) ^ (22 / 3 : ℝ)) ^ (1 / (22 / 3 : ℝ)) *
              G (τ + 2 * Real.log l)) := by gcongr
      _ = M * (ENNReal.ofReal (l ^ (a - 3 / (22 / 3 : ℝ))) * G (τ + 2 * Real.log l)) := by
        have hk : (∫⁻ z : Space, IIIa.sepKd j D (y - l • z) ^ (22 / 3 : ℝ)) ^ (1 / (22 / 3 : ℝ)) =
            ENNReal.ofReal (l ^ (-(3 / (22 / 3 : ℝ)))) * M :=
          IIIa.kernelNorm j D (22 / 3) hD hb0 y l hl.1
        rw [hk, sub_eq_add_neg, Real.rpow_add hl.1,
          ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _)]
        ring
  have hI : I1 ^ (1 / (22 / 3 : ℝ)) = ENNReal.ofReal (I1.toReal ^ (1 / (22 / 3 : ℝ))) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hI1top]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity)]
  have hexp : (-4 - (j : ℝ) + 3 / (22 / 3 : ℝ)) = -4 - (j : ℝ) + 9 / 22 := by ring
  calc IIIa.sepDom a j D g τ y
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1,
          M * (ENNReal.ofReal (l ^ (a - 3 / (22 / 3 : ℝ))) * G (τ + 2 * Real.log l)) := hslice
    _ = M * ∫⁻ l in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (l ^ (a - 3 / (22 / 3 : ℝ))) * G (τ + 2 * Real.log l) :=
        lintegral_const_mul' M _ hMtop
    _ ≤ M * (ENNReal.ofReal Cs * IIIa.ltauAt P G) :=
        mul_le_mul_of_nonneg_left (hS _ hc P hP hP1 G hGm hGper τ) zero_le
    _ = ENNReal.ofReal (I1.toReal ^ (1 / (22 / 3 : ℝ)) * Cs * D ^ (-4 - (j : ℝ) + 9 / 22)) *
          IIIa.ltauLq P (22 / 19) g := by
        rw [hGL, hM, hI, hexp, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- Pointwise `L^∞_{τ,y}` bound on `IIIa.wDerivNorm ν m T j τ y` for `rIn ≤ ϱ y` and `m.re > -1/4`. -/
theorem wDerivNorm_pointwiseSup (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ν : ℝ), 0 < ν → ∀ (m : ℂ), -(1 / 4 : ℝ) < m.re →
        ∀ (rOut rIn P : ℝ), 0 ≤ rOut → rOut < rIn → 0 < P → P ≤ 1 →
          ∀ T, IIIa.IsSepSource P rOut T →
            ∀ (τ : ℝ) (y : Space), rIn ≤ ϱ y →
              IIIa.wDerivNorm ν m T j τ y ≤
                ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
                  IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
  obtain ⟨C0, hC0, hDom⟩ := IIIa.sepWDominated IIIa.sepKernelBounds j
  obtain ⟨Cb, hCb, hB⟩ := sepDomPointwiseSup j
  obtain ⟨Cz, hCz, hBz⟩ := sepDomPointwiseSup 0
  refine ⟨C0 * Cb + 1, by positivity, ?_⟩
  intro ν hν m hm rOut rIn P hrO hrr hP hP1 T hT τ y hy
  have hD : 0 < rIn - rOut := sub_pos.2 hrr
  have hpos : 0 < (C0 * Cb + 1) * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22) :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos hD _)
  by_cases htop : IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  have ha : (9 / 22 : ℝ) ≤ 2 * m.re + 2 := by linarith
  have hgm := IIIa.sepAE_measurable_srcNorm hT
  have hper : ∀ s z, IIIa.srcNorm T (s + P) z = IIIa.srcNorm T s z := by
    intro s z; unfold IIIa.srcNorm; rw [hT.periodic]
  have h0lt : IIIa.sepDom (2 * m.re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ :=
    (hBz _ ha _ P hD hP hP1 _ hgm hper τ y).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 htop))
  have hy' : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hy
  calc IIIa.wDerivNorm ν m T j τ y
      ≤ ENNReal.ofReal C0 *
          IIIa.sepDom (2 * m.re + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y :=
        hDom ν hν m hm rOut rIn P hrO hrr hP T hT τ y hy' h0lt
    _ ≤ ENNReal.ofReal C0 *
          (ENNReal.ofReal (Cb * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) :=
        mul_le_mul_of_nonneg_left (hB _ ha _ P hD hP hP1 _ hgm hper τ y) zero_le
    _ = ENNReal.ofReal (C0 * Cb * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC0, mul_assoc]
    _ ≤ ENNReal.ofReal ((C0 * Cb + 1) * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
        gcongr
        linarith

/-- **Leaf 1 (`PartIII-b:C/rep/3/1/1`): pointwise `L^∞_{τ,y}` bounds on `wgxJet` and `wgyWJet`**
(source 3603-3629, 5203-5210, 5238-5244). -/
theorem sepJetPointwiseSup : SepJetPointwiseSup := by
  intro σ₁ σ₂ hσ j hj
  obtain ⟨Cw, hCw, hW⟩ := wDerivNorm_pointwiseSup j
  refine ⟨‖reL‖ * (Cw + Cw), by positivity, ?_⟩
  intro ν μ rOut rIn P hν hμ hrO hrr hP hP1 T hT hS τ y
  have hμre : -(1 / 4 : ℝ) < μ := lt_of_lt_of_le hσ hμ.1
  have hm1re : -(1 / 4 : ℝ) < ((μ : ℂ)).re := by simpa using hμre
  have hm2re : -(1 / 4 : ℝ) < ((μ : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hU : IsOpen {z : Space | rOut < ϱ z} := isOpen_lt continuous_const continuous_ϱ
  have hDnn : 0 ≤ (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22) :=
    Real.rpow_nonneg (sub_pos.2 hrr).le _
  have ht : 0 ≤ Cw * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22) := mul_nonneg hCw hDnn
  refine ⟨?_, fun _ => ?_⟩
  · by_cases h : rIn ≤ ϱ y
    · have hyU : y ∈ {z : Space | rOut < ϱ z} := lt_of_lt_of_le hrr h
      have hW1 : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {z : Space | rOut < ϱ z} :=
        contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν
          hm1re hrO hP hT hS τ i)
      have hW2 : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)
          {z : Space | rOut < ϱ z} :=
        contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T
          hν hm2re hrO hP hT hS τ i)
      have key := iteratedFDeriv_reL_le hU hW1 hW2 hj hyU
      have b1 := hW ν hν (μ : ℂ) hm1re rOut rIn P hrO hrr hP hP1 T hT τ y h
      have b2 := hW ν hν ((μ : ℂ) + 1) hm2re rOut rIn P hrO hrr hP hP1 T hT τ y h
      unfold wgxJet
      rw [if_pos h, sepX0_eq_reL]
      calc ‖iteratedFDeriv ℝ j (fun z => reL (IIIa.sepW ν (μ : ℂ) T z τ -
              IIIa.sepW ν ((μ : ℂ) + 1) T z τ)) y‖ₑ
          ≤ ENNReal.ofReal ‖reL‖ *
              (IIIa.wDerivNorm ν (μ : ℂ) T j τ y +
                IIIa.wDerivNorm ν ((μ : ℂ) + 1) T j τ y) := key
        _ ≤ ENNReal.ofReal ‖reL‖ *
              (ENNReal.ofReal (Cw * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) +
                ENNReal.ofReal (Cw * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) :=
            mul_le_mul_of_nonneg_left (add_le_add b1 b2) zero_le
        _ = ENNReal.ofReal (‖reL‖ * (Cw + Cw) * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
              IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
            rw [← add_mul, ← ENNReal.ofReal_add ht ht, ← mul_assoc,
              ← ENNReal.ofReal_mul (norm_nonneg _)]
            congr 2
            ring
    · unfold wgxJet
      rw [if_neg h]
      exact zero_le
  · by_cases h : rIn ≤ ϱ y
    · have hyU : rOut < ϱ y := lt_of_lt_of_le hrr h
      have key := wgy_jet_le hν hμre hrO hP hT hS τ hj hyU
      have b1 := hW ν hν (μ : ℂ) hm1re rOut rIn P hrO hrr hP hP1 T hT τ y h
      unfold wgyWJet
      rw [if_pos h]
      calc ‖iteratedFDeriv ℝ j (sepWre ν μ T τ) y‖ₑ
          ≤ ENNReal.ofReal ‖reL‖ * IIIa.wDerivNorm ν (μ : ℂ) T j τ y := key
        _ ≤ ENNReal.ofReal ‖reL‖ *
              (ENNReal.ofReal (Cw * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) :=
            mul_le_mul_of_nonneg_left b1 zero_le
        _ = ENNReal.ofReal (‖reL‖ * Cw * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
              IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), mul_assoc]
        _ ≤ ENNReal.ofReal (‖reL‖ * (Cw + Cw) * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 22)) *
              IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
            gcongr
            linarith
    · unfold wgyWJet
      rw [if_neg h]
      exact zero_le

end UnforcedLeray.Short.PartIIIb.Concrete

end
