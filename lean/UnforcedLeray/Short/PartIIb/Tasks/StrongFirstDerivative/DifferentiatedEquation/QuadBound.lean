import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.DifferentiatedEquation.QuadBound.InletBounds
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.DifferentiatedEquation.QuadBound.FieldLp
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.DifferentiatedEquation.QuadBound.Norm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuad
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.Main
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# `PartII-b:S1/1/2`: `DiffEqQuadBound` (SP 2528-2534, 2395-2405)

Source of record `the November 2 reference manuscript`.

For `u = e + w` (`e = E_bg α` the affine inlet, `w = wOf z`), the differentiated quadratic term
`⟨∂_jΦ, gQ⟩ = -⟨(u·∇)∂_jΦ, u⟩` is represented on solenoidal tests by the field
`F = -∑_k ∂_j∂_k(u_k u)` (`GEQuadField`, `gEQIbp`), which lies in `Y_{q₀}` (`gEQFieldCell_of_inlet`,
`periodicFieldToYq_proof`).  Its norm is bounded as in SP 2528-2531:
`|F| ≤ ∑_k (2|D²u||u| + |D_ku|² + |D_ju|²)`, `‖Dw‖²_{Y_{2q₀}} ≤ C‖w‖_∞‖D²w‖_{Y_{q₀}}`
(`gradL2pIBP`), with the quantitative bounds `‖w‖_∞ ≲ ν⁻¹‖z‖` (`rep_wOf_ae_bound`),
`‖D²w‖_{Y_{q₀}} ≲ ν⁻¹‖z‖` (`grad_and_hess_bound_of_geData`), and on the inlet
`‖e‖_∞ + ‖De‖_∞ ≲ ν^{-k}‖z‖` (`inlet_sup_le`), `‖De‖_{Y_{q₀}} ≲ ν^{-k}‖z‖`
(`inlet_dy_phaseLpNorm_le`), `‖D²e‖_{Y_{q₀}} ≲ ν^{-k}‖z‖` (`inlet_dydy_phaseLpNorm_le`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.B0412 (q0E q0E_ne_top)

theorem diffEqQuadBound_proof : UnforcedLeray.Short.IIb.DiffEqQuadBound := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C_GH, hC_GH, HGH⟩ := DiffEqSub.grad_and_hess_bound_of_geData
  obtain ⟨C_w, hC_w, Hw⟩ := rep_wOf_ae_bound
  obtain ⟨Cs, ks, νs, hCs, hνs, hνs1, Hs⟩ := QuadBoundSub.inlet_sup_le Sig lam q hSig hq dm dp hdm
  obtain ⟨Cd, kd, νd, hCd, hνd, hνd1, Hd⟩ := inlet_dy_phaseLpNorm_le Sig lam q hSig hq dm dp hdm
  obtain ⟨Ch, kh, νh, hCh, hνh, hνh1, Hh⟩ :=
    QuadBoundSub.inlet_dydy_phaseLpNorm_le Sig lam q hSig hq dm dp hdm
  obtain ⟨νC, hνC, HC⟩ := UnforcedLeray.Short.PartIIIb.Concrete.gEQFieldCell_of_inlet
    UnforcedLeray.Short.PartIIIb.Concrete.gEQInletGlobal lam q hq dm dp hdm
  obtain ⟨νI, hνI, HI⟩ := UnforcedLeray.Short.PartIIIb.Concrete.gEQIbp lam q hq dm dp hdm
  obtain ⟨kK, hkK⟩ : ∃ kK : ℕ, kK = ks + kd + kh + 1 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Cs + C_w + Ch + Cd + C_GH := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  refine ⟨186 * A ^ 2, 2 * kK, min (min (min νs νd) (min νh νC)) (min νI (dm ^ 3 / 12)),
    by positivity, lt_min (lt_min (lt_min hνs hνd) (lt_min hνh hνC)) (lt_min hνI (by positivity)),
    ?_⟩
  intro p d hreg hν hS hm z g₀ h gQ hd hh hQ j
  have hνs' : p.ν ≤ νs :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hνd' : p.ν ≤ νd :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hνh' : p.ν ≤ νh :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνC' : p.ν ≤ νC :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hνI' : p.ν ≤ νI := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνdm : p.ν ≤ dm ^ 3 / 12 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hνs'.trans hνs1
  have hνpos : 0 < p.ν := p.ν_pos
  have hP1 : p.period ≤ 1 := UnforcedLeray.Short.PartIIIb.Concrete.bgCorr_period_le_one hreg hνdm
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  -- the inlet is smooth
  have he : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine UnforcedLeray.Short.PartIIIb.Concrete.contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (UnforcedLeray.Short.PartIIIb.Concrete.inlet_contDiff_joint lam q hq hreg hν1 hm
      l).const_smul _
  -- bounds on `w`
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = C_w * (p.ν ^ 1)⁻¹ * ‖z‖ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hMw : ∀ᵐ x ∂(UnforcedLeray.Short.PartIIIb.Concrete.phaseμ p.period),
      ‖rep (p.wOf z) x.1 x.2‖ ≤ M := by
    rw [hMdef]; exact Hw p hP1 hν1 z
  have hGL := UnforcedLeray.Short.PartIIIb.Concrete.gradL2pIBP p.period (p.wOf z) g₀ h M hM0 hMw
    hd.2 hh
  have hyp : UnforcedLeray.Short.PartIIIb.Concrete.GEQHyp p z g₀ h := ⟨hh, fun k => (hGL k).1⟩
  obtain ⟨hGm, hGper, hGfin⟩ := HC p d hreg hνC' hm z g₀ hd h hyp j
  obtain ⟨F, hF⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof q0E q0E_ne_top p.period _
    hGm hGper hGfin
  refine ⟨F, ?_, ?_⟩
  · -- the pairing identity
    intro Φ hΦ
    have hΨ := UnforcedLeray.Short.PartIIIb.Concrete.gEW_isSolTest_dy hΦ j
    have hpairF : phasePair p.period q0E Φ F =
        pairF p.period Φ (UnforcedLeray.Short.PartIIIb.Concrete.GEQuadField p z g₀ h j) := by
      have hae : ∀ᵐ τ : ℝ,
          (fun y => UnforcedLeray.Short.PartIIIb.Concrete.GEQuadField p z g₀ h j (τ, y)) =ᵐ[volume]
            (fun y => rep F τ y) := by
        filter_upwards [hF.slice] with τ hτ
        exact hτ.trans (rep_slice F τ).symm
      have hint : ∀ᵐ τ : ℝ, ∫ y, dotL (Φ (τ, y)) (rep F τ y) =
          ∫ y, dotL (Φ (τ, y))
            (UnforcedLeray.Short.PartIIIb.Concrete.GEQuadField p z g₀ h j (τ, y)) := by
        filter_upwards [hae] with τ hτ
        apply integral_congr_ae
        filter_upwards [hτ] with y hy
        exact congrArg (dotL (Φ (τ, y))) hy.symm
      rw [phasePair_eq_pairF_rep hΦ.1 F]
      unfold pairF phaseInt
      congr 1
      apply setIntegral_congr_ae measurableSet_Ioc
      filter_upwards [hint] with τ hτ _
      exact hτ
    rw [hQ (dy j Φ) hΨ, hpairF, HI p d hreg hνI' hm z g₀ hd h hyp j Φ hΦ.1, neg_neg]
  · -- the norm bound
    set c : ℝ≥0∞ := ENNReal.ofReal p.period ^ (1 / q0E.toReal) with hc
    have hc0 : c ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 p.period_pos) ENNReal.ofReal_ne_top).ne'
    have hctop : c ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    have hFn : eLpNorm (UnforcedLeray.Short.PartIIIb.Concrete.GEQuadField p z g₀ h j) q0E
        (UnforcedLeray.Short.PartIIIb.Concrete.phaseμ p.period) = c * ‖F‖ₑ :=
      QuadBoundSub.eLpNorm_phaseμ_rep hF
    obtain ⟨hGb, hHb⟩ := HGH p hP1 hν1 z g₀ h hd hh
    -- the constants
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Cs * (p.ν ^ ks)⁻¹ * ‖z‖ := ⟨_, rfl⟩
    obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = L + M := ⟨_, rfl⟩
    obtain ⟨Bhh, hBhhdef⟩ : ∃ B : ℝ, B = Ch * (p.ν ^ kh)⁻¹ * ‖z‖ := ⟨_, rfl⟩
    obtain ⟨Bde, hBdedef⟩ : ∃ B : ℝ, B = Cd * (p.ν ^ kd)⁻¹ * ‖z‖ := ⟨_, rfl⟩
    obtain ⟨Cg, hCgdef⟩ : ∃ B : ℝ, B = C_GH * (p.ν ^ 1)⁻¹ * ‖z‖ := ⟨_, rfl⟩
    obtain ⟨KM, hKMdef⟩ : ∃ B : ℝ, B = (2 * q0E.toReal - 1) * M * (3 * Cg) := ⟨_, rfl⟩
    have hq0r : q0E.toReal = 11 / 4 := UnforcedLeray.B0412.q0E_toReal
    have hL0 : 0 ≤ L := by rw [hLdef]; positivity
    have hU0 : 0 ≤ U := by rw [hUdef]; positivity
    have hBhh0 : 0 ≤ Bhh := by rw [hBhhdef]; positivity
    have hBde0 : 0 ≤ Bde := by rw [hBdedef]; positivity
    have hCg0 : 0 ≤ Cg := by rw [hCgdef]; positivity
    have hKM0 : 0 ≤ KM := by rw [hKMdef, hq0r]; positivity
    have hU : ∀ᵐ x ∂(UnforcedLeray.Short.PartIIIb.Concrete.phaseμ p.period), ‖p.uOf z x‖ ≤ U := by
      filter_upwards [hMw] with x hx
      calc ‖p.uOf z x‖ ≤ ‖p.eFun (p.coord z) x‖ + ‖rep (p.wOf z) x.1 x.2‖ := norm_add_le _ _
        _ ≤ L + M := add_le_add (by rw [hLdef]; exact (Hs p d hreg hνs' hS hm z x).1) hx
        _ = U := hUdef.symm
    have hL : ∀ (k : Fin 3) (x : ℝ × Space), ‖dy k (p.eFun (p.coord z)) x‖ ≤ L := by
      intro k x; rw [hLdef]; exact (Hs p d hreg hνs' hS hm z x).2 k
    have hhh : ∀ k : Fin 3, eLpNorm (dy k (dy j (p.eFun (p.coord z)))) q0E
        (UnforcedLeray.Short.PartIIIb.Concrete.phaseμ p.period) ≤ c * ENNReal.ofReal Bhh := by
      intro k
      rw [hBhhdef]
      exact QuadBoundSub.eLpNorm_le_of_phaseLpNorm p.period_pos
        (contDiff_dy (contDiff_dy he j) k).continuous.aestronglyMeasurable
        (Hh p d hreg hνh' hS hm z k j)
    have hrepH : ∀ k l : Fin 3, eLpNorm (fun x : ℝ × Space => rep (h k l) x.1 x.2) q0E
        (UnforcedLeray.Short.PartIIIb.Concrete.phaseμ p.period) ≤ c * ENNReal.ofReal Cg := by
      intro k l
      rw [QuadBoundSub.eLpNorm_phaseμ_rep_self, ← ofReal_norm]
      gcongr
      rw [hCgdef]
      exact hHb k l
    have hde : ∀ k : Fin 3, eLpNorm (dy k (p.eFun (p.coord z))) q0E
        (UnforcedLeray.Short.PartIIIb.Concrete.phaseμ p.period) ≤ c * ENNReal.ofReal Bde := by
      intro k
      rw [hBdedef]
      exact QuadBoundSub.eLpNorm_le_of_phaseLpNorm p.period_pos
        (contDiff_dy he k).continuous.aestronglyMeasurable (Hd p d hreg hνd' hS hm z k)
    have hg2 : ∀ k : Fin 3, eLpNorm (fun x : ℝ × Space => ‖rep (g₀ k) x.1 x.2‖ ^ 2) q0E
        (UnforcedLeray.Short.PartIIIb.Concrete.phaseμ p.period) ≤ c * ENNReal.ofReal KM := by
      intro k
      have e1 : (fun x : ℝ × Space => ‖rep (g₀ k) x.1 x.2‖ ^ 2) =
          fun x => ‖rep (g₀ k) x.1 x.2‖ ^ (2 : ℝ) := by
        funext x; rw [Real.rpow_two]
      rw [e1, eLpNorm_norm_rpow _ (by norm_num : (0 : ℝ) < 2)]
      have e2 : q0E * ENNReal.ofReal 2 = 2 * q0E := by rw [ENNReal.ofReal_ofNat, mul_comm]
      rw [e2, ENNReal.rpow_two]
      refine (hGL k).2.trans ?_
      have hsum : ∑ l : Fin 3, eLpNorm (fun x : ℝ × Space => rep (h k l) x.1 x.2) q0E
          (UnforcedLeray.Short.PartIIIb.Concrete.phaseμ p.period) ≤
          ∑ _l : Fin 3, c * ENNReal.ofReal Cg := Finset.sum_le_sum fun l _ => hrepH k l
      have hco : 0 ≤ (2 * q0E.toReal - 1) * M := by rw [hq0r]; positivity
      calc ENNReal.ofReal ((2 * q0E.toReal - 1) * M) *
            ∑ l : Fin 3, eLpNorm (fun x : ℝ × Space => rep (h k l) x.1 x.2) q0E
              (UnforcedLeray.Short.PartIIIb.Concrete.phaseμ p.period)
          ≤ ENNReal.ofReal ((2 * q0E.toReal - 1) * M) * ∑ _l : Fin 3, c * ENNReal.ofReal Cg := by
            gcongr
        _ = c * ENNReal.ofReal KM := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hKMdef,
              ENNReal.ofReal_mul hco, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
            simp only [Nat.cast_ofNat, ENNReal.ofReal_ofNat]
            ring
    have hmain := QuadBoundSub.quadField_eLpNorm_le p z g₀ h j he c hU0 hL0 hBhh0 hBde0 hCg0 hKM0
      hU hL hhh (fun k => hrepH k j) hde hg2
    rw [hFn] at hmain
    set T : ℝ := 3 * (2 * U * Bhh + 2 * U * Cg + 2 * L * Bde + 2 * KM + 2 * L * Bde + 2 * KM)
      with hT
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    have hFT : ‖F‖ ≤ T := by
      have h4 : ‖F‖ₑ ≤ ENNReal.ofReal T := (ENNReal.mul_le_mul_iff_right hc0 hctop).1 hmain
      rw [← ofReal_norm] at h4
      exact (ENNReal.ofReal_le_ofReal_iff hT0).1 h4
    refine hFT.trans ?_
    -- the polynomial bound
    set u : ℝ := p.ν⁻¹ with hu
    have hu1 : 1 ≤ u := by rw [hu]; exact (one_le_inv₀ hνpos).2 hν1
    have hpow : ∀ m : ℕ, (p.ν ^ m)⁻¹ = u ^ m := fun m => by rw [hu, inv_pow]
    have hle : ∀ m : ℕ, m ≤ kK → u ^ m ≤ u ^ kK := fun m hm' => pow_le_pow_right₀ hu1 hm'
    obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = u ^ kK * ‖z‖ := ⟨_, rfl⟩
    have hX0 : 0 ≤ X := by rw [hXdef]; positivity
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have bnd : ∀ (C0 : ℝ) (m : ℕ), 0 ≤ C0 → m ≤ kK → C0 ≤ A →
        C0 * (p.ν ^ m)⁻¹ * ‖z‖ ≤ A * X := by
      intro C0 m hC0 hm' hCA
      rw [hpow, hXdef]
      have := hle m hm'
      calc C0 * u ^ m * ‖z‖ ≤ A * u ^ kK * ‖z‖ := by gcongr
        _ = A * (u ^ kK * ‖z‖) := by ring
    have hLb : L ≤ A * X := by
      rw [hLdef]; exact bnd Cs ks hCs.le (by omega) (by rw [hA]; linarith)
    have hMb : M ≤ A * X := by
      rw [hMdef]; exact bnd C_w 1 hC_w.le (by omega) (by rw [hA]; linarith)
    have hUb : U ≤ A * X := by
      rw [hUdef, hLdef, hMdef]
      have h3 : Cs * (p.ν ^ ks)⁻¹ * ‖z‖ + C_w * (p.ν ^ 1)⁻¹ * ‖z‖ ≤ (Cs + C_w) * X := by
        rw [hpow, hpow, hXdef]
        have e1 := hle ks (by omega)
        have e2 := hle 1 (by omega)
        calc Cs * u ^ ks * ‖z‖ + C_w * u ^ 1 * ‖z‖ ≤ Cs * u ^ kK * ‖z‖ + C_w * u ^ kK * ‖z‖ := by
              gcongr
          _ = (Cs + C_w) * (u ^ kK * ‖z‖) := by ring
      refine h3.trans ?_
      have : Cs + C_w ≤ A := by rw [hA]; linarith
      exact mul_le_mul_of_nonneg_right this hX0
    have hBhhb : Bhh ≤ A * X := by
      rw [hBhhdef]; exact bnd Ch kh hCh.le (by omega) (by rw [hA]; linarith)
    have hBdeb : Bde ≤ A * X := by
      rw [hBdedef]; exact bnd Cd kd hCd.le (by omega) (by rw [hA]; linarith)
    have hCgb : Cg ≤ A * X := by
      rw [hCgdef]; exact bnd C_GH 1 hC_GH.le (by omega) (by rw [hA]; linarith)
    have hKMb : KM ≤ 27 / 2 * ((A * X) * (A * X)) := by
      rw [hKMdef, hq0r]
      have hAX : 0 ≤ A * X := by positivity
      calc (2 * (11 / 4 : ℝ) - 1) * M * (3 * Cg) = 27 / 2 * (M * Cg) := by ring
        _ ≤ 27 / 2 * ((A * X) * (A * X)) := by gcongr
    have hAX : 0 ≤ A * X := by positivity
    calc T = 3 * (2 * U * Bhh + 2 * U * Cg + 2 * L * Bde + 2 * KM + 2 * L * Bde + 2 * KM) := hT
      _ ≤ 3 * (2 * (A * X) * (A * X) + 2 * (A * X) * (A * X) + 2 * (A * X) * (A * X) +
            2 * (27 / 2 * ((A * X) * (A * X))) + 2 * (A * X) * (A * X) +
            2 * (27 / 2 * ((A * X) * (A * X)))) := by gcongr
      _ = 186 * A ^ 2 * (u ^ kK * ‖z‖) ^ 2 := by rw [hXdef]; ring
      _ = 186 * A ^ 2 * (p.ν ^ (2 * kK))⁻¹ * ‖z‖ ^ 2 := by
          rw [hpow]; ring

end UnforcedLeray.Short.IIb
