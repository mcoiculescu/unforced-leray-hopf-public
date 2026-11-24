import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Seq

/-!
# `PLBound` for the concrete return sequence (source 5883-5891)

Source of record: `the November 2 reference manuscript` (73 pages), lines 5883-5891
(`closure:source-and-extraction`).

For `S = concreteReturnSeq D G`:
* `‖𝒫‖_{𝒜 → 𝓔_ν} ≤ C ν_n^{-k} e^{1.1a_s/ν_n}` from `𝒫 = 𝒥 ∘ R_μ ∘ F_A`, the near solver bounds
  `‖D_N⁻¹‖ ≤ P_ν`, `‖S_N‖ ≤ P_ν e^{η_δ/ν}` (`pairNormAndNearSolver_concrete`) with
  `e^{-γ/(8ν)}e^{η_δ/ν} ≤ 1` (`η_δ < θd₀/8 ≤ γ/8`), the body inverse bounds `NearBody`, and the
  `F_A` bound (`faFamily`);
* `‖L‖_{𝓔_ν → 𝒜} ≤ C ν_n^{-k}` from `L = 𝓛 ∘ Tc`, `‖Tc V‖ ≤ ‖V‖` (`PairSp.norm_eq`), and
  `‖𝓛‖ ≤ P_ν ε_n^3 e^{γ/ν_n} = P_ν` (`sourceLBounded_of`, `retEps_cube_mul`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData IsPlanarReference)
open UnforcedLeray.Short.PartIIIb.NearInst

/-- `θ(a,b) ≤ 3`, so `θ d₀ / 8 ≤ γ / 8` for `d₀ = γ / 3` and `γ ≥ 0`. -/
theorem etaDelta_le_gamma_div_eight {K : ℕ} {γ dm b δ m0 C0 : ℝ} (hγ : 0 ≤ γ)
    (hch : NearChoice K γ dm b δ m0 C0) : etaDelta γ δ ≤ γ / 8 := by
  obtain ⟨a, Dp, -, -, -, -, -, -, -, hη, -, -, -⟩ := hch
  have hθ : thetaAB a b ≤ 1 / 100 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hθ3 : thetaAB a b ≤ 3 := by linarith
  have hmul : thetaAB a b * (γ / 3) ≤ 3 * (γ / 3) :=
    mul_le_mul_of_nonneg_right hθ3 (by linarith)
  linarith

/-- Operator norm of `L = 𝓛 ∘ Tc` on `ReturnBase`: since `‖Tc V‖ ≤ ‖V‖`, `‖L‖ ≤ ‖𝓛‖`. -/
theorem norm_toOps_Lg_le {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)
    {CL : ℝ} (hCL : 0 ≤ CL) (hL : ‖B.Lj‖ ≤ CL) :
    ‖B.toOps.Lg‖ ≤ CL := by
  refine ContinuousLinearMap.opNorm_le_bound _ hCL fun V => ?_
  have h1 : ‖B.toOps.Lg V‖ ≤ ‖B.Lj‖ * ‖PairSp.TL V‖ := B.Lj.le_opNorm (PairSp.TL V)
  have h2 : ‖PairSp.TL V‖ ≤ ‖V‖ := by
    rw [PairSp.norm_eq]
    linarith [mul_nonneg (Real.exp_pos (-(γ / 8) / ν)).le (norm_nonneg (PairSp.wL V))]
  exact h1.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left h2 hCL))

/-- Pointwise bound on `𝒥(v) = (D_N⁻¹Mv, v - S_N D_N⁻¹Mv)` in the pair norm when `η_δ ≤ γ/8`. -/
theorem norm_jlift_le {c mZ ρb γ ν ηδ : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)
    (hν : 0 < ν) (hγ : 0 ≤ γ) (hη : ηδ ≤ γ / 8) {CN : ℝ} (hCN : 0 ≤ CN)
    (hDN : ∀ T, ‖B.DNinv T‖ ≤ CN * ‖T‖)
    (hSN : ∀ T, ‖B.SN T‖ ≤ CN * Real.exp (ηδ / ν) * ‖T‖) (v : VelG c γ ν) :
    ‖B.jlift v‖ ≤ (1 + CN) * CN * ‖B.M v‖ + ‖v‖ := by
  have hnorm : ‖B.jlift v‖ = ‖B.DNinv (B.M v)‖ +
      Real.exp (-(γ / 8) / ν) * ‖v - B.SN (B.DNinv (B.M v))‖ :=
    PairSp.norm_eq (B.jlift v)
  set T := B.DNinv (B.M v)
  have hT : ‖T‖ ≤ CN * ‖B.M v‖ := hDN (B.M v)
  have hsub : ‖v - B.SN T‖ ≤ ‖v‖ + CN * Real.exp (ηδ / ν) * ‖T‖ :=
    (norm_sub_le v (B.SN T)).trans (add_le_add le_rfl (hSN T))
  have he0 : 0 ≤ Real.exp (-(γ / 8) / ν) := (Real.exp_pos _).le
  have he1 : Real.exp (-(γ / 8) / ν) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hν.le)
  have he2 : Real.exp (-(γ / 8) / ν) * Real.exp (ηδ / ν) ≤ 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.2
    have hsum : -(γ / 8) / ν + ηδ / ν = (ηδ - γ / 8) / ν := by ring
    rw [hsum]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hν.le
  have hw : Real.exp (-(γ / 8) / ν) * ‖v - B.SN T‖ ≤ ‖v‖ + CN * ‖T‖ := by
    calc Real.exp (-(γ / 8) / ν) * ‖v - B.SN T‖
        ≤ Real.exp (-(γ / 8) / ν) * (‖v‖ + CN * Real.exp (ηδ / ν) * ‖T‖) :=
          mul_le_mul_of_nonneg_left hsub he0
      _ = Real.exp (-(γ / 8) / ν) * ‖v‖ +
          CN * (Real.exp (-(γ / 8) / ν) * Real.exp (ηδ / ν)) * ‖T‖ := by ring
      _ ≤ 1 * ‖v‖ + CN * 1 * ‖T‖ :=
          add_le_add (mul_le_mul_of_nonneg_right he1 (norm_nonneg v))
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he2 hCN) (norm_nonneg T))
      _ = ‖v‖ + CN * ‖T‖ := by ring
  calc ‖B.jlift v‖ = ‖T‖ + Real.exp (-(γ / 8) / ν) * ‖v - B.SN T‖ := hnorm
    _ ≤ ‖T‖ + (‖v‖ + CN * ‖T‖) := add_le_add le_rfl hw
    _ = (1 + CN) * ‖T‖ + ‖v‖ := by ring
    _ ≤ (1 + CN) * (CN * ‖B.M v‖) + ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hT (by linarith)) le_rfl
    _ = (1 + CN) * CN * ‖B.M v‖ + ‖v‖ := by ring

/-- Operator norm of `𝒫 = 𝒥 ∘ R_μ ∘ F_A` on `ReturnBase`. -/
theorem norm_toOps_P_le {c mZ ρb γ ν ηδ : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)
    (hν : 0 < ν) (hγ : 0 ≤ γ) (hη : ηδ ≤ γ / 8) {CN CB CF : ℝ}
    (hCN : 0 ≤ CN) (hCB : 0 ≤ CB) (hCF : 0 ≤ CF)
    (hDN : ∀ T, ‖B.DNinv T‖ ≤ CN * ‖T‖)
    (hSN : ∀ T, ‖B.SN T‖ ≤ CN * Real.exp (ηδ / ν) * ‖T‖)
    (hRB : ∀ f, ‖B.M (B.R f)‖ ≤ CB * ‖f‖ ∧ ‖B.R f‖ ≤ CB * ‖f‖)
    (hF : ‖B.FA‖ ≤ CF) :
    ‖B.toOps.P‖ ≤ ((1 + CN) * CN + 1) * CB * CF := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
  set f := B.FA A
  have hf : ‖f‖ ≤ CF * ‖A‖ :=
    (B.FA.le_opNorm A).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg A))
  obtain ⟨hMR, hR⟩ := hRB f
  have hj := norm_jlift_le B hν hγ hη hCN hDN hSN (B.R f)
  calc ‖B.toOps.P A‖ = ‖B.jlift (B.R f)‖ := rfl
    _ ≤ (1 + CN) * CN * ‖B.M (B.R f)‖ + ‖B.R f‖ := hj
    _ ≤ (1 + CN) * CN * (CB * ‖f‖) + CB * ‖f‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hMR (by positivity)) hR
    _ = ((1 + CN) * CN + 1) * CB * ‖f‖ := by ring
    _ ≤ ((1 + CN) * CN + 1) * CB * (CF * ‖A‖) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
    _ = ((1 + CN) * CN + 1) * CB * CF * ‖A‖ := by ring

set_option maxHeartbeats 800000 in
theorem plBound_concrete (hNS : NearInst.NearSolverC) (hEx : NearInst.NearOpsExistC)
    (hIn : ∀ (as c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ), SourceLInAff as c mZ ρb γ ν ε μ χo χy)
    (hFb : ∀ (as : ℝ) (χf : ℝ → ℝ), IsSourceCutoffC χf → FACoefBound as χf)
    (hEnv : ∀ χ : ℝ → ℝ, IsSourceCutoffC χ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (as ν : ℝ) (A : ℝ → Mat3),
      0 ≤ as → 0 < ν → IsAffElem as A → affM ν χ A ≤ C * Real.exp (1.1 * as / ν) * affNorm as A)
    (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) :
    ∃ Kint : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
      NearInst.NearChoice Kint (gRate Pl) dm D.K.b D.K.δ D.K.m0 D.K.C0 →
      D.RepairStanding dm dp → D.NearBody →
      ∀ G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)),
        PLBound (concreteReturnSeq D G) D.K.as := by
  by_cases hpre : IsPlanarReference Pl ∧ Pl.eigenvalue.im ≠ 0 ∧ 0 < σ₀ ∧ σ₀ < 1 / 4 ∧
      3 / 2 < mZ ∧ 0 < dm
  · obtain ⟨hP, hω, hσ₀, hσ₁, hmZ, hdm⟩ := hpre
    obtain ⟨Kint, hKint⟩ := pairNormAndNearSolver_concrete hNS hEx Pl hP hω σ₀ hσ₀ hσ₁ mZ hmZ
      dm dp hdm
    refine ⟨Kint, ?_⟩
    rintro D rfl rfl rfl hch hst hNB G
    have hγ : 0 < gRate D.Pl := hst.gamma_pos
    have has : 0 < D.K.as := hst.as_pos
    have hχf : IsSourceCutoffC D.K.χf := hst.chiF
    have hχy : IsStreamCutoff D.K.χy := hst.chiY
    have hηle : etaDelta (gRate D.Pl) D.K.δ ≤ gRate D.Pl / 8 :=
      etaDelta_le_gamma_div_eight hγ.le hch
    obtain ⟨C₁, k₁, N₁, hPN⟩ := hKint D rfl rfl rfl hch hst.actual hst.inlet G
    obtain ⟨CB, kB, eNB⟩ := hNB
    have hBd : ∀ (as mZ γ : ℝ) (Kset : Set ℝ) (χo χy : ℝ → ℝ), SourceLBounded as mZ γ Kset χo χy :=
      fun as mZ γ Kset χo χy => sourceLBounded_of (sourceLAmbient as Kset χo χy) (sourceLN0 mZ γ)
    obtain ⟨CL, kL, hCL⟩ := hBd D.K.as D.K.mZ (gRate D.Pl) (winK D.σ₀) D.K.χo D.K.χy has
      (isCompact_winK _) (winK_sub hσ₀ hσ₁) hmZ hγ
    obtain ⟨CF, kF, hCF0, hCF⟩ := hFb D.K.as D.K.χf hχf (winK D.σ₀) (isCompact_winK _)
      (winK_sub hσ₀ hσ₁)
    obtain ⟨Ce, hCe0, hCe⟩ := hEnv D.K.χf hχf
    set k₄ : ℕ := ⌈-(D.Pl.kappa.re - 5 - 2 * D.σ₀)⌉₊
    have hlev := (seq_levels D hω hσ₀ hσ₁ hst.actual hst.inlet one_pos).and
      (hst.near.and eNB)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hlev
    set CP : ℝ := ((1 + |C₁|) * |C₁| + 1) * |CB| * (CF * Ce)
    set CL' : ℝ := |CL| / (2 * ‖D.Pl.signedCoeff D.σ₀‖)
    set Ctot : ℝ := CP + CL'
    set ktot : ℕ := (2 * k₁ + kB + kF) + (kL + k₄)
    refine ⟨Ctot, ktot, max N₁ N₂, fun n hn z hz => ?_⟩
    have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
    have hn2 : N₂ ≤ n := (le_max_right _ _).trans hn
    obtain ⟨hDNn, hSNn, -⟩ := hPN n hn1 z hz
    obtain ⟨⟨-, -, -, hν1, hμ⟩, hnr, hNBn⟩ := hN₂ n hn2
    have hnear : NearAt D.Pl D.K (D.level n) (D.mu n z) := hnr z hz
    have hRBn : NearBodyAt D.Pl D.K (D.level n) (D.mu n z) CB kB := hNBn z hz
    have hμK : D.mu n z ∈ winK D.σ₀ := hμ z hz
    have hμI : D.mu n z ∈ Ioo (0 : ℝ) (1 / 4) := winK_sub hσ₀ hσ₁ hμK
    have hνp : 0 < retNu D.Pl D.σ₀ n := retNu_pos D.Pl D.σ₀ n
    have hνi : 0 ≤ (retNu D.Pl D.σ₀ n)⁻¹ := inv_nonneg.2 hνp.le
    have hνi1 : 1 ≤ (retNu D.Pl D.σ₀ n)⁻¹ := (one_le_inv₀ hνp).2 hν1
    -- `𝓛` pin and bound
    have hLH : LHyp (cOf (retNu D.Pl D.σ₀ n)) (retNu D.Pl D.σ₀ n) (retEps D.Pl D.σ₀ n) (D.mu n z)
        D.K.χo D.K.χy :=
      ⟨cOf_pos hνp, hνp, hν1, retEps_pos D.coeff_ne n, hμI.1, hμI.2, D.K.hχo, hχy⟩
    have hLjex := exists_LjOp_of (Pl := D.Pl) (K := D.K) (L := D.level n) (μ := D.mu n z) hLH hmZ
      hγ has (Set.singleton_subset_iff.2 hμI) (hIn _ _ _ _ _ _ _ _ _ _)
      (sourceLLinear _ _ _ _ _ _ _ _ _) (hBd _ _ _ _ _ _)
    have hLj : ∀ T, affIota D.K.as (LjOp D.Pl D.K (D.level n) (D.mu n z) T) =
        LjFun (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν
          (D.level n).ε (D.mu n z) D.K.χo D.K.χy T :=
      Classical.epsilon_spec hLjex
    set X : ℝ := retEps D.Pl D.σ₀ n ^ 3 * Real.exp (gRate D.Pl / retNu D.Pl D.σ₀ n) with hXdef
    have hX0 : 0 ≤ X := mul_nonneg (pow_nonneg (retEps_pos D.coeff_ne n).le 3) (Real.exp_pos _).le
    have hLnorm : ‖LjOp D.Pl D.K (D.level n) (D.mu n z)‖ ≤
        |CL| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kL * X := by
      refine ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hνi _)) hX0) fun T => ?_
      rw [← affNorm_affIota, hLj]
      refine (hCL _ _ _ _ _ hLH hμK T).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hνi _)) hX0) (norm_nonneg _)
    -- `F_A` family, pin and bound
    have hCFn := hCF (retNu D.Pl D.σ₀ n) (D.mu n z) hνp hν1 hμK
    have henvn : ∀ A : AffSp D.K.as, affM (retNu D.Pl D.σ₀ n) D.K.χf (affIota D.K.as A) ≤
        (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)) * ‖A‖ := by
      intro A
      have h := hCe D.K.as (retNu D.Pl D.σ₀ n) (affIota D.K.as A) has.le hνp (affIota_mem _ A)
      rwa [affNorm_affIota] at h
    have hfam := faFamily (μ := D.mu n z) hνp (faCoefLinear D.K.as D.K.χf hχf) CF kF hCF0 hCFn _
      henvn
    have hFApin : ∀ A, (FAOp D.K (D.level n) (D.mu n z) A : Chart → Merid)
        =ᵐ[srcMeasure (cOf (D.level n).ν)] FAcoef (D.level n).ν (D.mu n z) D.K.χf
          (affIota D.K.as A) :=
      FAOp_spec (K := D.K) (L := D.level n) (μ := D.mu n z) ⟨hfam.toCLM, hfam.toCLM_ae⟩
    have hCe' : 0 ≤ Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n) :=
      mul_nonneg hCe0 (Real.exp_pos _).le
    have hFnorm : ‖FAOp D.K (D.level n) (D.mu n z)‖ ≤
        CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF * (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)) := by
      refine ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg (mul_nonneg hCF0 (pow_nonneg hνi _)) hCe') fun A => ?_
      rw [Lp.norm_def, eLpNorm_congr_ae (hFApin A)]
      refine ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg (mul_nonneg (mul_nonneg hCF0 (pow_nonneg hνi _)) hCe') (norm_nonneg _))
        ((hCFn _ (affIota_mem _ A)).2.trans (ENNReal.ofReal_le_ofReal ?_))
      calc CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF * affM (retNu D.Pl D.σ₀ n) D.K.χf (affIota D.K.as A)
          ≤ CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF *
              ((Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)) * ‖A‖) :=
            mul_le_mul_of_nonneg_left (henvn A) (mul_nonneg hCF0 (pow_nonneg hνi _))
        _ = _ := by ring
    -- identify operators at `(n, z)` with `B.toOps`
    have hops := concreteReturnSeq_ops_eq D G n z hnear
    set B := concreteBase D.Pl D.K (D.level n) (D.mu n z) hnear
    rw [hops]
    have hDN' : ∀ T, ‖B.DNinv T‖ ≤ (|C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) * ‖T‖ := by
      intro T
      have h := hDNn T
      rw [hops] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C₁) (pow_nonneg hνi _)) (norm_nonneg T))
    have hSN' : ∀ T, ‖B.SN T‖ ≤ (|C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) *
        Real.exp (etaDelta (gRate D.Pl) D.K.δ / retNu D.Pl D.σ₀ n) * ‖T‖ := by
      intro T
      have h := hSNn T
      rw [hops] at h
      exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C₁) (pow_nonneg hνi _))
        (Real.exp_pos _).le) (norm_nonneg T))
    have hRB' : ∀ f, ‖B.M (B.R f)‖ ≤ (|CB| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kB) * ‖f‖ ∧
        ‖B.R f‖ ≤ (|CB| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kB) * ‖f‖ := by
      intro f
      obtain ⟨h1, h2⟩ := hRBn f
      have habs : CB * (retNu D.Pl D.σ₀ n)⁻¹ ^ kB * ‖f‖ ≤
          (|CB| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kB) * ‖f‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self CB) (pow_nonneg hνi _)) (norm_nonneg f)
      exact ⟨h1.trans habs, h2.trans habs⟩
    have hCN0 : 0 ≤ |C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁ :=
      mul_nonneg (abs_nonneg _) (pow_nonneg hνi _)
    have hCB0 : 0 ≤ |CB| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kB :=
      mul_nonneg (abs_nonneg _) (pow_nonneg hνi _)
    have hCF0' : 0 ≤ CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF *
        (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)) :=
      mul_nonneg (mul_nonneg hCF0 (pow_nonneg hνi _)) hCe'
    have hP0 := norm_toOps_P_le B hνp hγ.le hηle hCN0 hCB0 hCF0' hDN' hSN' hRB' hFnorm
    have hLg0 := norm_toOps_Lg_le B
      (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hνi _)) hX0) hLnorm
    have hc2 : 0 < 2 * ‖D.Pl.signedCoeff D.σ₀‖ := mul_pos two_pos (norm_pos_iff.2 D.coeff_ne)
    have hXle : X ≤ (retNu D.Pl D.σ₀ n)⁻¹ ^ k₄ / (2 * ‖D.Pl.signedCoeff D.σ₀‖) := by
      rw [hXdef, retEps_cube_mul D.coeff_ne n]
      exact div_le_div_of_nonneg_right (seq_rpow_le_inv_pow hνp hν1 _) hc2.le
    have hCP0 : 0 ≤ CP := by positivity
    have hCL'0 : 0 ≤ CL' := by positivity
    refine ⟨hP0.trans ?_, hLg0.trans ?_⟩
    · -- Bound for `P`
      have h1k : 1 ≤ (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁ := one_le_pow₀ hνi1
      have h1k2 : 1 ≤ (retNu D.Pl D.σ₀ n)⁻¹ ^ (2 * k₁) := one_le_pow₀ hνi1
      have hCN_quad : (1 + |C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) *
          (|C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) + 1 ≤
          ((1 + |C₁|) * |C₁| + 1) * (retNu D.Pl D.σ₀ n)⁻¹ ^ (2 * k₁) := by
        have ha : 1 + |C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁ ≤
            (1 + |C₁|) * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁ := by linarith
        have hb : (1 + |C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) *
            (|C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) ≤
            (1 + |C₁|) * |C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ (2 * k₁) := by
          calc (1 + |C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) *
                (|C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁)
              ≤ ((1 + |C₁|) * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) *
                  (|C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) :=
                mul_le_mul_of_nonneg_right ha hCN0
            _ = (1 + |C₁|) * |C₁| *
                ((retNu D.Pl D.σ₀ n)⁻¹ ^ k₁ * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) := by ring
            _ = (1 + |C₁|) * |C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ (2 * k₁) := by
                rw [← pow_add, two_mul]
        linarith
      have hpow_le : (retNu D.Pl D.σ₀ n)⁻¹ ^ (2 * k₁ + kB + kF) ≤
          (retNu D.Pl D.σ₀ n)⁻¹ ^ ktot :=
        pow_le_pow_right₀ hνi1 (Nat.le_add_right _ _)
      have hC_le : CP ≤ Ctot := le_add_of_nonneg_right hCL'0
      calc ((1 + |C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) *
              (|C₁| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₁) + 1) *
            (|CB| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kB) *
            (CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF *
              (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)))
          ≤ (((1 + |C₁|) * |C₁| + 1) * (retNu D.Pl D.σ₀ n)⁻¹ ^ (2 * k₁)) *
              (|CB| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kB) *
              (CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF *
                (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCN_quad hCB0) hCF0'
        _ = CP * (retNu D.Pl D.σ₀ n)⁻¹ ^ (2 * k₁ + kB + kF) *
              Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n) := by
            rw [pow_add, pow_add]
            ring
        _ ≤ Ctot * ((concreteReturnSeq D G).ν n)⁻¹ ^ ktot *
              Real.exp (1.1 * D.K.as / (concreteReturnSeq D G).ν n) := by
            show CP * (retNu D.Pl D.σ₀ n)⁻¹ ^ (2 * k₁ + kB + kF) *
                Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n) ≤
              Ctot * (retNu D.Pl D.σ₀ n)⁻¹ ^ ktot *
                Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul hC_le hpow_le (pow_nonneg hνi _) (by positivity))
              (Real.exp_pos _).le
    · -- Bound for `Lg`
      have hpow_le : (retNu D.Pl D.σ₀ n)⁻¹ ^ (kL + k₄) ≤
          (retNu D.Pl D.σ₀ n)⁻¹ ^ ktot :=
        pow_le_pow_right₀ hνi1 (Nat.le_add_left _ _)
      have hC_le : CL' ≤ Ctot := le_add_of_nonneg_left hCP0
      calc |CL| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kL * X
          ≤ |CL| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kL *
              ((retNu D.Pl D.σ₀ n)⁻¹ ^ k₄ / (2 * ‖D.Pl.signedCoeff D.σ₀‖)) :=
            mul_le_mul_of_nonneg_left hXle
              (mul_nonneg (abs_nonneg _) (pow_nonneg hνi _))
        _ = CL' * (retNu D.Pl D.σ₀ n)⁻¹ ^ (kL + k₄) := by
            rw [pow_add]
            ring
        _ ≤ Ctot * ((concreteReturnSeq D G).ν n)⁻¹ ^ ktot :=
            mul_le_mul hC_le hpow_le (pow_nonneg hνi _) (by positivity)
  · refine ⟨0, ?_⟩
    rintro D rfl rfl rfl - hst - -
    exact False.elim (hpre ⟨hst.planar, hst.omega_ne, hst.sigma_pos, hst.sigma_lt,
      hst.mZ_gt, hst.dm_pos⟩)

end UnforcedLeray.Short.PartIIIb.Concrete
