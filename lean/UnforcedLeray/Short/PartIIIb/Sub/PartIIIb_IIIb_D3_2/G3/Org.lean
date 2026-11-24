import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Fpm

/-!
# `ORG:D3/2/G3`: group G3 (old-output anisotropy and the earlier-old part)

Source: `the November 2 reference manuscript` (73 pp): young source theorem
4461-4553 (Duhamel at `H` 4501-4508, `eq:young-old-anisotropy` 4520-4539, real form 4540-4543),
its use in the signed old-stress response 4665-4676 (`u_o = ν^{-3/2}`), the earlier-old part
4677-4679 ("by the full forward gain estimate", `prop:short-full-clock` 2836-2846,
`eq:short-causal-weak-forward` 3096-3099, `eq:short-causal-long-forward` 3020-3023).

`GroupOld D` (`FlatUniform.lean`) has two conjuncts, both relative to `‖B‖_a`.  The source
proves each relative to the tested source norm `‖g_B‖_𝓘` and then uses `‖g_B‖_𝓘 ≤ C‖B‖_a`
(4665-4667), which is the first conjunct of `GroupTested D` (G4).  So:

* `OldAnisoTested D` : the real form of `eq:young-old-anisotropy` at `f = g_B` on `s ≥ u_o`,
  error `C𝒜_ν(ν + ω_can)‖g_B‖_𝓘` (`η_ν = O(ν)`, 4392);
* `EarlierOldTested D` : `|I_T(M_B; s < u_o)| ≤ C𝒜_ν ν^{-k}e^{-γ'/√ν}‖g_B‖_𝓘`;
* `ForwardGain D` : the full forward gain estimate on the actual evolution of the flat sequence,
  `X_{m,c} → X_{m,c}`, on the earlier-old range (the Part III-a statement, taken as hypothesis);
* `EarlierReadout D` : the old stress readout `ξ ↦ (1/c)∫_cell(2M_zz - M_rr)`, `M = v⊗K_cξ +
  K_cξ⊗v`, is bounded by `P_ν‖ξ‖` on the earlier-old range;
* `earlierOldTested_of` : the earlier-old part from `ForwardGain`, `EarlierReadout` and the
  admissibility `G1.GBAdmissible` of `g_B` (the window-uniform constant bookkeeping:
  `g(s) ≤ e^{γ/ν}e^{-γ'/√ν}` for `s ≤ u_o`, `g(t)⁻¹ ≤ 2.1^{|Re κ|}|F_+(t,0)|⁻¹` on the source band);
* `flatGroupOld_of` : `GroupOld D` from `GroupTested D` and the two tested-norm statements.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF

namespace G3

/-- **Old-output anisotropy at `f = g_B`, tested form** (source 4501-4543, used at 4665-4676).
For every actual flat sequence, uniformly in the window `μ = μ_n(z)`, `z ∈ [-1,1]`, and on the
class `𝓑_a`: with `u_o = ν^{-3/2}` and `𝒜_ν = |N_ν|ν^{3+2μ}/c`,
`|I_T(M_B; s ≥ u_o) - (3π/(2c))(μ+3/2)ν^{3+2μ} Im[a_{ν,+}(B)N_νJ(μ)]| ≤ C𝒜_ν(ν + ω_can)‖g_B‖_𝓘`.
This is `eq:young-old-anisotropy` (its `o_K(𝒜_ν)` written `𝒜_ν(η_ν + ω_can)`, `η_ν = O(ν)`) in the
real form of 4540-4543 (`a_- = ā_+` for real `μ` and real forcing): Duhamel at `H` (4501-4508), the
same unforced evolution for `s ≥ H` (4509-4510), `eq:young-later-output` for the remainder
(4511-4514), and the canonical Mellin limit and stress defect for the bare columns (4520-4521). -/
def OldAnisoTested (D : SeqData) : Prop :=
  ForActual D fun S =>
    ∃ (ωcan : ℕ → ℝ) (C : ℝ) (N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧ (∀ n, 0 ≤ ωcan n) ∧ 0 ≤ C ∧
      ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
        |(S n).IT (fun s => if nu D n ^ (-(3 / 2 : ℝ)) ≤ s then
              (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) -
            (3 * Real.pi / (2 * (S n).c)) * (D.mu n z + 3 / 2) * nu D n ^ (3 + 2 * D.mu n z) *
              (((S n).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z : ℂ) (nu D n) B) *
                Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ)).im| ≤
          C * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
            (S n).c) * (nu D n + ωcan n)) *
            testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
              ((S n).gB B)

/-- **The earlier-old part, tested form** (source 4677-4679): for every `0 < γ' < γ = Re λ`, the
part `1.2/ν < s < u_o = ν^{-3/2}` of `I_T(M_B)` has bound `C𝒜_ν P_ν e^{-γ'/√ν}‖g_B‖_𝓘`,
`P_ν = ν^{-k}`, uniformly in the window and on `𝓑_a`. -/
def EarlierOldTested (D : SeqData) : Prop :=
  ForActual D fun S => ∀ γ' : ℝ, 0 < γ' → γ' < D.Pl.eigenvalue.re →
    ∃ (C : ℝ) (k N : ℕ), 0 ≤ C ∧ ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B,
      IsBclass D.K.as (nu D n) B →
      |(S n).IT (fun s => if s < nu D n ^ (-(3 / 2 : ℝ)) then
            (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0)| ≤
        C * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
          (S n).c) * ((nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n))) *
          testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
            ((S n).gB B)

/-- **The full forward gain estimate on the actual flat evolution** (Part III-a,
`prop:short-full-clock` 2836-2846: `‖(g(t)/g(s))U(s,t)‖ ≤ C_bν^{-M_s}{1 + (s-t)^{-1/2}}`,
`g(s) = exp(γs/(1+νs))`, `eq:short-causal-weak-forward` 3096-3099; the moving form
`eq:short-causal-long-forward` 3020-3023 with `eq:short-causal-scales` 3031-3035), as used for
the earlier-old part (4677-4679): for every actual flat sequence, on the source band
`0 < t ≤ 1.1/ν` and the earlier-old range `1.2/ν ≤ s ≤ u_o = ν^{-3/2}` (inside the core
`s ≤ H_b = ν⁻¹((νb)⁻¹ - 1)` for small `ν`; `s - t ≥ 0.1/ν`),
`‖U(s,t)x‖_{X_{m,c}} ≤ Cν^{-k}(g(s)/g(t))‖x‖_{X_{m,c}}`. -/
def ForwardGain (D : SeqData) : Prop :=
  ForActual D fun S => ∃ (C : ℝ) (k N : ℕ), ∀ n ≥ N, ∀ t s : ℝ, 0 < t → t ≤ 1.1 / nu D n →
    1.2 / nu D n ≤ s → s ≤ nu D n ^ (-(3 / 2 : ℝ)) → ∀ x : (S n).pk.X,
      ‖(S n).pk.Uev s t x‖ ≤ C * (nu D n)⁻¹ ^ k *
        (IIIa.gainG D.Pl.eigenvalue.re (nu D n) s / IIIa.gainG D.Pl.eigenvalue.re (nu D n) t) *
          ‖x‖

/-- **The old stress readout on the earlier-old range** (source 4610-4612: `M = v⊗b + b⊗v`,
`b = K_cξ`; the flat train bound `stress-short:coefficients` 2713-2723 and the Biot-Savart
embedding `eq:ct-embeddings` 3230-3240): for every actual flat sequence and
`1.2/ν ≤ s ≤ u_o = ν^{-3/2}`, `|(1/c)∫_cell (2M_zz - M_rr)| ≤ P_ν‖ξ‖_{X_{m,c}}`. -/
def EarlierReadout (D : SeqData) : Prop :=
  ForActual D fun S => ∃ (C : ℝ) (k N : ℕ), ∀ n ≥ N, ∀ s : ℝ, 1.2 / nu D n ≤ s →
    s ≤ nu D n ^ (-(3 / 2 : ℝ)) → ∀ ξ : (S n).pk.X,
      |cellInt (S n).c (fun p => 2 * (S n).Mcell s ξ p 2 2 - (S n).Mcell s ξ p 0 0)| ≤
        C * (nu D n)⁻¹ ^ k * ‖ξ‖

/-- An actual flat sequence has, at large levels, `c = ν⁻²` and `χ_o(s) = χ̂_o(νs)`. -/
private theorem actual_facts {D : SeqData} {κ : IIIa.PlanarFrameKernels} {m : ℝ} [Fact (1 < m)]
    {S : ℕ → FlatSetting} (hS : IsActualSeq D κ m S) :
    ∀ᶠ n : ℕ in atTop, (S n).c = cOf (nu D n) ∧ ∀ s, (S n).chiO s = D.K.χo (nu D n * s) := by
  filter_upwards [hS] with n hn
  obtain ⟨FI, hFI⟩ := hn
  rw [hFI]
  exact ⟨rfl, fun s => rfl⟩

/-- `γs/(1+νs) ≤ γ/ν - γ'/√ν` when `νs ≤ 1/√ν` (i.e. `s ≤ u_o`) and `√ν ≤ γ/γ' - 1`. -/
private theorem gain_exponent_le {γ γ' ν s : ℝ} (hγ' : 0 < γ') (hν : 0 < ν)
    (hsq : Real.sqrt ν ≤ γ / γ' - 1) (hs0 : 0 ≤ s) (hs : ν * s ≤ (Real.sqrt ν)⁻¹) :
    γ * s / (1 + ν * s) ≤ γ / ν - γ' / Real.sqrt ν := by
  set r := Real.sqrt ν with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hν
  have hνr : ν = r ^ 2 := (Real.sq_sqrt hν.le).symm
  have h1 : ν * s * r ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hs hr0.le
    rwa [inv_mul_cancel₀ hr0.ne'] at this
  have h2 : γ' * r ≤ γ - γ' := by
    have := mul_le_mul_of_nonneg_left hsq hγ'.le
    rw [mul_sub, mul_div_cancel₀ _ hγ'.ne', mul_one] at this
    linarith
  have hd : 0 < 1 + ν * s := by positivity
  rw [div_le_iff₀ hd]
  have e : (γ / ν - γ' / r) * (1 + ν * s) = γ / ν + γ * s - (γ' / r + γ' * (ν * s) / r) := by
    field_simp
  have key : γ' / r + γ' * (ν * s) / r ≤ γ / ν := by
    have hlhs : γ' / r + γ' * (ν * s) / r = (γ' * r + γ' * (ν * s * r)) / ν := by
      rw [hνr]
      field_simp
    rw [hlhs]
    apply (div_le_div_iff_of_pos_right hν).2
    nlinarith [mul_le_mul_of_nonneg_left h1 hγ'.le]
  rw [e]
  linarith

/-- **The earlier-old part from the full forward gain estimate** (source 4677-4679): the window
bookkeeping of `ν, μ, γ'`, uniform in `z ∈ [-1,1]`.  Composed in task `PartIII-b:IIIb-D3/2/G3`. -/
theorem earlierOldTested_of {D : SeqData} (hG : ForwardGain D) (hR : EarlierReadout D)
    (hA : G1.GBAdmissible D) : EarlierOldTested D := by
  intro dm dp hst κ hκ m _ hm S hS γ' hγ'0 hγ'γ
  obtain ⟨CG, kG, NG, hCG⟩ := hG dm dp hst κ hκ m hm S hS
  obtain ⟨CR, kR, NR, hCR⟩ := hR dm dp hst κ hκ m hm S hS
  obtain ⟨NA, hNA⟩ := hA dm dp hst κ hκ m hm S hS
  set γ := D.Pl.eigenvalue.re with hγdef
  have hq : 0 < γ / γ' - 1 := by
    have : 1 < γ / γ' := (one_lt_div hγ'0).2 hγ'γ
    linarith
  set ν₁ : ℝ := min 1 ((γ / γ' - 1) ^ 2) with hν₁
  have hν₁pos : 0 < ν₁ := lt_min one_pos (pow_pos hq 2)
  have hev : ∀ᶠ n : ℕ in atTop,
      ((S n).c = cOf (nu D n) ∧ ∀ s, (S n).chiO s = D.K.χo (nu D n * s)) ∧
        nu D n < ν₁ ∧ ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ∈ Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) :=
    (actual_facts hS).and (((retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₁pos)).and
      (mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  set Kκ : ℝ := (2.1 : ℝ) ^ |D.Pl.kappa.re| with hKκ
  have hKκ0 : 0 ≤ Kκ := by positivity
  refine ⟨max CR 0 * max CG 0 * Kκ, kR + kG + 7 + ⌈|D.Pl.kappa.re|⌉₊,
    max (max NG NR) (max NA N0), by positivity, ?_⟩
  intro n hn z hz B hB
  have hnG : NG ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnR : NR ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnA : NA ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn0 : N0 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨⟨hc, hchi⟩, hνsmall, hμwin⟩ := hN0 n hn0
  obtain ⟨hsupp, -, -, -, -, hint⟩ := hNA n hnA z hz B hB
  set ν := nu D n with hνdef
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  have hν1 : ν ≤ 1 := hνsmall.le.trans (min_le_left _ _)
  have hsq : Real.sqrt ν ≤ γ / γ' - 1 := by
    have h1 : ν ≤ (γ / γ' - 1) ^ 2 := hνsmall.le.trans (min_le_right _ _)
    calc Real.sqrt ν ≤ Real.sqrt ((γ / γ' - 1) ^ 2) := Real.sqrt_le_sqrt h1
      _ = γ / γ' - 1 := Real.sqrt_sq hq.le
  set μ := D.mu n z with hμdef
  have hμ0 : 0 ≤ μ := by
    have := (hμwin z hz).1
    linarith [hst.sigma_pos]
  have hμ1 : μ ≤ 1 / 4 := by
    have := (hμwin z hz).2
    linarith [hst.sigma_lt]
  set tN := testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa ν (μ : ℂ) (1.1 / ν) ((S n).gB B)
    with htN
  have htN0 : 0 ≤ tN := by
    rw [htN]
    unfold testedNorm
    exact setIntegral_nonneg measurableSet_Ioc fun t ht =>
      mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (inv_nonneg.2 (norm_nonneg _)))
        (norm_nonneg _)
  set uo : ℝ := ν ^ (-(3 / 2 : ℝ)) with huo
  have huo0 : 0 ≤ uo := Real.rpow_nonneg hν.le _
  set E : ℝ := Real.exp (γ / ν) * Real.exp (-γ' / Real.sqrt ν) with hE
  have hE0 : 0 ≤ E := by positivity
  -- the gain at ages `s ≤ u_o`
  have hgain : ∀ s, 0 ≤ s → s ≤ uo → IIIa.gainG γ ν s ≤ E := by
    intro s hs0 hs
    have hνs : ν * s ≤ (Real.sqrt ν)⁻¹ := by
      have e1 : ν * uo = (Real.sqrt ν)⁻¹ := by
        have := Real.rpow_add hν (1 : ℝ) (-(3 / 2 : ℝ))
        rw [Real.rpow_one] at this
        rw [huo, ← this, Real.sqrt_eq_rpow, ← Real.rpow_neg hν.le]
        norm_num
      calc ν * s ≤ ν * uo := mul_le_mul_of_nonneg_left hs hν.le
        _ = (Real.sqrt ν)⁻¹ := e1
    have hx := gain_exponent_le hγ'0 hν hsq hs0 hνs
    unfold IIIa.gainG
    rw [hE, ← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [neg_div]
    linarith
  -- `g(t)⁻¹ ≤ 2.1^{|Re κ|}|F_+(t,0)|⁻¹` on the source band
  have hFinv : ∀ t, 0 < t → t ≤ 1.1 / ν →
      (IIIa.gainG γ ν t)⁻¹ ≤ Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ := by
    intro t ht htT
    have ha : 0 < aOf ν t := aOf_pos_of_nonneg ν t hν ht.le
    have ha1 : 1 ≤ aOf ν t := by
      unfold aOf
      nlinarith [mul_pos hν ht]
    have ha2 : aOf ν t ≤ 2.1 := by
      unfold aOf
      have : ν * t ≤ 1.1 := by
        calc ν * t ≤ ν * (1.1 / ν) := mul_le_mul_of_nonneg_left htT hν.le
          _ = 1.1 := by field_simp
      linarith
    have ha0 : aOf ν 0 = 1 := by simp [aOf]
    have hr : 0 < aOf ν t / aOf ν 0 := by rw [ha0, div_one]; exact ha
    have hnorm : ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖ =
        IIIa.gainG γ ν t * aOf ν t ^ D.Pl.kappa.re := by
      rw [fpm_true_eq, fpm_norm_formula _ _ ν t 0 hr, ha0, div_one]
      unfold IIIa.gainG zOf
      rw [ha0, zero_div, sub_zero]
      unfold aOf
      rw [mul_div_assoc]
    have hgpos : 0 < IIIa.gainG γ ν t := Real.exp_pos _
    have hapos : 0 < aOf ν t ^ D.Pl.kappa.re := Real.rpow_pos_of_pos ha _
    have heq : (IIIa.gainG γ ν t)⁻¹ =
        aOf ν t ^ D.Pl.kappa.re * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ := by
      rw [hnorm]
      field_simp
    have hle : aOf ν t ^ D.Pl.kappa.re ≤ Kκ :=
      (Real.rpow_le_rpow_of_exponent_le ha1 (le_abs_self _)).trans
        (Real.rpow_le_rpow ha.le ha2 (abs_nonneg _))
    rw [heq]
    exact mul_le_mul_of_nonneg_right hle (inv_nonneg.2 (norm_nonneg _))
  -- the Duhamel state on the earlier-old range
  have hduh : ∀ s, 1.2 / ν ≤ s → s ≤ uo →
      ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) s‖ ≤ max CG 0 * ν⁻¹ ^ kG * E * Kκ * tN := by
    intro s hs1 hs2
    have hTs : 1.1 / ν ≤ s := le_trans (div_le_div_of_nonneg_right (by norm_num) hν.le) hs1
    have hs0 : 0 ≤ s := le_trans (by positivity) hTs
    set K0 : ℝ := max CG 0 * ν⁻¹ ^ kG * E * Kκ with hK0
    have hK00 : 0 ≤ K0 := by positivity
    set F : ℝ → ℝ := fun t =>
      t ^ μ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ * ‖(S n).gB B t‖ with hF
    have hmaj : Integrable ((Ioc 0 (1.1 / ν)).indicator (fun t => K0 * F t))
        (volume.restrict (Ioc 0 s)) := by
      rw [integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
        Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 (Ioc_subset_Ioc_right hTs)]
      exact hint.const_mul K0
    calc ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) s‖
        ≤ ∫ t in Ioc 0 s, ‖((t : ℂ) ^ (μ : ℂ)) • ((S n).pk.Uev s t) ((S n).gB B t)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioc 0 s, (Ioc 0 (1.1 / ν)).indicator (fun t => K0 * F t) t := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hmaj ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          by_cases htT : t ≤ 1.1 / ν
          · rw [indicator_of_mem (show t ∈ Ioc 0 (1.1 / ν) from ⟨ht.1, htT⟩)]
            have hU := hCG n hnG t s ht.1 htT hs1 hs2 ((S n).gB B t)
            have hg1 := hgain s hs0 hs2
            have hg2 := hFinv t ht.1 htT
            have hgs : 0 ≤ IIIa.gainG γ ν s := (Real.exp_pos _).le
            have hgt : 0 < IIIa.gainG γ ν t := Real.exp_pos _
            have htμ : 0 ≤ t ^ μ := Real.rpow_nonneg ht.1.le _
            have hrat0 : 0 ≤ IIIa.gainG γ ν s / IIIa.gainG γ ν t := div_nonneg hgs hgt.le
            have hratio : IIIa.gainG γ ν s / IIIa.gainG γ ν t ≤
                E * (Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹) := by
              rw [div_eq_mul_inv]
              exact mul_le_mul hg1 hg2 (inv_nonneg.2 hgt.le) hE0
            rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.ofReal_re]
            have hstep : ‖(S n).pk.Uev s t ((S n).gB B t)‖ ≤ max CG 0 * ν⁻¹ ^ kG *
                (E * (Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹)) *
                  ‖(S n).gB B t‖ := by
              refine hU.trans ?_
              have hp0 : 0 ≤ ν⁻¹ ^ kG := by positivity
              have hx0 : 0 ≤ ‖(S n).gB B t‖ := norm_nonneg _
              calc CG * ν⁻¹ ^ kG * (IIIa.gainG γ ν s / IIIa.gainG γ ν t) * ‖(S n).gB B t‖
                  ≤ max CG 0 * ν⁻¹ ^ kG * (IIIa.gainG γ ν s / IIIa.gainG γ ν t) *
                      ‖(S n).gB B t‖ := by
                    gcongr
                    exact le_max_left _ _
                _ ≤ max CG 0 * ν⁻¹ ^ kG *
                    (E * (Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹)) *
                      ‖(S n).gB B t‖ := by
                    gcongr
            calc t ^ μ * ‖(S n).pk.Uev s t ((S n).gB B t)‖
                ≤ t ^ μ * (max CG 0 * ν⁻¹ ^ kG *
                    (E * (Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹)) *
                      ‖(S n).gB B t‖) := mul_le_mul_of_nonneg_left hstep htμ
              _ = K0 * F t := by
                  simp only [hK0, hF]
                  ring
          · have hz : (S n).gB B t = 0 := hsupp t (lt_of_not_ge htT)
            rw [hz, map_zero, smul_zero, norm_zero]
            exact indicator_nonneg (fun t ht' => mul_nonneg hK00
              (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht'.1.le _) (inv_nonneg.2 (norm_nonneg _)))
                (norm_nonneg _))) t
      _ = K0 * tN := by
          rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
            inter_eq_left.2 (Ioc_subset_Ioc_right hTs), integral_const_mul]
          rfl
  -- the density of the earlier-old piece
  set Q : ℝ := max CR 0 * ν⁻¹ ^ kR * (max CG 0 * ν⁻¹ ^ kG * E * Kκ * tN) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hdens : ∀ s, |(S n).ITdens (fun s => if s < uo then
      (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0) s| ≤
        (Ioo 0 uo).indicator (fun _ => Q) s := by
    intro s
    by_cases hmain : 1.2 / ν < s ∧ s < uo
    · obtain ⟨h1, h2⟩ := hmain
      have h12 : (1.2 : ℝ) ≤ 1.2 / ν := by
        rw [le_div_iff₀ hν]
        nlinarith
      have hs1 : 1 ≤ s := by linarith
      have hspos : 0 < s := by linarith
      rw [indicator_of_mem (show s ∈ Ioo 0 uo from ⟨hspos, h2⟩)]
      unfold FlatSetting.ITdens
      simp only [h2, ↓reduceIte]
      rw [abs_mul, abs_mul]
      have hchi1 : |(S n).chiO s| ≤ 1 := by
        rw [hchi s, abs_le]
        have := D.K.hχo.range (ν * s)
        constructor <;> linarith [this.1, this.2]
      have hspow : |s ^ (-(3 / 2 : ℝ))| ≤ 1 := by
        rw [abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
        exact Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
      have hread := hCR n hnR s h1.le h2.le ((S n).xi (μ : ℂ) B s)
      have hxi : ‖(S n).xi (μ : ℂ) B s‖ ≤ ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) s‖ := by
        unfold FlatSetting.xi
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hspos]
        simp only [Complex.neg_re, Complex.ofReal_re]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (Real.rpow_le_one_of_one_le_of_nonpos hs1 (by linarith))
      have hD := hduh s h1.le h2.le
      have hcell : |cellInt (S n).c (fun p => 2 * (S n).Mcell s ((S n).xi (μ : ℂ) B s) p 2 2 -
          (S n).Mcell s ((S n).xi (μ : ℂ) B s) p 0 0)| ≤ Q := by
        refine hread.trans ?_
        have hp0 : 0 ≤ ν⁻¹ ^ kR := by positivity
        calc CR * ν⁻¹ ^ kR * ‖(S n).xi (μ : ℂ) B s‖
            ≤ max CR 0 * ν⁻¹ ^ kR * ‖(S n).xi (μ : ℂ) B s‖ := by
              gcongr
              exact le_max_left _ _
          _ ≤ Q := by
              rw [hQ]
              gcongr
              exact hxi.trans hD
      calc |(S n).chiO s| * |s ^ (-(3 / 2 : ℝ))| *
            |cellInt (S n).c (fun p => 2 * (S n).Mcell s ((S n).xi (μ : ℂ) B s) p 2 2 -
              (S n).Mcell s ((S n).xi (μ : ℂ) B s) p 0 0)|
          ≤ 1 * 1 * Q :=
            mul_le_mul (mul_le_mul hchi1 hspow (abs_nonneg _) zero_le_one) hcell (abs_nonneg _)
              (by norm_num)
        _ = Q := by ring
    · have h0 : (S n).ITdens (fun s => if s < uo then
          (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0) s = 0 := by
        unfold FlatSetting.ITdens
        rcases not_and_or.1 hmain with h | h
        · have hle : ν * s ≤ 6 / 5 := by
            have : s ≤ 1.2 / ν := le_of_not_gt h
            calc ν * s ≤ ν * (1.2 / ν) := mul_le_mul_of_nonneg_left this hν.le
              _ = 6 / 5 := by field_simp; norm_num
          rw [hchi s, D.K.hχo.zero _ hle, zero_mul, zero_mul]
        · simp only [h, ↓reduceIte]
          simp [cellInt]
      rw [h0, abs_zero]
      exact indicator_nonneg (fun _ _ => hQ0) s
  -- the integral
  have hIT : |(S n).IT (fun s => if s < uo then
      (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0)| ≤ Q * uo := by
    rw [FlatSetting.IT_eq]
    calc |∫ s in Ioi (0 : ℝ), (S n).ITdens (fun s => if s < uo then
            (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0) s|
        ≤ ∫ s in Ioi (0 : ℝ), |(S n).ITdens (fun s => if s < uo then
            (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0) s| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ s in Ioi (0 : ℝ), (Ioo 0 uo).indicator (fun _ => Q) s := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) ?_
            (Eventually.of_forall hdens)
          rw [integrable_indicator_iff measurableSet_Ioo, IntegrableOn,
            Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Ioi_self]
          exact integrable_const Q
      _ = Q * uo := by
          rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
            inter_eq_left.2 Ioo_subset_Ioi_self, setIntegral_const, smul_eq_mul,
            Real.volume_real_Ioo_of_le huo0, sub_zero, mul_comm]
  -- the powers of `ν`
  have hpow : ν⁻¹ ^ kR * ν⁻¹ ^ kG * uo ≤ ν ^ (-D.Pl.kappa.re) * ν ^ (3 + 2 * μ) * ν ^ (2 : ℕ) *
      ν⁻¹ ^ (kR + kG + 7 + ⌈|D.Pl.kappa.re|⌉₊) := by
    have e1 : ∀ j : ℕ, ν⁻¹ ^ j = ν ^ (-(j : ℝ)) := fun j => by
      rw [Real.rpow_neg hν.le, Real.rpow_natCast, inv_pow]
    have e2 : ν ^ (2 : ℕ) = ν ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [e1, e1, e1, e2, huo, ← Real.rpow_add hν, ← Real.rpow_add hν, ← Real.rpow_add hν,
      ← Real.rpow_add hν, ← Real.rpow_add hν]
    apply Real.rpow_le_rpow_of_exponent_ge hν hν1
    push_cast
    have hc1 := Nat.le_ceil |D.Pl.kappa.re|
    have hab := neg_le_abs D.Pl.kappa.re
    linarith
  have hN : ‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ = Real.exp (γ / ν) * ν ^ (-D.Pl.kappa.re) := by
    unfold Nnu
    rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hν]
    simp [Complex.div_ofReal_re, hγdef]
  have hP0 : 0 ≤ max CR 0 * max CG 0 * Kκ * Real.exp (γ / ν) * Real.exp (-γ' / Real.sqrt ν) * tN := by
    positivity
  calc |(S n).IT (fun s => if s < uo then
        (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0)|
      ≤ Q * uo := hIT
    _ = (max CR 0 * max CG 0 * Kκ * Real.exp (γ / ν) * Real.exp (-γ' / Real.sqrt ν) * tN) *
          (ν⁻¹ ^ kR * ν⁻¹ ^ kG * uo) := by
        rw [hQ, hE]
        ring
    _ ≤ (max CR 0 * max CG 0 * Kκ * Real.exp (γ / ν) * Real.exp (-γ' / Real.sqrt ν) * tN) *
          (ν ^ (-D.Pl.kappa.re) * ν ^ (3 + 2 * μ) * ν ^ (2 : ℕ) *
            ν⁻¹ ^ (kR + kG + 7 + ⌈|D.Pl.kappa.re|⌉₊)) := mul_le_mul_of_nonneg_left hpow hP0
    _ = max CR 0 * max CG 0 * Kκ *
          (‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ * ν ^ (3 + 2 * μ) / (S n).c) *
          (ν⁻¹ ^ (kR + kG + 7 + ⌈|D.Pl.kappa.re|⌉₊) * Real.exp (-γ' / Real.sqrt ν)) * tN := by
        rw [hN, hc, cOf, div_inv_eq_mul]
        ring

/-- **Group G3 from the tested forms** (source 4665-4679): `GroupOld D` from the tested source
norm bound `‖g_B‖_𝓘 ≤ C‖B‖_a` (first conjunct of `GroupTested D`, 4665-4667) and the two
tested-norm statements.  Composed in task `PartIII-b:IIIb-D3/2/G3`. -/
theorem flatGroupOld_of {D : SeqData} (hT : GroupTested D) (hA : OldAnisoTested D)
    (hE : EarlierOldTested D) : GroupOld D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨⟨CT, NT, hCT⟩, -⟩ := hT dm dp hst κ hκ m hm S hS
  obtain ⟨Nc, hNc⟩ := eventually_atTop.1 (actual_facts hS)
  refine ⟨?_, ?_⟩
  · obtain ⟨ω, CA, NA, hω, hω0, hCA0, hCA⟩ := hA dm dp hst κ hκ m hm S hS
    refine ⟨ω, CA * max CT 0, max (max NT NA) Nc, hω, fun n hn z hz B hB => ?_⟩
    have h1 := hCT n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn) z hz B hB
    have h2 := hCA n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn) z hz B hB
    obtain ⟨hc, -⟩ := hNc n (le_trans (le_max_right _ _) hn)
    have hν := retNu_pos D.Pl D.σ₀ n
    have hA0 : 0 ≤ ‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
        (S n).c := by
      rw [hc]
      exact div_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hν.le _)) (cOf_pos hν).le
    have hb0 : 0 ≤ bNorm D.K.as B := ENNReal.toReal_nonneg
    have hX : 0 ≤ CA * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
        nu D n ^ (3 + 2 * D.mu n z) / (S n).c) * (nu D n + ω n)) :=
      mul_nonneg hCA0 (mul_nonneg hA0 (add_nonneg hν.le (hω0 n)))
    refine h2.trans ?_
    calc CA * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
            (S n).c) * (nu D n + ω n)) *
          testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
            ((S n).gB B)
        ≤ CA * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
            (S n).c) * (nu D n + ω n)) * (max CT 0 * bNorm D.K.as B) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hb0))
            hX
      _ = CA * max CT 0 * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
            nu D n ^ (3 + 2 * D.mu n z) / (S n).c) * (nu D n + ω n)) * bNorm D.K.as B := by
          ring
  · intro γ' h1 h2
    obtain ⟨CE, k, NE, hCE0, hCE⟩ := hE dm dp hst κ hκ m hm S hS γ' h1 h2
    refine ⟨CE * max CT 0, k, max (max NT NE) Nc, fun n hn z hz B hB => ?_⟩
    have h3 := hCT n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn) z hz B hB
    have h4 := hCE n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn) z hz B hB
    obtain ⟨hc, -⟩ := hNc n (le_trans (le_max_right _ _) hn)
    have hν := retNu_pos D.Pl D.σ₀ n
    have hA0 : 0 ≤ ‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
        (S n).c := by
      rw [hc]
      exact div_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hν.le _)) (cOf_pos hν).le
    have hb0 : 0 ≤ bNorm D.K.as B := ENNReal.toReal_nonneg
    have hX : 0 ≤ CE * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
        (S n).c) * ((nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n))) := by
      have : 0 ≤ (nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n)) := by positivity
      exact mul_nonneg (mul_nonneg hCE0 hA0) this
    refine h4.trans ?_
    calc CE * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
            (S n).c) * ((nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n))) *
          testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
            ((S n).gB B)
        ≤ CE * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
            (S n).c) * ((nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n))) *
            (max CT 0 * bNorm D.K.as B) :=
          mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hb0))
            hX
      _ = CE * max CT 0 * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
            nu D n ^ (3 + 2 * D.mu n z) / (S n).c) *
            ((nu D n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (nu D n))) * bNorm D.K.as B := by
          ring

end G3

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif
