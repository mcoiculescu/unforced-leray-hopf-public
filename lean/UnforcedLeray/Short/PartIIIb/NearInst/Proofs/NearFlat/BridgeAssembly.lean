import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearFlat.Inj
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearFlat.BridgeNorm

/-!
# The gained right inverse of `D₀` (`nearD0Surj_of_bridge`, source 3560-3581, 3875-3887)

Source of record: `the November 2 reference manuscript` (73 pages).

`cor:short-polynomial-stress` (source 3560-3581): `D₀⁻¹F = (F₁ - M₀b, F₂)`, `b = S_lin(F₁+F₂)`,
because "`b = S_{lin,μ}F` satisfies `b = S_{0,μ}(F - M₀b)` by free uniqueness".  In the concrete
near spaces (source 3866-3887) this reads, for `F ∈ Z`:

1. `IIIa.PolyStressCorollary`, applied to the planar blocks `F₁ = zBlk1 F`, `F₂ = zBlk2 F`
   (`zNorm2 (g⁻¹F₁) (g⁻¹F₂) ≤ ‖𝖦⁻¹F‖_Z`, `zNorm2_zBlk_le`), with the function-level train multiplier
   bound `FlatMultFunBound` as its hypothesis (`C_V = C`, `p_V = k`), gives `b`, `G` solving the
   free equation with tensor `T₀ = (F₁ - M₀b) + F₂` and the gained bound.
2. `b ∈ 𝓗`: `IIIa.FreeCausalExistsUnique` for `T₀` (finite `𝒯` norm by step 1) gives the unique
   solution, whose gained `𝓗` norm is finite; `b` is that solution a.e.
3. The near space `H` is real: `h = Re b ∈ H` (`memLp_reMer`); `Re b` solves the free equation with
   tensor `(F₁ - M₀ Re b) + F₂` (`isCausalEnergySolution_re`, `μ` real, `F₁`, `F₂` real).
4. `F' = F - M₀h`: by `IsFlatMult` the meridional block of `F'₁ + F'₂` is `(F₁ - M₀ Re b) + F₂` a.e.,
   so `Re b` and the representative of `S₀F'` given by `IsFreeStress` solve the same free equation;
   free uniqueness gives `S₀F' = h` (`s0_sub_M0_eq`), hence `D₀F' = F' + M₀h = F`.
5. `‖𝖦⁻¹F'‖ ≤ ‖𝖦⁻¹F‖ + ‖g⁻¹M₀ Re b‖_{𝒵₁} ≤ (2 + C'ν^{-M})‖𝖦⁻¹F‖ ≤ (2 + C')ν^{-M}‖𝖦⁻¹F‖` for
   `ν ≤ 1` (`norm_gainSymm_sub_M0_le`).

No hypothesis beyond those of the target is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.IIIa
  UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst UnforcedLeray.Blueprint.Planar

variable {c mZ ρb : ℝ}

/-- The real part of the free tensor `(F₁ - M₀b) + F₂` is `(F₁ - M₀ Re b) + F₂`. -/
theorem reTenC_stress (F : Zsp c mZ ρb) {ν' : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν' c)
    (b : Chart → Fin 2 → ℂ) :
    reTenC (fun p i j => (zBlk1 F p i j - flatMult tr b p i j) + zBlk2 F p i j) =
      fun p i j => (zBlk1 F p i j - flatMult tr (reVecC b) p i j) + zBlk2 F p i j := by
  funext p i j
  have e := congrFun (congrFun (congrFun (reTenC_flatMult tr b) p) i) j
  simp only [reTenC] at e ⊢
  rw [Complex.add_re, Complex.sub_re, Complex.ofReal_add, Complex.ofReal_sub, zBlk1_re, zBlk2_re,
    e]

/-- **`S₀(F - M₀h) = h`** (source 3577-3579, "by free uniqueness"): if `u` represents `h ∈ H` and
solves the free equation with tensor `(F₁ - M₀u) + F₂`, then `S₀(F - M₀h) = h`. -/
theorem s0_sub_M0_eq {ν μ γ : ℝ} (hν : 0 < ν) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (hρ1 : ρb ≤ 1)
    {o : NearOps (ν ^ (-2 : ℝ)) mZ ρb} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hM : IsFlatMult o.M0 tr) (hS : IsFreeStress o.S0 ν μ)
    (huniq : ∀ T : Chart → Fin 2 → Fin 2 → ℂ, (∀ p i j, T p i j = T p j i) →
      (∀ i j, Measurable fun p => T p i j) → tCalNorm (ν ^ (-2 : ℝ)) (gainConj γ ν T) < ⊤ →
      ∀ (b₁ : Chart → Fin 2 → ℂ) (G₁ : Chart → Fin 2 → Fin 2 → ℂ) (b₂ : Chart → Fin 2 → ℂ)
        (G₂ : Chart → Fin 2 → Fin 2 → ℂ),
        IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν (μ : ℂ) (fun _ _ _ => 0) T b₁ G₁ →
        IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν (μ : ℂ) (fun _ _ _ => 0) T b₂ G₂ →
        b₁ =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)))] b₂)
    (F : Zsp (ν ^ (-2 : ℝ)) mZ ρb) (h : Hsp (ν ^ (-2 : ℝ))) {u : Chart → Fin 2 → ℂ}
    {Gu : Chart → Fin 2 → Fin 2 → ℂ}
    (hu : velC (h : Chart → Merid) =ᵐ[ageμ (ν ^ (-2 : ℝ)) (-3 / 2)] u)
    (hsol : IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν (μ : ℂ) (fun _ _ _ => 0)
      (fun p i j => (zBlk1 F p i j - flatMult tr u p i j) + zBlk2 F p i j) u Gu) :
    o.S0 (F - o.M0 h) = h := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨b', G', hb', hsol'⟩ := hS (F - o.M0 h)
  obtain ⟨hMf, hMs⟩ := hM h
  -- the two components of `F - M₀h`
  have e1 : ((F - o.M0 h).fst : Chart → Ten3) =ᵐ[ageμ (ν ^ (-2 : ℝ)) (-1 / 2)]
      fun p => (F.fst : Chart → Ten3) p - ((o.M0 h).fst : Chart → Ten3) p := by
    have := Lp.coeFn_sub F.fst (o.M0 h).fst
    rw [ae_z1Measure] at this
    exact this
  have e2 : ((F - o.M0 h).snd : Chart → Ten3) = (F.snd : Chart → Ten3) := by
    rw [WithLp.sub_snd, hMs, sub_zero]
  rw [ae_z1Measure] at hMf
  have hzs : ∀ᵐ p ∂(ageμ (ν ^ (-2 : ℝ)) (-1 / 2)), zsum (F - o.M0 h) p =
      ((F.fst : Chart → Ten3) p - ten3Of (symOuter (trainMer tr p) (h p))) +
        (F.snd : Chart → Ten3) p := by
    filter_upwards [e1, hMf] with p h1 h2
    simp only [zsum]
    rw [h1, h2, e2]
  have hu' : velC (h : Chart → Merid) =ᵐ[ageμ (ν ^ (-2 : ℝ)) (-1 / 2)] u :=
    (ageμ_absCont (ν ^ (-2 : ℝ)) (-1 / 2) (-3 / 2)).ae_le hu
  -- the tensors of the two free equations agree a.e. on the half cell
  have hT : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)))),
      ∀ i j, (zBlk1 F p i j - flatMult tr u p i j) + zBlk2 F p i j =
        merBlockC (zsum (F - o.M0 h)) p i j := by
    filter_upwards [(volCyl_ac_ageμ hc (-1 / 2)).ae_le (hzs.and hu')] with p hp i j
    obtain ⟨h1, h2⟩ := hp
    have h2' : ∀ k, u p k = (((h : Chart → Merid) p k : ℝ) : ℂ) := fun k => by
      rw [← h2]; rfl
    simp only [merBlockC, h1, nsSym_add, nsSym_sub, nsSym_ten3Of_symOuter, flatMult, h2',
      zBlk1, zBlk2, trainMer_apply]
    push_cast
    ring
  have hI : ∀ Φ, flatIntegrand ν (μ : ℂ) (fun _ _ _ => 0)
      (fun p i j => (zBlk1 F p i j - flatMult tr u p i j) + zBlk2 F p i j) u Φ
        =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)))]
      flatIntegrand ν (μ : ℂ) (fun _ _ _ => 0) (merBlockC (zsum (F - o.M0 h))) u Φ := by
    intro Φ
    filter_upwards [hT] with p hp
    unfold flatIntegrand
    simp only [hp]
  have hsolT := causal_transport hsol hI
  -- free uniqueness
  have hTsym : ∀ p i j, merBlockC (zsum (F - o.M0 h)) p i j =
      merBlockC (zsum (F - o.M0 h)) p j i := merBlockC_symm _
  have hTmeas : ∀ i j, Measurable fun p => merBlockC (zsum (F - o.M0 h)) p i j := by
    rw [merBlockC_zsum_fun]
    intro i j
    exact (measurable_zBlk1 _ i j).add (measurable_zBlk2 _ i j)
  have hTfin := tCalNorm_gainConj_merBlockC_zsum_lt_top (γ := γ) hν hmZ hρ hρ1 (F - o.M0 h)
  have hbu := huniq _ hTsym hTmeas hTfin b' G' u Gu hsol' hsolT
  have hbu' : b' =ᵐ[ageμ (ν ^ (-2 : ℝ)) (-3 / 2)] u :=
    (ageμ_ac_volCyl (ν ^ (-2 : ℝ)) (-3 / 2)).ae_le hbu
  apply Lp.ext
  filter_upwards [hb', hbu', hu] with p h1 h2 h3
  have key : velC (o.S0 (F - o.M0 h) : Chart → Merid) p = velC (h : Chart → Merid) p := by
    rw [← h1, h2, h3]
  ext k
  have := congrFun key k
  simpa [velC] using this

/-- **The gained bound for `D₀⁻¹F = F - M₀ Re b`** (source 3573-3581): with the corollary's bound
`zNorm2 (g⁻¹(F₁ - M₀b)) (g⁻¹F₂) ≤ C_S ν^{-M} zNorm2 (g⁻¹F₁) (g⁻¹F₂)` and `ν ≤ 1`,
`‖𝖦⁻¹(F - M₀h)‖ ≤ (2 + C_S⁺) ν^{-M} ‖𝖦⁻¹F‖` for `h` represented by `Re b`. -/
theorem norm_gainSymm_sub_M0_le {ν γ CS : ℝ} {M : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hρ : 0 < ρb)
    {o : NearOps c mZ ρb} {tr : UnforcedLeray.B0140.TrainSol ν c} (hM : IsFlatMult o.M0 tr)
    (F : Zsp c mZ ρb) (h : Hsp c) {b : Chart → Fin 2 → ℂ} (hbm : ∀ i, Measurable fun p => b p i)
    (hu : velC (h : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] reVecC b)
    (hbd : zNorm2 c mZ ρb (gainConj γ ν (fun p i j => zBlk1 F p i j - flatMult tr b p i j))
        (gainConj γ ν (zBlk2 F)) ≤
      ENNReal.ofReal (CS * ν ^ (-(M : ℝ))) *
        zNorm2 c mZ ρb (gainConj γ ν (zBlk1 F)) (gainConj γ ν (zBlk2 F))) :
    ‖(gainEquiv c mZ ρb γ hν).symm (F - o.M0 h)‖ ≤
      (2 + max CS 0) * ν⁻¹ ^ M * ‖(gainEquiv c mZ ρb γ hν).symm F‖ := by
  set X := ‖(gainEquiv c mZ ρb γ hν).symm F‖ with hX
  set Y := ‖(gainEquiv c mZ ρb γ hν).symm (o.M0 h)‖ with hY
  set Z := zNorm2 c mZ ρb (gainConj γ ν (zBlk1 F)) (gainConj γ ν (zBlk2 F)) with hZdef
  have hZ : Z ≤ ENNReal.ofReal X := zNorm2_zBlk_le hν hρ F
  have hX0 : 0 ≤ X := norm_nonneg _
  have hY0 : 0 ≤ Y := norm_nonneg _
  -- `‖𝖦⁻¹M₀h‖ ≤ ‖g⁻¹M₀(Re b)‖_{𝒵₁}`
  have hY1 : ENNReal.ofReal Y ≤ z1Norm2 c mZ (gainConj γ ν (flatMult tr (velC (h : Chart → Merid)))) :=
    ofReal_norm_gainSymm_M0_le hν hM h
  have hY2 : z1Norm2 c mZ (gainConj γ ν (flatMult tr (velC (h : Chart → Merid)))) =
      z1Norm2 c mZ (gainConj γ ν (flatMult tr (reVecC b))) := by
    unfold z1Norm2
    apply eLpNorm_congr_ae
    filter_upwards [(ageμ_absCont c (-1 / 2) (-3 / 2)).ae_le hu] with p hp
    have e : flatMult tr (velC (h : Chart → Merid)) p = flatMult tr (reVecC b) p := by
      funext i j
      simp only [flatMult, hp]
    simp only [gainConj, e]
  have hY3 : z1Norm2 c mZ (gainConj γ ν (flatMult tr (reVecC b))) ≤
      z1Norm2 c mZ (gainConj γ ν (flatMult tr b)) := by
    unfold z1Norm2
    refine eLpNorm_mono_ae ?_
    filter_upwards [ae_pos_ageμ_chart c (-1 / 2)] with p hpos
    have hW := (transWeight_pos mZ p).le
    have hI := (gainInvFun_pos_chart γ ν p).le
    rw [tnorm2_gainConj _ hpos.le, tnorm2_gainConj _ hpos.le, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hW (mul_nonneg hI (tnorm2_nonneg _))),
      abs_of_nonneg (mul_nonneg hW (mul_nonneg hI (tnorm2_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (tnorm2_flatMult_reVecC_le tr b p) hI) hW
  -- `M₀b = F₁ - (F₁ - M₀b)`
  have hm1 : ∀ i j, Measurable fun p => gainConj γ ν (zBlk1 F) p i j :=
    measurable_gainConj (measurable_zBlk1 F)
  have hm2 : ∀ i j, Measurable fun p =>
      gainConj γ ν (fun p i j => zBlk1 F p i j - flatMult tr b p i j) p i j :=
    measurable_gainConj fun i j => (measurable_zBlk1 F i j).sub (measurable_flatMult tr hbm i j)
  have hY4 : z1Norm2 c mZ (gainConj γ ν (flatMult tr b)) ≤
      z1Norm2 c mZ (gainConj γ ν (zBlk1 F)) +
        z1Norm2 c mZ (gainConj γ ν (fun p i j => zBlk1 F p i j - flatMult tr b p i j)) := by
    have e : gainConj γ ν (flatMult tr b) = fun p i j => gainConj γ ν (zBlk1 F) p i j -
        gainConj γ ν (fun p i j => zBlk1 F p i j - flatMult tr b p i j) p i j := by
      funext p i j
      simp [gainConj, smul_sub]
    rw [e]
    exact z1Norm2_sub_le hm1 hm2
  have hz1 : z1Norm2 c mZ (gainConj γ ν (zBlk1 F)) ≤ Z := le_self_add
  have hz2 : z1Norm2 c mZ (gainConj γ ν (fun p i j => zBlk1 F p i j - flatMult tr b p i j)) ≤
      ENNReal.ofReal (max CS 0 * ν ^ (-(M : ℝ))) * Z := by
    refine le_self_add.trans (hbd.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hν.le _)
  set a := max CS 0 * ν ^ (-(M : ℝ)) with ha
  have ha0 : 0 ≤ a := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hν.le _)
  have hYZ : ENNReal.ofReal Y ≤ ENNReal.ofReal ((1 + a) * X) := by
    calc ENNReal.ofReal Y ≤ Z + ENNReal.ofReal a * Z :=
          hY1.trans (hY2.le.trans (hY3.trans (hY4.trans (add_le_add hz1 hz2))))
      _ ≤ ENNReal.ofReal X + ENNReal.ofReal a * ENNReal.ofReal X :=
          add_le_add hZ (mul_le_mul_right hZ _)
      _ = ENNReal.ofReal ((1 + a) * X) := by
          rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_add hX0 (mul_nonneg ha0 hX0)]
          congr 1
          ring
  have hYr : Y ≤ (1 + a) * X :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith) hX0)).1 hYZ
  have htri : ‖(gainEquiv c mZ ρb γ hν).symm (F - o.M0 h)‖ ≤ X + Y := by
    rw [map_sub]
    exact norm_sub_le _ _
  have hpow : ν ^ (-(M : ℝ)) = ν⁻¹ ^ M := by
    rw [Real.rpow_neg hν.le, Real.rpow_natCast, inv_pow]
  have hge1 : 1 ≤ ν⁻¹ ^ M := one_le_pow₀ ((one_le_inv₀ hν).2 hν1)
  rw [ha, hpow] at hYr
  have hCS : 0 ≤ max CS 0 := le_max_right _ _
  calc ‖(gainEquiv c mZ ρb γ hν).symm (F - o.M0 h)‖ ≤ X + Y := htri
    _ ≤ X + (1 + max CS 0 * ν⁻¹ ^ M) * X := by linarith
    _ = (2 + max CS 0 * ν⁻¹ ^ M) * X := by ring
    _ ≤ (2 + max CS 0) * ν⁻¹ ^ M * X := by
        apply mul_le_mul_of_nonneg_right _ hX0
        nlinarith

/-- **Gained right inverse of `D₀`** (source 3560-3581, 3875-3887): `NearD0Surj` from
`cor:short-polynomial-stress`, the free causal solver with uniqueness and the function-level train
multiplier bound. -/
theorem nearD0Surj_of_bridge (hPS : PolyStressCorollary) (hU : FreeCausalExistsUnique)
    (hA : FlatMultFunBound) : NearD0Surj := by
  intro P hP Kset hK hKs mZ hmZ
  have hmZ0 : 0 ≤ mZ := by linarith
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Kset with hKdef
  have hKadm : IsAdmissibleK K := by
    refine ⟨hK.image Complex.continuous_ofReal, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h0, h1⟩ := hKs hx
    simp only [Complex.ofReal_re]
    exact ⟨h0, h1⟩
  obtain ⟨ν₁, hν₁, hUν⟩ := hU P hP K hKadm
  obtain ⟨CA, k, ν₂, hν₂, hAν⟩ := hA mZ hmZ
  obtain ⟨M, hM⟩ := hPS P hP K hKadm mZ hmZ k
  obtain ⟨C', ν₃, hν₃, hPSν⟩ := hM CA
  refine ⟨2 + max C' 0, M, min (min ν₁ ν₂) (min ν₃ 1),
    by positivity, lt_min (lt_min hν₁ hν₂) (lt_min hν₃ one_pos), ?_⟩
  intro ν hν hνle c hc tr htr ρb hρ hρ1 μ hμ o hMo hSo F
  have hνν₁ : ν ≤ ν₁ := hνle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνν₂ : ν ≤ ν₂ := hνle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνν₃ : ν ≤ ν₃ := hνle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : ν ≤ 1 := hνle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc' : c = ν ^ (-2 : ℝ) := by rw [hc, Real.rpow_neg hν.le, Real.rpow_two]
  subst hc'
  have hμK : (μ : ℂ) ∈ K := ⟨μ, hμ, rfl⟩
  -- free uniqueness in the form used by `s0_sub_M0_eq`
  have huniq : ∀ T : Chart → Fin 2 → Fin 2 → ℂ, (∀ p i j, T p i j = T p j i) →
      (∀ i j, Measurable fun p => T p i j) →
      tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν T) < ⊤ →
      ∀ (b₁ : Chart → Fin 2 → ℂ) (G₁ : Chart → Fin 2 → Fin 2 → ℂ) (b₂ : Chart → Fin 2 → ℂ)
        (G₂ : Chart → Fin 2 → Fin 2 → ℂ),
        IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν (μ : ℂ) (fun _ _ _ => 0) T b₁ G₁ →
        IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν (μ : ℂ) (fun _ _ _ => 0) T b₂ G₂ →
        b₁ =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)))] b₂ := by
    intro T hs hm hf b₁ G₁ b₂ G₂ h1 h2
    obtain ⟨b₀, G₀, -, -, -, hu⟩ := hUν ν ⟨hν, hνν₁⟩ (μ : ℂ) hμK T hs hm hf
    exact (hu b₁ G₁ h1).trans (hu b₂ G₂ h2).symm
  -- step 1: the corollary on the planar blocks
  have hV := hAν ν ⟨hν, hνν₂⟩ tr htr
  have hfinZ : zNorm2 (ν ^ (-2 : ℝ)) mZ ρb (gainConj P.eigenvalue.re ν (zBlk1 F))
      (gainConj P.eigenvalue.re ν (zBlk2 F)) < ⊤ :=
    (zNorm2_zBlk_le hν hρ F).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨b, G, -, hsolF, hbd⟩ := hPSν ν ⟨hν, hνν₃⟩ tr htr ρb hρ hρ1 hV (μ : ℂ) hμK
    (zBlk1 F) (zBlk2 F) (zBlk1_symm F) (zBlk2_symm F) (measurable_zBlk1 F) (measurable_zBlk2 F)
    hfinZ
  -- step 2: `b ∈ 𝓗` through the free solver for `T₀ = (F₁ - M₀b) + F₂`
  have hT₀m1 : ∀ i j, Measurable fun p => zBlk1 F p i j - flatMult tr b p i j :=
    fun i j => (measurable_zBlk1 F i j).sub (measurable_flatMult tr hsolF.measurable i j)
  have hT₀s : ∀ p i j, (zBlk1 F p i j - flatMult tr b p i j) + zBlk2 F p i j =
      (zBlk1 F p j i - flatMult tr b p j i) + zBlk2 F p j i := by
    intro p i j
    rw [zBlk1_symm F p i j, zBlk2_symm F p i j]
    simp only [flatMult]
    ring
  have hT₀m : ∀ i j, Measurable fun p => (zBlk1 F p i j - flatMult tr b p i j) + zBlk2 F p i j :=
    fun i j => (hT₀m1 i j).add (measurable_zBlk2 F i j)
  have hT₀f : tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν
      (fun p i j => (zBlk1 F p i j - flatMult tr b p i j) + zBlk2 F p i j)) < ⊤ :=
    (tCalNorm_gainConj_add_le_zNorm2 hmZ0 hρ hρ1 hT₀m1 (measurable_zBlk2 F)).trans_lt
      (hbd.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinZ))
  obtain ⟨b₀, G₀, -, hb₀, -, hu₀⟩ := hUν ν ⟨hν, hνν₁⟩ (μ : ℂ) hμK _ hT₀s hT₀m hT₀f
  have hbb₀ := hu₀ b G hsolF
  have hgb : hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b) < ⊤ := by
    have e : hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b) =
        hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) := by
      unfold hCalNorm
      apply eLpNorm_congr_ae
      filter_upwards [(ageμ_ac_volCyl (ν ^ (-2 : ℝ)) (-3 / 2)).ae_le hbb₀] with p hp
      simp only [gainConj, hp]
    rw [e]
    exact hb₀.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT₀f)
  have hbfin := hCalNorm_lt_top_of_gainConj hν hgb
  -- step 3: `h = Re b ∈ H`, solving the free equation with tensor `(F₁ - M₀ Re b) + F₂`
  have hmem := memLp_reMer hsolF.measurable hbfin
  obtain ⟨h, hh⟩ : ∃ h : Hsp (ν ^ (-2 : ℝ)),
      velC (h : Chart → Merid) =ᵐ[ageμ (ν ^ (-2 : ℝ)) (-3 / 2)] reVecC b := by
    refine ⟨hmem.toLp _, ?_⟩
    filter_upwards [MemLp.coeFn_toLp hmem] with p hp
    rw [← velC_reMer]
    funext i
    simp only [velC, hp]
  have hre := isCausalEnergySolution_re hsolF
  rw [reTenC_stress] at hre
  -- step 4: `D₀(F - M₀h) = F`; step 5: the bound
  refine ⟨F - o.M0 h, ?_, norm_gainSymm_sub_M0_le hν hν1 hρ hMo F h hsolF.measurable hh hbd⟩
  have hS0 : o.S0 (F - o.M0 h) = h := s0_sub_M0_eq hν hmZ0 hρ hρ1 hMo hSo huniq F h hh hre
  simp [NearOps.D0, hS0]

#print axioms nearD0Surj_of_bridge

end UnforcedLeray.Short.PartIIIb.NearInst
