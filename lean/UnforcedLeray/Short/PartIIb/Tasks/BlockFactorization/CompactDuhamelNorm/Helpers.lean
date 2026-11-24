import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_4
import UnforcedLeray.Short.PartIIb.Org.RealCompactDuhamel
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenTransportCont

/-!
# Helpers for `PartII-b:F2/4/3` (`CompactDuhamelNorm/Helpers.lean`)

Provides reusable operator-theoretic and window-lifting lemmas for `compactDuhamelNormConvergence_proof`:
1. Adjoint and norm of the frozen radial transport `T_pl σ τ` (`adjoint_T_pl`, `norm_T_pl_le_one`);
2. Uniform continuity in slow age of `(σ, τ) ↦ T_pl σ τ x` on `[0, Sig] × [-Lmax, Lmax]`
   (`exists_age_delta_T_pl`) and compactness of orbit images (`isCompact_T_pl_image`) from
   `frozenTransportJointCont_proof`;
3. Semigroup Duhamel evolution structure for `(T_pl σ, AplOp σ, E_pl σ)` (`isDuhamelEvolution_planar`)
   and planar operator-norm convergence along `σ_n → σ*` (`planar_diff_tendsto`);
4. Window Duhamel evolution structure for the lifted cylinder propagator on `[t', t' + Lmax]`
   (`isDuhamelEvolutionOn_lifted`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real Metric

namespace UnforcedLeray.Short.IIb.CompactDuhamelNormHelp

open UnforcedLeray.Cons.C03.Concrete

/-- `T_pl σ τ` has operator norm at most `1` on `Xm m` for `σ ∈ [0, Sig]`. -/
theorem norm_T_pl_le_one {m Sig : ℝ} {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)}
    (hT : IsFrozenRadialTransport m Sig T_pl) {σ : ℝ} (hσ : σ ∈ Icc 0 Sig) (τ : ℝ) :
    ‖T_pl σ τ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [hT.isometry σ hσ τ f, one_mul]

/-- Group inverse application `T_pl σ τ (T_pl σ (-τ) y) = y`. -/
theorem T_pl_apply_neg {m Sig : ℝ} {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)}
    (hT : IsFrozenRadialTransport m Sig T_pl) {σ : ℝ} (hσ : σ ∈ Icc 0 Sig) (τ : ℝ) (y : Xm m) :
    T_pl σ τ (T_pl σ (-τ) y) = y := by
  have h := congrArg (fun A : Xm m →L[ℝ] Xm m => A y) (hT.add σ hσ τ (-τ))
  rw [add_neg_cancel, hT.zero σ hσ] at h
  exact h.symm

/-- Group inverse application `T_pl σ (-τ) (T_pl σ τ y) = y`. -/
theorem T_pl_neg_apply {m Sig : ℝ} {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)}
    (hT : IsFrozenRadialTransport m Sig T_pl) {σ : ℝ} (hσ : σ ∈ Icc 0 Sig) (τ : ℝ) (y : Xm m) :
    T_pl σ (-τ) (T_pl σ τ y) = y := by
  simpa only [neg_neg] using T_pl_apply_neg hT hσ (-τ) y

/-- The Hilbert-space adjoint of the isometric group `T_pl σ τ` is `T_pl σ (-τ)` (SP 2109–2113). -/
theorem adjoint_T_pl {m Sig : ℝ} {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)}
    (hT : IsFrozenRadialTransport m Sig T_pl) {σ : ℝ} (hσ : σ ∈ Icc 0 Sig) (τ : ℝ) :
    ContinuousLinearMap.adjoint (T_pl σ τ) = T_pl σ (-τ) := by
  have hiso : ∀ x z : Xm m, inner ℝ (T_pl σ τ x) (T_pl σ τ z) = inner ℝ x z := by
    intro x z
    have h1 := norm_add_sq_real (T_pl σ τ x) (T_pl σ τ z)
    have h2 := norm_add_sq_real x z
    have h3 : ‖T_pl σ τ x + T_pl σ τ z‖ ^ 2 = ‖x + z‖ ^ 2 := by
      rw [← map_add, hT.isometry σ hσ τ (x + z)]
    rw [h1, h2, hT.isometry σ hσ τ x, hT.isometry σ hσ τ z] at h3
    linarith
  refine ContinuousLinearMap.ext fun y => ?_
  have hdiff : ∀ x : Xm m,
      inner ℝ x (ContinuousLinearMap.adjoint (T_pl σ τ) y - T_pl σ (-τ) y) = 0 := by
    intro x
    rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
    have hinv : inner ℝ (T_pl σ τ x) y = inner ℝ x (T_pl σ (-τ) y) := by
      calc inner ℝ (T_pl σ τ x) y
          = inner ℝ (T_pl σ τ x) (T_pl σ τ (T_pl σ (-τ) y)) := by
              rw [T_pl_apply_neg hT hσ τ y]
        _ = inner ℝ x (T_pl σ (-τ) y) := hiso x (T_pl σ (-τ) y)
    linarith
  exact sub_eq_zero.1 (inner_self_eq_zero.1 (hdiff _))

/-- Continuity of `(σ, τ) ↦ T_pl σ τ x` on `[0, Sig] × ℝ` for fixed `x : Xm m`. -/
theorem continuousOn_T_pl_apply {m Sig : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)} (hT : IsFrozenRadialTransport m Sig T_pl) (x : Xm m) :
    ContinuousOn (fun q : ℝ × ℝ => T_pl q.1 q.2 x) (Icc 0 Sig ×ˢ univ) := by
  have hjoint := frozenTransportJointCont_proof m hm Sig hSig T_pl hT
  refine hjoint.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn ?_
  rintro ⟨σ, τ⟩ ⟨hσ, _⟩
  exact ⟨hσ, trivial⟩

/-- Uniform continuity in slow age of `T_pl σ τ x` on `[0, Sig] × [-Lmax, Lmax]`. -/
theorem exists_age_delta_T_pl {m Sig Lmax : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)} (hT : IsFrozenRadialTransport m Sig T_pl)
    (x : Xm m) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ_u : ℝ, 0 < δ_u ∧ ∀ ⦃σ₁ σ₂ τ : ℝ⦄, σ₁ ∈ Icc 0 Sig → σ₂ ∈ Icc 0 Sig →
      τ ∈ Icc (-Lmax) Lmax → |σ₁ - σ₂| < δ_u → ‖T_pl σ₁ τ x - T_pl σ₂ τ x‖ < ε := by
  let Q : Set (ℝ × ℝ) := Icc 0 Sig ×ˢ Icc (-Lmax) Lmax
  have hQc : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun q : ℝ × ℝ => T_pl q.1 q.2 x) Q :=
    (continuousOn_T_pl_apply hm hSig hT x).mono fun q hq => ⟨hq.1, trivial⟩
  have hunif : UniformContinuousOn (fun q : ℝ × ℝ => T_pl q.1 q.2 x) Q :=
    hQc.uniformContinuousOn_of_continuous hcont
  obtain ⟨δ_u, hδ_u, hdist⟩ := Metric.uniformContinuousOn_iff.1 hunif ε hε
  refine ⟨δ_u, hδ_u, fun σ₁ σ₂ τ hσ₁ hσ₂ hτ hlt => ?_⟩
  have hd : dist (σ₁, τ) (σ₂, τ) < δ_u := by
    rw [Prod.dist_eq, Real.dist_eq, dist_self]
    exact max_lt hlt hδ_u
  have h := hdist (σ₁, τ) ⟨hσ₁, hτ⟩ (σ₂, τ) ⟨hσ₂, hτ⟩ hd
  simpa only [dist_eq_norm] using h

/-- Compactness of the orbit `{T_pl σ τ x : σ ∈ [0, Sig], τ ∈ [0, Lmax]}`. -/
theorem isCompact_T_pl_image {m Sig Lmax : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)} (hT : IsFrozenRadialTransport m Sig T_pl) (x : Xm m) :
    IsCompact ((fun q : ℝ × ℝ => T_pl q.1 q.2 x) '' (Icc 0 Sig ×ˢ Icc 0 Lmax)) := by
  refine (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn ?_
  exact (continuousOn_T_pl_apply hm hSig hT x).mono fun q hq => ⟨hq.1, trivial⟩

/-- Semigroup Duhamel evolution structure for `(T_pl σ, AplOp σ, E_pl σ)` on blocks of length `Lmax`. -/
theorem isDuhamelEvolution_planar {m Sig Lmax : ℝ}
    {AplOp : ℝ → (Xm m →L[ℝ] Xm m)}
    {T_pl E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)}
    (hEcont : ∀ σ ∈ Icc 0 Sig, ∀ f : Xm m, ContinuousOn (fun τ => E_pl σ τ f) (Ici 0))
    (hEmild : ∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ → ∀ f : Xm m,
      IntervalIntegrable (fun r => T_pl σ (τ - r) (AplOp σ (E_pl σ r f))) volume 0 τ ∧
      E_pl σ τ f = T_pl σ τ f + ∫ r in (0 : ℝ)..τ, T_pl σ (τ - r) (AplOp σ (E_pl σ r f)))
    {σ : ℝ} (hσ : σ ∈ Icc 0 Sig) :
    RCDuhamel.IsDuhamelEvolution (𝕜 := ℝ) Lmax
      (fun (_ : Unit) t s => T_pl σ (t - s))
      (fun (_ : Unit) _ => AplOp σ)
      (fun (_ : Unit) t s => E_pl σ (t - s)) := by
  refine RCDuhamel.isDuhamelEvolution_of_semigroup (B := Lmax)
    (T := fun (_ : Unit) τ => T_pl σ τ)
    (E := fun (_ : Unit) τ => E_pl σ τ)
    (A := fun (_ : Unit) => AplOp σ)
    (fun _ τ h0 _ f => hEmild σ hσ τ h0 f) ?_
  intro _
  obtain ⟨C, hC⟩ := RCDuhamel.exists_norm_le_of_continuousOn (𝕜 := ℝ) (H := Xm m)
    (E := E_pl σ) (c := 0) (d := Lmax) (fun f => (hEcont σ hσ f).mono Icc_subset_Ici_self)
  exact ⟨C, fun τ h0 hL => hC τ ⟨h0, hL⟩⟩

/-- Planar side: as `σn n → σstar` in `[0, Sig]`, `(E_pl (σn n) - T_pl (σn n))(t - s)` converges
uniformly in operator norm on blocks `s ≤ t ≤ s + Lmax` to `(E_pl σstar - T_pl σstar)(t - s)`. -/
theorem planar_diff_tendsto {m Sig Lmax : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    {AplOp : ℝ → (Xm m →L[ℝ] Xm m)}
    (hAcont : ContinuousOn AplOp (Icc 0 Sig))
    (hAop : ∀ σ ∈ Icc 0 Sig, IsPlanarInteractionOp m σ (AplOp σ) ∧ IsCompactOperator (AplOp σ))
    {T_pl E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)}
    (hT : IsFrozenRadialTransport m Sig T_pl)
    (hEcont : ∀ σ ∈ Icc 0 Sig, ∀ f : Xm m, ContinuousOn (fun τ => E_pl σ τ f) (Ici 0))
    (hEmild : ∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ → ∀ f : Xm m,
      IntervalIntegrable (fun r => T_pl σ (τ - r) (AplOp σ (E_pl σ r f))) volume 0 τ ∧
      E_pl σ τ f = T_pl σ τ f + ∫ r in (0 : ℝ)..τ, T_pl σ (τ - r) (AplOp σ (E_pl σ r f)))
    {σn : ℕ → ℝ} {σstar : ℝ}
    (hσn : ∀ n, σn n ∈ Icc 0 Sig) (hσstar : σstar ∈ Icc 0 Sig)
    (hσlim : Tendsto σn atTop (nhds σstar)) :
    RCDuhamel.NormTendstoOnBlocks atTop Lmax
      (fun n (_ : Unit) t s => E_pl (σn n) (t - s) - T_pl (σn n) (t - s))
      (fun (_ : Unit) t s => E_pl σstar (t - s) - T_pl σstar (t - s)) := by
  obtain ⟨K_A, hK_A⟩ := isCompact_Icc.exists_bound_of_continuousOn hAcont
  have hFb : ∃ M, ∀ (n : ℕ) (p : Unit) (t s : ℝ), s ≤ t → t ≤ s + Lmax →
      ‖T_pl (σn n) (t - s)‖ ≤ M ∧ ‖T_pl σstar (t - s)‖ ≤ M :=
    ⟨1, fun n _ t s _ _ => ⟨norm_T_pl_le_one hT (hσn n) _, norm_T_pl_le_one hT hσstar _⟩⟩
  have hF : RCDuhamel.StrongTendstoOnBlocks atTop Lmax
      (fun n (_ : Unit) t s => T_pl (σn n) (t - s))
      (fun (_ : Unit) t s => T_pl σstar (t - s)) := by
    intro x ε hε
    obtain ⟨δ_u, hδ_u, hage⟩ := exists_age_delta_T_pl (Lmax := Lmax) hm hSig hT x hε
    filter_upwards [Metric.tendsto_nhds.1 hσlim δ_u hδ_u] with n hn _ t s hst hts
    have hL0 : 0 ≤ Lmax := by linarith
    refine hage (hσn n) hσstar ⟨by linarith, by linarith⟩ ?_
    simpa only [Real.dist_eq] using hn
  have hFadj : RCDuhamel.StrongTendstoOnBlocks atTop Lmax
      (fun n (_ : Unit) t s => ContinuousLinearMap.adjoint (T_pl (σn n) (t - s)))
      (fun (_ : Unit) t s => ContinuousLinearMap.adjoint (T_pl σstar (t - s))) := by
    intro x ε hε
    obtain ⟨δ_u, hδ_u, hage⟩ := exists_age_delta_T_pl (Lmax := Lmax) hm hSig hT x hε
    filter_upwards [Metric.tendsto_nhds.1 hσlim δ_u hδ_u] with n hn _ t s hst hts
    rw [adjoint_T_pl hT (hσn n), adjoint_T_pl hT hσstar]
    refine hage (hσn n) hσstar ⟨by linarith, by linarith⟩ ?_
    simpa only [Real.dist_eq] using hn
  have hAb : ∃ K, ∀ (n : ℕ) (_ : Unit) (_ : ℝ), ‖AplOp (σn n)‖ ≤ K :=
    ⟨K_A, fun n _ _ => hK_A (σn n) (hσn n)⟩
  have hAtend : Tendsto (fun n => AplOp (σn n)) atTop (nhds (AplOp σstar)) :=
    (hAcont σstar hσstar).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hσlim, Eventually.of_forall hσn⟩)
  have hA : ∀ ε > 0, ∀ᶠ n in atTop, ∀ (_ : Unit) (_ : ℝ), ‖AplOp (σn n) - AplOp σstar‖ < ε := by
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.1 hAtend ε hε] with n hn _ _
    rwa [dist_eq_norm] at hn
  have hA₀c : ∀ (_ : Unit) (_ : ℝ), IsCompactOperator (AplOp σstar) :=
    fun _ _ => (hAop σstar hσstar).2
  have hA₀p : TotallyBounded (range fun _ : Unit × ℝ => AplOp σstar) := by
    refine (Set.finite_singleton (AplOp σstar)).totallyBounded.subset ?_
    rintro _ ⟨_, rfl⟩
    exact mem_singleton _
  exact (RCDuhamel.real_compact_duhamel hFb hF hFadj hAb hA hA₀c hA₀p
    (fun n => isDuhamelEvolution_planar hEcont hEmild (hσn n))
    (isDuhamelEvolution_planar hEcont hEmild hσstar)).2.2

/-- Window Duhamel evolution structure on `[0, Lmax]` for the lifted cylinder propagators shifted by
`t'` when `[t', t' + Lmax] ⊆ [0, p.H]`. -/
theorem isDuhamelEvolutionOn_lifted {m Lmax : ℝ} {p : Params}
    {Sc U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hCD : IsCoupledDuhamelPropagator m p Sc Ac U)
    {t' : ℝ} (ht'0 : 0 ≤ t') (ht'H : t' + Lmax ≤ p.H) :
    RCDuhamel.IsDuhamelEvolutionOn (𝕜 := ℝ) 0 Lmax
      (fun (_ : Unit) τ ρ => (Jc p.c m).comp ((Sc (t' + τ) (t' + ρ)).comp (Rc p.c m)))
      (fun (_ : Unit) r => (Jc p.c m).comp ((Ac (t' + r)).comp (Rc p.c m)))
      (fun (_ : Unit) τ ρ => (Jc p.c m).comp ((U (t' + τ) (t' + ρ)).comp (Rc p.c m))) where
  integrable _ ρ τ hρ hρτ hτ x := by
    have hs : 0 ≤ t' + ρ := by linarith
    have hst : t' + ρ ≤ t' + τ := by linarith
    have ht : t' + τ ≤ p.H := by linarith
    have hint := hCD.duhamel_integrable (t' + ρ) (t' + τ) hs hst ht (Rc p.c m x)
    have hshift : IntervalIntegrable
        (fun r => Sc (t' + τ) (r + t') (Ac (r + t') (U (r + t') (t' + ρ) (Rc p.c m x))))
        volume ρ τ := by
      have h1 := hint.comp_add_right t'
      simpa only [add_sub_cancel_left] using h1
    have hJc : IntervalIntegrable
        (fun r => Jc p.c m (Sc (t' + τ) (r + t') (Ac (r + t') (U (r + t') (t' + ρ) (Rc p.c m x)))))
        volume ρ τ :=
      ⟨(Jc p.c m).integrable_comp hshift.1, (Jc p.c m).integrable_comp hshift.2⟩
    refine hJc.congr fun r _ => ?_
    simp only [ContinuousLinearMap.comp_apply, Rc_Jc, add_comm r t']
  duhamel _ ρ τ hρ hρτ hτ x := by
    have hs : 0 ≤ t' + ρ := by linarith
    have hst : t' + ρ ≤ t' + τ := by linarith
    have ht : t' + τ ≤ p.H := by linarith
    have hint := hCD.duhamel_integrable (t' + ρ) (t' + τ) hs hst ht (Rc p.c m x)
    have hshift : IntervalIntegrable
        (fun r => Sc (t' + τ) (r + t') (Ac (r + t') (U (r + t') (t' + ρ) (Rc p.c m x))))
        volume ρ τ := by
      simpa only [add_sub_cancel_left] using hint.comp_add_right t'
    have hfun : (fun r => ((Jc p.c m).comp ((Sc (t' + τ) (t' + r)).comp (Rc p.c m)))
          (((Jc p.c m).comp ((Ac (t' + r)).comp (Rc p.c m)))
            (((Jc p.c m).comp ((U (t' + r) (t' + ρ)).comp (Rc p.c m))) x))) =
        fun r => Jc p.c m (Sc (t' + τ) (r + t') (Ac (r + t') (U (r + t') (t' + ρ) (Rc p.c m x)))) := by
      funext r
      simp only [ContinuousLinearMap.comp_apply, Rc_Jc, add_comm r t']
    rw [hfun, (Jc p.c m).intervalIntegral_comp_comm hshift]
    have hcv := intervalIntegral.integral_comp_add_right
      (fun u => Sc (t' + τ) u (Ac u (U u (t' + ρ) (Rc p.c m x)))) t' (a := ρ) (b := τ)
    simp only [add_comm ρ t', add_comm τ t'] at hcv
    rw [hcv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hCD.duhamel_eq (t' + ρ) (t' + τ) hs hst ht (Rc p.c m x), map_add]
  bounded _ ρ hρ hρL := by
    have hs_mem : t' + ρ ∈ Icc 0 p.H := ⟨by linarith, by linarith⟩
    have hcont : ∀ x : Xm m, ContinuousOn
        (fun τ => ((Jc p.c m).comp ((U (t' + τ) (t' + ρ)).comp (Rc p.c m))) x) (Icc ρ Lmax) := by
      intro x
      have hu := hCD.coupled_prop.strongCont (t' + ρ) hs_mem (Rc p.c m x)
      have hsh : ContinuousOn (fun τ => U (t' + τ) (t' + ρ) (Rc p.c m x)) (Icc ρ Lmax) :=
        hu.comp (continuous_const.add continuous_id).continuousOn fun τ hτ =>
          ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      exact (Jc p.c m).continuous.comp_continuousOn hsh
    obtain ⟨C, hC⟩ := RCDuhamel.exists_norm_le_of_continuousOn (𝕜 := ℝ) (H := Xm m)
      (E := fun τ => (Jc p.c m).comp ((U (t' + τ) (t' + ρ)).comp (Rc p.c m)))
      (c := ρ) (d := Lmax) hcont
    exact ⟨C, fun τ h1 h2 => hC τ ⟨h1, h2⟩⟩

/-- In `BgRegime`, `p.c ^ (-2 : ℝ) = p.ν ^ 4`. -/
theorem c_rpow_neg_two {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) :
    p.c ^ (-2 : ℝ) = p.ν ^ 4 := by
  have hν : 0 < p.ν := p.ν_pos
  have hc0 : 0 ≤ (p.ν ^ 2)⁻¹ := by positivity
  rw [hbg.c_eq]
  change ((p.ν ^ 2)⁻¹) ^ (-(2 : ℝ)) = p.ν ^ 4
  rw [Real.rpow_neg hc0]
  have h2 : ((p.ν ^ 2)⁻¹) ^ (2 : ℝ) = ((p.ν ^ 2)⁻¹) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  rw [h2, inv_pow, inv_inv, ← pow_mul]

end UnforcedLeray.Short.IIb.CompactDuhamelNormHelp
