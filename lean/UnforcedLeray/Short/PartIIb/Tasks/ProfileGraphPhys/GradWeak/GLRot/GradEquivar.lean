import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLUniq
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.TestTransport
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.DyTransport
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.PairTransport
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.PairCongr
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.PairLinL
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.PairLinR
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.YrTransport
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.GradToEquivar

/-!
# Part II-b, task `PartII-b:T10/7/1/1/2/9` (`GLGradEquivar`): equivariance of the weak gradient

Source of record: `the November 2 reference manuscript` lines 1912-1921, chart 1639-1668.

Target: `gl_gradEquivar : UnforcedLeray.Short.IIb.GLGradEquivar`.

Outline. Let `M_jk = (T e_k)_j` (orthogonal). For a phase test `Φ`, `Ψ = trF T Φ` is a phase test.
By `gl_dyTransport` and the row orthogonality of `M`, `trF T (-∂_jΦ) = Σ_k M_jk • (-∂_kΨ)`.
Then `⟪Φ, g_j⟫ = ⟪-∂_jΦ, w⟫ = ⟪trF T (-∂_jΦ), w⟫ = Σ_k M_jk ⟪-∂_kΨ, w⟫ = Σ_k M_jk ⟪Ψ, g_k⟫
= Σ_k M_jk ⟪Φ, trF T⁻¹ g_k⟫`, which is the pairing of `F_j = Σ_k M_jk • trF T⁻¹ g_k`.
`gl_uniq` gives `g_j =ᵐ F_j`, and the measure preserving slice map `x ↦ (x.1, T x.2)` transports
this to the stated identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-! ### Algebra of `cApp` -/

theorem gle_cApp_neg (S : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : cApp S (-v) = -cApp S v := by
  have h := glg_cApp_smul S (-1) v
  simpa using h

theorem gle_cApp_sum3 (S : Space ≃ₗᵢ[ℝ] Space) (f : Fin 3 → CVec3) :
    cApp S (∑ k, f k) = ∑ k, cApp S (f k) := by
  simp only [Fin.sum_univ_three, glg_cApp_add]

theorem gle_cApp_symm_cApp (T : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) :
    cApp T.symm (cApp T v) = v := by
  have h : cApp T.symm (cApp T v) = B0412.realC (T.symm (reS (cApp T v)))
      + Complex.I • B0412.realC (T.symm (imS (cApp T v))) := rfl
  rw [h, glg_reS_cApp, glg_imS_cApp, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  exact (PairTr.realC_decomp v).symm

theorem gle_trF_trF_symm (T : Space ≃ₗᵢ[ℝ] Space) (f : ℝ × Space → CVec3) :
    trF T (trF T.symm f) = f := by
  funext x
  show cApp T.symm (cApp T.symm.symm (f (x.1, T.symm (T x.2)))) = f x
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_symm, gle_cApp_symm_cApp]

/-! ### Row orthogonality of the matrix of `T` -/

theorem gle_coord_inner (i : Fin 3) (b : Space) : inner ℝ (coordinateVector i) b = b i := by
  simp [coordinateVector, EuclideanSpace.inner_single_left]

theorem gle_coord_inner' (i : Fin 3) (b : Space) : inner ℝ b (coordinateVector i) = b i := by
  rw [real_inner_comm]
  exact gle_coord_inner i b

theorem gle_inner_sum (x y : Space) : inner ℝ x y = ∑ k : Fin 3, x k * y k := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem gle_row_orth (T : Space ≃ₗᵢ[ℝ] Space) (j l : Fin 3) :
    ∑ k : Fin 3, (T (coordinateVector k)) j * (T (coordinateVector k)) l =
      if j = l then 1 else 0 := by
  have hk : ∀ i k : Fin 3, (T (coordinateVector k)) i = (T.symm (coordinateVector i)) k := by
    intro i k
    have h1 : inner ℝ (T.symm (coordinateVector i)) (coordinateVector k)
        = inner ℝ (T (T.symm (coordinateVector i))) (T (coordinateVector k)) :=
      (LinearIsometryEquiv.inner_map_map T _ _).symm
    rw [LinearIsometryEquiv.apply_symm_apply] at h1
    rw [← gle_coord_inner i (T (coordinateVector k)),
      ← gle_coord_inner' k (T.symm (coordinateVector i)), h1]
  simp only [hk j, hk l]
  rw [← gle_inner_sum (T.symm (coordinateVector j)) (T.symm (coordinateVector l)),
    LinearIsometryEquiv.inner_map_map T.symm]
  rcases eq_or_ne j l with h | h
  · subst h
    simp [coordinateVector, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  · simp [coordinateVector, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, h,
      Ne.symm h]

theorem gle_sum_matrix (T : Space ≃ₗᵢ[ℝ] Space) (j : Fin 3) (V : Fin 3 → CVec3) :
    ∑ k : Fin 3, ((T (coordinateVector k)) j : ℂ) •
      ∑ l : Fin 3, ((T (coordinateVector k)) l : ℂ) • V l = V j := by
  have hdel : ∀ l : Fin 3, ∑ k : Fin 3, ((T (coordinateVector k)) j : ℂ) *
      ((T (coordinateVector k)) l : ℂ) = if j = l then 1 else 0 := by
    intro l
    have h := congrArg (fun r : ℝ => (r : ℂ)) (gle_row_orth T j l)
    simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h
    rw [h]
    split_ifs <;> simp
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hdel, ite_smul, one_smul, zero_smul]
  simp

theorem gle_key (T : Space ≃ₗᵢ[ℝ] Space) (j : Fin 3) (V : Fin 3 → CVec3) :
    cApp T.symm (-(V j)) = ∑ k : Fin 3, ((T (coordinateVector k)) j : ℂ) •
      -(cApp T.symm (∑ l : Fin 3, ((T (coordinateVector k)) l : ℂ) • V l)) := by
  have hm := gle_sum_matrix T j V
  rw [← hm, gle_cApp_neg, gle_cApp_sum3]
  simp only [glg_cApp_smul, Finset.sum_neg_distrib, smul_neg]

/-! ### `Y_r` is closed under sums and scalars (general exponent `r`) -/

/-- The phase measure `(Lebesgue on (0,P]) ⊗ Lebesgue` on `ℝ × ℝ³`. -/
abbrev gleMu (P : ℝ) : Measure (ℝ × Space) :=
  ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)

theorem gleMu_ac (P : ℝ) : gleMu P ≪ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.AbsolutelyContinuous.prod Measure.restrict_le_self.absolutelyContinuous
    (le_refl (volume : Measure Space)).absolutelyContinuous

theorem gle_aemeas_pow (P r : ℝ) (f : ℝ × Space → CVec3) (hf : AEStronglyMeasurable f volume) :
    AEMeasurable (fun z => ‖f z‖ₑ ^ r) (gleMu P) :=
  AEMeasurable.pow_const (AEStronglyMeasurable.enorm (hf.mono_ac (gleMu_ac P))) r

theorem gle_phaseLpNorm_eq (P r : ℝ) (f : ℝ × Space → CVec3) (hf : AEStronglyMeasurable f volume) :
    phaseLpNorm P r f = (ENNReal.ofReal P⁻¹ * ∫⁻ z, ‖f z‖ₑ ^ r ∂(gleMu P)) ^ (1 / r) := by
  unfold phaseLpNorm
  rw [lintegral_prod _ (gle_aemeas_pow P r f hf)]

theorem gle_lt_top_iff (P r : ℝ) (hP : 0 < P) (hr : 0 < r) (f : ℝ × Space → CVec3)
    (hf : AEStronglyMeasurable f volume) :
    phaseLpNorm P r f < ⊤ ↔ ∫⁻ z, ‖f z‖ₑ ^ r ∂(gleMu P) < ⊤ := by
  have hPinv : ENNReal.ofReal P⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hP)).ne'
  rw [gle_phaseLpNorm_eq P r f hf, ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.2 hr)]
  constructor
  · intro h
    rw [lt_top_iff_ne_top] at h ⊢
    intro hI
    apply h
    rw [hI, ENNReal.mul_top hPinv]
  · intro h
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem gle_isInYr_smul (P r : ℝ) (hP : 0 < P) (hr : 0 < r) (c : ℂ)
    {u : ℝ × Space → CVec3} (hu : IsInYr P r u) : IsInYr P r (fun x => c • u x) := by
  have hm : AEStronglyMeasurable (fun x => c • u x) volume := hu.meas.const_smul c
  refine ⟨?_, hm, ?_⟩
  · filter_upwards [hu.periodic] with x hx
    simp only [hx]
  · rw [gle_lt_top_iff P r hP hr _ hm]
    have hpt : ∀ z, ‖c • u z‖ₑ ^ r = ‖c‖ₑ ^ r * ‖u z‖ₑ ^ r := fun z => by
      rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le enorm_ne_top)]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_nonneg hr.le enorm_ne_top))
      ((gle_lt_top_iff P r hP hr u hu.meas).1 hu.finite)

theorem gle_isInYr_add (P r : ℝ) (hP : 0 < P) (hr : 1 ≤ r) {u v : ℝ × Space → CVec3}
    (hu : IsInYr P r u) (hv : IsInYr P r v) : IsInYr P r (fun x => u x + v x) := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hm : AEStronglyMeasurable (fun x => u x + v x) volume := hu.meas.add hv.meas
  refine ⟨?_, hm, ?_⟩
  · filter_upwards [hu.periodic, hv.periodic] with x h1 h2
    simp only [h1, h2]
  · rw [gle_lt_top_iff P r hP hr0 _ hm]
    have hpt : ∀ z, ‖u z + v z‖ₑ ^ r ≤ 2 ^ (r - 1) * (‖u z‖ₑ ^ r + ‖v z‖ₑ ^ r) := fun z =>
      (ENNReal.rpow_le_rpow (enorm_add_le _ _) hr0.le).trans
        (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr)
    have hu' := (gle_lt_top_iff P r hP hr0 u hu.meas).1 hu.finite
    have hv' := (gle_lt_top_iff P r hP hr0 v hv.meas).1 hv.finite
    have hmu := gle_aemeas_pow P r u hu.meas
    have h2 : (2 : ℝ≥0∞) ^ (r - 1) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
    calc ∫⁻ z, ‖u z + v z‖ₑ ^ r ∂(gleMu P)
        ≤ ∫⁻ z, 2 ^ (r - 1) * (‖u z‖ₑ ^ r + ‖v z‖ₑ ^ r) ∂(gleMu P) := lintegral_mono hpt
      _ = 2 ^ (r - 1) * (∫⁻ z, ‖u z‖ₑ ^ r ∂(gleMu P) + ∫⁻ z, ‖v z‖ₑ ^ r ∂(gleMu P)) := by
          rw [lintegral_const_mul' _ _ h2, lintegral_add_left' hmu]
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 h2)
          (ENNReal.add_lt_top.2 ⟨hu', hv'⟩)

theorem gle_isInYr_lin3 (P r : ℝ) (hP : 0 < P) (hr : 1 ≤ r) (c : Fin 3 → ℂ)
    (u : Fin 3 → ℝ × Space → CVec3) (hu : ∀ k, IsInYr P r (u k)) :
    IsInYr P r (fun x => ∑ k : Fin 3, c k • u k x) := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have e : (fun x => ∑ k : Fin 3, c k • u k x) =
      fun x => (c 0 • u 0 x + c 1 • u 1 x) + c 2 • u 2 x := by
    funext x
    simp only [Fin.sum_univ_three]
  rw [e]
  exact gle_isInYr_add P r hP hr
    (gle_isInYr_add P r hP hr (gle_isInYr_smul P r hP hr0 (c 0) (hu 0))
      (gle_isInYr_smul P r hP hr0 (c 1) (hu 1)))
    (gle_isInYr_smul P r hP hr0 (c 2) (hu 2))

/-! ### The main statement -/

theorem gl_gradEquivar : UnforcedLeray.Short.IIb.GLGradEquivar := by
  intro P r w g T hP hr1 hw hg hgp hweq
  have hr1' : (1 : ℝ) ≤ r := hr1.le
  have hu : ∀ k : Fin 3, IsInYr P r (trF T.symm (g k)) := fun k =>
    gl_yrTransport P r T.symm (g k) (hg k)
  have hF : ∀ j : Fin 3, IsInYr P r
      (fun x => ∑ k : Fin 3, ((T (coordinateVector k)) j : ℂ) • trF T.symm (g k) x) := fun j =>
    gle_isInYr_lin3 P r hP hr1' (fun k => ((T (coordinateVector k)) j : ℂ))
      (fun k => trF T.symm (g k)) hu
  have hpair : ∀ j : Fin 3, ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
      pairF P Φ (g j) =
        pairF P Φ (fun x => ∑ k : Fin 3, ((T (coordinateVector k)) j : ℂ) • trF T.symm (g k) x) := by
    intro j Φ hΦ
    have hΨ : IsPhaseTest P (trF T Φ) := gl_testTransport P T Φ hΦ
    have hA : pairF P Φ (g j) = pairF P (-(dy j Φ)) w := (hgp j Φ hΦ).symm
    have htw : trF T w =ᵐ[volume] w := by
      filter_upwards [hweq] with x hx
      show cApp T.symm (w (x.1, T x.2)) = w x
      rw [hx, gle_cApp_symm_cApp]
    have hB : pairF P (-(dy j Φ)) w = pairF P (trF T (-(dy j Φ))) w := by
      rw [gl_pairTransport P T (-(dy j Φ)) w]
      exact gl_pairCongr P _ _ _ htw
    have hC : trF T (-(dy j Φ)) = fun x => ∑ k : Fin 3,
        ((T (coordinateVector k)) j : ℂ) • (-(dy k (trF T Φ))) x := by
      funext x
      have hd : ∀ k : Fin 3, dy k (trF T Φ) x =
          cApp T.symm (∑ l : Fin 3, ((T (coordinateVector k)) l : ℂ) • dy l Φ (x.1, T x.2)) :=
        fun k => gl_dyTransport T Φ hΦ.smooth k x
      simp only [Pi.neg_apply, hd]
      exact gle_key T j (fun l => dy l Φ (x.1, T x.2))
    have hL : pairF P (trF T (-(dy j Φ))) w = ∑ k : Fin 3,
        ((T (coordinateVector k)) j : ℂ) * pairF P (-(dy k (trF T Φ))) w := by
      rw [hC]
      exact gl_pairLinL P r (fun k => -(dy k (trF T Φ))) w
        (fun k => ((T (coordinateVector k)) j : ℂ)) hP hr1 (fun k => (hΨ.dy k).neg) hw
    have hG : ∀ k : Fin 3, pairF P (-(dy k (trF T Φ))) w = pairF P (trF T Φ) (g k) :=
      fun k => hgp k (trF T Φ) hΨ
    have hT : ∀ k : Fin 3, pairF P Φ (trF T.symm (g k)) = pairF P (trF T Φ) (g k) := by
      intro k
      have h := gl_pairTransport P T Φ (trF T.symm (g k))
      rw [gle_trF_trF_symm] at h
      exact h
    have hR : pairF P Φ (fun x => ∑ k : Fin 3, ((T (coordinateVector k)) j : ℂ) • trF T.symm (g k) x)
        = ∑ k : Fin 3, ((T (coordinateVector k)) j : ℂ) * pairF P Φ (trF T.symm (g k)) :=
      gl_pairLinR P r Φ (fun k => trF T.symm (g k)) (fun k => ((T (coordinateVector k)) j : ℂ))
        hP hr1 hΦ hu
    rw [hR, hA, hB, hL]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hG k, hT k]
  have hae : ∀ j : Fin 3, g j =ᵐ[volume]
      (fun x => ∑ k : Fin 3, ((T (coordinateVector k)) j : ℂ) • trF T.symm (g k) x) :=
    fun j => gl_uniq P r (g j) _ hP hr1 (hg j) (hF j) (hpair j)
  have hall : ∀ j : Fin 3, ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      g j (x.1, T x.2) = ∑ k : Fin 3, ((T (coordinateVector k)) j : ℂ) • cApp T (g k x) := by
    intro j
    have h1 : ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
        g j (x.1, T x.2) = (fun x => ∑ k : Fin 3,
          ((T (coordinateVector k)) j : ℂ) • trF T.symm (g k) x) (x.1, T x.2) :=
      (slice_measurePreserving T).quasiMeasurePreserving.ae
        (p := fun y => g j y = (fun x => ∑ k : Fin 3,
          ((T (coordinateVector k)) j : ℂ) • trF T.symm (g k) x) y) (hae j)
    filter_upwards [h1] with x hx
    rw [hx]
    simp only [trF, LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply, Prod.mk.eta]
  exact ae_all_iff.2 hall

end UnforcedLeray.Short.IIb
