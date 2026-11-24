import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrDeriv.Generic
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrDeriv.Weight
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.RegularEnergyDeriv

/-!
# Part III-a, task `PartIII-a:T21/c2/2/6`: `FmrDeriv`

Source of record: `the November 2 reference manuscript`, lines 2937-2946.
Differentiation under the integral sign for the dilated-weight energy of a regular flow
(`Clock/FreeMoving/Rate/FmrDeriv/Generic.lean`: abstract dominated-derivative lemma;
`.../Weight.lean`: bounds and `σ`-derivative of the weight). The domination is that of
`PartII-b` `regEnergyDeriv_pointwise`, with `p ≤ jb^m` and `|∂_σ p| ≤ ν m jb^m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa

theorem fmrDeriv : FmrDeriv := by
  intro c ν m t T v ω hc hν ht hm hω hM
  obtain ⟨M, hMb⟩ := hM
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = |m| + 2 := ⟨_, rfl⟩
  have hN1 : 1 < N + N - m := by
    rw [hNdef]; linarith [le_abs_self m, abs_nonneg m]
  obtain ⟨C, hC⟩ := hω.cell_decay N
  set K1 : ℝ := (2 * (|ν| + M) + 1) * C ^ 2 with hK1
  set G : B0579.Plane → ℝ := fun x => (K1 + ν * m * C ^ 2) * B0579.jb x ^ (m - (N + N)) with hG
  have hGint : IntegrableOn G (B0579.cell c) :=
    ((regEnergyDeriv_integrable_jb m N hN1).const_mul _).integrableOn
  have hcont_x : ∀ σ ∈ Icc t T, Continuous (ω σ) :=
    fun σ hσ => (hω.slice σ hσ).smooth.continuous
  have hσge : ∀ σ ∈ Icc t T, 1 ≤ clockA ν σ := fun σ hσ => fd_clockA_ge_one hν (ht.trans hσ.1)
  have hW_cont : ∀ σ ∈ Icc t T, Continuous (fun x : B0579.Plane => movWeight m (clockA ν σ) x) := by
    intro σ hσ
    have ha : 0 < clockA ν σ := by linarith [hσge σ hσ]
    unfold movWeight
    refine Continuous.rpow_const (by fun_prop) (fun x => Or.inl ?_)
    have : 0 ≤ (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ := by positivity
    linarith
  have hD_cont : ∀ σ ∈ Icc t T,
      Continuous (fun x : B0579.Plane => movWeightDt ν m (clockA ν σ) x) := by
    intro σ hσ
    have ha : 0 < clockA ν σ := by linarith [hσge σ hσ]
    unfold movWeightDt
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) (fun x => Or.inl ?_))
    have : 0 ≤ (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ := by positivity
    linarith
  -- the pointwise bounds
  have hpt : ∀ σ ∈ Icc t T, ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      |ω σ x ^ 2 * movWeight m (clockA ν σ) x| ≤ G x ∧
      |2 * (ω σ x * (ν * UnforcedLeray.Short.IIb.lapP (ω σ) x -
          (v σ x 0 * B0579.pd 0 (ω σ) x + v σ x 1 * B0579.pd 1 (ω σ) x)) *
          movWeight m (clockA ν σ) x)| ≤ G x ∧
      |ω σ x ^ 2 * movWeightDt ν m (clockA ν σ) x| ≤ G x := by
    intro σ hσ x hx
    have hσ0 : 0 ≤ σ := ht.trans hσ.1
    have hv0 : |v σ x 0| ≤ M := by
      have := hMb σ hσ x; linarith [abs_nonneg (v σ x 1)]
    have hv1 : |v σ x 1| ≤ M := by
      have := hMb σ hσ x; linarith [abs_nonneg (v σ x 0)]
    have hM0 : 0 ≤ M := le_trans (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hMb σ hσ x)
    have hu : 0 < B0579.jb x ^ N := Real.rpow_pos_of_pos (B0579.jb_pos x) N
    have hw : 0 ≤ movWeight m (clockA ν σ) x := by
      unfold movWeight
      have ha := hσge σ hσ
      exact Real.rpow_nonneg (add_nonneg zero_le_one (div_nonneg (by positivity) (by beta_reduce; linarith))) _
    have hwle := fd_weight_le ν σ m hν hσ0 hm x
    have hkey := regEnergyDeriv_pointwise (ω σ x) (B0579.pd 0 (ω σ) x) (B0579.pd 1 (ω σ) x)
      (UnforcedLeray.Short.IIb.lapP (ω σ) x) (v σ x 0) (v σ x 1) ν M (B0579.jb x ^ N)
      (movWeight m (clockA ν σ) x) C hu hw (hC σ hσ x hx) hv0 hv1 hM0
    have hq : movWeight m (clockA ν σ) x / (B0579.jb x ^ N * B0579.jb x ^ N) ≤
        B0579.jb x ^ (m - (N + N)) := by
      rw [regEnergyDeriv_rpow_eq x m N, B0579.coe_density]
      exact div_le_div_of_nonneg_right hwle (by positivity)
    have hjb0 : 0 ≤ B0579.jb x ^ (m - (N + N)) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have hK1nn : 0 ≤ K1 := by positivity
    have hνm : 0 ≤ ν * m * C ^ 2 := by positivity
    have hGge : K1 * B0579.jb x ^ (m - (N + N)) ≤ G x := by
      simp only [hG]; nlinarith [mul_nonneg hνm hjb0]
    refine ⟨?_, ?_, ?_⟩
    · exact hkey.2.trans ((mul_le_mul_of_nonneg_left hq hK1nn).trans hGge)
    · exact hkey.1.trans ((mul_le_mul_of_nonneg_left hq hK1nn).trans hGge)
    · -- the `σ`-derivative term
      have hω0 : |ω σ x| * B0579.jb x ^ N ≤ C := by
        refine le_trans (mul_le_mul_of_nonneg_right ?_ hu.le) (hC σ hσ x hx)
        linarith [abs_nonneg (B0579.pd 0 (ω σ) x), abs_nonneg (B0579.pd 1 (ω σ) x),
          abs_nonneg (UnforcedLeray.Short.IIb.lapP (ω σ) x)]
      have hC0 : 0 ≤ C := le_trans (mul_nonneg (abs_nonneg _) hu.le) hω0
      have hsq : ω σ x ^ 2 * (B0579.jb x ^ N * B0579.jb x ^ N) ≤ C ^ 2 := by
        have hw0sq : ω σ x ^ 2 = |ω σ x| * |ω σ x| := by rw [abs_mul_abs_self, sq]
        calc ω σ x ^ 2 * (B0579.jb x ^ N * B0579.jb x ^ N)
            = (|ω σ x| * B0579.jb x ^ N) * (|ω σ x| * B0579.jb x ^ N) := by rw [hw0sq]; ring
          _ ≤ C * C := mul_le_mul hω0 hω0 (mul_nonneg (abs_nonneg _) hu.le) hC0
          _ = C ^ 2 := by ring
      have hjm : B0579.jb x ^ m = B0579.jb x ^ (m - (N + N)) * (B0579.jb x ^ N * B0579.jb x ^ N) := by
        rw [← Real.rpow_add (B0579.jb_pos x), ← Real.rpow_add (B0579.jb_pos x)]; congr 1; ring
      have hDt := fd_weightDt_le ν σ m hν hσ0 hm x
      calc |ω σ x ^ 2 * movWeightDt ν m (clockA ν σ) x|
          = ω σ x ^ 2 * |movWeightDt ν m (clockA ν σ) x| := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        _ ≤ ω σ x ^ 2 * (ν * m * B0579.jb x ^ m) :=
            mul_le_mul_of_nonneg_left hDt (sq_nonneg _)
        _ = ν * m * B0579.jb x ^ (m - (N + N)) * (ω σ x ^ 2 * (B0579.jb x ^ N * B0579.jb x ^ N)) := by
            rw [hjm]; ring
        _ ≤ ν * m * B0579.jb x ^ (m - (N + N)) * C ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ ≤ G x := by simp only [hG]; nlinarith [mul_nonneg hK1nn hjb0]
  have hmeasF : ∀ σ ∈ Icc t T, AEStronglyMeasurable
      (fun x : B0579.Plane => ω σ x ^ 2 * movWeight m (clockA ν σ) x)
      (volume.restrict (B0579.cell c)) := fun σ hσ =>
    (((hcont_x σ hσ).pow 2).mul (hW_cont σ hσ)).aestronglyMeasurable
  have hgen := fd_generic (μ := volume) t T (B0579.cell c) (B0579.measurableSet_cell c)
    (fun σ x => ω σ x ^ 2 * movWeight m (clockA ν σ) x)
    (fun σ x => 2 * (ω σ x * (ν * UnforcedLeray.Short.IIb.lapP (ω σ) x -
          (v σ x 0 * B0579.pd 0 (ω σ) x + v σ x 1 * B0579.pd 1 (ω σ) x)) *
          movWeight m (clockA ν σ) x) + ω σ x ^ 2 * movWeightDt ν m (clockA ν σ) x)
    (fun x => 2 * G x) (hGint.const_mul 2) hmeasF
    (fun σ hσ x hx => by
      have h1 := (hpt σ hσ x (abs_fst_le_of_mem_cell hx)).1
      beta_reduce
      linarith [abs_nonneg (ω σ x ^ 2 * movWeight m (clockA ν σ) x)])
    (fun σ hσ x hx => by
      obtain ⟨h1, h2, h3⟩ := hpt σ hσ x (abs_fst_le_of_mem_cell hx)
      exact (abs_add_le _ _).trans (by beta_reduce; linarith))
    (fun x _ σ hσ => by
      have h1 := hω.pde σ hσ x
      have ha : 0 < clockA ν σ := by linarith [hσge σ hσ]
      have h2 := (fd_weight_hasDeriv ν σ m hν ha x).hasDerivWithinAt (s := Icc t T)
      have h3 := (h1.pow 2).mul h2
      exact h3.congr_deriv (by norm_num; ring))
  obtain ⟨hint, hcont, hderiv⟩ := hgen
  refine ⟨hint, ?_, ?_⟩
  · have hA : Continuous fun σ => clockA ν σ ^ 3 := by unfold clockA; fun_prop
    exact hA.continuousOn.mul hcont
  · intro τ hτ
    obtain ⟨hF'int, hI⟩ := hderiv τ hτ
    have hτI : τ ∈ Icc t T := ⟨hτ.1, hτ.2.le⟩
    have hA : HasDerivAt (fun σ => clockA ν σ ^ 3) (3 * clockA ν τ ^ 2 * ν) τ := by
      have : HasDerivAt (fun r => clockA ν r) ν τ := by
        unfold clockA; simpa using ((hasDerivAt_id τ).const_mul ν).const_add 1
      have h3 := (hasDerivAt_pow 3 (clockA ν τ)).comp τ this
      simpa [Function.comp_def] using h3
    have hprod := (hA.hasDerivWithinAt (s := Ici τ)).mul hI
    -- integrability of the two pieces of the derivative
    have hBint : IntegrableOn (fun x : B0579.Plane => ω τ x ^ 2 * movWeightDt ν m (clockA ν τ) x)
        (B0579.cell c) := by
      refine Integrable.mono' hGint
        (((hcont_x τ hτI).pow 2).mul (hD_cont τ hτI)).aestronglyMeasurable ?_
      refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
        (ae_of_all _ (fun x hx => ?_))
      rw [Real.norm_eq_abs]; exact (hpt τ hτI x (abs_fst_le_of_mem_cell hx)).2.2
    have hAint : IntegrableOn (fun x : B0579.Plane => 2 * (ω τ x * (ν * UnforcedLeray.Short.IIb.lapP (ω τ) x -
          (v τ x 0 * B0579.pd 0 (ω τ) x + v τ x 1 * B0579.pd 1 (ω τ) x)) *
          movWeight m (clockA ν τ) x)) (B0579.cell c) := by
      exact (hF'int.sub hBint).congr (ae_of_all _ (fun x => by simp))
    have hsplit : ∫ x in B0579.cell c, (2 * (ω τ x * (ν * UnforcedLeray.Short.IIb.lapP (ω τ) x -
          (v τ x 0 * B0579.pd 0 (ω τ) x + v τ x 1 * B0579.pd 1 (ω τ) x)) *
          movWeight m (clockA ν τ) x) + ω τ x ^ 2 * movWeightDt ν m (clockA ν τ) x) =
        2 * (∫ x in B0579.cell c, ω τ x * (ν * UnforcedLeray.Short.IIb.lapP (ω τ) x -
          (v τ x 0 * B0579.pd 0 (ω τ) x + v τ x 1 * B0579.pd 1 (ω τ) x)) *
          movWeight m (clockA ν τ) x) + ∫ x in B0579.cell c, ω τ x ^ 2 * movWeightDt ν m (clockA ν τ) x := by
      rw [integral_add hAint hBint, integral_const_mul]
    unfold movFlowEnergy movEnergy
    refine hprod.congr_deriv ?_
    rw [hsplit]
    unfold movRate
    simp only [show ∀ (g : B0579.Plane → ℝ) (x : B0579.Plane),
      UnforcedLeray.Short.IIb.lapP g x = UnforcedLeray.Short.IIIa.lapP g x from fun _ _ => rfl]
    ring

end UnforcedLeray.Short.IIIa
