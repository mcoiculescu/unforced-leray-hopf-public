import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1_2.L1PolyGauss
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1_2.L3DiffParam

/-!
# Generic parametric smoothness (`T0gContDiffParam`)

Source `the November 2 reference manuscript`
lines 1640-1656. Induction on `n`, generalizing over the codomain `V` and the family `K`.
The first derivative of `x ↦ ∫ G1(w) • K x w` is `x ↦ ∫ G1(w) • K' x w` with
`K' x w = fderiv (K · w) x : X →L V`, a family of the same kind (jointly smooth, and its
`x`-derivatives of order `k` are the `(k+1)`-st derivatives of `K`, hence polynomially bounded).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

theorem t0g_contDiffParam :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gContDiffParam := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gContDiffParam
  intro X V hXn hXs hXf hVn hVs hVc n K hK hKG
  -- differentiation under the integral sign, for every codomain and family of this kind
  have hfd : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (K : X → UnforcedLeray.Gaussian.Euc 2 → V),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : X × UnforcedLeray.Gaussian.Euc 2 => K p.1 p.2) →
      (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ x w,
        ‖iteratedFDeriv ℝ k (fun y => K y w) x‖ ≤ C * (1 + ‖w‖) ^ N) →
      ∀ x, HasFDerivAt (fun x => ∫ w, UnforcedLeray.Gaussian.gaussKernel 2 1 w • K x w)
        (∫ w, UnforcedLeray.Gaussian.gaussKernel 2 1 w • fderiv ℝ (fun y => K y w) x) x := by
    intro V hVn hVs hVc K hK hKG x
    obtain ⟨C0, N0, h0⟩ := hKG 0
    obtain ⟨C1, N1, h1⟩ := hKG 1
    have hKb : ∃ C : ℝ, ∃ N : ℕ, ∀ x w, ‖K x w‖ ≤ C * (1 + ‖w‖) ^ N :=
      ⟨C0, N0, fun x w => by simpa only [norm_iteratedFDeriv_zero] using h0 x w⟩
    have hKd : ∃ C : ℝ, ∃ N : ℕ, ∀ x w,
        ‖fderiv ℝ (fun y => K y w) x‖ ≤ C * (1 + ‖w‖) ^ N :=
      ⟨C1, N1, fun x w => by simpa only [norm_iteratedFDeriv_one] using h1 x w⟩
    exact t0g_diffParam t0g_polyGauss X V K hK hKb hKd x
  have key : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (K : X → UnforcedLeray.Gaussian.Euc 2 → V),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : X × UnforcedLeray.Gaussian.Euc 2 => K p.1 p.2) →
      (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ x w,
        ‖iteratedFDeriv ℝ k (fun y => K y w) x‖ ≤ C * (1 + ‖w‖) ^ N) →
      ContDiff ℝ (n : WithTop ℕ∞)
        (fun x => ∫ w, UnforcedLeray.Gaussian.gaussKernel 2 1 w • K x w) := by
    intro n
    induction n with
    | zero =>
      intro V hVn hVs hVc K hK hKG
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun x => (hfd V K hK hKG x).continuousAt
    | succ n ih =>
      intro V hVn hVs hVc K hK hKG
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      -- the joint smoothness of `K' x w = fderiv (K · w) x`
      set F2 : X × UnforcedLeray.Gaussian.Euc 2 → V := fun q => K q.1 q.2 with hF2def
      have hfdc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F2) :=
        hK.fderiv_right (by simp)
      have hL : ∀ (x : X) (w : UnforcedLeray.Gaussian.Euc 2),
          fderiv ℝ (fun y => K y w) x =
            (fderiv ℝ F2 (x, w)).comp
              ((ContinuousLinearMap.id ℝ X).prod (0 : X →L[ℝ] UnforcedLeray.Gaussian.Euc 2)) := by
        intro x w
        have h1 : HasFDerivAt (fun y : X => (y, w))
            ((ContinuousLinearMap.id ℝ X).prod (0 : X →L[ℝ] UnforcedLeray.Gaussian.Euc 2)) x :=
          (hasFDerivAt_id x).prodMk (hasFDerivAt_const w x)
        have h2 := ((hK.differentiable (by simp)) (x, w)).hasFDerivAt.comp x h1
        exact h2.fderiv
      have hK' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : X × UnforcedLeray.Gaussian.Euc 2 => fderiv ℝ (fun y => K y p.2) p.1) := by
        have e : (fun p : X × UnforcedLeray.Gaussian.Euc 2 => fderiv ℝ (fun y => K y p.2) p.1)
            = fun p => (fderiv ℝ F2 p).comp
                ((ContinuousLinearMap.id ℝ X).prod (0 : X →L[ℝ] UnforcedLeray.Gaussian.Euc 2)) :=
          funext fun p => hL p.1 p.2
        rw [e]
        exact hfdc.clm_comp contDiff_const
      have hKG' : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ x w,
          ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ (fun y' => K y' w) y) x‖ ≤ C * (1 + ‖w‖) ^ N := by
        intro k
        obtain ⟨C, N, hC⟩ := hKG (k + 1)
        refine ⟨C, N, fun x w => ?_⟩
        have e : ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ (fun y' => K y' w) y) x‖
            = ‖iteratedFDeriv ℝ (k + 1) (fun y => K y w) x‖ :=
          norm_iteratedFDeriv_fderiv
        rw [e]
        exact hC x w
      have hdiff : Differentiable ℝ (fun x => ∫ w, UnforcedLeray.Gaussian.gaussKernel 2 1 w • K x w) :=
        fun x => (hfd V K hK hKG x).differentiableAt
      have hfeq : fderiv ℝ (fun x => ∫ w, UnforcedLeray.Gaussian.gaussKernel 2 1 w • K x w)
          = fun x => ∫ w, UnforcedLeray.Gaussian.gaussKernel 2 1 w • fderiv ℝ (fun y => K y w) x :=
        funext fun x => (hfd V K hK hKG x).fderiv
      refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
      rw [hfeq]
      exact ih (X →L[ℝ] V) (fun x w => fderiv ℝ (fun y => K y w) x) hK' hKG'
  exact key n V K hK hKG

end
